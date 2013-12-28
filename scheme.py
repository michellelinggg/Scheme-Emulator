"""This module implements the core Scheme interpreter functions, including the
eval/apply mutual recurrence, environment model, and read-eval-print loop.
"""

from scheme_primitives import *
from scheme_reader import *
from ucb import main, trace

##############
# Eval/Apply #
##############

def scheme_eval(expr, env):
    """Evaluate Scheme expression EXPR in environment ENV.

    >>> expr = read_line("(+ 2 2)")
    >>> expr
    Pair('+', Pair(2, Pair(2, nil)))
    >>> scheme_eval(expr, create_global_frame())
    4
    """
    if expr is None:
        raise SchemeError("Cannot evaluate an undefined expression.")

    # Evaluate Atoms
    if scheme_symbolp(expr):
        return env.lookup(expr)
    elif scheme_atomp(expr) or scheme_stringp(expr) or expr is okay:
        return expr

    # All non-atomic expressions are lists.
    if not scheme_listp(expr):
        raise SchemeError("malformed list: {0}".format(str(expr)))
    first, rest = expr.first, expr.second

    # Evaluate Combinations
    if (scheme_symbolp(first)  # first might be unhashable
            and first in LOGIC_FORMS):
        return scheme_eval(LOGIC_FORMS[first](rest, env), env)
    elif first == "lambda":
        return do_lambda_form(rest, env)
    elif first == "mu":
        return do_mu_form(rest)
    elif first == "define":
        return do_define_form(rest, env)
    elif first == 'quote':
        return do_quote_form(rest)
    elif first == "let":
        expr, env = do_let_form(rest, env)
        return scheme_eval(expr, env)
    else:
        procedure = scheme_eval(first, env)
        args = rest.map(lambda operand: scheme_eval(operand, env))
        return scheme_apply(procedure, args, env)

def scheme_apply(procedure, args, env):
    """Apply Scheme PROCEDURE to argument values ARGS in environment ENV."""
    if isinstance(procedure, PrimitiveProcedure):
        return apply_primitive(procedure, args, env)
    elif isinstance(procedure, LambdaProcedure):
        frame = procedure.env.make_call_frame(procedure.formals, args)
        return scheme_eval(procedure.body, frame)
    elif isinstance(procedure, MuProcedure):
        frame = env.make_call_frame(procedure.formals, args)
        return scheme_eval(procedure.body, frame)
    else:
        raise SchemeError("Cannot call {0}".format(str(procedure)))

def list_from_pair(p):
    l = []
    while p != nil:
        l.append(p.first)
        p = p.second
    return l

def apply_primitive(procedure, args, env):
    """Apply PrimitiveProcedure PROCEDURE to a Scheme list of ARGS in ENV.

    >>> env = create_global_frame()
    >>> plus = env.bindings["+"]
    >>> twos = Pair(2, Pair(2, nil))
    >>> apply_primitive(plus, twos, env)
    4
    """
    args_as_list = list_from_pair(args)
    if procedure.use_env: args_as_list.append(env)
    try: return procedure.fn(*args_as_list)
    except TypeError as exception:
        raise SchemeError(exception)

################
# Environments #
################

class Frame(object):
    """An environment frame binds Scheme symbols to Scheme values."""

    def __init__(self, parent):
        """An empty frame with a PARENT frame (that may be None)."""
        self.bindings = {}
        self.parent = parent

    def __repr__(self):
        if self.parent is None:
            return "<Global Frame>"
        else:
            s = sorted('{0}: {1}'.format(k,v) for k,v in self.bindings.items())
            return "<{{{0}}} -> {1}>".format(', '.join(s), repr(self.parent))

    def lookup(self, symbol):
        """Return the value bound to SYMBOL.  Errors if SYMBOL is not found."""
        while not self is None:
            if symbol in self.bindings: return self.bindings[symbol]
            self = self.parent
        else:
            raise SchemeError("unknown identifier: {0}".format(str(symbol)))

    def global_frame(self):
        """The global environment at the root of the parent chain."""
        e = self
        while e.parent is not None:
            e = e.parent
        return e

    def make_call_frame(self, formals, vals):
        """Return a new local frame whose parent is SELF, in which the symbols
        in the Scheme formal parameter list FORMALS are bound to the Scheme
        values in the Scheme value list VALS. Raise an error if too many or too
        few arguments are given.

        >>> env = create_global_frame()
        >>> formals, vals = read_line("(a b c)"), read_line("(1 2 3)")
        >>> env.make_call_frame(formals, vals)
        <{a: 1, b: 2, c: 3} -> <Global Frame>>
        """
        frame = Frame(self)
        while not formals == vals == nil:
            if formals == nil or vals == nil:
                raise SchemeError('parameter mismatch')
            frame.define(formals.first, vals.first)
            formals = formals.second; vals = vals.second
        return frame

    def define(self, sym, val):
        """Define Scheme symbol SYM to have value VAL in SELF."""
        if not scheme_symbolp(sym): raise SchemeError("bad variable name: {0}".format(sym))
        self.bindings[sym] = val

class LambdaProcedure(object):
    """A procedure defined by a lambda expression or the complex define form."""

    def __init__(self, formals, body, env):
        """A procedure whose formal parameter list is FORMALS (a Scheme list),
        whose body is the single Scheme expression BODY, and whose parent
        environment is the Frame ENV.  A lambda expression containing multiple
        expressions, such as (lambda (x) (display x) (+ x 1)) can be handled by
        using (begin (display x) (+ x 1)) as the body."""
        self.formals = formals
        self.body = body
        self.env = env

    def __str__(self):
        return "(lambda {0} {1})".format(str(self.formals), str(self.body))

    def __repr__(self):
        args = (self.formals, self.body, self.env)
        return "LambdaProcedure({0}, {1}, {2})".format(*(repr(a) for a in args))

class MuProcedure(object):
    """A procedure defined by a mu expression, which has dynamic scope.
     _________________
    < Scheme is cool! >
     -----------------
            \   ^__^
             \  (oo)\_______
                (__)\       )\/\
                    ||----w |
                    ||     ||
    """

    def __init__(self, formals, body):
        """A procedure whose formal parameter list is FORMALS (a Scheme list),
        whose body is the single Scheme expression BODY.  A mu expression
        containing multiple expressions, such as (mu (x) (display x) (+ x 1))
        can be handled by using (begin (display x) (+ x 1)) as the body."""
        self.formals = formals
        self.body = body

    def __str__(self):
        return "(mu {0} {1})".format(str(self.formals), str(self.body))

    def __repr__(self):
        args = (self.formals, self.body)
        return "MuProcedure({0}, {1})".format(*(repr(a) for a in args))


#################
# Special forms #
#################

def do_lambda_form(vals, env):
    """Evaluate a lambda form with parameters VALS in environment ENV."""
    check_form(vals, 2)
    formals = vals[0]
    check_formals(formals)
    if len(vals) == 2:
        body = vals[1]
    else:
        body = Pair('begin', vals.second)
    f = LambdaProcedure(formals, body, env)
    return f

def do_mu_form(vals):
    """Evaluate a mu form with parameters VALS."""
    check_form(vals, 2)
    formals = vals[0]
    check_formals(formals)
    if len(vals) == 2:
        body = vals[1]
    else:
        body = Pair('begin', vals.second)
    f = MuProcedure(formals, body)
    return f

def do_define_form(vals, env):
    """Evaluate a define form with parameters VALS in environment ENV."""
    check_form(vals, 2)
    target = vals[0]
    if scheme_symbolp(target):
        check_form(vals, 2, 2)
        env.define(target, scheme_eval(vals[1], env))
        return target
    elif isinstance(target, Pair):
        name = target.first; formals = target.second; body = vals.second
        f = do_lambda_form(Pair(formals, body), env)
        env.define(name, f)
        return name
    else:
        raise SchemeError("bad argument to define")

def do_quote_form(vals):
    """Evaluate a quote form with parameters VALS."""
    check_form(vals, 1, 1)
    return vals.first


def do_let_form(vals, env):
    """Evaluate a let form with parameters VALS in environment ENV."""
    check_form(vals, 2)
    bindings = vals[0]
    exprs = vals.second
    if not scheme_listp(bindings):
        raise SchemeError("bad bindings list in let form")

    # Add a frame containing bindings
    names, values = nil, nil
    new_env = env.make_call_frame(names, values)
    for pair in bindings:
        name = pair[0]
        value = scheme_eval(pair[1], env)
        new_env.define(name, value)

    # Evaluate all but the last expression after bindings, and return the last
    last = len(exprs)-1
    for i in range(0, last):
        scheme_eval(exprs[i], new_env)
    return exprs[last], new_env


#########################
# Logical Special Forms #
#########################

def do_if_form(vals, env):
    """Evaluate if form with parameters VALS in environment ENV."""
    check_form(vals, 2, 3)
    expression = scheme_eval(vals[0], env)
    if scheme_true(expression):
        return vals[1]
    else:
        try:
            return vals[2]
        except IndexError:
            return okay

def do_and_form(vals, env):
    """Evaluate short-circuited and with parameters VALS in environment ENV."""
    if len(vals) == 0:
        return True
    for i in range(len(vals)):
        test = scheme_eval(vals[i], env)
        if scheme_false(test):
            return False
    else:
        return quote(test)

def quote(value):
    """Return a Scheme expression quoting the Scheme VALUE.

    >>> s = quote('hello')
    >>> print(s)
    (quote hello)
    >>> scheme_eval(s, Frame(None))  # "hello" is undefined in this frame.
    'hello'
    """
    return Pair('quote', Pair(value, nil))

def do_or_form(vals, env):
    """Evaluate short-circuited or with parameters VALS in environment ENV."""
    if len(vals) == 0:
        return False
    for i in range(len(vals) - 1):
        test = scheme_eval(vals[i], env)
        if scheme_true(test):
            return quote(test)
    else:
        return vals[len(vals) - 1]


def do_cond_form(vals, env):
    """Evaluate cond form with parameters VALS in environment ENV."""
    num_clauses = len(vals)
    for i, clause in enumerate(vals):
        check_form(clause, 1)
        if clause.first == "else":
            if i < num_clauses-1:
                raise SchemeError("else must be last")
            if clause.second is nil:
                raise SchemeError("badly formed else clause")
            test = True
        else:
            test = scheme_eval(clause.first, env)
        if scheme_true(test):
            if len(clause.second) == 0:
                return quote(test)
            elif len(clause.second) > 1:
                return Pair('begin', clause.second)
            else:
                return clause.second.first
    return okay

def do_begin_form(vals, env):
    """Evaluate begin form with parameters VALS in environment ENV."""
    check_form(vals, 1)
    while vals != nil:
        returned = scheme_eval(vals.first, env)
        vals = vals.second
    return quote(returned)

LOGIC_FORMS = {
    "and": do_and_form,
    "or": do_or_form,
    "if": do_if_form,
    "cond": do_cond_form,
    "begin": do_begin_form,
}

# Utility methods for checking the structure of Scheme programs

def check_form(expr, min, max=None):
    """Check EXPR (default SELF.expr) is a proper list whose length is
    at least MIN and no more than MAX (default: no maximum). Raises
    a SchemeError if this is not the case."""
    if not scheme_listp(expr):
        raise SchemeError("badly formed expression: " + str(expr))
    length = len(expr)
    if length < min:
        raise SchemeError("too few operands in form")
    elif max is not None and length > max:
        raise SchemeError("too many operands in form")

def check_formals(formals):
    """Check that FORMALS is a valid parameter list, a Scheme list of symbols
    in which each symbol is distinct.

    >>> check_formals(read_line("(a b c)"))
    >>> check_formals(read_line("(a b 1)"))
    Traceback (most recent call last):
    ...
    SchemeError: formal parameter 1 is not valid
    >>> check_formals(read_line("(a b b)"))
    Traceback (most recent call last):
    ...
    SchemeError: duplicate formal parameter 'b'
    """
    formals_set = set()
    while formals != nil:
        if formals.first in formals_set:
            raise SchemeError('duplicate formal parameter %r' % formals.first)
        if not scheme_symbolp(formals.first):
            raise SchemeError('formal parameter %r is not valid' % formals.first)
        formals_set.add(formals.first)
        formals = formals.second

##################
# Tail Recursion #
##################

def scheme_optimized_eval(expr, env):
    """Evaluate Scheme expression EXPR in environment ENV."""

    while True:

        if expr is None:
            raise SchemeError("Cannot evaluate an undefined expression.")

        # Evaluate Atoms
        if scheme_symbolp(expr):
            return env.lookup(expr)
        elif scheme_atomp(expr) or scheme_stringp(expr) or expr is okay:
            return expr

        # All non-atomic expressions are lists.
        if not scheme_listp(expr):
            # print(type(expr), 'WAITWAITWAITWAITWAITWAIT')
            raise SchemeError("malformed list: {0}".format(str(expr)))
        first, rest = expr.first, expr.second

        # Evaluate Combinations
        if (scheme_symbolp(first)  # first might be unhashable
                and first in LOGIC_FORMS):
            expr = LOGIC_FORMS[first](rest, env); continue
        elif first == "lambda":
            return do_lambda_form(rest, env)
        elif first == "mu":
            return do_mu_form(rest)
        elif first == "define":
            return do_define_form(rest, env)
        elif first == 'quote':
            return do_quote_form(rest)
        elif first == "let":
            expr, env = do_let_form(rest, env)
            continue
        else:
            procedure = scheme_eval(first, env)
            args = rest.map(lambda operand: scheme_eval(operand, env))

            if isinstance(procedure, PrimitiveProcedure):
                return apply_primitive(procedure, args, env)
            elif isinstance(procedure, LambdaProcedure):
                frame = procedure.env.make_call_frame(procedure.formals, args)
                expr = procedure.body; env = frame; continue
            elif isinstance(procedure, MuProcedure):
                frame = env.make_call_frame(procedure.formals, args)
                expr = procedure.body; env = frame; continue
            else:
                raise SchemeError("Cannot call {0}".format(str(procedure)))

################################################################
# Uncomment the following line to apply tail call optimization #
################################################################
# Regardless of whether or not you implemented the extra credit (question 23),
# when you submit leave the line that says "scheme_eval = scheme_optimized_eval" commented out.
# scheme_eval = scheme_optimized_eval


################
# Input/Output #
################

def read_eval_print_loop(next_line, env, quiet=False, startup=False,
                         interactive=False, load_files=()):
    """Read and evaluate input until an end of file or keyboard interrupt."""
    if startup:
        for filename in load_files:
            scheme_load(filename, True, env)
    while True:
        try:
            src = next_line()
            while src.more_on_line:
                expression = scheme_read(src)
                result = scheme_eval(expression, env)
                if not quiet and result is not None:
                    print(result)
        except (SchemeError, SyntaxError, ValueError, RuntimeError) as err:
            if (isinstance(err, RuntimeError) and
                    'maximum recursion depth exceeded' not in err.args[0]):
                raise
            print("Error:", err)
        except KeyboardInterrupt:  # <Control>-C
            if not startup:
                raise
            print("\nKeyboardInterrupt")
            if not interactive:
                return
        except EOFError:  # <Control>-D, etc.
            print()
            return


def scheme_load(*args):
    """Load a Scheme source file. ARGS should be of the form (SYM, ENV) or (SYM,
    QUIET, ENV). The file named SYM is loaded in environment ENV, with verbosity
    determined by QUIET (default true)."""
    if not (2 <= len(args) <= 3):
        vals = args[:-1]
        raise SchemeError("wrong number of arguments to load: {0}".format(vals))
    sym = args[0]
    quiet = args[1] if len(args) > 2 else True
    env = args[-1]
    if (scheme_stringp(sym)):
        sym = eval(sym)
    check_type(sym, scheme_symbolp, 0, "load")
    with scheme_open(sym) as infile:
        lines = infile.readlines()
    args = (lines, None) if quiet else (lines,)
    def next_line():
        return buffer_lines(*args)
    read_eval_print_loop(next_line, env.global_frame(), quiet=quiet)
    return okay

def scheme_open(filename):
    """If either FILENAME or FILENAME.scm is the name of a valid file,
    return a Python file opened to it. Otherwise, raise an error."""
    try:
        return open(filename)
    except IOError as exc:
        if filename.endswith('.scm'):
            raise SchemeError(str(exc))
    try:
        return open(filename + '.scm')
    except IOError as exc:
        raise SchemeError(str(exc))

def create_global_frame():
    """Initialize and return a single-frame environment with built-in names."""
    env = Frame(None)
    env.define("eval", PrimitiveProcedure(scheme_eval, True))
    env.define("apply", PrimitiveProcedure(scheme_apply, True))
    env.define("load", PrimitiveProcedure(scheme_load, True))
    add_primitives(env)
    return env

@main
def run(*argv):
    next_line = buffer_input
    interactive = True
    load_files = ()
    if argv:
        try:
            filename = argv[0]
            if filename == '-load':
                load_files = argv[1:]
            else:
                input_file = open(argv[0])
                lines = input_file.readlines()
                def next_line():
                    return buffer_lines(lines)
                interactive = False
        except IOError as err:
            print(err)
            sys.exit(1)
    read_eval_print_loop(next_line, create_global_frame(), startup=True,
                         interactive=interactive, load_files=load_files)
    tscheme_exitonclick()

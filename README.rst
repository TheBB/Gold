Gold language
=============

*Gold* is a programmable configuration language. Using Gold, you can produce
JSON-like data structures using familiar programming concepts.  It is inspired
by `Dhall`_, but it is less rigidly typed and therefore more flexible.

When a Gold file is evaluated, it produces a JSON-like value:

- an atomic type like a number (integer or double), string, boolean or null
- a composite type like a list or an object
- a function

Functions are the only non-JSON data type that Gold can produce. Although
functions are primarily intended to assist in the production of more complicated
or oft-repeated configuration structures, applications may still treat functions
as a first-class configuration value.

All Gold objects are immutable and non-self-referential.  Without exception,
unchanged Gold files always evaluate to the same values (assuming imported files
have not been changed), and the evaluation of a Gold script may not have side
effects.  The Gold language does not have statements, only expressions.


Basic data types
----------------

The basic data types in Gold are integers::

    1
    -5
    +13

floating-point numbers (treated as double-precision)::

    1.01
    .15
    -2.
    15e2
    -3e-1

strings, which are double-quoted::

    "text"
    ""
    "with typical escape sequences: \n, \b, \f, \r, \t, \\ and \""
    "as well as unicode: \u1bef"

and also supports interpolation of other values::

    let a = "Gold" in "this language is $a"
    # => "this language is Gold"

Longer strings can be concatened by juxtaposition::

    "here\n" "is\n" "a\n" "multiline\n" "string\n"

(See also multiline strings in objects, below.)

Finally, there are of course *null* and the two booleans *true* and *false*.


Lists
-----

Lists are formed, as in JSON, using square brackets::

    [1, 2, 3]

There's no requirement that a list be homogeneous, so this also works::

    ["a", -1, true]

Unlike JSON, a trailing comma is acceptable in Gold. This applies not only for
lists, but *all* list-like syntactical structures::

    [1, 2, 3,]

It is recommended to use a trailing comma when a list goes over multiple lines::

    [
        1,
        2,
        3,
    ]


Objects
-------

Gold's object notation will be familiar to Javascript programmers::

    {
        number: 1,
        string: "alpha",
        list: [2, 3, 4],
    }

Object keys are treated as literal values, not as variables. To use a
dynamically computed key, use interpolation syntax::

    let a = "b" in {$a: 1}              # => {b: 1}

Or use literal string syntax for keys which cause syntax problems::

    {"key:with:colons": 1}


Multiline strings
-----------------

For constructing objects with long strings, or even just short strings for which
you don't want to type quotation marks all the time, Gold offers multiline
string support::

    {
        name:: Bob the Builder
        weapon:: Hammer
    }

The double colon initiates a multiline string. The actual string contents start
from the next non-whitespace character, and runs until the next line whose
indentation is not greater than the line that started the string::

    {
        description:: Here starts some long text
            it continues here
        comment:: But this is a new one
    }

Note commas are not needed at the end of these strings to separate object items,
and indeed they will be counted as part of the string if present.

Indentation for lines after the first one is removed. If the lines have variable
indentation, the indentation corresponding to the least-indented line is
removed.


Let-bindings
------------

To bind objects to names, use the structure::

    let name = expr
    let othername = otherexpr
    in finalexpr

The bindings *name* and *othername* are visible in the expression *finalexpr*.
For example::

    let x = 1
    let y = 2
    in x + y  # => 3

Moreover, later bindings may make use of earlier bindings::

    let x = 1
    let y = x + 1  # => 2
    let z = y + 1  # => 3
    in x + y + z   # => 6

The bindings produced by a let-expression vanish after the final expression
(after *in*) is evaluated, and they are not visible anywhere else.


String interpolation
--------------------

Gold allows string interpolation using the syntax ``${...}``, with arbitrary
expressions allowed inside the curly braces::

    let x = 1
    let y = 2
    in "the sum of ${x} and ${y} is ${x+y}"

The value of the expression is stringified using the *str()* function (see
below), which admits all basic data types (numbers, booleans, null and other
strings), but not lists, objects or functions.

String interpolation can be suppressed by escaping the dollar sign::

    "this \${string} is not interpolated"


Branching
---------

Gold has an if-then-else structure::

    let cond = true
    in if cond then "yes" else "no"         # => "yes"

Because this must produce a value in all cases (it is an expression, not a
statement), it is not possible to omit the *else* branch.

In Gold, only *false*, *null* and zeros are treated as falsy values. Everything
else is truthy, including empty lists and objects!


Indexing
--------

You may use typical indexing syntax to extract values from lists and objects::

    let mylist = [1, 2, 3]
    let myobj = {a: 1, b: 2, c: 3}
    in [mylist[0], myobj["c"]]          # => [1, 3]

Objects support the more familiar dot-based syntax as well::

    let mylist = [1, 2, 3]
    let myobj = {a: 1, b: 2, c: 3}
    in [mylist[0], myobj.c]             # => [1, 3]


Functions
---------

Functions are defined using the syntax::

    |param1, param2, ...| expression

Functions in Gold are always anonymous, and must be called immediately or bound
to a name to have an effect, e.g.::

    let add = |x, y| x + y
    in add(1, 2)                    # => 3

or::

    (|x, y| x + y)(1, 2)            # => 3

Functions may take any number of parameters (including none at all) and form
closures non-local names, for example::

    let make_adder = |x| |y| x + y
    let adder = make_adder(3)
    let x = 4
    in adder(5)             # => 8

The value of *x* referred to by the return value of the *make_adder* function is
untainted by the later binding of *x*.

Functions may take positional as well as keyword parameters.  Positional and
keyword parameters are separated by a semicolon::

    |x; y| x + y

Keyword arguments are provided similary to object notation, so the previously
defined function may be called as such::

    let add = |x; y| x + y
    in add(1, y: 2)         # => 3

but not in either of these ways::

    add(1, 2)               # => error
    add(x: 1, y: 2)         # => error

Functions which only accept keyword arguments can be defined with the
alternative syntax::

    {|x, y, z|} x + y + z

rather than the slightly ugly (although perfectly legal)::

    |; x, y, z| x + y + z


Arithmetic and other operators
------------------------------

Gold supports standard arithmetical and logical operators, listed here in order
of precedence:

- ``^`` for exponentiation (whose result is always a floating point number)
- ``*``, ``/``, ``//`` for multiplication, true division and integer division
- ``+``, ``-`` for addition and subtraction
- ``<``, ``>`` ``<=``, ``>=`` for inequality comparison
- ``==``, ``!=`` for equality comparison
- ``has`` for containment check (works with lists and strings)
- ``and`` for logical conjunction
- ``or`` for logical disjunction

The logical operators are, of course, short-circuiting, although in a language
without side effects this is just a performance benefit rather than a semantic
requirement.

In addition, Gold has two unary prefix operators:

- ``-`` for unary negation
- ``not`` for logical negation

The power operator binds tighter than unary operators on the right, but not on the
left, so that ``-2^2`` evaluates to -4.  In every other case, postfix operators
(indexing and function calls) bind tighter than prefix operators, which in turn
bind tighter than binary operators.

All binary operators associate to the left, except for the power operator, which
associates to the right.


Destructuring
-------------

Gold supports advanced destructuring in let-bindings. For example, the
following works::

    let mylist = [1, 2, 3]
    let [a, b, c] = mylist
    in a + b + c        # => 6

It is also possible to destructure objects::

    let myobj = {a: 1, b: 2, c: 3}
    let {a, b, c} = myobj
    in a + b + c        # => 6

When destructuring objects, it's possible to differentiate between the name of a
key and the name of the binding::

    let myobj = {a: 1, b: 2, c: 3}
    let {a as x, b as y, c as z} = myobj
    in x + y + z        # => 6

For both list and object destructuring, it's possible to provide default
values::

    let mylist = [1, 2]
    let [a, b, c = 3] = mylist
    in a + b + c        # => 6

    let myobj = {a: 1, b: 2}
    let {a, b, c = 3} = myobj
    in a + b + c        # => 6

You can always use the ellipsis syntax to "slurp" remaining values in both lists
and objects::

    let mylist = [1, 2, 3, 4]
    let [_, ...x] = mylist
    in x                # => [2, 3, 4]

    let myobj = {a: 1, b: 2, c: 3}
    let {a, ...x} = myobj
    in x                # => {b: 2, c: 3}

Destructuring a list that is too long will result in an error.  If this is
intended, you may use an anonymous slurp::

    let mylist = [1, 2, 3, 4]
    let [x, ...] = mylist
    in x                # => 1

    let mylist = [1, 2, 3, 4]
    let [x] = mylist    # => error

No such requirements exist for objects, however: the presence of key-value pairs
on the right which are not captured on the left is not a problem.

Naturally, destructuring patterns may be arbitrarily deep::

    let myobj = {a: [{b: [{c: 1}]}]}
    let {a as [{b as [{c}]}]} = myobj
    in c                # => 1


Destructuring in functions
--------------------------

Syntactically, the positional and keyword parameters in function definitions are
equivalent to list and object destructuring expressions, respectively.  This
means that all the syntax discussed above works there too.  In particular,
default values are possible::

    let add = |x, y = 2| x + y
    in add(1)           # => 3

    let add = |; x = 1, y = 2| x + y
    in add()            # => 3

You can also slurp positional and keyword arguments::

    let test = |...args; ...kwargs| [args, kwargs]
    in test(1, 2, x: 3)     # => [[1, 2], {x: 3}]

And you may *splat* them when calling::

    let test = |...args; ...kwargs| [args, kwargs]
    let args = [1, 2]
    let kwargs = {x: 3}
    in test(...args, ...kwargs)     # => [[1, 2], {x: 3}]


Advanced collections
--------------------

Inspired by `Dart`_, Gold supports a handful of syntactical structures that
facilitate easy building of complicated lists and objects.

Elements can be made conditional (known in Dart as *collection if*)::

    let buildlist = |x| [1, when x > 3: x, 3]
    in buildlist(4)         # => [1, 4, 3]

but::

    in buildlist(2)         # => [1, 3]

Moreover, elements can be produced in a loop (known in Dart as *collection
for*)::

    # This function does the same thing as the built-in range(n)
    let buildlist = |n| [for x in range(n): x]
    in buildlist(2)         # => [0, 1]

However, the previous example could also be written using splat syntax,
which is the inverse of slurping in destructuring expressions::

    let buildlist = |n| [...range(n)]
    in buildlist(2)         # => [0, 1]

All the above structures work equivalently in objects, excepting that keys must
be provided::

    let buildobj = |x| {a: 1, when x > 3: x: x, c: 3}
    in buildobj(4)          # => {a: 1, x: 4, c: 3}

You can use the built-in *items* function to produce an object like this::

    let buildobj = |list| {for [key, val] in list: key: val}
    in buildobj([["a", 1], ["b", 2]])

However, this example will not work properly, because the ``key: val`` structure
uses *key* as a *literal key*, not as a reference to the bound name.  You can use
``$`` syntax instead, to obtain the desired result::

    let buildobj = |list| {for [key, val] in list: $key: val}
    in buildobj([["a", 1], ["b", 2]])       # => {a: 1, b: 2}

This is a handy utility to build objects with dynamically defined keys.  Just be
aware that, while other languages may allow you to use non-string keys in a hash
map, Gold does not::

    let x = 1
    in {$x: 1}          # => error


Built-in functions
------------------

Gold provides the following built-in functions:

- *int(x)* - convert its argument to an integer
- *bool(x)* - convert its argument to a boolean (as per branching rules)
- *str(x)* - convert its argument to a string
- *float(x)* - convert its argument to a floating point number
- *len(x)* - return the number of items in a list or object
- *range(n)* - return the list of integers from zero up to (and not including) *n*
- *map(f, x)* - return the list ``[for y in x: f(y)]``
- *filter(f, x)* - return the list ``[for y in x: if f(y): y]``
- *items(x)* - return a list of key-value pairs of the object *x*
- *exp(x, base=e)* - raise *base* to the power *x*
- *log(x, base=e)* - take the logarithm of *x* in base *base*
- *ord(x)* - return the ASCII index of the only character in the string *x*
- *chr(x)* - return a single-character string from the integer ASCII code *x*
- *isint(x)* - return true if *x* is an integer
- *isstr(x)* - return true if *x* is a string
- *isnull(x)* - return true if *x* is null
- *isbool(x)* - return true if *x* is a boolean
- *isfloat(x)* - return true if *x* is a floating-point number
- *isobject(x)* - return true if *x* is an object
- *islist(x)* - return true if *x* is a list
- *isfunc(x)* - return true if *x* is a function


Importing libraries
-------------------

You can write Gold code and data that can be imported in other files. The
*import* statement takes a path to a file (relative to the
file currently being loaded) which will be evaluated.  Its result will then be
bound to a name (or destructured).

This can be used to write libraries of functions, e.g. assume this is the
contents of the file ``mylib.gold``::

    {
        add: |x, y| x + y,
    }

The function *add* can be used from another file like this::

    import "mylib.gold" as mylib
    in mylib.add(1, 2)

or, more idiomatically, like this, using destructuring::

    import("mylib.gold") as { add }
    in add(1, 2)

Of course, there is no requirement that a file must evaluate to an object. For
the single function *add*, this would work just as well::

    # mylib.gold
    |x, y| x + y

    # other file
    import "mylib.gold" as add
    in add(1, 2)

In spite of this, libraries of functions should generally be written as objects.


Recursion
---------

Gold functions form a closure over non-local names when they are defined, and
they do so before they themselves are bound to a name.  It is therefore
impossible to define a recursive function like you would normally do it, e.g.::

    let factorial = |n| if n > 0 then n * factorial(n-1) else 1
    in factorial(4)

Indeed, this closure would be self-referential, and Gold is unable to define
self-referential structures.

This would cause an error indicating that the name *factorial* is unbound.

It is possible to do recursion by providing a function with itself as an
argument::

    let factorial = |f, n| if n > 0 then n * f(f, n-1) else 1
    in factorial(factorial, 4)              # => 24

This slightly unwieldy interface can be fixed using a helper function::

    let factorial = |n| (
        let inner = |f, n| if n > 0 then n * f(f, n-1) else 1
        in inner(inner, n)
    )

    in factorial(4)                         # => 24


.. _Dhall: https://dhall-lang.org/
.. _Dart: https://dart.dev/

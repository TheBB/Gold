# Whirlwind tour


## Core features of Gold

A Gold file consists of an arbitrary number of top-level statements, of which
currently there is only one type: imports. These top-level statements are then
followed by a *single* expression. The value of this expression is the value of
the file when evaluated.

A Gold program cannot affect its environment in any way: it cannot write files
to the disk, make network requests, etc. It also cannot (for the moment) read
environment variables. The only data available to a Gold program is the data in
the file itself, and other files that it imports. As such, the value of a Gold
file when evaluated is necessarily fixed and immutable and a faithful
representation of the source files: it cannot change if the the source files
also don't change.

Aside from the top-level import statements, Gold only has expressions - no
statements. Furthermore, every Gold value is immutable.

Except in very specific circumstances, Gold is whitespace and indentation
insensitive. In every case where comma-separated lists are expected, Gold allows
an optional trailing comma.

Comments are starting with a pound character `#` and last until the end of the
line.


## Types

Gold support all the JSON-like types, with the important addition of
*functions*. In addition to this, Gold distinguishes integers and floating-point
*numbers.

- integers: `0`, `1`, `-3` etc.,
- floating-point numbers: `1.0`, `3.14`, `0.2718e-1` etc.,
- strings, which are double-quoted: `""`, `"Hello World"` etc.,
- the singleton objects *null*, *true* and *false*,
- lists of other values,
- objects (mappings of strings to other values) and
- functions.


## Lists

Lists are constructed with square brackets surrounding a comma-separated list of
values.

```
[0, 1.0, "here is a string"]
```

An empty list is just

```
[]
```

Use square brackets to index a list and extract its elements

```
["a", "b", "c"][1]   # => "b"
```

In Gold, indexing is zero-based.


## Objects

Objects are constructed with curly brackets surrounding a comma-separated list of key-value pairs. The key and the value are themselves separated by a colon. In most cases it's not necessary to quote the key.

```
{
    my-key: "value",
    my-other-key: "some other value",
}
```

Quoting the key is necessary if it contains a colon, or if it starts with a quotation mark.

```
{
    "with-colon:": true,
    "\"with-quote": true,
}
```

An empty object is just

```
{}
```

Gold does not currently support objects whose keys are not strings.

Use dot-access syntax to access values from an object, in case the key is compatible with Gold syntax:

```
{x: 1}.x   # => 1
```

But this wouldn't work, since the hyphen is interpreted as a minus operator:

```
{some-key: 1}.some-key
```

In this case, rely on explicit indexing with square brackets:

```
{some-key: 1}["some-key"]   # => 1
```


## Binding names

To bind values to names, use the *let* expression:

```
let x = 1
in 2 + x
```

You can bind multiple names at once:

```
let x = 1
let y = 2
in x + y
```

After a sequence of bindings and the keyword `in` follows a *single* expression
in which all names bound previously are valid. The value of this expression
becomes the value of the whole let-expression.


## Destructuring

In let-expressions (and anywhere else where values are bound to names, see
[Advanced collections](#advanced-collections) and [Functions](#functions)),
Gold support destructuring assingments.

You can destructure lists:

```
let [a, b, c] = [1, 2, 3]
in a + b + c
```

and objects:

```
let {a, b, c} = {a: 1, b: 2, c: 3}
in a + b + c
```

Use the `as` keyword in object destructuring to use a different bound name than
the key in the object:

```
let {a as x, b as y, c as z} = {a: 1, b: 2, c: 3}
in x + y + z
```

In both list and object destructuring contexts, you can provide default values
if the right hand side lacks the relevant values:

```
let [a, b, c = 3] = [1, 2]
in a + b + c

let {a, b, c = 3} = {a: 1, b: 2}
in a + b + c
```

Destructuring a list that is too long is an error:

```
let [a, b, c] = [1, 2, 3, 4]   # Error here!
in a + b + c
```

To explicitly ignore extraneous values, slurp them by using the ellipsis
operator:

```
let [a, b, c, ...] = [1, 2, 3, 4]
in a + b + c
```

or, if the extraneous values are important, bind them to a name too. This will
produce a list called `rest`:

```
let [a, b, c, ...rest] = [1, 2, 3, 4]
in a + b + c + rest[0]
```

You can also collect extraneous key-value pairs in an object:

```
let {a, b, ...rest} = {a: 1, b: 2, c: 3, d: 4}
in a + b + rest.c + rest.d
```

Note that destructuring an object with too many keys *is not an error*, so there
is no need to do something like this:

```
let {a, b, ...} = {a: 1, b: 2, c: 3}
in a + b
```

And, in fact, that syntax is not valid. Instead, his will work just fine:

```
let {a, b} = {a: 1, b: 2, c: 3}
in a + b
```

You can also perform destructuring several levels deep. This pattern, for
example, will extract the key `c: 1` inside a list in an object in a list in an
object:

```
let {a as [{b as [{c}]}]} = {a: [{b: [{c: 1}]}]}
in a
```


## Branching

Gold has a single branching expression:

```
if condition then expression else expression
```

Since this is an expression (like everything else in Gold), the *else* branch is
not optional.

The value of *condition* can be anything - not just *true* or *false*. For the purposes of branching,
everything is considered *true* except

- *false*
- *null*
- the integer `0` and the floating-point value `0.0`

Notably, empty lists and objects are considered truthy.


## Advanced collections

Gold supports a number of features for easily performing advanced logic when
constructing collections (lists and objects). This is useful because, Gold
objects being immutable, it's not possible to initialize e.g. and empty list and
then fill it later, which you might do in Python:

```python
mylist = []
# fill mylist with elements
```

First, it's possible to conditionally add elements:

```
[
    1,
    if condition: 2,
    3,
]
```

This may evaluate to `[1, 2, 3]` or `[1, 3]` depending on whether the condition
is satisfed. Note that this is very different from the following:

```
[
    1,
    if condition 2 else null,
    3,
]
```

which is a list that *always* contains three elements: either `[1, 2, 3]` or
`[1, null, 3]`.

It's also possible to loop over an existing collection to add its elements to a
new collection:

```
let numbers = [3, 4]
in [
    1,
    2,
    for n in numbers: n,
    5,
]
```

which evaluates to `[1, 2, 3, 4, 5]`. For this usage, the following usage of the
splicing operator `...` is equivalent, and probably preferred:

```
let numbers = [3, 4]
in [1, 2, ...numbers, 5]
```

But the `for x in y` syntax has two important advantages. First, it is possible
to perform destructuring:

```
let numbers = [[3], [4]]
in [
    1,
    2,
    for [n] in numbers: n,
    5,
]
```

Second, the value produced may be any expression, so that this will also work:

```
let numbers = [[3], [4]]
in [
    1,
    2,
    for n in numbers: n[0],
    5,
]
```

And, indeed, loops and conditions may be nested arbitrarily deep:

```
# Extract the names of all adults
let people = [
    {name: "Bob", age: 42},
    {name: "Eve", age: 24},
    {name: "Jill", age: 12},
    {name: "Adam", age: 15},
    {name: "Patricia", age: 72},
]
in [
    for {name, age} in people:
        if age > 18: name
]
```

All the above works equally well with objects as with lists, with one important
caveat. Consider the following modification of the above code to filter a list
of people to obtain a list of adults.

```
# Extract ages of all adults
# ...
in {
    for {name, age} in people:
        if age > 18:
            name: age
}
```

We only needed to use curly braces instead of square ones, and change `name`
into `name: age` for the result to be a valid object. However, this will not
work as expected. The reason is that in an object, `{name: age}` interprets
`name` as the literal key, not a bound name to look up.

This can be fixed using [string interpolation](#advanced-strings):

```
# ...
in {
    for {name, age} in people:
        if age > 18:
            "$name": age
}
```

However, this particular use-case is common enough that Gold supports the
alternative syntax `$key: value`


```
# ...
in {
    for {name, age} in people:
        if age > 18:
            $name: age
}
```


## Advanced strings

Gold supports string interpolation of other values:

```
let a = "Gold"
in "This language is $a"
```

To explicitly demarcate the expression to be interpolated, use curly braces.
This allows usages like the following, to prevent Gold looking for the binding
`prefixflammable`:

```
let prefix = "in"
in "Be careful with ${prefix}flammable objects"
```

and the following, where the expression to be interpolated is more sophisticated
than just a name:

```
"1 + 2 is ${1 + 2}"
```

Gold does not currently support format specifiers in string interpolation.

To facilitate long strings, Gold supports juxtaposition:

```
"here\n"
"is\a"
"multiline\n"
"string\n"
```

Note that the newlines must still be explicitly provided: juxtaposition is just
concatenation - no extra characters are added between each part.

To facilitate writing objects with string values, which is common in many
configuration files, Gold provides the following long-form string syntax:

```
{
    key:: Some text goes here
    normal-key: false,
}
```

After a double colon, the string is read from the first non-whitespace character
until the end of the last line that precedes a line that is indented *not more
than* the line where the string started. In this example, that line is the third
line with the closing brace, which means that the string just contains the text
`"Some text goes here"`.

Note that there is *no comma* after such a string before the next element of the
object. If there were, it would be treated as part of the string, not a
syntactical element.

You can use this to create multiline strings too:

```
{
    key:: This is the first line,
        this is the second line,
        and this is the third line.
    other-key: true,
}
```

From the second line forward, the greatest common indentation is stripped from
all lines. Thus the string above could also be rendered as

```
"This is the first line,\nthis is the second line,\nand this is the third line."
```

If the first line is empty, it is ignored. Extra indentation is not stripped:

```
{
    example::
        # This is a faithful representation of Python code with indentation
        def func(x, y):
            return x + y
        print(func(1, 2))
}
```


## Functions

Functions are defined using the syntax

```
|param1, parm2, ...| expression
```

Where *expression* may depend on the values of *param1*, *param2*, etc.

Functions in Gold are always anonymous, and must be called immediately or bound
to a name to have an effect. For example:

```
let add = |x, y| x + y
in add(1, 2)
```

or

```
(|x, y| x + y)(1, 2)
```

Functions may take any number of parameters (including none at all), and form
closures around non-local names. For example:

```
let make_adder = |x| |y| x + y
let adder = make_adder(3)
let x = 4
in adder(5)
```

The `make_adder` function is a function that returns a function. The value of
*x* referred to by the function *adder* is enclosed over and is untainted by the
later binding of *x* to 4.

Functions may take positional as well as keyword parameters. The two kinds of
parameters are separated by a semicolon:

```
|x; y| x + y
```

This function can be called in this way:

```
let add = |x; y| x + y
in add(1, y: 2)
```

but not in either of these ways:

```
add(1, 2)
add(x: 1, y: 2)
```

In Gold, positional and keyword parameters are strictly distinct.

Functions which only accept keyword parameters can be defined with the
alternative syntax:

```
{|x, y, z|} x + y + z
```

Althouth this is perfectly valid (although somewhat ugly):

```
|; x, y, z| x + y + z
```

Function parameters are syntactically equivalent to list and object
destructuring expressions, respectively. Anything that works in those contexts
also works in function definitions:

```
let sum_first_elements = |[x, ...], [y, ...]| x + y
in sum_first_elements([1, 2], [3, 4])
```

Most notably, default parameter values:

```
|x, y = 2; multiply = false| if multiply then x * y else x + y
```


## Importing

Gold supports importing code and data from other files. The *import* statement
takes a path to a file, which is always relative to the file currently being
loaded. Gold then evaluates that file and assigns the resulting value to a name
or a destructuring pattern.

This can be used to write libraries of functions. If this is the contents of the
file `mylib.gold`:

```
{
    add: |x, y| x + y,
}
```

The function *add* can then be used from another file like this:

```
import "mylib.gold" as mylib
mylib.add(1, 2)
```

or like this:

```
import "mylib.gold" as {add}
add(1, 2)
```

Of course, there is no requirement that the value of an imported file must be an
object. For the single function *add*, the following would work just as well:

```
# mylib.gold
|x, y| x + y

# Other file
import "mylib.gold" as add
add(1, 2)
```

Imports are *statements* and must be found at the beginning of a file preceding
the expression to evaluate. It is not possible to import files mid-evaluation.

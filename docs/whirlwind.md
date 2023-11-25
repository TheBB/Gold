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
- the singleton objects `null`, `true` and `false`,
- lists of other values,
- objects, mappings of strings to other values, and
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


## Binding names


## Branching


## Pattern matching


## Splicing and slurping


## Advanced collections


## String interpolation


## Multiline text


## Functions


## Importing

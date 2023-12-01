# String formatting

Gold supports string formatting specifiers, similar to what you see in many
other languages, for specifying how a value should be formatted when used in a
string interpolation context:

```
"Here is a number: ${number:.2f}"
```

This will format a number using two digits after the decimal point.

The format specifier follows the expression to interpolate and is separated from
it by a colon.

```
"${expr:format}
```

The format string adheres to the following syntax, which should be fairly
familiar if you have used such features in other languages:

```
[[fill]align][sign]['#']['0'][width][grouping][.precision][type]
```


## Fill and align

The alignment `align`, if present, should be one of the following characters:

- `<`: indicates that the value should be left-aligned within its space.
- `>`: indecates that the value should be right-aligned within its space.
- `^`: indicates that the value should be centered within its space. In case
  there is an odd number of available columns, the value will be shifted one
  character to the left.
- `=`: for numbers, indicates that the sign (if any) should be left-aligned and
  that the value should be right-aligned.

The `fill` character, if present, is used to fill the remaining columns. The
default fill is a whitespace.

By default, numbers are aligned to the right and text values are aligned to the
left.

In most cases the fill and align settings are not useful unless `width` is also
specified, since then the value will be formatted using exactly the required
amount of space.


## Sign

For numbers, `sign` should be one of the following characters:

- `+`: indicates that the sign should always be printed, using `+` for
  nonnegative numbers and `-` for negative ones.
- `-`: indicates that the sign should only be printed for negative numbers.
- ` ` (a whitespace): indicates that the sign only be printed for negative
  numbers, and that a single whitespace be used in place for plus for
  nonnegative numbers.


## Alternate form

The presence of `#` indicates printing in alternate form. For numbers printed in
non-decimal form, this will add a `0x`, `0X`, `0b` or `0o` for hexadecimals
(lowercase or uppercase), binary or octal numbers, respectively. This indicator
will be placed *before* the number but *after* the sign (if present). In case
the alignment option `=` is used, it will also be placed *before* the fill
characters.


## Zero padding

The presence of `0` is equivalent to a fill and align specifier of `0=`. That
is, numbers will be zero-padded to the left to fill the available space, after
the sign (if any).


## Width

The `width` specifier should be any nonnegative integer indicating the *minimum
width* that the value should take up. There is no requirement that the value
cannot use more space if required.


## Grouping

Enable the *grouping* option to print separators between every third digit (in
decimal form) or every fourth digit (in binary, octal or hexadecimal form). The
available options are:

- `,`: use a comma as separator
- `_`: use an underscore as separator


## Precision

For floating-point numbers, the precision should be a nonnegative integer
indicating how many digits after the decimal separator to print.


## Formatting type

The final character, if present, indicates what type of formatting to use. They
are divided into three major families: strings, integers and floating-point
numbers. The family used influences how certain types are interpreted:

- Strings must be formatted as strings, and cannot be used with numerical format
  specifiers.
- Integers must be formatted as integers or floating-point numbers.
- Booleans are formatted as strings if possible, then integers or floating-point
  numbers if not. When interpreted as numbers, `true` is 1 and `false` is 0.
- Null is interpreted as a string, never as a number.
- Lists and objects cannot be formatted this way.


### Formatting strings

The only string formatting type is `s`. This is the default if the value being
formatted is a string, a boolean or null.


### Formatting integers

The available formatting types are:

- `b`: format the number in binary form.
- `c`: interpret the number as a unicode codepoint and print the respective
  character.
- `d`: format the number in decimal form. This is the default if the value being
  formatted is an integer.
- `o`: format the number in octal form.
- `x`: format the number in hexadecimal form using lowercase letters a-f.
- `X`: format the number in hexadecimal form using uppercase letters A-F.


### Formatting floating-point numbers

The available formatting types are:

- `e`: format the number in scientific form (mantissa and exponent) using a
  lowercase 'e'.
- `E`: format the number in scientific form (mantissa and exponent) using an
  uppercase 'E'.
- `f`: format the number in fixed-point form, using a number of digits indicated
  by the precision specifier (default 6).
- `g`: format the number using the number of digits required for an unambiguous
  representation. This is the default if the value being formatted is a
  floating-point number. If the precision is provided, the default is `f`
  instead.
- `%`: multiply the number by 100 and format as with `f`, printing a trailing
  percentage symbol.

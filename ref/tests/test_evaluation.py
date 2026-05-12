from __future__ import annotations

import math

import pytest

from ref.evaluation import EvalError, GoldBuiltin, GoldFunction, evaluate_source


def ev(src: str) -> object:
    return evaluate_source(src)


# ── Literals ──────────────────────────────────────────────────────────────────


def test_integer() -> None:
    assert ev("42") == 42
    assert ev("-1") == -1


def test_float() -> None:
    assert ev("3.14") == pytest.approx(3.14)


def test_bool() -> None:
    assert ev("true") is True
    assert ev("false") is False


def test_null() -> None:
    assert ev("null") is None


def test_string_literal() -> None:
    assert ev('"hello"') == "hello"


def test_string_escape() -> None:
    assert ev(r'"a\"b"') == 'a"b'
    assert ev(r'"a\\b"') == "a\\b"
    assert ev(r'"a\$b"') == "a$b"


# ── Arithmetic ────────────────────────────────────────────────────────────────


def test_add_ints() -> None:
    assert ev("1 + 2") == 3


def test_add_floats() -> None:
    assert ev("1.0 + 2.0") == pytest.approx(3.0)


def test_add_mixed() -> None:
    assert ev("1 + 2.0") == pytest.approx(3.0)


def test_subtract() -> None:
    assert ev("10 - 3") == 7


def test_multiply() -> None:
    assert ev("4 * 5") == 20


def test_divide() -> None:
    assert ev("7 / 2") == pytest.approx(3.5)


def test_integer_divide() -> None:
    assert ev("7 // 2") == 3


def test_power() -> None:
    assert ev("2 ^ 10") == 1024
    assert isinstance(ev("2 ^ 10"), int)


def test_power_negative_exp() -> None:
    result = ev("2 ^ -1")
    assert result == pytest.approx(0.5)
    assert isinstance(result, float)


def test_negate() -> None:
    assert ev("-5") == -5
    assert ev("-3.0") == pytest.approx(-3.0)


def test_string_concat() -> None:
    assert ev('"foo" + "bar"') == "foobar"


def test_list_concat() -> None:
    assert ev("[1, 2] + [3, 4]") == [1, 2, 3, 4]


# ── Comparisons ───────────────────────────────────────────────────────────────


def test_comparisons() -> None:
    assert ev("1 < 2") is True
    assert ev("2 < 1") is False
    assert ev("1 <= 1") is True
    assert ev("2 > 1") is True
    assert ev("1 == 1") is True
    assert ev("1 != 2") is True


def test_float_int_compare() -> None:
    assert ev("1 == 1.0") is True
    assert ev("1 < 1.5") is True


# ── Logic operators ───────────────────────────────────────────────────────────


def test_and_short_circuit() -> None:
    assert ev("false and 1/0") is False  # doesn't evaluate right side


def test_or_short_circuit() -> None:
    assert ev("true or 1/0") is True


def test_and_returns_value() -> None:
    assert ev("1 and 2") == 2
    assert ev("0 and 2") == 0


def test_or_returns_value() -> None:
    assert ev("0 or 2") == 2
    assert ev("1 or 2") == 1


def test_not() -> None:
    assert ev("not true") is False
    assert ev("not false") is True
    assert ev("not null") is True
    assert ev("not 0") is True


# ── Contains ─────────────────────────────────────────────────────────────────


def test_contains_list() -> None:
    assert ev("[1, 2, 3] has 1") is True
    assert ev("[1, 2, 3] has 4") is False


def test_contains_string() -> None:
    assert ev('"foobar" has "oo"') is True
    assert ev('"foobar" has "xyz"') is False


def test_contains_map() -> None:
    assert ev('{a: 1} has "a"') is True
    assert ev('{a: 1} has "z"') is False


# ── String interpolation ──────────────────────────────────────────────────────


def test_string_interpolation() -> None:
    assert ev('"${1 + 1}"') == "2"
    assert ev('"hello ${"world"}"') == "hello world"


def test_format_spec() -> None:
    assert ev('"${3.14:.2f}"') == "3.14"
    assert ev('"${42:05d}"') == "00042"
    assert ev('"${42:>10}"') == "        42"


# ── Branch ────────────────────────────────────────────────────────────────────


def test_branch() -> None:
    assert ev("if true then 1 else 2") == 1
    assert ev("if false then 1 else 2") == 2
    assert ev("if 0 then 1 else 2") == 2
    assert ev("if null then 1 else 2") == 2
    assert ev('if "" then 1 else 2') == 1  # empty string is truthy


# ── Let bindings ──────────────────────────────────────────────────────────────


def test_let() -> None:
    assert ev("let x = 10 in x") == 10


def test_let_sequential() -> None:
    assert ev("let x = 1 let y = x + 1 in y") == 2


def test_let_recursive() -> None:
    assert ev("let f = fn(n) if n <= 0 then 1 else n * f(n - 1) in f(5)") == 120


def test_let_mutual_recursion() -> None:
    src = """
    let isEven = fn(n) if n == 0 then true else isOdd(n - 1)
    let isOdd = fn(n) if n == 0 then false else isEven(n - 1)
    in isEven(4)
    """
    assert ev(src) is True


# ── Lists ─────────────────────────────────────────────────────────────────────


def test_list_literal() -> None:
    assert ev("[1, 2, 3]") == [1, 2, 3]


def test_list_splat() -> None:
    assert ev("[...[1, 2], 3]") == [1, 2, 3]


def test_list_for() -> None:
    assert ev("[for x in [1, 2, 3]: x * 2]") == [2, 4, 6]


def test_list_cond() -> None:
    assert ev("[for x in [1, 2, 3, 4]: when x > 2: x]") == [3, 4]


def test_list_index() -> None:
    assert ev("[10, 20, 30][1]") == 20
    assert ev("[10, 20, 30][-1]") == 30


# ── Maps ──────────────────────────────────────────────────────────────────────


def test_map_literal() -> None:
    assert ev("{a: 1, b: 2}") == {"a": 1, "b": 2}


def test_map_splat() -> None:
    assert ev("{...{a: 1}, b: 2}") == {"a": 1, "b": 2}


def test_map_for() -> None:
    assert ev('{for k in ["a", "b"]: $k: 1}') == {"a": 1, "b": 1}


def test_map_index() -> None:
    assert ev("{a: 42}.a") == 42


# ── Functions ─────────────────────────────────────────────────────────────────


def test_function_basic() -> None:
    assert ev("(fn(x) x + 1)(10)") == 11


def test_function_multi_arg() -> None:
    assert ev("(fn(x, y) x + y)(3, 4)") == 7


def test_function_keyword() -> None:
    assert ev("(fn(x; y) x + y)(1, y: 2)") == 3


def test_function_default() -> None:
    assert ev("(fn(x, y = 10) x + y)(5)") == 15
    assert ev("(fn(x, y = 10) x + y)(5, 3)") == 8


def test_function_slurp() -> None:
    assert ev("(fn(x, ...rest) rest)(1, 2, 3)") == [2, 3]


def test_closure() -> None:
    src = """
    let makeAdder = fn(n) fn(x) x + n
    let add5 = makeAdder(5)
    in add5(10)
    """
    assert ev(src) == 15


def test_function_is_value() -> None:
    result = ev("fn(x) x")
    assert isinstance(result, GoldFunction)


# ── Destructuring ─────────────────────────────────────────────────────────────


def test_list_destructure() -> None:
    assert ev("let [a, b] = [1, 2] in a + b") == 3


def test_list_destructure_slurp() -> None:
    assert ev("let [first, ...rest] = [1, 2, 3] in rest") == [2, 3]


def test_map_destructure() -> None:
    assert ev("let {a, b} = {a: 1, b: 2} in a + b") == 3


def test_map_destructure_default() -> None:
    assert ev("let {a, b = 99} = {a: 1} in b") == 99


# ── Built-ins ─────────────────────────────────────────────────────────────────


def test_builtin_len() -> None:
    assert ev("len([1, 2, 3])") == 3
    assert ev('len("hello")') == 5
    assert ev("len({a: 1, b: 2})") == 2


def test_builtin_range() -> None:
    assert ev("range(5)") == [0, 1, 2, 3, 4]
    assert ev("range(2, 5)") == [2, 3, 4]


def test_builtin_int() -> None:
    assert ev('int("42")') == 42
    assert ev("int(3.7)") == 4
    assert ev("int(true)") == 1


def test_builtin_float() -> None:
    assert ev('float("3.14")') == pytest.approx(3.14)
    assert ev("float(2)") == pytest.approx(2.0)


def test_builtin_str() -> None:
    assert ev("str(42)") == "42"
    assert ev("str(null)") == "null"
    assert ev("str(true)") == "true"


def test_builtin_bool() -> None:
    assert ev("bool(0)") is False
    assert ev("bool(1)") is True
    assert ev('bool("")') is True  # empty string is truthy in Gold


def test_builtin_map_filter() -> None:
    assert ev("map(fn(x) x * 2, [1, 2, 3])") == [2, 4, 6]
    assert ev("filter(fn(x) x > 2, [1, 2, 3, 4])") == [3, 4]


def test_builtin_items() -> None:
    assert ev("items({a: 1})") == [["a", 1]]


def test_builtin_type_predicates() -> None:
    assert ev("isint(42)") is True
    assert ev("isint(42.0)") is False
    assert ev('isstr("x")') is True
    assert ev("isnull(null)") is True
    assert ev("isbool(true)") is True
    assert ev("isfloat(1.0)") is True
    assert ev("isnumber(42)") is True
    assert ev("isnumber(1.0)") is True
    assert ev("isobject({})") is True
    assert ev("islist([])") is True
    assert ev("isfunc(fn(x) x)") is True


def test_builtin_ord_chr() -> None:
    assert ev('ord("A")') == 65
    assert ev("chr(65)") == "A"


def test_builtin_startswith_endswith() -> None:
    assert ev('startswith("foobar", "foo")') is True
    assert ev('endswith("foobar", "bar")') is True


def test_builtin_exp_log() -> None:
    assert ev("exp(1.0)") == pytest.approx(math.e)
    assert ev("log(1.0)") == pytest.approx(0.0)
    assert ev("exp(3.0, base: 2.0)") == pytest.approx(8.0)
    assert ev("log(8.0, base: 2.0)") == pytest.approx(3.0)


# ── Builtins as values ────────────────────────────────────────────────────────


def test_builtin_is_value() -> None:
    result = ev("len")
    assert isinstance(result, GoldBuiltin)
    assert result.name == "len"


def test_pass_builtin_to_map() -> None:
    assert ev("map(str, [1, 2, 3])") == ["1", "2", "3"]


# ── Error cases ───────────────────────────────────────────────────────────────


def test_undefined_name() -> None:
    with pytest.raises(EvalError, match="undefined name"):
        ev("x")


def test_call_non_function() -> None:
    with pytest.raises(EvalError):
        ev("42(1)")


def test_division_by_zero() -> None:
    with pytest.raises(EvalError):
        ev("1 / 0")


def test_type_mismatch() -> None:
    with pytest.raises(EvalError):
        ev("1 + true")


# ── Example files ─────────────────────────────────────────────────────────────


def test_fibonacci() -> None:
    result = ev("""
    let fib = fn(n) if n <= 1 then n else fib(n - 1) + fib(n - 2)
    in fib(10)
    """)
    assert result == 55

from __future__ import annotations

from pathlib import Path

import pytest

from ref.evaluation import evaluate_file_result
from ref.parser import parse

EXAMPLES = Path(__file__).parents[2] / "examples"
TESTDATA = Path(__file__).parents[2] / "testdata" / "examples"
ERRORS = Path(__file__).parents[2] / "testdata" / "errors"


def example_cases() -> list[str]:
    return sorted(p.stem for p in EXAMPLES.glob("*.gold"))


def error_cases() -> list[str]:
    return sorted(p.stem for p in ERRORS.glob("*.gold"))


@pytest.mark.parametrize("name", example_cases())
def test_example(name: str) -> None:
    source = (EXAMPLES / f"{name}.gold").read_text()
    expected = (TESTDATA / f"{name}.parse").read_text()
    result = parse(source)
    assert result.pprint(show_spans=True) == expected.rstrip("\n")


@pytest.mark.parametrize("name", error_cases())
def test_error(name: str) -> None:
    source = (ERRORS / f"{name}.gold").read_text()
    expected = (ERRORS / f"{name}.parse").read_text()
    result = parse(source)
    assert result.pprint(show_spans=True) == expected.rstrip("\n")


@pytest.mark.parametrize("name", example_cases())
def test_eval(name: str) -> None:
    expected = (TESTDATA / f"{name}.eval").read_text()
    result = evaluate_file_result(EXAMPLES / f"{name}.gold")
    assert result.pprint(show_spans=True) == expected.rstrip("\n")

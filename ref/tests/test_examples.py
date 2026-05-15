from __future__ import annotations

from pathlib import Path

import pytest

from ref.evaluation import evaluate_file_result, evaluate_source_result
from ref.parser import parse

EXAMPLES = Path(__file__).parents[2] / "examples"
TESTDATA = Path(__file__).parents[2] / "testdata" / "examples"
ERRORS = Path(__file__).parents[2] / "testdata" / "errors"
EVAL_FIXTURES = Path(__file__).parents[2] / "testdata" / "eval"


def example_cases() -> list[str]:
    return sorted(p.stem for p in EXAMPLES.glob("*.gold"))


def error_cases() -> list[str]:
    return sorted(p.stem for p in ERRORS.glob("*.gold"))


@pytest.mark.parametrize("name", example_cases())
def test_example(name: str) -> None:
    source = (EXAMPLES / f"{name}.gold").read_text(encoding="utf-8")
    expected = (TESTDATA / f"{name}.parse").read_text(encoding="utf-8")
    result = parse(source)
    assert result.pprint(show_spans=True) == expected.rstrip("\n")


@pytest.mark.parametrize("name", error_cases())
def test_error(name: str) -> None:
    source = (ERRORS / f"{name}.gold").read_text(encoding="utf-8")
    expected = (ERRORS / f"{name}.parse").read_text(encoding="utf-8")
    result = parse(source)
    assert result.pprint(show_spans=True) == expected.rstrip("\n")


@pytest.mark.parametrize("name", example_cases())
def test_eval(name: str) -> None:
    expected = (TESTDATA / f"{name}.eval").read_text(encoding="utf-8")
    result = evaluate_file_result(EXAMPLES / f"{name}.gold")
    assert result.pprint(show_spans=True) == expected.rstrip("\n")


def eval_fixture_cases() -> list[Path]:
    return sorted(EVAL_FIXTURES.rglob("*.gold"))


def test_eval_fixture_count() -> None:
    assert len(eval_fixture_cases()) == 434, "unexpected fixture count — did discovery break?"


@pytest.mark.parametrize(
    "gold_path", eval_fixture_cases(), ids=lambda p: str(p.relative_to(EVAL_FIXTURES).with_suffix(""))
)
def test_eval_fixture(gold_path: Path) -> None:
    source = gold_path.read_text(encoding="utf-8")
    expected = gold_path.with_suffix(".eval").read_text(encoding="utf-8")
    result = evaluate_source_result(source)
    assert result.pprint(show_spans=True) == expected.rstrip("\n")

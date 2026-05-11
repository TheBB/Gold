from __future__ import annotations

from pathlib import Path

import pytest

from ref.parser import parse

EXAMPLES = Path(__file__).parents[2] / "examples"
TESTDATA = Path(__file__).parents[2] / "testdata" / "examples"


def example_cases() -> list[str]:
    return sorted(p.stem for p in EXAMPLES.glob("*.gold"))


@pytest.mark.parametrize("name", example_cases())
def test_example(name: str) -> None:
    source = (EXAMPLES / f"{name}.gold").read_text()
    expected = (TESTDATA / f"{name}.out").read_text()
    result = parse(source)
    assert result.pprint(show_spans=True) == expected.rstrip("\n")

from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path
from typing import TYPE_CHECKING

import pytest

from ref.evaluation import PathImportResolver


if TYPE_CHECKING:
    from collections.abc import Callable, Iterator


EXAMPLE_PATH = Path(__file__).parents[2] / "examples"
TESTDATA_PATH = Path(__file__).parents[2] / "testdata"


@dataclass
class Fixture:
    source: Path
    parsed: Path | None = field(default=None)
    evaluated: Path | None = field(default=None)

    def read_source(self) -> str:
        return self.source.read_text(encoding="utf-8")

    def read_parsed(self) -> str:
        assert self.parsed is not None
        return self.parsed.read_text(encoding="utf-8").rstrip("\n")

    def read_evaluated(self) -> str:
        assert self.evaluated is not None
        return self.evaluated.read_text(encoding="utf-8").rstrip("\n")

    def resolver(self) -> PathImportResolver:
        return PathImportResolver(root=self.source.parent)

    def __str__(self) -> str:
        if self.source.is_relative_to(TESTDATA_PATH):
            return str(self.source.relative_to(TESTDATA_PATH).with_suffix(""))
        return self.source.stem


def make_parametrize(
    f: Callable[[], Iterator[Fixture]],
) -> Callable[[Callable[[Fixture], None]], pytest.MarkDecorator]:
    fixtures = list(f())
    names = [str(fixture) for fixture in fixtures]
    return pytest.mark.parametrize("fixture", fixtures, ids=names)


def example_fixtures() -> Iterator[Fixture]:
    for path in sorted(EXAMPLE_PATH.glob("*.gold")):
        path = path.relative_to(EXAMPLE_PATH)
        yield Fixture(
            source=EXAMPLE_PATH / path.name,
            parsed=TESTDATA_PATH / "examples" / path.with_suffix(".parse").name,
            evaluated=TESTDATA_PATH / "examples" / path.with_suffix(".eval").name,
        )


examples = make_parametrize(example_fixtures)


def eval_fixtures() -> Iterator[Fixture]:
    for path in sorted((TESTDATA_PATH / "eval").rglob("*.gold")):
        path = path.relative_to(TESTDATA_PATH / "eval")
        yield Fixture(
            source=TESTDATA_PATH / "eval" / path,
            parsed=TESTDATA_PATH / "eval" / path.with_suffix(".parse"),
            evaluated=TESTDATA_PATH / "eval" / path.with_suffix(".eval"),
        )


evals = make_parametrize(eval_fixtures)


def parse_fixtures() -> Iterator[Fixture]:
    for path in sorted((TESTDATA_PATH / "parse").rglob("*.gold")):
        path = path.relative_to(TESTDATA_PATH / "parse")
        yield Fixture(
            source=TESTDATA_PATH / "parse" / path,
            parsed=TESTDATA_PATH / "parse" / path.with_suffix(".parse"),
        )


parses = make_parametrize(parse_fixtures)

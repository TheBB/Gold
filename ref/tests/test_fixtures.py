from __future__ import annotations

from ref.evaluation import evaluate_source_result
from ref.parser import parse

from . import fixtures


def test_example_fixture_count() -> None:
    assert len(list(fixtures.example_fixtures())) == 14, "unexpected fixture count, did discovery break?"


@fixtures.examples
def test_example(fixture: fixtures.Fixture) -> None:
    result = parse(fixture.read_source())
    assert result.ok
    assert result.pprint(show_spans=True) == fixture.read_parsed()

    result = evaluate_source_result(
        fixture.read_source(),
        resolver=fixture.resolver(),
    ).pprint(show_spans=True)
    assert result == fixture.read_evaluated()


def test_eval_fixture_count() -> None:
    assert len(list(fixtures.eval_fixtures())) == 455, "unexpected fixture count, did discovery break?"


@fixtures.evals
def test_eval(fixture: fixtures.Fixture) -> None:
    result = parse(fixture.read_source())
    assert result.ok
    assert result.pprint(show_spans=True) == fixture.read_parsed()

    result = evaluate_source_result(
        fixture.read_source(),
        resolver=fixture.resolver(),
    ).pprint(show_spans=True)
    assert result == fixture.read_evaluated()


def test_parse_fixture_count() -> None:
    assert len(list(fixtures.parse_fixtures())) == 96, "unexpected fixture count, did discovery break?"


@fixtures.parses
def test_parse(fixture: fixtures.Fixture) -> None:
    result = parse(fixture.read_source()).pprint(show_spans=True)
    assert result == fixture.read_parsed()

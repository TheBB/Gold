from __future__ import annotations

import sys
from pathlib import Path

import click

from .evaluation import PathImportResolver, evaluate_file_result, evaluate_source_result
from .parser import parse as _parse


_TESTDATA = Path(__file__).parents[3] / "testdata"


@click.group()
def main() -> None:
    pass


@main.command()
@click.argument("file", default="-", type=click.Path(allow_dash=True))
@click.option("--spans", is_flag=True, default=False, help="Omit span information from output")
@click.option(
    "--max-str-len",
    metavar="N",
    type=int,
    default=None,
    help="Truncate strings longer than N chars",
)
def parse(file: str, spans: bool, max_str_len: int | None) -> None:
    """Parse a Gold source file and print the parse tree."""
    source = sys.stdin.read() if file == "-" else Path(file).read_text()

    result = _parse(source)
    click.echo(result.pprint(show_spans=spans, max_str_len=max_str_len))


@main.command()
@click.argument("file", default="-", type=click.Path(allow_dash=True))
@click.option("--spans", is_flag=True, default=False, help="Include span information in output")
@click.option(
    "--max-str-len",
    metavar="N",
    type=int,
    default=None,
    help="Truncate strings longer than N chars",
)
def run(file: str, spans: bool, max_str_len: int | None) -> None:
    """Evaluate a Gold source file and print the result."""
    result = evaluate_source_result(sys.stdin.read()) if file == "-" else evaluate_file_result(Path(file))
    click.echo(result.pprint(show_spans=spans, max_str_len=max_str_len))


@main.command("gen-fixture")
@click.argument("file", type=click.Path(allow_dash=True))
@click.argument("dest", required=False, default=None)
def gen_fixture(file: str, dest: str | None) -> None:
    """Generate .parse and .eval fixture files for a Gold source file.

    FILE may be a path or - for stdin. If FILE is inside the testdata directory,
    outputs go alongside it. Otherwise DEST (a directory in testdata) is required.
    When reading from stdin, DEST must be the full .gold path in testdata.
    """
    if file == "-":
        if dest is None:
            raise click.UsageError(
                "DEST is required when reading from stdin (provide the .gold path in testdata)"
            )
        dest_path = Path(dest)
        out_dir = dest_path.parent
        stem = dest_path.stem
        source = sys.stdin.read()
        resolver = PathImportResolver(root=out_dir)
    else:
        gold_path = Path(file).resolve()
        stem = gold_path.stem
        if gold_path.is_relative_to(_TESTDATA):
            out_dir = gold_path.parent
        else:
            if dest is None:
                raise click.UsageError("DEST is required when FILE is not inside the testdata directory")
            out_dir = Path(dest)
        source = gold_path.read_text(encoding="utf-8")
        resolver = PathImportResolver(root=gold_path.parent)

    parse_result = _parse(source)
    parse_file = out_dir / (stem + ".parse")
    parse_file.write_text(parse_result.pprint(show_spans=True) + "\n", encoding="utf-8")
    click.echo(f"Wrote {parse_file}")

    if parse_result.ok:
        eval_result = evaluate_source_result(source, resolver=resolver)
        eval_file = out_dir / (stem + ".eval")
        eval_file.write_text(eval_result.pprint(show_spans=True) + "\n", encoding="utf-8")
        click.echo(f"Wrote {eval_file}")
    else:
        click.echo("Parse errors detected; skipping evaluation.")

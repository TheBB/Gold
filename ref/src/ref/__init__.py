from __future__ import annotations

import sys
from pathlib import Path

import click

from .parser import parse as _parse


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

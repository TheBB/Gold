import re

from pygments.lexer import RegexLexer, bygroups, words
from pygments.token import Comment, Keyword, Name, Number, Operator, Punctuation, String, Text


class GoldLexer(RegexLexer):
    name = 'Gold'
    aliases = ['gold']
    filenames = ['*.gold']

    flags = re.MULTILINE

    KEYWORDS = ('let', 'in', 'fn', 'for', 'when', 'if', 'then', 'else', 'import', 'as')
    CONSTANTS = ('true', 'false', 'null')

    tokens = {
        'root': [
            (r'#.*$',                                                           Comment.Single),
            # Must come before [ \t]+ so the key's indentation isn't consumed
            # before the backreference \1 can use it to detect continuation lines.
            (r'^([ \t]*)([a-zA-Z_][a-zA-Z0-9_-]*)(::)([ \t]*.*(?:\n\1[ \t]+.*)*)',
             bygroups(Text, Name, Punctuation, String)),
            (r'\n',                                                             Text),
            (r'[ \t]+',                                                         Text),
            (words(KEYWORDS, suffix=r'\b'),                                     Keyword),
            (words(CONSTANTS, suffix=r'\b'),                                    Keyword.Constant),
            (r'\d+\.\d+',                                                       Number.Float),
            (r'\d+',                                                            Number.Integer),
            (r'"',                                                              String, 'string'),
            (r'[+\-*/]|==|!=|<=?|>=?',                                         Operator),
            (r'[=:.,\[\]{}()]',                                                 Punctuation),
            (r'[a-zA-Z_][a-zA-Z0-9_]*',                                        Name),
        ],
        'string': [
            (r'\$\{',                                                           String.Interpol, 'interpolation'),
            (r'[^"$\\]+',                                                       String),
            (r'\\.',                                                            String.Escape),
            (r'"',                                                              String, '#pop'),
        ],
        'interpolation': [
            (r'[a-zA-Z_][a-zA-Z0-9_-]*',                                       Name),
            (r'\}',                                                             String.Interpol, '#pop'),
        ],
    }

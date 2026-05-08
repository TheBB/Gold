from pygments.lexer import RegexLexer, words
from pygments.token import Comment, Keyword, Name, Number, Operator, Punctuation, String, Text


class GoldLexer(RegexLexer):
    name = 'Gold'
    aliases = ['gold']
    filenames = ['*.gold']

    KEYWORDS = ('let', 'in', 'fn', 'for', 'when', 'if', 'then', 'else', 'import', 'as')
    CONSTANTS = ('true', 'false', 'null')

    tokens = {
        'root': [
            (r'#.*$',                           Comment.Single),
            (r'\s+',                            Text),
            (words(KEYWORDS, suffix=r'\b'),     Keyword),
            (words(CONSTANTS, suffix=r'\b'),    Keyword.Constant),
            (r'\d+\.\d+',                       Number.Float),
            (r'\d+',                            Number.Integer),
            (r'"',                              String, 'string'),
            (r'[+\-*/]|==|!=|<=?|>=?',         Operator),
            (r'[=:.,\[\]{}()]',                 Punctuation),
            (r'[a-zA-Z_][a-zA-Z0-9_]*',        Name),
        ],
        'string': [
            (r'\$\{',                           String.Interpol, 'interpolation'),
            (r'[^"$\\]+',                       String),
            (r'\\.',                            String.Escape),
            (r'"',                              String, '#pop'),
        ],
        'interpolation': [
            (r'[a-zA-Z_][a-zA-Z0-9_]*',        Name),
            (r'\}',                             String.Interpol, '#pop'),
        ],
    }

use serde::{Deserialize, Serialize};

use crate::{error::Error, object::integer::Int};

#[derive(Debug, Clone, Copy, PartialEq, Serialize, Deserialize)]
pub enum StringAlignSpec {
    Left,
    Right,
    Center,
}

#[derive(Debug, Clone, Copy, PartialEq, Serialize, Deserialize)]
pub enum AlignSpec {
    AfterSign,
    String(StringAlignSpec),
}

impl Default for AlignSpec {
    fn default() -> Self {
        Self::left()
    }
}

impl AlignSpec {
    pub fn left() -> Self {
        Self::String(StringAlignSpec::Left)
    }

    pub fn right() -> Self {
        Self::String(StringAlignSpec::Right)
    }

    pub fn center() -> Self {
        Self::String(StringAlignSpec::Center)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Serialize, Deserialize)]
pub enum SignSpec {
    Plus,
    Minus,
    Space,
}

impl Default for SignSpec {
    fn default() -> Self {
        Self::Minus
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Serialize, Deserialize)]
pub enum GroupingSpec {
    Comma,
    Underscore,
}

#[derive(Debug, Clone, Copy, PartialEq, Serialize, Deserialize)]
pub enum UppercaseSpec {
    Upper,
    Lower,
}

#[derive(Debug, Clone, Copy, PartialEq, Serialize, Deserialize)]
pub enum IntegerFormatType {
    Binary,
    Character,
    Decimal,
    Octal,
    Hex(UppercaseSpec),
}

#[derive(Debug, Clone, Copy, PartialEq, Serialize, Deserialize)]
pub enum FloatFormatType {
    Sci(UppercaseSpec),
    Fixed,
    General,
    Percentage,
}

#[derive(Debug, Clone, Copy, PartialEq, Serialize, Deserialize)]
pub enum FormatType {
    String,
    Integer(IntegerFormatType),
    Float(FloatFormatType),
}

#[derive(Debug, Clone, Copy, PartialEq, Serialize, Deserialize)]
pub struct FormatSpec {
    pub fill: char,
    pub align: Option<AlignSpec>,
    pub sign: Option<SignSpec>,
    pub alternate: bool,
    pub width: Option<usize>,
    pub grouping: Option<GroupingSpec>,
    pub precision: Option<usize>,
    pub fmt_type: Option<FormatType>,
}

impl FormatSpec {
    pub fn string_spec(&self) -> Option<StringFormatSpec> {
        if self.sign.is_some()
            || self.alternate
            || self.grouping.is_some()
            || self.precision.is_some()
            || self.fmt_type.is_some_and(|x| x != FormatType::String)
        {
            return None;
        }

        let align = match self.align {
            Some(AlignSpec::AfterSign) => {
                return None;
            }
            Some(AlignSpec::String(x)) => x,
            None => StringAlignSpec::Left,
        };

        Some(StringFormatSpec {
            fill: self.fill,
            width: self.width,
            align,
        })
    }

    pub fn integer_spec(&self) -> Option<IntegerFormatSpec> {
        if self.precision.is_some() {
            return None;
        }

        let fmt_type = match self.fmt_type {
            None => IntegerFormatType::Decimal,
            Some(FormatType::Integer(x)) => x,
            _ => {
                return None;
            }
        };

        Some(IntegerFormatSpec {
            fill: self.fill,
            align: self.align.unwrap_or_else(AlignSpec::right),
            sign: self.sign.unwrap_or_default(),
            alternate: self.alternate,
            width: self.width,
            grouping: self.grouping,
            fmt_type,
        })
    }

    pub fn float_spec(&self) -> Option<FloatFormatSpec> {
        let fmt_type = match self.fmt_type {
            Some(FormatType::Float(x)) => x,
            None => {
                if self.precision.is_some() {
                    FloatFormatType::Fixed
                } else {
                    FloatFormatType::General
                }
            }
            _ => {
                return None;
            }
        };

        Some(FloatFormatSpec {
            fill: self.fill,
            align: self.align.unwrap_or_else(AlignSpec::right),
            sign: self.sign.unwrap_or_default(),
            width: self.width,
            grouping: self.grouping,
            precision: self.precision.unwrap_or(6),
            fmt_type,
        })
    }
}

impl Default for FormatSpec {
    fn default() -> Self {
        Self {
            fill: ' ',
            align: None,
            sign: None,
            alternate: false,
            width: None,
            grouping: None,
            precision: None,
            fmt_type: None,
        }
    }
}

pub struct StringFormatSpec {
    pub fill: char,
    pub align: StringAlignSpec,
    pub width: Option<usize>,
}

impl StringFormatSpec {
    pub fn format(&self, value: impl AsRef<str>) -> String {
        let s = value.as_ref();
        match self.width {
            None => s.to_owned(),
            Some(w) => {
                let nchars = s.chars().count();
                if nchars > w {
                    s.to_owned()
                } else {
                    let missing = w - nchars;
                    let (lfill, rfill) = match self.align {
                        StringAlignSpec::Left => (0, missing),
                        StringAlignSpec::Right => (missing, 0),
                        StringAlignSpec::Center => (missing / 2, missing - missing / 2),
                    };
                    let mut r = String::with_capacity(w);
                    for _ in 0..lfill {
                        r.push(self.fill);
                    }
                    r += s;
                    for _ in 0..rfill {
                        r.push(self.fill);
                    }
                    r
                }
            }
        }
    }
}

pub struct IntegerFormatSpec {
    pub fill: char,
    pub align: AlignSpec,
    pub sign: SignSpec,
    pub alternate: bool,
    pub width: Option<usize>,
    pub grouping: Option<GroupingSpec>,
    pub fmt_type: IntegerFormatType,
}

impl IntegerFormatSpec {
    pub fn string_spec(&self) -> Option<StringFormatSpec> {
        match (self.align, self.width) {
            (AlignSpec::AfterSign, _) => {
                return None;
            }
            (_, None) => {
                return None;
            }
            (AlignSpec::String(align), Some(width)) => Some(StringFormatSpec {
                fill: self.fill,
                align,
                width: Some(width),
            }),
        }
    }

    pub(crate) fn format(&self, value: &Int) -> Result<String, Error> {
        value.format(self)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Serialize, Deserialize)]
pub struct FloatFormatSpec {
    pub fill: char,
    pub align: AlignSpec,
    pub sign: SignSpec,
    pub width: Option<usize>,
    pub grouping: Option<GroupingSpec>,
    pub precision: usize,
    pub fmt_type: FloatFormatType,
}

impl FloatFormatSpec {
    pub fn string_spec(&self) -> Option<StringFormatSpec> {
        match (self.align, self.width) {
            (AlignSpec::AfterSign, _) => {
                return None;
            }
            (_, None) => {
                return None;
            }
            (AlignSpec::String(align), Some(width)) => Some(StringFormatSpec {
                fill: self.fill,
                align,
                width: Some(width),
            }),
        }
    }

    pub fn format(&self, value: f64) -> String {
        let base = match self.fmt_type {
            FloatFormatType::Fixed => format!(
                "{number:+.precision$}",
                number = value,
                precision = self.precision
            ),
            FloatFormatType::General => format!("{:+}", value),
            FloatFormatType::Sci(UppercaseSpec::Lower) => format!(
                "{number:+.precision$e}",
                number = value,
                precision = self.precision
            ),
            FloatFormatType::Sci(UppercaseSpec::Upper) => format!(
                "{number:+.precision$E}",
                number = value,
                precision = self.precision
            ),
            FloatFormatType::Percentage => format!(
                "{number:+.precision$}%",
                number = 100.0 * value,
                precision = self.precision
            ),
        };

        let mut base_digits = &base[1..];
        let mut buffer = String::new();

        match (self.sign, value < 0.0) {
            (_, true) => {
                buffer.push('-');
            }
            (SignSpec::Plus, false) => {
                buffer.push('+');
            }
            (SignSpec::Space, false) => {
                buffer.push(' ');
            }
            _ => {}
        }

        if let Some(group_spec) = self.grouping {
            let group_size: usize = 3;
            let group_char = match group_spec {
                GroupingSpec::Comma => ',',
                GroupingSpec::Underscore => '_',
            };

            let mut num_digits: usize = base_digits.len();
            for (i, c) in base_digits.char_indices() {
                match c {
                    '0'..='9' => {}
                    _ => {
                        num_digits = i;
                        break;
                    }
                }
            }

            let num_groups = (num_digits + group_size - 1) / group_size;
            let first_group_size = num_digits - (num_groups - 1) * group_size;

            if let (AlignSpec::AfterSign, Some(min_width)) = (self.align, self.width) {
                let num_width = base_digits.len() + buffer.len() + num_groups - 1;
                if num_width < min_width {
                    let extra = min_width - num_width;
                    for _ in 0..extra {
                        buffer.push(self.fill);
                    }
                }
            }

            buffer += &base_digits[..first_group_size];
            base_digits = &base_digits[first_group_size..];

            for _ in 1..num_groups {
                buffer.push(group_char);
                buffer += &base_digits[..group_size];
                base_digits = &base_digits[group_size..];
            }

            buffer += base_digits;
        } else {
            if let (AlignSpec::AfterSign, Some(min_width)) = (self.align, self.width) {
                let num_width = base_digits.len() + buffer.len();
                if num_width < min_width {
                    let extra = min_width - num_width;
                    for _ in 0..extra {
                        buffer.push(self.fill);
                    }
                }
            }

            buffer += base_digits;
        }

        if let Some(str_spec) = self.string_spec() {
            str_spec.format(buffer)
        } else {
            buffer
        }
    }
}

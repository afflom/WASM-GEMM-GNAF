//! A minimal JSON reader and writer.
//!
//! SPEC section 4 forbids network-fetched inputs in release verification.
//! Vendoring a parser and a serializer would trade that guarantee for
//! convenience, so this is a small recursive-descent reader plus a writer over
//! std.
//!
//! The writer exists because `MANIFEST.json` is not merely a report: SPEC
//! section 4 makes its canonical encoding the PREIMAGE of the identity stages,
//! so the byte sequence is load-bearing. [`Out::canonical`] is the injective
//! encoding that gets hashed (sorted keys, no insignificant whitespace) and
//! [`Out::pretty`] is the committed rendering.

use std::collections::BTreeMap;
use std::fmt::Write as _;

use crate::spec::{Result, SpecError};

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Null,
    Bool(bool),
    Number(f64),
    String(String),
    Array(Vec<Value>),
    Object(BTreeMap<String, Value>),
}

impl Value {
    /// Member of an object, or `None` for any other shape.
    pub fn get(&self, key: &str) -> Option<&Value> {
        match self {
            Value::Object(map) => map.get(key),
            _ => None,
        }
    }

    pub fn as_str(&self) -> Option<&str> {
        match self {
            Value::String(s) => Some(s),
            _ => None,
        }
    }

    pub fn as_array(&self) -> Option<&[Value]> {
        match self {
            Value::Array(items) => Some(items),
            _ => None,
        }
    }

    /// Is this field PRESENT and non-empty?
    ///
    /// A registry field may be a string, a list of proved declarations, or
    /// absent, and all three shapes mean something different. `null`, `""` and
    /// `[]` all mean "nothing was supplied", so they must not be mistaken for a
    /// discharged obligation just because the key exists.
    pub fn is_supplied(&self) -> bool {
        match self {
            Value::Null => false,
            Value::Bool(b) => *b,
            Value::Number(n) => *n != 0.0,
            Value::String(s) => !s.is_empty(),
            Value::Array(items) => !items.is_empty(),
            Value::Object(map) => !map.is_empty(),
        }
    }

    /// Re-encode a parsed value as JSON text.
    ///
    /// Used to search a body for an identity it must NOT contain (SPEC section 4
    /// acyclicity), so it has to include keys as well as values -- a stage that
    /// smuggled a later identity in as a key would still be cyclic.
    pub fn to_json(&self) -> String {
        match self {
            Value::Null => "null".into(),
            Value::Bool(b) => b.to_string(),
            Value::Number(n) => n.to_string(),
            Value::String(s) => {
                let mut out = String::new();
                escape(s, &mut out);
                out
            }
            Value::Array(items) => {
                let body: Vec<String> = items.iter().map(Value::to_json).collect();
                format!("[{}]", body.join(","))
            }
            Value::Object(map) => {
                let body: Vec<String> = map
                    .iter()
                    .map(|(k, v)| {
                        let mut out = String::new();
                        escape(k, &mut out);
                        format!("{out}:{}", v.to_json())
                    })
                    .collect();
                format!("{{{}}}", body.join(","))
            }
        }
    }

    /// A required string field, with an error naming the SPEC clause.
    pub fn required_str(&self, clause: &'static str, key: &str, context: &str) -> Result<&str> {
        self.get(key)
            .and_then(Value::as_str)
            .ok_or_else(|| SpecError::new(clause, format!("{context}: missing string field `{key}`")))
    }
}

pub fn parse(clause: &'static str, text: &str) -> Result<Value> {
    let mut p = Parser { chars: text.chars().collect(), pos: 0, clause };
    p.skip_ws();
    let value = p.value()?;
    p.skip_ws();
    if p.pos != p.chars.len() {
        return Err(p.error("trailing content after the top-level JSON value"));
    }
    Ok(value)
}

struct Parser {
    chars: Vec<char>,
    pos: usize,
    clause: &'static str,
}

impl Parser {
    fn error(&self, message: &str) -> SpecError {
        SpecError::new(self.clause, format!("malformed JSON at character {}: {message}", self.pos))
    }

    fn peek(&self) -> Option<char> {
        self.chars.get(self.pos).copied()
    }

    fn bump(&mut self) -> Option<char> {
        let c = self.peek();
        if c.is_some() {
            self.pos += 1;
        }
        c
    }

    fn skip_ws(&mut self) {
        while matches!(self.peek(), Some(' ' | '\t' | '\n' | '\r')) {
            self.pos += 1;
        }
    }

    fn expect(&mut self, want: char) -> Result<()> {
        match self.bump() {
            Some(c) if c == want => Ok(()),
            Some(c) => Err(self.error(&format!("expected `{want}`, found `{c}`"))),
            None => Err(self.error(&format!("expected `{want}`, found end of input"))),
        }
    }

    fn literal(&mut self, word: &str, value: Value) -> Result<Value> {
        if self.chars[self.pos..].starts_with(&word.chars().collect::<Vec<_>>()[..]) {
            self.pos += word.chars().count();
            Ok(value)
        } else {
            Err(self.error(&format!("expected `{word}`")))
        }
    }

    fn value(&mut self) -> Result<Value> {
        match self.peek() {
            Some('{') => self.object(),
            Some('[') => self.array(),
            Some('"') => Ok(Value::String(self.string()?)),
            Some('t') => self.literal("true", Value::Bool(true)),
            Some('f') => self.literal("false", Value::Bool(false)),
            Some('n') => self.literal("null", Value::Null),
            Some(c) if c == '-' || c.is_ascii_digit() => self.number(),
            Some(c) => Err(self.error(&format!("unexpected character `{c}`"))),
            None => Err(self.error("unexpected end of input")),
        }
    }

    fn object(&mut self) -> Result<Value> {
        self.expect('{')?;
        let mut map = BTreeMap::new();
        self.skip_ws();
        if self.peek() == Some('}') {
            self.pos += 1;
            return Ok(Value::Object(map));
        }
        loop {
            self.skip_ws();
            let key = self.string()?;
            self.skip_ws();
            self.expect(':')?;
            self.skip_ws();
            let value = self.value()?;
            map.insert(key, value);
            self.skip_ws();
            match self.bump() {
                Some(',') => continue,
                Some('}') => return Ok(Value::Object(map)),
                _ => return Err(self.error("expected `,` or `}` in object")),
            }
        }
    }

    fn array(&mut self) -> Result<Value> {
        self.expect('[')?;
        let mut items = Vec::new();
        self.skip_ws();
        if self.peek() == Some(']') {
            self.pos += 1;
            return Ok(Value::Array(items));
        }
        loop {
            self.skip_ws();
            items.push(self.value()?);
            self.skip_ws();
            match self.bump() {
                Some(',') => continue,
                Some(']') => return Ok(Value::Array(items)),
                _ => return Err(self.error("expected `,` or `]` in array")),
            }
        }
    }

    fn string(&mut self) -> Result<String> {
        self.expect('"')?;
        let mut s = String::new();
        loop {
            match self.bump() {
                None => return Err(self.error("unterminated string")),
                Some('"') => return Ok(s),
                Some('\\') => match self.bump() {
                    Some('"') => s.push('"'),
                    Some('\\') => s.push('\\'),
                    Some('/') => s.push('/'),
                    Some('b') => s.push('\u{8}'),
                    Some('f') => s.push('\u{c}'),
                    Some('n') => s.push('\n'),
                    Some('r') => s.push('\r'),
                    Some('t') => s.push('\t'),
                    Some('u') => s.push(self.unicode_escape()?),
                    Some(c) => return Err(self.error(&format!("unknown escape `\\{c}`"))),
                    None => return Err(self.error("unterminated escape")),
                },
                Some(c) => s.push(c),
            }
        }
    }

    fn unicode_escape(&mut self) -> Result<char> {
        let mut code = 0u32;
        for _ in 0..4 {
            let c = self.bump().ok_or_else(|| self.error("truncated \\u escape"))?;
            let digit = c
                .to_digit(16)
                .ok_or_else(|| self.error("non-hex digit in \\u escape"))?;
            code = code * 16 + digit;
        }
        char::from_u32(code).ok_or_else(|| self.error("\\u escape is not a scalar value"))
    }

    fn number(&mut self) -> Result<Value> {
        let start = self.pos;
        if self.peek() == Some('-') {
            self.pos += 1;
        }
        while matches!(self.peek(), Some(c) if c.is_ascii_digit() || matches!(c, '.' | 'e' | 'E' | '+' | '-'))
        {
            self.pos += 1;
        }
        let text: String = self.chars[start..self.pos].iter().collect();
        text.parse::<f64>()
            .map(Value::Number)
            .map_err(|_| self.error(&format!("`{text}` is not a number")))
    }
}

/// A JSON value being WRITTEN.
///
/// Distinct from [`Value`] on purpose: a read value has no meaningful key order
/// (`Value` sorts, which is all a lookup needs), whereas a written manifest has
/// a declared field order that the committed file preserves. Integers are also
/// kept exact -- a byte count that round-trips through `f64` and comes back as
/// `1234.0` is a different preimage and therefore a different identity.
/// Only the shapes the manifest actually uses. A writer that offers a type the
/// manifest never emits is a type nobody has checked the encoding of.
#[derive(Debug, Clone, PartialEq)]
pub enum Out {
    Null,
    Int(u64),
    Str(String),
    Arr(Vec<Out>),
    Obj(Vec<(String, Out)>),
}

/// `"..."` as a JSON string.
pub fn s(text: impl Into<String>) -> Out {
    Out::Str(text.into())
}

/// An object literal, keys kept in the order given.
pub fn obj(fields: Vec<(&str, Out)>) -> Out {
    Out::Obj(fields.into_iter().map(|(k, v)| (k.to_string(), v)).collect())
}

impl Out {
    /// The canonical encoding: keys sorted, no insignificant whitespace.
    ///
    /// This is the preimage SPEC section 4 hashes. Sorting makes the encoding
    /// independent of the order the tool happened to build the body in, so the
    /// identity of a stage depends only on its content.
    pub fn canonical(&self) -> String {
        let mut out = String::new();
        self.write_canonical(&mut out);
        out
    }

    /// The committed rendering: two-space indent, `": "` after keys.
    pub fn pretty(&self) -> String {
        let mut out = String::new();
        self.write_pretty(0, &mut out);
        out
    }

    fn write_canonical(&self, out: &mut String) {
        match self {
            Out::Null => out.push_str("null"),
            Out::Int(n) => {
                let _ = write!(out, "{n}");
            }
            Out::Str(text) => escape(text, out),
            Out::Arr(items) => {
                out.push('[');
                for (i, item) in items.iter().enumerate() {
                    if i > 0 {
                        out.push(',');
                    }
                    item.write_canonical(out);
                }
                out.push(']');
            }
            Out::Obj(fields) => {
                let mut sorted: Vec<&(String, Out)> = fields.iter().collect();
                sorted.sort_by(|a, b| a.0.cmp(&b.0));
                out.push('{');
                for (i, (key, value)) in sorted.iter().enumerate() {
                    if i > 0 {
                        out.push(',');
                    }
                    escape(key, out);
                    out.push(':');
                    value.write_canonical(out);
                }
                out.push('}');
            }
        }
    }

    fn write_pretty(&self, depth: usize, out: &mut String) {
        let pad = |n: usize, out: &mut String| out.push_str(&"  ".repeat(n));
        match self {
            Out::Arr(items) if !items.is_empty() => {
                out.push_str("[\n");
                for (i, item) in items.iter().enumerate() {
                    if i > 0 {
                        out.push_str(",\n");
                    }
                    pad(depth + 1, out);
                    item.write_pretty(depth + 1, out);
                }
                out.push('\n');
                pad(depth, out);
                out.push(']');
            }
            Out::Obj(fields) if !fields.is_empty() => {
                out.push_str("{\n");
                for (i, (key, value)) in fields.iter().enumerate() {
                    if i > 0 {
                        out.push_str(",\n");
                    }
                    pad(depth + 1, out);
                    escape(key, out);
                    out.push_str(": ");
                    value.write_pretty(depth + 1, out);
                }
                out.push('\n');
                pad(depth, out);
                out.push('}');
            }
            Out::Arr(_) => out.push_str("[]"),
            Out::Obj(_) => out.push_str("{}"),
            other => other.write_canonical(out),
        }
    }
}

/// Escape a string, keeping the output pure ASCII.
///
/// Everything outside printable ASCII becomes a `\uXXXX` escape (a non-BMP
/// scalar becomes a surrogate pair), so the manifest is byte-identical however
/// the reader's locale is configured -- an encoding that varied with the
/// environment would make the identity stages environment-dependent.
fn escape(text: &str, out: &mut String) {
    out.push('"');
    for c in text.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            '\u{8}' => out.push_str("\\b"),
            '\u{c}' => out.push_str("\\f"),
            ' '..='~' => out.push(c),
            _ => {
                let n = c as u32;
                if n > 0xFFFF {
                    let v = n - 0x10000;
                    let _ = write!(
                        out,
                        "\\u{:04x}\\u{:04x}",
                        0xD800 + (v >> 10),
                        0xDC00 + (v & 0x3FF)
                    );
                } else {
                    let _ = write!(out, "\\u{n:04x}");
                }
            }
        }
    }
    out.push('"');
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reads_a_claim_registry_shape() {
        let text = r#"{ "claims": [ { "id": "CO-001", "level": "formalProof",
            "leanDeclaration": "WasmGemmGnaf.Cost.coordinate_le_score" } ] }"#;
        let v = parse("17", text).expect("parses");
        let claims = v.get("claims").and_then(Value::as_array).expect("array");
        assert_eq!(claims.len(), 1);
        assert_eq!(claims[0].get("level").and_then(Value::as_str), Some("formalProof"));
    }

    #[test]
    fn handles_escapes_and_nesting() {
        let v = parse("17", r#"{"a":"x\tyA","b":[1,-2.5e3,true,null,{}]}"#).expect("parses");
        assert_eq!(v.get("a").and_then(Value::as_str), Some("x\tyA"));
        assert_eq!(v.get("b").and_then(Value::as_array).map(<[Value]>::len), Some(5));
    }

    #[test]
    fn rejects_trailing_junk() {
        assert!(parse("17", "{} {}").is_err());
        assert!(parse("17", "{\"a\":}").is_err());
    }
}

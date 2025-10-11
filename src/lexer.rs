use crate::error::JitError;

#[derive(Clone, Debug)]
pub(crate) enum Token {
    Ident(String),
    Num(f64),
    Plus,
    Minus,
    Star,
    Slash,
    Caret,
    EqEq,
    NotEq,
    Not,
    Lt,
    Le,
    Gt,
    Ge,
    AndAnd,
    OrOr,
    LParen,
    RParen,
    Comma,
    Eof,
}

pub(crate) struct Lexer<'a> {
    src: &'a [u8],
    i: usize,
}

impl<'a> Lexer<'a> {
    pub(crate) fn new(s: &'a str) -> Self {
        Self {
            src: s.as_bytes(),
            i: 0,
        }
    }
    fn peek(&self) -> Option<u8> {
        self.src.get(self.i).copied()
    }
    fn bump(&mut self) -> Option<u8> {
        let ch = self.src.get(self.i).copied();
        if ch.is_some() {
            self.i += 1;
        }
        ch
    }
    fn skip_ws(&mut self) {
        while let Some(c) = self.peek() {
            if c.is_ascii_whitespace() {
                self.i += 1;
            } else {
                break;
            }
        }
    }
    pub(crate) fn next_token(&mut self) -> Result<Token, JitError> {
        self.skip_ws();
        let c = match self.peek() {
            Some(c) => c,
            None => return Ok(Token::Eof),
        };
        match c {
            b'(' => {
                self.bump();
                Ok(Token::LParen)
            }
            b')' => {
                self.bump();
                Ok(Token::RParen)
            }
            b'+' => {
                self.bump();
                Ok(Token::Plus)
            }
            b'-' => {
                self.bump();
                Ok(Token::Minus)
            }
            b'*' => {
                self.bump();
                Ok(Token::Star)
            }
            b'/' => {
                self.bump();
                Ok(Token::Slash)
            }
            b'^' => {
                self.bump();
                Ok(Token::Caret)
            }
            b'=' => {
                self.bump();
                if self.peek() == Some(b'=') {
                    self.bump();
                    Ok(Token::EqEq)
                } else {
                    Err(JitError::Parse("expected '=' after '=' for '=='".into()))
                }
            }
            b'!' => {
                self.bump();
                if self.peek() == Some(b'=') {
                    self.bump();
                    Ok(Token::NotEq)
                } else {
                    Ok(Token::Not)
                }
            }
            b'<' => {
                self.bump();
                if self.peek() == Some(b'=') {
                    self.bump();
                    Ok(Token::Le)
                } else {
                    Ok(Token::Lt)
                }
            }
            b'>' => {
                self.bump();
                if self.peek() == Some(b'=') {
                    self.bump();
                    Ok(Token::Ge)
                } else {
                    Ok(Token::Gt)
                }
            }
            b'&' => {
                self.bump();
                if self.peek() == Some(b'&') {
                    self.bump();
                    Ok(Token::AndAnd)
                } else {
                    Err(JitError::Parse("expected '&' after '&' for '&&'".into()))
                }
            }
            b'|' => {
                self.bump();
                if self.peek() == Some(b'|') {
                    self.bump();
                    Ok(Token::OrOr)
                } else {
                    Err(JitError::Parse("expected '|' after '|' for '||'".into()))
                }
            }
            b',' => {
                self.bump();
                Ok(Token::Comma)
            }
            c if c.is_ascii_digit() || c == b'.' => self.lex_number(),
            _ => self.lex_ident(),
        }
    }
    fn lex_number(&mut self) -> Result<Token, JitError> {
        let start = self.i;
        let mut seen_dot = false;
        let mut seen_exp = false;
        // Parse mantissa (integer and fractional) and optional scientific exponent.
        while let Some(c) = self.peek() {
            if c.is_ascii_digit() {
                self.i += 1;
            } else if c == b'.' && !seen_dot && !seen_exp {
                seen_dot = true;
                self.i += 1;
            } else if (c == b'e' || c == b'E') && !seen_exp {
                // Scientific notation exponent part
                seen_exp = true;
                self.i += 1; // consume 'e' or 'E'
                // Optional sign after exponent
                if let Some(sign) = self.peek() {
                    if sign == b'+' || sign == b'-' {
                        self.i += 1;
                    }
                }
                // Consume exponent digits (if any). If none, parse() will error later.
                while let Some(d) = self.peek() {
                    if d.is_ascii_digit() {
                        self.i += 1;
                    } else {
                        break;
                    }
                }
            } else {
                break;
            }
        }
        let end = self.i;
        // Custom suffix: uppercase 'M' means multiply by 1,000,000 (million).
        let mut multiplier = 1.0;
        if self.peek() == Some(b'M') {
            self.bump();
            multiplier = 1_000_000.0;
        }
        let s = std::str::from_utf8(&self.src[start..end]).unwrap();
        let v: f64 = s
            .parse()
            .map_err(|e| JitError::Parse(format!("invalid number '{}': {}", s, e)))?;
        Ok(Token::Num(v * multiplier))
    }
    fn lex_ident(&mut self) -> Result<Token, JitError> {
        let start = self.i;
        while let Some(c) = self.peek() {
            if c.is_ascii_alphanumeric() || c == b'_' {
                self.i += 1;
            } else {
                break;
            }
        }
        let s = std::str::from_utf8(&self.src[start..self.i])
            .unwrap()
            .to_string();
        if s.is_empty() {
            return Err(JitError::Parse("unexpected character".into()));
        }
        Ok(Token::Ident(s))
    }
}

use crate::ast::Ast;
use crate::error::JitError;
use crate::lexer::{Lexer, Token};

pub(crate) struct Parser<'a> {
    lex: Lexer<'a>,
    look: Token,
}

impl<'a> Parser<'a> {
    pub(crate) fn new(s: &'a str) -> Result<Self, JitError> {
        let mut lex = Lexer::new(s);
        let look = lex.next_token()?;
        Ok(Self { lex, look })
    }
    fn bump(&mut self) -> Result<(), JitError> {
        self.look = self.lex.next_token()?;
        Ok(())
    }
    fn expect(&mut self, t: &Token) -> Result<(), JitError> {
        if std::mem::discriminant(&self.look) == std::mem::discriminant(t) {
            self.bump()
        } else {
            Err(JitError::Parse(format!("expected {:?}", t)))
        }
    }
    pub(crate) fn parse(mut self) -> Result<Ast, JitError> {
        let expr = self.or_expr()?;
        if !matches!(self.look, Token::Eof) {
            return Err(JitError::Parse("trailing tokens".into()));
        }
        Ok(expr)
    }
    fn or_expr(&mut self) -> Result<Ast, JitError> {
        let mut node = self.and_expr()?;
        while matches!(self.look, Token::OrOr) {
            self.bump()?;
            let rhs = self.and_expr()?;
            node = Ast::Or(Box::new(node), Box::new(rhs));
        }
        Ok(node)
    }
    fn and_expr(&mut self) -> Result<Ast, JitError> {
        let mut node = self.equality()?;
        while matches!(self.look, Token::AndAnd) {
            self.bump()?;
            let rhs = self.equality()?;
            node = Ast::And(Box::new(node), Box::new(rhs));
        }
        Ok(node)
    }
    fn equality(&mut self) -> Result<Ast, JitError> {
        let mut node = self.relational()?;
        loop {
            match self.look {
                Token::EqEq => {
                    self.bump()?;
                    let rhs = self.relational()?;
                    node = Ast::Eq(Box::new(node), Box::new(rhs));
                }
                Token::NotEq => {
                    self.bump()?;
                    let rhs = self.relational()?;
                    node = Ast::Ne(Box::new(node), Box::new(rhs));
                }
                _ => break,
            }
        }
        Ok(node)
    }
    fn relational(&mut self) -> Result<Ast, JitError> {
        let mut node = self.additive()?;
        loop {
            match self.look {
                Token::Lt => {
                    self.bump()?;
                    let rhs = self.additive()?;
                    node = Ast::Lt(Box::new(node), Box::new(rhs));
                }
                Token::Le => {
                    self.bump()?;
                    let rhs = self.additive()?;
                    node = Ast::Le(Box::new(node), Box::new(rhs));
                }
                Token::Gt => {
                    self.bump()?;
                    let rhs = self.additive()?;
                    node = Ast::Gt(Box::new(node), Box::new(rhs));
                }
                Token::Ge => {
                    self.bump()?;
                    let rhs = self.additive()?;
                    node = Ast::Ge(Box::new(node), Box::new(rhs));
                }
                _ => break,
            }
        }
        Ok(node)
    }
    fn additive(&mut self) -> Result<Ast, JitError> {
        let mut node = self.multiplicative()?;
        loop {
            match self.look.clone() {
                Token::Plus => {
                    self.bump()?;
                    let rhs = self.multiplicative()?;
                    node = Ast::Add(Box::new(node), Box::new(rhs));
                }
                Token::Minus => {
                    self.bump()?;
                    let rhs = self.multiplicative()?;
                    node = Ast::Sub(Box::new(node), Box::new(rhs));
                }
                _ => break,
            }
        }
        Ok(node)
    }
    fn multiplicative(&mut self) -> Result<Ast, JitError> {
        let mut node = self.unary()?;
        loop {
            match self.look.clone() {
                Token::Star => {
                    self.bump()?;
                    let rhs = self.unary()?;
                    node = Ast::Mul(Box::new(node), Box::new(rhs));
                }
                Token::Slash => {
                    self.bump()?;
                    let rhs = self.unary()?;
                    node = Ast::Div(Box::new(node), Box::new(rhs));
                }
                _ => break,
            }
        }
        Ok(node)
    }
    fn unary(&mut self) -> Result<Ast, JitError> {
        match self.look.clone() {
            Token::Minus => {
                self.bump()?;
                Ok(Ast::Neg(Box::new(self.unary()?)))
            }
            Token::Not => {
                self.bump()?;
                Ok(Ast::Not(Box::new(self.unary()?)))
            }
            _ => self.primary(),
        }
    }
    fn primary(&mut self) -> Result<Ast, JitError> {
        match self.look.clone() {
            Token::Num(v) => {
                self.bump()?;
                Ok(Ast::Num(v))
            }
            Token::Ident(s) => {
                self.bump()?;
                if s == "if" {
                    self.expect(&Token::LParen)?;
                    let cond = self.or_expr()?;
                    self.expect(&Token::Comma)?;
                    let then_e = self.or_expr()?;
                    self.expect(&Token::Comma)?;
                    let else_e = self.or_expr()?;
                    self.expect(&Token::RParen)?;
                    Ok(Ast::If(Box::new(cond), Box::new(then_e), Box::new(else_e)))
                } else if s == "ifs" {
                    self.expect(&Token::LParen)?;
                    let mut args = Vec::new();
                    if !matches!(self.look, Token::RParen) {
                        loop {
                            let arg = self.or_expr()?;
                            args.push(Box::new(arg));
                            if matches!(self.look, Token::Comma) {
                                self.bump()?;
                                continue;
                            }
                            break;
                        }
                    }
                    self.expect(&Token::RParen)?;
                    if args.len() < 3 || args.len() % 2 == 0 {
                        return Err(JitError::Parse(
                            "IFS requires an odd number of arguments, with a minimum of 3.".into(),
                        ));
                    }
                    Ok(Ast::Ifs(args))
                } else if s == "max" {
                    self.expect(&Token::LParen)?;
                    let a = self.or_expr()?;
                    self.expect(&Token::Comma)?;
                    let b = self.or_expr()?;
                    self.expect(&Token::RParen)?;
                    Ok(Ast::Max(Box::new(a), Box::new(b)))
                } else if s == "min" {
                    self.expect(&Token::LParen)?;
                    let a = self.or_expr()?;
                    self.expect(&Token::Comma)?;
                    let b = self.or_expr()?;
                    self.expect(&Token::RParen)?;
                    Ok(Ast::Min(Box::new(a), Box::new(b)))
                } else if matches!(self.look, Token::LParen) {
                    // Generic function call: name(args..)
                    self.bump()?; // consume '('
                    let mut args = Vec::new();
                    if !matches!(self.look, Token::RParen) {
                        loop {
                            let arg = self.or_expr()?;
                            args.push(arg);
                            if matches!(self.look, Token::Comma) {
                                self.bump()?; // consume ','
                                continue;
                            }
                            break;
                        }
                    }
                    self.expect(&Token::RParen)?;
                    Ok(Ast::Call { name: s, args })
                } else {
                    Ok(Ast::Var(s))
                }
            }
            Token::LParen => {
                self.bump()?;
                let e = self.or_expr()?;
                self.expect(&Token::RParen)?;
                Ok(e)
            }
            _ => Err(JitError::Parse(
                "expected number, identifier, or \'(\'".into(),
            )),
        }
    }
}

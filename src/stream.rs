//! A slice-backed, peekable token stream for recursive descent parsing.

use std::{cell::Cell, error::Error, fmt, marker::PhantomData};

use bumpalo::Bump;
use unicode_width::UnicodeWidthChar;

use crate::{
    token::{tokenize, Token, TokenSlice, TokenType},
    Parse,
};

/// A virtual cursor position.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct CursorPosition {
    line: u32,
    col: u32,
}

const TAB_WIDTH: u32 = 8;

impl CursorPosition {
    fn new() -> Self {
        CursorPosition { line: 1, col: 1 }
    }

    /// The line number of the cursor.
    pub fn line(&self) -> u32 {
        self.line
    }

    /// The column number of the cursor.
    pub fn col(&self) -> u32 {
        self.col
    }

    fn newline(&mut self) {
        self.line += 1;
        self.col = 1;
    }

    fn advance<T>(&mut self, tok: &Token<T>)
    where
        T: TokenType,
    {
        let mut it = tok.input().chars().peekable();

        while let Some(c) = it.next() {
            if c == '\r' {
                if let Some('\n') = it.peek() {
                    it.next();
                    self.newline();
                }
            } else if c == '\n' {
                self.newline();
            } else if c == '\t' {
                self.col += TAB_WIDTH;
            } else {
                self.col += c.width().unwrap_or(0) as u32;
            }
        }
    }
}

/// A trait for types which can be turned into a token stream.
pub trait Tokenize<'i, T: TokenType> {
    /// Construct a `TokenStream` from `self`.
    fn tokenize(&'i self) -> TokenStream<'i, T, Vec<Token<'i, T>>>;
}

impl<'i, T, S> Tokenize<'i, T> for S
where
    T: TokenType,
    S: AsRef<str>,
{
    fn tokenize(&'i self) -> TokenStream<'i, T, Vec<Token<'i, T>>> {
        TokenStream::new(tokenize(self.as_ref()))
    }
}

/// An error produced by a `TokenStream`.
#[derive(Clone, Debug)]
pub enum TokenStreamError<'i, T> {
    /// A token was expected, but there were no tokens remaining.
    UnexpectedEof {
        /// If `Some`, contains the type of token which was expected.
        expected: Option<T>,
    },

    /// A token of one type was expected, but another was found.
    UnexpectedToken {
        /// The type of token which was expected.
        expected: T,

        /// The actual token value which was found.
        actual: Token<'i, T>,
    },
}

impl<'i, T: TokenType> fmt::Display for TokenStreamError<'i, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use TokenStreamError::*;
        match self {
            UnexpectedEof { expected } => match expected {
                Some(exp) => write!(
                    f,
                    "unexpected end of input: expected a token of type {:?}",
                    exp
                ),
                None => write!(f, "unexpected end of input"),
            },
            UnexpectedToken { expected, actual } => {
                write!(
                    f,
                    "unexpected token: expected a token of type {:?}, but found token {:?}",
                    expected, actual
                )
            }
        }
    }
}

impl<'i, T> Error for TokenStreamError<'i, T> where T: TokenType {}

/// A stream of tokens.
pub struct TokenStream<'i, T, S> {
    /// The underlying slice of tokens.
    tokens: S,

    /// The position in the token stream.
    pos: Cell<u64>,

    /// The position in the input stream.
    cursor_pos: Cell<CursorPosition>,

    phantom: PhantomData<&'i T>,
}

impl<'i, T, S> TokenStream<'i, T, S>
where
    T: TokenType,
    S: TokenSlice<'i, T>,
{
    fn new(tokens: S) -> TokenStream<'i, T, S> {
        TokenStream {
            tokens,
            pos: Cell::new(0),
            cursor_pos: Cell::new(CursorPosition::new()),
            phantom: PhantomData,
        }
    }

    fn take_ref(&self) -> TokenStream<'i, T, &[Token<'i, T>]> {
        TokenStream {
            tokens: &self.tokens.as_ref(),
            pos: self.pos.clone(),
            cursor_pos: self.cursor_pos.clone(),
            phantom: PhantomData,
        }
    }

    /// Get the cursor position in the original input.
    pub fn cursor_position(&self) -> CursorPosition {
        self.cursor_pos.get()
    }

    /// Check whether any tokens remain in the stream.
    pub fn is_exhausted(&self) -> bool {
        self.pos.get() as usize == self.tokens.as_ref().len()
    }

    /// Skip contiguous tokens matching a predicate.
    pub fn skip_while<F>(&self, f: F)
    where
        F: Fn(&Token<T>) -> bool,
    {
        while let Some(tok) = self.peek_opt() {
            if f(&tok) {
                self.advance();
            } else {
                break;
            }
        }
    }

    /// Optionally get the next token in the stream without advancing.
    ///
    /// Returns `None` if the stream is exhausted.
    pub fn peek_opt(&self) -> Option<&Token<'i, T>> {
        self.tokens.as_ref().get(self.pos.get() as usize)
    }

    /// Get the next token in the stream without advancing.
    ///
    /// # Errors
    ///
    /// Returns `TokenStreamError::UnexpectedEof` if the stream is exhausted.
    pub fn peek(&self) -> Result<&Token<'i, T>, TokenStreamError<'i, T>> {
        self.peek_opt()
            .ok_or(TokenStreamError::UnexpectedEof { expected: None })
    }

    /// Advance the input stream by one token.
    pub fn advance(&self) {
        if let Some(tok) = self.peek_opt() {
            let mut curs = self.cursor_pos.get();
            curs.advance(&tok);
            self.cursor_pos.set(curs);

            let new_pos = self.pos.get() + 1;
            self.pos.set(new_pos);
        }
    }

    /// Optionally get the next token in the stream and advance.
    ///
    /// Returns `None` if the stream is exhausted.
    pub fn next_opt(&self) -> Option<&Token<'i, T>> {
        self.advance();
        self.tokens.as_ref().get(self.pos.get().min(1) as usize - 1)
    }

    /// Get the next token in the stream and advance.
    ///
    /// # Errors
    ///
    /// Returns `TokenStreamError::UnexpectedEof` if the stream is exhausted.
    pub fn next(&self) -> Result<&Token<'i, T>, TokenStreamError<'i, T>> {
        self.next_opt()
            .ok_or(TokenStreamError::UnexpectedEof { expected: None })
    }

    /// Peek the next token if its type matches the expected value.
    ///
    /// # Errors
    ///
    /// Returns an error if the token's type is not expected or the stream is
    /// exhausted.
    pub fn peek_expect(&self, expected: T) -> Result<&Token<'i, T>, TokenStreamError<'i, T>> {
        let tok = self.peek().map_err(|_| TokenStreamError::UnexpectedEof {
            expected: Some(expected.clone()),
        })?;
        match tok.ty() {
            t if *t == expected => Ok(tok),
            _ => Err(TokenStreamError::UnexpectedToken {
                expected,
                actual: tok.clone(),
            }),
        }
    }

    /// Get the next token if its type matches the expected value.
    ///
    /// If successful, the position of the stream is advanced.
    ///
    /// # Errors
    ///
    /// Returns an error if the token's type is not expected or the stream is
    /// exhausted. In either case, the position of the stream is unchanged.
    pub fn next_expect(&self, expected: T) -> Result<&Token<'i, T>, TokenStreamError<'i, T>> {
        let tok = self.peek().map_err(|_| TokenStreamError::UnexpectedEof {
            expected: Some(expected.clone()),
        })?;
        match tok.ty() {
            t if *t == expected => {
                self.advance();
                Ok(tok)
            }
            _ => Err(TokenStreamError::UnexpectedToken {
                expected,
                actual: tok.clone(),
            }),
        }
    }

    /// Parse a value out of the token stream.
    ///
    /// The three possible return values represent three different parsing outcomes:
    /// - `Ok(Some(val))` is a successful parse.
    /// - `Ok(None)` is a backtracking error.
    /// - `Err(e)` is a fatal error.
    ///
    /// If the parse succeeds, the stream position is updated to reflect the
    /// tokens consumed during the parse. If the parse backtracks or errors, the
    /// stream position is unchanged.
    pub fn parse<'a, P>(&self, bump: &'a Bump) -> Result<Option<P::Output>, P::Error>
    where
        P: Parse<'i, 'a, T>,
    {
        let mut cloned = self.take_ref();

        // If the parse errors, the cloned stream is dropped.
        let val = P::parse(&mut cloned, bump)?;

        // If the parse succeeds, update the stream position.
        if val.is_some() {
            self.pos.set(cloned.pos.get());
            self.cursor_pos.set(cloned.cursor_pos.get());
        }

        Ok(val)
    }
}

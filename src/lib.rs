#![warn(missing_docs)]

//! A flexible, zero-copy recursive descent parsing toolkit.
//!
//! This library provides a set of traits and types useful for constructing
//! lexers and recursive-descent parsers which consume lexer output.  Tokens
//! (lexemes) are defined by the `TokenType` trait, while syntax rules are
//! described by the `Parse` trait.

use std::error::Error;

pub use bumpalo;
use bumpalo::Bump;

pub mod cons;
pub use cons::ConsList;

pub mod stream;
pub use stream::{TokenStream, TokenStreamError, Tokenize};

pub mod token;
pub use token::{Token, TokenSlice, TokenType};

/// A trait for types which may be parsed out of a token stream.
///
/// Implementing this trait for a type allows it to be parsed using
/// [`TokenStream::parse`].
pub trait Parse<'i, 'a, T>: Sized
where
    T: TokenType,
{
    /// The datatype produced by parsing this type.
    ///
    /// In most cases, this will be `Self`. However, this can be combined with
    /// generics to output other types like lists of rules.
    ///
    /// For example, consider Rust's grammar. It contains a large number of
    /// comma-separated lists: in tuple types and expressions, array
    /// expressions, function argument lists, constructors, etc.
    ///
    /// This might be represented using a type `CommaSepList<T>`, where
    /// `Output = Vec<T>`. Then, `CommaSepList<FuncArg>` would parse to
    /// `Vec<FuncArg>`, and so on with the other rules.
    type Output: 'a;

    /// The type of any fatal errors produced when parsing this type.
    type Error: Error;

    /// Attempt to parse a value out of the token stream.
    ///
    /// There are three possible returns:
    /// - If successful, returns `Ok(Some(Self::Output))`.
    /// - If the parser should backtrack and try another rule, returns `Ok(None)`.
    /// - If the error is fatal, returns `Err(Self::Error)`.
    ///
    /// In order to ease propagation of backtracking errors, the `bt!` macro
    /// provides similar semantics to the `?` operator: `bt!(expr)` either
    /// extracts the `Some` variant of `expr` or causes the caller to return
    /// `Ok(None)`.
    fn parse<S>(
        tokens: &mut TokenStream<'i, T, S>,
        bump: &'a Bump,
    ) -> Result<Option<Self::Output>, Self::Error>
    where
        S: TokenSlice<'i, T>;
}

/// Shorthand for backtracking, similar to the `?` operator.
///
/// Takes an expression yielding `Option<T>` as its sole argument.
/// `bt!(Some(val))` yields `val`, while `bt!(None)` causes the calling function
/// to return `Ok(None)`.
#[macro_export]
macro_rules! bt {
    ($e:expr) => {
        match $e {
            Some(val) => val,
            None => return Ok(None),
        }
    };
}

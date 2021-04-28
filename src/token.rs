//! The `Token` type and its associated traits.

use std::fmt;

/// A trait for token type specifiers.
///
/// This will typically be an `enum`. Tokens are returned by reference from the
/// methods of [`TokenStream`], so implementors of this trait may freely store
/// expensive data structures; the `Clone` implementation is only used when
/// constructing errors.
///
/// [`TokenStream`]: ../stream/struct.TokenStream.html
pub trait TokenType: Clone + fmt::Debug + PartialEq + Eq {
    /// Attempts to recognize a token from `input`.
    ///
    /// Implementors should recognize a single token at the start of the input.
    fn token(input: &str) -> Option<Token<Self>>;
}

/// A single token recognized from an input text.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Token<'i, T> {
    ty: T,
    input: &'i str,
}

impl<'i, T> Token<'i, T>
where
    T: TokenType,
{
    /// Constructs a new token from the given type and input.
    ///
    /// If the input is empty, returns `None`. This prevents implementations of
    /// [`TokenType::token`] from causing infinite recursion by matching empty
    /// tokens.
    ///
    /// [`TokenType::token`]: trait.TokenType.html#tymethod.token
    pub fn new(ty: T, input: &'i str) -> Option<Token<'i, T>> {
        if input.is_empty() {
            None
        } else {
            Some(Token { ty, input })
        }
    }

    /// Get the type of this token.
    pub fn ty(&self) -> &T {
        &self.ty
    }

    /// Get the input recognized by this token.
    pub fn input(&self) -> &'i str {
        self.input
    }
}

/// Convenience trait for slices of `Token`.
pub trait TokenSlice<'i, T>: AsRef<[Token<'i, T>]> {}
impl<'i, T, S> TokenSlice<'i, T> for S where S: AsRef<[Token<'i, T>]> {}

/// A macro for automatically generating "tag" tokens.
///
/// Each invocation of the macro generates a single function of the form
/// `fn(&str) -> Option<Token<T>>`.
///
/// ## Example
/// ```rust
/// # use dissent::{tag_tokens, Token, TokenType};
/// // Simple token type that recognizes "a", "b", "c" and "d".
/// #[derive(Copy, Clone, Debug, PartialEq, Eq)]
/// enum AbcdTokenType {
///     A,
///     B,
///     Cd,
/// }
///
/// // Automatically generates the function:
/// // `fn abcd_tag_tokens(input: &input) -> Option<Token<AbcdTokenType>> { ... }`
/// tag_tokens! {
///     abcd_tag_tokens -> AbcdTokenType {
///         "a" => A,
///         "b" => B,
///         "c" , "d" => Cd,
///     }
/// }
///
/// impl TokenType for AbcdTokenType {
///     fn token(input: &str) -> Option<Token<Self>> {
///         abcd_tag_tokens(input)
///     }
/// }
///
/// # fn main() {
/// assert_eq!(abcd_tag_tokens("a"), Token::new(AbcdTokenType::A, "a"));
/// assert_eq!(abcd_tag_tokens("b"), Token::new(AbcdTokenType::B, "b"));
/// assert_eq!(abcd_tag_tokens("c"), Token::new(AbcdTokenType::Cd, "c"));
/// assert_eq!(abcd_tag_tokens("d"), Token::new(AbcdTokenType::Cd, "d"));
/// # }
/// ```
#[macro_export]
macro_rules! tag_tokens {
    (
        $v:vis $rule:ident -> $ttype:ty {
            $( $val:expr $( , $vals:expr)* => $variant:ident ),* $(,)?
        }
    ) => {
        $v fn $rule<'i>(input: &'i str) -> Option<$crate::Token<'i, $ttype>> {
            $(
                if input.starts_with($val)   {
                    $crate::Token::new(<$ttype>::$variant, &input[..$val.len()])
                } $( else if input.starts_with($vals) {
                    $crate::Token::new(<$ttype>::$variant, &input[..$vals.len()])
                })*

                else
            )* {
                None
            }
        }
    }
}

/// A macro for automatically generating tokens based on a regular expression.
///
/// Each invocation of the macro generates a single function of the form
/// `fn(&str) -> Option<Token<T>>`.
///
/// The resulting function will only match at the start of the input; any
/// pattern which does not already start with "\A" will have that prefix added
/// when the regex is compiled.
///
/// The regex is compiled at most once, when the branch is first evaluated.
///
/// ## Example
/// ```rust
/// # use dissent::{regex_tokens, Token, TokenType};
/// // A token type that recognizes words and whitespace.
/// #[derive(Copy, Clone, Debug, PartialEq, Eq)]
/// enum ExampleTokenType {
///     Word,
///     Whitespace,
/// }
///
/// regex_tokens! {
///     example_regex -> ExampleTokenType {
///         // Match one or more letters
///         r"[A-Za-z]+" => Word,
///
///         // Match one or more spaces or tabs
///         r"[ \t]+" => Whitespace,
///     }
/// }
///
/// impl TokenType for ExampleTokenType {
///     fn token(input: &str) -> Option<Token<Self>> {
///         example_regex(input)
///     }
/// }
///
/// # fn main() {
/// assert_eq!(example_regex("some words"), Token::new(ExampleTokenType::Word, "some"));
/// assert_eq!(example_regex("  whitespace"), Token::new(ExampleTokenType::Whitespace, "  "));
/// assert_eq!(example_regex("42"), None);
/// # }
/// ```
#[cfg(feature = "regex")]
#[macro_export]
macro_rules! regex_tokens {
    (
        $v:vis $name:ident -> $tty:ty {
            $( $pattern:literal => $variant:ident ),*
            $(,)?
        }
    ) => {
        $v fn $name(input: &str) -> Option<$crate::Token<$tty>> {
            $(
                if let Some(m) = {
                    lazy_static::lazy_static! {
                        static ref REGEX: regex::Regex = if $pattern.starts_with(r"\A") {
                            regex::Regex::new($pattern).unwrap()
                        } else {
                            regex::Regex::new(concat!(r"\A", $pattern)).unwrap()
                        };
                    }

                    REGEX.find(input)
                } {
                    $crate::Token::new(<$tty>::$variant, &input[..m.end()])
                } else
            )* {
                None
            }
        }
    };
}

const EST_BYTES_PER_TOKEN: usize = 8;

pub(crate) fn tokenize<T>(input: &str) -> Vec<Token<T>>
where
    T: TokenType,
{
    let mut tokens =
        Vec::with_capacity((input.len() + EST_BYTES_PER_TOKEN - 1) / EST_BYTES_PER_TOKEN);
    let mut remaining = input;

    while let Some(tok) = T::token(remaining) {
        remaining = &remaining[tok.input.len()..];
        tokens.push(tok);
    }

    tokens
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum TokTy {
        Bang,
        Star,
        Tick,
    }

    // Make sure `pub` works in token macros.
    mod module {
        use super::*;

        tag_tokens! {
            pub public -> TokTy {
                "*" => Star,
            }
        }

        regex_tokens! {
            pub re_public -> TokTy {
                r"!" => Bang,
                r"'" => Tick,
            }
        }
    }

    impl TokenType for TokTy {
        fn token(input: &str) -> Option<Token<TokTy>> {
            module::public(input).or_else(|| module::re_public(input))
        }
    }

    #[test]
    fn test_tag_tokens_impl() {
        assert_eq!(TokTy::token("!"), Token::new(TokTy::Bang, "!"));
        assert_eq!(TokTy::token("*"), Token::new(TokTy::Star, "*"));
        assert_eq!(TokTy::token("'"), Token::new(TokTy::Tick, "'"));
    }
}

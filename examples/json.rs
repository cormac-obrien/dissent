use std::{error::Error, fmt, marker::PhantomData};

use bumpalo::Bump;
use dissent::{
    bt, exact_tokens, ConsList, Parse, Token, TokenSlice, TokenStream, TokenStreamError, TokenType,
    Tokenize,
};

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum JsonTokenType {
    LBrace,
    RBrace,
    LBracket,
    RBracket,
    Colon,
    Comma,
    Whitespace,
    String,
    Boolean,
    Number,
    Null,
}

exact_tokens! {
    json_exact -> JsonTokenType {
        "{" => LBrace,
        "}" => RBrace,
        "[" => LBracket,
        "]" => RBracket,
        ":" => Colon,
        "," => Comma,
        "false", "true" => Boolean,
        "null" => Null,
    }
}

fn is_whitespace(c: char) -> bool {
    match c {
        '\t' | '\n' | '\r' | ' ' => true,
        _ => false,
    }
}

fn whitespace(input: &str) -> Option<Token<JsonTokenType>> {
    for (i, c) in input.char_indices() {
        if !is_whitespace(c) {
            return Token::new(JsonTokenType::Whitespace, &input[..i]);
        }
    }

    Token::new(JsonTokenType::Whitespace, input)
}

fn is_basic_escape(c: char) -> bool {
    match c {
        '"' | '\\' | '/' | 'b' | 'f' | 'n' | 'r' | 't' => true,
        _ => false,
    }
}

// 'u' + four ASCII hex digits
const UNICODE_ESCAPE_LEN: usize = 5;
fn escape(input: &str) -> Option<&str> {
    let mut it = input.char_indices();

    if it.next()?.1 != '\\' {
        return None;
    }

    match it.next()? {
        (i, 'u') => {
            for _ in 0..4 {
                if !it.next()?.1.is_ascii_hexdigit() {
                    return None;
                }
            }

            Some(&input[..i + UNICODE_ESCAPE_LEN])
        }
        (i, c) if is_basic_escape(c) => Some(&input[..i + c.len_utf8()]),
        _ => None,
    }
}

fn string_char(input: &str) -> Option<&str> {
    match input.chars().next()? {
        '"' | '\\' => None,
        c => Some(&input[..c.len_utf8()]),
    }
}

fn string(input: &str) -> Option<Token<JsonTokenType>> {
    const STRING_DELIM: char = '"';

    if !input.starts_with(STRING_DELIM) {
        return None;
    }

    let mut matched = STRING_DELIM.len_utf8();
    let mut rest = &input[matched..];

    while let Some(s) = escape(rest).or_else(|| string_char(rest)) {
        matched += s.len();
        rest = &input[matched..];
    }

    if !rest.starts_with(STRING_DELIM) {
        None
    } else {
        matched += STRING_DELIM.len_utf8();
        Token::new(JsonTokenType::String, &input[..matched])
    }
}

#[cfg(not(feature = "regex"))]
fn number(input: &str) -> Option<Token<JsonTokenType>> {
    compile_error!("This example requires the \"regex\" feature.");
    None
}

#[cfg(feature = "regex")]
dissent::regex_tokens! {
    number -> JsonTokenType {
        // In order:
        // - An optional leading '-'.
        // - Either a single '0', or a nonzero digit followed by zero or more
        //   digits.
        // - Optionally, a '.' followed by one or more digits.
        // - Optionally, either 'E' or 'e', then an optional '+' or '-',
        //   followed by one or more digits.
        r"-?(?:0|[1-9][0-9]*)(?:\.[0-9]+)?(?:[Ee][+-]?[0-9]+)?" => Number,
    }
}

impl TokenType for JsonTokenType {
    fn token(input: &str) -> Option<Token<JsonTokenType>> {
        json_exact(input)
            .or_else(|| whitespace(input))
            .or_else(|| string(input))
            .or_else(|| number(input))
    }
}

#[derive(Clone, Debug)]
pub enum JsonError<'i> {
    TokenStream(TokenStreamError<'i, JsonTokenType>),
    MemberExpectedValue { key: &'i str },
    ExpectedValue,
}

impl<'i> fmt::Display for JsonError<'i> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            JsonError::TokenStream(e) => write!(f, "{}", e),
            JsonError::MemberExpectedValue { key } => {
                write!(
                    f,
                    "while parsing object member with key {}: expected a value",
                    key
                )
            }
            JsonError::ExpectedValue => write!(f, "expected a value"),
        }
    }
}

impl<'i> From<TokenStreamError<'i, JsonTokenType>> for JsonError<'i> {
    fn from(e: TokenStreamError<'i, JsonTokenType>) -> Self {
        JsonError::TokenStream(e)
    }
}

pub trait JsonTokenStreamExt<'i> {
    fn skip_ws(&mut self);
}

impl<'i, S> JsonTokenStreamExt<'i> for TokenStream<'i, JsonTokenType, S>
where
    S: TokenSlice<'i, JsonTokenType>,
{
    fn skip_ws(&mut self) {
        self.skip_while(|tok| *tok.ty() == JsonTokenType::Whitespace);
    }
}

impl<'i> Error for JsonError<'i> {}

/// Combinator type which skips whitespace tokens.
pub struct SkipWs<T>(PhantomData<T>);

impl<'i, 'a, T> Parse<'i, 'a, JsonTokenType> for SkipWs<T>
where
    T: Parse<'i, 'a, JsonTokenType>,
{
    type Output = T::Output;
    type Error = T::Error;

    fn parse<S>(
        tokens: &mut TokenStream<'i, JsonTokenType, S>,
        bump: &'a Bump,
    ) -> Result<Option<Self::Output>, Self::Error>
    where
        S: TokenSlice<'i, JsonTokenType>,
    {
        tokens.skip_ws();
        tokens.parse::<T>(bump)
    }
}

/// Combinator type which parses comma-separated rules.
pub struct CommaList<T>(PhantomData<T>);

impl<'i, 'a, T> Parse<'i, 'a, JsonTokenType> for CommaList<T>
where
    T: Parse<'i, 'a, JsonTokenType>,
    T::Error: From<JsonError<'i>>,
{
    type Output = ConsList<'a, T::Output>;
    type Error = T::Error;

    fn parse<S>(
        tokens: &mut TokenStream<'i, JsonTokenType, S>,
        bump: &'a Bump,
    ) -> Result<Option<Self::Output>, Self::Error>
    where
        S: TokenSlice<'i, JsonTokenType>,
    {
        let mut items = ConsList::new_in(bump);

        // Match the first item.
        if let Some(first) = tokens.parse::<T>(bump)? {
            items.push(first);

            // Repeatedly match a comma followed by an item.
            loop {
                tokens.skip_ws();
                if tokens.next_expect(JsonTokenType::Comma).is_err() {
                    break;
                }

                tokens.skip_ws();
                let item = tokens.parse::<T>(bump)?.ok_or(JsonError::ExpectedValue)?;
                items.push(item);
            }
        }

        Ok(Some(items))
    }
}

#[derive(Clone, Debug)]
pub enum Value<'i, 'a> {
    Null,
    Object(Object<'i, 'a>),
    Array(Array<'i, 'a>),
    String(&'i str),
    Boolean(&'i str),
    Number(&'i str),
}

impl<'i, 'a> Parse<'i, 'a, JsonTokenType> for Value<'i, 'a>
where
    'i: 'a,
{
    type Output = Self;
    type Error = JsonError<'i>;

    fn parse<S>(
        tokens: &mut TokenStream<'i, JsonTokenType, S>,
        bump: &'a Bump,
    ) -> Result<Option<Self::Output>, Self::Error>
    where
        S: TokenSlice<'i, JsonTokenType>,
    {
        if let Some(obj) = tokens.parse::<Object>(bump)? {
            Ok(Some(Value::Object(obj)))
        } else if let Some(arr) = tokens.parse::<Array>(bump)? {
            Ok(Some(Value::Array(arr)))
        } else if let Some(s) = tokens.next_expect(JsonTokenType::String).ok() {
            Ok(Some(Value::String(s.input())))
        } else if let Some(b) = tokens.next_expect(JsonTokenType::Boolean).ok() {
            Ok(Some(Value::Boolean(b.input())))
        } else if let Some(n) = tokens.next_expect(JsonTokenType::Number).ok() {
            Ok(Some(Value::Number(n.input())))
        } else {
            Ok(None)
        }
    }
}

#[derive(Clone, Debug)]
pub struct Object<'i, 'a> {
    members: ConsList<'a, Member<'i, 'a>>,
}

impl<'i, 'a> Parse<'i, 'a, JsonTokenType> for Object<'i, 'a>
where
    'i: 'a,
{
    type Output = Self;
    type Error = JsonError<'i>;

    fn parse<S>(
        tokens: &mut TokenStream<'i, JsonTokenType, S>,
        bump: &'a Bump,
    ) -> Result<Option<Self::Output>, Self::Error>
    where
        S: TokenSlice<'i, JsonTokenType>,
    {
        bt!(tokens.next_expect(JsonTokenType::LBrace).ok());

        let members = tokens.parse::<SkipWs<CommaList<Member>>>(bump)?.unwrap();

        tokens.skip_ws();
        tokens.next_expect(JsonTokenType::RBrace)?;

        Ok(Some(Object { members }))
    }
}

#[derive(Clone, Debug)]
pub struct Member<'i, 'a> {
    key: &'i str,
    value: Value<'i, 'a>,
}

impl<'i, 'a> Parse<'i, 'a, JsonTokenType> for Member<'i, 'a>
where
    'i: 'a,
{
    type Output = Self;
    type Error = JsonError<'i>;

    fn parse<S>(
        tokens: &mut TokenStream<'i, JsonTokenType, S>,
        bump: &'a Bump,
    ) -> Result<Option<Self::Output>, Self::Error>
    where
        S: TokenSlice<'i, JsonTokenType>,
    {
        let key = bt!(tokens.next_expect(JsonTokenType::String).ok()).input();

        tokens.skip_ws();
        tokens.next_expect(JsonTokenType::Colon)?;

        let value = tokens
            .parse::<SkipWs<Value>>(bump)?
            .ok_or(JsonError::MemberExpectedValue { key })?;

        Ok(Some(Member { key, value }))
    }
}

/// A JSON array.
#[derive(Clone, Debug)]
pub struct Array<'i, 'a> {
    elements: ConsList<'a, Value<'i, 'a>>,
}

impl<'i, 'a> Parse<'i, 'a, JsonTokenType> for Array<'i, 'a>
where
    'i: 'a,
{
    type Output = Self;
    type Error = JsonError<'i>;

    fn parse<S>(
        tokens: &mut TokenStream<'i, JsonTokenType, S>,
        bump: &'a Bump,
    ) -> Result<Option<Self::Output>, Self::Error>
    where
        S: TokenSlice<'i, JsonTokenType>,
    {
        bt!(tokens.next_expect(JsonTokenType::LBracket).ok());

        let elements = tokens
            .parse::<SkipWs<CommaList<Value>>>(bump)?
            .ok_or(JsonError::ExpectedValue)?;

        tokens.skip_ws();
        tokens.next_expect(JsonTokenType::RBracket)?;

        Ok(Some(Array { elements }))
    }
}

fn main() {
    let args = std::env::args().collect::<Vec<_>>();
    let bump = Bump::with_capacity(8 * 1024 * 1024);

    let input = match args.get(1) {
        Some(input) => match input.as_str() {
            "-h" | "--help" => {
                println!("usage: {} <json>", &args[0]);
                return;
            }
            _ => input.to_owned(),
        },
        None => {
            let stdin = std::io::stdin();
            use std::io::Read;
            let mut input = String::with_capacity(8 * 1024 * 1024);
            stdin.lock().read_to_string(&mut input).unwrap();
            input
        }
    };

    match input.tokenize().parse::<Value>(&bump) {
        Ok(v) => {
            println!("{:#?}", v);
        }
        Err(e) => {
            eprintln!("{}", e);
        }
    }
}

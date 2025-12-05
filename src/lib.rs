//! # parse-more
//! Parse-more is an extension of the [syn::parse::Parse] trait from the [syn](https://docs.rs/syn/) crate, allowing to parse input from procedural macros directly, without having to create a custom structure and implementing the [syn::parse::Parse] trait on it.
//!
//! It provides classic [syn](https://docs.rs/syn/) macros and functions variant, using the [ParseMore] trait instead.
//!
//! # Example
//!
//! ```
//! # extern crate proc_macro;
//! use quote::quote;
//! use parse_more::{parse_more_macro_input, Concat, Braced};
//! use proc_macro::TokenStream;
//! use syn::{Expr, Ident, Token, punctuated::Punctuated};
//!
//! # const IGNORE_TOKENS: &str = stringify! {
//! #[proc_macro]
//! # };
//! pub fn complex_args(input: TokenStream) -> TokenStream {
//!    let content = parse_more_macro_input!(
//!        input as Punctuated<Concat<Ident, Token![=>], Braced<(Ident, Expr)>>, Token![,]>
//!    );
//!    content
//!        .into_iter()
//!        .map(|concat| {
//!            // Second item is discarded (it's the => arrow)
//!            let (ident, _, Braced((other_ident, literal))) = concat.into();
//!            quote! {
//!                println!("{}: {} versus other type {}", #literal, (-1i8) as #ident, (-1i8) as #other_ident);
//!            }
//!        })
//!        .collect::<proc_macro2::TokenStream>()
//!        .into()
//! }
//! ```
//! And then :
//! ```
//! # macro_rules! complex_args { ($($tt:tt)*) => {} }
//! complex_args! {
//!     u8 => {
//!         (i8, "u8 integer")
//!     },
//!     u16 => {
//!         (i16, "u16 integer")
//!     },
//!     Foo => {
//!         (Bar, 8 + 42)
//!     }
//! }
//! ```

extern crate proc_macro;

pub mod syn_types;

/// Re-export `crate` as `parse_more` to use the `parse_more` macro easily.
pub use crate as parse_more;

/// Re-export proc macro.
pub use parse_more_macros::{filler, parse_more};

use syn::{
    braced, bracketed, parenthesized,
    parse::{Nothing, Parse},
    punctuated::Punctuated,
    LitInt, LitStr,
};

/// Parsing interface implemented by all types from the [syn] crate which already implement [syn::parse::Parse], and some others usefull ones.
/// Use the [parse_more_auto_impl] macros to easily implement [ParseMore] on a type which already implement [syn::parse::Parse].
pub trait ParseMore: Sized {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self>;
}

/// This wrapper implements [syn::parse::Parse] when T implements [ParseMore]. It permits to use this wrapper and a type implementing [ParseMore] in a parsing function from [syn].
///
/// You should probably use [parse_more()], [parse_more_macro_input], or any other function from this crate instead of using this type directly.
///
/// # Example
///
/// ```
/// # extern crate proc_macro;
/// use quote::quote;
/// use parse_more::ParseMoreWrapper;
/// use proc_macro::TokenStream;
/// use syn::{Ident, Token};
///
/// # const IGNORE_TOKENS: &str = stringify! {
/// #[proc_macro]
/// # };
/// pub fn flip_identifiers(input: TokenStream) -> TokenStream {
///     let (ident_a, arrow, ident_b) = syn::parse::<ParseMoreWrapper<(Ident, Token![=>], Ident)>>(input).unwrap().0;
///     quote! {
///         #ident_b <= #ident_a
///     }.into()
/// }
/// ```
pub struct ParseMoreWrapper<T>(pub T);

/// Call the [ParseMore::parse] method.
impl<T: ParseMore> Parse for ParseMoreWrapper<T> {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        Ok(ParseMoreWrapper(ParseMore::parse(input)?))
    }
}

/// This macro auto-implements the [ParseMore] traits on its arguments, which *MUST* implement the [syn::parse::Parse] trait.
/// It allows using custom types inside of any parse-more macros/functions.
///
/// See the [macro@parse_more] macro.
///
/// # Example
///
/// ```
/// use parse_more::parse_more_auto_impl;
/// use syn::{Ident, Token};
///
/// struct MyParsedStruct(Ident, Ident);
///
/// impl syn::parse::Parse for MyParsedStruct {
///     fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
///         let a = input.parse()?;
///         input.parse::<Token![=>]>()?;
///         let b = input.parse()?;
///         Ok(Self(a, b))
///     }
/// }
///
/// parse_more_auto_impl! {
///     MyParsedStruct
/// }
/// ```
#[macro_export]
macro_rules! parse_more_auto_impl {
    ($($ty:ty),*) => {
        $(impl $crate::ParseMore for $ty {
            fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
                <Self as syn::parse::Parse>::parse(input)
            }
        })*
    }
}

/// Implement [ParseMore] for a given tuple.
macro_rules! tuple_impls {
    ($first:ident) => {
        impl<$first:ParseMore> ParseMore for ($first, ) {
            fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
                let content;
                parenthesized!(content in input);
                let first = content.parse::<ParseMoreWrapper<$first>>()?.0;
                content.parse::<syn::Token![,]>()?;
                Ok((first,))
            }
        }
    };
    ($first:ident $($generics:ident)*) => {
        impl<$first:ParseMore, $($generics: ParseMore),*> ParseMore for ($first, $($generics,)*) {
            fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
                let content;
                parenthesized!(content in input);
                let first = content.parse::<ParseMoreWrapper<$first>>()?.0;
                let res = Ok((first,
                    $({
                        content.parse::<syn::Token![,]>()?;
                        content.parse::<ParseMoreWrapper<$generics>>()?.0
                    },)*
                ));

                // If there is a remaining comma, parse it
                if content.peek(syn::Token![,]) {
                    content.parse::<syn::Token![,]>().unwrap();
                }
                res
            }
        }
    };
}

/// Inner code of the [for_each_tuple] macro.
macro_rules! for_each_tuple_ {
    ($mac:ident =>) => {};
    ($mac:ident => $first:ident, $($generics:ident,)*) => {
        $mac! {
            $first $($generics)*
        }
        for_each_tuple_ ! {
            $mac => $($generics,)*
        }
    };
}

/// Call a macro over every tuple size between 1 and 20.
macro_rules! for_each_tuple {
    ($mac:ident) => {
        for_each_tuple_! {
            $mac => A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S, T,
        }
    };
}

// Generate [ParseMore] impls for tuples.
for_each_tuple! {
    tuple_impls
}

/// Implement [ParseMore] for the array type.
/// ```
/// # extern crate proc_macro;
/// use quote::quote;
/// use parse_more::parse_more_macro_input;
/// use proc_macro::TokenStream;
/// use syn::{Ident, Token};
///
/// # const IGNORE_TOKENS: &str = stringify! {
/// #[proc_macro]
/// # };
/// pub fn identifiers_sum(input: TokenStream) -> TokenStream {
///     let idents = parse_more_macro_input!(input as [Ident; 3]);
///     let [a, b, c] = idents;
///     quote! {
///         #a + #b + #c
///     }.into()
/// }
/// ```
impl<T: ParseMore, const N: usize> ParseMore for [T; N] {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let content;
        bracketed!(content in input);

        let mut res = vec![];
        for i in 0..N {
            if i != 0 {
                content.parse::<syn::Token![,]>()?;
            }
            res.push(content.parse::<ParseMoreWrapper<T>>()?.0)
        }

        // If there is a remaining comma, parse it
        if content.peek(syn::Token![,]) {
            content.parse::<syn::Token![,]>().unwrap();
        }
        Ok(unsafe { res.try_into().unwrap_unchecked() })
    }
}

/// Implement [ParseMore] for the [Vec] type, with a behaviour similar to [syn::punctuated::Punctuated<T, syn::parse::Nothing>]
/// ```
/// # extern crate proc_macro;
/// use quote::quote;
/// use parse_more::parse_more_macro_input;
/// use proc_macro::TokenStream;
/// use syn::Ident;
///
/// # const IGNORE_TOKENS: &str = stringify! {
/// #[proc_macro]
/// # };
/// pub fn identifiers_sum(input: TokenStream) -> TokenStream {
///     let idents = parse_more_macro_input!(input as Vec<Ident>);
///     idents.into_iter().map(|ident| quote! {
///         #ident
///     }).collect::<proc_macro2::TokenStream>().into()
/// }
/// ```
impl<T: ParseMore> ParseMore for Vec<T> {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let mut res = vec![];
        while let Ok(parsed) = input.parse::<ParseMoreWrapper<T>>() {
            res.push(parsed.0);
        }
        Ok(res)
    }
}

/// Implement [ParseMore] for the [syn::punctuated::Punctuated] type.
/// ```
/// # extern crate proc_macro;
/// use quote::quote;
/// use parse_more::parse_more_macro_input;
/// use proc_macro::TokenStream;
/// use syn::{Ident, Token, punctuated::Punctuated};
///
/// # const IGNORE_TOKENS: &str = stringify! {
/// #[proc_macro]
/// # };
/// pub fn identifiers_sum(input: TokenStream) -> TokenStream {
///     let idents = parse_more_macro_input!(input as Punctuated<Ident, Token![,]>);
///     idents.into_iter().map(|ident| quote! {
///         #ident
///     }).collect::<proc_macro2::TokenStream>().into()
/// }
/// ```
impl<T: ParseMore, P: ParseMore> ParseMore for Punctuated<T, P> {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let mut res = Punctuated::new();
        let wrapped =
            Punctuated::<ParseMoreWrapper<T>, ParseMoreWrapper<P>>::parse_terminated(input)?;

        // Unwrap parsed values
        wrapped.into_pairs().for_each(|pair| {
            let pair = pair.into_tuple();
            res.push_value(pair.0 .0);
            if let Some(punct) = pair.1 {
                res.push_punct(punct.0);
            }
        });

        Ok(res)
    }
}

/// Parse successive items.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[parse_more]
pub struct Concat<A, B, C = Nothing, D = Nothing, E = Nothing, F = Nothing, G = Nothing> {
    first: A,
    second: B,
    third: C,
    fourth: D,
    fifth: E,
    sixth: F,
    seventh: G,
}

impl<A, B, C, D, E, F, G> From<Concat<A, B, C, D, E, F, G>> for (A, B, C, D, E, F, G) {
    fn from(value: Concat<A, B, C, D, E, F, G>) -> Self {
        (
            value.first,
            value.second,
            value.third,
            value.fourth,
            value.fifth,
            value.sixth,
            value.seventh,
        )
    }
}
impl<A, B, C, D, E, F> From<Concat<A, B, C, D, E, F>> for (A, B, C, D, E, F) {
    fn from(value: Concat<A, B, C, D, E, F>) -> Self {
        (
            value.first,
            value.second,
            value.third,
            value.fourth,
            value.fifth,
            value.sixth,
        )
    }
}
impl<A, B, C, D, E> From<Concat<A, B, C, D, E>> for (A, B, C, D, E) {
    fn from(value: Concat<A, B, C, D, E>) -> Self {
        (
            value.first,
            value.second,
            value.third,
            value.fourth,
            value.fifth,
        )
    }
}
impl<A, B, C, D> From<Concat<A, B, C, D>> for (A, B, C, D) {
    fn from(value: Concat<A, B, C, D>) -> Self {
        (value.first, value.second, value.third, value.fourth)
    }
}
impl<A, B, C> From<Concat<A, B, C>> for (A, B, C) {
    fn from(value: Concat<A, B, C>) -> Self {
        (value.first, value.second, value.third)
    }
}
impl<A, B> From<Concat<A, B>> for (A, B) {
    fn from(value: Concat<A, B>) -> Self {
        (value.first, value.second)
    }
}
impl<A, B> Concat<A, B> {
    /// Convert itself to a tuple containing the parsed values.
    pub fn into_tuple2(self) -> (A, B) {
        self.into()
    }
}
impl<A, B, C> Concat<A, B, C> {
    /// Convert itself to a tuple containing the parsed values.
    pub fn into_tuple3(self) -> (A, B, C) {
        self.into()
    }
}
impl<A, B, C, D> Concat<A, B, C, D> {
    /// Convert itself to a tuple containing the parsed values.
    pub fn into_tuple4(self) -> (A, B, C, D) {
        self.into()
    }
}
impl<A, B, C, D, E> Concat<A, B, C, D, E> {
    /// Convert itself to a tuple containing the parsed values.
    pub fn into_tuple5(self) -> (A, B, C, D, E) {
        self.into()
    }
}
impl<A, B, C, D, E, F> Concat<A, B, C, D, E, F> {
    /// Convert itself to a tuple containing the parsed values.
    pub fn into_tuple6(self) -> (A, B, C, D, E, F) {
        self.into()
    }
}
impl<A, B, C, D, E, F, G> Concat<A, B, C, D, E, F, G> {
    /// Convert itself to a tuple containing the parsed values.
    pub fn into_tuple7(self) -> (A, B, C, D, E, F, G) {
        self.into()
    }
}

/// Parse an item surrounded by braces.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Braced<T>(pub T);

/// Imlement [ParseMore] for the [Braced] type.
impl<T: ParseMore> ParseMore for Braced<T> {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let content;
        braced!(content in input);
        Ok(Self(content.parse::<ParseMoreWrapper<T>>()?.0))
    }
}

impl<T> Braced<T> {
    /// Get the parsed value.
    pub fn value(self) -> T {
        self.0
    }
}

/// Parse an item surrounded by parenthesis.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Parenthesized<T>(pub T);

/// Imlement [ParseMore] for the [Parenthesized] type.
impl<T: ParseMore> ParseMore for Parenthesized<T> {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let content;
        parenthesized!(content in input);
        Ok(Self(content.parse::<ParseMoreWrapper<T>>()?.0))
    }
}

impl<T> Parenthesized<T> {
    /// Get the parsed value.
    pub fn value(self) -> T {
        self.0
    }
}

/// Parse an item surrounded by brackets.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Bracketed<T>(pub T);

/// Imlement [ParseMore] for the [Bracketed] type.
impl<T: ParseMore> ParseMore for Bracketed<T> {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let content;
        bracketed!(content in input);
        Ok(Self(content.parse::<ParseMoreWrapper<T>>()?.0))
    }
}

impl<T> Bracketed<T> {
    /// Get the parsed value.
    pub fn value(self) -> T {
        self.0
    }
}

/// Imlement [ParseMore] for the [Option] type.
impl<T: ParseMore> ParseMore for Option<T> {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        // Fork the input to be sure to don't advance the cursor if the parsing fails.
        let input_forked = input.fork();
        if let Ok(parsed) = input_forked.parse::<ParseMoreWrapper<T>>() {
            // Parse it on the primary stream too to advance the cursor
            // It should not fails.
            assert!(input.parse::<ParseMoreWrapper<T>>().is_ok());
            Ok(Some(parsed.0))
        } else {
            Ok(None)
        }
    }
}

/// Parse an item surrounded by brackets.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Invalid;

/// Imlement [ParseMore] for the [Invalid] type.
impl ParseMore for Invalid {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        Err(syn::Error::new(input.span(), "Invalid can never be parsed"))
    }
}

/// Parse an item in a given list. If multiple types can be parsed, the first one is chosen.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[parse_more]
pub enum Either<A, B, C = Invalid, D = Invalid, E = Invalid, F = Invalid, G = Invalid> {
    First(A),
    Second(B),
    Third(C),
    Fourth(D),
    Fifth(E),
    Sixth(F),
    Seventh(G),
}

impl<A, B, C, D, E, F, G> Either<A, B, C, D, E, F, G> {
    /// Check if the type of the parsed value is the first one.
    pub fn is_first(&self) -> bool {
        matches!(self, Either::First(_))
    }
    /// Check if the type of the parsed value is the second one.
    pub fn is_second(&self) -> bool {
        matches!(self, Either::Second(_))
    }
    /// Check if the type of the parsed value is the third one.
    pub fn is_third(&self) -> bool {
        matches!(self, Either::Third(_))
    }
    /// Check if the type of the parsed value is the fourth one.
    pub fn is_fourth(&self) -> bool {
        matches!(self, Either::Fourth(_))
    }
    /// Check if the type of the parsed value is the fifth one.
    pub fn is_fifth(&self) -> bool {
        matches!(self, Either::Fifth(_))
    }
    /// Check if the type of the parsed value is the sixth one.
    pub fn is_sixth(&self) -> bool {
        matches!(self, Either::Sixth(_))
    }
    /// Check if the type of the parsed value is the seveth one.
    pub fn is_seventh(&self) -> bool {
        matches!(self, Either::Seventh(_))
    }
}

macro_rules! integer_impls {
    ($($ty:ty),*) => {
        $(
            /// Imlement [ParseMore] for the [u8] type.
            impl ParseMore for $ty {
                fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
                    input.parse::<LitInt>()?.base10_parse::<Self>()
                }
            }
        )*
    };
}

integer_impls! {
    u8, u16, u32, u64, u128, usize,
    i8, i16, i32, i64, i128, isize
}

/// Imlement [ParseMore] for the [String] type.
impl ParseMore for String {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        Ok(input.parse::<LitStr>()?.value())
    }
}

/// Same as the [syn::parse_quote] macro, but using the [ParseMore] trait.
#[macro_export]
macro_rules! parse_more_quote {
    ($($tt:tt)*) => {{
        // Add an type hint for the compiler
        let __tmp: $crate::ParseMoreWrapper<_> = syn::parse_quote!($($tt:tt)*);
        __tmp.0
    }};
}

/// Same as the [syn::parse_macro_input] macro, but using the [ParseMore] trait.
#[macro_export]
macro_rules! parse_more_macro_input {
    ($tokenstream:ident as $ty:ty) => {
        match $crate::parse_more::<$ty>($tokenstream) {
            Ok(data) => data,
            Err(err) => {
                return proc_macro::TokenStream::from(err.to_compile_error());
            }
        }
    };
    ($tokenstream:ident) => {
        $crate::parse_more_macro_input!($tokenstream as _)
    };
}

/// Same as the [syn::parse()] function, but using the [ParseMore] trait.
pub fn parse_more<T: ParseMore>(tokens: proc_macro::TokenStream) -> syn::Result<T> {
    Ok(syn::parse::<ParseMoreWrapper<T>>(tokens)?.0)
}

/// Same as the [syn::parse2] function, but using the [ParseMore] trait.
pub fn parse2_more<T: ParseMore>(tokens: proc_macro2::TokenStream) -> syn::Result<T> {
    Ok(syn::parse2::<ParseMoreWrapper<T>>(tokens)?.0)
}

/// Same as the [syn::parse_str] function, but using the [ParseMore] trait.
pub fn parse_more_str<T: ParseMore>(s: &str) -> syn::Result<T> {
    Ok(syn::parse_str::<ParseMoreWrapper<T>>(s)?.0)
}

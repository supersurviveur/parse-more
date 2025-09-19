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
//!        input as Punctuated<Concat<(Ident, Token![=>], Braced<(Ident, Expr)>)>, Token![,]>
//!    );
//!    content
//!        .into_iter()
//!        .map(|concat| {
//!            // Second item is discarded (it's the => arrow)
//!            let (ident, _, Braced((other_ident, literal))) = concat.value();
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

use syn::{braced, bracketed, parenthesized, parse::Parse, punctuated::Punctuated};

/// Parsing interface implemented by all types from the [syn] crate which already implement [syn::parse::Parse], and some others usefull ones.
/// Use the [parse_more_auto_impl] macros to easily implement [ParseMore] on a type which already implement [syn::parse::Parse].
pub trait ParseMore: Sized {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self>;
}

/// This wrapper implements [syn::parse::Parse] when T implements [ParseMore]. It permits to use this wrapper and a type implementing [ParseMore] in a parsing function from [syn].
///
/// You should probably use [parse_more], [parse_more_macro_input], or any other function from this crate instead of using this type directly.
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
/// FIXME: create a derive macro to handle this.
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
pub struct Concat<T>(pub T);

/// Imlement [ParseMore] for the [Concat] type.
macro_rules! concat_impls {
    ($($generics:ident)*) => {
        impl<$($generics: ParseMore),*> ParseMore for Concat<($($generics,)*)> {
            fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
                Ok(Self((
                    $(input.parse::<ParseMoreWrapper<$generics>>()?.0,)*
                )))
            }
        }
    };
}

impl<T> Concat<T> {
    /// Get the parsed value, as a tuple containing all items.
    pub fn value(self) -> T {
        self.0
    }
}

for_each_tuple! { concat_impls }

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

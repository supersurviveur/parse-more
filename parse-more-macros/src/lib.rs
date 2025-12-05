use proc_macro::TokenStream;
use proc_macro2::Span;
use quote::{format_ident, quote};
use syn::{parse_quote, spanned::Spanned, Attribute, ItemEnum, ItemStruct};

/// Auto-implements the parse_more::ParseMore trait on an item.
///
/// # Example
/// ```rust, ignore
/// use parse_more::{parse_more, filler};
/// use syn::{Ident, Expr, Token};
///
/// #[parse_more]
/// struct Foo {
///     name: Ident,
///     #[filler(Token![=>])]
///     values: (Expr, Expr),
/// }
/// ```
#[proc_macro_attribute]
pub fn parse_more(_args: TokenStream, input: TokenStream) -> TokenStream {
    if let Ok(mut struct_item) = syn::parse::<ItemStruct>(input.clone()) {
        let struct_ident = &struct_item.ident;

        let mut named_generics = struct_item.generics.clone();
        named_generics.params.iter_mut().for_each(|param| match param {
            syn::GenericParam::Type(type_param) => type_param.default = None,
            syn::GenericParam::Const(const_param) => const_param.default = None,
            _ => {}
        });
        let mut generics = named_generics.clone();
        generics.params.iter_mut().for_each(|param| match param {
            syn::GenericParam::Type(type_param) => {
                type_param.bounds.push(syn::TypeParamBound::Trait(parse_quote!(parse_more::ParseMore)));
            },
            _ => {}
        });

        let mut parsed = vec![];
        let mut field_idents = vec![];

        let edit_attributes = |attrs: &mut Vec<Attribute>, parsed: &mut Vec<_>| {
            // Remove filler attributes and parse the corresponding item.
            attrs.iter().cloned().enumerate().filter_map(|(i, attribute)| {
                if attribute.path().segments.last().is_some_and(|arg | arg.ident == "filler") {
                    let path = attribute.path();
                    let path_struct = format_ident!("__AvoidImportWarning{}", i);
                    match attribute.parse_args::<syn::Type>() {
                        Err(e) => Some(Err(e)),
                        Ok(ty) => {
                            parsed.push(quote! {
                                input.parse::<parse_more::ParseMoreWrapper<#ty>>()?;
                                #[#path]
                                struct #path_struct;
                            });
                            None
                        }
                    }
                } else {
                    Some(Ok(attribute))
                }
            }).collect::<Result<Vec<_>, _>>()
        };

        for field in &mut struct_item.fields {
            let field_ident = &field.ident;
            let field_type = &field.ty;

            // Remove filler attributes and parse the corresponding item.
            field.attrs = match edit_attributes(&mut field.attrs, &mut parsed) {
                Ok(attrs) => attrs,
                Err(e) => return e.into_compile_error().into(),
            };

            // Add the current field to fields initialization and parse it.
            field_idents.push(field_ident.clone());
            parsed.push(quote! {
                let #field_ident = input.parse::<parse_more::ParseMoreWrapper<#field_type>>()?.0;
            });
        }

        quote! {
            #struct_item
            impl #generics parse_more::ParseMore for #struct_ident #named_generics {
                fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
                    #(#parsed)*
                    Ok(Self {
                        #(#field_idents),*
                    })
                }
            }
        }
    } else if let Ok(enum_item) = syn::parse::<ItemEnum>(input) {
        let enum_ident = &enum_item.ident;

        let mut named_generics = enum_item.generics.clone();
        named_generics.params.iter_mut().for_each(|param| match param {
            syn::GenericParam::Type(type_param) => type_param.default = None,
            syn::GenericParam::Const(const_param) => const_param.default = None,
            _ => {}
        });
        let mut generics = named_generics.clone();
        generics.params.iter_mut().for_each(|param| match param {
            syn::GenericParam::Type(type_param) => {
                type_param.bounds.push(syn::TypeParamBound::Trait(parse_quote!(parse_more::ParseMore)));
            },
            _ => {}
        });

        let mut parsed = vec![];

        for (i, variant) in enum_item.variants.iter().enumerate() {
            let variant_ident = &variant.ident;
            // If the variant fields are not of len 1, we don't know how to parse it (Using Concat, Tuple, Either) ?
            // So we raise an error.
            if variant.fields.len() != 1 {
                return syn::Error::new(variant.fields.span(), "ParseMore derive macro require that enum variants contains exactly one type.").into_compile_error().into();
            }
            let variant_type = &variant.fields.iter().next().unwrap().ty;

            // If it's the first iteration, err isn't already initialized.
            let error = if i == 0 {
                quote! {
                    err = e
                }
            } else {
                quote! {
                    err.combine(e)
                }
            };
            // Try parse the current variant, return it if success (by parsing it again since we parsed it in a fork of the input,
            // to avoid advancing the cursor in case of a well formed start and then a failure).
            parsed.push(quote! {
                match input.fork().parse::<parse_more::ParseMoreWrapper<#variant_type>>() {
                    Ok(_) => return Ok(Self::#variant_ident(input.parse::<parse_more::ParseMoreWrapper<#variant_type>>().unwrap().0)),
                    Err(e) => #error,
                }
            });
        }

        quote! {
            #enum_item
            impl #generics parse_more::ParseMore for #enum_ident #named_generics {
                fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
                    let mut err;
                    #(#parsed)*
                    Err(err)
                }
            }
        }
    } else {
        syn::Error::new(
            Span::call_site(),
            "This macro attribute must be applied on a struct or an enum",
        )
        .into_compile_error()
    }
    .into()
}

/// Parse an additionnal type between two struct fields.
///
/// # Example
/// ```rust, ignore
/// use parse_more::{parse_more, filler};
/// use syn::{Ident, Expr, Token};
///
/// #[parse_more]
/// struct Foo {
///     name: Ident,
///     #[filler(Token![=>])]
///     values: (Expr, Expr),
/// }
/// ```
#[proc_macro_attribute]
pub fn filler(_args: TokenStream, _input: TokenStream) -> TokenStream {
    TokenStream::new()
}

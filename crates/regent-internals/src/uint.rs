// SPDX-License-Identifier: MPL-2.0

//! Types modeling unsigned integer primitives.

use super::*;

/// Implements [`fmt::Display`] for the given unsigned integer model.
macro_rules! impl_display {
    ($ty:ty) => {
        impl fmt::Display for $ty {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(f, "u{}", self.width)
            }
        }
    };
}

/// Models a (possibly imaginary) unsigned integer type of arbitrary bit-width:
/// <code>u&#8239;<em>width</em></code>.
///
/// This type corresponds to the *&lt;uint-type&gt;* syntactical rule from the struct specification
/// and can express any unsigned integer type permissible in [`bitwise!`] struct syntax.
///
/// This type is not [spanned].
///
/// [spanned]: Span2
#[derive(Clone, Copy)]
pub(crate) struct PseudoType {
    width: usize,
}

impl PseudoType {
    /// Attempts to parse a `PseudoType` from a [`syn::Ident`].
    ///
    /// This returns `None` if `ident` is not an unsigned integer (i.e., not of the form
    /// <code>u&#8239;<em>width</em></code>), `Some(Err(_))` if `ident` appears to be an unsigned
    /// integer but the *width* suffix fails to parse or is zero, and `Some(Ok(_))` otherwise.
    pub(crate) fn parse(ident: &syn::Ident) -> Option<Result<Self>> {
        let (span, ident) = (ident.span(), ident.to_string());
        let Some(("", width)) = ident.split_once('u') else {
            // This is not even an unsigned integer!
            return None;
        };
        let Ok(width) = width.parse() else {
            return Some(Err(err!(span; "integer has invalid width suffix")));
        };
        if width == 0 {
            return Some(Err(err!(span; "this cannot be zero-sized")));
        }

        Some(Ok(Self { width }))
    }

    /// The bit-width of this type.
    ///
    /// This is guaranteed to be non-zero.
    pub(crate) fn width(&self) -> usize {
        self.width
    }

    /// Rounds [the width] of this type up to the next smallest power of two that is at least 8.
    ///
    /// This type is not guaranteed to [exist] after calling this method. For example, if the
    /// initial width is 129, it will be rounded up to 256 despite the nonexistence of the `u256`
    /// primitive.
    ///
    /// [the width]: Self::width
    /// [exist]: Self::exists
    ///
    /// # Examples
    ///
    /// ```ignore
    /// let span: Span2;
    /// # span = Span2::call_site();
    /// let Some(Ok(mut ty)) = PseudoType::parse(&syn::Ident::new("u37", span)) else {
    ///     return Err(err!("not an unsigned integer type"));
    /// }
    /// assert_eq!(ty.width(), 37);
    /// ty.round_up();
    /// assert_eq!(ty.width(), 64);
    /// ty.round_up();
    /// // 64 is already a power of two, so the width is unchanged.
    /// assert_eq!(ty.width(), 64);
    /// ```
    pub(crate) fn round_up(&mut self) {
        if self.width <= 8 {
            self.width = 8;
            return;
        }

        let exp = self.width.ilog2() as usize;
        let rem = self.width & ((1 << exp) - 1);

        if rem > 0 {
            self.width = 1 << (exp + 1);
        }
    }

    /// Determines if this pseudo-type models an unsigned integer primitive that exists in Rust.
    ///
    /// This method returns `true` only if [the width] of this type is a power of two between 8 and
    /// 128, inclusive.
    ///
    /// [the width]: Self::width
    pub(crate) fn exists(&self) -> bool {
        matches!(self.width, 8 | 16 | 32 | 64 | 128)
    }

    /// Attempts to convert this `PseudoType` into a [`RustType`].
    ///
    /// This method returns `None` if this pseudo-type does not [exist].
    ///
    /// [exist]: Self::exists
    ///
    /// # Examples
    ///
    /// Imaginary pseudo-type:
    ///
    /// ```ignore
    /// let ty: PseudoType;
    /// # ty = PseudoType { width: 37 };
    /// assert_eq!(ty.width(), 37);
    /// assert_eq!(ty.try_into_rust_type(), None);
    /// ```
    ///
    /// Real pseudo-type:
    ///
    /// ```ignore
    /// let ty: PseudoType;
    /// # ty = PseudoType { width: 64 };
    /// assert_eq!(ty.width(), 64);
    /// assert_eq!(ty.try_into_rust_type(), Some(_));
    /// ```
    pub(crate) fn try_into_rust_type(self) -> Option<RustType> {
        self.exists().then_some(RustType { width: self.width })
    }
}

impl_display!(PseudoType);

/// Models an unsigned integer primitive that exists in Rust: `u8`, `u16`, `u32`, `u64`, or `u128`.
///
/// This type is not [spanned].
///
/// [spanned]: Span2
#[derive(Clone, Copy)]
pub(crate) struct RustType {
    width: usize,
}

impl RustType {
    /// Determines the best representation, or storage type, for an item.
    ///
    /// # Arguments
    ///
    /// - `item_span` is a span covering the entire item.
    /// - `item_ident` is the name of the item and is used to generate precise error messages.
    /// - `item_width` is the computed bit-width of the item.
    /// - `item_attrs` is a mutable reference to the outer attributes on the item.
    /// - `const_ctx` corresponds to [`Output::const_ctx`].
    /// - `handle_repr_attr` is a callback that receives `item_attrs` and the index of the `#[repr]`
    ///   attribute if found.
    ///
    /// # Errors
    ///
    /// An error is returned
    ///
    /// 1. if `item_attrs` contains the `#[repr]` attribute and
    ///     - the argument cannot [be parsed] as a [`PseudoType`];
    ///     - the argument is a valid `PseudoType` but cannot [be converted] into a `RustType`; or
    ///     - the argument is a valid `RustType` but is narrower than `item_width`.
    /// 2. if `item_attrs` does not contain the `#[repr]` attribute and
    ///     - `item_width` depends on compile-time information; or
    ///     - `item_width`, when [rounded up] to the next power of two, cannot be converted into a
    ///       `RustType`.
    ///
    /// [be parsed]: PseudoType::parse
    /// [be converted]: PseudoType::try_into_rust_type
    /// [rounded up]: PseudoType::round_up
    pub(crate) fn repr_for_item(
        item_span: Span2,
        item_ident: &syn::Ident,
        item_width: &Width,
        item_attrs: &mut Vec<syn::Attribute>,
        const_ctx: &mut Vec<syn::Stmt>,
        handle_repr_attr: impl FnOnce(&mut Vec<syn::Attribute>, usize),
    ) -> Result<Self> {
        if let Some((i, attr)) =
            item_attrs.iter().enumerate().find(|(_, attr)| attr.path().is_ident("repr"))
        {
            let ident = attr.parse_args::<syn::Ident>().map_err(Error)?;
            let span = ident.span();
            let repr = match PseudoType::parse(&ident) {
                Some(Ok(ty)) => ty
                    .try_into_rust_type()
                    .ok_or_else(|| err!(span; "argument must be an existing Rust primitive")),
                Some(Err(e)) => Err(e),
                None => Err(err!(span; "argument must be an unsigned integer primitive")),
            }?;
            match item_width {
                Width::Met(_, item_width) => {
                    let item_width = *item_width;
                    if repr.width < item_width {
                        return Err(
                            err!(span; "type is too small to represent item of {item_width} bits"),
                        );
                    }
                }
                Width::Ct(item_width) => {
                    let error_msg = format!(
                        "type `{repr}` is too small to represent item `{item_ident}` of width {}",
                        parenthesize(item_width.clone()).into_token_stream(),
                    );
                    let error_msg = syn::ExprLit {
                        attrs: vec![],
                        lit: syn::LitStr::new(&error_msg, span).into(),
                    }
                    .into();
                    let repr_width = syn::ExprLit {
                        attrs: vec![],
                        lit: syn::LitInt::new(&repr.width.to_string(), span).into(),
                    }
                    .into();

                    let args: Punctuated<syn::Expr, syn::Token![,]> = Punctuated::from_iter([
                        item_width.clone(),
                        repr_width,
                        error_msg,
                    ]);
                    let mac = syn::Macro {
                        path: path!(span; assert_eq),
                        bang_token: syn::Token![!](span),
                        delimiter: syn::MacroDelimiter::Paren(syn::token::Paren(span)),
                        tokens: args.into_token_stream(),
                    };

                    const_ctx.push(syn::Stmt::Expr(
                        syn::ExprMacro { attrs: vec![], mac }.into(),
                        Some(syn::Token![;](span)),
                    ));
                }
            }
            handle_repr_attr(item_attrs, i);

            return Ok(repr);
        }

        let mut pseudo_type = match item_width {
            Width::Met(_, width) => PseudoType { width: *width },
            Width::Ct(_) => {
                return Err(err!(
                    item_span;
                    "not enough information to compute item width at macro evaluation time",
                ));
            }
        };
        pseudo_type.round_up();

        pseudo_type.try_into_rust_type().ok_or_else(
            || err!(item_span; "item cannot be represented by any unsigned integer primitive"),
        )
    }

    /// The bit-width of this type.
    ///
    /// This is guaranteed to be 8, 16, 32, 64, or 128.
    pub(crate) fn width(&self) -> usize {
        self.width
    }

    /// Converts this into a [`syn::Type`] with the given span.
    pub(crate) fn into_syn_type(self, span: Span2) -> syn::Type {
        ty_path!(syn::Ident::new(&self.to_string(), span))
    }
}

impl_display!(RustType);

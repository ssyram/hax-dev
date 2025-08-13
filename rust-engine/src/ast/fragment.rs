//! The `Fragment` type for holding arbitrary AST fragments.
//!
//! This enum is useful for diagnostics or dynamic dispatch on generic AST values.
//! It acts as a type-erased wrapper around various core AST node types.

use crate::ast::*;

/// Macro that derives automatically the `Fragment` and `FragmentRef` enumerations.
macro_rules! mk {
    ($($ty:ident),*) => {
        #[derive_group_for_ast]
        #[allow(missing_docs)]
        /// An owned fragment of AST in hax.
        pub enum Fragment {
            $(
                #[doc = concat!("An owned [`", stringify!($ty), "`] node.")]
                $ty($ty),
            )*
            /// Represent an unknown node in the AST with a message.
            Unknown(String),
        }
        #[derive(Copy)]
        #[derive_group_for_ast_base]
        #[derive(::serde::Serialize)]
        #[allow(missing_docs)]
        /// A borrowed fragment of AST in hax.
        pub enum FragmentRef<'lt> {
            $(
                #[doc = concat!("A borrowed [`", stringify!($ty), "`] node.")]
                $ty(&'lt $ty),
            )*
        }

        $(
            impl From<$ty> for Fragment {
                fn from(fragment: $ty) -> Self {
                    Self::$ty(fragment)
                }
            }
            impl<'lt> From<&'lt $ty> for FragmentRef<'lt> {
                fn from(fragment: &'lt $ty) -> Self {
                    Self::$ty(fragment)
                }
            }
        )*
    };
}

mk!(
    GlobalId,
    Expr,
    Pat,
    ExprKind,
    PatKind,
    Ty,
    TyKind,
    Metadata,
    Literal,
    LocalId,
    Lhs,
    Symbol,
    LoopKind,
    SafetyKind,
    Quote,
    SpannedTy,
    BindingMode,
    PrimitiveTy,
    Region,
    ImplExpr,
    IntKind,
    FloatKind,
    GenericValue,
    Arm,
    LoopState,
    ControlFlowKind,
    DynTraitGoal,
    Attribute,
    QuoteContent,
    BorrowKind,
    TraitGoal,
    ImplExprKind,
    IntSize,
    Signedness,
    Guard,
    AttributeKind,
    GuardKind,
    ImplItem,
    ImplItemKind,
    TraitItem,
    TraitItemKind,
    ItemQuoteOrigin,
    ItemQuoteOriginKind,
    ItemQuoteOriginPosition,
    GenericParamKind,
    ImplIdent,
    ProjectionPredicate,
    GenericParam,
    Generics,
    DocCommentKind,
    Param,
    Variant,
    ItemKind,
    Item,
    GenericConstraint,
    ErrorNode,
    Module,
    ResugaredExprKind,
    ResugaredTyKind,
    ResugaredPatKind,
    ResugaredImplItemKind,
    ResugaredTraitItemKind,
    ResugaredItemKind
);

//! This module provides the trait [`PrettyAst`] which is the main trait a printer should implement.
//! The module also provides a set of macros and helpers.

use std::fmt::Display;

use super::*;
use crate::ast::*;
use pretty::{DocAllocator, DocBuilder};

use crate::symbol::Symbol;
use identifiers::*;
use literals::*;
use resugared::*;

/// A newtype for any value that serde can serialize. When formatted, this
/// renders to a convenient `just` command line invocation to see the full
/// value, serialized as JSON.
pub struct DebugJSON<T: serde::Serialize>(T);

impl<T: serde::Serialize> Display for DebugJSON<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fn append_line_json(path: &str, value: &serde_json::Value) -> std::io::Result<usize> {
            use std::{
                fs::OpenOptions,
                io::{BufRead, BufReader, Write},
            };
            let file = OpenOptions::new()
                .read(true)
                .append(true)
                .create(true)
                .open(path)?;
            let count = BufReader::new(&file).lines().count();
            writeln!(&file, "{value}")?;
            Ok(count)
        }

        const PATH: &str = "/tmp/hax-ast-debug.json";
        let id = append_line_json(PATH, &serde_json::to_value(&self.0).unwrap()).unwrap();
        write!(f, "`just debug-json {id}`")
    }
}

impl<'a, 'b, A: 'a + Clone, P: PrettyAst<'a, 'b, A>, T: 'b + serde::Serialize> Pretty<'a, P, A>
    for DebugJSON<T>
{
    fn pretty(self, allocator: &'a P) -> DocBuilder<'a, P, A> {
        allocator.as_string(format!("{self}"))
    }
}

#[macro_export]
/// Similar to [`std::todo`], but returns a document instead of panicking with a message.
macro_rules! todo_document {
    ($allocator:ident,) => {
        {return $allocator.todo_document(&format!("TODO_LINE_{}", std::line!()));}
    };
    ($allocator:ident, $($tt:tt)*) => {
        {
            let message = format!($($tt)*);
            return $allocator.todo_document(&message);
        }
    };
}
pub use todo_document;

#[macro_export]
/// `install_pretty_helpers!(allocator: AllocatorType)` defines locally the helpers macros and functions using allocator `allocator`.
macro_rules! install_pretty_helpers {
    ($allocator:ident : $allocator_type:ty) => {
        /// `opt!(e)` is a shorthand for `e.as_ref().map(|e| docs![e])`
        #[allow(unused)]
        macro_rules! opt {
            ($e:expr) => {$e.as_ref().map(|e| <_ as pretty::Pretty<'_, $allocator_type, _>>::pretty(e, $allocator))};
        }

        /// `iter_pretty(e)` is a shorthand for `e.iter().map(|e| docs![e])`
        #[allow(unused)]
        macro_rules! iter_pretty {
            ($e:expr) => {$e.iter().map(|el| el.pretty($allocator))};
        }

        $crate::printer::pretty_ast::install_pretty_helpers!(
            @$allocator,
            #[doc = ::std::concat!("Proxy macro for [`", stringify!($crate), "::printer::pretty_ast::todo_document`] that automatically uses `", stringify!($allocator),"` as allocator.")]
            disambiguated_todo{$crate::printer::pretty_ast::todo_document!},
            #[doc = ::std::concat!("Proxy macro for [`pretty::docs`] that automatically uses `", stringify!($allocator),"` as allocator.")]
            docs{pretty::docs!},
            #[doc = ::std::concat!("Proxy macro for [`pretty::DocAllocator::nil`] that automatically uses `", stringify!($allocator),"` as allocator.")]
            nil{<$allocator_type as ::pretty::DocAllocator<'_, _>>::nil},
            #[doc = ::std::concat!("Proxy macro for [`pretty::DocAllocator::fail`] that automatically uses `", stringify!($allocator),"` as allocator.")]
            fail{<$allocator_type as ::pretty::DocAllocator<'_, _>>::fail},
            #[doc = ::std::concat!("Proxy macro for [`pretty::DocAllocator::hardline`] that automatically uses `", stringify!($allocator),"` as allocator.")]
            hardline{<$allocator_type as ::pretty::DocAllocator<'_, _>>::hardline},
            #[doc = ::std::concat!("Proxy macro for [`pretty::DocAllocator::space`] that automatically uses `", stringify!($allocator),"` as allocator.")]
            space{<$allocator_type as ::pretty::DocAllocator<'_, _>>::space},
            #[doc = ::std::concat!("Proxy macro for [`pretty::DocAllocator::line`] that automatically uses `", stringify!($allocator),"` as allocator.")]
            disambiguated_line{<$allocator_type as ::pretty::DocAllocator<'_, _>>::line},
            #[doc = ::std::concat!("Proxy macro for [`pretty::DocAllocator::line_`] that automatically uses `", stringify!($allocator),"` as allocator.")]
            line_{<$allocator_type as ::pretty::DocAllocator<'_, _>>::line_},
            #[doc = ::std::concat!("Proxy macro for [`pretty::DocAllocator::softline`] that automatically uses `", stringify!($allocator),"` as allocator.")]
            softline{<$allocator_type as ::pretty::DocAllocator<'_, _>>::softline},
            #[doc = ::std::concat!("Proxy macro for [`pretty::DocAllocator::softline_`] that automatically uses `", stringify!($allocator),"` as allocator.")]
            softline_{<$allocator_type as ::pretty::DocAllocator<'_, _>>::softline_},
            #[doc = ::std::concat!("Proxy macro for [`pretty::DocAllocator::as_string`] that automatically uses `", stringify!($allocator),"` as allocator.")]
            as_string{<$allocator_type as ::pretty::DocAllocator<'_, _>>::as_string},
            #[doc = ::std::concat!("Proxy macro for [`pretty::DocAllocator::text`] that automatically uses `", stringify!($allocator),"` as allocator.")]
            text{<$allocator_type as ::pretty::DocAllocator<'_, _>>::text},
            #[doc = ::std::concat!("Proxy macro for [`pretty::DocAllocator::concat`] that automatically uses `", stringify!($allocator),"` as allocator.")]
            disambiguated_concat{<$allocator_type as ::pretty::DocAllocator<'_, _>>::concat},
            #[doc = ::std::concat!("Proxy macro for [`pretty::DocAllocator::intersperse`] that automatically uses `", stringify!($allocator),"` as allocator.")]
            intersperse{<$allocator_type as ::pretty::DocAllocator<'_, _>>::intersperse},
            #[doc = ::std::concat!("Proxy macro for [`pretty::DocAllocator::column`] that automatically uses `", stringify!($allocator),"` as allocator.")]
            column{<$allocator_type as ::pretty::DocAllocator<'_, _>>::column},
            #[doc = ::std::concat!("Proxy macro for [`pretty::DocAllocator::nesting`] that automatically uses `", stringify!($allocator),"` as allocator.")]
            nesting{<$allocator_type as ::pretty::DocAllocator<'_, _>>::nesting},
            #[doc = ::std::concat!("Proxy macro for [`pretty::DocAllocator::reflow`] that automatically uses `", stringify!($allocator),"` as allocator.")]
            reflow{<$allocator_type as ::pretty::DocAllocator<'_, _>>::reflow}
        );
    };
    (@$allocator:ident, $($(#[$($attrs:tt)*])*$name:ident{$($callable:tt)*}),*) => {
        $(
            #[hax_rust_engine_macros::partial_apply($($callable)*, $allocator,)]
            #[allow(unused)]
            $(#[$($attrs)*])*
            macro_rules! $name {}
        )*
    };
}
pub use install_pretty_helpers;

macro_rules! mk {
    ($($ty:ident),*) => {
        pastey::paste! {
            /// A trait that defines a print method per type in the AST.
            /// This is the main trait a printer should implement.
            /// This trait takes care automatically of annotations (think source maps).
            pub trait PrettyAst<'a, 'b, A: 'a + Clone>: DocAllocator<'a, A> + Printer {
                /// Produces a todo document.
                fn todo_document(&'a self, message: &str) -> DocBuilder<'a, Self, A> {
                    self.as_string(message)
                }
                /// Produces an error document for an unimplemented document.
                fn unimplemented_method(&'a self, method: &str, ast: ast::fragment::FragmentRef<'_>) -> DocBuilder<'a, Self, A> {
                    self.text(format!("`{method}` unimpl, {}", DebugJSON(ast))).parens()
                }
                $(
                    #[doc = "Defines how a printer prints a given type."]
                    #[doc = "Don't call this method directly, instead use `Pretty::pretty`."]
                    #[doc = "Calling this method directly will cause issues related to spans or syntax highlighting."]
                    #[deprecated = concat!("Please use `Pretty::pretty` instead: the method `", stringify!([<$ty:snake>]), "` should never be called directly.")]
                    fn [<$ty:snake>](&'a self, [<$ty:snake>]: &'b $ty) -> DocBuilder<'a, Self, A> {
                        mk!(@method_body $ty [<$ty:snake>] self [<$ty:snake>])
                    }
                )*
            }

            $(
                impl<'a, 'b, A: 'a + Clone, P: PrettyAst<'a, 'b, A>> Pretty<'a, P, A> for &'b $ty {
                    fn pretty(self, allocator: &'a P) -> DocBuilder<'a, P, A> {
                        // Note about deprecation:
                        //   Here is the only place where calling the deprecated methods from the trait `PrettyAst` is fine.
                        //   Here is the place we (will) take care of spans, etc.
                        #[allow(deprecated)]
                        let print = <P as PrettyAst<'_, '_, _>>::[<$ty:snake>];
                        print(allocator, self)
                    }
                }
            )*
        }
    };
    // Special default implementation for specific types
    (@method_body Symbol $meth:ident $self:ident $value:ident) => {
        $self.text($value.to_string())
    };
    (@method_body LocalId $meth:ident $self:ident $value:ident) => {
        ::pretty::docs![$self, &$value.0]
    };
    (@method_body $ty:ident $meth:ident $self:ident $value:ident) => {
        $self.unimplemented_method(stringify!($meth), ast::fragment::FragmentRef::from($meth))
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

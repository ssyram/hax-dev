//! This modules provides types and helper for the printers of hax.

mod allocator;
use std::ops::Deref;

pub use allocator::Allocator;

use crate::ast;
use ast::visitors::dyn_compatible;
use pretty::Pretty;

pub mod pretty_ast;
pub use pretty_ast::PrettyAst;

/// A resugaring is an erased mapper visitor with a name.
/// A resugaring is a *local* transformation on the AST that produces exclusively `ast::resugared` nodes.
/// Any involved or non-local transformation should be a phase, not a resugaring.
pub trait Resugaring: for<'a> dyn_compatible::AstVisitorMut<'a> {
    /// Get the name of the resugar.
    fn name(&self) -> String;
}

/// A printer defines a list of resugaring phases.
pub trait Printer: Sized {
    /// A list of resugaring phases.
    fn resugaring_phases() -> Vec<Box<dyn Resugaring>>;
    /// The name of the printer
    const NAME: &str;
}

/// Implement `Printer` for `Allocator<P>` when `P` implements `Printer`.
/// This is just a convenience implementation proxying the underlying `Printer` implementation for `P`.
impl<P: Printer> Printer for Allocator<P> {
    fn resugaring_phases() -> Vec<Box<dyn Resugaring>> {
        P::resugaring_phases()
    }

    const NAME: &str = P::NAME;
}

/// Placeholder type for sourcemaps.
pub struct SourceMap;

/// Helper trait to print AST fragments.
pub trait Print<T>: Printer {
    /// Print a fragment using a backend.
    fn print(self, fragment: T) -> (String, SourceMap);
}

impl<P: Printer, T> Print<T> for P
where
    for<'a, 'b> &'b T: Pretty<'a, Allocator<Self>, ast::span::Span>,
    // The following node is equivalent to "T is an AST node"
    for<'a> dyn Resugaring: dyn_compatible::AstVisitableMut<'a, T>,
{
    fn print(self, mut fragment: T) -> (String, SourceMap) {
        for mut reguaring_phase in Self::resugaring_phases() {
            reguaring_phase.visit(&mut fragment)
        }
        let allocator = Allocator::new(self);
        let doc_builder: pretty::BoxDoc<'_, ast::span::Span> =
            fragment.pretty(&allocator).into_doc();
        (doc_builder.deref().pretty(80).to_string(), SourceMap)
    }
}

//! Copies of the types related to attributes.
//! Such types are mostly contained in the crate `rustc_attr_data_structures`.

use crate::prelude::*;

/// Reflects [`rustc_attr_data_structures::AttributeKind`]
#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_attr_data_structures::AttributeKind, state: S as tcx)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum AttributeKind {
    Align {
        align: Align,
        span: Span,
    },
    AutomaticallyDerived(Span),
    Coverage(Span, CoverageStatus),
    Deprecation {
        deprecation: Deprecation,
        span: Span,
    },
    DocComment {
        style: AttrStyle,
        kind: CommentKind,
        span: Span,
        comment: Symbol,
    },
    Ignore {
        span: Span,
        reason: Option<Symbol>,
    },
    Marker(Span),
    MayDangle(Span),
    MustUse {
        span: Span,
        reason: Option<Symbol>,
    },
    Path(Symbol, Span),
    #[todo]
    Todo(String),
}

/// Reflects [`rustc_attr_data_structures::Deprecation`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<'tcx, S>, from: rustc_attr_data_structures::Deprecation, state: S as _s)]
pub struct Deprecation {
    pub since: DeprecatedSince,
    pub note: Option<Symbol>,
    pub suggestion: Option<Symbol>,
}

/// Reflects [`rustc_attr_data_structures::DeprecatedSince`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<'tcx, S>, from: rustc_attr_data_structures::DeprecatedSince, state: S as _s)]
pub enum DeprecatedSince {
    RustcVersion(RustcVersion),
    Future,
    NonStandard(Symbol),
    Unspecified,
    Err,
}

/// Reflects [`rustc_attr_data_structures::RustcVersion`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<'tcx, S>, from: rustc_attr_data_structures::RustcVersion, state: S as _s)]
pub struct RustcVersion {
    pub major: u16,
    pub minor: u16,
    pub patch: u16,
}

/// Reflects [`rustc_attr_data_structures::CoverageStatus`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<'tcx, S>, from: rustc_attr_data_structures::CoverageStatus, state: S as _s)]
pub enum CoverageStatus {
    On,
    Off,
}

/// Reflects [`rustc_attr_data_structures::InlineAttr`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_attr_data_structures::InlineAttr, state: S as _s)]
pub enum InlineAttr {
    None,
    Hint,
    Always,
    Never,
    Force {
        attr_span: Span,
        reason: Option<Symbol>,
    },
}

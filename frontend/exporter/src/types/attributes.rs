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
    AllowConstFnUnstable(Vec<Symbol>, Span),
    AllowIncoherentImpl(Span),
    AllowInternalUnstable(Vec<(Symbol, Span)>, Span),
    AsPtr(Span),
    AutomaticallyDerived(Span),
    BodyStability {
        stability: DefaultBodyStability,
        span: Span,
    },
    CoherenceIsCore,
    Coinductive(Span),
    Cold(Span),
    Confusables {
        symbols: Vec<Symbol>,
        first_span: Span,
    },
    ConstContinue(Span),
    ConstStability {
        stability: PartialConstStability,
        span: Span,
    },
    ConstStabilityIndirect,
    ConstTrait(Span),
    Coverage(Span, CoverageStatus),
    DenyExplicitImpl(Span),
    Deprecation {
        deprecation: Deprecation,
        span: Span,
    },
    DoNotImplementViaObject(Span),
    DocComment {
        style: AttrStyle,
        kind: CommentKind,
        span: Span,
        comment: Symbol,
    },
    Dummy,
    ExportName {
        name: Symbol,
        span: Span,
    },
    ExportStable,
    FfiConst(Span),
    FfiPure(Span),
    Fundamental,
    Ignore {
        span: Span,
        reason: Option<Symbol>,
    },
    Inline(InlineAttr, Span),
    LinkName {
        name: Symbol,
        span: Span,
    },
    LinkOrdinal {
        ordinal: u16,
        span: Span,
    },
    LinkSection {
        name: Symbol,
        span: Span,
    },
    LoopMatch(Span),
    MacroTransparency(Transparency),
    Marker(Span),
    MayDangle(Span),
    MustUse {
        span: Span,
        reason: Option<Symbol>,
    },
    Naked(Span),
    NoImplicitPrelude(Span),
    NoMangle(Span),
    NonExhaustive(Span),
    OmitGdbPrettyPrinterSection,
    Optimize(OptimizeAttr, Span),
    ParenSugar(Span),
    PassByValue(Span),
    Path(Symbol, Span),
    Pointee(Span),
    PubTransparent(Span),
    Repr {
        reprs: Vec<(ReprAttr, Span)>,
        first_span: Span,
    },
    RustcLayoutScalarValidRangeEnd(u128, Span),
    RustcLayoutScalarValidRangeStart(u128, Span),
    RustcObjectLifetimeDefault,
    SkipDuringMethodDispatch {
        array: bool,
        boxed_slice: bool,
        span: Span,
    },
    SpecializationTrait(Span),
    Stability {
        stability: Stability,
        span: Span,
    },
    StdInternalSymbol(Span),
    TargetFeature(Vec<(Symbol, Span)>, Span),
    TrackCaller(Span),
    TypeConst(Span),
    UnsafeSpecializationMarker(Span),
    UnstableFeatureBound(Vec<(Symbol, Span)>),
    Used {
        used_by: UsedBy,
        span: Span,
    },
}

/// Reflects [`rustc_span::hygiene::Transparency`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<'tcx, S>, from: rustc_span::hygiene::Transparency, state: S as _s)]
pub enum Transparency {
    Transparent,
    SemiOpaque,
    Opaque,
}

/// Reflects [`rustc_attr_data_structures::Stability`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<'tcx, S>, from: rustc_attr_data_structures::Stability, state: S as _s)]
pub struct Stability {
    pub level: StabilityLevel,
    pub feature: Symbol,
}

/// Reflects [`rustc_attr_data_structures::DefaultBodyStability`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<'tcx, S>, from: rustc_attr_data_structures::DefaultBodyStability, state: S as _s)]
pub struct DefaultBodyStability {
    pub level: StabilityLevel,
    pub feature: Symbol,
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

/// Reflects [`rustc_attr_data_structures::ReprAttr`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<'tcx, S>, from: rustc_attr_data_structures::ReprAttr, state: S as _s)]
pub enum ReprAttr {
    ReprInt(IntType),
    ReprRust,
    ReprC,
    ReprPacked(Align),
    ReprSimd,
    ReprTransparent,
    ReprAlign(Align),
}

/// Reflects [`rustc_attr_data_structures::IntType`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<'tcx, S>, from: rustc_attr_data_structures::IntType, state: S as _s)]
pub enum IntType {
    SignedInt(IntTy),
    UnsignedInt(UintTy),
}

/// Reflects [`rustc_attr_data_structures::UsedBy`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<'tcx, S>, from: rustc_attr_data_structures::UsedBy, state: S as _s)]
pub enum UsedBy {
    Compiler,
    Linker,
}

/// Reflects [`rustc_attr_data_structures::StabilityLevel`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<'tcx, S>, from: rustc_attr_data_structures::StabilityLevel, state: S as _s)]
pub enum StabilityLevel {
    Unstable {
        reason: UnstableReason,
        #[map(x.map(|x| x.get()))]
        issue: Option<u32>,
        is_soft: bool,
        implied_by: Option<Symbol>,
        old_name: Option<Symbol>,
    },
    Stable {
        since: StableSince,
        allowed_through_unstable_modules: Option<Symbol>,
    },
}

/// Reflects [`rustc_attr_data_structures::CoverageStatus`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<'tcx, S>, from: rustc_attr_data_structures::CoverageStatus, state: S as _s)]
pub enum CoverageStatus {
    On,
    Off,
}

/// Reflects [`rustc_attr_data_structures::PartialConstStability`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<'tcx, S>, from: rustc_attr_data_structures::PartialConstStability, state: S as _s)]
pub struct PartialConstStability {
    pub level: StabilityLevel,
    pub feature: Symbol,
    pub promotable: bool,
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

/// Reflects [`rustc_attr_data_structures::StableSince`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<'tcx, S>, from: rustc_attr_data_structures::StableSince, state: S as _s)]
pub enum StableSince {
    Version(RustcVersion),
    Current,
    #[custom_arm(rustc_attr_data_structures::StableSince::Err(_) => StableSince::Err,)]
    Err,
}

/// Reflects [`rustc_attr_data_structures::UnstableReason`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<'tcx, S>, from: rustc_attr_data_structures::UnstableReason, state: S as _s)]
pub enum UnstableReason {
    None,
    Default,
    Some(Symbol),
}

/// Reflects [`rustc_attr_data_structures::OptimizeAttr`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<'tcx, S>, from: rustc_attr_data_structures::OptimizeAttr, state: S as _s)]
pub enum OptimizeAttr {
    Default,
    DoNotOptimize,
    Speed,
    Size,
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

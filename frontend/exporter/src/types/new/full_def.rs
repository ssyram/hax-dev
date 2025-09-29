use crate::prelude::*;

#[cfg(feature = "rustc")]
use rustc_hir::def::DefKind as RDefKind;
#[cfg(feature = "rustc")]
use rustc_middle::ty;
#[cfg(feature = "rustc")]
use rustc_span::def_id::DefId as RDefId;
#[cfg(feature = "rustc")]
use std::sync::Arc;

/// Hack: charon used to rely on the old `()` default everywhere. To avoid big merge conflicts with
/// in-flight PRs we're changing the default here. Eventually this should be removed.
type DefaultFullDefBody = MirBody<mir_kinds::Unknown>;

/// Gathers a lot of definition information about a [`rustc_hir::def_id::DefId`].
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub struct FullDef<Body = DefaultFullDefBody> {
    /// A reference to the current item. If the item was provided with generic args, they are
    /// stored here; otherwise the args are the identity_args for this item.
    pub this: ItemRef,
    /// The span of the definition of this item (e.g. for a function this is is signature).
    pub span: Span,
    /// The span of the whole definition (including e.g. the function body).
    pub source_span: Option<Span>,
    /// The text of the whole definition.
    pub source_text: Option<String>,
    /// Attributes on this definition, if applicable.
    pub attributes: Vec<Attribute>,
    /// Visibility of the definition, for definitions where this makes sense.
    pub visibility: Option<bool>,
    /// If this definition is a lang item, we store the identifier, e.g. `sized`.
    pub lang_item: Option<String>,
    /// If this definition is a diagnostic item, we store the identifier, e.g. `box_new`.
    pub diagnostic_item: Option<String>,
    pub kind: FullDefKind<Body>,
}

#[cfg(feature = "rustc")]
/// Construct the `FullDefKind` for this item. If `args` is `Some`, the returned `FullDef` will be
/// instantiated with the provided generics.
fn translate_full_def<'tcx, S, Body>(
    s: &S,
    def_id: &DefId,
    args: Option<ty::GenericArgsRef<'tcx>>,
) -> FullDef<Body>
where
    S: UnderOwnerState<'tcx>,
    Body: IsBody + TypeMappable,
{
    let tcx = s.base().tcx;
    let rust_def_id = def_id.underlying_rust_def_id();
    let source_span;
    let attributes;
    let visibility;
    let lang_item;
    let diagnostic_item;
    let kind;
    match def_id.promoted_id() {
        None => {
            kind = translate_full_def_kind(s, rust_def_id, args);

            let def_kind = get_def_kind(tcx, rust_def_id);
            source_span = rust_def_id.as_local().map(|ldid| tcx.source_span(ldid));
            attributes = get_def_attrs(tcx, rust_def_id, def_kind).sinto(s);
            visibility = get_def_visibility(tcx, rust_def_id, def_kind);
            lang_item = s
                .base()
                .tcx
                .as_lang_item(rust_def_id)
                .map(|litem| litem.name())
                .sinto(s);
            diagnostic_item = tcx.get_diagnostic_name(rust_def_id).sinto(s);
        }

        Some(promoted_id) => {
            let parent_def = def_id
                .parent
                .as_ref()
                .unwrap()
                .full_def_maybe_instantiated::<_, Body>(s, args);
            let parent_param_env = parent_def.param_env().unwrap();
            let param_env = ParamEnv {
                generics: TyGenerics {
                    parent: def_id.parent.clone(),
                    parent_count: parent_param_env.generics.count_total_params(),
                    params: vec![],
                    has_self: false,
                    has_late_bound_regions: None,
                },
                predicates: GenericPredicates { predicates: vec![] },
                parent: Some(parent_def.this().clone()),
            };
            let body = get_promoted_mir(tcx, rust_def_id, promoted_id.as_rust_promoted_id());
            let body = substitute(tcx, s.typing_env(), args, body);
            source_span = Some(body.span);

            let ty: Ty = body.local_decls[rustc_middle::mir::Local::ZERO].ty.sinto(s);
            kind = FullDefKind::Const {
                param_env,
                ty,
                kind: ConstKind::PromotedConst,
                body: Body::from_mir(s, body),
            };

            // None of these make sense for a promoted constant.
            attributes = Default::default();
            visibility = Default::default();
            lang_item = Default::default();
            diagnostic_item = Default::default();
        }
    }

    let source_text = source_span
        .filter(|source_span| source_span.ctxt().is_root())
        .and_then(|source_span| tcx.sess.source_map().span_to_snippet(source_span).ok());
    let this = if can_have_generics(tcx, rust_def_id) {
        let args_or_default =
            args.unwrap_or_else(|| ty::GenericArgs::identity_for_item(tcx, rust_def_id));
        let item = translate_item_ref(s, rust_def_id, args_or_default);
        // Tricky: hax's DefId has more info (could be a promoted const), we must be careful to use
        // the input DefId instead of the one derived from `rust_def_id`.
        item.with_def_id(s, def_id)
    } else {
        ItemRef::dummy_without_generics(s, def_id.clone())
    };
    FullDef {
        this,
        span: def_id.def_span(s),
        source_span: source_span.sinto(s),
        source_text,
        attributes,
        visibility,
        lang_item,
        diagnostic_item,
        kind,
    }
}

#[cfg(feature = "rustc")]
impl DefId {
    /// Get the span of the definition of this item. This is the span used in diagnostics when
    /// referring to the item.
    pub fn def_span<'tcx>(&self, s: &impl BaseState<'tcx>) -> Span {
        use DefKind::*;
        match &self.kind {
            // These kinds cause `def_span` to panic.
            ForeignMod => rustc_span::DUMMY_SP,
            _ => s.base().tcx.def_span(self.underlying_rust_def_id()),
        }
        .sinto(s)
    }

    /// Get the full definition of this item.
    pub fn full_def<'tcx, S, Body>(&self, s: &S) -> Arc<FullDef<Body>>
    where
        Body: IsBody + TypeMappable,
        S: BaseState<'tcx>,
    {
        self.full_def_maybe_instantiated(s, None)
    }

    /// Get the full definition of this item, instantiated if `args` is `Some`.
    pub fn full_def_maybe_instantiated<'tcx, S, Body>(
        &self,
        s: &S,
        args: Option<ty::GenericArgsRef<'tcx>>,
    ) -> Arc<FullDef<Body>>
    where
        Body: IsBody + TypeMappable,
        S: BaseState<'tcx>,
    {
        let rust_def_id = self.underlying_rust_def_id();
        let s = &s.with_owner_id(rust_def_id);
        let cache_key = (self.promoted_id(), args);
        if let Some(def) =
            s.with_cache(|cache| cache.full_defs.entry(cache_key).or_default().get().cloned())
        {
            return def;
        }
        let def = Arc::new(translate_full_def(s, self, args));
        s.with_cache(|cache| {
            cache
                .full_defs
                .entry(cache_key)
                .or_default()
                .insert(def.clone());
        });
        def
    }
}

#[cfg(feature = "rustc")]
impl ItemRef {
    /// Get the full definition of the item, instantiated with the provided generics.
    pub fn instantiated_full_def<'tcx, S, Body>(&self, s: &S) -> Arc<FullDef<Body>>
    where
        Body: IsBody + TypeMappable,
        S: BaseState<'tcx>,
    {
        let args = self.rustc_args(s);
        self.def_id.full_def_maybe_instantiated(s, Some(args))
    }
}

/// The combination of type generics and related predicates.
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub struct ParamEnv {
    /// Generic parameters of the item.
    pub generics: TyGenerics,
    /// Required predicates for the item (see `traits::utils::required_predicates`).
    pub predicates: GenericPredicates,
    /// A reference to the parent of this item, with appropriate args.
    pub parent: Option<ItemRef>,
}

/// The kind of a constant item.
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub enum ConstKind {
    /// Top-level constant: `const CONST: usize = 42;`
    TopLevel,
    /// Anonymous constant, e.g. the `1 + 2` in `[u8; 1 + 2]`
    AnonConst,
    /// An inline constant, e.g. `const { 1 + 2 }`
    InlineConst,
    /// A promoted constant, e.g. the `1 + 2` in `&(1 + 2)`
    PromotedConst,
}

/// Imbues [`rustc_hir::def::DefKind`] with a lot of extra information.
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub enum FullDefKind<Body> {
    // Types
    /// ADts (`Struct`, `Enum` and `Union` map to this variant).
    Adt {
        param_env: ParamEnv,
        adt_kind: AdtKind,
        variants: IndexVec<VariantIdx, VariantDef>,
        flags: AdtFlags,
        repr: ReprOptions,
        /// MIR body of the builtin `drop` impl.
        drop_glue: Option<Body>,
        /// Info required to construct a virtual `Drop` impl for this adt.
        drop_impl: Box<VirtualTraitImpl>,
    },
    /// Type alias: `type Foo = Bar;`
    TyAlias {
        param_env: ParamEnv,
        ty: Ty,
    },
    /// Type from an `extern` block.
    ForeignTy,
    /// Associated type: `trait MyTrait { type Assoc; }`
    AssocTy {
        param_env: ParamEnv,
        implied_predicates: GenericPredicates,
        associated_item: AssocItem,
        value: Option<Ty>,
    },
    /// Opaque type, aka `impl Trait`.
    OpaqueTy,

    // Traits
    Trait {
        param_env: ParamEnv,
        implied_predicates: GenericPredicates,
        /// The special `Self: Trait` clause.
        self_predicate: TraitPredicate,
        /// Associated items, in definition order.
        items: Vec<AssocItem>,
        /// `dyn Trait<Args.., Ty = <Self as Trait>::Ty..>` for this trait. This is `Some` iff this
        /// trait is dyn-compatible.
        dyn_self: Option<Ty>,
    },
    /// Trait alias: `trait IntIterator = Iterator<Item = i32>;`
    TraitAlias {
        param_env: ParamEnv,
        implied_predicates: GenericPredicates,
        /// The special `Self: Trait` clause.
        self_predicate: TraitPredicate,
        /// `dyn Trait<Args.., Ty = <Self as Trait>::Ty..>` for this trait. This is `Some` iff this
        /// trait is dyn-compatible.
        dyn_self: Option<Ty>,
    },
    TraitImpl {
        param_env: ParamEnv,
        /// The trait that is implemented by this impl block.
        trait_pred: TraitPredicate,
        /// `dyn Trait<Args.., Ty = <Self as Trait>::Ty..>` for the implemented trait. This is
        /// `Some` iff the trait is dyn-compatible.
        dyn_self: Option<Ty>,
        /// The `ImplExpr`s required to satisfy the predicates on the trait declaration. E.g.:
        /// ```ignore
        /// trait Foo: Bar {}
        /// impl Foo for () {} // would supply an `ImplExpr` for `Self: Bar`.
        /// ```
        implied_impl_exprs: Vec<ImplExpr>,
        /// Associated items, in the order of the trait declaration. Includes defaulted items.
        items: Vec<ImplAssocItem>,
    },
    InherentImpl {
        param_env: ParamEnv,
        /// The type to which this block applies.
        ty: Ty,
        /// Associated items, in definition order.
        items: Vec<AssocItem>,
    },

    // Functions
    Fn {
        param_env: ParamEnv,
        inline: InlineAttr,
        is_const: bool,
        sig: PolyFnSig,
        body: Option<Body>,
    },
    /// Associated function: `impl MyStruct { fn associated() {} }` or `trait Foo { fn associated()
    /// {} }`
    AssocFn {
        param_env: ParamEnv,
        associated_item: AssocItem,
        inline: InlineAttr,
        is_const: bool,
        /// The full vtable signature when this method is used in a vtable. `None` if this method is not
        /// vtable safe. `Some(sig)` if it is vtable safe, where `sig` is the signature from the trait
        /// declaration with `Self` substituted by `dyn_self` and associated types normalized.
        vtable_receiver: Option<PolyFnSig>,
        sig: PolyFnSig,
        body: Option<Body>,
    },
    /// A closure, coroutine, or coroutine-closure.
    ///
    /// Note: the (early-bound) generics of a closure are the same as those of the item in which it
    /// is defined.
    Closure {
        args: ClosureArgs,
        is_const: bool,
        /// Info required to construct a virtual `FnOnce` impl for this closure.
        fn_once_impl: Box<VirtualTraitImpl>,
        /// Info required to construct a virtual `FnMut` impl for this closure.
        fn_mut_impl: Option<Box<VirtualTraitImpl>>,
        /// Info required to construct a virtual `Fn` impl for this closure.
        fn_impl: Option<Box<VirtualTraitImpl>>,
        /// For `FnMut`&`Fn` closures: the MIR for the `call_once` method; it simply calls
        /// `call_mut`.
        once_shim: Option<Body>,
        /// MIR body of the builtin `drop` impl.
        drop_glue: Option<Body>,
        /// Info required to construct a virtual `Drop` impl for this closure.
        drop_impl: Box<VirtualTraitImpl>,
    },

    // Constants
    Const {
        param_env: ParamEnv,
        ty: Ty,
        kind: ConstKind,
        body: Option<Body>,
    },
    /// Associated constant: `trait MyTrait { const ASSOC: usize; }`
    AssocConst {
        param_env: ParamEnv,
        associated_item: AssocItem,
        ty: Ty,
        body: Option<Body>,
    },
    Static {
        param_env: ParamEnv,
        /// Whether it's a `unsafe static`, `safe static` (inside extern only) or just a `static`.
        safety: Safety,
        /// Whether it's a `static mut` or just a `static`.
        mutability: Mutability,
        /// Whether it's an anonymous static generated for nested allocations.
        nested: bool,
        ty: Ty,
        body: Option<Body>,
    },

    // Crates and modules
    ExternCrate,
    Use,
    Mod {
        items: Vec<(Option<Ident>, DefId)>,
    },
    /// An `extern` block.
    ForeignMod {
        items: Vec<DefId>,
    },

    // Type-level parameters
    /// Type parameter: the `T` in `struct Vec<T> { ... }`
    TyParam,
    /// Constant generic parameter: `struct Foo<const N: usize> { ... }`
    ConstParam,
    /// Lifetime parameter: the `'a` in `struct Foo<'a> { ... }`
    LifetimeParam,

    // ADT parts
    /// Refers to the variant definition, [`DefKind::Ctor`] refers to its constructor if it exists.
    Variant,
    /// The constructor function of a tuple/unit struct or tuple/unit enum variant.
    Ctor {
        adt_def_id: DefId,
        ctor_of: CtorOf,
        variant_id: VariantIdx,
        fields: IndexVec<FieldIdx, FieldDef>,
        output_ty: Ty,
    },
    /// A field in a struct, enum or union. e.g.
    /// - `bar` in `struct Foo { bar: u8 }`
    /// - `Foo::Bar::0` in `enum Foo { Bar(u8) }`
    Field,

    // Others
    /// Macros
    Macro(MacroKind),
    /// A use of `global_asm!`.
    GlobalAsm,
    /// A synthetic coroutine body created by the lowering of a coroutine-closure, such as an async
    /// closure.
    SyntheticCoroutineBody,
}

#[cfg(feature = "rustc")]
fn gen_vtable_receiver<'tcx>(
    // The state that owns the method DefId
    assoc_method_s: &StateWithOwner<'tcx>,
    args: Option<ty::GenericArgsRef<'tcx>>,
) -> Option<PolyFnSig>
{
    let def_id = assoc_method_s.owner_id();
    let tcx = assoc_method_s.base().tcx;
    let assoc_item = tcx.associated_item(def_id);
    let s = &assoc_method_s.with_owner_id(assoc_item.container_id(tcx));
    
    // The args for the container
    let container_args = {
        let container_def_id = assoc_item.container_id(tcx);
        let container_generics = tcx.generics_of(container_def_id);
        args.map(|args| {
            tcx.mk_args_from_iter(args.iter().take(container_generics.count()))
        })
    };

    let dyn_self: ty::Ty = match assoc_item.container {
        ty::AssocItemContainer::Trait => {
            get_trait_decl_dyn_self_ty(s, container_args)
        },
        ty::AssocItemContainer::Impl => {
            // For impl methods, compute concrete dyn_self from the impl's trait reference
            let impl_def_id = assoc_item.container_id(tcx);
            let Some(impl_trait_ref) = tcx.impl_trait_ref(impl_def_id) else {
                // There might be inherent impl methods, which is surely not vtable safe.
                return None;
            };
            // Get the concrete trait reference by rebasing the impl's trait ref args onto `container_args`
            let concrete_trait_ref = inst_binder(tcx, s.typing_env(), container_args, impl_trait_ref);
            dyn_self_ty(tcx, s.typing_env(), concrete_trait_ref)
        },
    }?;

    // Get the original trait method definition
    let origin_trait_method_id = match assoc_item.trait_item_def_id {
        Some(id) => id,
        // It is itself a trait method declaration
        None => def_id,
    };
    
    // Get the signature from the trait definition
    let origin_trait_method_sig = tcx.fn_sig(origin_trait_method_id);

    use ty::TypeFoldable;

    struct SelfReplacer<'tcx>(ty::TyCtxt<'tcx>, ty::Ty<'tcx>);

    impl<'tcx> ty::TypeFolder<ty::TyCtxt<'tcx>> for SelfReplacer<'tcx> {
        fn cx(&self) -> ty::TyCtxt<'tcx> {
            self.0
        }
        fn fold_ty(&mut self, t: ty::Ty<'tcx>) -> ty::Ty<'tcx> {
            use rustc_middle::ty::TypeSuperFoldable;
            match t.kind() {
                ty::Param(param) => {
                    if param.name == rustc_span::symbol::kw::SelfUpper {
                        assert!(param.index == 0);
                        return self.1.clone();
                    }
                    return t.super_fold_with(self);
                },
                _ => t.super_fold_with(self)
            }
        }
    }

    let mut replacer = SelfReplacer(tcx, dyn_self);

    // Get the instantiated signature and then substitute Self with dyn_self
    let trait_sig = inst_binder(tcx, s.typing_env(), container_args, origin_trait_method_sig);
    let vtable_sig = trait_sig.fold_with(&mut replacer);
    
    // Normalize associated types using constraints from dyn_self
    use crate::traits::normalize;
    let normalized_vtable_sig = normalize(tcx, s.typing_env(), vtable_sig);
    
    Some(normalized_vtable_sig.sinto(s))
}

#[cfg(feature = "rustc")]
/// Construct the `FullDefKind` for this item.
///
/// If `args` is `Some`, instantiate the whole definition with these generics; otherwise keep the
/// polymorphic definition.
// Note: this is tricky to get right, we have to make sure to isntantiate every single field that
// may contain a type/const/trait reference.
fn translate_full_def_kind<'tcx, S, Body>(
    s: &S,
    def_id: RDefId,
    args: Option<ty::GenericArgsRef<'tcx>>,
) -> FullDefKind<Body>
where
    S: BaseState<'tcx>,
    Body: IsBody + TypeMappable,
{
    let s = &s.with_owner_id(def_id);
    let tcx = s.base().tcx;
    let type_of_self = || inst_binder(tcx, s.typing_env(), args, tcx.type_of(def_id));
    let args_or_default =
        || args.unwrap_or_else(|| ty::GenericArgs::identity_for_item(tcx, def_id));
    match get_def_kind(tcx, def_id) {
        RDefKind::Struct { .. } | RDefKind::Union { .. } | RDefKind::Enum { .. } => {
            let def = tcx.adt_def(def_id);
            let variants = def
                .variants()
                .iter_enumerated()
                .map(|(variant_idx, variant)| {
                    let discr = if def.is_enum() {
                        def.discriminant_for_variant(tcx, variant_idx)
                    } else {
                        // Structs and unions have a single variant.
                        assert_eq!(variant_idx.index(), 0);
                        ty::util::Discr {
                            val: 0,
                            ty: tcx.types.isize,
                        }
                    };
                    VariantDef::sfrom(s, variant, discr, args)
                })
                .collect();

            let drop_trait = tcx.lang_items().drop_trait().unwrap();
            FullDefKind::Adt {
                param_env: get_param_env(s, args),
                adt_kind: def.adt_kind().sinto(s),
                variants,
                flags: def.flags().sinto(s),
                repr: def.repr().sinto(s),
                drop_glue: get_drop_glue_shim(s, args),
                drop_impl: virtual_impl_for(
                    s,
                    ty::TraitRef::new(tcx, drop_trait, [type_of_self()]),
                ),
            }
        }
        RDefKind::TyAlias { .. } => {
            let s = &s.with_base(Base {
                ty_alias_mode: true,
                ..s.base()
            });
            FullDefKind::TyAlias {
                param_env: get_param_env(s, args),
                ty: type_of_self().sinto(s),
            }
        }
        RDefKind::ForeignTy => FullDefKind::ForeignTy,
        RDefKind::AssocTy { .. } => FullDefKind::AssocTy {
            param_env: get_param_env(s, args),
            implied_predicates: get_implied_predicates(s, args),
            associated_item: AssocItem::sfrom_instantiated(s, &tcx.associated_item(def_id), args),
            value: if tcx.defaultness(def_id).has_value() {
                Some(type_of_self().sinto(s))
            } else {
                None
            },
        },
        RDefKind::OpaqueTy => FullDefKind::OpaqueTy,
        RDefKind::Trait { .. } => FullDefKind::Trait {
            param_env: get_param_env(s, args),
            implied_predicates: get_implied_predicates(s, args),
            self_predicate: get_self_predicate(s, args),
            dyn_self: get_trait_decl_dyn_self_ty(s, args).sinto(s),
            items: tcx
                .associated_items(def_id)
                .in_definition_order()
                .map(|assoc| {
                    let item_args = args.map(|args| {
                        let item_identity_args =
                            ty::GenericArgs::identity_for_item(tcx, assoc.def_id);
                        let item_args = item_identity_args.rebase_onto(tcx, def_id, args);
                        tcx.mk_args(item_args)
                    });
                    AssocItem::sfrom_instantiated(s, assoc, item_args)
                })
                .collect::<Vec<_>>(),
        },
        RDefKind::TraitAlias { .. } => FullDefKind::TraitAlias {
            param_env: get_param_env(s, args),
            implied_predicates: get_implied_predicates(s, args),
            self_predicate: get_self_predicate(s, args),
            dyn_self: get_trait_decl_dyn_self_ty(s, args).sinto(s),
        },
        RDefKind::Impl { .. } => {
            use std::collections::HashMap;
            let param_env = get_param_env(s, args);
            match inst_binder(tcx, s.typing_env(), args, tcx.impl_subject(def_id)) {
                ty::ImplSubject::Inherent(ty) => {
                    let items = tcx
                        .associated_items(def_id)
                        .in_definition_order()
                        .map(|assoc| {
                            let item_args = args.map(|args| {
                                let item_identity_args =
                                    ty::GenericArgs::identity_for_item(tcx, assoc.def_id);
                                let item_args = item_identity_args.rebase_onto(tcx, def_id, args);
                                tcx.mk_args(item_args)
                            });
                            AssocItem::sfrom_instantiated(s, assoc, item_args)
                        })
                        .collect::<Vec<_>>();
                    FullDefKind::InherentImpl {
                        param_env,
                        ty: ty.sinto(s),
                        items,
                    }
                }
                ty::ImplSubject::Trait(trait_ref) => {
                    let polarity = tcx.impl_polarity(def_id);
                    let trait_pred = TraitPredicate {
                        trait_ref: trait_ref.sinto(s),
                        is_positive: matches!(polarity, ty::ImplPolarity::Positive),
                    };
                    let dyn_self = dyn_self_ty(tcx, s.typing_env(), trait_ref).sinto(s);
                    // Impl exprs required by the trait.
                    let required_impl_exprs =
                        solve_item_implied_traits(s, trait_ref.def_id, trait_ref.args);

                    let mut item_map: HashMap<RDefId, _> = tcx
                        .associated_items(def_id)
                        .in_definition_order()
                        .map(|assoc| (assoc.trait_item_def_id.unwrap(), assoc))
                        .collect();
                    let items = tcx
                        .associated_items(trait_ref.def_id)
                        .in_definition_order()
                        .map(|decl_assoc| {
                            let decl_def_id = decl_assoc.def_id;
                            // Impl exprs required by the item.
                            let required_impl_exprs;
                            let value = match item_map.remove(&decl_def_id) {
                                Some(impl_assoc) => {
                                    required_impl_exprs = {
                                        let item_args = ty::GenericArgs::identity_for_item(
                                            tcx,
                                            impl_assoc.def_id,
                                        );
                                        // Subtlety: we have to add the GAT arguments (if any) to the trait ref arguments.
                                        let args =
                                            item_args.rebase_onto(tcx, def_id, trait_ref.args);
                                        let state_with_id = s.with_owner_id(impl_assoc.def_id);
                                        solve_item_implied_traits(&state_with_id, decl_def_id, args)
                                    };

                                    ImplAssocItemValue::Provided {
                                        def_id: impl_assoc.def_id.sinto(s),
                                        is_override: decl_assoc.defaultness(tcx).has_value(),
                                    }
                                }
                                None => {
                                    required_impl_exprs = if tcx
                                        .generics_of(decl_def_id)
                                        .is_own_empty()
                                    {
                                        // Non-GAT case.
                                        let item_args =
                                            ty::GenericArgs::identity_for_item(tcx, decl_def_id);
                                        let args =
                                            item_args.rebase_onto(tcx, def_id, trait_ref.args);
                                        // TODO: is it the right `def_id`?
                                        let state_with_id = s.with_owner_id(def_id);
                                        solve_item_implied_traits(&state_with_id, decl_def_id, args)
                                    } else {
                                        // FIXME: For GATs, we need a param_env that has the arguments of
                                        // the impl plus those of the associated type, but there's no
                                        // def_id with that param_env.
                                        vec![]
                                    };
                                    match decl_assoc.kind {
                                        ty::AssocKind::Type { .. } => {
                                            let ty = tcx
                                                .type_of(decl_def_id)
                                                .instantiate(tcx, trait_ref.args)
                                                .sinto(s);
                                            ImplAssocItemValue::DefaultedTy { ty }
                                        }
                                        ty::AssocKind::Fn { .. } => {
                                            let sig = if tcx.generics_of(decl_def_id).is_own_empty()
                                            {
                                                // The method doesn't have generics of its own, so
                                                // we can instantiate it with just the trait
                                                // generics.
                                                let sig = tcx
                                                    .fn_sig(decl_def_id)
                                                    .instantiate(tcx, trait_ref.args)
                                                    .sinto(s);
                                                Some(sig)
                                            } else {
                                                None
                                            };
                                            ImplAssocItemValue::DefaultedFn { sig }
                                        }
                                        ty::AssocKind::Const { .. } => {
                                            ImplAssocItemValue::DefaultedConst {}
                                        }
                                    }
                                }
                            };

                            ImplAssocItem {
                                name: decl_assoc.opt_name().sinto(s),
                                value,
                                required_impl_exprs,
                                decl_def_id: decl_def_id.sinto(s),
                            }
                        })
                        .collect();
                    assert!(item_map.is_empty());
                    FullDefKind::TraitImpl {
                        param_env,
                        trait_pred,
                        dyn_self,
                        implied_impl_exprs: required_impl_exprs,
                        items,
                    }
                }
            }
        }
        RDefKind::Fn { .. } => FullDefKind::Fn {
            param_env: get_param_env(s, args),
            inline: tcx.codegen_fn_attrs(def_id).inline.sinto(s),
            is_const: tcx.constness(def_id) == rustc_hir::Constness::Const,
            sig: inst_binder(tcx, s.typing_env(), args, tcx.fn_sig(def_id)).sinto(s),
            body: get_body(s, args),
        },
        RDefKind::AssocFn { .. } => {
            let item = tcx.associated_item(def_id);
            FullDefKind::AssocFn {
                param_env: get_param_env(s, args),
                associated_item: AssocItem::sfrom_instantiated(s, &item, args),
                inline: tcx.codegen_fn_attrs(def_id).inline.sinto(s),
                is_const: tcx.constness(def_id) == rustc_hir::Constness::Const,
                vtable_receiver: gen_vtable_receiver(s, args),
                sig: get_method_sig(tcx, s.typing_env(), def_id, args).sinto(s),
                body: get_body(s, args),
            }
        }
        RDefKind::Closure { .. } => {
            use ty::ClosureKind::{Fn, FnMut};
            let closure_ty = type_of_self();
            let ty::TyKind::Closure(_, closure_args) = closure_ty.kind() else {
                unreachable!()
            };
            let closure = closure_args.as_closure();
            // We lose lifetime information here. Eventually would be nice not to.
            let input_ty = erase_free_regions(tcx, closure.sig().input(0).skip_binder());
            let trait_args = [closure_ty, input_ty];
            let fn_once_trait = tcx.lang_items().fn_once_trait().unwrap();
            let fn_mut_trait = tcx.lang_items().fn_mut_trait().unwrap();
            let fn_trait = tcx.lang_items().fn_trait().unwrap();
            let drop_trait = tcx.lang_items().drop_trait().unwrap();
            FullDefKind::Closure {
                is_const: tcx.constness(def_id) == rustc_hir::Constness::Const,
                args: ClosureArgs::sfrom(s, def_id, closure),
                once_shim: get_closure_once_shim(s, closure_ty),
                drop_glue: get_drop_glue_shim(s, args),
                drop_impl: virtual_impl_for(
                    s,
                    ty::TraitRef::new(tcx, drop_trait, [type_of_self()]),
                ),
                fn_once_impl: virtual_impl_for(
                    s,
                    ty::TraitRef::new(tcx, fn_once_trait, trait_args),
                ),
                fn_mut_impl: matches!(closure.kind(), FnMut | Fn)
                    .then(|| virtual_impl_for(s, ty::TraitRef::new(tcx, fn_mut_trait, trait_args))),
                fn_impl: matches!(closure.kind(), Fn)
                    .then(|| virtual_impl_for(s, ty::TraitRef::new(tcx, fn_trait, trait_args))),
            }
        }
        kind @ (RDefKind::Const { .. }
        | RDefKind::AnonConst { .. }
        | RDefKind::InlineConst { .. }) => {
            let kind = match kind {
                RDefKind::Const { .. } => ConstKind::TopLevel,
                RDefKind::AnonConst { .. } => ConstKind::AnonConst,
                RDefKind::InlineConst { .. } => ConstKind::InlineConst,
                _ => unreachable!(),
            };
            FullDefKind::Const {
                param_env: get_param_env(s, args),
                ty: type_of_self().sinto(s),
                kind,
                body: get_body(s, args),
            }
        }
        RDefKind::AssocConst { .. } => FullDefKind::AssocConst {
            param_env: get_param_env(s, args),
            associated_item: AssocItem::sfrom_instantiated(s, &tcx.associated_item(def_id), args),
            ty: type_of_self().sinto(s),
            body: get_body(s, args),
        },
        RDefKind::Static {
            safety,
            mutability,
            nested,
            ..
        } => FullDefKind::Static {
            param_env: get_param_env(s, args),
            safety: safety.sinto(s),
            mutability: mutability.sinto(s),
            nested: nested.sinto(s),
            ty: type_of_self().sinto(s),
            body: get_body(s, args),
        },
        RDefKind::ExternCrate => FullDefKind::ExternCrate,
        RDefKind::Use => FullDefKind::Use,
        RDefKind::Mod { .. } => FullDefKind::Mod {
            items: get_mod_children(tcx, def_id).sinto(s),
        },
        RDefKind::ForeignMod { .. } => FullDefKind::ForeignMod {
            items: get_foreign_mod_children(tcx, def_id).sinto(s),
        },
        RDefKind::TyParam => FullDefKind::TyParam,
        RDefKind::ConstParam => FullDefKind::ConstParam,
        RDefKind::LifetimeParam => FullDefKind::LifetimeParam,
        RDefKind::Variant => FullDefKind::Variant,
        RDefKind::Ctor(ctor_of, _) => {
            let args = args_or_default();
            let ctor_of = ctor_of.sinto(s);

            // The def_id of the adt this ctor belongs to.
            let adt_def_id = match ctor_of {
                CtorOf::Struct => tcx.parent(def_id),
                CtorOf::Variant => tcx.parent(tcx.parent(def_id)),
            };
            let adt_def = tcx.adt_def(adt_def_id);
            let variant_id = adt_def.variant_index_with_ctor_id(def_id);
            let fields = adt_def
                .variant(variant_id)
                .fields
                .iter()
                .map(|f| FieldDef::sfrom(s, f, args))
                .collect();
            let output_ty = ty::Ty::new_adt(tcx, adt_def, args).sinto(s);
            FullDefKind::Ctor {
                adt_def_id: adt_def_id.sinto(s),
                ctor_of,
                variant_id: variant_id.sinto(s),
                fields,
                output_ty,
            }
        }
        RDefKind::Field => FullDefKind::Field,
        RDefKind::Macro(kind) => FullDefKind::Macro(kind.sinto(s)),
        RDefKind::GlobalAsm => FullDefKind::GlobalAsm,
        RDefKind::SyntheticCoroutineBody => FullDefKind::SyntheticCoroutineBody,
    }
}

/// An associated item in a trait impl. This can be an item provided by the trait impl, or an item
/// that reuses the trait decl default value.
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub struct ImplAssocItem {
    /// This is `None` for RPTITs.
    pub name: Option<Symbol>,
    /// The definition of the item from the trait declaration. This is an `AssocTy`, `AssocFn` or
    /// `AssocConst`.
    pub decl_def_id: DefId,
    /// The `ImplExpr`s required to satisfy the predicates on the associated type. E.g.:
    /// ```ignore
    /// trait Foo {
    ///     type Type<T>: Clone,
    /// }
    /// impl Foo for () {
    ///     type Type<T>: Arc<T>; // would supply an `ImplExpr` for `Arc<T>: Clone`.
    /// }
    /// ```
    /// Empty if this item is an associated const or fn.
    pub required_impl_exprs: Vec<ImplExpr>,
    /// The value of the implemented item.
    pub value: ImplAssocItemValue,
}

#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub enum ImplAssocItemValue {
    /// The item is provided by the trait impl.
    Provided {
        /// The definition of the item in the trait impl. This is an `AssocTy`, `AssocFn` or
        /// `AssocConst`.
        def_id: DefId,
        /// Whether the trait had a default value for this item (which is therefore overriden).
        is_override: bool,
    },
    /// This is an associated type that reuses the trait declaration default.
    DefaultedTy {
        /// The default type, with generics properly instantiated. Note that this can be a GAT;
        /// relevant generics and predicates can be found in `decl_def`.
        ty: Ty,
    },
    /// This is a non-overriden default method.
    /// FIXME: provide properly instantiated generics.
    DefaultedFn {
        /// The signature of the method, if we could translate it. `None` if the method as generics
        /// of its own, because then we'd need to resolve traits but the method doesn't have it's
        /// own `DefId`.
        sig: Option<PolyFnSig>,
    },
    /// This is an associated const that reuses the trait declaration default. The default const
    /// value can be found in `decl_def`.
    DefaultedConst,
}

/// Partial data for a trait impl, used for fake trait impls that we generate ourselves such as
/// `FnOnce` and `Drop` impls.
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub struct VirtualTraitImpl {
    /// The trait that is implemented by this impl block.
    pub trait_pred: TraitPredicate,
    /// The `ImplExpr`s required to satisfy the predicates on the trait declaration.
    pub implied_impl_exprs: Vec<ImplExpr>,
    /// The associated types and their predicates, in definition order.
    pub types: Vec<(Ty, Vec<ImplExpr>)>,
}

impl<Body> FullDef<Body> {
    pub fn def_id(&self) -> &DefId {
        &self.this.def_id
    }

    /// Reference to the item itself.
    pub fn this(&self) -> &ItemRef {
        &self.this
    }

    pub fn kind(&self) -> &FullDefKind<Body> {
        &self.kind
    }

    /// Returns the generics and predicates for definitions that have those.
    pub fn param_env(&self) -> Option<&ParamEnv> {
        use FullDefKind::*;
        match self.kind() {
            Adt { param_env, .. }
            | Trait { param_env, .. }
            | TraitAlias { param_env, .. }
            | TyAlias { param_env, .. }
            | AssocTy { param_env, .. }
            | Fn { param_env, .. }
            | AssocFn { param_env, .. }
            | Const { param_env, .. }
            | AssocConst { param_env, .. }
            | Static { param_env, .. }
            | TraitImpl { param_env, .. }
            | InherentImpl { param_env, .. } => Some(param_env),
            _ => None,
        }
    }

    /// Return the parent of this item if the item inherits the typing context from its parent.
    #[cfg(feature = "rustc")]
    pub fn typing_parent<'tcx>(&self, s: &impl BaseState<'tcx>) -> Option<ItemRef> {
        use FullDefKind::*;
        match self.kind() {
            AssocTy { .. }
            | AssocFn { .. }
            | AssocConst { .. }
            | Const {
                kind: ConstKind::AnonConst | ConstKind::InlineConst | ConstKind::PromotedConst,
                ..
            } => self.param_env().unwrap().parent.clone(),
            Closure { .. } | Ctor { .. } | Variant { .. } => {
                let parent = self.def_id().parent.as_ref().unwrap();
                // The parent has the same generics as this item.
                Some(self.this().with_def_id(s, parent))
            }
            _ => None,
        }
    }

    /// Whether the item has any generics at all (including parent generics).
    pub fn has_any_generics(&self) -> bool {
        match self.param_env() {
            Some(p) => p.generics.parent_count != 0 || !p.generics.params.is_empty(),
            None => false,
        }
    }

    /// Whether the item has any generics of its own (ignoring parent generics).
    pub fn has_own_generics(&self) -> bool {
        match self.param_env() {
            Some(p) => !p.generics.params.is_empty(),
            None => false,
        }
    }

    /// Lists the children of this item that can be named, in the way of normal rust paths. For
    /// types, this includes inherent items.
    #[cfg(feature = "rustc")]
    pub fn nameable_children<'tcx>(&self, s: &impl BaseState<'tcx>) -> Vec<(Symbol, DefId)> {
        let mut children = match self.kind() {
            FullDefKind::Mod { items } => items
                .iter()
                .filter_map(|(opt_ident, def_id)| {
                    Some((opt_ident.as_ref()?.0.clone(), def_id.clone()))
                })
                .collect(),
            FullDefKind::Adt {
                adt_kind: AdtKind::Enum,
                variants,
                ..
            } => variants
                .iter()
                .map(|variant| (variant.name.clone(), variant.def_id.clone()))
                .collect(),
            FullDefKind::InherentImpl { items, .. } | FullDefKind::Trait { items, .. } => items
                .iter()
                .filter_map(|item| Some((item.name.clone()?, item.def_id.clone())))
                .collect(),
            FullDefKind::TraitImpl { items, .. } => items
                .iter()
                .filter_map(|item| Some((item.name.clone()?, item.def_id().clone())))
                .collect(),
            _ => vec![],
        };
        // Add inherent impl items if any.
        if let Some(rust_def_id) = self.def_id().as_rust_def_id() {
            let tcx = s.base().tcx;
            for impl_def_id in tcx.inherent_impls(rust_def_id) {
                children.extend(
                    tcx.associated_items(impl_def_id)
                        .in_definition_order()
                        .filter_map(|assoc| Some((assoc.opt_name()?, assoc.def_id).sinto(s))),
                );
            }
        }
        children
    }
}

impl ImplAssocItem {
    /// The relevant definition: the provided implementation if any, otherwise the default
    /// declaration from the trait declaration.
    pub fn def_id(&self) -> &DefId {
        match &self.value {
            ImplAssocItemValue::Provided { def_id, .. } => def_id,
            _ => &self.decl_def_id,
        }
    }
}

#[cfg(feature = "rustc")]
fn get_self_predicate<'tcx, S: UnderOwnerState<'tcx>>(
    s: &S,
    args: Option<ty::GenericArgsRef<'tcx>>,
) -> TraitPredicate {
    use ty::Upcast;
    let tcx = s.base().tcx;
    let typing_env = s.typing_env();
    let pred: ty::TraitPredicate = crate::traits::self_predicate(tcx, s.owner_id())
        .no_bound_vars()
        .unwrap()
        .upcast(tcx);
    let pred = substitute(tcx, typing_env, args, pred);
    pred.sinto(s)
}

/// Generates a `dyn Trait<Args.., Ty = <Self as Trait>::Ty..>` type for this trait.
#[cfg(feature = "rustc")]
fn get_trait_decl_dyn_self_ty<'tcx, S: UnderOwnerState<'tcx>>(
    s: &S,
    args: Option<ty::GenericArgsRef<'tcx>>,
) -> Option<ty::Ty<'tcx>> {
    let tcx = s.base().tcx;
    let typing_env = s.typing_env();
    let def_id = s.owner_id();

    let self_tref = ty::TraitRef::new_from_args(
        tcx,
        def_id,
        args.unwrap_or_else(|| ty::GenericArgs::identity_for_item(tcx, def_id)),
    );
    rustc_utils::dyn_self_ty(tcx, typing_env, self_tref).map(|ty| {
        let ty = if args.is_some() {
            erase_free_regions(tcx, ty)
        } else {
            ty
        };
        ty
    })
}

/// Do the trait resolution necessary to create a new impl for the given trait_ref. Used when we
/// generate fake trait impls e.g. for `FnOnce` and `Drop`.
#[cfg(feature = "rustc")]
fn virtual_impl_for<'tcx, S>(s: &S, trait_ref: ty::TraitRef<'tcx>) -> Box<VirtualTraitImpl>
where
    S: UnderOwnerState<'tcx>,
{
    let tcx = s.base().tcx;
    let trait_pred = TraitPredicate {
        trait_ref: trait_ref.sinto(s),
        is_positive: true,
    };
    // Impl exprs required by the trait.
    let required_impl_exprs = solve_item_implied_traits(s, trait_ref.def_id, trait_ref.args);
    let types = tcx
        .associated_items(trait_ref.def_id)
        .in_definition_order()
        .filter(|assoc| matches!(assoc.kind, ty::AssocKind::Type { .. }))
        .map(|assoc| {
            // This assumes non-GAT because this is for builtin-trait (that don't
            // have GATs).
            let ty = ty::Ty::new_projection(tcx, assoc.def_id, trait_ref.args).sinto(s);
            // Impl exprs required by the type.
            let required_impl_exprs = solve_item_implied_traits(s, assoc.def_id, trait_ref.args);
            (ty, required_impl_exprs)
        })
        .collect();
    Box::new(VirtualTraitImpl {
        trait_pred,
        implied_impl_exprs: required_impl_exprs,
        types,
    })
}

#[cfg(feature = "rustc")]
fn get_body<'tcx, S, Body>(s: &S, args: Option<ty::GenericArgsRef<'tcx>>) -> Option<Body>
where
    S: UnderOwnerState<'tcx>,
    Body: IsBody + TypeMappable,
{
    let def_id = s.owner_id();
    Body::body(s, def_id, args)
}

#[cfg(feature = "rustc")]
fn get_closure_once_shim<'tcx, S, Body>(s: &S, closure_ty: ty::Ty<'tcx>) -> Option<Body>
where
    S: UnderOwnerState<'tcx>,
    Body: IsBody + TypeMappable,
{
    let tcx = s.base().tcx;
    let mir = crate::closure_once_shim(tcx, closure_ty)?;
    let body = Body::from_mir(s, mir)?;
    Some(body)
}

#[cfg(feature = "rustc")]
fn get_drop_glue_shim<'tcx, S, Body>(s: &S, args: Option<ty::GenericArgsRef<'tcx>>) -> Option<Body>
where
    S: UnderOwnerState<'tcx>,
    Body: IsBody + TypeMappable,
{
    let tcx = s.base().tcx;
    let mir = crate::drop_glue_shim(tcx, s.owner_id(), args)?;
    let body = Body::from_mir(s, mir)?;
    Some(body)
}

#[cfg(feature = "rustc")]
fn get_param_env<'tcx, S: UnderOwnerState<'tcx>>(
    s: &S,
    args: Option<ty::GenericArgsRef<'tcx>>,
) -> ParamEnv {
    let tcx = s.base().tcx;
    let def_id = s.owner_id();
    let generics = tcx.generics_of(def_id).sinto(s);

    let parent = generics.parent.as_ref().map(|parent| {
        let parent = parent.underlying_rust_def_id();
        let args = args.unwrap_or_else(|| ty::GenericArgs::identity_for_item(tcx, def_id));
        let parent_args = args.truncate_to(tcx, tcx.generics_of(parent));
        translate_item_ref(s, parent, parent_args)
    });
    match args {
        None => ParamEnv {
            generics,
            predicates: required_predicates(tcx, def_id, s.base().options.bounds_options).sinto(s),
            parent,
        },
        // An instantiated item is monomorphic.
        Some(_) => ParamEnv {
            generics: TyGenerics {
                parent_count: 0,
                params: Default::default(),
                ..generics
            },
            predicates: GenericPredicates::default(),
            parent,
        },
    }
}

#[cfg(feature = "rustc")]
fn get_implied_predicates<'tcx, S: UnderOwnerState<'tcx>>(
    s: &S,
    args: Option<ty::GenericArgsRef<'tcx>>,
) -> GenericPredicates {
    use std::borrow::Cow;
    let tcx = s.base().tcx;
    let def_id = s.owner_id();
    let typing_env = s.typing_env();
    let mut implied_predicates = implied_predicates(tcx, def_id, s.base().options.bounds_options);
    if args.is_some() {
        implied_predicates = Cow::Owned(
            implied_predicates
                .iter()
                .copied()
                .map(|(clause, span)| {
                    let clause = substitute(tcx, typing_env, args, clause);
                    (clause, span)
                })
                .collect(),
        );
    }
    implied_predicates.sinto(s)
}

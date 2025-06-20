use crate::prelude::*;
use std::sync::Arc;

#[cfg(feature = "rustc")]
use rustc_hir::def::DefKind as RDefKind;
#[cfg(feature = "rustc")]
use rustc_middle::{mir, ty};
#[cfg(feature = "rustc")]
use rustc_span::def_id::DefId as RDefId;

/// Hack: charon used to rely on the old `()` default everywhere. To avoid big merge conflicts with
/// in-flight PRs we're changing the default here. Eventually this should be removed.
type DefaultFullDefBody = MirBody<mir_kinds::Unknown>;

/// Gathers a lot of definition information about a [`rustc_hir::def_id::DefId`].
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub struct FullDef<Body = DefaultFullDefBody> {
    pub def_id: DefId,
    /// The enclosing item.
    pub parent: Option<DefId>,
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
fn translate_full_def<'tcx, S, Body>(s: &S, def_id: &DefId) -> FullDef<Body>
where
    S: BaseState<'tcx>,
    Body: IsBody + TypeMappable,
{
    let tcx = s.base().tcx;
    let rust_def_id = def_id.underlying_rust_def_id();
    let state_with_id = with_owner_id(s.base(), (), (), rust_def_id);
    let source_span;
    let attributes;
    let visibility;
    let lang_item;
    let diagnostic_item;
    let kind;
    match def_id.promoted_id() {
        None => {
            kind = translate_full_def_kind(s, rust_def_id);

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
            let parent_def = def_id.parent.as_ref().unwrap().full_def::<_, Body>(s);
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
            };
            let body = get_promoted_mir(tcx, rust_def_id, promoted_id.as_rust_promoted_id());
            source_span = Some(body.span);

            let ty: Ty = body.local_decls[rustc_middle::mir::Local::ZERO]
                .ty
                .sinto(&state_with_id);
            // Promoted constants only happen within MIR bodies; we can therefore assume that
            // `Body` is a MIR body and unwrap.
            let body = Body::from_mir(&state_with_id, body).s_unwrap(s);
            kind = FullDefKind::PromotedConst {
                param_env,
                ty,
                body,
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
    FullDef {
        def_id: def_id.clone(),
        parent: def_id.parent.clone(),
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
        let rust_def_id = self.underlying_rust_def_id();
        if let Some(def) = s.with_item_cache(rust_def_id, |cache| match self.promoted_id() {
            None => cache.full_def.get().cloned(),
            Some(promoted_id) => cache.promoteds.or_default().get(&promoted_id).cloned(),
        }) {
            return def;
        }
        let def = Arc::new(translate_full_def(s, self));
        s.with_item_cache(rust_def_id, |cache| match self.promoted_id() {
            None => {
                cache.full_def.insert(def.clone());
            }
            Some(promoted_id) => {
                cache
                    .promoteds
                    .or_default()
                    .insert(promoted_id, def.clone());
            }
        });
        def
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
}

/// Imbues [`rustc_hir::def::DefKind`] with a lot of extra information.
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub enum FullDefKind<Body> {
    // Types
    /// Refers to the struct definition, [`DefKind::Ctor`] refers to its constructor if it exists.
    Struct {
        param_env: ParamEnv,
        def: AdtDef,
        /// MIR body of the builtin `drop` impl.
        drop_glue: Option<Body>,
    },
    Union {
        param_env: ParamEnv,
        def: AdtDef,
        /// MIR body of the builtin `drop` impl.
        drop_glue: Option<Body>,
    },
    Enum {
        param_env: ParamEnv,
        def: AdtDef,
        /// MIR body of the builtin `drop` impl.
        drop_glue: Option<Body>,
    },
    /// Type alias: `type Foo = Bar;`
    TyAlias {
        param_env: ParamEnv,
        /// `Some` if the item is in the local crate.
        ty: Option<Ty>,
    },
    /// Type from an `extern` block.
    ForeignTy,
    /// Associated type: `trait MyTrait { type Assoc; }`
    AssocTy {
        parent: DefId,
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
        items: Vec<(AssocItem, Arc<FullDef<Body>>)>,
    },
    /// Trait alias: `trait IntIterator = Iterator<Item = i32>;`
    TraitAlias {
        param_env: ParamEnv,
        implied_predicates: GenericPredicates,
        /// The special `Self: Trait` clause.
        self_predicate: TraitPredicate,
    },
    TraitImpl {
        param_env: ParamEnv,
        /// The trait that is implemented by this impl block.
        trait_pred: TraitPredicate,
        /// The `ImplExpr`s required to satisfy the predicates on the trait declaration. E.g.:
        /// ```ignore
        /// trait Foo: Bar {}
        /// impl Foo for () {} // would supply an `ImplExpr` for `Self: Bar`.
        /// ```
        implied_impl_exprs: Vec<ImplExpr>,
        /// Associated items, in the order of the trait declaration. Includes defaulted items.
        items: Vec<ImplAssocItem<Body>>,
    },
    InherentImpl {
        param_env: ParamEnv,
        /// The type to which this block applies.
        ty: Ty,
        /// Associated items, in definition order.
        items: Vec<(AssocItem, Arc<FullDef<Body>>)>,
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
        parent: DefId,
        param_env: ParamEnv,
        associated_item: AssocItem,
        inline: InlineAttr,
        is_const: bool,
        sig: PolyFnSig,
        body: Option<Body>,
    },
    /// A closure, coroutine, or coroutine-closure.
    ///
    /// Note: the (early-bound) generics of a closure are the same as those of the item in which it
    /// is defined.
    Closure {
        /// The enclosing item. Note: this item could itself be a closure; to get the generics, you
        /// might have to recurse through several layers of parents until you find a function or
        /// constant.
        parent: DefId,
        is_const: bool,
        args: ClosureArgs,
        /// For `FnMut`&`Fn` closures: the MIR for the `call_once` method; it simply calls
        /// `call_mut`.
        once_shim: Option<Body>,
        /// MIR body of the builtin `drop` impl.
        drop_glue: Option<Body>,
    },

    // Constants
    Const {
        param_env: ParamEnv,
        ty: Ty,
        body: Option<Body>,
    },
    /// Associated constant: `trait MyTrait { const ASSOC: usize; }`
    AssocConst {
        parent: DefId,
        param_env: ParamEnv,
        associated_item: AssocItem,
        ty: Ty,
        body: Option<Body>,
    },
    /// Anonymous constant, e.g. the `1 + 2` in `[u8; 1 + 2]`
    AnonConst {
        param_env: ParamEnv,
        ty: Ty,
        body: Option<Body>,
    },
    /// An inline constant, e.g. `const { 1 + 2 }`
    InlineConst {
        param_env: ParamEnv,
        ty: Ty,
        body: Option<Body>,
    },
    /// A promoted constant, e.g. `&(1 + 2)`
    PromotedConst {
        param_env: ParamEnv,
        ty: Ty,
        body: Body,
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
fn translate_full_def_kind<'tcx, S, Body>(s: &S, def_id: RDefId) -> FullDefKind<Body>
where
    S: BaseState<'tcx>,
    Body: IsBody + TypeMappable,
{
    let s = &with_owner_id(s.base(), (), (), def_id);
    let tcx = s.base().tcx;
    match get_def_kind(tcx, def_id) {
        RDefKind::Struct { .. } => FullDefKind::Struct {
            param_env: get_param_env(s, def_id),
            def: tcx.adt_def(def_id).sinto(s),
            drop_glue: drop_glue_shim(tcx, def_id).and_then(|body| Body::from_mir(s, body)),
        },
        RDefKind::Union { .. } => FullDefKind::Union {
            param_env: get_param_env(s, def_id),
            def: tcx.adt_def(def_id).sinto(s),
            drop_glue: drop_glue_shim(tcx, def_id).and_then(|body| Body::from_mir(s, body)),
        },
        RDefKind::Enum { .. } => FullDefKind::Enum {
            param_env: get_param_env(s, def_id),
            def: tcx.adt_def(def_id).sinto(s),
            drop_glue: drop_glue_shim(tcx, def_id).and_then(|body| Body::from_mir(s, body)),
        },
        RDefKind::TyAlias { .. } => FullDefKind::TyAlias {
            param_env: get_param_env(s, def_id),
            ty: tcx.hir_get_if_local(def_id).map(|node| {
                let rustc_hir::Node::Item(item) = node else {
                    unreachable!()
                };
                let rustc_hir::ItemKind::TyAlias(_, _generics, ty) = &item.kind else {
                    unreachable!()
                };
                let mut s = State::from_under_owner(s);
                s.base.ty_alias_mode = true;
                ty.sinto(&s)
            }),
        },
        RDefKind::ForeignTy => FullDefKind::ForeignTy,
        RDefKind::AssocTy { .. } => FullDefKind::AssocTy {
            parent: tcx.parent(def_id).sinto(s),
            param_env: get_param_env(s, def_id),
            implied_predicates: implied_predicates(
                tcx,
                def_id,
                s.base().options.resolve_drop_bounds,
            )
            .sinto(s),
            associated_item: tcx.associated_item(def_id).sinto(s),
            value: if tcx.defaultness(def_id).has_value() {
                Some(tcx.type_of(def_id).instantiate_identity().sinto(s))
            } else {
                None
            },
        },
        RDefKind::OpaqueTy => FullDefKind::OpaqueTy,
        RDefKind::Trait { .. } => FullDefKind::Trait {
            param_env: get_param_env(s, def_id),
            implied_predicates: implied_predicates(
                tcx,
                def_id,
                s.base().options.resolve_drop_bounds,
            )
            .sinto(s),
            self_predicate: get_self_predicate(s),
            items: tcx
                .associated_items(def_id)
                .in_definition_order()
                .map(|assoc| {
                    let def_id = assoc.def_id.sinto(s);
                    (assoc.sinto(s), def_id.full_def(s))
                })
                .collect::<Vec<_>>(),
        },
        RDefKind::TraitAlias { .. } => FullDefKind::TraitAlias {
            param_env: get_param_env(s, def_id),
            implied_predicates: implied_predicates(
                tcx,
                def_id,
                s.base().options.resolve_drop_bounds,
            )
            .sinto(s),
            self_predicate: get_self_predicate(s),
        },
        RDefKind::Impl { .. } => {
            use std::collections::HashMap;
            let param_env = get_param_env(s, def_id);
            match tcx.impl_subject(def_id).instantiate_identity() {
                ty::ImplSubject::Inherent(ty) => {
                    let items = tcx
                        .associated_items(def_id)
                        .in_definition_order()
                        .map(|assoc| {
                            let def_id = assoc.def_id.sinto(s);
                            (assoc.sinto(s), def_id.full_def(s))
                        })
                        .collect::<Vec<_>>();
                    FullDefKind::InherentImpl {
                        param_env,
                        ty: ty.sinto(s),
                        items,
                    }
                }
                ty::ImplSubject::Trait(trait_ref) => {
                    // Also record the polarity.
                    let polarity = tcx.impl_polarity(def_id);
                    let trait_pred = TraitPredicate {
                        trait_ref: trait_ref.sinto(s),
                        is_positive: matches!(polarity, ty::ImplPolarity::Positive),
                    };
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
                            let decl_def = decl_def_id.sinto(s).full_def(s);
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
                                        let state_with_id =
                                            with_owner_id(s.base(), (), (), impl_assoc.def_id);
                                        solve_item_implied_traits(&state_with_id, decl_def_id, args)
                                    };

                                    ImplAssocItemValue::Provided {
                                        def: impl_assoc.def_id.sinto(s).full_def(s),
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
                                        let state_with_id = with_owner_id(s.base(), (), (), def_id);
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
                                            ImplAssocItemValue::DefaultedFn {}
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
                                decl_def,
                            }
                        })
                        .collect();
                    assert!(item_map.is_empty());
                    FullDefKind::TraitImpl {
                        param_env,
                        trait_pred,
                        implied_impl_exprs: required_impl_exprs,
                        items,
                    }
                }
            }
        }
        RDefKind::Fn { .. } => FullDefKind::Fn {
            param_env: get_param_env(s, def_id),
            inline: tcx.codegen_fn_attrs(def_id).inline.sinto(s),
            is_const: tcx.constness(def_id) == rustc_hir::Constness::Const,
            sig: tcx.fn_sig(def_id).instantiate_identity().sinto(s),
            body: Body::body(def_id, s),
        },
        RDefKind::AssocFn { .. } => FullDefKind::AssocFn {
            parent: tcx.parent(def_id).sinto(s),
            param_env: get_param_env(s, def_id),
            associated_item: tcx.associated_item(def_id).sinto(s),
            inline: tcx.codegen_fn_attrs(def_id).inline.sinto(s),
            is_const: tcx.constness(def_id) == rustc_hir::Constness::Const,
            sig: get_method_sig(s).sinto(s),
            body: Body::body(def_id, s),
        },
        RDefKind::Closure { .. } => {
            let closure_ty = tcx.type_of(def_id).instantiate_identity();
            let ty::TyKind::Closure(_, args) = closure_ty.kind() else {
                unreachable!()
            };
            FullDefKind::Closure {
                parent: tcx.parent(def_id).sinto(s),
                is_const: tcx.constness(def_id) == rustc_hir::Constness::Const,
                args: ClosureArgs::sfrom(s, def_id, args.as_closure()),
                once_shim: closure_once_shim(tcx, closure_ty)
                    .and_then(|body| Body::from_mir(s, body)),
                drop_glue: drop_glue_shim(tcx, def_id).and_then(|body| Body::from_mir(s, body)),
            }
        }
        RDefKind::Const { .. } => FullDefKind::Const {
            param_env: get_param_env(s, def_id),
            ty: tcx.type_of(def_id).instantiate_identity().sinto(s),
            body: Body::body(def_id, s),
        },
        RDefKind::AssocConst { .. } => FullDefKind::AssocConst {
            parent: tcx.parent(def_id).sinto(s),
            param_env: get_param_env(s, def_id),
            associated_item: tcx.associated_item(def_id).sinto(s),
            ty: tcx.type_of(def_id).instantiate_identity().sinto(s),
            body: Body::body(def_id, s),
        },
        RDefKind::AnonConst { .. } => FullDefKind::AnonConst {
            param_env: get_param_env(s, def_id),
            ty: tcx.type_of(def_id).instantiate_identity().sinto(s),
            body: Body::body(def_id, s),
        },
        RDefKind::InlineConst { .. } => FullDefKind::InlineConst {
            param_env: get_param_env(s, def_id),
            ty: tcx.type_of(def_id).instantiate_identity().sinto(s),
            body: Body::body(def_id, s),
        },
        RDefKind::Static {
            safety,
            mutability,
            nested,
            ..
        } => FullDefKind::Static {
            param_env: get_param_env(s, def_id),
            safety: safety.sinto(s),
            mutability: mutability.sinto(s),
            nested: nested.sinto(s),
            ty: tcx.type_of(def_id).instantiate_identity().sinto(s),
            body: Body::body(def_id, s),
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
        RDefKind::Ctor(ctor_of, _) => get_ctor_contents(s, ctor_of.sinto(s)),
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
pub struct ImplAssocItem<Body> {
    /// This is `None` for RPTITs.
    pub name: Option<Symbol>,
    /// The definition of the item from the trait declaration. This is `AssocTy`, `AssocFn` or
    /// `AssocConst`.
    pub decl_def: Arc<FullDef<Body>>,
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
    pub value: ImplAssocItemValue<Body>,
}

#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub enum ImplAssocItemValue<Body> {
    /// The item is provided by the trait impl.
    Provided {
        /// The definition of the item in the trait impl. This is `AssocTy`, `AssocFn` or
        /// `AssocConst`.
        def: Arc<FullDef<Body>>,
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
    DefaultedFn {},
    /// This is an associated const that reuses the trait declaration default. The default const
    /// value can be found in `decl_def`.
    DefaultedConst,
}

impl<Body> FullDef<Body> {
    pub fn def_id(&self) -> &DefId {
        &self.def_id
    }

    pub fn kind(&self) -> &FullDefKind<Body> {
        &self.kind
    }

    /// Returns the generics and predicates for definitions that have those.
    pub fn param_env(&self) -> Option<&ParamEnv> {
        use FullDefKind::*;
        match &self.kind {
            Struct { param_env, .. }
            | Union { param_env, .. }
            | Enum { param_env, .. }
            | Trait { param_env, .. }
            | TraitAlias { param_env, .. }
            | TyAlias { param_env, .. }
            | AssocTy { param_env, .. }
            | Fn { param_env, .. }
            | AssocFn { param_env, .. }
            | Const { param_env, .. }
            | AssocConst { param_env, .. }
            | AnonConst { param_env, .. }
            | InlineConst { param_env, .. }
            | Static { param_env, .. }
            | TraitImpl { param_env, .. }
            | InherentImpl { param_env, .. } => Some(param_env),
            _ => None,
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
            FullDefKind::Enum { def, .. } => def
                .variants
                .raw
                .iter()
                .map(|variant| (variant.name.clone(), variant.def_id.clone()))
                .collect(),
            FullDefKind::InherentImpl { items, .. } | FullDefKind::Trait { items, .. } => items
                .iter()
                .filter_map(|(item, _)| Some((item.name.clone()?, item.def_id.clone())))
                .collect(),
            FullDefKind::TraitImpl { items, .. } => items
                .iter()
                .filter_map(|item| Some((item.name.clone()?, item.def().def_id.clone())))
                .collect(),
            _ => vec![],
        };
        // Add inherent impl items if any.
        if let Some(rust_def_id) = self.def_id.as_rust_def_id() {
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

impl<Body> ImplAssocItem<Body> {
    /// The relevant definition: the provided implementation if any, otherwise the default
    /// declaration from the trait declaration.
    pub fn def(&self) -> &FullDef<Body> {
        match &self.value {
            ImplAssocItemValue::Provided { def, .. } => def.as_ref(),
            _ => self.decl_def.as_ref(),
        }
    }

    /// The kind of item this is.
    pub fn assoc_kind(&self) -> &AssocKind {
        match self.def().kind() {
            FullDefKind::AssocTy {
                associated_item, ..
            }
            | FullDefKind::AssocFn {
                associated_item, ..
            }
            | FullDefKind::AssocConst {
                associated_item, ..
            } => &associated_item.kind,
            _ => unreachable!(),
        }
    }
}

/// Gets the visibility (`pub` or not) of the definition. Returns `None` for defs that don't have a
/// meaningful visibility.
#[cfg(feature = "rustc")]
fn get_def_visibility<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    def_id: RDefId,
    def_kind: RDefKind,
) -> Option<bool> {
    use RDefKind::*;
    match def_kind {
        AssocConst
        | AssocFn
        | Const
        | Enum
        | Field
        | Fn
        | ForeignTy
        | Macro { .. }
        | Mod
        | Static { .. }
        | Struct
        | Trait
        | TraitAlias
        | TyAlias { .. }
        | Union
        | Use
        | Variant => Some(tcx.visibility(def_id).is_public()),
        // These kinds don't have visibility modifiers (which would cause `visibility` to panic).
        AnonConst
        | AssocTy
        | Closure
        | ConstParam
        | Ctor { .. }
        | ExternCrate
        | ForeignMod
        | GlobalAsm
        | Impl { .. }
        | InlineConst
        | LifetimeParam
        | OpaqueTy
        | SyntheticCoroutineBody
        | TyParam => None,
    }
}

/// Gets the attributes of the definition.
#[cfg(feature = "rustc")]
fn get_def_attrs<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    def_id: RDefId,
    def_kind: RDefKind,
) -> &'tcx [rustc_hir::Attribute] {
    use RDefKind::*;
    match def_kind {
        // These kinds cause `get_attrs_unchecked` to panic.
        ConstParam | LifetimeParam | TyParam | ForeignMod => &[],
        _ => tcx.get_attrs_unchecked(def_id),
    }
}

/// Gets the children of a module.
#[cfg(feature = "rustc")]
fn get_mod_children<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    def_id: RDefId,
) -> Vec<(Option<rustc_span::Ident>, RDefId)> {
    match def_id.as_local() {
        Some(ldid) => match tcx.hir_node_by_def_id(ldid) {
            rustc_hir::Node::Crate(m)
            | rustc_hir::Node::Item(&rustc_hir::Item {
                kind: rustc_hir::ItemKind::Mod(_, m),
                ..
            }) => m
                .item_ids
                .iter()
                .map(|&item_id| {
                    let opt_ident = tcx.hir_item(item_id).kind.ident();
                    let def_id = item_id.owner_id.to_def_id();
                    (opt_ident, def_id)
                })
                .collect(),
            node => panic!("DefKind::Module is an unexpected node: {node:?}"),
        },
        None => tcx
            .module_children(def_id)
            .iter()
            .map(|child| (Some(child.ident), child.res.def_id()))
            .collect(),
    }
}

/// Gets the children of an `extern` block. Empty if the block is not defined in the current crate.
#[cfg(feature = "rustc")]
fn get_foreign_mod_children<'tcx>(tcx: ty::TyCtxt<'tcx>, def_id: RDefId) -> Vec<RDefId> {
    match def_id.as_local() {
        Some(ldid) => tcx
            .hir_node_by_def_id(ldid)
            .expect_item()
            .expect_foreign_mod()
            .1
            .iter()
            .map(|foreign_item_ref| foreign_item_ref.id.owner_id.to_def_id())
            .collect(),
        None => vec![],
    }
}

#[cfg(feature = "rustc")]
fn get_self_predicate<'tcx, S: UnderOwnerState<'tcx>>(s: &S) -> TraitPredicate {
    use ty::Upcast;
    let tcx = s.base().tcx;
    let pred: ty::TraitPredicate = crate::traits::self_predicate(tcx, s.owner_id())
        .no_bound_vars()
        .unwrap()
        .upcast(tcx);
    pred.sinto(s)
}

/// The signature of a method impl may be a subtype of the one expected from the trait decl, as in
/// the example below. For correctness, we must be able to map from the method generics declared in
/// the trait to the actual method generics. Because this would require type inference, we instead
/// simply return the declared signature. This will cause issues if it is possible to use such a
/// more-specific implementation with its more-specific type, but we have a few other issues with
/// lifetime-generic function pointers anyway so this is unlikely to cause problems.
///
/// ```ignore
/// trait MyCompare<Other>: Sized {
///     fn compare(self, other: Other) -> bool;
/// }
/// impl<'a> MyCompare<&'a ()> for &'a () {
///     // This implementation is more general because it works for non-`'a` refs. Note that only
///     // late-bound vars may differ in this way.
///     // `<&'a () as MyCompare<&'a ()>>::compare` has type `fn<'b>(&'a (), &'b ()) -> bool`,
///     // but type `fn(&'a (), &'a ()) -> bool` was expected from the trait declaration.
///     fn compare<'b>(self, _other: &'b ()) -> bool {
///         true
///     }
/// }
/// ```
#[cfg(feature = "rustc")]
fn get_method_sig<'tcx, S>(s: &S) -> ty::PolyFnSig<'tcx>
where
    S: UnderOwnerState<'tcx>,
{
    let tcx = s.base().tcx;
    let def_id = s.owner_id();
    let real_sig = tcx.fn_sig(def_id).instantiate_identity();
    let item = tcx.associated_item(def_id);
    if !matches!(item.container, ty::AssocItemContainer::Impl) {
        return real_sig;
    }
    let Some(decl_method_id) = item.trait_item_def_id else {
        return real_sig;
    };
    let declared_sig = tcx.fn_sig(decl_method_id);

    // TODO(Nadrieril): Temporary hack: if the signatures have the same number of bound vars, we
    // keep the real signature. While the declared signature is more correct, it is also less
    // normalized and we can't normalize without erasing regions but regions are crucial in
    // function signatures. Hence we cheat here, until charon gains proper normalization
    // capabilities.
    if declared_sig.skip_binder().bound_vars().len() == real_sig.bound_vars().len() {
        return real_sig;
    }

    let impl_def_id = item.container_id(tcx);
    // The trait predicate that is implemented by the surrounding impl block.
    let implemented_trait_ref = tcx
        .impl_trait_ref(impl_def_id)
        .unwrap()
        .instantiate_identity();
    // Construct arguments for the declared method generics in the context of the implemented
    // method generics.
    let impl_args = ty::GenericArgs::identity_for_item(tcx, def_id);
    let decl_args = impl_args.rebase_onto(tcx, impl_def_id, implemented_trait_ref.args);
    let sig = declared_sig.instantiate(tcx, decl_args);
    // Avoids accidentally using the same lifetime name twice in the same scope
    // (once in impl parameters, second in the method declaration late-bound vars).
    let sig = tcx.anonymize_bound_vars(sig);
    sig
}

#[cfg(feature = "rustc")]
fn get_ctor_contents<'tcx, S, Body>(s: &S, ctor_of: CtorOf) -> FullDefKind<Body>
where
    S: UnderOwnerState<'tcx>,
    Body: IsBody + TypeMappable,
{
    let tcx = s.base().tcx;
    let def_id = s.owner_id();

    // The def_id of the adt this ctor belongs to.
    let adt_def_id = match ctor_of {
        CtorOf::Struct => tcx.parent(def_id),
        CtorOf::Variant => tcx.parent(tcx.parent(def_id)),
    };
    let adt_def = tcx.adt_def(adt_def_id);
    let variant_id = adt_def.variant_index_with_ctor_id(def_id);
    let fields = adt_def.variant(variant_id).fields.sinto(s);
    let generic_args = ty::GenericArgs::identity_for_item(tcx, adt_def_id);
    let output_ty = ty::Ty::new_adt(tcx, adt_def, generic_args).sinto(s);
    FullDefKind::Ctor {
        adt_def_id: adt_def_id.sinto(s),
        ctor_of,
        variant_id: variant_id.sinto(s),
        fields,
        output_ty,
    }
}

#[cfg(feature = "rustc")]
fn closure_once_shim<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    closure_ty: ty::Ty<'tcx>,
) -> Option<mir::Body<'tcx>> {
    let ty::Closure(def_id, args) = closure_ty.kind() else {
        unreachable!()
    };
    let instance = match args.as_closure().kind() {
        ty::ClosureKind::Fn | ty::ClosureKind::FnMut => {
            ty::Instance::fn_once_adapter_instance(tcx, *def_id, args)
        }
        ty::ClosureKind::FnOnce => return None,
    };
    let mir = tcx.instance_mir(instance.def).clone();
    let mir = ty::EarlyBinder::bind(mir).instantiate(tcx, instance.args);
    Some(mir)
}

#[cfg(feature = "rustc")]
fn drop_glue_shim<'tcx>(tcx: ty::TyCtxt<'tcx>, def_id: RDefId) -> Option<mir::Body<'tcx>> {
    let drop_in_place =
        tcx.require_lang_item(rustc_hir::LangItem::DropInPlace, rustc_span::DUMMY_SP);
    if !tcx.generics_of(def_id).is_empty() {
        // Hack: layout code panics if it can't fully normalize types, which can happen e.g. with a
        // trait associated type. For now we only translate the glue for monomorphic types.
        return None;
    }
    let ty = tcx.type_of(def_id).instantiate_identity();
    let instance_kind = ty::InstanceKind::DropGlue(drop_in_place, Some(ty));
    let mir = tcx.instance_mir(instance_kind).clone();
    Some(mir)
}

#[cfg(feature = "rustc")]
fn get_param_env<'tcx, S: BaseState<'tcx>>(s: &S, def_id: RDefId) -> ParamEnv {
    let tcx = s.base().tcx;
    let s = &with_owner_id(s.base(), (), (), def_id);
    ParamEnv {
        generics: tcx.generics_of(def_id).sinto(s),
        predicates: required_predicates(tcx, def_id, s.base().options.resolve_drop_bounds).sinto(s),
    }
}

use crate::prelude::*;

#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum ConstantInt {
    Int(
        #[serde(with = "serialize_int::signed")]
        #[schemars(with = "String")]
        i128,
        IntTy,
    ),
    Uint(
        #[serde(with = "serialize_int::unsigned")]
        #[schemars(with = "String")]
        u128,
        UintTy,
    ),
}

#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum ConstantLiteral {
    Bool(bool),
    Char(char),
    Float(String, FloatTy),
    Int(ConstantInt),
    Str(String),
    ByteStr(Vec<u8>),
}

/// The subset of [Expr] that corresponds to constants.
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum ConstantExprKind {
    Literal(ConstantLiteral),
    Adt {
        info: VariantInformations,
        fields: Vec<ConstantFieldExpr>,
    },
    Array {
        fields: Vec<ConstantExpr>,
    },
    Tuple {
        fields: Vec<ConstantExpr>,
    },
    /// A top-level constant or a constant appearing in an impl block.
    ///
    /// Remark: constants *can* have generic parameters.
    /// Example:
    /// ```text
    /// struct V<const N: usize, T> {
    ///   x: [T; N],
    /// }
    ///
    /// impl<const N: usize, T> V<N, T> {
    ///   const LEN: usize = N; // This has generics <N, T>
    /// }
    /// ```
    GlobalName {
        id: GlobalIdent,
        generics: Vec<GenericArg>,
        trait_refs: Vec<ImplExpr>,
    },
    /// A trait constant
    ///
    /// Ex.:
    /// ```text
    /// impl Foo for Bar {
    ///   const C : usize = 32; // <-
    /// }
    /// ```
    TraitConst {
        impl_expr: ImplExpr,
        name: String,
    },
    /// A shared reference to a static variable.
    Borrow(ConstantExpr),
    /// A raw borrow (`*const` or `*mut`).
    RawBorrow {
        mutability: Mutability,
        arg: ConstantExpr,
    },
    /// A cast `<source> as <type>`, `<type>` is stored as the type of
    /// the current constant expression. Currently, this is only used
    /// to represent `lit as *mut T` or `lit as *const T`, where `lit`
    /// is a `usize` literal.
    Cast {
        source: ConstantExpr,
    },
    ConstRef {
        id: ParamConst,
    },
    FnPtr {
        def_id: DefId,
        generics: Vec<GenericArg>,
        /// The implementation expressions for every generic bounds
        /// ```text
        /// fn foo<T : Bar>(...)
        ///            ^^^
        /// ```
        generics_impls: Vec<ImplExpr>,
        /// If the function is a method of trait `Foo`, `method_impl`
        /// is an implementation of `Foo`
        method_impl: Option<ImplExpr>,
    },
    /// A blob of memory containing the byte representation of the value. This can occur when
    /// evaluating MIR constants. Interpreting this back to a structured value is left as an
    /// exercice to the consumer.
    Memory(Vec<u8>),
    Todo(String),
}

#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct ConstantFieldExpr {
    pub field: DefId,
    pub value: ConstantExpr,
}

/// Rustc has different representation for constants: one for MIR
/// ([`rustc_middle::mir::Const`]), one for the type system
/// ([`rustc_middle::ty::ConstKind`]). For simplicity hax maps those
/// two construct to one same `ConstantExpr` type.
pub type ConstantExpr = Decorated<ConstantExprKind>;

// For ConstantKind we merge all the cases (Ty, Val, Unevaluated) into one
pub type ConstantKind = ConstantExpr;

#[cfg(feature = "rustc")]
pub use self::rustc::*;
#[cfg(feature = "rustc")]
mod rustc {
    use super::*;
    use rustc_const_eval::interpret::{interp_ok, InterpResult};
    use rustc_middle::mir::interpret;
    use rustc_middle::{mir, ty};

    impl From<ConstantFieldExpr> for FieldExpr {
        fn from(c: ConstantFieldExpr) -> FieldExpr {
            FieldExpr {
                value: c.value.into(),
                field: c.field,
            }
        }
    }

    impl ConstantLiteral {
        /// Rustc always represents string constants as `&[u8]`, but this
        /// is not nice to consume. This associated function interpret
        /// bytes as an unicode string, and as a byte string otherwise.
        fn byte_str(bytes: Vec<u8>) -> Self {
            match String::from_utf8(bytes.clone()) {
                Ok(s) => Self::Str(s),
                Err(_) => Self::ByteStr(bytes),
            }
        }
    }

    impl From<ConstantExpr> for Expr {
        fn from(c: ConstantExpr) -> Expr {
            use ConstantExprKind::*;
            let kind = match *c.contents {
                Literal(lit) => {
                    use ConstantLiteral::*;
                    let mut neg = false;
                    let node = match lit {
                        Bool(b) => LitKind::Bool(b),
                        Char(c) => LitKind::Char(c),
                        Int(i) => {
                            use LitIntType::*;
                            match i {
                                ConstantInt::Uint(v, t) => LitKind::Int(v, Unsigned(t)),
                                ConstantInt::Int(v, t) => {
                                    neg = v.is_negative();
                                    LitKind::Int(v.abs_diff(0), Signed(t))
                                }
                            }
                        }
                        Float(f, ty) => LitKind::Float(f, LitFloatType::Suffixed(ty)),
                        ByteStr(raw) => LitKind::ByteStr(raw, StrStyle::Cooked),
                        Str(raw) => LitKind::Str(raw, StrStyle::Cooked),
                    };
                    let span = c.span.clone();
                    let lit = Spanned { span, node };
                    ExprKind::Literal { lit, neg }
                }
                Adt { info, fields } => ExprKind::Adt(AdtExpr {
                    info,
                    fields: fields.into_iter().map(|field| field.into()).collect(),
                    base: None,
                    user_ty: None,
                }),
                // TODO: propagate the generics and trait refs (see #636)
                GlobalName {
                    id,
                    generics: _,
                    trait_refs: _,
                } => ExprKind::GlobalName {
                    id,
                    constructor: None,
                },
                Borrow(e) => ExprKind::Borrow {
                    borrow_kind: BorrowKind::Shared,
                    arg: e.into(),
                },
                RawBorrow { mutability, arg } => ExprKind::RawBorrow {
                    mutability,
                    arg: arg.into(),
                },
                ConstRef { id } => ExprKind::ConstRef { id },
                Array { fields } => ExprKind::Array {
                    fields: fields.into_iter().map(|field| field.into()).collect(),
                },
                Tuple { fields } => ExprKind::Tuple {
                    fields: fields.into_iter().map(|field| field.into()).collect(),
                },
                Cast { source } => ExprKind::Cast {
                    source: source.into(),
                },
                kind @ (FnPtr { .. } | TraitConst { .. } | Memory { .. }) => {
                    // SH: I see the `Closure` kind, but it's not the same as function pointer?
                    ExprKind::Todo(format!("FnPtr or TraitConst or Memory. kind={:#?}", kind))
                }
                Todo(msg) => ExprKind::Todo(msg),
            };
            Decorated {
                contents: Box::new(kind),
                ..c
            }
        }
    }

    #[tracing::instrument(level = "trace", skip(s))]
    pub(crate) fn scalar_int_to_constant_literal<'tcx, S: UnderOwnerState<'tcx>>(
        s: &S,
        x: rustc_middle::ty::ScalarInt,
        ty: rustc_middle::ty::Ty<'tcx>,
    ) -> ConstantLiteral {
        match ty.kind() {
            ty::Char => ConstantLiteral::Char(
                char::try_from(x).s_expect(s, "scalar_int_to_constant_literal: expected a char"),
            ),
            ty::Bool => ConstantLiteral::Bool(
                x.try_to_bool()
                    .s_expect(s, "scalar_int_to_constant_literal: expected a bool"),
            ),
            ty::Int(kind) => {
                let v = x.to_int(x.size());
                ConstantLiteral::Int(ConstantInt::Int(v, kind.sinto(s)))
            }
            ty::Uint(kind) => {
                let v = x.to_uint(x.size());
                ConstantLiteral::Int(ConstantInt::Uint(v, kind.sinto(s)))
            }
            ty::Float(kind) => {
                let v = x.to_bits_unchecked();
                bits_and_type_to_float_constant_literal(v, kind.sinto(s))
            }
            _ => {
                let ty_sinto: Ty = ty.sinto(s);
                supposely_unreachable_fatal!(
                    s,
                    "scalar_int_to_constant_literal_ExpectedLiteralType";
                    { ty, ty_sinto, x }
                )
            }
        }
    }

    /// Converts a bit-representation of a float of type `ty` to a constant literal
    fn bits_and_type_to_float_constant_literal(bits: u128, ty: FloatTy) -> ConstantLiteral {
        use rustc_apfloat::{ieee, Float};
        let string = match &ty {
            FloatTy::F16 => ieee::Half::from_bits(bits).to_string(),
            FloatTy::F32 => ieee::Single::from_bits(bits).to_string(),
            FloatTy::F64 => ieee::Double::from_bits(bits).to_string(),
            FloatTy::F128 => ieee::Quad::from_bits(bits).to_string(),
        };
        ConstantLiteral::Float(string, ty)
    }

    /// Whether a `DefId` is a `AnonConst`. An anonymous constant is
    /// generated by Rustc, hoisting every constat bits from items as
    /// separate top-level items. This AnonConst mechanism is internal to
    /// Rustc; we don't want to reflect that, instead we prefer inlining
    /// those. `is_anon_const` is used to detect such AnonConst so that we
    /// can evaluate and inline them.
    pub(crate) fn is_anon_const(
        did: rustc_span::def_id::DefId,
        tcx: rustc_middle::ty::TyCtxt<'_>,
    ) -> bool {
        matches!(
            tcx.def_path(did).data.last().map(|x| x.data),
            Some(rustc_hir::definitions::DefPathData::AnonConst)
        )
    }

    #[tracing::instrument(level = "trace", skip(s))]
    fn trait_const_to_constant_expr_kind<'tcx, S: BaseState<'tcx> + HasOwnerId>(
        s: &S,
        _const_def_id: rustc_hir::def_id::DefId,
        generics: rustc_middle::ty::GenericArgsRef<'tcx>,
        assoc: &rustc_middle::ty::AssocItem,
    ) -> ConstantExprKind {
        assert!(assoc.trait_item_def_id.is_some());
        let name = assoc.name.to_string();

        // Retrieve the trait information
        let impl_expr = self_clause_for_item(s, assoc, generics).unwrap();

        ConstantExprKind::TraitConst { impl_expr, name }
    }

    impl ConstantExprKind {
        pub fn decorate(self, ty: Ty, span: Span) -> Decorated<Self> {
            Decorated {
                contents: Box::new(self),
                hir_id: None,
                attributes: vec![],
                ty,
                span,
            }
        }
    }

    pub enum TranslateUnevalRes<T> {
        // TODO: rename
        GlobalName(ConstantExpr),
        EvaluatedConstant(T),
    }

    pub trait ConstantExt<'tcx>: Sized + std::fmt::Debug {
        fn eval_constant<S: UnderOwnerState<'tcx>>(&self, s: &S) -> Option<Self>;

        /// Performs a one-step translation of a constant.
        ///  - When a constant refers to a named top-level constant, we want to use that, thus we translate the constant to a `ConstantExprKind::GlobalName`. This is captured by the variant `TranslateUnevalRes::GlobalName`.
        ///  - When a constant refers to a anonymous top-level constant, we evaluate it. If the evaluation fails, we report an error: we expect every AnonConst to be reducible. Otherwise, we return the variant `TranslateUnevalRes::EvaluatedConstant`.
        fn translate_uneval(
            &self,
            s: &impl UnderOwnerState<'tcx>,
            ucv: rustc_middle::ty::UnevaluatedConst<'tcx>,
            span: rustc_span::Span,
        ) -> TranslateUnevalRes<Self> {
            let tcx = s.base().tcx;
            if is_anon_const(ucv.def, tcx) {
                TranslateUnevalRes::EvaluatedConstant(self.eval_constant(s).unwrap_or_else(|| {
                    // TODO: This is triggered when compiling using `generic_const_exprs`
                    supposely_unreachable_fatal!(s, "TranslateUneval"; {self, ucv});
                }))
            } else {
                let param_env = s.param_env();
                let ty = s.base().tcx.type_of(ucv.def).instantiate(tcx, ucv.args);
                let ty = tcx
                    .try_normalize_erasing_regions(param_env, ty)
                    .unwrap_or(ty);
                let kind = if let Some(assoc) = s.base().tcx.opt_associated_item(ucv.def) {
                    if assoc.trait_item_def_id.is_some() {
                        // This must be a trait declaration constant
                        trait_const_to_constant_expr_kind(s, ucv.def, ucv.args, &assoc)
                    } else {
                        // Constant appearing in an inherent impl block.

                        // Solve the trait obligations
                        let parent_def_id = tcx.parent(ucv.def);
                        let trait_refs = solve_item_required_traits(s, parent_def_id, ucv.args);

                        // Convert
                        let id = ucv.def.sinto(s);
                        let generics = ucv.args.sinto(s);
                        ConstantExprKind::GlobalName {
                            id,
                            generics,
                            trait_refs,
                        }
                    }
                } else {
                    // Top-level constant.
                    assert!(ucv.args.is_empty(), "top-level constant has generics?");
                    let id = ucv.def.sinto(s);
                    ConstantExprKind::GlobalName {
                        id,
                        generics: vec![],
                        trait_refs: vec![],
                    }
                };
                let cv = kind.decorate(ty.sinto(s), span.sinto(s));
                TranslateUnevalRes::GlobalName(cv)
            }
        }
    }
    impl<'tcx> ConstantExt<'tcx> for ty::Const<'tcx> {
        fn eval_constant<S: UnderOwnerState<'tcx>>(&self, s: &S) -> Option<Self> {
            let (ty, evaluated) = self
                .eval_valtree(s.base().tcx, s.param_env(), rustc_span::DUMMY_SP)
                .ok()?;
            let evaluated = ty::Const::new(s.base().tcx, ty::ConstKind::Value(ty, evaluated));
            (&evaluated != self).then_some(evaluated)
        }
    }
    impl<'tcx> ConstantExt<'tcx> for mir::Const<'tcx> {
        fn eval_constant<S: UnderOwnerState<'tcx>>(&self, s: &S) -> Option<Self> {
            let evaluated = self
                .eval(s.base().tcx, s.param_env(), rustc_span::DUMMY_SP)
                .ok()?;
            let evaluated = mir::Const::Val(evaluated, self.ty());
            (&evaluated != self).then_some(evaluated)
        }
    }
    impl<'tcx, S: UnderOwnerState<'tcx>> SInto<S, ConstantExpr> for ty::Const<'tcx> {
        #[tracing::instrument(level = "trace", skip(s))]
        fn sinto(&self, s: &S) -> ConstantExpr {
            use rustc_middle::query::Key;
            let span = self.default_span(s.base().tcx);
            match self.kind() {
                ty::ConstKind::Param(p) => {
                    let ty = p.find_ty_from_env(s.param_env());
                    let kind = ConstantExprKind::ConstRef { id: p.sinto(s) };
                    kind.decorate(ty.sinto(s), span.sinto(s))
                }
                ty::ConstKind::Infer(..) => {
                    fatal!(s[span], "ty::ConstKind::Infer node? {:#?}", self)
                }

                ty::ConstKind::Unevaluated(ucv) => match self.translate_uneval(s, ucv, span) {
                    TranslateUnevalRes::EvaluatedConstant(c) => c.sinto(s),
                    TranslateUnevalRes::GlobalName(c) => c,
                },
                ty::ConstKind::Value(ty, valtree) => valtree_to_constant_expr(s, valtree, ty, span),
                ty::ConstKind::Error(_) => fatal!(s[span], "ty::ConstKind::Error"),
                ty::ConstKind::Expr(e) => fatal!(s[span], "ty::ConstKind::Expr {:#?}", e),

                ty::ConstKind::Bound(i, bound) => {
                    supposely_unreachable_fatal!(s[span], "ty::ConstKind::Bound"; {i, bound});
                }
                _ => fatal!(s[span], "unexpected case"),
            }
        }
    }

    #[tracing::instrument(level = "trace", skip(s))]
    pub(crate) fn valtree_to_constant_expr<'tcx, S: UnderOwnerState<'tcx>>(
        s: &S,
        valtree: rustc_middle::ty::ValTree<'tcx>,
        ty: rustc_middle::ty::Ty<'tcx>,
        span: rustc_span::Span,
    ) -> ConstantExpr {
        let kind = match (valtree, ty.kind()) {
            (_, ty::Ref(_, inner_ty, _)) => {
                ConstantExprKind::Borrow(valtree_to_constant_expr(s, valtree, *inner_ty, span))
            }
            (ty::ValTree::Branch(valtrees), ty::Str) => {
                let bytes = valtrees
                    .iter()
                    .map(|x| match x {
                        ty::ValTree::Leaf(leaf) => leaf.to_u8(),
                        _ => fatal!(
                            s[span],
                            "Expected a flat list of leaves while translating \
                            a str literal, got a arbitrary valtree."
                        ),
                    })
                    .collect();
                ConstantExprKind::Literal(ConstantLiteral::byte_str(bytes))
            }
            (ty::ValTree::Branch(_), ty::Array(..) | ty::Tuple(..) | ty::Adt(..)) => {
                let contents: rustc_middle::ty::DestructuredConst = s
                    .base()
                    .tcx
                    .destructure_const(ty::Const::new_value(s.base().tcx, valtree, ty));
                let fields = contents.fields.iter().copied();
                match ty.kind() {
                    ty::Array(_, _) => ConstantExprKind::Array {
                        fields: fields.map(|field| field.sinto(s)).collect(),
                    },
                    ty::Tuple(_) => ConstantExprKind::Tuple {
                        fields: fields.map(|field| field.sinto(s)).collect(),
                    },
                    ty::Adt(def, _) => {
                        let variant_idx = contents
                            .variant
                            .s_expect(s, "destructed const of adt without variant idx");
                        let variant_def = &def.variant(variant_idx);

                        ConstantExprKind::Adt {
                            info: get_variant_information(def, variant_idx, s),
                            fields: fields
                                .into_iter()
                                .zip(&variant_def.fields)
                                .map(|(value, field)| ConstantFieldExpr {
                                    field: field.did.sinto(s),
                                    value: value.sinto(s),
                                })
                                .collect(),
                        }
                    }
                    _ => unreachable!(),
                }
            }
            (ty::ValTree::Leaf(x), ty::RawPtr(_, _)) => {
                use crate::rustc_type_ir::inherent::Ty;
                let raw_address = x.to_bits_unchecked();
                let uint_ty = UintTy::Usize;
                let usize_ty = rustc_middle::ty::Ty::new_usize(s.base().tcx).sinto(s);
                let lit = ConstantLiteral::Int(ConstantInt::Uint(raw_address, uint_ty));
                ConstantExprKind::Cast {
                    source: ConstantExprKind::Literal(lit).decorate(usize_ty, span.sinto(s)),
                }
            }
            (ty::ValTree::Leaf(x), _) => {
                ConstantExprKind::Literal(scalar_int_to_constant_literal(s, x, ty))
            }
            _ => supposely_unreachable_fatal!(
                s[span], "valtree_to_expr";
                {valtree, ty}
            ),
        };
        kind.decorate(ty.sinto(s), span.sinto(s))
    }

    /// Use the const-eval interpreter to convert an evaluated operand back to a structured
    /// constant expression.
    fn op_to_const<'tcx, S: UnderOwnerState<'tcx>>(
        s: &S,
        span: rustc_span::Span,
        ecx: &rustc_const_eval::const_eval::CompileTimeInterpCx<'tcx>,
        op: rustc_const_eval::interpret::OpTy<'tcx>,
    ) -> InterpResult<'tcx, ConstantExpr> {
        use crate::rustc_const_eval::interpret::Projectable;
        // Code inspired from `try_destructure_mir_constant_for_user_output` and
        // `const_eval::eval_queries::op_to_const`.
        let tcx = s.base().tcx;
        let ty = op.layout.ty;
        // Helper for struct-likes.
        let read_fields = |of: rustc_const_eval::interpret::OpTy<'tcx>, field_count| {
            (0..field_count).map(move |i| {
                let field_op = ecx.project_field(&of, i)?;
                op_to_const(s, span, &ecx, field_op)
            })
        };
        let kind = match ty.kind() {
            // Detect statics
            _ if let Some(place) = op.as_mplace_or_imm().left()
                && let ptr = place.ptr()
                && let (alloc_id, _, _) = ecx.ptr_get_alloc_id(ptr, 0)?
                && let interpret::GlobalAlloc::Static(did) = tcx.global_alloc(alloc_id) =>
            {
                ConstantExprKind::GlobalName {
                    id: did.sinto(s),
                    generics: Vec::new(),
                    trait_refs: Vec::new(),
                }
            }
            ty::Char | ty::Bool | ty::Uint(_) | ty::Int(_) | ty::Float(_) => {
                let scalar = ecx.read_scalar(&op)?;
                let scalar_int = scalar.try_to_scalar_int().unwrap();
                let lit = scalar_int_to_constant_literal(s, scalar_int, ty);
                ConstantExprKind::Literal(lit)
            }
            ty::Adt(adt_def, ..) if !adt_def.is_union() => {
                let variant = ecx.read_discriminant(&op)?;
                let down = ecx.project_downcast(&op, variant)?;
                let field_count = adt_def.variants()[variant].fields.len();
                let fields = read_fields(down, field_count)
                    .zip(&adt_def.variant(variant).fields)
                    .map(|(value, field)| {
                        interp_ok(ConstantFieldExpr {
                            field: field.did.sinto(s),
                            value: value?,
                        })
                    })
                    .collect::<InterpResult<Vec<_>>>()?;
                let variants_info = get_variant_information(adt_def, variant, s);
                ConstantExprKind::Adt {
                    info: variants_info,
                    fields,
                }
            }
            ty::Tuple(args) => {
                let fields = read_fields(op, args.len()).collect::<InterpResult<Vec<_>>>()?;
                ConstantExprKind::Tuple { fields }
            }
            ty::Array(..) | ty::Slice(..) => {
                let len = op.len(ecx)?;
                let fields = (0..len)
                    .map(|i| {
                        let op = ecx.project_index(&op, i)?;
                        op_to_const(s, span, ecx, op)
                    })
                    .collect::<InterpResult<Vec<_>>>()?;
                ConstantExprKind::Array { fields }
            }
            ty::Str => {
                let str = ecx.read_str(&op.assert_mem_place())?;
                ConstantExprKind::Literal(ConstantLiteral::Str(str.to_owned()))
            }
            ty::FnDef(def_id, args) => {
                let (def_id, generics, generics_impls, method_impl) =
                    get_function_from_def_id_and_generics(s, *def_id, args);
                ConstantExprKind::FnPtr {
                    def_id,
                    generics,
                    generics_impls,
                    method_impl,
                }
            }
            ty::RawPtr(..) | ty::Ref(..) => {
                let op = ecx.deref_pointer(&op)?;
                let val = op_to_const(s, span, ecx, op.into())?;
                match ty.kind() {
                    ty::Ref(..) => ConstantExprKind::Borrow(val),
                    ty::RawPtr(.., mutability) => ConstantExprKind::RawBorrow {
                        arg: val,
                        mutability: mutability.sinto(s),
                    },
                    _ => unreachable!(),
                }
            }
            _ => {
                fatal!(s[span], "Cannot convert constant back to an expression"; {op})
            }
        };
        let val = kind.decorate(ty.sinto(s), span.sinto(s));
        interp_ok(val)
    }

    pub fn const_value_to_constant_expr<'tcx, S: UnderOwnerState<'tcx>>(
        s: &S,
        ty: rustc_middle::ty::Ty<'tcx>,
        val: mir::ConstValue<'tcx>,
        span: rustc_span::Span,
    ) -> InterpResult<'tcx, ConstantExpr> {
        let tcx = s.base().tcx;
        let param_env = ty::ParamEnv::reveal_all();
        let (ecx, op) = rustc_const_eval::const_eval::mk_eval_cx_for_const_val(
            tcx.at(span),
            param_env,
            val,
            ty,
        )
        .unwrap();
        op_to_const(s, span, &ecx, op)
    }
}

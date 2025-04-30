//! Logic for translating frontend representations into the internal AST.
//!
//! It handles fallbacks for unsupported constructs by emitting `Diagnostic` errors.

use crate::ast::diagnostics::*;
use crate::ast::{self as dst, GenericValue};
use hax_frontend_exporter::{
    self as src, ConstantExprKind, ConstantInt, ConstantLiteral, Decorated, GenericArg,
};

use hax_frontend_exporter::ThirBody as Body;

fn translate_ty(ty: &src::Ty, span: dst::Span) -> dst::Ty {
    let translate_ty = |ty| translate_ty(ty, span);
    match ty.inner().as_ref() {
        src::TyKind::Bool => dst::Ty::Primitive(dst::PrimitiveTy::Bool),
        src::TyKind::Int(size) => dst::Ty::Primitive(dst::PrimitiveTy::Int(dst::IntKind {
            size: (*size).into(),
            signedness: dst::Signedness::Signed,
        })),
        src::TyKind::Uint(size) => dst::Ty::Primitive(dst::PrimitiveTy::Int(dst::IntKind {
            size: (*size).into(),
            signedness: dst::Signedness::Unsigned,
        })),
        src::TyKind::Ref(_, ty, mutability) => dst::Ty::Ref {
            inner: Box::new(translate_ty(ty)),
            mutable: *mutability,
        },
        src::TyKind::Tuple(types) => dst::Ty::Tuple(types.iter().map(translate_ty).collect()),
        src::TyKind::Arrow(binder) => dst::Ty::Arrow {
            inputs: binder.value.inputs.iter().map(translate_ty).collect(),
            output: Box::new(translate_ty(&binder.value.output)),
        },
        src::TyKind::Slice(ty) => dst::Ty::App {
            head: dst::GlobalId::slice(),
            args: vec![dst::GenericValue::Ty(translate_ty(ty.as_ref()))],
        },
        src::TyKind::Array(ty, _constant) => dst::Ty::App {
            // TODO: translate as a slice
            head: dst::GlobalId::slice(),
            args: vec![dst::GenericValue::Ty(translate_ty(ty.as_ref()))],
        },
        ty => dst::Ty::Error(Diagnostic::new(
            dst::Node::Unknown(format!("Rust THIR: ty: {ty:?}")),
            DiagnosticInfo {
                context: Context::Import,
                span,
                kind: DiagnosticInfoKind::Custom("Unimplemented".to_string()),
            },
        )),
    }
}
fn translate_pat(pat: &src::Pat) -> dst::Pat {
    let span = (&pat.span).into();
    let kind = match pat.contents.as_ref() {
        src::PatKind::Wild => dst::PatKind::Wild,
        src::PatKind::Binding { var, .. } => dst::PatKind::Binding {
            mutable: false,
            var: var.into(),
            mode: dst::BindingMode::ByValue,
        },
        pat => dst::PatKind::Error(Diagnostic::new(
            dst::Node::Unknown(format!("Rust THIR: pat: {pat:?}")),
            DiagnosticInfo {
                context: Context::Import,
                span,
                kind: DiagnosticInfoKind::Custom("Unimplemented".to_string()),
            },
        )),
    };
    let ty = translate_ty(&pat.ty, span);
    let meta = dst::Metadata {
        span,
        attrs: translate_attributes(&pat.attributes),
    };
    dst::Pat { kind, ty, meta }
}
fn translate_param(param: &src::Param, span: dst::Span) -> Result<dst::Param, DiagnosticInfo> {
    Ok(dst::Param {
        pat: translate_pat(param.pat.as_ref().ok_or(DiagnosticInfo {
            context: Context::Import,
            span,
            kind: DiagnosticInfoKind::ImportParamWithoutPattern,
        })?),
        ty: dst::SpannedTy {
            ty: translate_ty(&param.ty, span),
            span: param.ty_span.as_ref().map(Into::into).unwrap_or(span),
        },
        attributes: vec![],
    })
}
fn translate_generic_arg(generic_arg: &GenericArg, span: dst::Span) -> GenericValue {
    match generic_arg {
        GenericArg::Lifetime(region) => unimplemented!(),
        GenericArg::Type(ty) => GenericValue::Ty(translate_ty(ty, span)),
        GenericArg::Const(c_expr) => GenericValue::Expr(translate_constant_expr(c_expr)),
    }
}
fn translate_generic_args(generic_args: &Vec<GenericArg>, span: dst::Span) -> Vec<GenericValue> {
    generic_args
        .iter()
        .map(|generic_arg| translate_generic_arg(generic_arg, span))
        .collect()
}
fn translate_int_literal(ty: &dst::Ty, value: u128, negative: bool) -> dst::Literal {
    match ty {
        dst::Ty::Primitive(dst::PrimitiveTy::Int(kind)) => dst::Literal::Int {
            value,
            negative,
            kind: kind.clone(),
        },
        _ => unimplemented!(),
    }
}
fn translate_constant_expr(c_expr: &Decorated<ConstantExprKind>) -> dst::Expr {
    let span = (&c_expr.span).into();
    let ty = translate_ty(&c_expr.ty, span);
    let kind = match c_expr.contents.as_ref() {
        ConstantExprKind::Literal(lit) => dst::ExprKind::Literal(match lit {
            ConstantLiteral::Bool(bool) => dst::Literal::Bool(*bool),
            ConstantLiteral::Int(ConstantInt::Int(value, _)) => {
                translate_int_literal(&ty, i128::abs(*value) as u128, *value < 0)
            }
            ConstantLiteral::Int(ConstantInt::Uint(value, _)) => {
                translate_int_literal(&ty, *value, false)
            }
            _ => unimplemented!(),
        }),
        ConstantExprKind::Adt { info, fields } => unimplemented!(),
        ConstantExprKind::Array { fields } => unimplemented!(),
        ConstantExprKind::Tuple { fields } => unimplemented!(),
        ConstantExprKind::GlobalName {
            id,
            generics,
            trait_refs,
        } => unimplemented!(),
        _ => unimplemented!(),
    };
    dst::Expr {
        kind: Box::new(kind),
        ty,
        meta: dst::Metadata {
            span,
            attrs: vec![],
        },
    }
}
fn translate_expr(expr: &src::Expr) -> dst::Expr {
    let span = (&expr.span).into();
    let ty = translate_ty(&expr.ty, span);
    let kind = match expr.contents.as_ref() {
        src::ExprKind::Literal { lit, neg } => dst::ExprKind::Literal(match lit.node {
            src::LitKind::Bool(bool) => dst::Literal::Bool(bool),
            src::LitKind::Int(value, _) => translate_int_literal(&ty, value, *neg),
            _ => unimplemented!(),
        }),
        src::ExprKind::Index { lhs, index } => {
            let head = dst::Expr {
                kind: Box::new(dst::ExprKind::GlobalId(dst::GlobalId::index())),
                ty: ty.clone(),
                meta: dst::Metadata {
                    span,
                    attrs: vec![],
                },
            };
            let args = vec![translate_expr(lhs), translate_expr(index)];
            dst::ExprKind::App {
                head,
                args,
                generic_args: Vec::new(),
                bounds_impls: Vec::new(),
                trait_: None,
            }
        }
        src::ExprKind::GlobalName { id, .. } => dst::ExprKind::GlobalId(id.clone().into()),
        src::ExprKind::PointerCoercion { source, .. } => return translate_expr(source),
        src::ExprKind::Array { fields } => {
            dst::ExprKind::Array(fields.iter().map(translate_expr).collect())
        }
        src::ExprKind::Call {
            fun,
            args,
            generic_args,
            bounds_impls,
            r#trait,
            ..
        } => {
            let head = translate_expr(fun);
            let args = args.iter().map(translate_expr).collect::<Vec<_>>();
            let generic_args = translate_generic_args(generic_args, span);

            let trait_ = r#trait.as_ref().map(|(impl_expr, g_args)| {
                (impl_expr.clone(), translate_generic_args(&g_args, span))
            });
            dst::ExprKind::App {
                head,
                args,
                generic_args,
                bounds_impls: bounds_impls.clone(),
                trait_,
            }
        }
        src::ExprKind::Borrow {
            borrow_kind: src::BorrowKind::Shared,
            arg,
        } => dst::ExprKind::Borrow {
            mutable: false,
            inner: translate_expr(arg),
        },
        src::ExprKind::Tuple { fields } => {
            dst::ExprKind::Tuple(fields.iter().map(translate_expr).collect())
        }
        src::ExprKind::Deref { arg } => dst::ExprKind::Deref(translate_expr(arg)),
        src::ExprKind::VarRef { id } => dst::ExprKind::LocalId(id.into()),
        src::ExprKind::Block {
            block: src::Block { stmts, expr, .. },
        } => {
            let mut terminator = expr.as_ref().map(translate_expr).unwrap_or_else(|| {
                let kind = dst::ExprKind::Tuple(vec![]);
                dst::Expr {
                    kind: Box::new(kind),
                    ty,
                    meta: dst::Metadata {
                        span,
                        attrs: vec![],
                    },
                }
            });
            for src::Stmt { kind: stmt } in stmts.iter().rev() {
                let (lhs, rhs) = match stmt {
                    src::StmtKind::Let {
                        pattern: lhs,
                        initializer: Some(rhs),
                        ..
                    } => (translate_pat(lhs), translate_expr(rhs)),
                    src::StmtKind::Expr { expr, .. } => {
                        let rhs = translate_expr(expr);
                        (
                            dst::Pat {
                                kind: dst::PatKind::Wild,
                                ty: rhs.ty.clone(),
                                meta: dst::Metadata {
                                    attrs: vec![],
                                    ..rhs.meta
                                },
                            },
                            rhs,
                        )
                    }
                    _ => unimplemented!(),
                };
                let ty = terminator.ty.clone();
                let kind = dst::ExprKind::Let {
                    lhs,
                    rhs,
                    body: terminator,
                };
                terminator = dst::Expr {
                    kind: Box::new(kind),
                    ty,
                    meta: dst::Metadata {
                        span,
                        attrs: vec![],
                    },
                }
            }
            return terminator;
        }
        expr => dst::ExprKind::Error(Diagnostic::new(
            dst::Node::Unknown(format!("Rust THIR: expr: {expr:?}")),
            DiagnosticInfo {
                context: Context::Import,
                span,
                kind: DiagnosticInfoKind::Custom("Unimplemented".to_string()),
            },
        )),
    };
    dst::Expr {
        kind: Box::new(kind),
        ty,
        meta: dst::Metadata {
            span,
            attrs: vec![],
        },
    }
}
fn translate_attributes(_attributes: &[src::Attribute]) -> Vec<dst::Attribute> {
    vec![]
}

pub fn translate_item_kind(
    item_kind: &src::ItemKind<Body>,
    name: dst::GlobalId,
    span: dst::Span,
) -> dst::ItemKind {
    match item_kind {
        src::ItemKind::Fn {
            ident,
            generics,
            def: fn_def,
        } => {
            let params = fn_def
                .params
                .iter()
                .map(|param| translate_param(param, span))
                .collect::<Result<_, _>>();
            let params = match params {
                Ok(params) => params,
                Err(diag_info) => {
                    return dst::ItemKind::Error(Diagnostic::new(
                        dst::Node::Unknown(format!("Rust THIR: param in function <{name:?}>")),
                        diag_info,
                    ))
                }
            };
            dst::ItemKind::Fn {
                name,
                generics: dst::Generics,
                body: translate_expr(&fn_def.body),
                params,
                safety: dst::SafetyKind::Safe,
            }
        }
        _ => dst::ItemKind::Error(Diagnostic::new(
            dst::Node::Unknown(format!("Rust THIR: item: {item_kind:?}")),
            DiagnosticInfo {
                context: Context::Import,
                span,
                kind: DiagnosticInfoKind::Custom("Unimplemented".to_string()),
            },
        )),
    }
}

pub fn translate_item(item: &src::Item<Body>) -> dst::Item {
    let span = (&item.span).into();
    let name: dst::GlobalId = item.owner_id.clone().into();
    let kind = translate_item_kind(&item.kind, name.clone(), span);
    dst::Item {
        ident: name,
        kind,
        meta: dst::Metadata {
            span,
            attrs: translate_attributes(&item.attributes.attributes[..]),
        },
    }
}

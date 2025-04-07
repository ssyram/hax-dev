#![feature(coverage_attribute)]
#![allow(unused_attributes)]
#![allow(dead_code)]
#![allow(unreachable_code)]
#[cfg(any(feature = "json", feature = "fstar", feature = "coq"))]
mod attr;
#[cfg(any(feature = "json", feature = "fstar", feature = "coq"))]
mod auxiliary;
#[cfg(any())]
mod branch;
#[cfg(any(feature = "json", feature = "fstar", feature = "coq"))]
mod condition;
mod mcdc;
#[cfg(any(feature = "json", feature = "fstar"))]
mod abort;
#[cfg(any(feature = "json", feature = "fstar", feature = "coq"))]
mod assert_not;
#[cfg(any(feature = "json", feature = "fstar", feature = "coq"))]
#[path="assert-ne.rs"]
mod assert_ne;
#[cfg(any(feature = "json", feature = "fstar"))]
mod assert;
#[cfg(any())]
mod async_block;
#[cfg(any())]
mod async_closure;
#[cfg(any())]
mod r#async;
#[cfg(any())]
mod async2;
#[cfg(any())]
mod await_ready;
#[cfg(any())]
mod bad_counter_ids;
#[cfg(any())]
mod bench;
#[cfg(any())]
mod closure_bug;
#[cfg(any())]
mod closure_macro_async;
#[cfg(any(feature = "json", feature = "fstar", feature = "coq"))]
mod closure_macro;
#[cfg(any())]
mod closure;
#[cfg(any(feature = "json", feature = "fstar", feature = "coq"))]
mod closure_unit_return;
#[cfg(any(feature = "json"))]
mod color;
#[cfg(any(feature = "json", feature = "fstar", feature = "coq"))]
mod conditions;
#[cfg(any(feature = "json", feature = "fstar"))]
mod r#continue;
#[cfg(any())]
mod coroutine;
#[cfg(any())]
mod coverage_attr_closure;
#[cfg(any(feature = "json", feature = "fstar", feature = "coq"))]
mod dead_code;
#[cfg(any())]
#[path="discard-all-issue-133606.rs"]
mod discard_all_issue_133606;
#[cfg(any(feature = "json", feature = "fstar", feature = "coq"))]
mod drop_trait;
#[cfg(any(feature = "json", feature = "fstar", feature = "coq"))]
mod fn_sig_into_try;
#[cfg(any(feature = "json", feature = "fstar", feature = "coq"))]
mod generics;
#[cfg(any())]
#[path="generic-unused-impl.rs"]
mod generic_unused_impl;
#[cfg(any())]
mod holes;
#[cfg(any(feature = "json", feature = "fstar", feature = "coq"))]
mod if_else;
#[cfg(any(feature = "json"))]
mod if_not;
#[cfg(any(feature = "json", feature = "fstar", feature = "coq"))]
mod r#if;
#[cfg(any(feature = "json", feature = "fstar", feature = "coq"))]
mod ignore_map;
#[cfg(any(feature = "json", feature = "fstar", feature = "coq"))]
mod ignore_run;
#[cfg(any(feature = "json", feature = "fstar", feature = "coq"))]
#[path="inline-dead.rs"]
mod inline_dead;
#[cfg(any())]
mod inline_mixed;
#[cfg(any(feature = "json"))]
mod inline;
#[cfg(any(feature = "json"))]
mod inner_items;
#[cfg(any(feature = "json", feature = "fstar", feature = "coq"))]
#[path="issue-83601.rs"]
mod issue_83601;
#[cfg(any())]
#[path="issue-84561.rs"]
mod issue_84561;
#[cfg(any())]
#[path="issue-85461.rs"]
mod issue_85461;
#[cfg(any())]
#[path="issue-93054.rs"]
mod issue_93054;
#[cfg(any(feature = "json", feature = "fstar", feature = "coq"))]
mod lazy_boolean;
#[cfg(any(feature = "json"))]
mod let_else_loop;
#[cfg(any(feature = "json", feature = "fstar", feature = "coq"))]
mod long_and_wide;
#[cfg(any(feature = "json"))]
#[path="loop-break.rs"]
mod loop_break;
#[cfg(any(feature = "json"))]
mod loop_break_value;
#[cfg(any(feature = "json"))]
mod loops_branches;
#[cfg(any(feature = "json", feature = "fstar", feature = "coq"))]
mod macro_in_closure;
#[cfg(any())]
mod macro_name_span;
#[cfg(any(feature = "json", feature = "fstar", feature = "coq"))]
mod match_or_pattern;
#[cfg(any(feature = "json", feature = "fstar"))]
mod nested_loops;
#[cfg(any())]
#[path="no-core.rs"]
mod no_core;
#[cfg(any(feature = "json", feature = "fstar", feature = "coq"))]
mod no_cov_crate;
#[cfg(any(feature = "json", feature = "fstar", feature = "coq"))]
mod no_spans_if_not;
#[cfg(any(feature = "json", feature = "fstar", feature = "coq"))]
mod no_spans;
#[cfg(any(feature = "json", feature = "fstar"))]
mod overflow;
#[cfg(any(feature = "json", feature = "fstar"))]
mod panic_unwind;
#[cfg(any(feature = "json", feature = "fstar", feature = "coq"))]
mod partial_eq;
#[cfg(any(feature = "json"))]
mod simple_loop;
#[cfg(any(feature = "json"))]
mod simple_match;
#[cfg(any(feature = "json", feature = "fstar", feature = "coq"))]
mod sort_groups;
#[cfg(any(feature = "json", feature = "fstar", feature = "coq"))]
mod test_harness;
#[cfg(any(feature = "json"))]
mod tight_inf_loop;
#[cfg(any(feature = "json", feature = "fstar", feature = "coq"))]
mod trivial;
#[cfg(any(feature = "json", feature = "fstar", feature = "coq"))]
mod try_error_result;
#[cfg(any(feature = "json"))]
mod unicode;
#[cfg(any())]
mod unreachable;
#[cfg(any(feature = "json", feature = "fstar", feature = "coq"))]
mod unused_mod;
#[cfg(any(feature = "json", feature = "fstar"))]
mod unused;
#[cfg(any())]
mod uses_crate;
#[cfg(any())]
mod uses_inline_crate;
#[cfg(any(feature = "json", feature = "fstar"))]
mod while_early_ret;
#[cfg(any(feature = "json"))]
mod r#while;
#[cfg(any())]
mod r#yield;
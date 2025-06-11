module Core.Fmt.Rt
open Rust_primitives

val t_Argument: Type0
val impl_1__new_display (#t:Type0) (x: t): t_Argument
val impl_1__new_debug (#t:Type0) (x: t): t_Argument
val impl_4__new_v1_formatted (#t:Type0) (x: t) : t_Argument
val impl_1__new_binary (#t:Type0) (x: t) : t_Argument
val impl_1__new_lower_hex (#t:Type0) (x: t) : t_Argument

val impl_1__none : unit -> t_Array Core.Fmt.Rt.t_Argument (MkInt 0)

type t_Count =
  | Count_Is : int_t U16 -> t_Count
  | Count_Param : int_t U16 -> t_Count
  | Count_Implied : t_Count

type t_Placeholder: Type0
val impl_Placeholder__new : usize -> (int_t U32) -> t_Count -> t_Count -> t_Placeholder

type t_UnsafeArg
val impl_UnsafeArg__new : unit -> t_UnsafeArg

module Core.Iter.Traits.Collect

open Rust_primitives

class t_IntoIterator self = {
  f_IntoIter: Type0;
  // f_Item: Type0;
  f_into_iter: self -> f_IntoIter;
}

unfold instance impl t {| Core.Iter.Traits.Iterator.t_Iterator t |}: t_IntoIterator t = {
  f_IntoIter = t;
  f_into_iter = id;
}

class t_Extend
  (v_Self: Type0) (v_A: Type0)
  = {
  f_extend_post:
      #v_T: Type0 ->
      {| i1:
          Core.Iter.Traits.Collect.t_IntoIterator
          v_T |} ->
      v_Self ->
      v_T ->
      v_Self
    -> Type0; 
  f_extend:
      #v_T: Type0 ->
      {| i1:
          Core.Iter.Traits.Collect.t_IntoIterator
          v_T |} ->
      x0: v_Self ->
      x1: v_T
    -> v_Self
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val extend_slice (t: eqtype): t_Extend (t_Slice t) t

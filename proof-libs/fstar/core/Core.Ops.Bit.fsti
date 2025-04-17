module Core.Ops.Bit
open FStar.Mul

class t_Shr (v_Self: Type0) (v_Rhs: Type0) = {
  f_Output:Type0;
}

class t_BitXor self rhs = {
  [@@@ Tactics.Typeclasses.no_method]
  f_Output: Type;
  f_bitxor_pre: self -> rhs -> bool;
  f_bitxor_post: self -> rhs -> f_Output -> bool;
  f_bitxor: x:self -> y:rhs -> Pure f_Output (f_bitxor_pre x y) (fun r -> f_bitxor_post x y r);
}

class t_BitAnd self rhs = {
  [@@@ Tactics.Typeclasses.no_method]
  f_Output: Type;
  f_bitand_pre: self -> rhs -> bool;
  f_bitand_post: self -> rhs -> f_Output -> bool;
  f_bitand: x:self -> y:rhs -> Pure f_Output (f_bitand_pre x y) (fun r -> f_bitand_post x y r);
}


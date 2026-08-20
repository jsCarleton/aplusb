(* Hand-encoded Coq AST for the add function defined in add.wat. This term
   is proved (in AddCorrespondence.v) to be byte-identical, via
   WasmCert-Coq's binary parser, to what wat2wasm actually compiles from
   add.wat -- so this file's correspondence with the .wat source is not
   merely asserted by eye, it is machine-checked. Local indices follow the
   .wat source: 0=$a (param) 1=$b (param). *)

From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From Wasm Require Import datatypes.
Require Import BinNat.

Definition l_a : localidx := 0%N.
Definition l_b : localidx := 1%N.

Definition add_body : list basic_instruction :=
  [:: BI_local_get l_a; BI_local_get l_b; BI_binop T_i32 (Binop_i BOI_add) ].

(* No non-parameter locals: modfunc_locals does not include the two
   parameters ($a, $b), which are supplied by function_type instead. *)
Definition add_locals : list value_type := [::].

Definition add_module_func : module_func :=
  {| modfunc_type := 0%N;
     modfunc_locals := add_locals;
     modfunc_body := add_body |}.

Definition add_function_type : function_type :=
  Tf [:: T_num T_i32; T_num T_i32] [:: T_num T_i32].

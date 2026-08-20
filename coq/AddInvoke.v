(* Direct-invocation setup: a minimal store/frame/function-closure and
   initial configuration for invoking add_module_func via the real
   reduce/reduce_trans semantics, skipping WasmCert-Coq's generic
   module-instantiation machinery (module_typing/instantiate/alloc_module),
   which is orthogonal boilerplate already proven sound upstream and not
   specific to what this add function actually does. There are no host
   function calls and no memory anywhere in add_module_func (add.wat
   declares no memory), so we reuse WasmCert-Coq's own ready-made "no host
   functions" instances (host_function := void) from extraction_instance.v
   rather than inventing new ones. *)

From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From Wasm Require Import datatypes operations opsem memory extraction_instance.
From Add Require Import AddAst.
Require Import BinNat.

Existing Instance Memory_instance.memory_instance.
Existing Instance Extraction_instance.hfc.
Existing Instance Extraction_instance.host_instance.

Definition add_moduleinst : moduleinst :=
  {| inst_types := [:: add_function_type];
     inst_funcs := [:: 0%N];
     inst_tables := [::];
     inst_mems := [::];
     inst_globals := [::];
     inst_elems := [::];
     inst_datas := [::];
     inst_exports := [::] |}.

Definition initial_store : store_record :=
  {| s_funcs := [:: FC_func_native add_function_type add_moduleinst add_module_func];
     s_tables := [::];
     s_mems := [::];
     s_globals := [::];
     s_elems := [::];
     s_datas := [::] |}.

Definition initial_frame : frame := {| f_locs := [::]; f_inst := add_moduleinst |}.

(* The invoked function takes ($a $b) as i32 arguments off the stack,
   immediately followed by AI_invoke of function address 0 (the only
   function in our hand-built store). *)
Definition initial_config (a b : Wasm_int.Int32.int)
  : host_state * store_record * frame * list administrative_instruction :=
  (tt, initial_store, initial_frame,
   [:: AI_basic (BI_const_num (VAL_int32 a));
       AI_basic (BI_const_num (VAL_int32 b));
       AI_invoke 0%N]).

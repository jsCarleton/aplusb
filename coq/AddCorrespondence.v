(* Machine-checked correspondence between add.wat and the hand-encoded
   Coq AST in AddAst.v.

   Trust chain: wat2wasm compiles add.wat -> add.wasm (trusted, external,
   outside Coq); tools/wasm_bytes_to_coq.py copies those exact bytes into
   AddBytes.v (mechanical, no interpretation); WasmCert-Coq's binary parser
   (also outside the kernel's soundness argument, but its *output* here is
   checked *by* the kernel) turns those bytes into a `module` AST. This file
   proves, by kernel-checked computation, that the parsed function is
   identical to add_module_func -- the term every other proof in this
   project is actually about. That closes the "did I transcribe the .wat
   correctly into Coq" gap: from here on, add_module_func is provably what
   wat2wasm actually produced from add.wat, not just a lookalike. *)

From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From Wasm Require Import datatypes binary_format_parser.
From Add Require Import AddBytes.
From Add Require Import AddAst.

Definition parsed_module : option module := run_parse_module add_wasm_bytes.

Lemma add_wasm_parses : exists m, parsed_module = Some m.
Proof. eexists. vm_compute. reflexivity. Qed.

Lemma add_wasm_func_matches :
  match parsed_module with
  | Some m => List.nth_error m.(mod_funcs) 0 = Some add_module_func
  | None => False
  end.
Proof. vm_compute. reflexivity. Qed.

Lemma add_wasm_type_matches :
  match parsed_module with
  | Some m => List.nth_error m.(mod_types) 0 = Some add_function_type
  | None => False
  end.
Proof. vm_compute. reflexivity. Qed.

(* Top-level correctness: invoking add_module_func through WasmCert-Coq's
   real small-step semantics, on any two i32 arguments, reduces to a single
   value equal to Wasm_int.Int32.iadd of those arguments -- i.e. exactly the
   32-bit wrapping addition the Wasm spec defines i32.add to perform. A
   corollary restates that in "textbook" unsigned-integer-mod-2^32 terms. *)

From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From Wasm Require Import datatypes operations opsem memory extraction_instance.
From Add Require Import AddAst AddInvoke AddSteps.
Require Import BinNat.
Require Import ZArith.

Existing Instance Memory_instance.memory_instance.
Existing Instance Extraction_instance.hfc.
Existing Instance Extraction_instance.host_instance.

Open Scope Z_scope.

Definition mkframe (a b : value) : frame := {| f_locs := [:: a; b]; f_inst := add_moduleinst |}.

(* r_invoke_native, specialised to our single hand-built function: pops the
   two i32 arguments into locals 0/1 (add_locals = [::], so there are no
   extra locals to default-fill), and enters a fresh frame wrapping a fresh
   (arity-1, matching the single i32 result) label around the function
   body. *)
Lemma step_invoke :
  forall hs (a b : Wasm_int.Int32.int) rest,
    reduce_trans
      (hs, initial_store, initial_frame,
       [:: AI_basic (BI_const_num (VAL_int32 a));
           AI_basic (BI_const_num (VAL_int32 b));
           AI_invoke 0%N] ++ rest)
      (hs, initial_store, initial_frame,
       [:: AI_frame 1 (mkframe (VAL_num (VAL_int32 a)) (VAL_num (VAL_int32 b)))
             [:: AI_label 1 [::] (to_e_list add_body)]] ++ rest).
Proof.
  intros hs a b rest.
  apply (step1 hs initial_store initial_frame
           [:: AI_basic (BI_const_num (VAL_int32 a));
               AI_basic (BI_const_num (VAL_int32 b));
               AI_invoke 0%N]
           hs initial_store initial_frame
           [:: AI_frame 1 (mkframe (VAL_num (VAL_int32 a)) (VAL_num (VAL_int32 b)))
                 [:: AI_label 1 [::] (to_e_list add_body)]]
           rest).
  eapply (r_invoke_native (addr := 0%N)
            (ves := [:: AI_basic (BI_const_num (VAL_int32 a)); AI_basic (BI_const_num (VAL_int32 b))])
            (vs := [:: VAL_num (VAL_int32 a); VAL_num (VAL_int32 b)]));
    reflexivity.
Qed.

(* The function body itself: local.get $a; local.get $b; i32.add. *)
Lemma add_body_runs :
  forall hs s (a b : Wasm_int.Int32.int) rest,
    reduce_trans
      (hs, s, mkframe (VAL_num (VAL_int32 a)) (VAL_num (VAL_int32 b)), to_e_list add_body ++ rest)
      (hs, s, mkframe (VAL_num (VAL_int32 a)) (VAL_num (VAL_int32 b)),
       $VN (VAL_int32 (Wasm_int.Int32.iadd a b)) :: rest).
Proof.
  intros hs s a b rest.
  set (f0 := mkframe (VAL_num (VAL_int32 a)) (VAL_num (VAL_int32 b))).
  unfold add_body.
  eapply steps_trans.
  { apply (step_local_get hs s f0 l_a (VAL_num (VAL_int32 a))). reflexivity. }
  eapply steps_trans.
  { apply prepend1.
    apply (step_local_get hs s f0 l_b (VAL_num (VAL_int32 b))). reflexivity. }
  apply (step_binop_i32 hs s f0 BOI_add a b (Wasm_int.Int32.iadd a b)).
  reflexivity.
Qed.

Theorem add_correct :
  forall (a b : Wasm_int.Int32.int),
    reduce_trans (initial_config a b)
                 (tt, initial_store, initial_frame, [:: v_to_e (VAL_num (VAL_int32 (Wasm_int.Int32.iadd a b)))]).
Proof.
  intros a b.
  unfold initial_config.
  eapply steps_trans.
  { apply (step_invoke tt a b [::]). }
  eapply steps_trans.
  { eapply reduce_trans_frame.
    eapply steps_trans.
    { eapply lift_through_label_n. apply (add_body_runs tt initial_store a b [::]). }
    apply (step1 tt initial_store (mkframe (VAL_num (VAL_int32 a)) (VAL_num (VAL_int32 b)))
             [:: AI_label 1 [::] [:: $VN (VAL_int32 (Wasm_int.Int32.iadd a b))]]
             tt initial_store (mkframe (VAL_num (VAL_int32 a)) (VAL_num (VAL_int32 b)))
             [:: $VN (VAL_int32 (Wasm_int.Int32.iadd a b))] [::]).
    apply r_simple. apply rs_label_const. reflexivity. }
  apply (step1 tt initial_store initial_frame
           [:: AI_frame 1 (mkframe (VAL_num (VAL_int32 a)) (VAL_num (VAL_int32 b)))
                 [:: $VN (VAL_int32 (Wasm_int.Int32.iadd a b))]]
           tt initial_store initial_frame
           [:: $VN (VAL_int32 (Wasm_int.Int32.iadd a b))] [::]).
  apply r_simple. eapply rs_local_const; reflexivity.
Qed.

(* Corollary: restated as plain unsigned-integer addition mod 2^32, the
   ordinary "textbook" meaning of what an i32 add instruction computes. *)
Corollary add_correct_unsigned :
  forall (a b : Wasm_int.Int32.int),
    exists final_store final_frame,
      reduce_trans (initial_config a b)
                   (tt, final_store, final_frame,
                    [:: v_to_e (VAL_num (VAL_int32 (Wasm_int.Int32.iadd a b)))]) /\
      Wasm_int.Int32.unsigned (Wasm_int.Int32.iadd a b) =
        (Wasm_int.Int32.unsigned a + Wasm_int.Int32.unsigned b) mod Wasm_int.Int32.modulus.
Proof.
  intros a b.
  exists initial_store, initial_frame.
  split.
  - apply add_correct.
  - unfold Wasm_int.Int32.iadd.
    rewrite Wasm_int.Int32.add_unsigned.
    apply Wasm_int.Int32.unsigned_repr_eq.
Qed.

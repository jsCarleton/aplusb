(* Small-step reasoning infrastructure, and the specific atomic-instruction
   lemmas needed for add_body = [local.get $a; local.get $b; i32.add].
   The general-purpose lemmas here (reduce_trans_label, reduce_trans_frame,
   step1, steps_trans, prepend1) are not specific to this function; they are
   the same machinery WasmCert-Coq's own r_label/r_frame congruence rules
   only provide a single-step version of. *)

From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From Wasm Require Import datatypes operations opsem memory extraction_instance.
From Add Require Import AddInvoke.
Require Import BinNat.
Require Import Relations.Relation_Operators.
Require Import Relations.Operators_Properties.

Existing Instance Memory_instance.memory_instance.
Existing Instance Extraction_instance.hfc.
Existing Instance Extraction_instance.host_instance.

Lemma reduce_trans_label :
  forall k (lh : lholed k) hs s f es hs' s' f' es',
    reduce_trans (hs, s, f, es) (hs', s', f', es') ->
    reduce_trans (hs, s, f, lfill lh es) (hs', s', f', lfill lh es').
Proof.
  intros k lh hs s f es hs' s' f' es' H.
  unfold reduce_trans in *.
  apply clos_rt_rt1n_iff.
  apply clos_rt_rt1n_iff in H.
  remember (hs, s, f, es) as X eqn:HeqX.
  remember (hs', s', f', es') as Y eqn:HeqY.
  revert hs s f es hs' s' f' es' HeqX HeqY.
  induction H as [X | X Ymid Z Hstep Hrest IH]; intros hs s f es hs' s' f' es' HeqX HeqY; subst.
  - inversion HeqY; subst. apply rt1n_refl.
  - destruct Ymid as [[[hsm sm] fm] esm].
    unfold reduce_tuple in Hstep.
    eapply Relation_Operators.rt1n_trans with (y := (hsm, sm, fm, lfill lh esm)).
    + eapply r_label. exact Hstep. reflexivity. reflexivity.
    + eapply (IH hsm sm fm esm hs' s' f' es'); reflexivity.
Qed.

Lemma reduce_trans_frame :
  forall hs s f0 n f es hs' s' f' es',
    reduce_trans (hs, s, f, es) (hs', s', f', es') ->
    reduce_trans (hs, s, f0, [:: AI_frame n f es]) (hs', s', f0, [:: AI_frame n f' es']).
Proof.
  intros hs s f0 n f es hs' s' f' es' H.
  unfold reduce_trans in *.
  apply clos_rt_rt1n_iff.
  apply clos_rt_rt1n_iff in H.
  remember (hs, s, f, es) as X eqn:HeqX.
  remember (hs', s', f', es') as Y eqn:HeqY.
  revert hs s f es hs' s' f' es' HeqX HeqY.
  induction H as [X | X Ymid Z Hstep Hrest IH]; intros hs s f es hs' s' f' es' HeqX HeqY; subst.
  - inversion HeqY; subst. apply rt1n_refl.
  - destruct Ymid as [[[hsm sm] fm] esm].
    unfold reduce_tuple in Hstep.
    eapply Relation_Operators.rt1n_trans with (y := (hsm, sm, f0, [:: AI_frame n fm esm])).
    + apply r_frame. exact Hstep.
    + eapply (IH hsm sm fm esm hs' s' f' es'); reflexivity.
Qed.

Lemma step1 :
  forall hs s f es hs' s' f' es' (rest : seq administrative_instruction),
    reduce hs s f es hs' s' f' es' ->
    reduce_trans (hs, s, f, es ++ rest) (hs', s', f', es' ++ rest).
Proof.
  intros hs s f es hs' s' f' es' rest Hred.
  pose proof (reduce_trans_label 0 (LH_base [::] rest) hs s f es hs' s' f' es') as Hlift.
  simpl in Hlift.
  apply Hlift.
  apply Relation_Operators.rt_step.
  unfold reduce_tuple. exact Hred.
Qed.

Lemma steps_trans :
  forall hs s f es hs1 s1 f1 es1 hs2 s2 f2 es2,
    reduce_trans (hs, s, f, es) (hs1, s1, f1, es1) ->
    reduce_trans (hs1, s1, f1, es1) (hs2, s2, f2, es2) ->
    reduce_trans (hs, s, f, es) (hs2, s2, f2, es2).
Proof.
  intros. unfold reduce_trans in *. eapply Relation_Operators.rt_trans; eauto.
Qed.

Lemma reduce_trans_prepend :
  forall hs s f es hs' s' f' es' (vs : list value),
    reduce_trans (hs, s, f, es) (hs', s', f', es') ->
    reduce_trans (hs, s, f, v_to_e_list vs ++ es) (hs', s', f', v_to_e_list vs ++ es').
Proof.
  intros hs s f es hs' s' f' es' vs H.
  pose proof (reduce_trans_label 0 (LH_base vs [::]) hs s f es hs' s' f' es' H) as Hlift.
  simpl in Hlift. rewrite !cats0 in Hlift. exact Hlift.
Qed.

Lemma prepend1 :
  forall hs s f v es hs' s' f' es',
    reduce_trans (hs, s, f, es) (hs', s', f', es') ->
    reduce_trans (hs, s, f, v_to_e v :: es) (hs', s', f', v_to_e v :: es').
Proof.
  intros hs s f v es hs' s' f' es' H.
  exact (reduce_trans_prepend hs s f es hs' s' f' es' [:: v] H).
Qed.

Lemma lift_through_label_n :
  forall n hs s f es hs' s' f' es' rest,
    reduce_trans (hs, s, f, es) (hs', s', f', es') ->
    reduce_trans (hs, s, f, AI_label n [::] es :: rest) (hs', s', f', AI_label n [::] es' :: rest).
Proof.
  intros n hs s f es hs' s' f' es' rest H.
  pose proof (reduce_trans_label 1 (LH_rec [::] n [::] (LH_base [::] [::]) rest)
                hs s f es hs' s' f' es' H) as Hlift.
  simpl in Hlift. rewrite ?cats0 in Hlift.
  exact Hlift.
Qed.

(* ===== Atomic instruction steps. ===== *)

Lemma step_local_get :
  forall hs s f j v rest,
    lookup_N f.(f_locs) j = Some v ->
    reduce_trans (hs, s, f, AI_basic (BI_local_get j) :: rest) (hs, s, f, v_to_e v :: rest).
Proof.
  intros hs s f j v rest Hlookup.
  apply (step1 hs s f [:: AI_basic (BI_local_get j)] hs s f [:: v_to_e v] rest).
  apply r_local_get. exact Hlookup.
Qed.

Lemma step_binop_i32 :
  forall hs s f op v1 v2 v rest,
    app_binop (Binop_i op) (VAL_int32 v1) (VAL_int32 v2) = Some (VAL_int32 v) ->
    reduce_trans (hs, s, f, $VN (VAL_int32 v1) :: $VN (VAL_int32 v2) :: AI_basic (BI_binop T_i32 (Binop_i op)) :: rest)
                 (hs, s, f, $VN (VAL_int32 v) :: rest).
Proof.
  intros hs s f op v1 v2 v rest Happ.
  apply (step1 hs s f [:: $VN (VAL_int32 v1); $VN (VAL_int32 v2); AI_basic (BI_binop T_i32 (Binop_i op))]
           hs s f [:: $VN (VAL_int32 v)] rest).
  apply r_simple.
  eapply rs_binop_success; [reflexivity | exact Happ].
Qed.

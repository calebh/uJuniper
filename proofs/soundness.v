Set Warnings "-notation-overridden,-parsing,-require-in-module".
From Coq Require Export
     String
     List
     Nat (* For natural number comparision operators. *)
     Arith.PeanoNat. (* For some additional lemmas about natural numbers. *)
Import List.ListNotations.
Import PeanoNat.Nat.
Import Coq.Logic.Decidable.
From Coq Require Import Lia.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.

(***************************************************************************
  Type Safety
 ***************************************************************************)

From PLF Require Import Smallstep.
From PLF Require Import Maps.
From Top Require Import uJuniperLang.
Module uJuniperSoundness.

  Definition context := partial_map ty.

  #[local] Hint Constructors has_type : core.
  #[local] Hint Constructors value : core.
  
  Axiom value_dec_link : forall t,
      value t <-> value_helper t = true.
  
  Axiom value_dec : forall t,
      value t \/ ~(value t).

(*
  Lemma value_dec : forall t,
      value t \/ ~(value t).
  Proof.
    intros.
    destruct t.
  
  Theorem progress2 : forall t T,
      empty |- t \in T ->
      value t \/ exists t', t --> t'.
  Proof.
  intros t T Ht.
  remember empty as Gamma.
  generalize dependent HeqGamma.
  induction Ht; intros HeqGamma; subst; eauto.
  - discriminate H.
  - right.
    eexists.
    destruct IHHt1; subst; eauto.
    + destruct IHHt2; subst; eauto.
      destruct t1; inversion H; simpl in H1; try discriminate.
      destruct H.
      econstructor.
      destruct Ht1.

destruct IHHt1; subst; eauto.
    + destruct IHHt2; subst; eauto.
      * left.
        econstructor.
        simpl.

destruct H; try solve_by_invert; eauto.
    * destruct H0 as [t2' Hstp]; eauto.
*)

  Lemma not_value_dec_link : forall t,
      ~(value t) <-> value_helper t = false.
  Proof.
    intros.
    intuition.
    unfold not in H.
    rewrite value_dec_link in H.
    destruct (value_helper t).
    intuition.
    reflexivity.
    rewrite value_dec_link in H0.
    rewrite H0 in H.
    inversion H.
  Qed.

(*
  Lemma not_value_dec_link_impl : forall t,
      ~(value t) -> value_helper t = false.
  Proof.
    intros.
    rewrite not_value_dec_link in H.
    trivial.
  Qed.
*)

  Lemma array_to_array : forall T a b,
      tm_array_lit T a --> b ->
      exists a', tm_array_lit T a' = b.
  Proof.
    intros.
    destruct b; inversion H; subst.
    eexists.
    eauto.
    eexists.
    eauto.
  Qed.

  Lemma progress1 : forall t T,
      empty |- t \in T ->
      ~(value t) ->
      exists t', t --> t'.
  Proof.
    intros.
    remember empty as Gamma.
    generalize dependent HeqGamma.
    induction H; intros HeqGamma; subst; eauto.
    admit.
    admit.
    admit.
    admit.
    admit.
    admit.
    admit.
    admit.
    admit.
    - induction H.
      admit.
      rewrite (not_value_dec_link (tm_array_lit T1 (x :: l))) in H0.
      simpl in H0.
      pose proof (Coq.Bool.Bool.bool_dec (value_helper x) true).
      destruct H2.
      * rewrite e in H0.
        apply value_dec_link in e.
        rewrite andb_true_l in H0.
        rewrite value_dec_link in IHForall.
        simpl in IHForall.
        rewrite not_true_iff_false in IHForall.
        intuition.
        destruct H2.
        pose proof (array_to_array T1 l x0 H2).
        destruct H3.
        subst.
        eexists.
        econstructor 14.
        trivial.
        eauto.
      * rewrite not_true_iff_false in n.
        rewrite <- not_value_dec_link in n.
        
        rewrite andb_false_l in H2.
        Search (false && _ = _).
      apply array_to_array in H3.
      destruct x0; inversion H3.
      subst.
      eexists.
      econstructor.
      inversion H3; subst.
      rewrite H6.
      eexists.
      econstructor 15.
      Search (
      econstructor 15.
      Search (_ <> true <-> _ = false).

  Theorem progress : forall t T,
      empty |- t \in T ->
      value t \/ exists t', t --> t'.
  Proof.
  intros t T Ht.
  remember empty as Gamma.
  generalize dependent HeqGamma.
  induction Ht; intros HeqGamma; subst; eauto.
  - (* T_Var *)
    (* The final rule in the given typing derivation cannot be
       [T_Var], since it can never be the case that
       [empty |- x \in T] (since the context is empty). *)
    discriminate H.
  - (* T_App *)
    (* If the last rule applied was T_App, then [t = t1 t2],
       and we know from the form of the rule that
         [empty |- t1 \in T1 -> T2]
         [empty |- t2 \in T1]
       By the induction hypothesis, each of t1 and t2 either is
       a value or can take a step. *)
    right.
    destruct IHHt1; subst; eauto.
    + (* t1 is a value *)
      destruct IHHt2; subst; eauto.
      * (* t2 is a value *)
        (* If both [t1] and [t2] are values, then we know that
           [t1 = \x0 : T0, t11], since abstractions are the
           only values that can have an arrow type.  But
           [(\x0 : T0, t11) t2 --> [x:=t2]t11] by [ST_AppAbs]. *)
        destruct H; try solve_by_invert; eauto.
      * (* t2 steps *)
        (* If [t1] is a value and [t2 --> t2'],
           then [t1 t2 --> t1 t2'] by [ST_App2]. *)
        destruct H0 as [t2' Hstp]; eauto.
    + (* t1 steps *)
      (* Finally, If [t1 --> t1'], then [t1 t2 --> t1' t2]
         by [ST_App1]. *)
      destruct H as [t1' Hstp]; eauto.
    (* FILL IN HERE *)
  - right.
    destruct IHHt1; subst; eauto; destruct IHHt2; subst; eauto; destruct IHHt3; subst; eauto; destruct H; destruct H0; destruct H1; try solve_by_invert; eauto.
  - intuition.
    + right.
      destruct H1.
      eexists.
      econstructor.
      eauto.
    + right.
      destruct H0.
      eexists.
      econstructor 8.
      trivial.
      eauto.
    + right.
      destruct H0; destruct H1.
      eexists.
      econstructor.
      eauto.
  - intuition.
    + right.
      destruct H0; subst; eauto; try solve_by_invert; eauto.
    + right.
      destruct H0; subst.
      eexists.
      econstructor.
      eauto.
  - intuition.
    + right.
      destruct H0; subst; eauto; try solve_by_invert; eauto.
    + right.
      destruct H0; subst.
      eexists.
      econstructor.
      eauto.
  - induction H.
    + repeat econstructor.
    + destruct IHForall.
      pose proof (value_dec x).
      destruct H2.
      admit.
      right.
      admit.
      pose proof (value_dec x).
      right.
      intuition.
      destruct H1.
      destruct x0; inversion H1; subst.
      eexists.
      eauto.
      eexists.
      eauto.
      eexists.
      econstructor 15.
      exists (tm_array_lit T1 (x :: x0)).
      instantiate (1:=(tm_array_lit T1 (x :: x0))).
      econstructor 15.
      destruct IHForall.
      destruct H.
      subst.
      destruct H2.
      destruct H0.
      destruct H.
      subst.
      
      destruct x.

induction H.
    + repeat econstructor.
    + intuition.
      left.
      econstructor.
      admit.
      * destruct H1.
        
        econstructor 14.
      eexists.
      econstructor 14.
      econstructor.

inversion H.
      intuition.
      * subst.
        destruct x.
        admit.
    intros.
    

 inversion H.
    + left.
      econstructor.
      econstructor.
    + subst. 
inversion H.
      subst.
      intuition.
      Focus 2.
      apply (H2 T1).
      right.
      eexists.
      econstructor 14.

simpl.
    + intuition.
      left.
      econstructor.
      econstructor.
      subst.
      * left.
        econstructor.
        econstructor.
 destruct H.
      left.
      econstructor.
      econstructor.
right.
      eexists.
      econstructor.
  Qed.

  (* ###################################################################### *)
  (** *** Substitution *)

  Lemma weakening : forall Gamma Gamma' t T,
      includedin Gamma Gamma' ->
      Gamma  |- t \in T  ->
      Gamma' |- t \in T.
  Proof.
    intros Gamma Gamma' t T H Ht.
    generalize dependent Gamma'.
    induction Ht; eauto 7 using includedin_update.
  Qed.

  Lemma weakening_empty : forall Gamma t T,
      empty |- t \in T  ->
                     Gamma |- t \in T.
  Proof.
    intros Gamma t T.
    eapply weakening.
    discriminate.
  Qed.

  Lemma substitution_preserves_typing : forall Gamma x U t v T,
      (x |-> U ; Gamma) |- t \in T ->
                                 empty |- v \in U   ->
                                                Gamma |- [x:=v]t \in T.
  Proof.
  (* UNCOMMENT THE FOLLOWING LINES AFTER COMPLETING the [has_type] EXERCISE*)
  intros Gamma x U t v T Ht Hv.
  generalize dependent Gamma. generalize dependent T.
  (* Proof: By induction on the term [t].  Most cases follow
     directly from the IH, with the exception of [var]
     and [abs]. These aren't automatic because we must
     reason about how the variables interact. The proofs
     of these cases are similar to the ones in STLC.
     We refer the reader to StlcProp.v for explanations. *)
  induction t; intros T Gamma H;
  (* in each case, we'll want to get at the derivation of H *)
    inversion H; clear H; subst; simpl; eauto.
  - (* var *)
    rename s into y. pose proof (String.string_dec x y). destruct H; subst.
    + (* x=y *)
      rewrite update_eq in H2.
      injection H2 as H2; subst.
      apply weakening_empty.
      rewrite eqb_refl; eauto.
    + (* x<>y *)
      generalize n; intro; apply eqb_neq in n; rewrite n.
      apply T_Var. rewrite update_neq in H2; auto.
  - (* abs *)
    rename s into y, t into S.
    pose proof (Bool.bool_dec (eqb_string x y) (true)).
    destruct H.
    + (* x=y *)
      rewrite e.
      apply T_Abs.
      unfold eqb_string in e.
      destruct (string_dec x y).
      subst.
      rewrite update_shadow in H5. assumption.
      discriminate.
    + (* x<>y *)
      apply Bool.not_true_is_false in n.
      rewrite n.
      apply T_Abs.
      apply IHt.
      rewrite update_permute; auto.
      unfold eqb_string in n.
      destruct (string_dec x y).
      discriminate.
      apply not_eq_sym in n0.
      assumption.    
  Qed.

  (* ###################################################################### *)
  (** *** Preservation *)

  (** Exercise: 2 points (preservation) *)
  (* Complete the proof of [preservation] for the calculus: *)
  Theorem preservation : forall t t' T,
      empty |- t \in T  ->
                     t --> t'  ->
                     empty |- t' \in T.
  Proof.
    intros t t' T HT. generalize dependent t'.
    remember empty as Gamma.
  (* Proof: By induction on the given typing derivation.
     Hint: Many cases are contradictory ([T_Var], [T_Abs]).
     The most interesting cases are [T_App], [T_Fst], and [T_Snd] *)
    (* FILL IN HERE *)
    induction HT.
    - intros.
      subst.
      inversion H.
    - intros.
      inversion H.
    - intros.
      inversion H; subst.
      inversion HT1; subst.
      * apply (substitution_preserves_typing empty x T2 t0 t2 T1).
        trivial.
        trivial.
      * econstructor.
        eapply IHHT1.
        trivial.
        trivial.
        inversion H; subst; trivial.
      * econstructor.
        eauto.
        apply IHHT2.
        trivial.
        trivial.
    - intros.
      inversion H.
    - intros.
      inversion H.
    - intros.
      inversion H; subst.
      * trivial.
      * trivial.
      * econstructor.
        apply IHHT1.
        trivial.
        trivial.
        trivial.
        trivial.
    - intros.
      inversion H; subst.
      * econstructor.
        apply IHHT1.
        trivial.
        trivial.
        trivial.
      * econstructor.
        trivial.
        apply IHHT2.
        trivial.
        trivial.
    - intros.
      inversion H; subst.
      * econstructor.
        apply IHHT.
        trivial.
        trivial.
      * inversion HT; subst.
        trivial.
    - intros.
      inversion H; subst.
      * econstructor.
        apply IHHT.
        trivial.
        trivial.
      * inversion HT; subst.
        trivial.
  Qed.

  Definition stuck (t:tm) : Prop :=
    (normal_form step) t /\ ~ value t.

  (* Combine the proofs of [progress] and [preservation] to complete the
   proof of type soundness: *)
  Corollary soundness :
    forall t t' T,
      (empty |- t \in T) ->
      t -->* t' ->
      ~(stuck t').
  Proof.
    (* FILL IN HERE *)
    intros.
    generalize dependent H.
    induction H0.
    - intros.
      pose proof (progress x T).
      intuition.
      inversion H1.
      intuition.
      inversion H0.
      unfold stuck in H1.
      intuition.
    - intros.
      apply IHmulti.
      pose proof (preservation x y T).
      intuition.
  Qed.

End uJuniperSoundness.

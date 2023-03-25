Set Warnings "-notation-overridden,-parsing,-require-in-module".
From Coq Require Export
     String
     List
     Nat (* For natural number comparision operators. *)
     Arith.PeanoNat. (* For some additional lemmas about natural numbers. *)
Import List.ListNotations.
Import PeanoNat.Nat.
From Coq Require Import Lia.

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

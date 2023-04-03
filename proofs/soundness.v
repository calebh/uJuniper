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
Require Import Coq.Program.Equality.

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
  - intuition.
    + right.
      destruct H1.
      eexists.
      econstructor 14.
      eauto.
    + right.
      destruct H0.
      pose proof (array_to_array T2 xs x0 H).
      destruct H0.
      subst.
      eexists.
      econstructor.
      trivial.
      eauto.
    + right.
      destruct H1.
      eexists.
      econstructor 14.
      eauto.
  - intuition.
    + right.
      eexists.
      econstructor 16.
      trivial.
    + right.
      destruct H0.
      eexists.
      econstructor.
      eauto.
  - right.
    destruct IHHt1; subst; eauto; destruct IHHt2; subst; eauto; destruct IHHt3; subst; eauto; destruct H; destruct H0; destruct H1; try solve_by_invert; eauto.
  - right.
    destruct IHHt1; subst; eauto; destruct IHHt2; subst; eauto; destruct IHHt3; subst; eauto; destruct H; destruct H0; destruct H1; try solve_by_invert; eauto.
  - right.
    destruct IHHt1; subst; eauto; destruct IHHt2; subst; eauto; destruct H; destruct H0; try solve_by_invert; eauto.
  - right.
    destruct IHHt1; subst; eauto; destruct IHHt2; subst; eauto; destruct H; destruct H0; try solve_by_invert; eauto.
  - right.
    destruct IHHt1; subst; eauto; destruct IHHt2; subst; eauto; destruct H; destruct H0; try solve_by_invert; eauto.
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
  intros.
  dependent induction H; simpl; eauto.
  - rename x0 into y. pose proof (String.string_dec x y). destruct H1; subst.
    + rewrite update_eq in H.
      injection H as H; subst.
      apply weakening_empty.
      rewrite eqb_refl; eauto.
    + generalize n; intro; apply eqb_neq in n; rewrite n.
      apply T_Var. rewrite update_neq in H; auto.
  - rename x0 into y.
    pose proof (Bool.bool_dec (String.eqb x y) (true)).
    destruct H1.
    + (* x=y *)
      rewrite e.
      apply T_Abs.
      rewrite eqb_eq in e.
      subst.
      rewrite update_shadow in H.
      assumption.
    + (* x<>y *)
      apply Bool.not_true_is_false in n.
      rewrite n.
      apply T_Abs.
      pose proof (IHhas_type (y |-> T2; Gamma) x U).
      apply H1.
      rewrite update_permute; auto.
      rewrite eqb_neq in n.
      assumption.
      assumption.
  Qed.    
  
  Lemma repeat_cons : forall (t : tm) m,
      exists xs, (repeat t (S m)) = t::xs.
  Proof.
    intros.
    eexists.
    instantiate (1:=repeat t m).
    simpl.
    reflexivity.
  Qed.

  Lemma repeat_tail : forall (t : tm) x m,
      repeat t (S m) = t :: x ->
      repeat t m = x.
  Proof.
    intros.
    simpl in H.
    injection H as H.
    assumption.
  Qed.

  Lemma array_con_size : forall T0 t0 m,
      empty |- t0 \in T0 ->
      empty |- <<tm_array_lit T0 (repeat t0 m)>> \in (T0 [m]).
  Proof.
    intros.
    induction m.
    - simpl.
      econstructor.
    - pose proof (repeat_cons t0 m).
      destruct H0.
      rewrite H0.
      econstructor.
      * eauto.
      * reflexivity.
      * pose proof (repeat_tail t0 x m H0).
        rewrite H1 in IHm.
        assumption.
  Qed.

  Lemma nth_preserves : forall T1 m (m0 : nat) arrlst dflt,
      empty |- dflt \in T1 ->
      empty |- (n m0) \in Nat ->
      empty |- <<tm_array_lit T1 arrlst>> \in (T1 [m]) ->
      empty |- <<nth m0 arrlst dflt>> \in T1.
  Proof.
    intros.
    generalize dependent m.
    generalize dependent arrlst.
    induction m0.
    - intros.
      destruct arrlst.
      simpl.
      assumption.
      inversion H1; subst.
      simpl.
      assumption.
    - intros.
      assert (empty |- (n m0) \in Nat).
      econstructor.
      intuition.
      destruct arrlst.
      simpl.
      assumption.
      simpl.
      destruct m.
      inversion H1.
      inversion H1; subst.
      eapply H3.
      eauto.
  Qed.

  Lemma set_nth_preserves : forall m0 val T1 arrlst m,
      empty |- val \in T1 ->
      empty |- <<tm_array_lit T1 arrlst>> \in (T1 [m]) ->
      empty |- <<tm_array_lit T1 (ListExtensions.set_nth m0 val arrlst)>> \in (T1 [m]).
  Proof.
    intros m0.
    induction m0.
    - intros.
      simpl.
      destruct arrlst.
      assumption.
      destruct m.
      inversion H0.
      econstructor.
      eauto.
      reflexivity.
      inversion H0; subst.
      assumption.
    - intros.
      destruct arrlst.
      simpl.
      assumption.
      destruct m.
      inversion H0.
      inversion H0; subst.
      econstructor.
      eauto.
      reflexivity.
      eapply IHm0.
      assumption.
      assumption.
  Qed.

  Lemma arrty_inversion : forall arrty arrlst T1 m,
      empty |- <<tm_array_lit arrty arrlst>> \in (T1 [m]) ->
      arrty = T1.
  Proof.
    intros.
    inversion H; subst.
    reflexivity.
    reflexivity.
  Qed.
  

  Lemma mapi_preserves_general : forall arrlst r T3 T1 m f,
      empty |- <<tm_array_lit T3 arrlst>> \in (T3 [m]) ->
      empty |- f \in (Nat -> T3 -> T1) ->
      empty |- <<tm_array_lit T1 (ListExtensions.mapi_helper r (fun (i : nat) (x : tm) => <{ f (n i) x }>) arrlst)>> \in (T1 [m]).
  Proof.
    intros arrlst.
    induction arrlst.
    - intros.
      inversion H; subst.
      simpl.
      econstructor.
    - intros.
      inversion H; subst.
      simpl.
      econstructor.
      econstructor.
      econstructor.
      eauto.
      econstructor.
      reflexivity.
      eauto.
      reflexivity.
      reflexivity.
      eapply IHarrlst.
      eauto.
      assumption.
  Qed.
    

  Lemma mapi_preserves : forall f m arrlst T3 T1,
      empty |- <<tm_array_lit T3 arrlst>> \in (T3 [m]) ->
      empty |- f \in (Nat -> T3 -> T1) ->
      empty |- <<tm_array_lit T1 (ListExtensions.mapi (fun (i : nat) (x : tm) => <{ f (n i) x }>) arrlst)>> \in (T1 [m]).
  Proof.
    intros.
    eapply mapi_preserves_general.
    eauto.
    assumption.
  Qed.


  (* ###################################################################### *)
  (** *** Preservation *)

  Theorem preservation : forall t t' T,
      empty |- t \in T  ->
                     t --> t'  ->
                     empty |- t' \in T.
  Proof.
    intros t t' T HT. generalize dependent t'.
    remember empty as Gamma.
    dependent induction HT.
    - intros.
      subst.
      inversion H.
    - intros.
      inversion H.
    - intros.
      subst.
      inversion H0; subst.
      inversion HT1; subst.
      * apply (substitution_preserves_typing empty x T3 t0 t2 T1).
        trivial.
        trivial.
      * econstructor.
        eapply IHHT1.
        trivial.
        trivial.
        eauto.
        reflexivity.
      * econstructor.
        eauto.
        apply IHHT2.
        trivial.
        trivial.
        reflexivity.
    - intros.
      inversion H.
    - intros.
      inversion H.
    - intros.
      inversion H0; subst.
      * trivial.
      * trivial.
      * econstructor.
        apply IHHT1.
        trivial.
        trivial.
        trivial.
        trivial.
        eauto.
        reflexivity.
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
    - intros.
      inversion H; subst.
    - intros.
      pose proof (array_to_array T1 (x::xs) t').
      intuition.
      destruct H4.
      subst.
      destruct x0.
      inversion H0.
      inversion H0; subst.
      * econstructor.
        eauto.
        reflexivity.
        eapply H3.
        assumption.
      * econstructor.
        eauto.
        reflexivity.
        inversion HT2; subst.
        econstructor.
        assumption.
    - intros.
      inversion H; subst.
      * econstructor.
        eapply IHHT.
        reflexivity.
        assumption.
      * pose proof (array_con_size T0 t0 m HT).
        assumption.
    - intros.
      inversion H0; subst.
      * econstructor.
        eapply IHHT1.
        reflexivity.
        assumption.
        assumption.
        eauto.
        reflexivity.
      * econstructor.
        eauto.
        eapply IHHT2.
        reflexivity.
        assumption.
        eauto.
        reflexivity.
      * econstructor.
        eauto.
        assumption.
        eapply IHHT3.
        reflexivity.
        assumption.
        reflexivity.
      * inversion HT1; subst.
        simpl.
        destruct m0.
        assumption.
        assumption.
        eapply nth_preserves.
        assumption.
        econstructor.
        eauto.
    - intros.
      inversion H0; subst.
      econstructor.
      eapply IHHT1.
      reflexivity.
      trivial.
      trivial.
      eauto.
      reflexivity.
      econstructor.
      assumption.
      eapply IHHT2.
      reflexivity.
      assumption.
      eauto.
      reflexivity.
      econstructor.
      assumption.
      assumption.
      eapply IHHT3.
      reflexivity.
      assumption.
      reflexivity.
      pose proof (arrty_inversion arrty arrlst T1 m HT1).
      subst.
      eapply set_nth_preserves.
      assumption.
      assumption.
  - intros.
    inversion H0; subst.
    econstructor.
    eapply IHHT1.
    reflexivity.
    assumption.
    eauto.
    reflexivity.
    econstructor.
    eauto.
    eapply IHHT2.
    reflexivity.
    assumption.
    reflexivity.
    pose proof (arrty_inversion arrty arrlst T3 m HT2).
    subst.
    eapply mapi_preserves.
    eauto.
    assumption.
  - intros.
    inversion H.
  - intros.
    inversion H; subst.
    econstructor.
    eapply IHHT1.
    reflexivity.
    assumption.
    assumption.
    econstructor.
    assumption.
    eapply IHHT2.
    reflexivity.
    assumption.
    pose proof (Bool.bool_dec (a0 =? b0) (true)).
    destruct H0.
    rewrite e.
    econstructor.
    rewrite not_true_iff_false in n.
    rewrite n.
    econstructor.
  - intros.
    inversion H; subst.
    econstructor.
    eapply IHHT1.
    reflexivity.
    assumption.
    assumption.
    econstructor.
    assumption.
    eapply IHHT2.
    reflexivity.
    assumption.
    pose proof (Bool.bool_dec (a0 <? b0) (true)).
    destruct H0.
    rewrite e.
    econstructor.
    rewrite not_true_iff_false in n.
    rewrite n.
    econstructor.
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

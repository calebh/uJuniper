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
Module uJuniperExamples.

  Definition junList (elem : ty) (capacity : nat) := <| Nat * (elem[capacity]) |>.
  Definition junStr (capacity : nat) := junList <| Nat |> (capacity + 1).
  
  Definition temp : string := "temp".
  Definition xLen : string := "xLen".
  Definition yLen : string := "yLen".
  Definition idx : string := "idx".
  Definition c : string := "c".
  Definition xArr : string := "xArr".
  Definition yArr : string := "yArr".
  Definition resArr : string := "resArr".

  Definition concatStr (capX : nat) (capY : nat) :=
    <{\ x : <<junStr capX>>, \y : <<junStr capY>>,
      let temp : <|Nat[<<capX + capY + 1>>]|> = <<tm_array_con (capX + capY + 1) <| Nat |> <{n 0}>>> in
      let xLen : <|Nat|> = fst x in
      let yLen : <|Nat|> = fst y in
      let xArr : <|Nat[<<capX + 1>>]|> = snd x in
      let yArr : <|Nat[<<capY + 1>>]|> = snd y in
      <
        (xLen + yLen) - n 1,
        <<tm_mapi
          <{
          (\idx : Nat, \c : Nat,
            if idx < (xLen - n 1) then
              <<tm_array_get xArr idx <{n 0}>>>
            else
              <<tm_array_get yArr <{(idx + n 1) - xLen}> <{n 0}>>>)
          }>
          <{ temp }>
          <| Nat |>
        >>
      >
      }>.
  
  Definition hello := <{<n 6, <<tm_array_lit <|Nat|> [<{n 72}>; <{n 101}>; <{n 108}>; <{n 108}>; <{n 111}>; <{n 0}>]>>>}>.
  Definition world := <{<n 7, <<tm_array_lit <|Nat|> [<{n 32}>; <{n 119}>; <{n 111}>; <{n 114}>; <{n 108}>; <{n 100}>; <{n 0}>]>>>}>.
  
  Definition hello_world := <{<n 12, <<tm_array_lit <|Nat|> [<{n 72}>; <{n 101}>; <{n 108}>; <{n 108}>; <{n 111}>; <{n 32}>; <{n 119}>; <{n 111}>; <{n 114}>; <{n 108}>; <{n 100}>; <{n 0}>]>>>}>.
  
  Theorem string_concat_type :
    forall capX capY,
    empty |- <<concatStr capX capY>> \in
    (<<junStr capX>> -> (<<junStr capY>> -> <<junStr (capX + capY)>>)).
  Proof.
    intros.
    unfold concatStr.
    unfold junStr.
    unfold junList.
    unfold letin.
    repeat econstructor.
  Qed.

  Theorem string_concat_example :
    <{<<concatStr 5 6>> <<hello>> <<world>>}> -->* hello_world.
  Proof.
    unfold concatStr.
    unfold letin.
    unfold junStr.
    unfold junList.
    simpl.
    unfold hello.
    unfold world.
    unfold hello_world.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    simpl.
    econstructor 3.
    econstructor.
    econstructor 16.
    econstructor.
    simpl.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    simpl.
    econstructor 3.
    econstructor.
    econstructor 10.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    simpl.
    econstructor.
    econstructor 3.
    econstructor.
    econstructor 10.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    simpl.
    econstructor.
    econstructor 3.
    econstructor.
    econstructor 12.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    simpl.
    econstructor.
    econstructor 3.
    econstructor.
    econstructor 12.
    econstructor.
    repeat econstructor.
    econstructor.
    econstructor.
    repeat econstructor.
    simpl.
    econstructor.
    econstructor.
    econstructor.
    econstructor 36.
    simpl.
    econstructor.
    econstructor.
    econstructor 39.
    simpl.
    econstructor.
    econstructor 8.
    econstructor.
    eapply ST_Mapi3.
    repeat econstructor.
    repeat econstructor.
    unfold ListExtensions.mapi.
    simpl.
    (* mapi evaluated *)
    econstructor.
    eapply ST_Pair2.
    econstructor.
    eapply ST_ArrayLit1.
    econstructor.
    econstructor.
    econstructor.
    simpl.
    econstructor.
    eapply ST_Pair2.
    econstructor.
    eapply ST_ArrayLit1.
    econstructor.
    econstructor.
    simpl.
    econstructor.
    eapply ST_Pair2.
    econstructor.
    eapply ST_ArrayLit1.
    econstructor.
    eapply ST_Nat_Leq2.
    econstructor.
    eapply ST_Nat_Sub3.
    simpl.
    econstructor.
    eapply ST_Pair2.
    econstructor.
    eapply ST_ArrayLit1.
    econstructor.
    eapply ST_Nat_Leq3.
    simpl.
    (* True branch *)
    econstructor.
    eapply ST_Pair2.
    econstructor.
    eapply ST_ArrayLit1.
    econstructor.
    econstructor.
    eapply ST_Pair2.
    econstructor.
    eapply ST_ArrayLit1.
    eapply ST_Array_Get4.
    repeat econstructor.
    econstructor.
    simpl.
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.

    eapply ST_ArrayLit1.
    econstructor.
    econstructor.
    econstructor.
    simpl.
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.
    eapply ST_ArrayLit1.
    econstructor.
    econstructor.
    simpl.
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.
    eapply ST_ArrayLit1.
    econstructor.
    eapply ST_Nat_Leq2.
    econstructor.
    eapply ST_Nat_Sub3.
    simpl.
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.
    eapply ST_ArrayLit1.
    econstructor.
    eapply ST_Nat_Leq3.
    simpl.
    (* True branch *)
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.
    eapply ST_ArrayLit1.
    econstructor.
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.
    eapply ST_ArrayLit1.
    eapply ST_Array_Get4.
    repeat econstructor.
    econstructor.
    simpl.
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.


    econstructor.
    econstructor.


    eapply ST_ArrayLit1.
    econstructor.
    econstructor.
    econstructor.
    simpl.
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply ST_ArrayLit1.
    econstructor.
    econstructor.
    simpl.
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply ST_ArrayLit1.
    econstructor.
    eapply ST_Nat_Leq2.
    econstructor.
    eapply ST_Nat_Sub3.
    simpl.
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply ST_ArrayLit1.
    econstructor.
    eapply ST_Nat_Leq3.
    simpl.
    (* True branch *)
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply ST_ArrayLit1.
    econstructor.
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply ST_ArrayLit1.
    eapply ST_Array_Get4.
    repeat econstructor.
    econstructor.
    simpl.
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.

    econstructor.
    econstructor.
    econstructor.
    econstructor.

    eapply ST_ArrayLit1.
    econstructor.
    econstructor.
    econstructor.
    simpl.
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply ST_ArrayLit1.
    econstructor.
    econstructor.
    simpl.
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply ST_ArrayLit1.
    econstructor.
    eapply ST_Nat_Leq2.
    econstructor.
    eapply ST_Nat_Sub3.
    simpl.
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply ST_ArrayLit1.
    econstructor.
    eapply ST_Nat_Leq3.
    simpl.
    (* True branch *)
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply ST_ArrayLit1.
    econstructor.
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply ST_ArrayLit1.
    eapply ST_Array_Get4.
    repeat econstructor.
    econstructor.
    simpl.
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.

    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.

    eapply ST_ArrayLit1.
    econstructor.
    econstructor.
    econstructor.
    simpl.
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply ST_ArrayLit1.
    econstructor.
    econstructor.
    simpl.
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply ST_ArrayLit1.
    econstructor.
    eapply ST_Nat_Leq2.
    econstructor.
    eapply ST_Nat_Sub3.
    simpl.
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply ST_ArrayLit1.
    econstructor.
    eapply ST_Nat_Leq3.
    simpl.
    (* True branch *)
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply ST_ArrayLit1.
    econstructor.
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply ST_ArrayLit1.
    eapply ST_Array_Get4.
    repeat econstructor.
    econstructor.
    simpl.
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.

    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.


    eapply ST_ArrayLit1.
    econstructor.
    econstructor.
    econstructor.
    simpl.
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply ST_ArrayLit1.
    econstructor.
    econstructor.
    simpl.
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply ST_ArrayLit1.
    econstructor.
    eapply ST_Nat_Leq2.
    econstructor.
    eapply ST_Nat_Sub3.
    simpl.
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply ST_ArrayLit1.
    econstructor.
    eapply ST_Nat_Leq3.
    simpl.
    (* False branch *)
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply ST_ArrayLit1.
    econstructor.
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply ST_ArrayLit1.
    eapply ST_Array_Get2.
    repeat econstructor.
    econstructor.
    eapply ST_Nat_Add3.
    simpl.
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply ST_ArrayLit1.
    eapply ST_Array_Get2.
    repeat econstructor.
    eapply ST_Nat_Sub3.
    simpl.
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply ST_ArrayLit1.
    eapply ST_Array_Get4.
    repeat econstructor.
    econstructor.
    simpl.
    econstructor.
    eapply ST_Pair2.
    econstructor.

    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.


    eapply ST_ArrayLit1.
    econstructor.
    econstructor.
    econstructor.
    simpl.
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply ST_ArrayLit1.
    econstructor.
    econstructor.
    simpl.
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply ST_ArrayLit1.
    econstructor.
    eapply ST_Nat_Leq2.
    econstructor.
    eapply ST_Nat_Sub3.
    simpl.
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply ST_ArrayLit1.
    econstructor.
    eapply ST_Nat_Leq3.
    simpl.
    (* False branch *)
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply ST_ArrayLit1.
    econstructor.
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply ST_ArrayLit1.
    eapply ST_Array_Get2.
    repeat econstructor.
    econstructor.
    eapply ST_Nat_Add3.
    simpl.
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply ST_ArrayLit1.
    eapply ST_Array_Get2.
    repeat econstructor.
    eapply ST_Nat_Sub3.
    simpl.
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply ST_ArrayLit1.
    eapply ST_Array_Get4.
    repeat econstructor.
    econstructor.
    simpl.
    econstructor.
    eapply ST_Pair2.
    econstructor.


    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.



    eapply ST_ArrayLit1.
    econstructor.
    econstructor.
    econstructor.
    simpl.
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply ST_ArrayLit1.
    econstructor.
    econstructor.
    simpl.
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply ST_ArrayLit1.
    econstructor.
    eapply ST_Nat_Leq2.
    econstructor.
    eapply ST_Nat_Sub3.
    simpl.
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply ST_ArrayLit1.
    econstructor.
    eapply ST_Nat_Leq3.
    simpl.
    (* False branch *)
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply ST_ArrayLit1.
    econstructor.
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply ST_ArrayLit1.
    eapply ST_Array_Get2.
    repeat econstructor.
    econstructor.
    eapply ST_Nat_Add3.
    simpl.
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply ST_ArrayLit1.
    eapply ST_Array_Get2.
    repeat econstructor.
    eapply ST_Nat_Sub3.
    simpl.
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply ST_ArrayLit1.
    eapply ST_Array_Get4.
    repeat econstructor.
    econstructor.
    simpl.
    econstructor.
    eapply ST_Pair2.
    econstructor.


    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.


    eapply ST_ArrayLit1.
    econstructor.
    econstructor.
    econstructor.
    simpl.
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply ST_ArrayLit1.
    econstructor.
    econstructor.
    simpl.
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply ST_ArrayLit1.
    econstructor.
    eapply ST_Nat_Leq2.
    econstructor.
    eapply ST_Nat_Sub3.
    simpl.
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply ST_ArrayLit1.
    econstructor.
    eapply ST_Nat_Leq3.
    simpl.
    (* False branch *)
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply ST_ArrayLit1.
    econstructor.
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply ST_ArrayLit1.
    eapply ST_Array_Get2.
    repeat econstructor.
    econstructor.
    eapply ST_Nat_Add3.
    simpl.
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply ST_ArrayLit1.
    eapply ST_Array_Get2.
    repeat econstructor.
    eapply ST_Nat_Sub3.
    simpl.
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply ST_ArrayLit1.
    eapply ST_Array_Get4.
    repeat econstructor.
    econstructor.
    simpl.
    econstructor.
    eapply ST_Pair2.
    econstructor.


    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.


    eapply ST_ArrayLit1.
    econstructor.
    econstructor.
    econstructor.
    simpl.
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply ST_ArrayLit1.
    econstructor.
    econstructor.
    simpl.
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply ST_ArrayLit1.
    econstructor.
    eapply ST_Nat_Leq2.
    econstructor.
    eapply ST_Nat_Sub3.
    simpl.
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply ST_ArrayLit1.
    econstructor.
    eapply ST_Nat_Leq3.
    simpl.
    (* False branch *)
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply ST_ArrayLit1.
    econstructor.
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply ST_ArrayLit1.
    eapply ST_Array_Get2.
    repeat econstructor.
    econstructor.
    eapply ST_Nat_Add3.
    simpl.
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply ST_ArrayLit1.
    eapply ST_Array_Get2.
    repeat econstructor.
    eapply ST_Nat_Sub3.
    simpl.
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply ST_ArrayLit1.
    eapply ST_Array_Get4.
    repeat econstructor.
    econstructor.
    simpl.
    econstructor.
    eapply ST_Pair2.
    econstructor.


    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.


    eapply ST_ArrayLit1.
    econstructor.
    econstructor.
    econstructor.
    simpl.
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply ST_ArrayLit1.
    econstructor.
    econstructor.
    simpl.
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply ST_ArrayLit1.
    econstructor.
    eapply ST_Nat_Leq2.
    econstructor.
    eapply ST_Nat_Sub3.
    simpl.
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply ST_ArrayLit1.
    econstructor.
    eapply ST_Nat_Leq3.
    simpl.
    (* False branch *)
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply ST_ArrayLit1.
    econstructor.
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply ST_ArrayLit1.
    eapply ST_Array_Get2.
    repeat econstructor.
    econstructor.
    eapply ST_Nat_Add3.
    simpl.
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply ST_ArrayLit1.
    eapply ST_Array_Get2.
    repeat econstructor.
    eapply ST_Nat_Sub3.
    simpl.
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply ST_ArrayLit1.
    eapply ST_Array_Get4.
    repeat econstructor.
    econstructor.
    simpl.
    econstructor.
    eapply ST_Pair2.
    econstructor.


    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.


    eapply ST_ArrayLit1.
    econstructor.
    econstructor.
    econstructor.
    simpl.
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply ST_ArrayLit1.
    econstructor.
    econstructor.
    simpl.
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply ST_ArrayLit1.
    econstructor.
    eapply ST_Nat_Leq2.
    econstructor.
    eapply ST_Nat_Sub3.
    simpl.
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply ST_ArrayLit1.
    econstructor.
    eapply ST_Nat_Leq3.
    simpl.
    (* False branch *)
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply ST_ArrayLit1.
    econstructor.
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply ST_ArrayLit1.
    eapply ST_Array_Get2.
    repeat econstructor.
    econstructor.
    eapply ST_Nat_Add3.
    simpl.
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply ST_ArrayLit1.
    eapply ST_Array_Get2.
    repeat econstructor.
    eapply ST_Nat_Sub3.
    simpl.
    econstructor.
    eapply ST_Pair2.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply ST_ArrayLit1.
    eapply ST_Array_Get4.
    repeat econstructor.
    econstructor.
    simpl.
    
    econstructor.
  Qed.

End uJuniperExamples.

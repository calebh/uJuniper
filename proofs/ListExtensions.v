Require Import Coq.Lists.List.
Import ListNotations.

Fixpoint set_nth {A : Type} (n : nat) (x : A) (l : list A) : list A :=
  match l with
  | [] => []
  | h :: t => match n with
              | 0 => x :: t
              | S m => h :: set_nth m x t
              end
  end.

Fixpoint mapi_helper {A B : Type} (i : nat) (f : nat -> A -> B) (l : list A) :=
  match l with
  | [] => []
  | x :: xs =>
    (f i x)::(mapi_helper (S i) f xs)
  end.

Definition mapi {A B : Type} (f : nat -> A -> B) (l : list A) : list B :=
  mapi_helper 0 f l.
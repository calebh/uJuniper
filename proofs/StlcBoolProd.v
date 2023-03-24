Set Warnings "-notation-overridden,-parsing,-require-in-module".
From PLF Require Import Smallstep.
From PLF Require Import Maps.
Require Import Coq.Lists.List.
Require Import ListExtensions.

  (* In BNF Notation, the syntax for the types of this language is:
     T := T -> T | bool | T * T

     and the syntax for the language itself is:

       t ::=
       | x                    (variable)
       | \x : T,t                 (abstraction)
       | t t                  (application)
       | true                 (constant true)
       | false                (constant false)
       | if t then t else t   (conditional)

       | (t,t)                (pair [tm_pair])
       | t.fst                (first projection [tm_fst])
       | t.snd                (second projection [tm_snd])

       (The only difference from the untyped version is the typing
       annotation on lambda abstractions. *)

  Inductive ty : Type :=
  | Ty_Arrow : ty -> ty -> ty
  | Ty_Bool  : ty
  | Ty_Prod : ty -> ty -> ty
  | Ty_Array : ty -> nat -> ty
  | Ty_Nat : ty.

  Inductive tm : Type :=
  | tm_let_in   : string -> tm -> tm -> tm
  | tm_var   : string -> tm
  | tm_array_lit : ty -> list tm -> tm
  | tm_array_con : nat -> ty -> tm -> tm
  | tm_nat_lit : nat -> tm
  | tm_array_get : tm -> tm -> tm -> tm
  | tm_array_set : tm -> tm -> tm -> tm
  | tm_mapi : tm -> tm -> tm
  | tm_app   : tm -> tm -> tm
  | tm_abs   : string -> ty -> tm -> tm
  | tm_true  : tm
  | tm_false  : tm
  | tm_ite  : tm -> tm -> tm -> tm
  | tm_fst : tm -> tm
  | tm_snd : tm -> tm
  | tm_pair : tm -> tm -> tm
  | tm_nat_eq : tm -> tm -> tm
  | tm_lt : tm -> tm -> tm.

Declare Custom Entry stlc.
Declare Custom Entry stlc_ty.

Notation "<< e >>" := e (e at level 99).
Notation "<{ e }>" := e (e custom stlc at level 99).
Notation "<| e |>" := e (e custom stlc_ty at level 99).
Notation "( x )" := x (in custom stlc, x at level 99).
Notation "( x )" := x (in custom stlc_ty, x at level 99).
Notation "x" := x (in custom stlc at level 0, x constr at level 0).
Notation "x" := x (in custom stlc_ty at level 0, x constr at level 0).
(*
Notation "'[' ']' 'con' m ty tm" :=
  (tm_array_con m ty tm) (in custom stlc at level 0,
                          ty custom stlc_ty at level 99).
Notation "'litarr' ty lst" :=
  (tm_array_lit ty lst) (in custom stlc at level 0,
                            ty custom stlc_ty at level 99,
                            lst at level 99).
*)
Notation "x y" := (tm_app x y) (in custom stlc at level 1, left associativity).
Notation "'if' x 'then' y 'else' z" :=
  (tm_ite x y z) (in custom stlc at level 89,
                    x custom stlc at level 99,
                    y custom stlc at level 99,
                    z custom stlc at level 99,
                    left associativity).
Notation "'true'"  := tm_true (in custom stlc at level 0).
Notation "'false'"  := tm_false (in custom stlc at level 0).
Notation "'fst' tm"  := (tm_fst tm) (in custom stlc at level 0).
Notation "'snd' tm"  := (tm_snd tm) (in custom stlc at level 0).
Notation "f '$' lst" := (tm_mapi f lst) (in custom stlc at level 0).
Notation "'<' tm1 ',' tm2 '>'" := (tm_pair tm1 tm2) (in custom stlc at level 0).
Notation "'set' arr '[' idx ']' '=' val" := (tm_array_set arr idx val) (in custom stlc at level 0).
Notation "'get' arr '[' idx ']' 'else' tm" := (tm_array_get arr idx tm) (in custom stlc at level 0).
Notation "lhs '==' rhs" := (tm_nat_eq lhs rhs) (in custom stlc at level 0).
Notation "lhs '<' rhs" := (tm_lt lhs rhs) (in custom stlc at level 0).
Notation "'n' num" := (tm_nat_lit num) (in custom stlc at level 0).
Notation "'let' x '=' val 'in' tm" := (tm_let_in x val tm) (in custom stlc at level 0).

Notation "\ x : t , y" :=
  (tm_abs x t y) (in custom stlc at level 90, x at level 99,
                     t custom stlc_ty at level 99,
                     y custom stlc at level 99,
                     left associativity).

Notation "S -> T" := (Ty_Arrow S T) (in custom stlc_ty at level 50, right associativity).
Notation "X * Y" :=
  (Ty_Prod X Y) (in custom stlc_ty at level 2, X custom stlc_ty, Y custom stlc_ty at level 0).
Notation "'Bool'" := Ty_Bool (in custom stlc_ty at level 0).
Notation "'Nat'" := Ty_Nat (in custom stlc_ty at level 0).
Notation "S '[' N ']'" :=
  (Ty_Array S N) (in custom stlc_ty at level 51, left associativity).

Coercion tm_var : string >-> tm.

Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".
Definition w : string := "w".
Definition t : string := "t".
Definition f : string := "f".
Definition s : string := "s".

Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".
Definition U : string := "U".
Definition V : string := "V".
Definition W : string := "W".

#[global] Hint Unfold x : core.
#[global] Hint Unfold y : core.
#[global] Hint Unfold z : core.
#[global] Hint Unfold w : core.
#[global] Hint Unfold s : core.

(* Here are lambda expressions for logical negation and swapping the
   elements of a pair *)
Definition notB : tm := <{\x : Bool, if x then false else true}>.
Definition swap : tm := <{\x : Bool * Bool, <snd x, fst x> }>.

(* Question 21 [and2B, or2B, not2B] (3 points):

   Write down expressions to calculate the bitwise and, bitwise or,
   and bitwise negation of a pair of booleans (i.e. a 2-bit vector).  *)

Definition andB : tm := <{\x : Bool, \y : Bool, if x then y else false}>.
Definition and2B : tm := <{\x : Bool * Bool, \y : Bool * Bool, <andB (fst x) (fst y), andB (snd x) (snd y)>}>.

Definition orB : tm := <{\x : Bool, \y : Bool, if x then true else y}>.
Definition or2B : tm := <{\x : Bool * Bool, \y : Bool * Bool, <orB (fst x) (fst y), orB (snd x) (snd y)>}>.

Definition not2B : tm := <{\x : Bool,  <notB (fst x), notB (snd x)>}>.


(* ================================================================= *)
(** ** Substitution *)

Reserved Notation "'[' x ':=' s ']' t" (in custom stlc at level 20, x constr).

(*
Definition eqb_string x y :=
  if string_dec x y then true else false.
*)

Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | tm_var y =>
    if String.eqb x y then s else t
  | <{\y: T , t1}> =>
      if String.eqb x y then t else <{\y:T, [x:=s] t1}>
  | <{t1 t2}> =>
    <{([x:=s] t1) ([x:=s] t2)}>
  | <{true}> => <{true}>
  | <{false}> => <{false}>
  | <{if t1 then t2 else t3}> =>
    <{if ([x:=s] t1) then ([x:=s] t2) else ([x:=s] t3)}>
  | <{fst t}> => <{fst ([x:=s] t)}>
  | <{snd t}> => <{snd ([x:=s] t)}>
  | <{< t1, t2> }> =>
      <{< [x:=s] t1 , [x:=s] t2>}>
  | <{let y = v in b}> =>
      if String.eqb x y then t else <{let y = [x:=s] v in [x:=s] b}>
  | tm_array_lit ty lst =>
      tm_array_lit ty (List.map (fun val => <{[x:=s] val}>) lst)
  | tm_array_con m ty tm =>
      tm_array_con m ty <{[x:=s]tm}>
  | <{ n num }> =>
      <{ n num }>
  | <{ get arr[idx] else tm }> =>
      <{ get ([x:=s] arr)[[x:=s] idx] else ([x:=s] tm) }>
  | <{ set arr [idx]= val }> =>
      <{ set ([x:=s] arr) [[x:=s] idx] = [x:=s]val }>
  | <{ f $ lst }> =>
      <{ ([x:=s] f) $ ([x:=s] lst) }>
  | <{ lhs == rhs }> =>
      <{ ([x:=s] lhs) == ([x:=s] rhs) }>
  | <{ lhs < rhs }> =>
      <{ ([x:=s] lhs) < ([x:=s] rhs) }>
  end

where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc).

(* ================================================================= *)
(** ** Reduction *)

Inductive value : tm -> Prop :=
  (* In pure STLC, function abstractions are values: *)
  | v_abs : forall x T2 t1,
      value <{\x:T2, t1}>
  (* Booleans are values: *)
  | v_true :
      value <{true}>
   | v_false :
      value <{false}>
   (* A pair is a value if both components are: *)
  | v_pair : forall v1 v2,
      value v1 ->
      value v2 ->
      value <{<v1, v2>}>
  (* An array is a value if it is a literal and all
     terms within the array are values *)
  | v_array_lit : forall ty lst,
      Forall value lst ->
      value (tm_array_lit ty lst)
  (* A natural number is a literal *)
  | v_nat_lit : forall x,
      value <{n x}>.

(** We'll be using the Call-By-Value semantics rules for the Lambda
    Calculus + Booleans + Pairs in this exercise. *)

Reserved Notation "t '-->' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  (* pure STLC *)
  | ST_AppAbs : forall x T2 t1 v2,
         value v2 ->
         <{(\x:T2, t1) v2}> --> <{ [x:=v2]t1 }>
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         <{t1 t2}> --> <{t1' t2}>
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         <{v1 t2}> --> <{v1  t2'}>
  (* booleans  *)
  | ST_IfTrue : forall t1 t2,
      <{if true then t1 else t2}> --> t1
  | ST_IfFalse : forall t1 t2,
      <{if false then t1 else t2}> --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      <{if t1 then t2 else t3}> --> <{if t1' then t2 else t3}>
  (* pairs *)

  | ST_Pair1 : forall t1 t1' t2,
        t1 --> t1' ->
        <{ <t1,t2> }> --> <{ <t1' , t2> }>
  | ST_Pair2 : forall v1 t2 t2',
        value v1 ->
        t2 --> t2' ->
        <{ <v1, t2> }> -->  <{ <v1, t2'> }>
  | ST_Fst1 : forall t0 t0',
        t0 --> t0' ->
        <{ fst t0 }> --> <{ fst t0' }>
  | ST_FstPair : forall v1 v2,
        value v1 ->
        value v2 ->
        <{ fst <v1,v2> }> --> v1
  | ST_Snd1 : forall t0 t0',
        t0 --> t0' ->
        <{ snd t0 }> --> <{ snd t0' }>
  | ST_SndPair : forall v1 v2,
        value v1 ->
        value v2 ->
        <{ snd <v1,v2> }> --> v2
  | ST_ArrayLit1 : forall ty x x' xs,
        x --> x' ->
        (tm_array_lit ty (cons x xs)) --> (tm_array_lit ty (cons x' xs))
  | ST_ArrayLit2 : forall ty x xs xs',
        value x ->
        (tm_array_lit ty xs) --> (tm_array_lit ty xs') ->
        (tm_array_lit ty (cons x xs)) --> (tm_array_lit ty (cons x xs'))
  | ST_ArrayCon1 : forall m ty t0 t0',
        t0 --> t0' ->
        (tm_array_con m ty t0) --> (tm_array_con m ty t0')
  | ST_ArrayCon2 : forall m ty t,
        value t ->
        (tm_array_con m ty t) --> (tm_array_lit ty (repeat t m))
  | ST_Array_Get1 : forall arr arr' idx dflt,
        arr --> arr' ->
        <{get arr[idx] else dflt}> --> <{get arr'[idx] else dflt}>
  | ST_Array_Get2 : forall arr idx idx' dflt,
        value arr ->
        idx --> idx' ->
        <{get arr[idx] else dflt}> --> <{get arr[idx'] else dflt}>
  | ST_Array_Get3 : forall arr idx dflt dflt',
        value arr ->
        value idx ->
        dflt --> dflt' ->
        <{get arr[idx] else dflt}> --> <{get arr[idx] else dflt'}>
  | ST_Array_Get4 : forall arrty arrlst m dflt,
        value (tm_array_lit arrty arrlst) ->
        value dflt ->
        <{get <<tm_array_lit arrty arrlst>>[n m] else dflt}> --> (List.nth m arrlst dflt)
  | ST_Array_Set1 : forall arr arr' idx val,
        arr --> arr' ->
        <{set arr[idx] = val}> --> <{set arr'[idx] = val}>
  | ST_Array_Set2 : forall arr idx idx' val,
        value arr ->
        idx --> idx' ->
        <{set arr[idx] = val}> --> <{set arr[idx'] = val}>
  | ST_Array_Set3 : forall arr idx val val',
        value arr ->
        value idx ->
        <{set arr[idx] = val}> --> <{set arr[idx] = val'}>
  | ST_Array_Set4 : forall arrty arrlst m val,
        value (tm_array_lit arrty arrlst) ->
        value val ->
        <{set <<tm_array_lit arrty arrlst>>[n m] = val}> --> (tm_array_lit arrty (set_nth m val arrlst))
  | ST_Mapi1 : forall f f' lst,
        f --> f' ->
        <{ f $ lst }> --> <{ f' $ lst }>
  | ST_Mapi2 : forall f lst lst',
        value f ->
        lst --> lst' ->
        <{ f $ lst }> --> <{ f $ lst' }>
  | ST_Mapi3 : forall f arrty arrlst,
        value f ->
        value (tm_array_lit arrty arrlst) ->
        <{ f $ <<(tm_array_lit arrty arrlst)>> }> --> tm_array_lit arrty (mapi (fun i x => <{f (n <<i>>) <<x>>}>) arrlst)

  where "t '-->' t'" := (step t t').


#[global] Hint Constructors step : core.

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Definition context := partial_map ty.

Set Warnings "-notation-overridden,-parsing,-require-in-module".
From PLF Require Import Smallstep.
From PLF Require Import Maps.
Require Import Coq.Lists.List.
Require Import ListExtensions.

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
Definition orB : tm := <{\x : Bool, \y : Bool, if x then true else y}>.
Definition ltEq : tm := <{\x : Nat, \y : Nat, <<orB>> (x == y) (x < y)}>.
Definition gt : tm := <{\x : Nat, \y : Nat, <<notB>> (<<ltEq>> x y) }>.
Definition gtEq : tm := <{\x : Nat, \y : Nat, <<notB>> (x < y)}>.

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
  (*| v_array_lit_rec : forall ty xs,
      Forall value xs ->
      value (tm_array_lit ty xs)*)
  | v_arrray_lit_base : forall ty,
      value (tm_array_lit ty List.nil)
  | v_array_lit_rec : forall ty x xs,
      value x ->
      value (tm_array_lit ty xs) ->
      value (tm_array_lit ty (List.cons x xs))
  (* A natural number is a literal *)
  | v_nat_lit : forall x,
      value <{n x}>.


Fixpoint value_helper (t : tm) : bool :=
  match t with
  | <{\x:T2, t1}> =>
      true
  | <{true}> =>
      true
  | <{false}> =>
      true
  | <{<v1,v2>}> =>
      (value_helper v1) && (value_helper v2)
  | tm_array_lit ty xs =>
      List.forallb value_helper xs
  | <{n x}> =>
      true
  | _ =>
      false
  end.

(*
Inductive value : tm -> Prop :=
  | value_con : forall tm,
      value_helper tm = true ->
      value tm.
*)

(** We'll be using the Call-By-Value semantics rules for the Lambda
    Calculus + Booleans + Pairs in this exercise. *)

Reserved Notation "t '-->' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  (* Pure STLC *)
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
  
  (* Booleans  *)
  | ST_IfTrue : forall t1 t2,
      <{if true then t1 else t2}> --> t1
  | ST_IfFalse : forall t1 t2,
      <{if false then t1 else t2}> --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      <{if t1 then t2 else t3}> --> <{if t1' then t2 else t3}>
  
  (* Pairs *)
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

  (* Arrays *)
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
  
  (* Nats *)
  | ST_Nat_Eq1 : forall lhs lhs' rhs,
        lhs --> lhs' ->
        <{ lhs == rhs }> --> <{ lhs' == rhs }>
  | ST_Nat_Eq2 : forall lhs rhs rhs',
        value lhs ->
        rhs --> rhs' ->
        <{ lhs == rhs }> --> <{ lhs == rhs' }>
  | ST_Nat_Eq3 : forall a b,
        <{ n a == n b }> --> (if Nat.eqb a b then <{true}> else <{false}>)
  | ST_Nat_Leq1 : forall lhs lhs' rhs,
        lhs --> lhs' ->
        <{ lhs < rhs }> --> <{ lhs' < rhs }>
  | ST_Nat_Leq2 : forall lhs rhs rhs',
        value lhs ->
        rhs --> rhs' ->
        <{ lhs < rhs }> --> <{ lhs < rhs' }>
  | ST_Nat_Leq3 : forall a b,
        <{ n a < n b }> --> (if Nat.ltb a b then <{true}> else <{false}>)
  
  (* Let expressions *)
  | ST_Let_In1 : forall varname bound bound' body,
        bound --> bound' ->
        <{ let varname = bound in body }> --> <{ let varname = bound' in body}>
  | ST_Let_In2 : forall varname bound body,
        value bound ->
        <{ let varname = bound in body }> --> <{ [varname:=bound] body }>
  

  where "t '-->' t'" := (step t t').

#[global] Hint Constructors step : core.

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Definition context := partial_map ty.

Reserved Notation "Gamma '|-' t '\in' T" (at level 40, t custom stlc, T custom stlc_ty at level 0).

Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var :
    forall Gamma x T1,
    Gamma x = Some T1 ->
    Gamma |- x \in T1
  | T_Abs :
    forall Gamma x t1 T1 T2,
    (x |-> T2; Gamma) |- t1 \in T1 ->
    Gamma |- <{\x:T2, t1}> \in (T2 -> T1)
  | T_App :
    forall Gamma t1 t2 T1 T2 T3,
    Gamma |- t1 \in (T2 -> T1) ->
    Gamma |- t2 \in T3 ->
    T2 = T3 ->
    Gamma |- <{t1 t2}> \in T1
  | T_True :
    forall Gamma,
    Gamma |- <{true}> \in Bool
  | T_False :
    forall Gamma,
    Gamma |- <{false}> \in Bool
  | T_If :
    forall Gamma t1 t2 t3 T1 T2,
    Gamma |- t1 \in Bool ->
    Gamma |- t2 \in T1 ->
    Gamma |- t3 \in T2 ->
    T1 = T2 ->
    Gamma |- <{if t1 then t2 else t3}> \in T1
  | T_Pair :
    forall Gamma t1 t2 T1 T2,
    Gamma |- t1 \in T1 ->
    Gamma |- t2 \in T2 ->
    Gamma |- <{<t1, t2>}> \in (T1*T2)
  | T_Fst :
    forall Gamma t0 T1 T2,
    Gamma |- t0 \in (T1*T2) ->
    Gamma |- <{fst t0}> \in T1
  | T_Snd :
    forall Gamma t0 T1 T2,
    Gamma |- t0 \in (T1*T2) ->
    Gamma |- <{snd t0}> \in T2
  | T_Array_Lit :
    forall Gamma lst T1,
    Forall (fun tm => exists T2, T1 = T2 /\ has_type Gamma tm T2) lst ->
    Gamma |- <<(tm_array_lit T1 lst)>> \in <<(Ty_Array T1 (length lst))>>
  | T_Array_Con :
    forall Gamma m T0 t0,
    Gamma |- t0 \in T0 ->
    Gamma |- <<(tm_array_con m T0 t0)>> \in <<(Ty_Array T0 m)>>
  | T_Array_Get :
    forall Gamma arr idx dflt T0 T1 m,
    Gamma |- arr \in <<(Ty_Array T0 m)>> ->
    Gamma |- idx \in Nat ->
    Gamma |- dflt \in T1 ->
    T0 = T1 ->
    Gamma |- get arr[idx] else dflt \in T0
  | T_Array_Set :
    forall Gamma arr idx val T0 T1 m,
    Gamma |- arr \in <<(Ty_Array T0 m)>> ->
    Gamma |- idx \in Nat ->
    Gamma |- val \in T1 ->
    T0 = T1 ->
    Gamma |- set arr[idx] = val \in <<(Ty_Array T0 m)>>
  | T_Mapi :
    forall Gamma f lst m T0 T1 T3,
    Gamma |- f \in (Nat -> T0 -> T1) ->
    Gamma |- lst \in <<(Ty_Array T3 m)>> ->
    T0 = T3 ->
    Gamma |- f $ lst \in <<(Ty_Array T1 m)>>
  | T_Nat_Lit :
    forall Gamma m,
    Gamma |- n m \in Nat
  | T_Nat_Eq :
    forall Gamma a b,
    Gamma |- a \in Nat ->
    Gamma |- b \in Nat ->
    Gamma |- a == b \in Bool
  | T_Nat_Lt :
    forall Gamma a b,
    Gamma |- a \in Nat ->
    Gamma |- b \in Nat ->
    Gamma |- a < b \in Bool
  | T_Let_In :
    forall Gamma varname bound body T0 T1,
    Gamma |- bound \in T0 ->
    (varname |-> T0; Gamma) |- body \in T1 ->
    Gamma |- let varname = bound in body \in T1

  where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

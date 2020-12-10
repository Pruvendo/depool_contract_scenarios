Require Import Coq.Program.Basics.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Combinators.
Require Import ZArith.
Require Import Strings.String.

Require Import FinProof.Common.
Require Import FinProof.CommonInstances.
Require Import FinProof.StateMonad2.
Require Import FinProof.StateMonadInstances.
Require Import FinProof.ProgrammingWith.

Require Import depoolContract.SolidityNotations.
Require Import Lists.List.
Import ListNotations.
Local Open Scope list_scope.

Definition toErrorProp {E X} (l: list (X -> (Prop*E))) (x: X) (e:E):=
let fix f l x := match l with
| nil => [ ]
| p::ls => let p' := f ls x in
            ((fst (p x))::(hd (@nil Prop) p'))::p'
end  in
let l' := List.map (fun t => (hd True t) :: (List.map (fun (p:Prop) => ~p) (tl t))) (f l x) in
let l'':= List.map (fun t => match t with
                             | [ ] => True
                             | x::xs => fold_left and xs x
                             end) l'  in
let l''' :=  l'' in
let fix g m l := 
match m, l with 
| xm::ms, xl::ls => (xm /\ e = (snd xl)) :: (g ms ls)
| _, _ => [ ]
end in let l'''' := g l''' (List.map (fun p => p x) l) in
let l''''':= match l'''' with
| [ ] => False
| x::xs => fold_left or xs x
end in l'''''.

Definition toValueProp {X E} (l: list (X -> (Prop*E))) (x: X):=
let l' := List.map (fun p => ~ (fst (p x))) l in
match l' with
     | [ ] => True
     | x::xs => fold_left and xs x
end.


Definition toErrorList {E X} (l: list (X -> (Prop*E))) (x: X) :=
map (fun f => (snd (f x))) l.

Notation "$0"  := (prod_curry)       (at level 60, right associativity). 
Notation "$1"  := (prod_curry ∘ $0)  (at level 60, right associativity).
Notation "$2"  := (prod_curry ∘ $1)  (at level 60, right associativity).
Notation "$3"  := (prod_curry ∘ $2)  (at level 60, right associativity).
Notation "$4"  := (prod_curry ∘ $3)  (at level 60, right associativity).
Notation "$5"  := (prod_curry ∘ $4)  (at level 60, right associativity).
Notation "$6"  := (prod_curry ∘ $5)  (at level 60, right associativity).
Notation "$7"  := (prod_curry ∘ $6)  (at level 60, right associativity).

Notation "#0"  := (prod_uncurry)       (at level 60, right associativity). 
Notation "#1"  := ( prod_uncurry ∘ #0 )  (at level 60, right associativity).
Notation "#2"  := ( prod_uncurry ∘ #1 )  (at level 60, right associativity).
Notation "#3"  := ( prod_uncurry ∘ #2 )  (at level 60, right associativity).
Notation "#4"  := ( prod_uncurry ∘ #3 )  (at level 60, right associativity).
Notation "#5"  := ( prod_uncurry ∘ #4 )  (at level 60, right associativity).
Notation "#6"  := ( prod_uncurry ∘ #5 )  (at level 60, right associativity).
Notation "#7"  := ( prod_uncurry ∘ #6 )  (at level 60, right associativity).

Module XTypesSig <: SolidityNotations.XTypesSig.
Definition XBool := bool.
Definition XInteger := Z.

(*Definition XInteger256 := Z.*)
Definition XString := string. 
Definition XMaybe := option.
Definition XList := list.
Definition XProd := prod.
Definition XHMap := listPair.
Definition XErrorValue := ErrorValue.

(*xInt2 xInt3 xInt20 xInt30 xInt50 xInt128 xInt255 xInt86400*)

(* Definition xInt0 := 0%Z.
Definition xInt1 := 1%Z.
Definition xInt2 := 2%Z.
Definition xInt3 := 3%Z.
Definition xInt20 := 20%Z.
Definition xInt30 := 30%Z.
Definition xInt50 := 50%Z.
Definition xInt128 := 128%Z.
Definition xInt255 := 255%Z.
Definition xInt86400 := 86400%Z.


Definition xInt100 := 100%Z.
Definition xInt101 := 101%Z.
Definition xInt102 := 102%Z.
Definition xInt103 := 103%Z.
Definition xInt104 := 104%Z.
Definition xInt105 := 105%Z.
Definition xInt106 := 106%Z.
Definition xInt107 := 107%Z.
Definition xInt108 := 108%Z.
Definition xInt109 := 109%Z.
Definition xInt110 := 110%Z.
Definition xInt111 := 111%Z.
Definition xInt112 := 112%Z.
Definition xInt113 := 113%Z.
Definition xInt114 := 114%Z.
Definition xInt115 := 115%Z.
Definition xInt116 := 116%Z.
Definition xInt117 := 117%Z.
Definition xInt118 := 118%Z.
Definition xInt119 := 119%Z.
Definition xInt120 := 120%Z.
Definition xInt121 := 121%Z.
Definition xInt122 := 122%Z.

Definition xInt5 := 5%Z.
Definition xInt4 := 4%Z.
Definition xInt6 := 6%Z.
Definition xInt7 := 7%Z.
Definition xInt8 := 8%Z.
Definition xInt11 := 11%Z.
Definition xInt32 := 32%Z.
Definition xInt33 := 33%Z.
Definition xInt40 := 40%Z.
Definition xInt64 := 64%Z.
Definition xInt84 := 84%Z.
Definition xInt125 := 125%Z.
Definition xInt129 := 129%Z.
Definition xInt254 := 254%Z.
Definition xInt256 := 256%Z.
Definition xInt512 := 512%Z.
Definition xInt1000 := 1000%Z.
Definition xInt1024 := 1024%Z.
Definition xInt8192 := 8192%Z. *)

Definition xInt1000000000 := 1000000000%Z.
Definition xInt10000000000 := 10000000000%Z.
Definition xInt104 := 104%Z.
Definition xInt100000000000 := 100000000000%Z.
Definition xInt103 := 103%Z.
Definition xInt4 := 4%Z.
Definition xInt18 := 18%Z.
Definition xInt2 := 2%Z.
Definition xInt100 := 100%Z.
Definition xInt64 := 64%Z.
Definition xInt102 := 102%Z.
Definition xInt101 := 101%Z.
Definition xInt1 := 1%Z.
Definition xInt17 := 17%Z.
Definition xInt15 := 15%Z.
Definition xInt32 := 32%Z.
Definition xInt34 := 34%Z.
Definition xInt0 := 0%Z.
Definition xInt65536 := 65536%Z.
Definition xInt3 := 3%Z.
Definition xInt1_000_000_000 := 1000000000%Z.
Definition xInt228_000_000 := 228000000%Z.
Definition Ox4444444444444444444444444444444444444444444444444444444444444444 := 30877890463284318779618929335650108760871995910837483743855355735443501237316%Z.
Definition xInt8 := 8%Z.
Definition x1_ton := 1000000000%Z.
Definition xInt1E9 := 1000000000%Z.
Definition xInt5 := 5%Z.
Definition xInt6 := 6%Z.
Definition xInt7 := 7%Z. 
Definition xInt9 := 9%Z. 
(* Definition x365_days := (365*24*60*60)%Z. *)
Definition xInt365 := 365%Z.
Definition x1_day := 86400%Z. 




(* Definition xInt10000000 := 10000000%Z.  *)
(* Definition xIntFFFF := 65535%Z.
Definition xIntFFFFFFFF := 4294967295%Z. *)

(* Definition xInt4294967295 := 4294967295%Z. *)

Definition bfr := boolFunRec.
Definition pfr := prodFunRec.
Definition mfr := maybeFunRec.
Definition ifr := intFunRec.
Definition lfr := listFunRec.
Definition sfr := strFunRec.
Definition hmfr:= hmapFunRec.
Definition evfr:= errorFunRec. 
End XTypesSig.


(* Module Type A.

Set Universe Polymorphism.
Set Printing Universes.
Unset Cumulativity Weak Constraints.


Section UniSection.
Polymorphic Universes i j k.
Polymorphic Constraint i <= simpleState.u0.
Polymorphic Constraint j <= simpleState.u1.
Polymorphic Constraint i <= k.
Polymorphic Constraint j <= k. 

Polymorphic Axiom StateT: Type@{i} -> Type@{j} -> Type@{k}.

End UniSection.

(*Module*) Monomorphic Axiom monadStateT: forall S, Monad (StateT S).
Existing Instance monadStateT.
(*Module*) Monomorphic Axiom monadStateStateT : forall S, MonadState (M:=StateT S) S.
End A.  *)

Module StateMonadSig <: SolidityNotations.StateMonadSig. 

(* Polymorphic Definition StateT (S X: Type): Type.
 refine (simpleState S X).
 Defined. *)


 Definition StateT := simpleState.

(* 
 Check simpleStateMonad. *)

 Definition monadStateT := simpleStateMonad.

(*  Polymorphic Definition monadStateT : forall S, Monad (StateT S).
 refine (simpleStateMonad).
 Defined. *)

 Definition monadStateStateT := simpleStateMonadState.
(* 
 Polymorphic Definition monadStateStateT := simpleStateMonadState. *)

End StateMonadSig.

(* Module B (xt: XTypesSig) (sm: StateMonadSig).
(* Module LedgerClass := LedgerClass xt sm .
Import LedgerClass.
Import SolidityNotations. *)
(* 
Module Type DePoolSpecSig.
Import xt. Import sm. *)

End B.

Module B' := B XTypesSig StateMonadSig. *)


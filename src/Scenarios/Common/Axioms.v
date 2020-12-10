Require Import Coq.Program.Basics.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Combinators.
Require Import omega.Omega.
Require Import Setoid.
Require Import ZArith.

Require Import FinProof.Common.
Require Import FinProof.CommonInstances.
Require Import FinProof.StateMonad2.
Require Import FinProof.StateMonadInstances.
Require Import FinProof.ProgrammingWith. 

Local Open Scope struct_scope.

Require Import FinProof.CommonProofs.
Require Import depoolContract.ProofEnvironment.
Require Import depoolContract.DePoolClass.
Require Import depoolContract.SolidityNotations.

Require Import depoolContract.DePoolFunc.
Module DePoolFuncs := DePoolFuncs XTypesSig StateMonadSig.
Import DePoolFuncs.
Import DePoolSpec.
Import LedgerClass.


Require Import depoolContract.Lib.CommonModelProofs.
Module CommonModelProofs := CommonModelProofs StateMonadSig.
Import CommonModelProofs. 
Require Import depoolContract.Lib.Tactics.
Require Import depoolContract.Lib.ErrorValueProofs.
(*Require Import depoolContract.Lib.CommonCommon.*)
(* Require Import depoolContract.Lib.tvmFunctionsProofs. *)

Import DePoolSpec.LedgerClass.SolidityNotations. 

Local Open Scope struct_scope.
Local Open Scope Z_scope.
Local Open Scope solidity_scope.
Require Import Lists.List.
Import ListNotations.
Local Open Scope list_scope.

Set Typeclasses Iterative Deepening.
Set Typeclasses Depth 100.

Require Export depoolContract.Scenarios.Common.CommonDefinitions.

Axiom prevCurValidator : forall l , prevValidator l <> currentValidator l.

Axiom validatorsNeverSame : forall l1 l2 l3,
    now l1 < now l2 -> 
    now l2 < now l3 ->
    currentValidator l2 <> currentValidator l3 ->
    currentValidator l1 <> currentValidator l3.

Axiom validatorsMonotonic : forall l1 l2,
    prevValidator l2 = currentValidator l1 ->
    now l1 < now l2.

Axiom unfreezeLessMax : forall l,
    validationStart l + currentValidator l < MAX_INT l.

Axiom nowLessMax : forall l,
    now l < MAX_INT l.

Axiom unfreezeLagLessNow : forall l,
    ELECTOR_UNFREEZE_LAG l < now l.
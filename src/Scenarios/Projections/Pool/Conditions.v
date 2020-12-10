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

Require Export depoolContract.Scenarios.Projections.Pool.States.
Require Export depoolContract.Scenarios.Common.RotateRoundsCondition.

Section Pool_conditions.

Variable terminatorCalled : Prop.
Variable ticktockCalled : Prop.
Variable constructorCalled : Prop.

Definition projection_pool_terminate_condition (l : Ledger) : Prop :=
    ownerOrSelfCall l /\
    projection_pool_state_isClosed (getProjection_Pool_State l) = false /\
    terminatorCalled.

Definition projection_pool_terminate_move (ol nl : Ledger) : Prop :=
    let op := getProjection_Pool_State ol in
    let np := getProjection_Pool_State nl in
    projection_pool_terminate_condition ol  /\
    projection_pool_state_isClosed np = true /\
    projection_pull_state_getPre0_index np = projection_pull_state_getPre0_index op /\
    projection_pull_state_getRound0_index np = projection_pull_state_getRound0_index op /\
    projection_pull_state_getRound1_index np = projection_pull_state_getRound1_index op /\
    projection_pull_state_getRound2_index np = projection_pull_state_getRound2_index op.

Definition projection_pool_constructor_condition (l : Ledger) := constructorCalled.

Definition projection_pool_constructor_move (ol nl : Ledger) : Prop :=
    let np := getProjection_Pool_State nl in
    projection_pool_constructor_condition nl /\
    projection_pool_state_isClosed np = true /\
    projection_pull_state_getPre0_index np = 3 /\
    projection_pull_state_getRound0_index np = 2 /\
    projection_pull_state_getRound1_index np = 1 /\
    projection_pull_state_getRound2_index np = 0.

Definition projection_pool_destructor_condition (l : Ledger) :=
    updateRoundsCalled l ticktockCalled /\
    isEmptyRound (roundPre0 l) /\
    isEmptyRound (round0 l) /\
    isEmptyRound (round1 l) /\
    isEmptyRound (round2 l).

Definition projections_pool_rotate_rounds_condition (l : Ledger) : Prop :=
    rotate_round_conditions_full l ticktockCalled.

Definition projection_pool_rotate_rounds_move (ol nl : Ledger) : Prop :=
    let op := getProjection_Pool_State ol in
    let np := getProjection_Pool_State nl in
    projections_pool_rotate_rounds_condition ol  /\
    projection_pool_state_isClosed np = projection_pool_state_isClosed op /\
    projection_pull_state_getPre0_index np = projection_pull_state_getPre0_index op + 1 /\
    projection_pull_state_getRound0_index np = projection_pull_state_getPre0_index op /\
    projection_pull_state_getRound1_index np = projection_pull_state_getRound0_index op /\
    projection_pull_state_getRound2_index np = projection_pull_state_getRound1_index op.

End Pool_conditions.

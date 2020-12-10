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
Require Export depoolContract.Scenarios.Common.CommonDefinitions.

Import DePoolSpec.LedgerClass.SolidityNotations. 

Local Open Scope struct_scope.
Local Open Scope Z_scope.
Local Open Scope solidity_scope.
Require Import Lists.List.
Import ListNotations.
Local Open Scope list_scope.

Set Typeclasses Iterative Deepening.
Set Typeclasses Depth 100.

Inductive Projection_Round_Stakes_State :=
| _Projection_Round_Stakes_State :
    Z (*stake*) ->
    Z (*recoveredStake*) ->
    Z (*unused*) ->
    bool (*isValidatorStakeCompleted*) ->
    Z (*rewards*) ->
    Z (*validatorStake*) ->
    Z (*handledStakesAndRewards*) ->
    Projection_Round_Stakes_State.

Definition getProjectionRoundStakesState (r : RoundsBase_ι_Round) :=
    _Projection_Round_Stakes_State
    (RoundsBase_ι_Round_ι_stake r)
    (RoundsBase_ι_Round_ι_recoveredStake r)
    (RoundsBase_ι_Round_ι_unused r)
    (RoundsBase_ι_Round_ι_isValidatorStakeCompleted r)
    (RoundsBase_ι_Round_ι_rewards r)
    (RoundsBase_ι_Round_ι_validatorStake r)
    (RoundsBase_ι_Round_ι_handledStakesAndRewards r).

Definition projection_round_stakes_getStake (prc : Projection_Round_Stakes_State) :=
    match prc with
    | _Projection_Round_Stakes_State x _ _ _ _ _ _ => x
    end.

Definition projection_round_stakes_getRecoveredStake (prc : Projection_Round_Stakes_State) :=
    match prc with
    | _Projection_Round_Stakes_State _ x _ _ _ _ _ => x
    end.

Definition projection_round_stakes_getUnused (prc : Projection_Round_Stakes_State) :=
    match prc with
    | _Projection_Round_Stakes_State _ _ x _ _ _ _ => x
    end.

Definition projection_round_stakes_getIsValidatorStakeCompleted (prc : Projection_Round_Stakes_State) :=
    match prc with
    | _Projection_Round_Stakes_State _ _ _ x _ _ _ => x
    end.

Definition projection_round_stakes_getRewards (prc : Projection_Round_Stakes_State) :=
    match prc with
    | _Projection_Round_Stakes_State _ _ _ _ x _ _ => x
    end.

Definition projection_round_stakes_getValidatorStake (prc : Projection_Round_Stakes_State) :=
    match prc with
    | _Projection_Round_Stakes_State _ _ _ _ _ x _ => x
    end.

Definition projection_round_stakes_getHandledStakesAndRewards (prc : Projection_Round_Stakes_State) :=
    match prc with
    | _Projection_Round_Stakes_State _ _ _ _ _ _ x => x
    end.

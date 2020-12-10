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

Require Export depoolContract.Scenarios.Projections.Round_Pool.States.
Require Export depoolContract.Scenarios.Common.RotateRoundsCondition.

Section Round_Pool_conditions.

Variable ticktockCalled : Prop.
Variable constructorCalled : Prop.
Variable terminatorCalled : Prop.

Definition generateRoundCalled (l : Ledger) :=
    constructorCalled \/ rotate_round_conditions_full l ticktockCalled.

Definition projection_round_pool_constructor_condition
(l : Ledger) (r : RoundsBase_ι_Round) :=
    generateRoundCalled l.

Definition projection_round_pool_constructor_move
(ol nl : Ledger) (or nr : RoundsBase_ι_Round) :=
    roundIn nl nr /\
    ~ roundIn ol nr /\
    projection_round_pool_constructor_condition ol or /\
    getProjectionRoundPoolState nl nr = Projection_Round_Pool_State_Pre0.

Definition projection_round_pool_constructor_0_condition
(l : Ledger) (r : RoundsBase_ι_Round) :=
    constructorCalled.

Definition projection_round_pool_constructor_0_move
(ol nl : Ledger) (or nr : RoundsBase_ι_Round) :=
    roundIn nl nr /\
    ~ roundIn ol nr /\
    projection_round_pool_constructor_0_condition ol or /\
    getProjectionRoundPoolState nl nr = Projection_Round_Pool_State_0.

Definition projection_round_pool_constructor_1_condition
(l : Ledger) (r : RoundsBase_ι_Round) :=
    constructorCalled.

Definition projection_round_pool_constructor_1_move
(ol nl : Ledger) (or nr : RoundsBase_ι_Round) :=
    roundIn nl nr /\
    ~ roundIn ol nr /\
    projection_round_pool_constructor_0_condition ol or /\
    getProjectionRoundPoolState nl nr = Projection_Round_Pool_State_0.

Definition projection_round_pool_constructor_2_condition
(l : Ledger) (r : RoundsBase_ι_Round) :=
    constructorCalled.

Definition projection_round_pool_constructor_2_move
(ol nl : Ledger) (or nr : RoundsBase_ι_Round) :=
    roundIn nl nr /\
    ~ roundIn ol nr /\
    projection_round_pool_constructor_0_condition ol or /\
    getProjectionRoundPoolState nl nr = Projection_Round_Pool_State_0.

Definition projection_round_pool_destruction_pre0_condition
(l : Ledger) (r : RoundsBase_ι_Round) :=
    getProjectionRoundPoolState l r = Projection_Round_Pool_State_Pre0 /\
    updateRoundsCalled l ticktockCalled /\
    eval_state (↑12 ε DePoolContract_ι_m_poolClosed) l = true /\
    isEmptyRound (roundPre0 l) /\
    isEmptyRound (round0 l) /\
    isEmptyRound (round1 l) /\
    isEmptyRound (round2 l).

Definition projection_round_pool_destruction_0_condition
(l : Ledger) (r : RoundsBase_ι_Round) :=
    getProjectionRoundPoolState l r = Projection_Round_Pool_State_0 /\
    updateRoundsCalled l ticktockCalled /\
    eval_state (↑12 ε DePoolContract_ι_m_poolClosed) l = true /\
    isEmptyRound (roundPre0 l) /\
    isEmptyRound (round0 l) /\
    isEmptyRound (round1 l) /\
    isEmptyRound (round2 l).

Definition projection_round_pool_destruction_1_condition
(l : Ledger) (r : RoundsBase_ι_Round) :=
    getProjectionRoundPoolState l r = Projection_Round_Pool_State_1 /\
    updateRoundsCalled l ticktockCalled /\
    eval_state (↑12 ε DePoolContract_ι_m_poolClosed) l = true /\
    isEmptyRound (roundPre0 l) /\
    isEmptyRound (round0 l) /\
    isEmptyRound (round1 l) /\
    isEmptyRound (round2 l).

Definition projection_round_pool_destruction_2_condition
(l : Ledger) (r : RoundsBase_ι_Round) :=
    getProjectionRoundPoolState l r = Projection_Round_Pool_State_2 /\
    updateRoundsCalled l ticktockCalled /\
    eval_state (↑12 ε DePoolContract_ι_m_poolClosed) l = true /\
    isEmptyRound (roundPre0 l) /\
    isEmptyRound (round0 l) /\
    isEmptyRound (round1 l) /\
    isEmptyRound (round2 l).

Definition projection_round_pool_move_0_condition
(l : Ledger) (r : RoundsBase_ι_Round) :=
    getProjectionRoundPoolState l r = Projection_Round_Pool_State_Pre0 /\
    rotate_round_conditions_full l ticktockCalled.

Definition projection_round_pool_move_0_move
    (ol nl : Ledger) (or nr : RoundsBase_ι_Round) :=
    projection_round_pool_move_0_condition ol or /\
    roundsSame or nr /\
    getProjectionRoundPoolState nl nr = Projection_Round_Pool_State_0.

Definition projection_round_pool_move_1_condition
(l : Ledger) (r : RoundsBase_ι_Round) :=
    getProjectionRoundPoolState l r = Projection_Round_Pool_State_0 /\
    rotate_round_conditions_full l ticktockCalled.

Definition projection_round_pool_move_1_move
    (ol nl : Ledger) (or nr : RoundsBase_ι_Round) :=
    projection_round_pool_move_1_condition ol or /\
    roundsSame or nr /\
    getProjectionRoundPoolState nl nr = Projection_Round_Pool_State_1.

Definition projection_round_pool_move_2_condition
(l : Ledger) (r : RoundsBase_ι_Round) :=
    getProjectionRoundPoolState l r = Projection_Round_Pool_State_1 /\
    rotate_round_conditions_full l ticktockCalled.

Definition projection_round_pool_move_2_move
    (ol nl : Ledger) (or nr : RoundsBase_ι_Round) :=
    projection_round_pool_move_2_condition ol or /\
    roundsSame or nr /\
    getProjectionRoundPoolState nl nr = Projection_Round_Pool_State_2.

Definition projection_round_pool_move_expired_condition
(l : Ledger) (r : RoundsBase_ι_Round) :=
    getProjectionRoundPoolState l r = Projection_Round_Pool_State_2 /\
    rotate_round_conditions_full l ticktockCalled.

Definition projection_round_pool_move_expired_move
    (ol nl : Ledger) (or nr : RoundsBase_ι_Round) :=
    projection_round_pool_move_expired_condition ol or /\
    roundsSame or nr /\
    getProjectionRoundPoolState nl nr = Projection_Round_Pool_State_Expired.

End Round_Pool_conditions.
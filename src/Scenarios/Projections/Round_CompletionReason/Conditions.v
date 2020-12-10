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

Require Export depoolContract.Scenarios.Projections.Round_CompletionReason.States.
Require Export depoolContract.Scenarios.Common.RotateRoundsCondition.

Section Round_CompletionReason_conditions.

Variable ticktockCalled : Prop.
Variable constructorCalled : Prop.
Variable terminatorCalled : Prop.
Variable onSuccessToRecoverStakeCalled : Prop.
Variable onFailToRecoverStakeCalled : Prop.
Variable onStakeRejectCalled : Prop.
Variable onStakeAcceptCalled : Prop.
Variable queryId elector : Z.

Definition generateRoundCalled (l : Ledger) :=
    constructorCalled \/ rotate_round_conditions_full l ticktockCalled.


Definition projection_round_completion_reason_constructor_condition
(l : Ledger) (r : RoundsBase_ι_Round) :=
    generateRoundCalled l.

Definition projection_round_completion_reason_constructor_move
(ol nl : Ledger) (or nr : RoundsBase_ι_Round) :=
    roundIn nl nr /\
    ~ roundIn ol nr /\
    projection_round_completion_reason_constructor_condition ol or /\
    getProjectionRoundCompletionReasonState nr = RoundsBase_ι_CompletionReasonP_ι_Undefined.

Definition projection_round_completion_reason_constructor_fake_round_condition
    (l : Ledger) (r : RoundsBase_ι_Round) := 
    constructorCalled.

Definition projection_round_completion_reason_constructor_fake_round_move
(ol nl : Ledger) (or nr : RoundsBase_ι_Round) :=
    roundIn nl nr /\
    ~ roundIn ol nr /\
    projection_round_completion_reason_constructor_fake_round_condition ol or /\
    getProjectionRoundCompletionReasonState nr = RoundsBase_ι_CompletionReasonP_ι_FakeRound.

Definition projection_round_completion_reason_undefined_from_stake_rejected_by_elector_condition
    (l : Ledger) (r : RoundsBase_ι_Round) :=
    getProjectionRoundCompletionReasonState r = RoundsBase_ι_CompletionReasonP_ι_Undefined /\
    roundIn l r /\
    onStakeAcceptCalled /\
    RoundsBase_ι_Round_ι_elector r = elector /\
    RoundsBase_ι_Round_ι_id r = queryId /\
    eval_state (↑16 ε VMState_ι_msg_sender) l = RoundsBase_ι_Round_ι_proxy r /\
    RoundsBase_ι_Round_ι_step r = RoundsBase_ι_RoundStepP_ι_WaitingIfStakeAccepted.

Definition projection_round_completion_reason_undefined_from_stake_rejected_by_elector_move
    (ol nl : Ledger) (or nr : RoundsBase_ι_Round) :=
    projection_round_completion_reason_undefined_from_stake_rejected_by_elector_condition ol or /\
    roundIn nl nr /\
    roundsSame or nr /\
    getProjectionRoundCompletionReasonState nr = RoundsBase_ι_CompletionReasonP_ι_Undefined
    .

Definition projection_round_completion_reason_validator_is_punished_condition
    (l : Ledger) (r : RoundsBase_ι_Round) :=
        getProjectionRoundCompletionReasonState r = RoundsBase_ι_CompletionReasonP_ι_Undefined /\
        roundIn l r /\
        RoundsBase_ι_Round_ι_elector r = elector /\
        RoundsBase_ι_Round_ι_id r = queryId /\
        eval_state (↑16 ε VMState_ι_msg_sender) l = RoundsBase_ι_Round_ι_proxy r /\
        RoundsBase_ι_Round_ι_step r = RoundsBase_ι_RoundStepP_ι_WaitingReward /\
        (onSuccessToRecoverStakeCalled /\
            msgValue l + eval_state (↑9 ε DePoolLib_ι_PROXY_FEE) l <
            RoundsBase_ι_Round_ι_stake r - RoundsBase_ι_Round_ι_unused r
    \/
        onFailToRecoverStakeCalled
        ).

Definition projection_round_completion_reason_validator_is_punished_move
    (ol nl : Ledger) (or nr : RoundsBase_ι_Round) :=
    projection_round_completion_reason_validator_is_punished_condition ol or /\
    roundIn nl nr /\
    roundsSame or nr /\
    getProjectionRoundCompletionReasonState nr = RoundsBase_ι_CompletionReasonP_ι_ValidatorIsPunished
    .

Definition projection_round_completion_reason_pool_closed_condition
    (l : Ledger) (r : RoundsBase_ι_Round) :=
    getProjectionRoundCompletionReasonState r = RoundsBase_ι_CompletionReasonP_ι_Undefined /\
    roundIn l r /\
    terminatorCalled /\
    ownerOrSelfCall l /\
    eval_state (↑12 ε DePoolContract_ι_m_poolClosed) l = false /\
        r = roundPre0 l \/
        r = round0 l \/
        (   r = round1 l /\
            RoundsBase_ι_Round_ι_step r = RoundsBase_ι_RoundStepP_ι_WaitingValidatorRequest).

Definition projection_round_completion_reason_pool_closed_move
    (ol nl : Ledger) (or nr : RoundsBase_ι_Round) :=
    projection_round_completion_reason_pool_closed_condition ol or /\
    roundIn nl nr /\
    roundsSame or nr /\
    getProjectionRoundCompletionReasonState nr = RoundsBase_ι_CompletionReasonP_ι_PoolClosed
.

Definition projection_round_completion_reason_pool_closed_from_rejected_condition
    (l : Ledger) (r : RoundsBase_ι_Round) :=
    getProjectionRoundCompletionReasonState r = RoundsBase_ι_CompletionReasonP_ι_StakeIsRejectedByElector /\
    roundIn l r /\
    terminatorCalled /\
    ownerOrSelfCall l /\
    eval_state (↑12 ε DePoolContract_ι_m_poolClosed) l = false /\
    r = round1 l /\
    RoundsBase_ι_Round_ι_step r = RoundsBase_ι_RoundStepP_ι_WaitingValidatorRequest.

Definition projection_round_completion_reason_pool_closed_from_rejected_move
    (ol nl : Ledger) (or nr : RoundsBase_ι_Round) :=
    projection_round_completion_reason_pool_closed_from_rejected_condition ol or /\
    roundIn nl nr /\
    roundsSame or nr /\
    getProjectionRoundCompletionReasonState nr = RoundsBase_ι_CompletionReasonP_ι_PoolClosed
.

Definition projection_round_completion_reason_validator_stake_is_too_small_condition
    (l : Ledger) (r : RoundsBase_ι_Round) :=
    getProjectionRoundCompletionReasonState r = RoundsBase_ι_CompletionReasonP_ι_Undefined /\
    roundIn l r /\
    rotate_round_conditions_full l ticktockCalled /\
    eval_state (↑12 ε DePoolContract_ι_m_poolClosed) l = false /\
    r = round0 l /\
        RoundsBase_ι_Round_ι_validatorStake r <
        eval_state (↑12 ε DePoolContract_ι_m_validatorAssurance) l.

Definition projection_round_completion_reason_validator_stake_is_too_small_move
    (ol nl : Ledger) (or nr : RoundsBase_ι_Round) :=
    projection_round_completion_reason_validator_stake_is_too_small_condition ol or /\
    roundIn nl nr /\
    roundsSame or nr /\
    getProjectionRoundCompletionReasonState nr = RoundsBase_ι_CompletionReasonP_ι_ValidatorStakeIsTooSmall
    .

Definition projection_round_completion_reason_stake_rejected_by_elector_condition
    (l : Ledger) (r : RoundsBase_ι_Round) :=
    getProjectionRoundCompletionReasonState r = RoundsBase_ι_CompletionReasonP_ι_Undefined /\
    roundIn l r /\
    onStakeRejectCalled /\
    RoundsBase_ι_Round_ι_elector r = elector /\
    RoundsBase_ι_Round_ι_id r = queryId /\
    eval_state (↑16 ε VMState_ι_msg_sender) l = RoundsBase_ι_Round_ι_proxy r /\
    RoundsBase_ι_Round_ι_step r = RoundsBase_ι_RoundStepP_ι_WaitingIfStakeAccepted.

Definition projection_round_completion_reason_stake_rejected_by_elector_move
    (ol nl : Ledger) (or nr : RoundsBase_ι_Round) :=
    projection_round_completion_reason_stake_rejected_by_elector_condition ol or /\
    roundIn nl nr /\
    roundsSame or nr /\
    getProjectionRoundCompletionReasonState nr = RoundsBase_ι_CompletionReasonP_ι_StakeIsRejectedByElector
    .

Definition projection_round_completion_reason_reward_is_received_condition
    (l : Ledger) (r : RoundsBase_ι_Round) :=
        getProjectionRoundCompletionReasonState r = RoundsBase_ι_CompletionReasonP_ι_Undefined /\
        roundIn l r /\
        RoundsBase_ι_Round_ι_elector r = elector /\
        RoundsBase_ι_Round_ι_id r = queryId /\
        eval_state (↑16 ε VMState_ι_msg_sender) l = RoundsBase_ι_Round_ι_proxy r /\
        RoundsBase_ι_Round_ι_step r = RoundsBase_ι_RoundStepP_ι_WaitingReward /\
        onSuccessToRecoverStakeCalled /\
            msgValue l + eval_state (↑9 ε DePoolLib_ι_PROXY_FEE) l >=
            RoundsBase_ι_Round_ι_stake r - RoundsBase_ι_Round_ι_unused r.

Definition projection_round_completion_reason_reward_is_received_move
    (ol nl : Ledger) (or nr : RoundsBase_ι_Round) :=
    projection_round_completion_reason_reward_is_received_condition ol or /\
    roundIn nl nr /\
    roundsSame or nr /\
    getProjectionRoundCompletionReasonState nr = RoundsBase_ι_CompletionReasonP_ι_RewardIsReceived
    .

Definition projection_round_completion_reason_elections_are_lost_condition
    (l : Ledger) (r : RoundsBase_ι_Round) :=
    getProjectionRoundCompletionReasonState r = RoundsBase_ι_CompletionReasonP_ι_Undefined /\
    roundIn l r /\
    RoundsBase_ι_Round_ι_elector r = elector /\
    RoundsBase_ι_Round_ι_id r = queryId /\
    eval_state (↑16 ε VMState_ι_msg_sender) l = RoundsBase_ι_Round_ι_proxy r /\
    RoundsBase_ι_Round_ι_step r = RoundsBase_ι_RoundStepP_ι_WaitingIfValidatorWinElections /\
    onSuccessToRecoverStakeCalled /\
    msgValue l + eval_state (↑9 ε DePoolLib_ι_PROXY_FEE) l > RoundsBase_ι_Round_ι_stake r.

Definition projection_round_completion_reason_elections_are_lost_move
    (ol nl : Ledger) (or nr : RoundsBase_ι_Round) :=
    projection_round_completion_reason_elections_are_lost_condition ol or /\
    roundIn nl nr /\
    roundsSame or nr /\
    getProjectionRoundCompletionReasonState nr = RoundsBase_ι_CompletionReasonP_ι_ElectionsAreLost
    .

Definition projection_round_completion_reason_no_validator_request_condition
    (l : Ledger) (r : RoundsBase_ι_Round) :=
    getProjectionRoundCompletionReasonState r = RoundsBase_ι_CompletionReasonP_ι_Undefined /\
    roundIn l r /\
    RoundsBase_ι_Round_ι_step r = RoundsBase_ι_RoundStepP_ι_WaitingValidatorRequest /\
    updateRoundsCalled l ticktockCalled /\
        r = round2 l \/
        (r = round1 l /\ rotate_round_conditions_full l ticktockCalled).

Definition projection_round_completion_reason_no_validator_request_move
    (ol nl : Ledger) (or nr : RoundsBase_ι_Round) :=
    projection_round_completion_reason_no_validator_request_condition ol or /\
    roundIn nl nr /\
    roundsSame or nr /\
    getProjectionRoundCompletionReasonState nr = RoundsBase_ι_CompletionReasonP_ι_NoValidatorRequest
    .

End Round_CompletionReason_conditions.
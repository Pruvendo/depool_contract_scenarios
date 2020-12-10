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

Require Export depoolContract.Scenarios.Projections.Round_Steps.States.
Require Export depoolContract.Scenarios.Common.RotateRoundsCondition.
Require Export depoolContract.Scenarios.Common.RoundDefinitions.
Require Export depoolContract.Scenarios.Common.unfreezeCondition.

Section Round_Steps_conditions.

Variable ticktockCalled : Prop.
Variable constructorCalled : Prop.
Variable terminatorCalled : Prop.
Variable onSuccessToRecoverStakeCalled : Prop.
Variable onFailToRecoverStakeCalled : Prop.
Variable onStakeRejectCalled : Prop.
Variable onStakeAcceptCalled : Prop.
Variable participateInElectionsCalled : Prop.
Variable completeRoundWithChunkCalled : Prop.
Variable queryId elector stakeAt chunkSize : Z.
Variable bounceExternal : Prop.
Variable functionId process_new_stakeId recover_stakeId decodedRoundId : Z.

Definition generateRoundCalled (l : Ledger) :=
    constructorCalled \/ rotate_round_conditions_full l ticktockCalled.


Definition projection_round_steps_constructor_condition
(l : Ledger) (r : RoundsBase_ι_Round) :=
    generateRoundCalled l.

Definition projection_round_steps_constructor_move
(ol nl : Ledger) (or nr : RoundsBase_ι_Round) :=
    roundIn nl nr /\
    ~ roundIn ol nr /\
    projection_round_steps_constructor_condition ol or /\
    getProjectionRoundStepState nr = RoundsBase_ι_RoundStepP_ι_PrePooling.

Definition projection_round_steps_constructor_fake0_condition
    (l : Ledger) (r : RoundsBase_ι_Round) :=
        constructorCalled.

Definition projection_round_steps_constructor_fake0_move
(ol nl : Ledger) (or nr : RoundsBase_ι_Round) :=
    roundIn nl nr /\
    ~ roundIn ol nr /\
    projection_round_steps_constructor_fake0_condition ol or /\
    getProjectionRoundStepState nr = RoundsBase_ι_RoundStepP_ι_Pooling.

Definition projection_round_steps_constructor_fake1_condition
    (l : Ledger) (r : RoundsBase_ι_Round) :=
        constructorCalled.

Definition projection_round_steps_constructor_fake1_move
(ol nl : Ledger) (or nr : RoundsBase_ι_Round) :=
    roundIn nl nr /\
    ~ roundIn ol nr /\
    projection_round_steps_constructor_fake1_condition ol or /\
    getProjectionRoundStepState nr = RoundsBase_ι_RoundStepP_ι_WaitingUnfreeze.

Definition projection_round_steps_constructor_fake2_condition
    (l : Ledger) (r : RoundsBase_ι_Round) :=
        constructorCalled.

Definition projection_round_steps_constructor_fake2_move
(ol nl : Ledger) (or nr : RoundsBase_ι_Round) :=
    roundIn nl nr /\
    ~ roundIn ol nr /\
    projection_round_steps_constructor_fake2_condition ol or /\
    getProjectionRoundStepState nr = RoundsBase_ι_RoundStepP_ι_Completed.

Definition projection_round_steps_prepool_completing_condition
    (l : Ledger) (r : RoundsBase_ι_Round) :=
    terminatorCalled /\
    r = roundPre0 l /\
    getProjectionRoundStepState r = RoundsBase_ι_RoundStepP_ι_PrePooling /\
    ownerOrSelfCall l /\
    poolClosed l = false /\
    0 < RoundsBase_ι_Round_ι_participantQty r.

Definition projection_round_steps_prepool_completing_move
(ol nl : Ledger) (or nr : RoundsBase_ι_Round) :=
    projection_round_steps_prepool_completing_condition ol or /\
    roundIn nl nr /\
    getProjectionRoundStepState nr = RoundsBase_ι_RoundStepP_ι_Completing.

Definition projection_round_steps_prepool_completed_condition
    (l : Ledger) (r : RoundsBase_ι_Round) :=
    terminatorCalled /\
    r = roundPre0 l /\
    getProjectionRoundStepState r = RoundsBase_ι_RoundStepP_ι_PrePooling /\
    ownerOrSelfCall l /\
    poolClosed l = false /\
    0 = RoundsBase_ι_Round_ι_participantQty r.

Definition projection_round_steps_prepool_completed_move
(ol nl : Ledger) (or nr : RoundsBase_ι_Round) :=
    projection_round_steps_prepool_completed_condition ol or /\
    roundIn nl nr /\
    getProjectionRoundStepState nr = RoundsBase_ι_RoundStepP_ι_Completed.

Definition projection_round_steps_prepool_pooling_condition
    (l : Ledger) (r : RoundsBase_ι_Round) :=
    rotate_round_conditions_full l ticktockCalled /\
    r = roundPre0 l /\
    poolClosed l = false /\
    getProjectionRoundStepState r = RoundsBase_ι_RoundStepP_ι_PrePooling.

Definition projection_round_steps_prepool_pooling_move
    (ol nl : Ledger) (or nr : RoundsBase_ι_Round) :=
        projection_round_steps_prepool_pooling_condition ol or /\
        roundIn nl nr /\
        getProjectionRoundStepState nr = RoundsBase_ι_RoundStepP_ι_Pooling.

Definition projection_round_steps_pooling_completing_condition
    (l : Ledger) (r : RoundsBase_ι_Round) :=
    terminatorCalled /\
    r = roundPre0 l /\
    getProjectionRoundStepState r = RoundsBase_ι_RoundStepP_ι_Pooling /\
    ownerOrSelfCall l /\
    poolClosed l = false /\
    0 < RoundsBase_ι_Round_ι_participantQty r.

Definition projection_round_steps_pooling_completing_move
(ol nl : Ledger) (or nr : RoundsBase_ι_Round) :=
    projection_round_steps_pooling_completing_condition ol or /\
    roundIn nl nr /\
    getProjectionRoundStepState nr = RoundsBase_ι_RoundStepP_ι_Completing.

Definition projection_round_steps_pooling_completed_condition
    (l : Ledger) (r : RoundsBase_ι_Round) :=
    terminatorCalled /\
    r = roundPre0 l /\
    getProjectionRoundStepState r = RoundsBase_ι_RoundStepP_ι_Pooling /\
    ownerOrSelfCall l /\
    poolClosed l = false /\
    0 = RoundsBase_ι_Round_ι_participantQty r.

Definition projection_round_steps_pooling_completed_move
(ol nl : Ledger) (or nr : RoundsBase_ι_Round) :=
    projection_round_steps_pooling_completed_condition ol or /\
    roundIn nl nr /\
    getProjectionRoundStepState nr = RoundsBase_ι_RoundStepP_ι_Completed.

Definition projection_round_steps_pooling_waiting_unfreeze_condition
    (l : Ledger) (r : RoundsBase_ι_Round) :=
    rotate_round_conditions_full l ticktockCalled /\
    r = round0 l /\
    poolClosed l = false /\
    getProjectionRoundStepState r = RoundsBase_ι_RoundStepP_ι_Pooling /\
    stakeSum (validatorStake l r) < m_validatorAssurance l.

Definition projection_round_steps_pooling_waiting_unfreeze_move
    (ol nl : Ledger) (or nr : RoundsBase_ι_Round) :=
    projection_round_steps_pooling_waiting_unfreeze_condition ol or /\
    roundIn nl nr /\
    getProjectionRoundStepState nr = RoundsBase_ι_RoundStepP_ι_WaitingUnfreeze.

Definition projection_round_steps_pooling_waiting_validator_request_condition
    (l : Ledger) (r : RoundsBase_ι_Round) :=
    rotate_round_conditions_full l ticktockCalled /\
    r = round0 l /\
    poolClosed l = false /\
    getProjectionRoundStepState r = RoundsBase_ι_RoundStepP_ι_Pooling /\
    m_validatorAssurance l <= stakeSum (validatorStake l r).

Definition projection_round_steps_pooling_waiting_validator_request_move
    (ol nl : Ledger) (or nr : RoundsBase_ι_Round) :=
    projection_round_steps_pooling_waiting_validator_request_condition ol or /\
    roundIn nl nr /\
    getProjectionRoundStepState nr = RoundsBase_ι_RoundStepP_ι_WaitingValidatorRequest.

Definition projection_round_steps_waiting_validator_request_completing1_condition
    (l : Ledger) (r : RoundsBase_ι_Round) :=
    terminatorCalled /\
    r = round1 l /\
    getProjectionRoundStepState r = RoundsBase_ι_RoundStepP_ι_WaitingValidatorRequest /\
    ownerOrSelfCall l /\
    poolClosed l = false.

Definition projection_round_steps_waiting_validator_request_completing1_move
(ol nl : Ledger) (or nr : RoundsBase_ι_Round) :=
    projection_round_steps_waiting_validator_request_completing1_condition ol or /\
    roundIn nl nr /\
    getProjectionRoundStepState nr = RoundsBase_ι_RoundStepP_ι_Completing.

Definition projection_round_steps_waiting_validator_request_completing2_condition
    (l : Ledger) (r : RoundsBase_ι_Round) :=
    rotate_round_conditions_full l ticktockCalled /\
    r = round1 l /\
    getProjectionRoundStepState r = RoundsBase_ι_RoundStepP_ι_WaitingValidatorRequest.

Definition projection_round_steps_waiting_validator_request_completing2_move
    (ol nl : Ledger) (or nr : RoundsBase_ι_Round) :=
    projection_round_steps_waiting_validator_request_completing2_condition ol or /\
    roundIn nl nr /\
    getProjectionRoundStepState nr = RoundsBase_ι_RoundStepP_ι_Completing.

Definition projection_round_steps_waiting_validator_request_waiting_if_stake_accepted_condition
    (l : Ledger) (r : RoundsBase_ι_Round) :=
    participateInElectionsCalled /\
    onlyValidatorContract l /\
    poolClosed l = false /\
    checkDePoolBalance l (msgValue l) (balance l) /\
    stakeAt = RoundsBase_ι_Round_ι_supposedElectedAt r /\
    r = round1 l /\
    getProjectionRoundStepState r = RoundsBase_ι_RoundStepP_ι_WaitingValidatorRequest.

Definition projection_round_steps_waiting_validator_request_waiting_if_stake_accepted_move
    (ol nl : Ledger) (or nr : RoundsBase_ι_Round) :=
    projection_round_steps_waiting_validator_request_waiting_if_stake_accepted_condition
        ol or /\
    roundIn nl nr /\
    getProjectionRoundStepState nr = RoundsBase_ι_RoundStepP_ι_WaitingIfStakeAccepted.

Definition projection_round_steps_waiting_if_stake_accepted_waiting_validator_request0_condition
    (l : Ledger) (r : RoundsBase_ι_Round) :=
    bounceExternal /\
    functionId = process_new_stakeId /\
    RoundsBase_ι_Round_ι_id r = decodedRoundId /\
    r = round1 l /\
    getProjectionRoundStepState r = RoundsBase_ι_RoundStepP_ι_WaitingIfStakeAccepted.

Definition projection_round_steps_waiting_if_stake_accepted_waiting_validator_request0_move
(ol nl : Ledger) (or nr : RoundsBase_ι_Round) :=
    projection_round_steps_waiting_if_stake_accepted_waiting_validator_request0_condition
        ol or /\
    roundIn nl nr /\
    getProjectionRoundStepState nr = RoundsBase_ι_RoundStepP_ι_WaitingValidatorRequest.

Definition projection_round_steps_waiting_if_stake_accepted_waiting_validator_request1_condition
    (l : Ledger) (r : RoundsBase_ι_Round) :=
    onStakeRejectCalled /\
    RoundsBase_ι_Round_ι_id r = queryId /\
    r = round1 l /\
    msgSender l = RoundsBase_ι_Round_ι_proxy r /\
    elector = RoundsBase_ι_Round_ι_elector r /\
    getProjectionRoundStepState r = RoundsBase_ι_RoundStepP_ι_WaitingIfStakeAccepted.

Definition projection_round_steps_waiting_if_stake_accepted_waiting_validator_request1_move
    (ol nl : Ledger) (or nr : RoundsBase_ι_Round) :=
    projection_round_steps_waiting_if_stake_accepted_waiting_validator_request1_condition
        ol or /\
    roundIn nl nr /\
    getProjectionRoundStepState nr = RoundsBase_ι_RoundStepP_ι_WaitingValidatorRequest.

Definition projection_round_steps_waiting_if_stake_accepted_waiting_validator_start_condition
    (l : Ledger) (r : RoundsBase_ι_Round) :=
    onStakeAcceptCalled /\
    RoundsBase_ι_Round_ι_id r = queryId /\
    r = round1 l /\
    msgSender l = RoundsBase_ι_Round_ι_proxy r /\
    elector = RoundsBase_ι_Round_ι_elector r /\
    getProjectionRoundStepState r = RoundsBase_ι_RoundStepP_ι_WaitingIfStakeAccepted.

Definition projection_round_steps_waiting_if_stake_accepted_waiting_validator_start_move
    (ol nl : Ledger) (or nr : RoundsBase_ι_Round) :=
    projection_round_steps_waiting_if_stake_accepted_waiting_validator_start_condition
        ol or /\
    roundIn nl nr /\
    getProjectionRoundStepState nr = RoundsBase_ι_RoundStepP_ι_WaitingValidationStart.

Definition projection_round_steps_waiting_validator_start_waiting_reward1_condition
    (l : Ledger) (r : RoundsBase_ι_Round) :=
    rotate_round_conditions_full l ticktockCalled /\
    r = round1 l /\
    RoundsBase_ι_Round_ι_vsetHashInElectionPhase r <> currentValidator l /\
    RoundsBase_ι_Round_ι_vsetHashInElectionPhase r <> prevValidator l /\
    validationStart l + RoundsBase_ι_Round_ι_stakeHeldFor r + ELECTOR_UNFREEZE_LAG l <= now l /\
    getProjectionRoundStepState r = RoundsBase_ι_RoundStepP_ι_WaitingValidationStart.

Definition projection_round_steps_waiting_validator_start_waiting_reward1_move
(ol nl : Ledger) (or nr : RoundsBase_ι_Round) :=
    projection_round_steps_waiting_validator_start_waiting_reward1_condition
        ol or /\
    roundIn nl nr /\
    getProjectionRoundStepState nr = RoundsBase_ι_RoundStepP_ι_WaitingReward.

Definition projection_round_steps_waiting_validator_start_waiting_reward2_condition
    (l : Ledger) (r : RoundsBase_ι_Round) :=
    updateRoundsCalled l ticktockCalled /\
    r = round2 l /\
    RoundsBase_ι_Round_ι_vsetHashInElectionPhase r <> currentValidator l /\
    RoundsBase_ι_Round_ι_vsetHashInElectionPhase r <> prevValidator l /\
    validationStart l + RoundsBase_ι_Round_ι_stakeHeldFor r + ELECTOR_UNFREEZE_LAG l <= now l /\
    getProjectionRoundStepState r = RoundsBase_ι_RoundStepP_ι_WaitingValidationStart.

Definition projection_round_steps_waiting_validator_start_waiting_reward2_move
    (ol nl : Ledger) (or nr : RoundsBase_ι_Round) :=
    projection_round_steps_waiting_validator_start_waiting_reward2_condition
        ol or /\
    roundIn nl nr /\
    getProjectionRoundStepState nr = RoundsBase_ι_RoundStepP_ι_WaitingReward.

Definition projection_round_steps_waiting_validator_start_waiting_if_validator_win_elections_condition
(l : Ledger) (r : RoundsBase_ι_Round) :=
    updateRoundsCalled l ticktockCalled /\
    r = round1 l /\
    RoundsBase_ι_Round_ι_vsetHashInElectionPhase r = prevValidator l /\
    getProjectionRoundStepState r = RoundsBase_ι_RoundStepP_ι_WaitingValidationStart.

Definition projection_round_steps_waiting_validator_start_waiting_if_validator_win_elections_move
    (ol nl : Ledger) (or nr : RoundsBase_ι_Round) :=
    projection_round_steps_waiting_validator_start_waiting_if_validator_win_elections_condition
        ol or /\
    roundIn nl nr /\
    getProjectionRoundStepState nr = RoundsBase_ι_RoundStepP_ι_WaitingReward.

Definition projection_round_steps_waiting_if_validator_win_elections_waiting_validator_start_condition
(l : Ledger) (r : RoundsBase_ι_Round) :=
    bounceExternal /\
    functionId = recover_stakeId /\
    RoundsBase_ι_Round_ι_id r = decodedRoundId /\
    r = round1 l /\
    getProjectionRoundStepState r = RoundsBase_ι_RoundStepP_ι_WaitingIfValidatorWinElections.

Definition projection_round_steps_waiting_if_validator_win_elections_waiting_validator_start_move
(ol nl : Ledger) (or nr : RoundsBase_ι_Round) :=
    projection_round_steps_waiting_if_validator_win_elections_waiting_validator_start_condition
        ol or /\
    roundIn nl nr /\
    getProjectionRoundStepState nr = RoundsBase_ι_RoundStepP_ι_WaitingValidationStart.

Definition projection_round_steps_waiting_if_validator_win_elections_waiting_unfreeze_condition
(l : Ledger) (r : RoundsBase_ι_Round) :=
    (onSuccessToRecoverStakeCalled \/ onFailToRecoverStakeCalled) /\
    RoundsBase_ι_Round_ι_id r = queryId /\
    roundIn l r /\
    msgSender l = RoundsBase_ι_Round_ι_proxy r /\
    elector = RoundsBase_ι_Round_ι_elector r /\
    getProjectionRoundStepState r = RoundsBase_ι_RoundStepP_ι_WaitingIfValidatorWinElections.

Definition projection_round_steps_waiting_if_validator_win_elections_waiting_unfreeze_move
(ol nl : Ledger) (or nr : RoundsBase_ι_Round) :=
    projection_round_steps_waiting_if_validator_win_elections_waiting_unfreeze_condition
        ol or /\
    roundIn nl nr /\
    getProjectionRoundStepState nr = RoundsBase_ι_RoundStepP_ι_WaitingUnfreeze.

Definition projection_round_steps_waiting_unfreeze_waiting_reward_condition1
    (l : Ledger) (r : RoundsBase_ι_Round) :=
    rotate_round_conditions_full l ticktockCalled /\
    r = round1 l /\
    shouldBeUnfrozen l r /\
    RoundsBase_ι_Round_ι_completionReason r = RoundsBase_ι_CompletionReasonP_ι_Undefined /\
    getProjectionRoundStepState r = RoundsBase_ι_RoundStepP_ι_WaitingUnfreeze.

Definition projection_round_steps_waiting_unfreeze_waiting_reward_move1
(ol nl : Ledger) (or nr : RoundsBase_ι_Round) :=
    projection_round_steps_waiting_unfreeze_waiting_reward_condition1
        ol or /\
    roundIn nl nr /\
    getProjectionRoundStepState nr = RoundsBase_ι_RoundStepP_ι_WaitingReward.

Definition projection_round_steps_waiting_unfreeze_waiting_reward_condition2
    (l : Ledger) (r : RoundsBase_ι_Round) :=
    updateRoundsCalled l ticktockCalled /\
    r = round2 l /\
    shouldBeUnfrozen l r /\
    RoundsBase_ι_Round_ι_completionReason r = RoundsBase_ι_CompletionReasonP_ι_Undefined /\
    getProjectionRoundStepState r = RoundsBase_ι_RoundStepP_ι_WaitingUnfreeze.

Definition projection_round_steps_waiting_unfreeze_waiting_reward_move2
(ol nl : Ledger) (or nr : RoundsBase_ι_Round) :=
    projection_round_steps_waiting_unfreeze_waiting_reward_condition2
        ol or /\
    roundIn nl nr /\
    getProjectionRoundStepState nr = RoundsBase_ι_RoundStepP_ι_WaitingReward.

Definition projection_round_steps_waiting_unfreeze_completing_condition1
    (l : Ledger) (r : RoundsBase_ι_Round) :=
    rotate_round_conditions_full l ticktockCalled /\
    r = round1 l /\
    shouldBeUnfrozen l r /\
    RoundsBase_ι_Round_ι_completionReason r <> RoundsBase_ι_CompletionReasonP_ι_Undefined /\
    0 < RoundsBase_ι_Round_ι_participantQty r /\
    getProjectionRoundStepState r = RoundsBase_ι_RoundStepP_ι_WaitingUnfreeze.

Definition projection_round_steps_waiting_unfreeze_completing_move1
(ol nl : Ledger) (or nr : RoundsBase_ι_Round) :=
    projection_round_steps_waiting_unfreeze_completing_condition1
        ol or /\
    roundIn nl nr /\
    getProjectionRoundStepState nr = RoundsBase_ι_RoundStepP_ι_Completing.

Definition projection_round_steps_waiting_unfreeze_completing_condition2
    (l : Ledger) (r : RoundsBase_ι_Round) :=
    updateRoundsCalled l ticktockCalled /\
    r = round2 l /\
    shouldBeUnfrozen l r /\
    RoundsBase_ι_Round_ι_completionReason r <> RoundsBase_ι_CompletionReasonP_ι_Undefined /\
    0 < RoundsBase_ι_Round_ι_participantQty r /\
    getProjectionRoundStepState r = RoundsBase_ι_RoundStepP_ι_WaitingUnfreeze.

Definition projection_round_steps_waiting_unfreeze_completing_move2
(ol nl : Ledger) (or nr : RoundsBase_ι_Round) :=
    projection_round_steps_waiting_unfreeze_completing_condition2
        ol or /\
    roundIn nl nr /\
    getProjectionRoundStepState nr = RoundsBase_ι_RoundStepP_ι_Completing.

Definition projection_round_steps_waiting_unfreeze_completed_condition1
    (l : Ledger) (r : RoundsBase_ι_Round) :=
    rotate_round_conditions_full l ticktockCalled /\
    r = round1 l /\
    shouldBeUnfrozen l r /\
    RoundsBase_ι_Round_ι_completionReason r <> RoundsBase_ι_CompletionReasonP_ι_Undefined /\
    0 = RoundsBase_ι_Round_ι_participantQty r /\
    getProjectionRoundStepState r = RoundsBase_ι_RoundStepP_ι_WaitingUnfreeze.

Definition projection_round_steps_waiting_unfreeze_completed_move1
(ol nl : Ledger) (or nr : RoundsBase_ι_Round) :=
    projection_round_steps_waiting_unfreeze_completed_condition1
        ol or /\
    roundIn nl nr /\
    getProjectionRoundStepState nr = RoundsBase_ι_RoundStepP_ι_Completed.

Definition projection_round_steps_waiting_unfreeze_completed_condition2
    (l : Ledger) (r : RoundsBase_ι_Round) :=
    updateRoundsCalled l ticktockCalled /\
    r = round2 l /\
    shouldBeUnfrozen l r /\
    RoundsBase_ι_Round_ι_completionReason r <> RoundsBase_ι_CompletionReasonP_ι_Undefined /\
    0 = RoundsBase_ι_Round_ι_participantQty r /\
    getProjectionRoundStepState r = RoundsBase_ι_RoundStepP_ι_WaitingUnfreeze.

Definition projection_round_steps_waiting_unfreeze_completed_move2
(ol nl : Ledger) (or nr : RoundsBase_ι_Round) :=
    projection_round_steps_waiting_unfreeze_completed_condition2
        ol or /\
    roundIn nl nr /\
    getProjectionRoundStepState nr = RoundsBase_ι_RoundStepP_ι_Completed.

Definition projection_round_steps_waiting_rewards_waiting_unfreeze_condition
    (l : Ledger) (r : RoundsBase_ι_Round) :=
    bounceExternal /\
    functionId = recover_stakeId /\
    RoundsBase_ι_Round_ι_id r = decodedRoundId /\
    r = round2 l /\
    getProjectionRoundStepState r = RoundsBase_ι_RoundStepP_ι_WaitingReward.

Definition projection_round_steps_waiting_rewards_waiting_unfreeze_move
(ol nl : Ledger) (or nr : RoundsBase_ι_Round) :=
    projection_round_steps_waiting_rewards_waiting_unfreeze_condition
        ol or /\
    roundIn nl nr /\
    getProjectionRoundStepState nr = RoundsBase_ι_RoundStepP_ι_WaitingUnfreeze.

Definition projection_round_steps_waiting_rewards_completing_condition
    (l : Ledger) (r : RoundsBase_ι_Round) :=
    (onSuccessToRecoverStakeCalled \/ onFailToRecoverStakeCalled) /\
    RoundsBase_ι_Round_ι_id r = queryId /\
    roundIn l r /\
    msgSender l = RoundsBase_ι_Round_ι_proxy r /\
    elector = RoundsBase_ι_Round_ι_elector r /\
    getProjectionRoundStepState r = RoundsBase_ι_RoundStepP_ι_WaitingReward.

Definition projection_round_steps_waiting_rewards_completing_move
(ol nl : Ledger) (or nr : RoundsBase_ι_Round) :=
    projection_round_steps_waiting_rewards_completing_condition
        ol or /\
    roundIn nl nr /\
    getProjectionRoundStepState nr = RoundsBase_ι_RoundStepP_ι_Completing.

Definition projection_round_steps_completing_completed_condition
    (l : Ledger) (r : RoundsBase_ι_Round) :=
    completeRoundWithChunkCalled /\
    selfCall l /\
    RoundsBase_ι_Round_ι_id r = queryId /\
    r = round2 l /\
    Z.of_nat (length (RoundsBase_ι_Round_ι_stakes r)) <= chunkSize /\
    getProjectionRoundStepState r = RoundsBase_ι_RoundStepP_ι_Completing.

Definition projection_round_steps_completing_completed_move
(ol nl : Ledger) (or nr : RoundsBase_ι_Round) :=
    projection_round_steps_completing_completed_condition
        ol or /\
    roundIn nl nr /\
    getProjectionRoundStepState nr = RoundsBase_ι_RoundStepP_ι_Completed.

End Round_Steps_conditions.
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

Require Export depoolContract.Scenarios.Projections.Round_Stakes.States.
Require Export depoolContract.Scenarios.Common.RotateRoundsCondition.
Require Export depoolContract.Scenarios.Common._returnOrReinvestMove.
Require Export depoolContract.Scenarios.Common.RewardsMove.
Require Export depoolContract.Scenarios.Common.RotateRoundsCondition.

Section Round_Stakes_conditions.

Variable constructorCalled : Prop.
Variable ticktockCalled : Prop.
Variable completeRoundWithChunkCalled : Prop.
Variable addOrdinaryStakeCalled : Prop.
Variable addVestingStakeCalled : Prop.
Variable addLockStateCalled : Prop.
Variable withdrawFromPoolingRoundCalled : Prop.
Variable roundId participantQty chunkSize stake totalPeriod withdrawalPeriod : Z.
Variable withdrawValue queryId elector : Z.
Variable beneficiary : XAddress.

Definition generateRoundCalled (l : Ledger) :=
    constructorCalled \/ rotate_round_conditions_full l ticktockCalled.

Definition projection_round_stakes_constructor_condition
(l : Ledger) (r : RoundsBase_ι_Round) :=
    generateRoundCalled l.

Definition projection_round_stakes_constructor_move
(ol nl : Ledger) (or nr : RoundsBase_ι_Round) :=
    roundIn nl nr /\
    ~ roundIn ol nr /\
    projection_round_stakes_constructor_condition ol or /\
    getProjectionRoundStakesState nr = _Projection_Round_Stakes_State 0 0 0 false 0 0 0.

Definition projection_round_stakes_add_ordinary_stake_condition
(l : Ledger) (r : RoundsBase_ι_Round) :=
    eval_state (↑12 ε DePoolContract_ι_m_poolClosed) l = false /\
    internalMessage l /\
    addOrdinaryStakeCalled /\
    r = round0 l /\
    stake + STAKE_FEE l <= msgValue l /\
    m_minStake l <= stake
    .

Definition projection_round_stakes_add_ordinary_stake_move
(ol nl : Ledger) (or nr : RoundsBase_ι_Round) :=
    projection_round_stakes_add_ordinary_stake_condition ol or /\
    roundsSame or nr /\
    nr = round0 nl /\
    let nprc := getProjectionRoundStakesState nr in
    let oprc := getProjectionRoundStakesState or in
    projection_round_stakes_getStake nprc = projection_round_stakes_getStake oprc + stake /\
    projection_round_stakes_getRecoveredStake nprc = projection_round_stakes_getRecoveredStake oprc /\
    projection_round_stakes_getUnused nprc = projection_round_stakes_getUnused oprc /\
    projection_round_stakes_getIsValidatorStakeCompleted nprc =
        projection_round_stakes_getIsValidatorStakeCompleted oprc /\
    projection_round_stakes_getRewards nprc = projection_round_stakes_getRewards oprc /\
    projection_round_stakes_getValidatorStake nprc = projection_round_stakes_getValidatorStake oprc /\
    projection_round_stakes_getHandledStakesAndRewards nprc =
        projection_round_stakes_getHandledStakesAndRewards oprc.

Definition projection_round_stakes_add_vesting_or_lock_stake_condition
(l : Ledger) (r : RoundsBase_ι_Round) :=
    eval_state (↑12 ε DePoolContract_ι_m_poolClosed) l = false /\
    (addLockStateCalled \/ addVestingStakeCalled)  /\
    isStdAddrWithoutAnyCast beneficiary = true /\
    (r = round0 l \/ r = roundPre0 l) /\
    stake + STAKE_FEE l <= msgValue l /\
    m_minStake l <= stake / 2 /\
    totalPeriod <= withdrawalPeriod /\
    totalPeriod <= 18 * 365 * 86400 /\
    0 < withdrawalPeriod /\
    Zmod totalPeriod withdrawalPeriod = 0
    .

Definition projection_round_stakes_add_vesting_or_lock_stake_move
(ol nl : Ledger) (or nr : RoundsBase_ι_Round) :=
    projection_round_stakes_add_ordinary_stake_condition ol or /\
    roundsSame or nr /\
    ((nr = round0 nl /\ or = round0 ol) \/ (nr = roundPre0 nl /\ or = roundPre0 ol))  /\
    let nprc := getProjectionRoundStakesState nr in
    let oprc := getProjectionRoundStakesState or in
    projection_round_stakes_getStake nprc = projection_round_stakes_getStake oprc + stake /\
    projection_round_stakes_getRecoveredStake nprc = projection_round_stakes_getRecoveredStake oprc /\
    projection_round_stakes_getUnused nprc = projection_round_stakes_getUnused oprc /\
    projection_round_stakes_getIsValidatorStakeCompleted nprc =
        projection_round_stakes_getIsValidatorStakeCompleted oprc /\
    projection_round_stakes_getRewards nprc = projection_round_stakes_getRewards oprc /\
    projection_round_stakes_getValidatorStake nprc = projection_round_stakes_getValidatorStake oprc /\
    projection_round_stakes_getHandledStakesAndRewards nprc =
        projection_round_stakes_getHandledStakesAndRewards oprc.

Definition projection_round_stakes_complete_round_with_chunk_condition
(l : Ledger) (r : RoundsBase_ι_Round) :=
    selfCall l /\
    completeRoundWithChunkCalled /\
    poolClosed l = false /\
    roundId = RoundsBase_ι_Round_ι_id r /\
    r = round2 l /\
    RoundsBase_ι_Round_ι_step r = RoundsBase_ι_RoundStepP_ι_Completing /\
    (0%nat < length (RoundsBase_ι_Round_ι_stakes r))%nat.

Definition projection_round_stakes_complete_round_with_chunk_move
(ol nl : Ledger) (or nr : RoundsBase_ι_Round) :=
    projection_round_stakes_complete_round_with_chunk_condition ol or /\
    roundsSame or nr /\
    nr = round2 nl  /\
    let nprc := getProjectionRoundStakesState nr in
    let oprc := getProjectionRoundStakesState or in
    projection_round_stakes_getStake nprc = projection_round_stakes_getStake oprc /\
    projection_round_stakes_getRecoveredStake nprc = projection_round_stakes_getRecoveredStake oprc /\
    projection_round_stakes_getUnused nprc = projection_round_stakes_getUnused oprc /\
    projection_round_stakes_getIsValidatorStakeCompleted nprc = true /\
    projection_round_stakes_getRewards nprc = projection_round_stakes_getRewards oprc /\
    projection_round_stakes_getValidatorStake nprc =
        projection_round_stakes_getValidatorStake oprc /\
    projection_round_stakes_getHandledStakesAndRewards nprc =
    _returnOrReinvest_round2_handledStakesAndRewards ol or.

Definition projection_round_stakes_complete_round_with_chunk0_condition
(l : Ledger) (r : RoundsBase_ι_Round) :=
    selfCall l /\
    completeRoundWithChunkCalled /\
    poolClosed l = false /\
    roundId = RoundsBase_ι_Round_ι_id (round2 l) /\
    r = round0 l /\
    RoundsBase_ι_Round_ι_step (round2 l) = RoundsBase_ι_RoundStepP_ι_Completing /\
    (0%nat < length (RoundsBase_ι_Round_ι_stakes (round2 l)))%nat.

Definition projection_round_stakes_complete_round_with_chunk0_move
(ol nl : Ledger) (or nr : RoundsBase_ι_Round) :=
    projection_round_stakes_complete_round_with_chunk0_condition ol or /\
    roundsSame or nr /\
    nr = round0 nl  /\
    let nprc := getProjectionRoundStakesState nr in
    let oprc := getProjectionRoundStakesState or in
    projection_round_stakes_getStake nprc = projection_round_stakes_getStake oprc +
        _returnOrReinvest_round0_stake ol (round2 ol) /\
    projection_round_stakes_getRecoveredStake nprc = projection_round_stakes_getRecoveredStake oprc /\
    projection_round_stakes_getUnused nprc = projection_round_stakes_getUnused oprc /\
    projection_round_stakes_getIsValidatorStakeCompleted nprc =
        projection_round_stakes_getIsValidatorStakeCompleted oprc /\
    projection_round_stakes_getRewards nprc = projection_round_stakes_getRewards oprc /\
    projection_round_stakes_getValidatorStake nprc =
        projection_round_stakes_getValidatorStake oprc /\
    projection_round_stakes_getHandledStakesAndRewards nprc =
    projection_round_stakes_getHandledStakesAndRewards oprc.

Definition projection_round_stakes_withdraw_from_pooling_round_condition
(l : Ledger) (r : RoundsBase_ι_Round) :=
    internalMessage l /\
    withdrawFromPoolingRoundCalled /\
    r = round0 l /\
    poolClosed l = false /\
    0 < withdrawValue /\
    isSome ((RoundsBase_ι_Round_ι_stakes r) ->fetch (msgSender l)) = true /\
    0 < RoundsBase_ι_StakeValue_ι_ordinary (
        maybeGet ((RoundsBase_ι_Round_ι_stakes r) ->fetch (msgSender l))).

Definition projection_round_stakes_withdraw_from_pooling_round_move
(ol nl : Ledger) (or nr : RoundsBase_ι_Round) :=
    projection_round_stakes_withdraw_from_pooling_round_condition ol or /\
    roundsSame or nr /\
    nr = round0 nl  /\
    let nprc := getProjectionRoundStakesState nr in
    let oprc := getProjectionRoundStakesState or in
    projection_round_stakes_getStake nprc = projection_round_stakes_getStake oprc -
        intMin
            (RoundsBase_ι_StakeValue_ι_ordinary (
                maybeGet ((RoundsBase_ι_Round_ι_stakes or) ->fetch (msgSender ol))))
            withdrawValue /\
    projection_round_stakes_getRecoveredStake nprc = projection_round_stakes_getRecoveredStake oprc /\
    projection_round_stakes_getUnused nprc = projection_round_stakes_getUnused oprc /\
    projection_round_stakes_getIsValidatorStakeCompleted nprc = 
        projection_round_stakes_getIsValidatorStakeCompleted oprc /\
    projection_round_stakes_getRewards nprc = projection_round_stakes_getRewards oprc /\
    projection_round_stakes_getValidatorStake nprc =
        projection_round_stakes_getValidatorStake oprc /\
    projection_round_stakes_getHandledStakesAndRewards nprc =
    projection_round_stakes_getHandledStakesAndRewards oprc.

Definition projection_round_stakes_on_recover_stake_condition
    (l : Ledger) (r : RoundsBase_ι_Round) :=
    queryId = RoundsBase_ι_Round_ι_id r /\
    roundIn l r /\
    msgSender l = RoundsBase_ι_Round_ι_proxy r /\
    elector = RoundsBase_ι_Round_ι_elector r /\
    RoundsBase_ι_Round_ι_step r = RoundsBase_ι_RoundStepP_ι_WaitingReward.

Definition projection_round_stakes_on_recover_stake_move
(ol nl : Ledger) (or nr : RoundsBase_ι_Round) :=
    projection_round_stakes_on_recover_stake_condition ol or /\
    roundsSame or nr /\
    let nprc := getProjectionRoundStakesState nr in
    let oprc := getProjectionRoundStakesState or in
    projection_round_stakes_getStake nprc = projection_round_stakes_getStake oprc /\
    projection_round_stakes_getRecoveredStake nprc =
        msgValue ol + PROXY_FEE ol /\
    projection_round_stakes_getUnused nprc = projection_round_stakes_getUnused oprc /\
    projection_round_stakes_getIsValidatorStakeCompleted nprc = 
        projection_round_stakes_getIsValidatorStakeCompleted oprc /\
    projection_round_stakes_getRewards nprc = rewardsMove_reward ol or /\
    projection_round_stakes_getValidatorStake nprc =
        projection_round_stakes_getValidatorStake oprc /\
    projection_round_stakes_getHandledStakesAndRewards nprc =
    projection_round_stakes_getHandledStakesAndRewards oprc.

Definition projection_round_stakes_on_recover_stake_unused_condition
    (l : Ledger) (r : RoundsBase_ι_Round) :=
    queryId = RoundsBase_ι_Round_ι_id r /\
    roundIn l r /\
    msgSender l = RoundsBase_ι_Round_ι_proxy r /\
    elector = RoundsBase_ι_Round_ι_elector r /\
    RoundsBase_ι_Round_ι_step r = RoundsBase_ι_RoundStepP_ι_WaitingIfValidatorWinElections /\
    msgValue l < RoundsBase_ι_Round_ι_stake r.

Definition projection_round_stakes_on_recover_stake_unused_move
(ol nl : Ledger) (or nr : RoundsBase_ι_Round) :=
    projection_round_stakes_on_recover_stake_unused_condition ol or /\
    roundsSame or nr /\
    let nprc := getProjectionRoundStakesState nr in
    let oprc := getProjectionRoundStakesState or in
    projection_round_stakes_getStake nprc = projection_round_stakes_getStake oprc /\
    projection_round_stakes_getRecoveredStake nprc = projection_round_stakes_getRecoveredStake oprc /\
    projection_round_stakes_getUnused nprc = msgValue ol + PROXY_FEE ol /\
    projection_round_stakes_getIsValidatorStakeCompleted nprc = 
        projection_round_stakes_getIsValidatorStakeCompleted oprc /\
    projection_round_stakes_getRewards nprc = projection_round_stakes_getRewards oprc /\
    projection_round_stakes_getValidatorStake nprc =
        projection_round_stakes_getValidatorStake oprc /\
    projection_round_stakes_getHandledStakesAndRewards nprc =
    projection_round_stakes_getHandledStakesAndRewards oprc.

Definition projection_round_stakes_on_rotate_rounds_condition
    (l : Ledger) (r : RoundsBase_ι_Round) :=
    rotate_round_conditions_full l ticktockCalled /\
    r = round0 l /\
    poolClosed l = false /\
    isValidatorInRound l r = true.

Definition projection_round_stakes_on_rotate_rounds_move
(ol nl : Ledger) (or nr : RoundsBase_ι_Round) :=
    projection_round_stakes_on_rotate_rounds_condition ol or /\
    roundsSame or nr /\
    let nprc := getProjectionRoundStakesState nr in
    let oprc := getProjectionRoundStakesState or in
    projection_round_stakes_getStake nprc = projection_round_stakes_getStake oprc /\
    projection_round_stakes_getRecoveredStake nprc = projection_round_stakes_getRecoveredStake oprc /\
    projection_round_stakes_getUnused nprc = projection_round_stakes_getUnused oprc /\
    projection_round_stakes_getIsValidatorStakeCompleted nprc = 
        projection_round_stakes_getIsValidatorStakeCompleted oprc /\
    projection_round_stakes_getRewards nprc = projection_round_stakes_getRewards oprc /\
    projection_round_stakes_getValidatorStake nprc = stakeSum (validatorStake ol or) /\
    projection_round_stakes_getHandledStakesAndRewards nprc =
    projection_round_stakes_getHandledStakesAndRewards oprc.

End Round_Stakes_conditions.
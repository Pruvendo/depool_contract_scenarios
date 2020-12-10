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
Require Export depoolContract.Scenarios.Common.RoundDefinitions.
Require Export depoolContract.Scenarios.Common.cutWithdrawalValueMove.
Require Export depoolContract.Scenarios.Common._returnOrReinvestForParticipant_attachedValueMove.

Definition stakeIsLost (r : RoundsBase_ι_Round) : bool :=
    completionReasonEqb
        (RoundsBase_ι_Round_ι_completionReason r)
        RoundsBase_ι_CompletionReasonP_ι_ValidatorIsPunished.

Definition lostFunds0 (r : RoundsBase_ι_Round) :=
    if stakeIsLost r then
        RoundsBase_ι_Round_ι_stake r -
        RoundsBase_ι_Round_ι_unused r -
        RoundsBase_ι_Round_ι_recoveredStake r
    else
        0.

Definition reward0 (r : RoundsBase_ι_Round) (s : RoundsBase_ι_StakeValue) :=
    if stakeIsLost r then 0
    else intMulDiv
            (stakeSum s)
            (RoundsBase_ι_Round_ι_rewards r)
            (RoundsBase_ι_Round_ι_stake r).

Definition newStake0 (r : RoundsBase_ι_Round)(s : RoundsBase_ι_StakeValue)(isValidator : bool) :=
    if stakeIsLost r
        then
            if isValidator
                then
                    RoundsBase_ι_StakeValue_ι_ordinary s -
                    intMin (RoundsBase_ι_StakeValue_ι_ordinary s) (lostFunds0 r)
                else intMulDiv
                    (
                        RoundsBase_ι_Round_ι_unused r +
                        RoundsBase_ι_Round_ι_recoveredStake r -
                        RoundsBase_ι_Round_ι_validatorRemainingStake r
                    )
                    (RoundsBase_ι_StakeValue_ι_ordinary s)
                    (
                        RoundsBase_ι_Round_ι_stake r -
                        RoundsBase_ι_Round_ι_validatorRemainingStake r
                    )
        else
            (RoundsBase_ι_StakeValue_ι_ordinary s) + reward0 r s.

Definition lostFunds1 (r : RoundsBase_ι_Round)(s : RoundsBase_ι_StakeValue)(isValidator : bool) :=
    if andb (stakeIsLost r) isValidator
        then    lostFunds0 r -
                intMin (RoundsBase_ι_StakeValue_ι_ordinary s) (lostFunds0 r)
        else
                lostFunds0 r.

Definition oldVesting (s : RoundsBase_ι_StakeValue) :=
    RoundsBase_ι_InvestParams_ι_amount (maybeGet (RoundsBase_ι_StakeValue_ι_vesting s)).

Definition hasVesting (s : RoundsBase_ι_StakeValue) :=
    isSome (RoundsBase_ι_StakeValue_ι_vesting s).

Definition newVesting (r : RoundsBase_ι_Round)(s : RoundsBase_ι_StakeValue)(isValidator : bool) :=
    if stakeIsLost r
        then
            if isValidator
                then
                    oldVesting s -
                    intMin (oldVesting s) (lostFunds1 r s isValidator)
                else
                    intMulDiv
                        (
                            RoundsBase_ι_Round_ι_unused r +
                            RoundsBase_ι_Round_ι_recoveredStake r -
                            RoundsBase_ι_Round_ι_validatorRemainingStake r
                        )
                        (oldVesting s)
                        (
                            RoundsBase_ι_Round_ι_stake r -
                            RoundsBase_ι_Round_ι_validatorRemainingStake r
                        )   
        else
            oldVesting s.

Definition lostFunds2 (r : RoundsBase_ι_Round)(s : RoundsBase_ι_StakeValue)(isValidator : bool) :=
    if andb (stakeIsLost r) isValidator
        then    lostFunds1 r s isValidator -
                intMin (oldVesting s) (lostFunds1 r s isValidator)
        else
                lostFunds1 r s isValidator.

Definition newVestingObject
    (r : RoundsBase_ι_Round)(s : RoundsBase_ι_StakeValue)(isValidator : bool) :=
    {$ (maybeGet (RoundsBase_ι_StakeValue_ι_vesting s)) with 
    RoundsBase_ι_InvestParams_ι_amount := newVesting r s isValidator $} .

Definition newVesting1
    (l : Ledger)(r : RoundsBase_ι_Round)(s : RoundsBase_ι_StakeValue)(isValidator : bool) :=
    if hasVesting s
    then newAmount l (newVestingObject r s isValidator)
    else newVesting r s isValidator.

Definition newVestingLastWithdrawalTime
    (l : Ledger)(r : RoundsBase_ι_Round)(s : RoundsBase_ι_StakeValue)(isValidator : bool) :=
    if hasVesting s
    then newLastWithdrawalTime l (newVestingObject r s isValidator)
    else 0.

Definition newStake1
    (l : Ledger)(r : RoundsBase_ι_Round)(s : RoundsBase_ι_StakeValue)(isValidator : bool) :=
    if hasVesting s
    then newStake0 r s isValidator + withdrawal l (newVestingObject r s isValidator)
    else newStake0 r s isValidator.

Definition reinvestParticipant (l : Ledger)(addr : XAddress) := 
    maybeGet ( eval_state (↓ ParticipantBase_Ф_fetchParticipant addr) l).

Definition newStake2
    (l : Ledger)(r : RoundsBase_ι_Round)(s : RoundsBase_ι_StakeValue)(isValidator : bool)
    (addr : XAddress) :=
    attachedValue_NewStake l (reinvestParticipant l addr) (newStake1 l r s isValidator).

Definition oldLock (s : RoundsBase_ι_StakeValue) :=
    RoundsBase_ι_InvestParams_ι_amount (maybeGet (RoundsBase_ι_StakeValue_ι_lock s)).

Definition newLock (r : RoundsBase_ι_Round)(s : RoundsBase_ι_StakeValue)(isValidator : bool) :=
    if stakeIsLost r
        then
            if isValidator
                then
                    oldLock s -
                    intMin (oldLock s) (lostFunds2 r s isValidator)
                else
                    intMulDiv
                        (
                            RoundsBase_ι_Round_ι_unused r +
                            RoundsBase_ι_Round_ι_recoveredStake r -
                            RoundsBase_ι_Round_ι_validatorRemainingStake r
                        )
                        (oldLock s)
                        (
                            RoundsBase_ι_Round_ι_stake r -
                            RoundsBase_ι_Round_ι_validatorRemainingStake r
                        )   
        else
            oldLock s.

Definition lostFunds3 (r : RoundsBase_ι_Round)(s : RoundsBase_ι_StakeValue)(isValidator : bool) :=
    if andb (stakeIsLost r) isValidator
        then    lostFunds2 r s isValidator -
                intMin (oldLock s) (lostFunds2 r s isValidator)
        else
                lostFunds2 r s isValidator.

Definition newLockObject
    (r : RoundsBase_ι_Round)(s : RoundsBase_ι_StakeValue)(isValidator : bool) :=
    {$ (maybeGet (RoundsBase_ι_StakeValue_ι_lock s)) with 
    RoundsBase_ι_InvestParams_ι_amount := newLock r s isValidator $} .
    

Definition _returnOrReinvestForParticipant_not_validator_less_stake
    (r2 : RoundsBase_ι_Round)(isValidator : bool) :=
    isValidator = false ->
    RoundsBase_ι_Round_ι_validatorRemainingStake r2 < RoundsBase_ι_Round_ι_stake r2.

(*************************************Result*******************************************)

Definition _returnOrReinvestForParticipant_round2_handledStakesAndRewards
    (l : Ledger)(r0 r2 : RoundsBase_ι_Round)(s : RoundsBase_ι_StakeValue)(isValidator : bool)
    (addr : XAddress) :=
    RoundsBase_ι_Round_ι_handledStakesAndRewards r2 +
    newStake0 r2 s isValidator +
    newVesting r2 s isValidator +
    newLock r2 s isValidator.

Definition _returnOrReinvestForParticipant_round2_validatorRemainingStake
    (l : Ledger)(r0 r2 : RoundsBase_ι_Round)(s : RoundsBase_ι_StakeValue)(isValidator : bool)
    (addr : XAddress) :=
    RoundsBase_ι_Round_ι_validatorRemainingStake r2 +
    if (andb (stakeIsLost r2) isValidator)
        then stakeSum (validatorStake l r2) -
            intMin (stakeSum (validatorStake l r2)) (lostFunds0 r2)
        else 0.

Definition _returnOrReinvestForParticipant_round0_stake
    (l : Ledger)(r0 r2 : RoundsBase_ι_Round)(s : RoundsBase_ι_StakeValue)(isValidator : bool)
    (addr : XAddress) :=
    if andb (DePoolLib_ι_Participant_ι_reinvest (reinvestParticipant l addr))
            (negb (poolClosed l))
        then RoundsBase_ι_Round_ι_stake r0 +
            newStake2 l r2 s isValidator addr + newVesting1 l r2 s isValidator + newLock r2 s isValidator
        else RoundsBase_ι_Round_ι_stake r0.

Definition _returnOrReinvestForParticipant_round0_stake_diff
    (l : Ledger)(r0 r2 : RoundsBase_ι_Round)(s : RoundsBase_ι_StakeValue)(isValidator : bool)
    (addr : XAddress) :=
    if andb (DePoolLib_ι_Participant_ι_reinvest (reinvestParticipant l addr))
            (negb (poolClosed l))
        then newStake2 l r2 s isValidator addr + newVesting1 l r2 s isValidator + newLock r2 s isValidator
        else 0.

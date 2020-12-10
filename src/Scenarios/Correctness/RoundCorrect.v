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
Require Export depoolContract.Scenarios.Correctness.StakeValueCorrect.
Require Export depoolContract.Scenarios.Correctness.LedgerCorrect.

Definition _roundCorrectNonNegative (r : RoundsBase_ι_Round) := 
    0 <= RoundsBase_ι_Round_ι_supposedElectedAt r /\
    0 <= RoundsBase_ι_Round_ι_unfreeze r /\
    0 <= RoundsBase_ι_Round_ι_participantQty r /\
    0 <= RoundsBase_ι_Round_ι_stake r /\
    0 <= RoundsBase_ι_Round_ι_rewards r /\
    0 <= RoundsBase_ι_Round_ι_unused r /\
    0 <= RoundsBase_ι_Round_ι_stakeHeldFor r /\
    0 <= RoundsBase_ι_Round_ι_recoveredStake r /\
    0 <= RoundsBase_ι_Round_ι_validatorStake r /\
    0 <= RoundsBase_ι_Round_ι_validatorRemainingStake r /\
    0 <= RoundsBase_ι_Round_ι_handledStakesAndRewards r.

Definition _roundCorrectStakeIsTheMost (r : RoundsBase_ι_Round) :=
    RoundsBase_ι_Round_ι_unused r +
    RoundsBase_ι_Round_ι_recoveredStake r
    <= RoundsBase_ι_Round_ι_stake r.

Definition _roundCorrectStakeSum (r : RoundsBase_ι_Round) :=
    fold_left Z.add (map stakeSum (map snd (RoundsBase_ι_Round_ι_stakes r))) 0 =
    RoundsBase_ι_Round_ι_stake r.

Definition _roundCorrectStakes (l : Ledger)(r : RoundsBase_ι_Round) :=
    Forall (StakeValueCorrectLocally l) (map snd (RoundsBase_ι_Round_ι_stakes r)).

Definition _roundValidatorRemainingStake (r : RoundsBase_ι_Round) :=
    RoundsBase_ι_Round_ι_validatorRemainingStake r <=
    RoundsBase_ι_Round_ι_unused r + RoundsBase_ι_Round_ι_recoveredStake r.

Definition _roundNoDupStakes (r : RoundsBase_ι_Round) :=
    NoDup (map fst (RoundsBase_ι_Round_ι_stakes r)).

Definition _roundValidatorRemainingStakeLessOrEqualValidatorStake
    (l : Ledger)(r : RoundsBase_ι_Round) :=
    RoundsBase_ι_Round_ι_validatorRemainingStake r <= stakeSum (validatorStake l r).

Definition _roundCorrectPrepoolingAndCompletionReasons
    (l : Ledger)(r : RoundsBase_ι_Round) :=
    RoundsBase_ι_Round_ι_step (roundPre0 l) = RoundsBase_ι_RoundStepP_ι_PrePooling /\
        (RoundsBase_ι_Round_ι_step r = RoundsBase_ι_RoundStepP_ι_PrePooling ->
        roundIn l r ->
        poolClosed l = false ->
        r = roundPre0 l
        ) /\
    RoundsBase_ι_Round_ι_completionReason (roundPre0 l) =
        RoundsBase_ι_CompletionReasonP_ι_Undefined.

Definition _roundCorrectPoolingAndCompletionReasons
    (l : Ledger)(r : RoundsBase_ι_Round) := poolClosed l = false -> (
    RoundsBase_ι_Round_ι_step (round0 l) = RoundsBase_ι_RoundStepP_ι_Pooling /\
        (RoundsBase_ι_Round_ι_step r = RoundsBase_ι_RoundStepP_ι_Pooling ->
        roundIn l r ->
        poolClosed l = false ->
        r = round0 l
        )) /\
    RoundsBase_ι_Round_ι_completionReason (round0 l) =
        RoundsBase_ι_CompletionReasonP_ι_Undefined.

Definition _roundCorrectWaitingValidatorRequestAndCompletionReasons
    (l : Ledger)(r : RoundsBase_ι_Round) :=
    RoundsBase_ι_Round_ι_step r = RoundsBase_ι_RoundStepP_ι_WaitingValidatorRequest ->
    roundIn l r ->
    (r = round1 l
            /\
    RoundsBase_ι_Round_ι_completionReason r =
        RoundsBase_ι_CompletionReasonP_ι_Undefined).

Definition _roundCorrectWaitingIfStakeAcceptedAndCompletionReasons
    (l : Ledger)(r : RoundsBase_ι_Round) :=
    RoundsBase_ι_Round_ι_step r = RoundsBase_ι_RoundStepP_ι_WaitingIfStakeAccepted ->
    roundIn l r ->
    (r = round1 l
            /\
    RoundsBase_ι_Round_ι_completionReason r =
        RoundsBase_ι_CompletionReasonP_ι_Undefined).

Definition _roundCorrectWaitingValidatorStartAndCompletionReasons
    (l : Ledger)(r : RoundsBase_ι_Round) :=
    RoundsBase_ι_Round_ι_step r = RoundsBase_ι_RoundStepP_ι_WaitingValidationStart ->
    roundIn l r ->
    ((r = round1 l \/ r = round2 l)
            /\
    RoundsBase_ι_Round_ι_completionReason r =
        RoundsBase_ι_CompletionReasonP_ι_Undefined).

Definition _roundCorrectWaitingIfValidatorWinsElectionsAndCompletionReasons
    (l : Ledger)(r : RoundsBase_ι_Round) :=
    RoundsBase_ι_Round_ι_step r = RoundsBase_ι_RoundStepP_ι_WaitingIfValidatorWinElections ->
    roundIn l r ->
    ((r = round1 l \/ r = round2 l)
            /\
    RoundsBase_ι_Round_ι_completionReason r =
        RoundsBase_ι_CompletionReasonP_ι_Undefined).

Definition _roundCorrectStepsAndCompletionReasons
    (l : Ledger)(r : RoundsBase_ι_Round) :=
    _roundCorrectPrepoolingAndCompletionReasons l r /\
    _roundCorrectPoolingAndCompletionReasons l r /\
    _roundCorrectWaitingValidatorRequestAndCompletionReasons l r /\
    _roundCorrectWaitingIfStakeAcceptedAndCompletionReasons l r /\
    _roundCorrectWaitingValidatorStartAndCompletionReasons l r /\
    _roundCorrectWaitingIfValidatorWinsElectionsAndCompletionReasons l r.

Definition roundCorrectLocally (l : Ledger)(r : RoundsBase_ι_Round) := 
    _roundCorrectNonNegative r /\
    _roundCorrectStakeIsTheMost r /\
    _roundCorrectStakeSum r /\
    _roundCorrectStakes l r /\
    _roundValidatorRemainingStake r /\
    _roundNoDupStakes r /\
    _roundValidatorRemainingStakeLessOrEqualValidatorStake l r /\
    ledgerCorrectLocally l /\
    _roundCorrectStepsAndCompletionReasons l r.

Definition roundCorrectGlobally (l : Ledger) := 
    StakeValueCorrectGlobally l /\ (
    forall r,
    roundIn l r /\
    roundCorrectLocally l r).

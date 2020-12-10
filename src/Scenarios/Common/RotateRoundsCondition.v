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

Definition updateRoundsCalled (l : Ledger)(ticktockCalled : Prop) :=
    ticktockCalled /\
    internalMessage l /\
    checkDePoolBalance l (msgValue l) (balance l).
    
Definition areElectionsStarted (l : Ledger) : Prop :=
    ((validationEnd l - electionsStartBefore l)%Z <= now l)%Z.

Definition areElectionsStopped (l : Ledger) := areElectionsStarted l /\
    RoundsBase_ι_Round_ι_vsetHashInElectionPhase (round1 l) <> currentValidator l.

Definition calcUnfreezeTime (l : Ledger) :=
    (validationStart l + stakesHeldFor l + ELECTOR_UNFREEZE_LAG l)%Z.

Definition roundObsolete (r : RoundsBase_ι_Round)(l : Ledger) :=
    RoundsBase_ι_Round_ι_vsetHashInElectionPhase r <> currentValidator l /\
    RoundsBase_ι_Round_ι_vsetHashInElectionPhase r <> prevValidator l.

Inductive timeToUnfreeze : Ledger -> RoundsBase_ι_Round -> Z -> Prop :=
    | timeToUnfreeze_now : forall l r now,
        convertUnfreezeTime l r = UnfreezeNow -> timeToUnfreeze l r now
    | timeToUnfreeze_At : forall l r u now, 
        convertUnfreezeTime l r = UnfreezeAt u ->
        u <= now ->
        timeToUnfreeze l r now
    .

Definition updateRound2ToCompleted_time_to_unfreeze_obsolete_round (l : Ledger)(r : RoundsBase_ι_Round)
: Prop :=
    roundObsolete r l /\
    timeToUnfreeze l (
        {$ r with RoundsBase_ι_Round_ι_unfreeze := (calcUnfreezeTime l) $}) (now l).

Definition updateRound2ToCompleted_time_to_unfreeze (l : Ledger)(r : RoundsBase_ι_Round) : Prop :=
    timeToUnfreeze l r (now l) \/
    updateRound2ToCompleted_time_to_unfreeze_obsolete_round l r.

Definition updateRound2ToCompleted_state_reason (l : Ledger)(r : RoundsBase_ι_Round) : Prop :=
    let roundState := RoundsBase_ι_Round_ι_step r in
    roundState = RoundsBase_ι_RoundStepP_ι_WaitingValidatorRequest
    \/ ((roundState = RoundsBase_ι_RoundStepP_ι_WaitingUnfreeze) /\
        RoundsBase_ι_Round_ι_completionReason r <> RoundsBase_ι_CompletionReasonP_ι_Undefined /\
        updateRound2ToCompleted_time_to_unfreeze l r).

Definition updateRound2ToCompleted (l : Ledger) : Prop :=
    updateRound2ToCompleted_state_reason l (round2 l) /\
    RoundsBase_ι_Round_ι_participantQty (round2 l) = 0%Z.

Definition rotate_round_conditions_logical (l : Ledger) :=
    allInsCorrect l /\
    areElectionsStopped l /\
        (RoundsBase_ι_Round_ι_step (round2 l) = RoundsBase_ι_RoundStepP_ι_WaitingValidatorRequest \/
        updateRound2ToCompleted l).

Definition rotate_round_conditions_full (l : Ledger)(ticktockCalled : Prop) := 
    updateRoundsCalled l ticktockCalled /\
    rotate_round_conditions_logical l /\
    noSelfDestruct l.

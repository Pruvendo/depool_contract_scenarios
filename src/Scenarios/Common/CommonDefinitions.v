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

Definition CRITICAL_THRESHOLD (l : Ledger) :=
    eval_state (↑12 ε DePoolContract_ι_CRITICAL_THRESHOLD) l.
Definition MAX_INT (l : Ledger) := eval_state (↑9 ε DePoolLib_ι_MAX_TIME) l.
Definition ELECTOR_UNFREEZE_LAG (l : Ledger) :=
    eval_state (↑9 ε DePoolLib_ι_ELECTOR_UNFREEZE_LAG) l .
Definition STAKE_FEE (l : Ledger) := eval_state (↑12 ε DePoolContract_ι_STAKE_FEE) l.
Definition MAX_MSG_PER_TR (l : Ledger) := eval_state (↑12 ε DePoolContract_ι_MAX_MSGS_PER_TR) l.
Definition PROXY_FEE (l : Ledger) := eval_state (↑9 ε DePoolLib_ι_PROXY_FEE) l.
Definition RET_OR_REINV_FEE (l : Ledger) := eval_state (↑12 ε DePoolContract_ι_RET_OR_REINV_FEE) l.

Definition m_minStake (l : Ledger) := eval_state (↑12 ε DePoolContract_ι_m_minStake) l.
Definition m_validatorWallet (l : Ledger) := eval_state (↑2 ε ValidatorBase_ι_m_validatorWallet) l.
Definition m_participantRewardFraction (l : Ledger) :=
    eval_state (↑12 ε DePoolContract_ι_m_participantRewardFraction) l.
Definition m_balanceThreshold (l : Ledger) :=
    eval_state (↑12 ε DePoolContract_ι_m_balanceThreshold) l.
Definition m_validatorAssurance (l : Ledger) :=
    eval_state (↑12 ε DePoolContract_ι_m_validatorAssurance) l.

Definition poolClosed (l : Ledger) := eval_state (↑12 ε DePoolContract_ι_m_poolClosed) l.

Definition totalStake (r : RoundsBase_ι_Round) : XInteger64 :=
    let unused := RoundsBase_ι_Round_ι_unused r in
    let stake := RoundsBase_ι_Round_ι_stake r in
    let rewards := RoundsBase_ι_Round_ι_rewards r in
    let recoveredStake := RoundsBase_ι_Round_ι_recoveredStake r in
    let handledStakesAndRewards := RoundsBase_ι_Round_ι_handledStakesAndRewards r in
    match  RoundsBase_ι_Round_ι_step r , RoundsBase_ι_Round_ι_completionReason r with
    | RoundsBase_ι_RoundStepP_ι_Completed , _ => 0
    | RoundsBase_ι_RoundStepP_ι_WaitingUnfreeze ,
        RoundsBase_ι_CompletionReasonP_ι_Undefined => unused
    | RoundsBase_ι_RoundStepP_ι_WaitingUnfreeze , _  
    | RoundsBase_ι_RoundStepP_ι_PrePooling , _ 
    | RoundsBase_ι_RoundStepP_ι_Pooling , _  
    | RoundsBase_ι_RoundStepP_ι_WaitingValidatorRequest , _ => stake
    | RoundsBase_ι_RoundStepP_ι_Completing ,
        RoundsBase_ι_CompletionReasonP_ι_ValidatorIsPunished =>
        unused + recoveredStake - handledStakesAndRewards
    |  RoundsBase_ι_RoundStepP_ι_Completing , _ => stake + rewards - handledStakesAndRewards 
    | _ , _ => unused
    end.

Definition totalParticipantsStake (l : Ledger) :=
    totalStake (eval_state (RoundsBase_Ф_getRoundPre0) l) +
    totalStake (eval_state (RoundsBase_Ф_getRound0) l) +
    totalStake (eval_state (RoundsBase_Ф_getRound1) l) +
    totalStake (eval_state (RoundsBase_Ф_getRound2) l).

Definition totalParticipantsStakeBut2 (l : Ledger) :=
    totalStake (eval_state (RoundsBase_Ф_getRoundPre0) l) +
    totalStake (eval_state (RoundsBase_Ф_getRound0) l) +
    totalStake (eval_state (RoundsBase_Ф_getRound1) l).

Definition checkDePoolBalance (l : Ledger)(msgValue balance : Z) :=
    (CRITICAL_THRESHOLD l + totalParticipantsStake l + msgValue <= balance)%Z.

Definition isEmptyRound (r : RoundsBase_ι_Round) : Prop := 
    RoundsBase_ι_Round_ι_step r = RoundsBase_ι_RoundStepP_ι_Completed \/
    RoundsBase_ι_Round_ι_stake r = 0.

Definition stakeSum (s : RoundsBase_ι_StakeValue) := 
    let ordinary := RoundsBase_ι_StakeValue_ι_ordinary s in
    let vesting := RoundsBase_ι_InvestParams_ι_amount (maybeGet (RoundsBase_ι_StakeValue_ι_vesting s)) in
    let lock := RoundsBase_ι_InvestParams_ι_amount (maybeGet (RoundsBase_ι_StakeValue_ι_lock s)) in
    ordinary + vesting + lock .

Definition notEmptyRound (r : RoundsBase_ι_Round) : Prop := 
    RoundsBase_ι_Round_ι_step r <> RoundsBase_ι_RoundStepP_ι_Completed /\
    RoundsBase_ι_Round_ι_stake r <> 0.

Inductive UnfreezeTime :=
| UnfreezeNever
| UnfreezeNow
| UnfreezeAt : Z -> UnfreezeTime .

Definition convertUnfreezeTime (l : Ledger)(r : RoundsBase_ι_Round) := 
    let unfreezeTime := RoundsBase_ι_Round_ι_unfreeze r in
    if unfreezeTime =? MAX_INT l then UnfreezeNever
    else if unfreezeTime =? 0 then UnfreezeNow
    else UnfreezeAt unfreezeTime.

Definition ownerCall (l : Ledger) := eval_state (↑16 ε VMState_ι_msg_pubkey) l =
    eval_state tvm_pubkey l.
Definition selfCall (l : Ledger) := eval_state (↑16 ε VMState_ι_msg_sender) l =
    eval_state (↑16 ε VMState_ι_address) l.
Definition ownerOrSelfCall (l : Ledger) := ownerCall l \/ selfCall l.
Definition internalMessage (l : Ledger) := eval_state (↑16 ε VMState_ι_msg_sender) l <> 0.
Definition onlyValidatorContract (l : Ledger) := eval_state (↑16 ε VMState_ι_msg_sender) l =
    m_validatorWallet l.

Definition balance (l : Ledger) := eval_state (↑16 ε VMState_ι_balance) l.
Definition msgValue (l : Ledger) := eval_state (↑16 ε VMState_ι_msg_value) l.
Definition msgSender (l : Ledger) := eval_state (↑16 ε VMState_ι_msg_sender) l.
Definition now (l : Ledger) := eval_state tvm_now l.

Definition curValidatorData (l : Ledger) :=
    let withError := eval_state (↓ ConfigParamsBase_Ф_getCurValidatorData) l in
    errorMapDefault Datatypes.id withError default.
Definition currentValidator (l : Ledger) := fst (fst (curValidatorData l)).
Definition validationStart (l : Ledger) := snd (fst (curValidatorData l)).
Definition validationEnd (l : Ledger) := snd (curValidatorData l).
Definition curValidatorDataCorrect (l : Ledger) :=
    errorValueIsError (eval_state (↓ ConfigParamsBase_Ф_getCurValidatorData) l) = false.

Definition roundTimeParams (l : Ledger) :=
    let withError := eval_state (↓ ConfigParamsBase_Ф_roundTimeParams) l in
    errorMapDefault Datatypes.id withError default.
Definition validatorsElectedFor (l : Ledger) := fst (fst (fst (roundTimeParams l))).
Definition electionsStartBefore (l : Ledger) := snd (fst (fst (roundTimeParams l))).
Definition electionsEndBefore (l : Ledger) := snd (fst (roundTimeParams l)).
Definition stakesHeldFor (l : Ledger) := snd (roundTimeParams l).
Definition roundTimeParamsCorrect (l : Ledger) :=
    errorValueIsError (eval_state (↓ ConfigParamsBase_Ф_roundTimeParams) l) = false.

Definition prevValidator (l : Ledger) := 
    let withError := eval_state (↓ ConfigParamsBase_Ф_getPrevValidatorHash) l in
    errorMapDefault Datatypes.id withError default.
Definition prevValidatorCorrect (l : Ledger) :=
    errorValueIsError (eval_state (↓ ConfigParamsBase_Ф_getPrevValidatorHash) l) = false.

Definition allInsCorrect (l : Ledger) :=
    curValidatorDataCorrect l /\ roundTimeParamsCorrect l /\ prevValidatorCorrect l.

Definition roundPre0 (l : Ledger) := eval_state (↓ RoundsBase_Ф_getRoundPre0) l.
Definition round0 (l : Ledger) := eval_state (↓ RoundsBase_Ф_getRound0) l.
Definition round1 (l : Ledger) := eval_state (↓ RoundsBase_Ф_getRound1) l.
Definition round2 (l : Ledger) := eval_state (↓ RoundsBase_Ф_getRound2) l.

Definition roundIn (l : Ledger) (r : RoundsBase_ι_Round) :=
    r = roundPre0 l \/
    r = round0 l \/
    r = round1 l \/
    r = round2 l.

Definition roundsSame (r1 r2 : RoundsBase_ι_Round) :=
    RoundsBase_ι_Round_ι_id r1 = RoundsBase_ι_Round_ι_id r2.

Definition noSelfDestruct (l : Ledger) :=
    eval_state (↑12 ε DePoolContract_ι_m_poolClosed) l = false \/
    notEmptyRound (roundPre0 l) \/
    notEmptyRound (round0 l) \/
    notEmptyRound (round1 l) \/
    notEmptyRound (round2 l).

Definition valueIn {K V} (v : V)(m : XHMap K V) :=
    In v (map snd m).

Definition investParamsInRound (r : RoundsBase_ι_Round) (i : RoundsBase_ι_InvestParams) :=
    exists s,
        In s (RoundsBase_ι_Round_ι_stakes r) /\
        (
            (maybeGet (RoundsBase_ι_StakeValue_ι_vesting (snd s)) = i /\
            isSome (RoundsBase_ι_StakeValue_ι_vesting (snd s)) = true) \/
            (maybeGet (RoundsBase_ι_StakeValue_ι_lock (snd s)) = i /\
            isSome (RoundsBase_ι_StakeValue_ι_lock (snd s)) = true)
        ).

Definition stakeValueInRound (r : RoundsBase_ι_Round) (s : RoundsBase_ι_StakeValue) :=
    valueIn s (RoundsBase_ι_Round_ι_stakes r).

Definition investParamsIn (l : Ledger) (i : RoundsBase_ι_InvestParams) :=
    exists r ,
        roundIn l r /\
        investParamsInRound r i.

Definition stakeValueIn (l : Ledger) (s : RoundsBase_ι_StakeValue) :=
    exists r ,
        roundIn l r /\
        stakeValueInRound r s.

Definition participantIn (l : Ledger)(p : DePoolLib_ι_Participant) := 
    exists addr, (
    isSome (eval_state ( ParticipantBase_Ф_fetchParticipant addr) l) = true /\
    maybeGet (eval_state ( ParticipantBase_Ф_fetchParticipant addr) l) = p).

Definition participantOut (l : Ledger)(p : DePoolLib_ι_Participant) := 
    forall addr,
    isSome (eval_state ( ParticipantBase_Ф_fetchParticipant addr) l) = true ->
    ~ maybeGet (eval_state ( ParticipantBase_Ф_fetchParticipant addr) l) = p.

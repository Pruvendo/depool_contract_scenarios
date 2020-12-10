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

Definition _ledgerCorrectPositive (l : Ledger) := 
    0 < MAX_MSG_PER_TR l /\
    0 < m_minStake l /\
    0 < now l /\
    0 < PROXY_FEE l /\
    0 < RET_OR_REINV_FEE l /\
    0 < m_participantRewardFraction l /\
    0 <= msgValue l /\
    0 < m_validatorAssurance l /\
    0 < ELECTOR_UNFREEZE_LAG l.

Definition _ledgerCorrectRoundsIds (l : Ledger) := 
    forall r, roundIn l r ->
    eval_state (RoundsBase_Ф_fetchRound (RoundsBase_ι_Round_ι_id r)) l = Some r.

Definition _ledgerCorrectNotTooLarge (l : Ledger) :=
    m_participantRewardFraction l <= 100.

Definition _ledgerCorrectBalance (l : Ledger) := 
    0 < m_balanceThreshold l /\
    m_balanceThreshold l <= balance l.

Definition ledgerCorrectLocally (l : Ledger) := 
    _ledgerCorrectPositive l /\
    _ledgerCorrectRoundsIds l /\
    _ledgerCorrectNotTooLarge l /\
    _ledgerCorrectBalance l.
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
Require Export depoolContract.Scenarios.Correctness.LedgerCorrect.

Definition _investParamsNowCorrect (l : Ledger)(i  : RoundsBase_ι_InvestParams) :=
    RoundsBase_ι_InvestParams_ι_lastWithdrawalTime i <= now l.

Definition _investParamsPositive (i  : RoundsBase_ι_InvestParams) :=
    0 < RoundsBase_ι_InvestParams_ι_lastWithdrawalTime i /\
    0 < RoundsBase_ι_InvestParams_ι_withdrawalPeriod i /\
    0 < RoundsBase_ι_InvestParams_ι_withdrawalValue i /\
    isStdAddrWithoutAnyCast (RoundsBase_ι_InvestParams_ι_owner i) = true.

Definition _investParamsAmountMinStake (l : Ledger)(i  : RoundsBase_ι_InvestParams) :=
    0 = RoundsBase_ι_InvestParams_ι_amount i \/
    m_minStake l <= RoundsBase_ι_InvestParams_ι_amount i.

(*Important!!! This condition is for global correctness only, locally may be violated*)
Definition _investParamsAmountPositive (i  : RoundsBase_ι_InvestParams) :=
    0 < RoundsBase_ι_InvestParams_ι_amount i.

Definition investParamsCorrectLocally (l : Ledger)(i  : RoundsBase_ι_InvestParams) :=
    ledgerCorrectLocally l /\
    _investParamsNowCorrect l i /\
    _investParamsPositive i /\
    _investParamsAmountMinStake l i.

Definition investParamsCorrectGlobally (l : Ledger) := forall i,
    investParamsIn l i ->
    (
        investParamsCorrectLocally l i /\
        _investParamsAmountPositive i
    ).

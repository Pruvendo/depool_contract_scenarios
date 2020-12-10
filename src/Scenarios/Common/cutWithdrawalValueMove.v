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

Definition periodQty (l : Ledger)(i : RoundsBase_ι_InvestParams) :=
    (now l - (RoundsBase_ι_InvestParams_ι_lastWithdrawalTime i)) /
    (RoundsBase_ι_InvestParams_ι_withdrawalPeriod i).

Definition initialWithdrawal (l: Ledger)(i : RoundsBase_ι_InvestParams) :=
    intMin ((periodQty l i) * (RoundsBase_ι_InvestParams_ι_withdrawalValue i))
        (RoundsBase_ι_InvestParams_ι_amount i).

Definition withdrawal (l: Ledger)(i : RoundsBase_ι_InvestParams) :=
    if RoundsBase_ι_InvestParams_ι_amount i - initialWithdrawal l i <? m_minStake l
    then RoundsBase_ι_InvestParams_ι_amount i
    else initialWithdrawal l i.

Definition newAmount (l: Ledger)(i : RoundsBase_ι_InvestParams) :=
    RoundsBase_ι_InvestParams_ι_amount i - withdrawal l i.

Definition newLastWithdrawalTime (l: Ledger)(i : RoundsBase_ι_InvestParams) :=
    (RoundsBase_ι_InvestParams_ι_lastWithdrawalTime i) +
    periodQty l i * RoundsBase_ι_InvestParams_ι_withdrawalPeriod i.
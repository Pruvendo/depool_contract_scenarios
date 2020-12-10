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
Require Export depoolContract.Scenarios.Correctness.InvestParamsCorrect.

Definition _StakeValueCorrectOrdinaryNonNegative (s : RoundsBase_ι_StakeValue) :=
    0 <= RoundsBase_ι_StakeValue_ι_ordinary s.

Definition _StakeValueCorrectVestingLocally (l : Ledger)(s : RoundsBase_ι_StakeValue) :=
    isSome (RoundsBase_ι_StakeValue_ι_vesting s) = false \/
    investParamsCorrectLocally l (maybeGet (RoundsBase_ι_StakeValue_ι_vesting s)).

Definition _StakeValueCorrectLockLocally (l : Ledger)(s : RoundsBase_ι_StakeValue) :=
    isSome (RoundsBase_ι_StakeValue_ι_lock s) = false \/
    investParamsCorrectLocally l (maybeGet (RoundsBase_ι_StakeValue_ι_lock s)).

Definition StakeValueCorrectLocally (l : Ledger)(s : RoundsBase_ι_StakeValue) :=
    _StakeValueCorrectOrdinaryNonNegative s /\
    _StakeValueCorrectVestingLocally l s /\
    _StakeValueCorrectLockLocally l s /\
    ledgerCorrectLocally l.

Definition _StakeValueCorrectPositiveSum (l : Ledger)(s : RoundsBase_ι_StakeValue) :=
    0 < stakeSum s.

Definition StakeValueCorrectGlobally (l : Ledger) :=
    investParamsCorrectGlobally l /\
    (forall s, stakeValueIn l s ->
        StakeValueCorrectLocally l s /\
        _StakeValueCorrectPositiveSum l s
    ).
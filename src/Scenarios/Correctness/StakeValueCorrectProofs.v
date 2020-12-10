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
Require Export Coq.micromega.Lia.

Local Open Scope struct_scope.
Local Open Scope Z_scope.
Local Open Scope solidity_scope.
Require Import Lists.List.
Import ListNotations.
Local Open Scope list_scope.

Set Typeclasses Iterative Deepening.
Set Typeclasses Depth 100.

Require Export depoolContract.Scenarios.Common.CommonDefinitions.
Require Export depoolContract.Scenarios.Correctness.StakeValueCorrect.

Lemma sv_vesting_not_negative : forall l s,
    StakeValueCorrectLocally l s ->
    0 <= RoundsBase_ι_InvestParams_ι_amount
        (maybeGet (RoundsBase_ι_StakeValue_ι_vesting s)).
Proof.
intros. unfold StakeValueCorrectLocally in H. inversion_clear H.
inversion_clear H1. unfold _StakeValueCorrectVestingLocally in H.
inversion H. destruct (RoundsBase_ι_StakeValue_ι_vesting s). inversion_clear H1.
simpl. unfold xInt0. lia. inversion H1. inversion_clear H4. inversion_clear H6.
inversion_clear H7. setoid_rewrite <- H6. lia. apply Z.le_trans with (m := m_minStake l).
inversion H3. unfold _ledgerCorrectPositive in H7. decompose [and] H7. lia. assumption.
Qed.

Lemma sv_lock_not_negative : forall l s,
    StakeValueCorrectLocally l s ->
    0 <= RoundsBase_ι_InvestParams_ι_amount
        (maybeGet (RoundsBase_ι_StakeValue_ι_lock s)).
Proof.
intros. unfold StakeValueCorrectLocally in H. inversion_clear H.
inversion_clear H1. unfold _StakeValueCorrectLockLocally in H2.
inversion H2. destruct (RoundsBase_ι_StakeValue_ι_lock s). inversion_clear H1. inversion H4.
inversion_clear H4. decompose [and] H5. unfold _investParamsAmountMinStake in H8.
inversion_clear H8. setoid_rewrite <- H6. lia. apply Z.le_trans with (m := m_minStake l).
unfold ledgerCorrectLocally in H1. unfold _ledgerCorrectPositive in H1. decompose [and] H1. lia.
assumption. compute. intros. discriminate.
Qed.

Lemma stakeSum_not_negative : forall l s,
    StakeValueCorrectLocally l s ->
    0 <= stakeSum s.
Proof.
intros. unfold stakeSum. repeat apply Z.add_nonneg_nonneg. unfold StakeValueCorrectLocally in H.
inversion_clear H. assumption. apply sv_vesting_not_negative with (l := l). assumption.
apply sv_lock_not_negative with (l := l). assumption.
Qed.
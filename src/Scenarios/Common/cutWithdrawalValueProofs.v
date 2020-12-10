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
Require Export depoolContract.Scenarios.Common.cutWithdrawalValueMove.
Require Export depoolContract.Scenarios.Common.UtilProofs.
Require Export depoolContract.Scenarios.Correctness.InvestParamsCorrect.

Definition _cutWithdrawalValueMoveUpdatedInvestParams
    (i : RoundsBase_ι_InvestParams)
    (a : Z)
    (lwt : Z) :=
    {$ {$ i with RoundsBase_ι_InvestParams_ι_amount := a $}
            with RoundsBase_ι_InvestParams_ι_lastWithdrawalTime := lwt $}.

Definition cutWithdrawalValueMoveUpdatedInvestParams (l : Ledger) (i : RoundsBase_ι_InvestParams) :=
    _cutWithdrawalValueMoveUpdatedInvestParams
    i
    (newAmount l i)
    (newLastWithdrawalTime l i).

Lemma cutWithdrawalValueMove_locallyCorrect : forall l i,
    investParamsCorrectLocally l i ->
    investParamsCorrectLocally l (cutWithdrawalValueMoveUpdatedInvestParams l i).
Proof.
intros. unfold cutWithdrawalValueMoveUpdatedInvestParams.
unfold _cutWithdrawalValueMoveUpdatedInvestParams. unfold investParamsCorrectLocally in *.
split. inversion H. assumption.
inversion H. clear H. unfold _investParamsNowCorrect in *. simpl.
unfold newLastWithdrawalTime. unfold periodQty. unfold _investParamsPositive in H1.
inversion_clear H1. inversion_clear H2. inversion_clear H1. inversion_clear H4.
split.
apply Z.le_trans with (n := (RoundsBase_ι_InvestParams_ι_lastWithdrawalTime
i +
(now l -
RoundsBase_ι_InvestParams_ι_lastWithdrawalTime
 i) /
RoundsBase_ι_InvestParams_ι_withdrawalPeriod
i *
RoundsBase_ι_InvestParams_ι_withdrawalPeriod i))
(p := now l)
(m := RoundsBase_ι_InvestParams_ι_lastWithdrawalTime
i +
(now l -
RoundsBase_ι_InvestParams_ι_lastWithdrawalTime
 i)). apply Z.add_le_mono_l. rewrite Z.mul_comm. apply Z_mult_div_ge. lia. lia.
unfold _investParamsPositive in *. inversion_clear H5.
split. split. simpl. unfold newLastWithdrawalTime. apply Z.add_pos_nonneg. assumption.
apply Z.mul_nonneg_nonneg. unfold periodQty. unfold _investParamsNowCorrect in H0.
apply Z.div_pos. apply Z.le_0_sub. assumption. assumption. apply Z.lt_le_incl. assumption.
split. simpl. assumption. split. simpl. assumption. simpl. assumption.
unfold _investParamsAmountMinStake. simpl. unfold newAmount. unfold withdrawal.
case_eq(RoundsBase_ι_InvestParams_ι_amount i - initialWithdrawal l i <? m_minStake l).
intros. setoid_rewrite H5. left. lia. intros. setoid_rewrite H5. right. apply Z.ltb_ge.
assumption.
Qed.

Lemma cutWithdrawalValueMove_withdrawal_plus_newAmount : forall l i,
    newAmount l i + withdrawal l i = RoundsBase_ι_InvestParams_ι_amount i.
Proof.
intros. unfold newAmount. lia.
Qed.

Lemma cutWithdrawalValueMove_lastWithdrawalTime_later: forall l i,
    investParamsCorrectLocally l i ->
    RoundsBase_ι_InvestParams_ι_lastWithdrawalTime i <= newLastWithdrawalTime l i.
Proof.
intros. unfold newLastWithdrawalTime. apply Z.le_sub_le_add_l. rewrite Z.sub_diag.
unfold investParamsCorrectLocally in H. inversion_clear H. inversion_clear H1.
inversion_clear H2. apply Z.mul_nonneg_nonneg. unfold _investParamsPositive in H1.
inversion_clear H1. inversion_clear H4. inversion_clear H5.
unfold periodQty. apply Z.div_pos. unfold _investParamsNowCorrect in H0.
apply Zle_minus_le_0. assumption. assumption. apply Z.lt_le_incl.
inversion_clear H1. inversion_clear H4. assumption.
Qed.

Lemma cutWithdrawalValueMove_withdrawal_pos: forall l i,
    investParamsCorrectLocally l i ->
    0 < periodQty l i ->
    0 < RoundsBase_ι_InvestParams_ι_amount i ->
    0 < withdrawal l i.
Proof.
intros. unfold withdrawal. case_eq
(RoundsBase_ι_InvestParams_ι_amount i - initialWithdrawal l i <? m_minStake l).
intros. setoid_rewrite H2. assumption. intros. setoid_rewrite H2.
unfold investParamsCorrectLocally in H. inversion_clear H. unfold initialWithdrawal.
unfold cutWithdrawalValueMove.DePoolFuncs.intMin. simpl.
case_eq(periodQty l i * RoundsBase_ι_InvestParams_ι_withdrawalValue i <=?
RoundsBase_ι_InvestParams_ι_amount i) ; intros ; setoid_rewrite H. apply Z.mul_pos_pos.
assumption. inversion_clear H4. inversion_clear H6. unfold _investParamsPositive in H4.
inversion_clear H4. inversion_clear H8. inversion_clear H9. assumption. assumption.
Qed.

Lemma cutWithdrawalValueMove_lastWithdrawalTime_strictly_later: forall l i,
    investParamsCorrectLocally l i ->
    0 < withdrawal l i ->
    RoundsBase_ι_InvestParams_ι_lastWithdrawalTime i < newLastWithdrawalTime l i.
Proof.
intros. unfold investParamsCorrectLocally in H. inversion_clear H. inversion_clear H2.
unfold withdrawal in H0. unfold _investParamsNowCorrect in H. inversion_clear H3.
unfold _investParamsPositive in H2. inversion_clear H2. inversion_clear H5.
inversion_clear H6.
unfold newLastWithdrawalTime. rewrite Z.add_comm. apply Zlt_0_minus_lt. rewrite Z.add_simpl_r.
rewrite Z.mul_comm. apply Z.mul_pos_pos. assumption.
case_eq( RoundsBase_ι_InvestParams_ι_amount i - initialWithdrawal l i <? m_minStake l).
intros. setoid_rewrite H6 in H0. apply Zlt_is_lt_bool in H6.
case_eq(initialWithdrawal l i <? 0). intros. apply Zlt_is_lt_bool in H8.
unfold initialWithdrawal in H8. unfold cutWithdrawalValueMove.DePoolFuncs.intMin in H8.
simpl in H8.
case_eq(periodQty l i * RoundsBase_ι_InvestParams_ι_withdrawalValue i <=?
RoundsBase_ι_InvestParams_ι_amount i). intros. setoid_rewrite H9 in H8. apply Z.lt_mul_0 in H8.
inversion H8. inversion H10. unfold periodQty in H11. apply div_neg_neg_or in H11.
inversion H11. apply -> Z.lt_sub_0 in H13. apply Zlt_not_le in H13. contradiction.
apply Zlt_not_le in H13. apply Z.lt_le_incl in H2. contradiction. inversion H10. assumption.
intros. setoid_rewrite H9 in H8. apply Zlt_not_le in H8. apply Z.lt_le_incl in H0. contradiction.
intros. apply neg_lt0b_ge0 in H8. inversion H8. rewrite H9 in H6. rewrite Z.sub_0_r in H6.
unfold _investParamsAmountMinStake in H4. inversion H4. setoid_rewrite <- H10 in H0. lia.
apply Zlt_not_le in H6. contradiction. unfold initialWithdrawal in H9.
unfold cutWithdrawalValueMove.DePoolFuncs.intMin in H9. simpl in H9.
case_eq(periodQty l i * RoundsBase_ι_InvestParams_ι_withdrawalValue i <=?
    RoundsBase_ι_InvestParams_ι_amount i). intros. setoid_rewrite H10 in H9.
apply Z.mul_pos_cancel_r in H9 ; assumption. intros. apply Z.leb_gt in H10.
apply Z.lt_trans with (n := 0)
                    (m:= RoundsBase_ι_InvestParams_ι_amount i)
                    (p := periodQty l i * RoundsBase_ι_InvestParams_ι_withdrawalValue i)
                    in H0.
apply Z.mul_pos_cancel_r in H0 ; assumption. assumption. intros. setoid_rewrite H6 in H0.
unfold initialWithdrawal in H0. unfold cutWithdrawalValueMove.DePoolFuncs.intMin in H0.
simpl in H0.
case_eq(periodQty l i * RoundsBase_ι_InvestParams_ι_withdrawalValue i <=?
    RoundsBase_ι_InvestParams_ι_amount i). intros. setoid_rewrite H8 in H0.
apply Z.mul_pos_cancel_r in H0 ; assumption. intros. setoid_rewrite H8 in H0. apply Z.leb_gt in H8.
apply Z.lt_trans with (n := 0)
                    (m:= RoundsBase_ι_InvestParams_ι_amount i)
                    (p := periodQty l i * RoundsBase_ι_InvestParams_ι_withdrawalValue i)
                    in H0.
apply Z.mul_pos_cancel_r in H0 ; assumption. assumption.
Qed.
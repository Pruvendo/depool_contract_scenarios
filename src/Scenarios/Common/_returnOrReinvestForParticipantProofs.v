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
Require Export depoolContract.Scenarios.Common._returnOrReinvestForParticipant_attachedValueMove.
Require Export depoolContract.Scenarios.Common._returnOrReinvestForParticipant_attachedValueProofs.
Require Export depoolContract.Scenarios.Common._returnOrReinvestForParticipantMove.
Require Export depoolContract.Scenarios.Correctness.RoundCorrect.
Require Export depoolContract.Scenarios.Correctness.RoundCorrectProofs.

Lemma _returnOrReinvestForParticipant_lostFunds0_non_neg :
    forall l r2,
    roundCorrectLocally l r2 ->
    0 <= lostFunds0 r2.
Proof.
intros. unfold lostFunds0. case_eq (stakeIsLost r2) ; intros.
rewrite <- Z.sub_add_distr. apply Zle_minus_le_0. unfold roundCorrectLocally in H.
inversion_clear H. inversion_clear H2. unfold _roundCorrectStakeIsTheMost in H.
assumption. lia.
Qed.

Lemma _returnOrReinvestForParticipant_lostFunds1_non_neg :
    forall l r2 s isValidator ,
    roundCorrectLocally l r2 ->
    0 <= lostFunds1 r2 s isValidator.
Proof.
intros. unfold lostFunds1. case_eq (andb (stakeIsLost r2) isValidator) ; intros.
apply sub_sub_min_non_neg_r.
apply _returnOrReinvestForParticipant_lostFunds0_non_neg with (l := l).
assumption.
apply _returnOrReinvestForParticipant_lostFunds0_non_neg with (l := l).
assumption.
Qed.

Lemma _returnOrReinvestForParticipant_lostFunds2_non_neg :
    forall l r2 s isValidator ,
    roundCorrectLocally l r2 ->
    0 <= lostFunds2 r2 s isValidator.
Proof.
intros. unfold lostFunds2. case_eq (andb (stakeIsLost r2) isValidator) ; intros.
apply sub_sub_min_non_neg_r.
apply _returnOrReinvestForParticipant_lostFunds1_non_neg with (l := l).
assumption.
apply _returnOrReinvestForParticipant_lostFunds1_non_neg with (l := l).
assumption.
Qed.

Lemma _returnOrReinvestForParticipant_less_reward_than_stake_if_punished :
    forall l r0 r2 s isValidator addr ,
    roundCorrectLocally l r2 ->
    stakeValueInRound r2 s ->
    _returnOrReinvestForParticipant_not_validator_less_stake r2 isValidator ->
    stakeIsLost r2 = true ->
    _returnOrReinvestForParticipant_round2_handledStakesAndRewards l r0 r2 s isValidator addr <=
    RoundsBase_ι_Round_ι_handledStakesAndRewards r2 + RoundsBase_ι_Round_ι_stake r2.
Proof.
intros. unfold _returnOrReinvestForParticipant_round2_handledStakesAndRewards.
rewrite <- Z.add_assoc. rewrite <- Z.add_assoc. apply Z.add_le_mono_l.
rewrite Z.add_assoc. unfold newStake0. unfold newLock. unfold newVesting. setoid_rewrite H2.
assert (StakeValueCorrectLocally l s).
apply stakeValueCorrectLocally_for_each_stake with (r := r2) ; assumption.
remember H3 as SVCL. clear HeqSVCL. unfold StakeValueCorrectLocally in H3.
inversion_clear H3. inversion_clear H5. remember H as RCL. clear HeqRCL.
unfold roundCorrectLocally in H. inversion_clear H. inversion_clear H7.
inversion_clear H8. inversion_clear H9. inversion_clear H10.
unfold _roundValidatorRemainingStake in H11.
case_eq(isValidator) ; intros.
apply add_le_3 with  (m1 := RoundsBase_ι_StakeValue_ι_ordinary s)
                     (m2 := oldVesting s)
                     (m3 := oldLock s) ; try apply Z.le_sub_nonneg ; try apply min_gte_0 .
unfold _StakeValueCorrectOrdinaryNonNegative in H3. assumption.
apply _returnOrReinvestForParticipant_lostFunds0_non_neg with (l := l). assumption.
unfold oldVesting. apply sv_vesting_not_negative with (l := l). assumption.
apply _returnOrReinvestForParticipant_lostFunds1_non_neg with (l := l). assumption.
unfold oldLock. apply sv_lock_not_negative with (l := l). assumption.
apply _returnOrReinvestForParticipant_lostFunds2_non_neg with (l := l). assumption.
unfold oldVesting. unfold oldLock.
apply ordinary_vesting_lock_less_than_stake_svr with (l := l) ; assumption.
apply add_le_3 with  (m1 := RoundsBase_ι_StakeValue_ι_ordinary s)
                     (m2 := oldVesting s)
                     (m3 := oldLock s) ; try apply intMulDiv_le_full.
apply Zle_minus_le_0. assumption. unfold _StakeValueCorrectOrdinaryNonNegative in H3.
assumption. apply Z.sub_le_mono_r. unfold _roundCorrectStakeIsTheMost in H.
assumption. replace 0 with (RoundsBase_ι_Round_ι_stake r2 - RoundsBase_ι_Round_ι_stake r2).
apply Z.sub_lt_mono_l.
unfold _returnOrReinvestForParticipant_not_validator_less_stake in H1. apply H1 in H10.
assumption. lia. unfold _roundValidatorRemainingStake in H9. apply Zle_minus_le_0.
assumption. unfold oldVesting. unfold _StakeValueCorrectVestingLocally in H3.
apply sv_vesting_not_negative with (l := l). assumption.
apply Z.sub_le_mono_r. unfold _roundCorrectStakeIsTheMost in H. assumption.
replace 0 with (RoundsBase_ι_Round_ι_stake r2 - RoundsBase_ι_Round_ι_stake r2).
apply Z.sub_lt_mono_l.
unfold _returnOrReinvestForParticipant_not_validator_less_stake in H1. apply H1 in H10.
assumption. lia. unfold _roundValidatorRemainingStake in H9. apply Zle_minus_le_0.
assumption. unfold oldLock. unfold _StakeValueCorrectLockLocally in H6.
apply sv_lock_not_negative with (l := l). assumption.
apply Z.sub_le_mono_r. unfold _roundCorrectStakeIsTheMost in H. assumption.
unfold _returnOrReinvestForParticipant_not_validator_less_stake in H1. apply H1 in H10.
lia. apply ordinary_vesting_lock_less_than_stake_svr with (l := l); assumption.
Qed.

Lemma _returnOrReinvestForParticipant_round2_validatorRemainingStake_non_neg :
    forall l r0 r2 s isValidator addr,
    roundCorrectLocally l r2 ->
    RoundsBase_ι_Round_ι_validatorRemainingStake r2 <=
    _returnOrReinvestForParticipant_round2_validatorRemainingStake l r0 r2 s isValidator addr.
Proof.
intros. unfold _returnOrReinvestForParticipant_round2_validatorRemainingStake.
setoid_rewrite <- Z.add_0_r at 1. apply Zplus_le_compat_l.
case_eq((stakeIsLost r2 && isValidator)%bool) ; intros. apply sub_sub_min_non_neg_l.
apply validatorStake_non_neg. assumption. lia.
Qed.

Lemma _returnOrReinvestForParticipant_round2_validatorRemainingStake_diff_le_validator_stake :
    forall l r0 r2 s isValidator addr,
    roundCorrectLocally l r2 ->
    _returnOrReinvestForParticipant_round2_validatorRemainingStake l r0 r2 s isValidator addr -
    RoundsBase_ι_Round_ι_validatorRemainingStake r2 <= stakeSum (validatorStake l r2).
Proof.
intros. unfold _returnOrReinvestForParticipant_round2_validatorRemainingStake.
rewrite Z.add_comm. rewrite <- Z.add_sub_assoc. rewrite Z.sub_diag. rewrite Z.add_0_r.
case_eq(andb (stakeIsLost r2) isValidator) ; intros. apply Z.le_sub_nonneg. apply min_gte_0.
apply validatorStake_non_neg. assumption.
apply _returnOrReinvestForParticipant_lostFunds0_non_neg with (l := l). assumption.
apply validatorStake_non_neg. assumption.
Qed.

Lemma _returnOrReinvestForParticipant_newStake0_not_neg :
    forall l r2 s isValidator,
    roundCorrectLocally l r2 ->
    stakeValueInRound r2 s ->
    0 < RoundsBase_ι_Round_ι_stake r2 ->
    _returnOrReinvestForParticipant_not_validator_less_stake r2 isValidator ->
    0 <= newStake0 r2 s isValidator.
Proof.
intros. unfold newStake0. case_eq(stakeIsLost r2) ; intros. case_eq(isValidator) ; intros.
apply Zle_minus_le_0. apply min_lte_l. apply intMulDiv_ge_0. unfold roundCorrectLocally in H.
decompose [and] H. unfold _roundValidatorRemainingStake in H6. apply Zle_minus_le_0.
assumption. apply stakeValueCorrectLocally_for_each_stake with(s := s) in H.
unfold StakeValueCorrectLocally in H. inversion_clear H.
unfold _StakeValueCorrectOrdinaryNonNegative in H3. assumption. assumption.
unfold _returnOrReinvestForParticipant_not_validator_less_stake in H1.
apply H2 in H4. lia. apply Z.add_nonneg_nonneg.
apply stakeValueCorrectLocally_for_each_stake with(s := s) in H.
unfold StakeValueCorrectLocally in H. inversion_clear H. assumption. assumption.
unfold reward0. setoid_rewrite H3. apply intMulDiv_ge_0.
apply stakeSum_not_negative with (l := l).
apply stakeValueCorrectLocally_for_each_stake with(s := s) in H ; assumption.
unfold roundCorrectLocally in H. inversion_clear H. unfold _roundCorrectNonNegative in H4.
decompose [and] H4. assumption. assumption.
Qed.

Lemma _returnOrReinvestForParticipant_oldVesting_not_neg :
    forall l (s : RoundsBase_ι_StakeValue),
    StakeValueCorrectLocally l s ->
    0 <= oldVesting s.
Proof.
intros. unfold oldVesting. apply sv_vesting_not_negative with (l := l). assumption.
Qed.

Lemma _returnOrReinvestForParticipant_oldLock_not_neg :
    forall l (s : RoundsBase_ι_StakeValue),
    StakeValueCorrectLocally l s ->
    0 <= oldLock s.
Proof.
intros. unfold oldLock. apply sv_lock_not_negative with (l := l). assumption.
Qed.

Lemma _returnOrReinvestForParticipant_newVesting_not_neg :
    forall l r2 s isValidator,
    roundCorrectLocally l r2 ->
    stakeValueInRound r2 s ->
    _returnOrReinvestForParticipant_not_validator_less_stake r2 isValidator ->
    0 <= newVesting r2 s isValidator.
Proof.
intros. unfold newVesting. case_eq (stakeIsLost r2) ; intros. case_eq(isValidator) ; intros.
apply Zle_minus_le_0. apply min_lte_l. remember H. clear Heqr. unfold roundCorrectLocally in H.
decompose [and] H. apply intMulDiv_ge_0. unfold _roundCorrectStakeIsTheMost in H5.
apply Zle_minus_le_0. assumption.
apply stakeValueCorrectLocally_for_each_stake with(s := s) in H.
apply _returnOrReinvestForParticipant_oldVesting_not_neg with (l := l). assumption. assumption.
unfold _returnOrReinvestForParticipant_not_validator_less_stake in H1. apply H1 in H3. lia.
apply _returnOrReinvestForParticipant_oldVesting_not_neg with (l := l).
apply stakeValueCorrectLocally_for_each_stake with(s := s) in H ; assumption.
Qed.

Lemma _returnOrReinvestForParticipant_newStake1_not_neg :
    forall l r2 s isValidator,
    roundCorrectLocally l r2 ->
    stakeValueInRound r2 s ->
    0 < RoundsBase_ι_Round_ι_stake r2 ->
    _returnOrReinvestForParticipant_not_validator_less_stake r2 isValidator ->
    0 <= newStake1 l r2 s isValidator.
Proof.
intros. unfold newStake1. case_eq(hasVesting s) ; intro HV. apply Z.add_nonneg_nonneg.
apply _returnOrReinvestForParticipant_newStake0_not_neg with (l := l) ; assumption.
unfold withdrawal.
case_eq(RoundsBase_ι_InvestParams_ι_amount (newVestingObject r2 s isValidator) -
initialWithdrawal l (newVestingObject r2 s isValidator) <? m_minStake l) ; intros ;
setoid_rewrite H3 ; unfold newVestingObject ; simpl.
apply _returnOrReinvestForParticipant_newVesting_not_neg with (l := l) ; assumption.
unfold initialWithdrawal. apply min_gte_0. apply Z.mul_nonneg_nonneg.
unfold periodQty. apply Z.div_pos. simpl. apply Zle_minus_le_0.
apply stakeValueCorrectLocally_for_each_stake with(s := s) in H.
unfold StakeValueCorrectLocally in H. decompose [and] H.
unfold _StakeValueCorrectVestingLocally in H6. inversion_clear H6.
assert (maybeGet (RoundsBase_ι_StakeValue_ι_vesting s) = default).
apply isSome_false_default. apply H7. setoid_rewrite H6. simpl.
unfold ledgerCorrectLocally in H8. unfold _ledgerCorrectPositive in H8.
decompose [and] H8. unfold xInt0. lia. unfold investParamsCorrectLocally in H7.
decompose [and] H7. unfold _investParamsNowCorrect in H10. assumption. assumption. simpl.
apply stakeValueCorrectLocally_for_each_stake with(s := s) in H.
unfold StakeValueCorrectLocally in H. decompose [and] H.
unfold _StakeValueCorrectVestingLocally in H6. inversion_clear H6.
unfold hasVesting in HV. setoid_rewrite HV in H7. discriminate.
unfold investParamsCorrectLocally in H7. decompose [and] H7.
unfold _investParamsPositive in H9. decompose [and] H9. assumption. assumption.
simpl.
apply stakeValueCorrectLocally_for_each_stake with(s := s) in H.
unfold StakeValueCorrectLocally in H. decompose [and] H.
unfold _StakeValueCorrectVestingLocally in H6. inversion_clear H6.
unfold hasVesting in HV. setoid_rewrite HV in H7. discriminate.
unfold investParamsCorrectLocally in H7. decompose [and] H7.
unfold _investParamsPositive in H9. decompose [and] H9. apply Z.lt_le_incl. assumption.
assumption. simpl. apply _returnOrReinvestForParticipant_newVesting_not_neg with (l := l) ;
assumption.
apply _returnOrReinvestForParticipant_newStake0_not_neg with(l := l) ; assumption.
Qed.

Lemma _returnOrReinvestForParticipant_newStake2_not_neg :
    forall l r2 s isValidator addr,
    roundCorrectLocally l r2 ->
    stakeValueInRound r2 s ->
    participantCorrectLocally (reinvestParticipant l addr) ->
    0 < RoundsBase_ι_Round_ι_stake r2 ->
    _returnOrReinvestForParticipant_not_validator_less_stake r2 isValidator ->
    0 <= newStake2 l r2 s isValidator addr.
Proof.
intros. unfold newStake2. remember attachedValue_attachedValue_plus_NewStake. clear Heqe.
remember (reinvestParticipant l addr) as p. set (s1 := newStake1 l r2 s isValidator).
remember H1 as PCL. clear HeqPCL. apply e with(l := l)(stake := s1) in H1.
assert(attachedValue_NewStake l p s1 = 1 + s1 - attachedValue l p s1) by lia.
setoid_rewrite H4. clear H4. clear e. apply Zle_minus_le_0.
apply attachedValue_attachedValue_lt_1_plus_s. unfold s1.
apply _returnOrReinvestForParticipant_newStake1_not_neg ; try assumption.
unfold s1. apply _returnOrReinvestForParticipant_newStake1_not_neg ; assumption.
Qed.

Lemma _returnOrReinvestForParticipant_newVesting1_not_neg :
    forall l r2 s isValidator,
    roundCorrectLocally l r2 ->
    stakeValueInRound r2 s ->
    _returnOrReinvestForParticipant_not_validator_less_stake r2 isValidator ->
    0 <= newVesting1 l r2 s isValidator.
Proof.
intros. unfold newVesting1. case_eq (hasVesting s) ; intros. unfold newAmount. unfold newVestingObject.
simpl. unfold withdrawal. simpl.
case_eq (newVesting r2 s isValidator - initialWithdrawal l
  {$_returnOrReinvestForParticipantMove.CommonModelProofs.DePoolSpec.LedgerClass.SolidityNotations.maybeGet
      (RoundsBase_ι_StakeValue_ι_vesting s)
  with RoundsBase_ι_InvestParams_ι_amount := newVesting r2 s isValidator $} <?
m_minStake l) ; intros ; setoid_rewrite H3. lia.
remember(initialWithdrawal l
{$_returnOrReinvestForParticipantMove.CommonModelProofs.DePoolSpec.LedgerClass.SolidityNotations.maybeGet
    (RoundsBase_ι_StakeValue_ι_vesting s)
with RoundsBase_ι_InvestParams_ι_amount := newVesting r2 s isValidator $}). setoid_rewrite <- Heqx.
apply Z.ltb_ge in H3. apply stakeValueCorrectLocally_for_each_stake with(s := s) in H.
unfold StakeValueCorrectLocally in H. decompose [and] H. unfold ledgerCorrectLocally in H8.
unfold _ledgerCorrectPositive in H8. decompose [and] H8. lia. assumption.
apply _returnOrReinvestForParticipant_newVesting_not_neg with(l := l) ; assumption.
Qed.

Lemma _returnOrReinvestForParticipant_newLock_not_neg :
    forall l r2 (s : RoundsBase_ι_StakeValue) isValidator,
    roundCorrectLocally l r2 ->
    stakeValueInRound r2 s ->
    _returnOrReinvestForParticipant_not_validator_less_stake r2 isValidator ->
    0 <= newLock r2 s isValidator.
Proof.
intros. unfold newLock. case_eq (stakeIsLost r2) ; intros. case_eq (isValidator) ; intros.
apply Zle_minus_le_0. apply min_lte_l. apply intMulDiv_ge_0. unfold roundCorrectLocally in H.
decompose [and] H. unfold _roundValidatorRemainingStake in H8. apply Zle_minus_le_0. assumption.
apply _returnOrReinvestForParticipant_oldLock_not_neg with (l := l).
apply stakeValueCorrectLocally_for_each_stake with(s := s) in H ; assumption.
unfold roundCorrectLocally in H. decompose [and] H.
unfold _returnOrReinvestForParticipant_not_validator_less_stake in H1. apply H1 in H3. lia.
apply _returnOrReinvestForParticipant_oldLock_not_neg with (l := l).
apply stakeValueCorrectLocally_for_each_stake with(s := s) in H ; assumption.
Qed.

Lemma _returnOrReinvestForParticipant_round0_stake_diff_non_neg :
    forall l r0 r2 s isValidator addr,
    roundCorrectLocally l r2 ->
    stakeValueInRound r2 s ->
    participantCorrectLocally (reinvestParticipant l addr) ->
    0 < RoundsBase_ι_Round_ι_stake r2 ->
    _returnOrReinvestForParticipant_not_validator_less_stake r2 isValidator ->
    RoundsBase_ι_Round_ι_stake r0 <=
    _returnOrReinvestForParticipant_round0_stake l r0 r2 s isValidator addr.
Proof.
intros. unfold _returnOrReinvestForParticipant_round0_stake.
case_eq(andb (DePoolLib_ι_Participant_ι_reinvest (reinvestParticipant l addr))
    (negb (poolClosed l))) ; intros. setoid_rewrite <- Z.add_0_r at 1.
setoid_rewrite <- Z.add_assoc at 1. setoid_rewrite <- Z.add_assoc. apply Zplus_le_compat_l.
setoid_rewrite Z.add_assoc. repeat apply Z.add_nonneg_nonneg.
apply _returnOrReinvestForParticipant_newStake2_not_neg with (l := l) ; assumption.
apply _returnOrReinvestForParticipant_newVesting1_not_neg ; assumption.
apply _returnOrReinvestForParticipant_newLock_not_neg with(l := l) ; assumption.
apply Z.le_refl.
Qed.

Lemma _returnOrReinvestForParticipant_round0_stake_diff_eq :
    forall l r0 r2 s isValidator addr,
    _returnOrReinvestForParticipant_round0_stake l r0 r2 s isValidator addr  =
    _returnOrReinvestForParticipant_round0_stake_diff l r0 r2 s isValidator addr
    + RoundsBase_ι_Round_ι_stake r0.
Proof.
intros. unfold _returnOrReinvestForParticipant_round0_stake.
unfold _returnOrReinvestForParticipant_round0_stake_diff.
case_eq((DePoolLib_ι_Participant_ι_reinvest
(reinvestParticipant l addr) &&
negb (poolClosed l))%bool); intros ; lia.
Qed.

Lemma _returnOrReinvestForParticipant_lte_reward_than_currect_stake_punished :
forall l r0 r2 s isValidator addr ,
    stakeIsLost r2 = true ->
    roundCorrectLocally l r2 ->
    stakeValueInRound r2 s ->
    _returnOrReinvestForParticipant_not_validator_less_stake r2 isValidator ->
    _returnOrReinvestForParticipant_round2_handledStakesAndRewards l r0 r2 s isValidator addr <=
    RoundsBase_ι_Round_ι_handledStakesAndRewards r2 + stakeSum s.
Proof.
intro l. intro r0. intro r2. intro s. intro isValidator.  intro addr. intro SLT.
intros. unfold _returnOrReinvestForParticipant_round2_handledStakesAndRewards.
setoid_rewrite <- Z.add_assoc at 1. setoid_rewrite <- Z.add_assoc at 1.
apply Zplus_le_compat_l. setoid_rewrite Z.add_assoc. unfold newStake0. unfold newVesting.
unfold newLock. case_eq (stakeIsLost r2) ; intros. case_eq (isValidator) ; intros.
remember H as RCL. clear HeqRCL.
apply stakeValueCorrectLocally_for_each_stake with(s := s) in H.
unfold StakeValueCorrectLocally in H. decompose [and] H. clear H.
apply add_le_3 with
    (m1 := RoundsBase_ι_StakeValue_ι_ordinary s)
    (m2 := oldVesting s)
    (m3 := oldLock s) ; try apply Z.le_sub_nonneg ; try apply min_gte_0.
assumption.
apply _returnOrReinvestForParticipant_lostFunds0_non_neg with (l:=l). assumption.
unfold _StakeValueCorrectVestingLocally in H6. inversion_clear H6.
assert (maybeGet (RoundsBase_ι_StakeValue_ι_vesting s) = default).
apply isSome_false_default. assumption. unfold oldVesting. setoid_rewrite H6. simpl.
unfold xInt0. lia. unfold oldVesting. unfold investParamsCorrectLocally in H.
decompose [and] H. unfold _investParamsAmountMinStake in H11. inversion_clear H11.
setoid_rewrite <- H10. lia. apply Z.le_trans with (m := m_minStake l).
unfold ledgerCorrectLocally in H8. unfold _ledgerCorrectPositive in H8.
decompose [and] H8. lia. assumption.
apply _returnOrReinvestForParticipant_lostFunds1_non_neg with (l:=l). assumption.
apply _returnOrReinvestForParticipant_oldLock_not_neg with (l:=l).
apply stakeValueCorrectLocally_for_each_stake with(s := s) in RCL ; assumption.
apply _returnOrReinvestForParticipant_lostFunds2_non_neg with (l:=l). assumption.
unfold oldVesting. unfold oldLock. unfold stakeSum. apply Z.le_refl. assumption.
apply add_le_3 with
    (m1 := RoundsBase_ι_StakeValue_ι_ordinary s)
    (m2 := oldVesting s)
    (m3 := oldLock s) ; try apply intMulDiv_le_full.
unfold roundCorrectLocally in H. decompose [and] H.
unfold _roundValidatorRemainingStake in H8. apply Zle_minus_le_0. assumption.
apply stakeValueCorrectLocally_for_each_stake with(s := s) in H.
unfold StakeValueCorrectLocally in H. decompose [and] H. assumption. assumption.
apply Z.sub_le_mono_r. unfold roundCorrectLocally in H. decompose [and] H.
unfold _roundCorrectStakeIsTheMost in H6. assumption.
unfold _returnOrReinvestForParticipant_not_validator_less_stake in H1.
apply H1 in H3. lia.
apply Zle_minus_le_0. unfold roundCorrectLocally in H. decompose [and] H.
unfold _roundValidatorRemainingStake in H8. assumption.
apply _returnOrReinvestForParticipant_oldVesting_not_neg with (l := l).
apply stakeValueCorrectLocally_for_each_stake with(s := s) in H. assumption.
assumption.
apply Z.sub_le_mono_r. unfold roundCorrectLocally in H. decompose [and] H.
unfold _roundCorrectStakeIsTheMost in H6. assumption.
unfold _returnOrReinvestForParticipant_not_validator_less_stake in H1.
apply H1 in H3. lia.
apply Zle_minus_le_0. unfold roundCorrectLocally in H. decompose [and] H.
unfold _roundValidatorRemainingStake in H8. assumption.
apply _returnOrReinvestForParticipant_oldLock_not_neg with (l := l).
apply stakeValueCorrectLocally_for_each_stake with(s := s) in H. assumption.
assumption.
apply Z.sub_le_mono_r. unfold roundCorrectLocally in H. decompose [and] H.
unfold _roundCorrectStakeIsTheMost in H6. assumption.
unfold _returnOrReinvestForParticipant_not_validator_less_stake in H1.
apply H1 in H3. lia.
unfold oldVesting. unfold oldLock. unfold stakeSum. apply Z.le_refl.
congruence.
Qed.
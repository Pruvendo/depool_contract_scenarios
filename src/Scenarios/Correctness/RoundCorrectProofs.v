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
Require Export depoolContract.Scenarios.Common.UtilProofs.
Require Export depoolContract.Scenarios.Correctness.RoundCorrect.
Require Export depoolContract.Scenarios.Correctness.StakeValueCorrectProofs.
Require Export depoolContract.Scenarios.Correctness.LedgerCorrectGlobal.

Lemma stakeValueCorrectLocally_for_each_stake_value :
    forall l r s,
    In s (RoundsBase_ι_Round_ι_stakes r) ->
    roundCorrectLocally l r ->
    StakeValueCorrectLocally l (snd s).
Proof.
intros. inversion H0. inversion_clear H2. inversion_clear H4. inversion_clear H5.
unfold _roundCorrectStakes in H4. apply -> ForAll_map in H4.
assert ((StakeValueCorrectLocally l ∘ snd) s = StakeValueCorrectLocally l (snd s))
by auto. rewrite <- H5.
apply (Forall_In (l :=(RoundsBase_ι_Round_ι_stakes r))) ; assumption.
Qed.

Lemma stakeValueCorrectLocally_for_each_stake :
    forall l r s,
    roundCorrectLocally l r ->
    stakeValueInRound r s ->
    StakeValueCorrectLocally l s.
Proof.
intros. unfold stakeValueInRound in H0. unfold valueIn in H0.
apply in_map_exists in H0. inversion_clear H0. inversion_clear H1.
rewrite H2. apply stakeValueCorrectLocally_for_each_stake_value with (r := r) ;
assumption.
Qed.

Lemma vesting_less_than_stake : forall l r s,
    In s (RoundsBase_ι_Round_ι_stakes r) ->
    roundCorrectLocally l r ->
    RoundsBase_ι_InvestParams_ι_amount
        (maybeGet (RoundsBase_ι_StakeValue_ι_vesting (snd s))) <=
    RoundsBase_ι_Round_ι_stake r.
Proof.
intros.
assert (StakeValueCorrectLocally l (snd s)) by
(apply stakeValueCorrectLocally_for_each_stake_value with (r := r) ; assumption).
remember H0 as rCL. clear HeqrCL.
unfold roundCorrectLocally in H0. inversion_clear H0. inversion_clear H3.
inversion_clear H4.
unfold _roundCorrectStakeSum in H3. setoid_rewrite <- H3.
apply Z.le_trans with (m := stakeSum (snd s)). unfold stakeSum.
setoid_rewrite Z.add_comm at 2.
replace (RoundsBase_ι_InvestParams_ι_amount
(maybeGet (RoundsBase_ι_StakeValue_ι_vesting (snd s)))) with
(RoundsBase_ι_InvestParams_ι_amount
(maybeGet (RoundsBase_ι_StakeValue_ι_vesting (snd s))) + 0).
rewrite <- Z.add_assoc. apply Zplus_le_compat_l.
apply Z.add_nonneg_nonneg. unfold StakeValueCorrectLocally in H1.
inversion_clear H1. unfold _StakeValueCorrectOrdinaryNonNegative in H4.
assumption. apply sv_lock_not_negative with (l := l). assumption. lia.
apply element_less_sum. unfold non_neg_zlist. apply ForAll_map. apply ForAll_map.
apply Forall_forall. intros.
assert (StakeValueCorrectLocally l (snd x)).
apply stakeValueCorrectLocally_for_each_stake_value with (r := r). assumption.
assumption. unfold compose. simpl. unfold stakeSum.
repeat apply Z.add_nonneg_nonneg. unfold StakeValueCorrectLocally in H6.
inversion_clear H6. unfold _StakeValueCorrectOrdinaryNonNegative in H7. assumption.
apply sv_vesting_not_negative with (l := l). assumption.
apply sv_lock_not_negative with (l := l). assumption. apply in_map. apply in_map.
assumption.
Qed.

Lemma vesting_less_than_stake_svr : forall l r s,
    stakeValueInRound r s ->
    roundCorrectLocally l r ->
    RoundsBase_ι_InvestParams_ι_amount
        (maybeGet (RoundsBase_ι_StakeValue_ι_vesting s)) <=
    RoundsBase_ι_Round_ι_stake r.
Proof.
intros. unfold stakeValueInRound in H. unfold valueIn in H.
apply in_map_exists in H. inversion H. inversion_clear H1. setoid_rewrite H3.
apply vesting_less_than_stake with(l := l); assumption.
Qed.

Lemma vesting_plus_ordinary_less_than_stake : forall l r s,
    In s (RoundsBase_ι_Round_ι_stakes r) ->
    roundCorrectLocally l r ->
    RoundsBase_ι_InvestParams_ι_amount
        (maybeGet (RoundsBase_ι_StakeValue_ι_vesting (snd s)))
        + RoundsBase_ι_StakeValue_ι_ordinary (snd s) <=
    RoundsBase_ι_Round_ι_stake r.
Proof.
intros.
assert (StakeValueCorrectLocally l (snd s)) by
(apply stakeValueCorrectLocally_for_each_stake_value with (r := r) ; assumption).
remember H0 as rCL. clear HeqrCL. unfold roundCorrectLocally in H0.
inversion_clear H0. inversion_clear H3. inversion_clear H4.
unfold _roundCorrectStakeSum in H3. setoid_rewrite <- H3.
apply Z.le_trans with (m := stakeSum (snd s)). unfold stakeSum.
rewrite Z.add_comm. replace
(RoundsBase_ι_StakeValue_ι_ordinary (snd s) +
RoundsBase_ι_InvestParams_ι_amount
  (maybeGet (RoundsBase_ι_StakeValue_ι_vesting (snd s)))) with
(RoundsBase_ι_StakeValue_ι_ordinary (snd s) +
RoundsBase_ι_InvestParams_ι_amount
  (maybeGet (RoundsBase_ι_StakeValue_ι_vesting (snd s))) + 0).
apply Zplus_le_compat_l. apply sv_lock_not_negative with (l := l). assumption. lia.
apply element_less_sum.  unfold non_neg_zlist. apply ForAll_map. apply ForAll_map.
apply Forall_forall. intros.
assert (StakeValueCorrectLocally l (snd x)).
apply stakeValueCorrectLocally_for_each_stake_value with (r := r). assumption.
assumption. unfold compose. simpl. unfold stakeSum.
repeat apply Z.add_nonneg_nonneg. unfold StakeValueCorrectLocally in H6.
inversion_clear H6. unfold _StakeValueCorrectOrdinaryNonNegative in H7.
assumption. apply sv_vesting_not_negative with (l := l). assumption.
apply sv_lock_not_negative with (l := l). assumption. apply in_map.
apply in_map. assumption.
Qed.

Lemma vesting_plus_ordinary_less_than_stake_svr : forall l r s,
    stakeValueInRound r s ->
    roundCorrectLocally l r ->
    RoundsBase_ι_InvestParams_ι_amount
        (maybeGet (RoundsBase_ι_StakeValue_ι_vesting s))
        + RoundsBase_ι_StakeValue_ι_ordinary s <=
    RoundsBase_ι_Round_ι_stake r.
Proof.
intros. unfold stakeValueInRound in H. unfold valueIn in H.
apply in_map_exists in H. inversion H. inversion_clear H1. setoid_rewrite H3.
apply vesting_plus_ordinary_less_than_stake with(l := l); assumption.
Qed.

Lemma lock_less_than_stake : forall l r s,
    In s (RoundsBase_ι_Round_ι_stakes r) ->
    roundCorrectLocally l r ->
    RoundsBase_ι_InvestParams_ι_amount
        (maybeGet (RoundsBase_ι_StakeValue_ι_lock (snd s))) <=
    RoundsBase_ι_Round_ι_stake r.
Proof.
intros.
assert (StakeValueCorrectLocally l (snd s)) by
(apply stakeValueCorrectLocally_for_each_stake_value with (r := r) ; assumption).
remember H1 as rCL. clear HeqrCL. remember H0 as rRL. clear HeqrRL.
unfold roundCorrectLocally in H0. inversion_clear H0. inversion_clear H3.
inversion_clear H4.
unfold _roundCorrectStakeSum in H3. setoid_rewrite <- H3.
apply Z.le_trans with (m := stakeSum (snd s)). unfold stakeSum.
setoid_rewrite Z.add_comm at 2.
replace (RoundsBase_ι_InvestParams_ι_amount
(maybeGet (RoundsBase_ι_StakeValue_ι_lock (snd s)))) with
(RoundsBase_ι_InvestParams_ι_amount
(maybeGet (RoundsBase_ι_StakeValue_ι_lock (snd s))) + 0).
setoid_rewrite Z.add_comm at 2. apply Zplus_le_compat_l.
apply Z.add_nonneg_nonneg. unfold StakeValueCorrectLocally in H1.
inversion_clear H1. unfold _StakeValueCorrectOrdinaryNonNegative in H4.
apply sv_vesting_not_negative with (l := l). assumption.
unfold StakeValueCorrectLocally in rCL. inversion_clear rCL.
unfold _StakeValueCorrectOrdinaryNonNegative in H4. assumption. lia.
apply element_less_sum. unfold non_neg_zlist. apply ForAll_map. apply ForAll_map.
apply Forall_forall. intros.
assert (StakeValueCorrectLocally l (snd x)).
apply stakeValueCorrectLocally_for_each_stake_value with (r := r). assumption.
assumption. unfold compose. simpl. unfold stakeSum.
repeat apply Z.add_nonneg_nonneg. unfold StakeValueCorrectLocally in H6.
inversion_clear H6. unfold _StakeValueCorrectOrdinaryNonNegative in H7. assumption.
apply sv_vesting_not_negative with (l := l). assumption.
apply sv_lock_not_negative with (l := l). assumption. apply in_map. apply in_map.
assumption.
Qed.

Lemma lock_less_than_stake_svr : forall l r s,
    stakeValueInRound r s ->
    roundCorrectLocally l r ->
    RoundsBase_ι_InvestParams_ι_amount
        (maybeGet (RoundsBase_ι_StakeValue_ι_lock s)) <=
    RoundsBase_ι_Round_ι_stake r.
Proof.
intros. unfold stakeValueInRound in H. unfold valueIn in H.
apply in_map_exists in H. inversion H. inversion_clear H1. setoid_rewrite H3.
apply lock_less_than_stake with(l := l); assumption.
Qed.

Lemma vesting_lock_less_than_stake : forall l r s,
    In s (RoundsBase_ι_Round_ι_stakes r) ->
    roundCorrectLocally l r ->

    RoundsBase_ι_InvestParams_ι_amount
        (maybeGet (RoundsBase_ι_StakeValue_ι_vesting (snd s))) +
    RoundsBase_ι_InvestParams_ι_amount
        (maybeGet (RoundsBase_ι_StakeValue_ι_lock (snd s))) <=
    RoundsBase_ι_Round_ι_stake r.
Proof.
intros.
assert (StakeValueCorrectLocally l (snd s)) by
(apply stakeValueCorrectLocally_for_each_stake_value with (r := r) ; assumption).
remember H1 as rCL. clear HeqrCL. remember H0 as rRL. clear HeqrRL.
unfold roundCorrectLocally in H0. inversion_clear H0. inversion_clear H3.
inversion_clear H4.
unfold _roundCorrectStakeSum in H3. setoid_rewrite <- H3.
apply Z.le_trans with (m := stakeSum (snd s)). unfold stakeSum.
setoid_rewrite <- Z.add_assoc. rewrite <- Z.add_0_l at 1. apply Z.add_le_mono_r.
unfold StakeValueCorrectLocally in H1. inversion_clear H1.
unfold _StakeValueCorrectOrdinaryNonNegative in H4. assumption.
apply element_less_sum. unfold non_neg_zlist. apply ForAll_map. apply ForAll_map.
apply Forall_forall. intros.
assert (StakeValueCorrectLocally l (snd x)).
apply stakeValueCorrectLocally_for_each_stake_value with (r := r). assumption.
assumption. unfold compose. simpl. unfold stakeSum.
repeat apply Z.add_nonneg_nonneg. unfold StakeValueCorrectLocally in H6.
inversion_clear H6. unfold _StakeValueCorrectOrdinaryNonNegative in H7. assumption.
apply sv_vesting_not_negative with (l := l). assumption.
apply sv_lock_not_negative with (l := l). assumption. apply in_map. apply in_map.
assumption.
Qed.

Lemma vesting_lock_less_than_stake_svr : forall l r s,
    stakeValueInRound r s ->
    roundCorrectLocally l r ->
    RoundsBase_ι_InvestParams_ι_amount
        (maybeGet (RoundsBase_ι_StakeValue_ι_vesting s)) +
    RoundsBase_ι_InvestParams_ι_amount
        (maybeGet (RoundsBase_ι_StakeValue_ι_lock s)) <=
    RoundsBase_ι_Round_ι_stake r.
Proof.
intros. unfold stakeValueInRound in H. unfold valueIn in H.
apply in_map_exists in H. inversion H. inversion_clear H1. setoid_rewrite H3.
apply vesting_lock_less_than_stake with(l := l); assumption.
Qed.

Lemma ordinary_vesting_lock_less_than_stake : forall l r s,
    In s (RoundsBase_ι_Round_ι_stakes r) ->
    roundCorrectLocally l r ->
    RoundsBase_ι_StakeValue_ι_ordinary (snd s) +
    RoundsBase_ι_InvestParams_ι_amount
        (maybeGet (RoundsBase_ι_StakeValue_ι_vesting (snd s))) +
    RoundsBase_ι_InvestParams_ι_amount
        (maybeGet (RoundsBase_ι_StakeValue_ι_lock (snd s))) <=
    RoundsBase_ι_Round_ι_stake r.
Proof.
intros.
assert (StakeValueCorrectLocally l (snd s)) by
(apply stakeValueCorrectLocally_for_each_stake_value with (r := r) ; assumption).
remember H1 as rCL. clear HeqrCL. remember H0 as rRL. clear HeqrRL.
unfold roundCorrectLocally in H0. inversion_clear H0. inversion_clear H3.
inversion_clear H4.
unfold _roundCorrectStakeSum in H3. setoid_rewrite <- H3.
apply Z.le_trans with (m := stakeSum (snd s)). unfold stakeSum.
apply Z.eq_le_incl. reflexivity.
apply element_less_sum. unfold non_neg_zlist. apply ForAll_map. apply ForAll_map.
apply Forall_forall. intros.
assert (StakeValueCorrectLocally l (snd x)).
apply stakeValueCorrectLocally_for_each_stake_value with (r := r). assumption.
assumption. unfold compose. simpl. unfold stakeSum.
repeat apply Z.add_nonneg_nonneg. unfold StakeValueCorrectLocally in H6.
inversion_clear H6. unfold _StakeValueCorrectOrdinaryNonNegative in H7. assumption.
apply sv_vesting_not_negative with (l := l). assumption.
apply sv_lock_not_negative with (l := l). assumption. apply in_map. apply in_map.
assumption.
Qed.

Lemma ordinary_vesting_lock_less_than_stake_svr : forall l r s,
    stakeValueInRound r s ->
    roundCorrectLocally l r ->
    RoundsBase_ι_StakeValue_ι_ordinary s +
    RoundsBase_ι_InvestParams_ι_amount
        (maybeGet (RoundsBase_ι_StakeValue_ι_vesting s)) +
    RoundsBase_ι_InvestParams_ι_amount
        (maybeGet (RoundsBase_ι_StakeValue_ι_lock s)) <=
    RoundsBase_ι_Round_ι_stake r.
Proof.
intros. unfold stakeValueInRound in H. unfold valueIn in H.
apply in_map_exists in H. inversion H. inversion_clear H1. setoid_rewrite H3.
apply ordinary_vesting_lock_less_than_stake with(l := l); assumption.
Qed.

Lemma rounds_globally_correct_allStakesAreNotEmpty : forall l r,
    ledgerCorrectGlobally l ->
    roundIn l r ->
    allStakesAreNotEmpty l r.
Proof.
intros. unfold ledgerCorrectGlobally in H. inversion_clear H. remember H0.
clear Heqr0. apply H2 in H0.
unfold roundCorrectGlobally in H0. inversion_clear H0.
unfold StakeValueCorrectGlobally in H. inversion_clear H.
unfold allStakesAreNotEmpty. apply Forall_forall. intros. unfold compose.
unfold stakeValueIn in H4.
assert((exists r : DePoolFuncs.DePoolSpec.LedgerClass.RoundsBase_ι_Round,
roundIn l r /\ stakeValueInRound r (snd x))). exists r. split. assumption.
unfold stakeValueInRound. unfold valueIn. apply in_map. assumption. apply H4 in H5.
inversion_clear H5. unfold _StakeValueCorrectPositiveSum in H7. assumption.
Qed.

Lemma validator_stake_not_empty_validator_exists : forall l r,
    roundCorrectLocally l r ->
    0 < stakeSum (validatorStake l r) ->
    isValidatorInRound l r = true.
Proof.
intros. unfold validatorStake in H0. unfold isValidatorInRound. unfold isSome.
unfold RoundDefinitions.CommonModelProofs.DePoolSpec.LedgerClass.SolidityNotations.maybeGet.
destruct RoundDefinitions.CommonModelProofs.DePoolSpec.LedgerClass.SolidityNotations.hmapFetchM.
reflexivity. compute in H0. inversion H0.
Qed.

Lemma isValidatorInRound_In: forall l r,
    isValidatorInRound l r = true <->
    (exists x,
    In x (RoundsBase_ι_Round_ι_stakes r) /\
    fst x = (m_validatorWallet l)).
Proof.
intros. split. intros. unfold isValidatorInRound in H.
unfold RoundDefinitions.CommonModelProofs.DePoolSpec.LedgerClass.SolidityNotations.hmapFetchM
in H. unfold isSome in H. apply matchOpt_exists in H. apply memberLookup in H.
unfold hmapIsMember in H. unfold xListIn in H. unfold listFunRec in H.
unfold xHMapKeys in H. unfold hmapFunRec in H. simpl in H.
remember ((RoundsBase_ι_Round_ι_stakes r)). clear Heqx.
induction x. inversion H. simpl in H. apply Bool.orb_prop in H. inversion_clear H.
apply Z.eqb_eq in H0. exists a. split. simpl. left. reflexivity. assumption.
apply IHx in H0. inversion_clear H0. inversion_clear H. exists x0. split. simpl. right.
assumption. assumption. unfold eqb. unfold boolEquivalence. simpl. intros. split; intros ;
apply Z.eqb_eq ; assumption.
intros. inversion_clear H. inversion_clear H0. unfold isValidatorInRound. unfold isSome.
apply matchOpt_exists. apply memberLookup. unfold eqb. unfold boolEquivalence. simpl. intros.
split; intros ; apply Z.eqb_eq ; assumption. unfold hmapIsMember. unfold xListIn.
unfold listFunRec. unfold xHMapKeys. unfold hmapFunRec. simpl.
remember (RoundsBase_ι_Round_ι_stakes r). clear Heqx0. induction x0. inversion H. simpl.
apply Bool.orb_true_intro. simpl in H. inversion_clear H. left. apply Z.eqb_eq.
rewrite H0. assumption. right. apply IHx0. assumption.
Qed.

Lemma validatorStake_exists_snd :
    forall l r x,
    roundCorrectLocally l r ->
    In x (RoundsBase_ι_Round_ι_stakes r) /\ fst x = m_validatorWallet l ->
    validatorStake l r = snd x.
Proof.
intros. unfold roundCorrectLocally in H. inversion_clear H. clear H1. inversion_clear H2.
clear H. inversion_clear H1. clear H. inversion_clear H2. clear H. inversion_clear H1.
clear H. inversion_clear H2. clear H1. unfold _roundNoDupStakes in H.
unfold validatorStake. remember (RoundsBase_ι_Round_ι_stakes r). setoid_rewrite <- Heqx0.
clear Heqx0.
unfold RoundDefinitions.CommonModelProofs.DePoolSpec.LedgerClass.SolidityNotations.maybeGet.
unfold RoundDefinitions.CommonModelProofs.DePoolSpec.LedgerClass.SolidityNotations.hmapFetchM.
apply lookupFindSome. unfold hmapLookup. simpl.
induction x0. inversion_clear H0. inversion H1.
simpl. case_eq (m_validatorWallet l =? fst a) ; intros ; setoid_rewrite H1.
apply Z.eqb_eq in H1. simpl. inversion_clear H0. simpl in H2. simpl in H.
rewrite H1 in H3. inversion_clear H2. rewrite H0. reflexivity.
apply NoDup_cons_iff in H. inversion_clear H. apply in_map with (f := fst) in H0.
congruence. apply IHx0. inversion_clear H0. split. simpl in H2. inversion_clear H2.
rewrite <- H0 in H3. symmetry in H3. apply Z.eqb_eq in H3. congruence. assumption.
assumption. rewrite map_cons in H. apply NoDup_cons_iff in H. inversion H. assumption.
Qed.

Lemma long_stakes_validator_stake_less_stakes : forall l r,
    roundCorrectLocally l r ->
    allStakesAreNotEmpty l r ->
    (1 < roundStakesLen l r)%nat ->
    stakeSum (validatorStake l r) < RoundsBase_ι_Round_ι_stake r.
Proof.
intros. remember H as RCL. clear HeqRCL. unfold roundCorrectLocally in H.
inversion_clear H. inversion_clear H3. inversion_clear H4. unfold _roundCorrectStakeSum in H3.
rewrite <- H3.
assert(Forall (Z.gt (fold_left Z.add  (map stakeSum (map snd (RoundsBase_ι_Round_ι_stakes r))) 0))
(map stakeSum (map snd (RoundsBase_ι_Round_ι_stakes r)))).
apply element_strictly_less_sum. unfold allStakesAreNotEmpty in H0.
unfold pos_zlist. apply ForAll_map. apply ForAll_map. assumption. rewrite map_length.
rewrite map_length. assumption. case_eq(isValidatorInRound l r) ; intros.
apply isValidatorInRound_In in H6. inversion_clear H6. remember H7. clear Heqa.
apply validatorStake_exists_snd in H7. rewrite H7. inversion_clear a.
apply Z.gt_lt. apply (Forall_In(a := stakeSum (snd x))) in H4. assumption.
repeat apply in_map. assumption. assumption.
assert(stakeSum (validatorStake l r) <=0 \/ 0 < stakeSum (validatorStake l r)) by lia.
inversion_clear H7.
assert (0 <fold_left Z.add (map stakeSum (map snd (RoundsBase_ι_Round_ι_stakes r))) 0).
apply pos_zlist_sum_is_pos_not_empty. unfold allStakesAreNotEmpty in H0.
unfold pos_zlist. apply ForAll_map. apply ForAll_map. assumption. rewrite map_length.
rewrite map_length. unfold roundStakesLen in H1.
remember ((Datatypes.length (RoundsBase_ι_Round_ι_stakes r))%nat).
setoid_rewrite <- Heqn in H1. lia. lia.
apply validator_stake_not_empty_validator_exists in H8. congruence. assumption.
Qed.

Lemma no_validator_in_validator_stake_is_zero : forall l r,
    isValidatorInRound l r = false ->
    stakeSum (validatorStake l r) = 0.
Proof.
intros. unfold isValidatorInRound in H. unfold validatorStake.
unfold isSome in H.
destruct RoundDefinitions.CommonModelProofs.DePoolSpec.LedgerClass.SolidityNotations.hmapFetchM.
discriminate. compute. reflexivity.
Qed.

Lemma not_validator_stake_less_stakes : forall l r,
    roundCorrectLocally l r ->
    allStakesAreNotEmpty l r ->
    isNotValidatorInRound l r ->
    stakeSum (validatorStake l r) < RoundsBase_ι_Round_ι_stake r.
Proof.
intros. case_eq(1 <? roundStakesLen l r)%nat ; intros. apply Nat.ltb_lt in H2.
apply long_stakes_validator_stake_less_stakes ; assumption. apply Nat.ltb_ge in H2.
inversion H2. remember H as RCL. clear HeqRCL.
unfold allStakesAreNotEmpty in H0. unfold roundCorrectLocally in H.
decompose [and] H. clear H. unfold _roundCorrectStakeSum in H5. setoid_rewrite <- H5.
assert(exists x, RoundsBase_ι_Round_ι_stakes r = [ x ]).
apply len_one_as_list_one. unfold roundStakesLen in H4. symmetry. assumption.
inversion_clear H. rewrite H12. simpl. setoid_rewrite H12 in H0.
apply (Forall_one(a := x)) in H0. unfold compose in H0.
case_eq(isValidatorInRound l r) ; intros. apply isValidatorInRound_In in H. inversion_clear H.
setoid_rewrite H12 in H14. inversion_clear H14. simpl in H. inversion_clear H.
unfold isNotValidatorInRound in H1. inversion_clear H1. setoid_rewrite H12 in H.
inversion_clear H. simpl in H1. inversion_clear H1. inversion H14. rewrite <- H in H16.
inversion_clear H1. rewrite H14 in H16.
congruence. contradiction. contradiction.
apply no_validator_in_validator_stake_is_zero in H. rewrite H. assumption.
inversion H4. unfold isNotValidatorInRound in H1. inversion_clear H1. inversion_clear H5.
unfold roundStakesLen in H6. apply Lists.len0nil in H6. rewrite H6 in H1. inversion H1.
Qed.

Theorem notValidator_vaidator_remaining_stake_less_stake :
    forall l r ,
    roundCorrectLocally l r ->
    allStakesAreNotEmpty l r ->
    isNotValidatorInRound l r ->
    RoundsBase_ι_Round_ι_validatorRemainingStake r < RoundsBase_ι_Round_ι_stake r.
Proof.
intros. remember H as RCL. clear HeqRCL. unfold roundCorrectLocally in H. decompose [and] H.
clear H. unfold _roundValidatorRemainingStakeLessOrEqualValidatorStake in H8.
assert (stakeSum (validatorStake l r) < RoundsBase_ι_Round_ι_stake r).
apply not_validator_stake_less_stakes ; assumption. lia.
Qed.

Lemma validatorStake_non_neg :
    forall l r,
    roundCorrectLocally l r ->
    0 <= stakeSum (validatorStake l r).
Proof.
intros. unfold validatorStake.
unfold RoundDefinitions.CommonModelProofs.DePoolSpec.LedgerClass.SolidityNotations.maybeGet.
unfold RoundDefinitions.CommonModelProofs.DePoolSpec.LedgerClass.SolidityNotations.hmapFetchM.
unfold hmapLookup. unfold xMaybeMapDefault. simpl. unfold optionMapDefault.
remember (hd_error
(map snd
   (filter
      (fun
         p : RoundDefinitions.DePoolFuncs.DePoolSpec.LedgerClass.SolidityNotations.XAddress
             # (RoundsBase_ι_StakeValueP
                  RoundDefinitions.DePoolFuncs.DePoolSpec.LedgerClass.SolidityNotations.XInteger32
                  RoundDefinitions.DePoolFuncs.DePoolSpec.LedgerClass.SolidityNotations.XInteger64
                  RoundDefinitions.DePoolFuncs.DePoolSpec.LedgerClass.SolidityNotations.XAddress
                  XMaybe) =>
       m_validatorWallet l =? fst p)
      (Datatypes.id (RoundsBase_ι_Round_ι_stakes r))))). setoid_rewrite <- Heqo.
destruct o. unfold hd_error in Heqo.
remember (
    map snd
    (filter
       (fun
          p : RoundDefinitions.DePoolFuncs.DePoolSpec.LedgerClass.SolidityNotations.XAddress
              # (RoundsBase_ι_StakeValueP
                   RoundDefinitions.DePoolFuncs.DePoolSpec.LedgerClass.SolidityNotations.XInteger32
                   RoundDefinitions.DePoolFuncs.DePoolSpec.LedgerClass.SolidityNotations.XInteger64
                   RoundDefinitions.DePoolFuncs.DePoolSpec.LedgerClass.SolidityNotations.XAddress
                   XMaybe) =>
        m_validatorWallet l =? fst p)
       (Datatypes.id (RoundsBase_ι_Round_ι_stakes r)))
). destruct l0. discriminate. inversion Heqo. clear Heqo.
remember (filter
(fun
   p : RoundDefinitions.DePoolFuncs.DePoolSpec.LedgerClass.SolidityNotations.XAddress
       # (RoundsBase_ι_StakeValueP
            RoundDefinitions.DePoolFuncs.DePoolSpec.LedgerClass.SolidityNotations.XInteger32
            RoundDefinitions.DePoolFuncs.DePoolSpec.LedgerClass.SolidityNotations.XInteger64
            RoundDefinitions.DePoolFuncs.DePoolSpec.LedgerClass.SolidityNotations.XAddress
            XMaybe) =>
 m_validatorWallet l =? fst p)
(Datatypes.id (RoundsBase_ι_Round_ι_stakes r))). destruct l1. inversion Heql0.
rewrite map_cons in Heql0. inversion Heql0.
clear Heql0. clear H1. clear H2. clear H3.
assert (In x (filter
(fun
   p : RoundDefinitions.DePoolFuncs.DePoolSpec.LedgerClass.SolidityNotations.XAddress
       # (RoundsBase_ι_StakeValueP
            RoundDefinitions.DePoolFuncs.DePoolSpec.LedgerClass.SolidityNotations.XInteger32
            RoundDefinitions.DePoolFuncs.DePoolSpec.LedgerClass.SolidityNotations.XInteger64
            RoundDefinitions.DePoolFuncs.DePoolSpec.LedgerClass.SolidityNotations.XAddress
            XMaybe) =>
 m_validatorWallet l =? fst p)
(Datatypes.id (RoundsBase_ι_Round_ι_stakes r)))). setoid_rewrite <- Heql1. simpl.
left. reflexivity. clear Heql1. apply filter_In in H0. inversion_clear H0. clear H2.
unfold roundCorrectLocally in H. decompose [and] H. unfold _roundCorrectStakes in H4.
apply -> ForAll_map in H4. apply (Forall_In(a:=x)) in H4. unfold compose in H4.
apply stakeSum_not_negative with(l := l). assumption. assumption. compute. intros. discriminate.
Qed.

Lemma unused_le_stake : forall l r,
    roundCorrectLocally l r ->
    RoundsBase_ι_Round_ι_unused r <= RoundsBase_ι_Round_ι_stake r.
Proof.
intros. unfold roundCorrectLocally in H. decompose [and] H.
unfold _roundCorrectStakeIsTheMost in H2. unfold _roundCorrectNonNegative in H0.
decompose [and] H0. lia.
Qed.
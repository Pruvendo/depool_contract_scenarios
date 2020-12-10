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

Require Export Coq.micromega.Lia.

Require Export depoolContract.Scenarios.Common.CommonDefinitions.
Require Export depoolContract.Scenarios.Common.RewardsMove.
Require Export depoolContract.Scenarios.Common.UtilProofs.
Require Export depoolContract.Scenarios.Correctness.RoundCorrect.
Require Export depoolContract.Scenarios.Correctness.RoundCorrectProofs.

Lemma rewardsMove_reward0_gte_0 : forall l r,
    roundCorrectLocally l r ->
    RoundsBase_ι_Round_ι_stake r - RoundsBase_ι_Round_ι_unused r <= msgValue l ->
    0 <= reward0 l r.
Proof.
intros. unfold roundCorrectLocally in H. decompose [and] H. unfold ledgerCorrectLocally in H8.
decompose [and] H8. unfold _ledgerCorrectPositive in H8. decompose [and] H8.
unfold reward0. setoid_rewrite Z.add_comm at 3. rewrite <- Z.add_sub_assoc.
rewrite <- Z.add_assoc. apply Z.add_nonneg_nonneg. lia. rewrite <- Z.sub_sub_distr.
apply Zle_minus_le_0. assumption.
Qed.

Lemma rewardsMove_reward1_gte_0 : forall l r,
    roundCorrectLocally l r ->
    RoundsBase_ι_Round_ι_stake r - RoundsBase_ι_Round_ι_unused r <= msgValue l ->
    0 <= reward1 l r.
Proof.
intros. unfold reward1. unfold _cutDePoolRewardDelta.
case_eq(0 <? _cutDePoolRewardPreDelta l r) ; intros. rewrite intMin_sym. apply sub_sub_min_non_neg_r.
apply rewardsMove_reward0_gte_0 ; assumption. rewrite Z.sub_0_r.
apply rewardsMove_reward0_gte_0 ; assumption.
Qed.

Lemma rewardsMove_reward2_gte_0 : forall l r,
    roundCorrectLocally l r ->
    RoundsBase_ι_Round_ι_stake r - RoundsBase_ι_Round_ι_unused r <= msgValue l ->
    0 <= reward2 l r.
Proof.
intros. unfold reward2. rewrite intMin_sym. apply sub_sub_min_non_neg_r.
apply rewardsMove_reward1_gte_0 ; assumption.
Qed.

Lemma rewardsMove_reward3_gte_0 : forall l r,
    roundCorrectLocally l r ->
    RoundsBase_ι_Round_ι_stake r - RoundsBase_ι_Round_ι_unused r <= msgValue l ->
    0 <= reward3 l r.
Proof.
intros. unfold reward3. apply intMulDiv_ge_0. apply rewardsMove_reward2_gte_0 ;
assumption. unfold roundCorrectLocally in H. decompose [and] H. unfold ledgerCorrectLocally in H8.
decompose [and] H8. unfold _ledgerCorrectPositive in H9. decompose [and] H9. lia. lia.
Qed.

Lemma rewardsMove_reward0_leq_value : forall l r,
    roundCorrectLocally l r ->
    RoundsBase_ι_Round_ι_stake r - RoundsBase_ι_Round_ι_unused r <= msgValue l ->
    reward0 l r <= msgValue l + PROXY_FEE l.
Proof.
intros. unfold reward0. rewrite <- Z.sub_sub_distr. rewrite <- Z.sub_0_r. apply Z.sub_le_mono.
lia. apply Zle_minus_le_0. apply unused_le_stake with (l := l). assumption.
Qed.

Lemma rewardsMove_reward1_leq_value : forall l r,
    roundCorrectLocally l r ->
    RoundsBase_ι_Round_ι_stake r - RoundsBase_ι_Round_ι_unused r <= msgValue l ->
    reward1 l r <= msgValue l + PROXY_FEE l.
Proof.
intros. unfold reward1. rewrite <- Z.sub_0_r. apply Z.sub_le_mono.
apply rewardsMove_reward0_leq_value ; assumption. unfold _cutDePoolRewardDelta.
case_eq (0 <? _cutDePoolRewardPreDelta l r) ; intros. apply min_gte_0.
apply rewardsMove_reward0_gte_0 ; assumption. apply Z.ltb_lt in H1. lia. lia.
Qed.

Lemma rewardsMove_reward2_leq_value : forall l r,
    roundCorrectLocally l r ->
    RoundsBase_ι_Round_ι_stake r - RoundsBase_ι_Round_ι_unused r <= msgValue l ->
    reward2 l r <= msgValue l + PROXY_FEE l.
Proof.
intros. unfold reward2. apply Z.le_trans with (m := reward1 l r). apply Z.le_sub_nonneg.
apply min_gte_0. apply rewardsMove_reward1_gte_0 ; assumption. unfold roundCorrectLocally in H.
decompose [and] H. apply Z.mul_nonneg_nonneg. unfold _roundCorrectNonNegative in H1.
decompose [and] H1. assumption. unfold ledgerCorrectLocally in H8. decompose [and] H8.
unfold _ledgerCorrectPositive in H9. decompose [and] H9. lia.
apply rewardsMove_reward1_leq_value ; assumption.
Qed.

Lemma rewardsMove_reward3_leq_value : forall l r,
    roundCorrectLocally l r ->
    RoundsBase_ι_Round_ι_stake r - RoundsBase_ι_Round_ι_unused r <= msgValue l ->
    reward3 l r <= msgValue l + PROXY_FEE l.
Proof.
intros. unfold reward3. apply Z.le_trans with (m := (reward2 l r)).
apply intMulDiv_le_a. apply rewardsMove_reward2_gte_0 ; assumption.
unfold roundCorrectLocally in H. decompose [and] H. unfold ledgerCorrectLocally in H8.
decompose [and] H8. unfold _ledgerCorrectNotTooLarge in H11. decompose [and] H11.
assumption. lia. apply rewardsMove_reward2_leq_value ; assumption.
Qed.

Theorem rewardsMove_reward_gte_0 : forall l r,
    roundCorrectLocally l r ->
    0 <= rewardsMove_reward l r.
Proof.
intros. unfold rewardsMove_reward.
case_eq(RoundsBase_ι_Round_ι_stake r - RoundsBase_ι_Round_ι_unused r <=? msgValue l) ; intros ;
setoid_rewrite H0. apply rewardsMove_reward3_gte_0. assumption. apply Z.leb_le in H0. lia.
unfold roundCorrectLocally in H. decompose [and] H. unfold _roundCorrectNonNegative in H1.
decompose [and] H1. assumption.
Qed.

Lemma rewardsMove_reward_leq_value : forall l r,
    roundCorrectLocally l r ->
    RoundsBase_ι_Round_ι_stake r - RoundsBase_ι_Round_ι_unused r <= msgValue l ->
    rewardsMove_reward l r <= msgValue l + PROXY_FEE l.
Proof.
intros. unfold rewardsMove_reward.
case_eq(RoundsBase_ι_Round_ι_stake r - RoundsBase_ι_Round_ι_unused r <=? msgValue l) ; intros ;
setoid_rewrite H1. apply rewardsMove_reward3_leq_value ; assumption.
apply Z.leb_gt in H1. lia.
Qed.
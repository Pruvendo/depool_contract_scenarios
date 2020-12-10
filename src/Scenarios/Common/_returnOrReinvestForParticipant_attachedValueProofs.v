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
Require Export depoolContract.Scenarios.Common.UtilProofs.
Require Export depoolContract.Scenarios.Common._returnOrReinvestForParticipant_attachedValueMove.
Require Export depoolContract.Scenarios.Correctness.ParticipantCorrect.

Lemma attachedValue_NewParticipant_correct : forall p stake,
    participantCorrectLocally p ->
    0 <= stake ->
    participantCorrectLocally (attachedValue_NewParticipant p stake).
Proof.
intros. unfold participantCorrectLocally in *. unfold _participantCorrectPositive in *.
inversion_clear H. inversion_clear H2. unfold attachedValue_NewParticipant.
repeat split ; simpl ; try assumption.
unfold _curPause. unfold _returnOrReinvestForParticipant_attachedValueMove.DePoolFuncs.intMin.
simpl. case_eq ( DePoolLib_ι_Participant_ι_withdrawValue p <=? stake) ; intros ; setoid_rewrite H2.
lia. apply Z.leb_gt in H2. replace 0 with (stake - stake). apply Z.sub_le_mono_r.
apply Z.lt_le_incl. assumption. lia.
Qed.

Lemma attachedValue_attachedValue_ge0 : forall l p stake,
    participantCorrectLocally p ->
    0 <= stake ->
    0 < attachedValue l p stake.
Proof.
intros. unfold attachedValue. case_eq (stake - _curPause p stake <? m_minStake l) ; intros.
lia. unfold _curPause. unfold _returnOrReinvestForParticipant_attachedValueMove.DePoolFuncs.intMin.
Opaque "+". simpl. Transparent "+".
case_eq ( DePoolLib_ι_Participant_ι_withdrawValue p <=? stake) ; intros ; setoid_rewrite H2.
unfold participantCorrectLocally in H. unfold _participantCorrectPositive in H.
inversion_clear H. inversion_clear H4. rewrite Z.add_comm. apply Z.add_nonneg_pos. auto. lia.
rewrite Z.add_comm. apply Z.add_nonneg_pos. auto. lia.
Qed.

Lemma attachedValue_attachedValue_NewStake : forall l p stake,
    participantCorrectLocally p ->
    0 <= stake ->
    attachedValue_NewStake l p stake = 0 \/ m_minStake l <= attachedValue_NewStake l p stake.
Proof.
intros. unfold attachedValue_NewStake. unfold participantCorrectLocally in H.
unfold _participantCorrectPositive in H. inversion_clear H. inversion_clear H2.
case_eq(stake - _curPause p stake <? m_minStake l) ; intros.
left. reflexivity. right. apply Z.ltb_ge in H2. assumption.
Qed.

Lemma attachedValue_attachedValue_plus_NewStake : forall l p stake,
    participantCorrectLocally p ->
    0 <= stake ->
    attachedValue l p stake + attachedValue_NewStake l p stake = 1 + stake.
Proof.
intros. unfold attachedValue. unfold attachedValue_NewStake.
case_eq(stake - _curPause p stake <? m_minStake l) ; intros ; lia.
Qed.

Lemma attachedValue_attachedValue_lt_1_plus_s : forall l p stake,
    0 <= stake ->
    attachedValue l p stake <= 1 + stake.
Proof.
intros. unfold attachedValue.
case_eq(stake - _curPause p stake <? m_minStake l) ; intros. lia. apply Zplus_le_compat_l.
unfold _curPause. apply min_lte_r.
Qed.
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
Require Export depoolContract.Scenarios.Common.unfreezeCondition.
Require Export depoolContract.Scenarios.Common.Axioms.
Require Export depoolContract.Scenarios.Correctness.RoundCorrect.

Lemma untouchUnfreezeNeverUnfrozen : forall l r,
    roundCorrectLocally l r ->
    RoundsBase_ι_Round_ι_unfreeze r = MAX_INT l ->
    (currentValidator l = RoundsBase_ι_Round_ι_vsetHashInElectionPhase r \/
    prevValidator l = RoundsBase_ι_Round_ι_vsetHashInElectionPhase r) ->
    ~ shouldBeUnfrozen l r.
Proof.
intro l. intro r. intro CLR.
intros. unfold "~". intros. unfold shouldBeUnfrozen in H1. unfold resultedUnfreeze in H1.
case_eq((negb
(currentValidator
l =?
RoundsBase_ι_Round_ι_vsetHashInElectionPhase
r) &&
negb
(prevValidator
l =?
RoundsBase_ι_Round_ι_vsetHashInElectionPhase
r) &&
(RoundsBase_ι_Round_ι_unfreeze
r =?
MAX_INT
l))%bool) ; intros . clear H1. apply andb_prop in H2. inversion_clear H2. clear H3. apply andb_prop in H1.
inversion_clear H1. apply Bool.negb_true_iff in H2. apply Bool.negb_true_iff in H3.
apply Z.eqb_neq in H2. apply Z.eqb_neq in H3. inversion H0 ; contradiction. setoid_rewrite H2 in H1.
setoid_rewrite H in H1. rewrite <- Z.add_0_r in H1. apply Z.add_le_cases in H1. inversion H1.
assert (now l < MAX_INT l) by apply nowLessMax. lia. inversion_clear CLR. decompose [and] H5.
unfold ledgerCorrectLocally in H12. decompose [and] H12. unfold _ledgerCorrectPositive in H13.
decompose [and] H13. lia.
Qed.

Lemma zeroUnfreezeAlwaysUnfrozen : forall l r,
    roundCorrectLocally l r ->
    RoundsBase_ι_Round_ι_unfreeze r = 0 ->
    shouldBeUnfrozen l r.
Proof.
intros. unfold shouldBeUnfrozen. unfold resultedUnfreeze. setoid_rewrite H0. case_eq (MAX_INT l =? 0)
; intros. apply Z.eqb_eq in H1. assert (0 < MAX_INT l). apply Z.lt_trans with (m := now l).
unfold roundCorrectLocally in H. decompose [and] H. unfold ledgerCorrectLocally in H9.
decompose [and] H9. unfold _ledgerCorrectPositive in H10. decompose [and] H10. assumption.
apply nowLessMax. lia. rewrite Z.eqb_sym in H1. rewrite H1. rewrite Bool.andb_false_r.
setoid_rewrite H0. rewrite Z.add_0_l.
assert (ELECTOR_UNFREEZE_LAG l < now l) by apply unfreezeLagLessNow. lia.
Qed.

Lemma numericUnfrezeEventuallyUnfrozen : forall l r,
    roundCorrectLocally l r ->
    RoundsBase_ι_Round_ι_unfreeze r < MAX_INT l ->
    (exists t, t <= now l ->
    shouldBeUnfrozen l r
    ).
Proof.
intros. exists (RoundsBase_ι_Round_ι_unfreeze r + ELECTOR_UNFREEZE_LAG l). intros.
unfold shouldBeUnfrozen. unfold resultedUnfreeze.
case_eq((RoundsBase_ι_Round_ι_unfreeze r =? MAX_INT l)) ; intros. apply Z.eqb_eq in H2. lia.
setoid_rewrite H2. rewrite Bool.andb_false_r. assumption.
Qed.
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

Lemma emptyRounds: forall r ,
(isEmptyRound r <-> ~notEmptyRound r) /\ (~isEmptyRound r <-> notEmptyRound r) .
Proof.
split ; split ; unfold "~" ; intros.
unfold isEmptyRound in H. unfold notEmptyRound in H0. inversion H0. inversion H ; contradiction.
unfold notEmptyRound in H. unfold isEmptyRound.
assert (RoundsBase_ι_Round_ι_step r = RoundsBase_ι_RoundStepP_ι_Completed \/
RoundsBase_ι_Round_ι_step r <> RoundsBase_ι_RoundStepP_ι_Completed). decide equality.
inversion H0. left. apply H1.
assert(RoundsBase_ι_Round_ι_stake r = 0 \/ RoundsBase_ι_Round_ι_stake r <> 0). decide equality.
decide equality. decide equality. inversion H2. right. apply H3.
assert( RoundsBase_ι_Round_ι_step r <> RoundsBase_ι_RoundStepP_ι_Completed /\
RoundsBase_ι_Round_ι_stake r <> 0). auto. contradiction.
unfold isEmptyRound in H. unfold notEmptyRound.
assert(RoundsBase_ι_Round_ι_step r = RoundsBase_ι_RoundStepP_ι_Completed \/
RoundsBase_ι_Round_ι_step r <> RoundsBase_ι_RoundStepP_ι_Completed). decide equality.
inversion H0.
assert( RoundsBase_ι_Round_ι_stake r = 0 \/  RoundsBase_ι_Round_ι_stake r <> 0).
decide equality. inversion H2.
assert(RoundsBase_ι_Round_ι_step r = RoundsBase_ι_RoundStepP_ι_Completed \/
RoundsBase_ι_Round_ι_stake r = 0). auto. contradiction. split.
assert(RoundsBase_ι_Round_ι_step r = RoundsBase_ι_RoundStepP_ι_Completed \/
RoundsBase_ι_Round_ι_stake r = 0). left. apply H1. contradiction. apply H3. split.
apply H1.
assert( RoundsBase_ι_Round_ι_stake r = 0 \/  RoundsBase_ι_Round_ι_stake r <> 0). decide equality.
decide equality. decide equality. inversion H2.
assert(RoundsBase_ι_Round_ι_step r = RoundsBase_ι_RoundStepP_ι_Completed \/
RoundsBase_ι_Round_ι_stake r = 0). auto. contradiction. apply H3.
unfold notEmptyRound in H. unfold isEmptyRound in H0. inversion H. inversion H0 ; contradiction.
Qed.

Lemma participant_in_or_out : forall l p,
    (participantIn l p \/ participantOut l p) /\
    ~ (participantIn l p /\ participantOut l p).
Proof.
intros. split. assert (participantIn l p \/ ~participantIn l p). tauto.
inversion H. left. assumption. right. unfold participantOut. unfold participantIn in H0.
intros.
assert(
(CommonModelProofs.DePoolSpec.LedgerClass.SolidityNotations.maybeGet
(eval_state (DePoolFuncs.ParticipantBase_Ф_fetchParticipant addr) l) = p \/
(CommonModelProofs.DePoolSpec.LedgerClass.SolidityNotations.maybeGet
  (eval_state (DePoolFuncs.ParticipantBase_Ф_fetchParticipant addr) l) <> p))).
  decide equality ; decide equality ; decide equality. inversion H2.
assert(exists
addr : DePoolFuncs.DePoolSpec.LedgerClass.SolidityNotations.XAddress,
isSome
  (eval_state (DePoolFuncs.ParticipantBase_Ф_fetchParticipant addr) l) =
true /\
CommonModelProofs.DePoolSpec.LedgerClass.SolidityNotations.maybeGet
  (eval_state (DePoolFuncs.ParticipantBase_Ф_fetchParticipant addr) l) =
p). exists addr. clear H2. split ; assumption. contradiction. assumption.
unfold "~". intros. inversion H. unfold participantIn in H0. inversion_clear H0.
inversion_clear H2. unfold participantOut in H1. apply H1 in H0. contradiction.
Qed.
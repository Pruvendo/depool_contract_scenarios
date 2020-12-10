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
Require Export depoolContract.Scenarios.Common.RoundDefinitions.

Definition _participantCorrectPositive (p : DePoolLib_ι_Participant) :=
    0 <= DePoolLib_ι_Participant_ι_roundQty p /\
    0 <= DePoolLib_ι_Participant_ι_reward p /\
    0 <= DePoolLib_ι_Participant_ι_withdrawValue p.

Definition participantCorrectLocally (p : DePoolLib_ι_Participant) :=
    _participantCorrectPositive p.

Definition _participantCorrectlyExists (l : Ledger) (p : DePoolLib_ι_Participant) :=
    (participantIn l p /\ 0 < DePoolLib_ι_Participant_ι_roundQty p) \/
    (participantOut l p /\ 0 = DePoolLib_ι_Participant_ι_roundQty p).

Definition _participantInRound (l : Ledger) (p : DePoolLib_ι_Participant) :=
    participantIn l p <->
    (exists r addr, roundIn l r /\ addrInRound l r addr /\
    isSome (eval_state ( ParticipantBase_Ф_fetchParticipant addr) l) = true).

Definition participantCorrectGlobally (l : Ledger) :=
    forall p,
    participantIn l p ->
    (
        participantCorrectLocally p /\
        _participantCorrectlyExists l p /\
        _participantInRound l p
    ).
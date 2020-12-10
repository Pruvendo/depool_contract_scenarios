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

Definition _curPause (p : DePoolLib_ι_Participant)(stake : Z) := 
    intMin
        (DePoolLib_ι_Participant_ι_withdrawValue p) stake.

Definition attachedValue (l : Ledger)(p : DePoolLib_ι_Participant)(stake : Z) :=
    if(stake - _curPause p stake <? m_minStake l)
        then 1 + stake
        else 1 + _curPause p stake.

Definition attachedValue_NewStake (l : Ledger)(p : DePoolLib_ι_Participant)(stake : Z) :=
    if(stake - _curPause p stake <? m_minStake l)
        then 0
        else stake - _curPause p stake.

Definition attachedValue_NewParticipant (p : DePoolLib_ι_Participant)(stake : Z) :=
    {$ p with DePoolLib_ι_Participant_ι_withdrawValue :=
        (DePoolLib_ι_Participant_ι_withdrawValue p) - _curPause p stake
    $}.
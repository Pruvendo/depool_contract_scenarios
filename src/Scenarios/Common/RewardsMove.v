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

Definition reward0 (l : Ledger) (r : RoundsBase_ι_Round) := msgValue l + PROXY_FEE l -
    RoundsBase_ι_Round_ι_stake r + RoundsBase_ι_Round_ι_unused r.

Definition _cutDePoolRewardPreDelta (l : Ledger) (r : RoundsBase_ι_Round) := 
    m_balanceThreshold l +
    RoundsBase_ι_Round_ι_stake r +
    totalParticipantsStakeBut2 l +
    reward0 l r -
    balance l.
    
Definition _cutDePoolRewardDelta (l : Ledger) (r : RoundsBase_ι_Round) := 
    if(0 <? _cutDePoolRewardPreDelta l r)
    then intMin (reward0 l r) (_cutDePoolRewardPreDelta l r)
    else 0.

Definition reward1 (l : Ledger) (r : RoundsBase_ι_Round) :=
    reward0 l r - _cutDePoolRewardDelta l r.

Definition reward2 (l : Ledger) (r : RoundsBase_ι_Round) :=
    reward1 l r -
    intMin (reward1 l r) ((RoundsBase_ι_Round_ι_participantQty r) * (RET_OR_REINV_FEE l)).

Definition reward3 (l : Ledger) (r : RoundsBase_ι_Round) :=
    intMulDiv (reward2 l r) (m_participantRewardFraction l) 100.

(*****************Results***********************)
Definition rewardsMove_reward (l : Ledger) (r : RoundsBase_ι_Round) :=
    if(RoundsBase_ι_Round_ι_stake r - RoundsBase_ι_Round_ι_unused r <=? msgValue l)
    then reward3 l r
    else RoundsBase_ι_Round_ι_rewards r.
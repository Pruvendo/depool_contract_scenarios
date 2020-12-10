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
Require Export depoolContract.Scenarios.Common.CommonDefinitions.

Import DePoolSpec.LedgerClass.SolidityNotations. 

Local Open Scope struct_scope.
Local Open Scope Z_scope.
Local Open Scope solidity_scope.
Require Import Lists.List.
Import ListNotations.
Local Open Scope list_scope.

Set Typeclasses Iterative Deepening.
Set Typeclasses Depth 100.
 
Check eval_state (↑11 ε RoundsBase_ι_m_rounds).

Inductive Projection_Pool_State :=
| Projection_Pool_State_Opened :  XInteger64 -> XInteger64 ->  XInteger64 -> XInteger64 ->
    Projection_Pool_State
| Projection_Pool_State_Closed : XInteger64 -> XInteger64 ->  XInteger64 -> XInteger64 ->
    Projection_Pool_State.

Definition pool_closed (l : Ledger) : bool :=
    eval_state (↑12 ε DePoolContract_ι_m_poolClosed) l.

Definition getProjection_Pool_State (l : Ledger) : Projection_Pool_State :=
    (if pool_closed l
    then Projection_Pool_State_Closed
    else Projection_Pool_State_Opened)
    (RoundsBase_ι_Round_ι_id (eval_state (↓ RoundsBase_Ф_getRoundPre0) l))
    (RoundsBase_ι_Round_ι_id (eval_state (↓ RoundsBase_Ф_getRound0) l))
    (RoundsBase_ι_Round_ι_id (eval_state (↓ RoundsBase_Ф_getRound1) l))
    (RoundsBase_ι_Round_ι_id (eval_state (↓ RoundsBase_Ф_getRound2) l))
.

Definition projection_pool_state_isClosed (pps : Projection_Pool_State) : bool :=
    match pps with
    | Projection_Pool_State_Opened _ _ _ _ => false
    | _ => true
    end.

Definition projection_pull_state_getPre0_index (pps : Projection_Pool_State) : XInteger64 := 
    match pps with
    | Projection_Pool_State_Opened p0 _ _ _ | Projection_Pool_State_Closed p0 _ _ _ => p0
    end.

Definition projection_pull_state_getRound0_index (pps : Projection_Pool_State) : XInteger64 := 
    match pps with
    | Projection_Pool_State_Opened _ p0 _ _ | Projection_Pool_State_Closed _ p0 _ _ => p0
    end.

Definition projection_pull_state_getRound1_index (pps : Projection_Pool_State) : XInteger64 := 
    match pps with
    | Projection_Pool_State_Opened _ _ p1 _ | Projection_Pool_State_Closed _ _ p1 _ => p1
    end.

Definition projection_pull_state_getRound2_index (pps : Projection_Pool_State) : XInteger64 := 
    match pps with
    | Projection_Pool_State_Opened _ _ _ p2 | Projection_Pool_State_Closed _ _ _ p2 => p2
    end.
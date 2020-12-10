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

Inductive Projection_Round_Pool_State :=
| Projection_Round_Pool_State_Pre0
| Projection_Round_Pool_State_0
| Projection_Round_Pool_State_1
| Projection_Round_Pool_State_2
| Projection_Round_Pool_State_Expired
.

Definition getProjectionRoundPoolState (l : Ledger) (r : RoundsBase_ι_Round) := 
let index := RoundsBase_ι_Round_ι_id r in
if RoundsBase_ι_Round_ι_id (roundPre0 l) =? index then Projection_Round_Pool_State_Pre0
else if RoundsBase_ι_Round_ι_id (round0 l) =? index then Projection_Round_Pool_State_0
else if RoundsBase_ι_Round_ι_id (round1 l) =? index then Projection_Round_Pool_State_1
else if RoundsBase_ι_Round_ι_id (round2 l) =? index then Projection_Round_Pool_State_2
else Projection_Round_Pool_State_Expired
.

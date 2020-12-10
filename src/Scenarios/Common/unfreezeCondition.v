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
Require Export depoolContract.Scenarios.Common.RotateRoundsCondition.

Definition resultedUnfreeze (l : Ledger) (r : RoundsBase_ι_Round) :=
    if andb
        (andb   (negb (currentValidator l =? RoundsBase_ι_Round_ι_vsetHashInElectionPhase r))
                (negb (prevValidator l =? RoundsBase_ι_Round_ι_vsetHashInElectionPhase r)))
        (RoundsBase_ι_Round_ι_unfreeze r =? MAX_INT l)
    then validationStart l + RoundsBase_ι_Round_ι_stakeHeldFor r
    else RoundsBase_ι_Round_ι_unfreeze r.

Definition shouldBeUnfrozen (l : Ledger) (r : RoundsBase_ι_Round) :=
    resultedUnfreeze l r + ELECTOR_UNFREEZE_LAG l <= now l.
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

(* Import SolidityNotations. *)
Set Typeclasses Iterative Deepening.
Set Typeclasses Depth 100.
(*Set Typeclasses Strict Resolution. *)
(* Set Typeclasses Debug.  *) 
(* Set Typeclasses Unique Instances. 
Unset Typeclasses Unique Solutions. *)

(* Existing Instance monadStateT.
Existing Instance monadStateStateT. *)
(* Module MultiSigWalletSpecSig := MultiSigWalletSpecSig XTypesSig StateMonadSig. *)

Require Import depoolContract.Lib.CommonModelProofs.
Module CommonModelProofs := CommonModelProofs StateMonadSig.
Import CommonModelProofs. 
Require Import depoolContract.Lib.Tactics.
Require Import depoolContract.Lib.ErrorValueProofs.
Require Import depoolContract.Lib.CommonCommon.

(* Require Import MultiSigWallet.Proofs.tvmFunctionsProofs. *)

Import DePoolSpec.LedgerClass.SolidityNotations. 

Local Open Scope solidity_scope.

(* Require Import MultiSigWallet.Specifications._validatelimit_inlineSpec.
Module _validatelimit_inlineSpec := _validatelimit_inlineSpec MultiSigWalletSpecSig.
Import _validatelimit_inlineSpec. *)

Local Open Scope struct_scope.
Local Open Scope Z_scope.
Local Open Scope solidity_scope.
Require Import Lists.List.
Import ListNotations.
Local Open Scope list_scope.

(* Existing Instance embeddedLocalState.
 
Existing Instance monadStateT.
Existing Instance monadStateStateT. *)

(* Existing Instance embeddedLocalState.
Existing Instance embeddedMultisig. *)

(* function startRoundCompleting(Round round, CompletionReason reason) private returns (Round) {
        round.completionReason = reason;
        round.step = RoundStep.Completing;

        this.completeRound{flag: 1, bounce: false, value: VALUE_FOR_SELF_CALL}(round.id, round.participantQty);

        emit RoundCompleted(toTruncatedRound(round));

        return round;
    } *)
Lemma DePoolContract_Ф_startRoundCompleting_exec : forall ( Л_round : RoundsBase_ι_Round ) 
                                                 ( Л_reason : RoundsBase_ι_CompletionReason )
                                                 (l: Ledger) , 
                                                 (*: LedgerT RoundsBase_ι_Round*)
exec_state (  DePoolContract_Ф_startRoundCompleting Л_round Л_reason ) l = 

let round' := {$ Л_round with ( RoundsBase_ι_Round_ι_completionReason , Л_reason ) ;
                              ( RoundsBase_ι_Round_ι_step , RoundsBase_ι_RoundStepP_ι_Completing ) $} in
let oldMessages := VMState_ι_messages ( Ledger_ι_VMState l ) in
let newMessage  := {| contractAddress :=  0 ;
                      contractFunction := DePoolContract_Ф_completeRoundF 
                      ( round' ->> RoundsBase_ι_Round_ι_id ) ( round' ->> RoundsBase_ι_Round_ι_participantQty )      ;
                      contractMessage := {| messageValue := (eval_state ( ↑12 ε DePoolContract_ι_VALUE_FOR_SELF_CALL) l ) ;
                                            messageFlag  := 1 ; 
                                            messageBounce := false
                                            |} |} in 
        (* emit RoundCompleted(toTruncatedRound(round)); *)
let oldEvents := VMState_ι_events ( Ledger_ι_VMState l ) in
let tr := eval_state ( ↓ RoundsBase_Ф_toTruncatedRound round' ) l in
let newEvent  :=  RoundCompleted tr in

{$ l With ( VMState_ι_messages , newMessage :: oldMessages ) ; 
          ( VMState_ι_events , newEvent :: oldEvents ) $} . 
Proof. 
   intros. destruct l. auto. 
Qed. 
 
 Lemma DePoolContract_Ф_startRoundCompleting_eval : forall ( Л_round : RoundsBase_ι_Round ) 
                                                 ( Л_reason : RoundsBase_ι_CompletionReason )
                                                 (l: Ledger) , 
                                                 (*: LedgerT RoundsBase_ι_Round*)

 	 eval_state (  DePoolContract_Ф_startRoundCompleting Л_round Л_reason ) l = 

let round' := {$ Л_round with ( RoundsBase_ι_Round_ι_completionReason , Л_reason ) ;
                              ( RoundsBase_ι_Round_ι_step , RoundsBase_ι_RoundStepP_ι_Completing ) $} in
round' . 
 Proof. 
   intros. destruct l. auto. 
 Qed. 
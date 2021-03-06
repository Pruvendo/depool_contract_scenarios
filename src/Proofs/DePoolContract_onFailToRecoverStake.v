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
Require Import depoolContract.Lib.CommonStateProofs.

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

Opaque Z.eqb Z.add Z.sub Z.div Z.mul hmapLookup hmapInsert Z.ltb Z.geb Z.leb Z.gtb Z.modulo deleteListPair.

(* Opaque tvm_accept DePoolContract_Ф_checkPureDePoolBalance RoundsBase_Ф_getRound1. *)


Lemma ifSimpleState: forall X (b: bool) (f g: Ledger -> X * Ledger), 
(if b then SimpleState f else SimpleState g ) =
SimpleState (if b then f else  g).
Proof.
  intros. destruct b; auto.
Qed.  

Lemma ifFunApply: forall X (b: bool) (f g: Ledger -> X * Ledger) l, 
(if b then f else  g ) l =
(if b then f l else g l).
Proof.
  intros. destruct b; auto.
Qed. 

Lemma fstImplies : forall  X Y T (f: X*T) (g: X -> Y)  ,  (let (x, _) := f in g x) = g (fst f).
Proof.
  intros.
  destruct f; auto.
Qed.

Lemma sndImplies : forall  X Y T (f: X*T) (g: T -> Y)  ,  (let (_, t) := f in g t) = g (snd f).
Proof.
  intros.
  destruct f; auto.
Qed.

Lemma fstsndImplies : forall  X Y T (f: X*T) (g: X -> T -> Y)  ,  (let (x, t) := f in g x t) = g (fst f) (snd f).
Proof.
  intros.
  destruct f; auto.
Qed.


Lemma letIf: forall X Y (b: bool) (f g: X*Ledger) (h: X -> Ledger -> Y), 
(let (x, t) := if b then f else g in h x t)=
if b then let (x, t) := f in h x t else
          let (x, t) := g in h x t .
Proof.
  intros.
  destruct b; auto.
Qed.

Lemma matchIf: forall X (b: bool) (f g: LedgerT X) (l: Ledger), 
(match (if b then f else g) with | SimpleState c => c end l)=
if b then match f with | SimpleState c => c end l else 
match g with | SimpleState c => c end l.
Proof.
  intros.
  destruct b; auto.
Qed.




Ltac pr_numgoals := let n := numgoals in idtac "There are" n "goals".
Ltac pr_hyp := repeat match goal with
               | H: ?x = true |- _ => idtac x " = true"
               | H: ?x = false |- _ => idtac x " = false"  
                end.

Ltac remDestructIf :=
  match goal with
    | |- ?x =>
      match x with
        | context [if ?b then _ else _] => case_eq b ; intros
        | _ => idtac
      end
  end.


(*function onFailToRecoverStake(uint64 queryId, address elector) public override {
        optional(Round) optRound = fetchRound(queryId);
        require(optRound.hasValue(), InternalErrors.ERROR513);
        Round round = optRound.get();
        require(msg.sender == round.proxy, Errors.IS_NOT_PROXY);
        require(elector == round.elector, Errors.IS_NOT_ELECTOR);
        tvm.accept();
        if (round.step == RoundStep.WaitingIfValidatorWinElections) {
             round.step = RoundStep.WaitingUnfreeze;
        } else if (round.step == RoundStep.WaitingReward) {
            round = startRoundCompleting(round, CompletionReason.ValidatorIsPunished);
        } else {
            revert(InternalErrors.ERROR521);
        }
        setRound(queryId, round);  }*)
Opaque DePoolContract_Ф_startRoundCompleting.

Lemma DePoolContract_Ф_onFailToRecoverStake_exec : forall ( Л_queryId : XInteger64 ) 
                                                          ( Л_elector : XAddress ) 
                                                           (l: Ledger) , 
exec_state ( ↓ DePoolContract_Ф_onFailToRecoverStake Л_queryId Л_elector ) l =
let optRound := eval_state ( ↓ ( RoundsBase_Ф_fetchRound Л_queryId ) ) l in
        (* require(optRound.hasValue(), InternalErrors.ERROR513); *)
let req1 : bool := isSome optRound in
        (* Round round = optRound.get(); *)
let round := maybeGet optRound in
        (* require(msg.sender == round.proxy, Errors.IS_NOT_PROXY); *)
let req2 : bool := eval_state msg_sender  l  =?  round ->> RoundsBase_ι_Round_ι_proxy  in
        (* require(elector == round.elector, Errors.IS_NOT_ELECTOR); *)
let req3 : bool :=  Л_elector =? ( round ->> RoundsBase_ι_Round_ι_elector ) in
        (* tvm.accept(); *)
        (* if (round.step == RoundStep.WaitingIfValidatorWinElections) { *)
let if1 : bool := ( eqb ( round ->> RoundsBase_ι_Round_ι_step ) RoundsBase_ι_RoundStepP_ι_WaitingIfValidatorWinElections ) in
        (* } else if (round.step == RoundStep.WaitingReward) { *)
let if2 : bool := ( eqb ( round ->> RoundsBase_ι_Round_ι_step ) RoundsBase_ι_RoundStepP_ι_WaitingReward ) in

let (round', l') := if if1 then ({$ round with ( RoundsBase_ι_Round_ι_step , RoundsBase_ι_RoundStepP_ι_WaitingUnfreeze ) $}, l)
                    else if if2  then 
  run ( ↓ ( DePoolContract_Ф_startRoundCompleting round RoundsBase_ι_CompletionReasonP_ι_ValidatorIsPunished ) ) l 
               else (round, injEmbed (VMState_ι_savedDePoolContracts (Ledger_ι_VMState l)) l) in
if req1 then 
        if req2 then 
                if req3 then                
if if1 then exec_state ( ↓ ( RoundsBase_Ф_setRound Л_queryId round' ) ) l' 
       else if if2 then exec_state ( ↓ ( RoundsBase_Ф_setRound Л_queryId round' ) ) l' 
               else l'
               else l else l else l.
Proof.
        intros. destruct l. compute.
        repeat remDestructIf; auto.  
Qed.

Lemma DePoolContract_Ф_onFailToRecoverStake_eval : forall ( Л_queryId : XInteger64 ) 
                                                          ( Л_elector : XAddress ) 
                                                           (l: Ledger) , 
eval_state ( ↓ DePoolContract_Ф_onFailToRecoverStake Л_queryId Л_elector ) l =
let optRound := eval_state ( ↓ ( RoundsBase_Ф_fetchRound Л_queryId ) ) l in
        (* require(optRound.hasValue(), InternalErrors.ERROR513); *)
let req1 : bool := isSome optRound in
        (* Round round = optRound.get(); *)
let round := maybeGet optRound in
        (* require(msg.sender == round.proxy, Errors.IS_NOT_PROXY); *)
let req2 : bool := eval_state msg_sender  l  =?  round ->> RoundsBase_ι_Round_ι_proxy  in
        (* require(elector == round.elector, Errors.IS_NOT_ELECTOR); *)
let req3 : bool :=  Л_elector =? ( round ->> RoundsBase_ι_Round_ι_elector ) in
        (* tvm.accept(); *)
        (* if (round.step == RoundStep.WaitingIfValidatorWinElections) { *)
let if1 : bool := ( eqb ( round ->> RoundsBase_ι_Round_ι_step ) RoundsBase_ι_RoundStepP_ι_WaitingIfValidatorWinElections ) in
        (* } else if (round.step == RoundStep.WaitingReward) { *)
let if2 : bool := ( eqb ( round ->> RoundsBase_ι_Round_ι_step ) RoundsBase_ι_RoundStepP_ι_WaitingReward ) in

let (round', l') := if if1 then ({$ round with ( RoundsBase_ι_Round_ι_step , RoundsBase_ι_RoundStepP_ι_WaitingUnfreeze ) $}, l)
                    else if if2  then 
  run ( ↓ ( DePoolContract_Ф_startRoundCompleting round RoundsBase_ι_CompletionReasonP_ι_ValidatorIsPunished ) ) l 
               else (round, injEmbed (VMState_ι_savedDePoolContracts (Ledger_ι_VMState l)) l) in
if req1 then 
        if req2 then 
                if req3 then                
if if1 then Value I 
       else if if2 then Value I 
               else Error (eval_state (↑ε8 InternalErrors_ι_ERROR521) l)
                        else Error (eval_state (↑ε7 Errors_ι_IS_NOT_ELECTOR) l) 
                else Error (eval_state (↑ε7 Errors_ι_IS_NOT_PROXY) l) 
        else Error (eval_state (↑ε8 InternalErrors_ι_ERROR513) l).
Proof.
        intros. destruct l. compute.
        repeat remDestructIf; auto.  
Qed.

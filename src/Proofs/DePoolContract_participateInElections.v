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

Opaque Z.eqb Z.add Z.sub Z.div Z.mul hmapLookup hmapInsert Z.ltb Z.geb Z.leb Z.gtb Z.modulo.

(* Opaque tvm_accept DePoolContract_Ф_checkPureDePoolBalance RoundsBase_Ф_getRound1. *)

Opaque DePoolContract_Ф_checkPureDePoolBalance.

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

(* Parameter f g: bool*nat.
Parameter h : nat -> bool*nat. *)

(* Lemma foo: 
(let (x, _) := f in x) = true -> 

(let (x, t) := f in (if x then g else h t)) = g.
Proof.
  intros.

  match goal with  
  | |- ?x =>
    match x with
    | context [let (x, t) := ?f in @?g x t] => replace (let (x, t) := f in g x t) with (g (fst f) (snd f)) by (symmetry; apply fstsndImplies)
    end
  end.

  match goal with  
  | H : ?x |- _ =>
    match x with
    | context [let (x, t) := ?f in @?g x t] => replace (let (x, t) := f in g x t) with (g (fst f) (snd f)) in H by (symmetry; apply fstsndImplies)
    end
  end.


  rewrite H. auto.  
Qed. *)

(* Opaque default. *)
Lemma DePoolContract_Ф_participateInElections_exec : forall ( Л_queryId : XInteger64 ) 
                                                             ( Л_validatorKey : XInteger256 ) 
                                                             ( Л_stakeAt : XInteger32 ) 
                                                             ( Л_maxFactor : XInteger32 ) 
                                                             ( Л_adnlAddr : XInteger256 ) 
                                                             ( Л_signature : XList XInteger8 ) 
                                                             (l: Ledger), 
let req1 : bool  := ( eval_state ( ↓ msg_sender ) l =? eval_state ( ↑2 ε ValidatorBase_ι_m_validatorWallet ) l ) in
let req2 : bool  := negb ( eval_state ( ↑12 ε DePoolContract_ι_m_poolClosed ) l ) in
let l_tvmAccept  := exec_state ( ↓ tvm_accept ) l in
let ifBalance  : bool  := ( eval_state ( ↓ DePoolContract_Ф_checkPureDePoolBalance ) l_tvmAccept ) in
let l_checkPureDePoolBalance := exec_state ( ↓ DePoolContract_Ф_checkPureDePoolBalance ) l_tvmAccept in
let round := ( eval_state ( ↓ RoundsBase_Ф_getRound1 ) l_checkPureDePoolBalance ) in 
let req3 : bool :=  ( eqb ( round ->> RoundsBase_ι_Round_ι_step )  RoundsBase_ι_RoundStepP_ι_WaitingValidatorRequest  ) in
let req4 : bool :=  ( Л_stakeAt =?  ( round ->>  RoundsBase_ι_Round_ι_supposedElectedAt ) ) in  
let round1 := {$ round with ( RoundsBase_ι_Round_ι_validatorRequest ,
                      ( DePoolLib_ι_RequestC Л_queryId Л_validatorKey Л_stakeAt Л_maxFactor  Л_adnlAddr  Л_signature ) ) $} in  
let l__sendElectionRequest :=
                      exec_state ( ↓ ( ProxyBase_Ф__sendElectionRequest 
                                          ( round1 ->> RoundsBase_ι_Round_ι_proxy)
                                          ( round1 ->> RoundsBase_ι_Round_ι_id) 
                                          ( round1 ->> RoundsBase_ι_Round_ι_stake) 
                                          ( round1 ->> RoundsBase_ι_Round_ι_validatorRequest)
                                          ( round1 ->> RoundsBase_ι_Round_ι_elector) ) ) l_checkPureDePoolBalance in  
let round2 := {$ round1 with ( RoundsBase_ι_Round_ι_step ,  RoundsBase_ι_RoundStepP_ι_WaitingIfStakeAccepted ) $} in 

let l_setRound1 :=  exec_state ( ↓ RoundsBase_Ф_setRound1 round2 ) l__sendElectionRequest in 
                              
let l_returnChange := if ifBalance then exec_state ( ↓ DePoolContract_Ф__returnChange ) l_setRound1 
                                   else exec_state ( ↓ DePoolContract_Ф__returnChange ) l_checkPureDePoolBalance in
                                                          

exec_state ( DePoolContract_Ф_participateInElections Л_queryId Л_validatorKey Л_stakeAt Л_maxFactor Л_adnlAddr Л_signature ) l = 
if req1 then 
   (if req2 then 
    (if ifBalance then   
       (if req3 then 
            (if req4 then l_returnChange
                    else l_checkPureDePoolBalance)
       else l_checkPureDePoolBalance)
       else l_returnChange)
    else l)
else l. 
Proof. 
  intros.
  destruct l.
  compute. idtac.

 (*  match goal with
  | |- ?x =>
    match x with
    | context  [match DePoolContract_Ф_checkPureDePoolBalance
                with
                | SimpleState c => c
                end ?l] => destruct (match DePoolContract_Ф_checkPureDePoolBalance
                with
                | SimpleState c => c
                end l)
    end
  end.          *)     

  repeat (
  
  match goal with
    | |- ?x =>
      match x with
     (*  | context  [match DePoolContract_Ф_checkPureDePoolBalance
                  with
                  | SimpleState c => c
                  end ?l] => destruct (match DePoolContract_Ф_checkPureDePoolBalance
                  with
                  | SimpleState c => c
                  end l) as [v l]; destruct l ; compute *)
      | context [let (x, t) := ?f in @?g x t] => replace (let (x, t) := f in g x t) with (g (fst f) (snd f)) by (symmetry; apply fstsndImplies)  ; simpl
      | context [if ?b then _ else _] =>  repeat rewrite ifSimpleState ; 
                                            repeat rewrite ifFunApply ;
                                            (* compute ; *)
                                            (* let rem := fresh "rem" in  *)
                                            (* set (rem:= b) ;  *)
                                            case b ; simpl(* ; intros *)
        | _ =>  auto
      end
  end) . 
  
Qed. 



Lemma DePoolContract_Ф_participateInElections_eval : forall ( Л_queryId : XInteger64 ) 
                                                             ( Л_validatorKey : XInteger256 ) 
                                                             ( Л_stakeAt : XInteger32 ) 
                                                             ( Л_maxFactor : XInteger32 ) 
                                                             ( Л_adnlAddr : XInteger256 ) 
                                                             ( Л_signature : XList XInteger8 ) 
                                                             (l: Ledger), 
let req1 : bool  :=  ( eval_state ( ↓ msg_sender ) l =? eval_state ( ↑2 ε ValidatorBase_ι_m_validatorWallet ) l ) in
let req2 : bool  :=  negb ( eval_state ( ↑12 ε DePoolContract_ι_m_poolClosed ) l ) in
let l_tvmAccept := exec_state ( ↓ tvm_accept ) l in
let if1  : bool   := ( eval_state ( ↓ DePoolContract_Ф_checkPureDePoolBalance ) l_tvmAccept ) in 
let l_checkPureDePoolBalance := exec_state ( ↓ DePoolContract_Ф_checkPureDePoolBalance ) l_tvmAccept in
let round := ( eval_state ( ↓ RoundsBase_Ф_getRound1 ) l_checkPureDePoolBalance ) in 
let req3 : bool :=  ( eqb ( round ->> RoundsBase_ι_Round_ι_step )  
                             RoundsBase_ι_RoundStepP_ι_WaitingValidatorRequest  ) in
let req4 :=  ( Л_stakeAt  =?  ( round ->>  RoundsBase_ι_Round_ι_supposedElectedAt ) ) in  
eval_state (  DePoolContract_Ф_participateInElections Л_queryId Л_validatorKey Л_stakeAt Л_maxFactor Л_adnlAddr Л_signature ) l = 

if req1 then 
   (if req2 then 
    (if if1 then   
       (if req3 then 
            (if req4 then Value I
                    else Error ( eval_state ( ↑7 ε Errors_ι_INVALID_ELECTION_ID ) l_checkPureDePoolBalance ))
       else Error ( eval_state ( ↑7 ε Errors_ι_NO_ELECTION_ROUND ) l_checkPureDePoolBalance ))
       else Value I)
    else Error ( eval_state ( ↑7 ε Errors_ι_DEPOOL_IS_CLOSED ) l ))
else Error ( eval_state ( ↑7 ε Errors_ι_IS_NOT_VALIDATOR ) l ). 
 Proof. 
  intros.
  destruct l. 
  compute. idtac.
  idtac.

 repeat (
  
  
  match goal with
    | |- ?x =>
      match x with
      | context [let (x, t) := ?f in @?g x t] => replace (let (x, t) := f in g x t) with (g (fst f) (snd f)) by (symmetry; apply fstsndImplies)  ; simpl
        | context [if ?b then _ else _] =>  repeat rewrite ifSimpleState ; 
                                            repeat rewrite ifFunApply ;
                                            (* compute ; *)
                                            (* let rem := fresh "rem" in  *)
                                            (* set (rem:= b) ;  *)
                                            case_eq b ; simpl; intros
        | _ => auto
      end
  end) . 

 Qed.  


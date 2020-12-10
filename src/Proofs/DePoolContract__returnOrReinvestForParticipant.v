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

Ltac remDestructIf :=
  match goal with
    | |- ?x =>
      match x with
        | context [if ?b then _ else _] => case_eq b ; intros
        | _ => idtac
      end
  end.

  Ltac pr_numgoals := let n := numgoals in idtac "There are" n "goals".

Opaque Z.eqb Z.add Z.sub Z.div Z.mul hmapLookup hmapInsert Z.ltb Z.geb Z.leb Z.gtb Z.modulo.

(*
function _returnOrReinvestForParticipant(
        Round round2,
        Round round0,
        address addr,
        StakeValue stakes,
        bool isValidator
    ) private returns (Round, Round) {
        uint64 stakeSum = stakeSum(stakes);
        bool stakeIsLost = round2.completionReason == CompletionReason.ValidatorIsPunished;
        optional(DePoolLib.Participant) optParticipant = fetchParticipant(addr);
        require(optParticipant.hasValue(), InternalErrors.ERROR511);
        DePoolLib.Participant participant = optParticipant.get();
        --participant.roundQty;
        uint64 lostFunds = stakeIsLost? (round2.stake - round2.unused) - round2.recoveredStake : 0;  //header

        // upd ordinary stake
        uint64 newStake;
        uint64 reward;
        if (stakeIsLost) {
            if (isValidator) {
                newStake = stakes.ordinary;
                uint64 delta = math.min(newStake, lostFunds);
                newStake -= delta;
                lostFunds -= delta;
                round2.validatorRemainingStake += newStake;
            } else {
                newStake = math.muldiv(
                    round2.unused + round2.recoveredStake - round2.validatorRemainingStake,
                    stakes.ordinary,
                    round2.stake - round2.validatorStake
                );
            }
        } else {
            reward = math.muldiv(stakeSum, round2.rewards, round2.stake);
            participant.reward += reward;
            newStake = stakes.ordinary + reward;
        }
        round2.handledStakesAndRewards += newStake;  //tailer1

        // upd vesting
        optional(InvestParams) newVesting = stakes.vesting;
        if (newVesting.hasValue()) {
            if (stakeIsLost) {
                InvestParams params = newVesting.get();
                if (isValidator) {
                    uint64 delta = math.min(params.amount, lostFunds);
                    params.amount -= delta;
                    lostFunds -= delta;
                    round2.validatorRemainingStake += params.amount;
                } else {
                    params.amount = math.muldiv(
                        round2.unused + round2.recoveredStake - round2.validatorRemainingStake,
                        params.amount,
                        round2.stake - round2.validatorStake
                    );
                }
                newVesting.set(params);
            }
            round2.handledStakesAndRewards += newVesting.get().amount;
            uint64 withdrawalVesting;
            (newVesting, withdrawalVesting) = cutWithdrawalValue(newVesting.get());
            newStake += withdrawalVesting;
        }   //tailer2

        // pause stake and newStake
        uint64 attachedValue = 1;
        uint64 curPause = math.min(participant.withdrawValue, newStake);
        attachedValue += curPause;
        participant.withdrawValue -= curPause;
        newStake -= curPause;
        if (newStake < m_minStake) { // whole stake is transferred to the participant
            attachedValue += newStake;
            newStake = 0;
        }   //tailer3

        // upd lock
        optional(InvestParams) newLock = stakes.lock;
        if (newLock.hasValue()) {
            if (stakeIsLost) {
                InvestParams params = newLock.get();
                if (isValidator) {
                    uint64 delta = math.min(params.amount, lostFunds);
                    params.amount -= delta;
                    lostFunds -= delta;
                    round2.validatorRemainingStake += params.amount;
                } else {
                    params.amount = math.muldiv(
                        round2.unused + round2.recoveredStake - round2.validatorRemainingStake,
                        params.amount,
                        round2.stake - round2.validatorStake
                    );
                }
                newLock.set(params);
            }
            round2.handledStakesAndRewards += newLock.get().amount;
            uint64 withdrawalLock;
            (newLock, withdrawalLock) = cutWithdrawalValue(newLock.get());
            if (withdrawalLock != 0) {
                newLock.get().owner.transfer(withdrawalLock, false, 1);
            }
        }  //tailer4

        if (m_poolClosed) {
            attachedValue += newStake;
            if (newVesting.hasValue()) {
                newVesting.get().owner.transfer(newVesting.get().amount, false, 1);
            }
            if (newLock.hasValue()) {
                newLock.get().owner.transfer(newLock.get().amount, false, 1);
            }
        } else {
            if (newVesting.hasValue() && newVesting.get().amount == 0) newVesting.reset();
            if (newLock.hasValue() && newLock.get().amount == 0) newLock.reset();

            if (!participant.reinvest) {
                attachedValue += newStake;
                newStake = 0;
            }
            (round0, participant) = _addStakes(round0, participant, addr, newStake, newVesting, newLock);
        }

        _setOrDeleteParticipant(addr, participant);
        IParticipant(addr).onRoundComplete{value: attachedValue, bounce: false}(
            round2.id,
            reward,
            stakes.ordinary,
            stakes.vesting.hasValue() ? stakes.vesting.get().amount : 0,
            stakes.lock.hasValue() ? stakes.lock.get().amount : 0,
            participant.reinvest,
            uint8(round2.completionReason)
        );

        return (round0, round2);
    }
*)

Opaque RoundsBase_Ф__addStakes DePoolContract_Ф_cutWithdrawalValue RoundsBase_Ф_stakeSum.

Definition DePoolContract_Ф__returnOrReinvestForParticipant' ( Л_round2 : RoundsBase_ι_Round )
                                                              ( Л_round0 : RoundsBase_ι_Round )
                                                              ( Л_addr : XAddress )
                                                              ( Л_stakes : RoundsBase_ι_StakeValue ) 
                                                              ( Л_isValidator : XBool )
                                                              ( f : XBool -> XBool ->  RoundsBase_ι_StakeValue -> XInteger -> XAddress -> LedgerT (RoundsBase_ι_Round # RoundsBase_ι_Round) )
                                                  : LedgerT ( XErrorValue ( RoundsBase_ι_Round # RoundsBase_ι_Round ) XInteger ) := 
(↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_round2 := $ Л_round2) >> 
(↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_round0 := $ Л_round0) >>
U0! Л_stakeSum := RoundsBase_Ф_stakeSum (! $ Л_stakes !) ;
U0! Л_stakeIsLost := ($ (Л_round2 ->> RoundsBase_ι_Round_ι_completionReason) ) ?== ($ RoundsBase_ι_CompletionReasonP_ι_ValidatorIsPunished) ; 		
U0! Л_optParticipant := ParticipantBase_Ф_fetchParticipant (! $ Л_addr !) ; 
Require {{ $ Л_optParticipant ->hasValue , ↑8 D2! InternalErrors_ι_ERROR511 }} ; 

(↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_participant := $ Л_optParticipant ->get) >> 
(↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_participant ^^ DePoolLib_ι_Participant_ι_roundQty !--) >>

( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds := $ Л_stakeIsLost ? 
   ( D1! (D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2) ^^ RoundsBase_ι_Round_ι_stake !- 
     D1! (D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2) ^^ RoundsBase_ι_Round_ι_unused ) !- 
     D1! (D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2) ^^ RoundsBase_ι_Round_ι_recoveredStake 
                              ::: $ xInt0 ) >> f Л_stakeIsLost Л_isValidator Л_stakes Л_stakeSum Л_addr. 
                              
                              

Definition DePoolContract_Ф__returnOrReinvestForParticipant_tailer1 ( Л_stakeIsLost: XBool ) 
                                                                    ( Л_isValidator : XBool )
                                                                    ( Л_stakes : RoundsBase_ι_StakeValue ) 
                                                                    ( Л_stakeSum: XInteger)
                                                                    (Л_addr : XAddress)
                                                                    ( f : RoundsBase_ι_StakeValue -> XBool -> XBool -> XAddress -> LedgerT (RoundsBase_ι_Round # RoundsBase_ι_Round) )
                                                  : LedgerT ( RoundsBase_ι_Round # RoundsBase_ι_Round ) :=  
(↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_newStake := $default) >>
(↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_reward := $default) >>

(
	If ($ Л_stakeIsLost) then {
   ( If ( $ Л_isValidator ) 
     then {
           ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_newStake := $ ( Л_stakes ->> RoundsBase_ι_StakeValue_ι_ordinary ) ) >>  
           U0! Л_delta := math->min2 (! ↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newStake ,
                                         ↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds !) ; 
           ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_newStake !-= $ Л_delta ) >>  
           ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds !-= $ Л_delta ) >> 
           ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ^^ RoundsBase_ι_Round_ι_validatorRemainingStake
                       !+= D2! LocalState_ι__returnOrReinvestForParticipant_Л_newStake )
     } 
     else {
		(↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_newStake := math->muldiv (! 
                D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^  RoundsBase_ι_Round_ι_unused !+
                D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^  RoundsBase_ι_Round_ι_recoveredStake !-
                D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^  RoundsBase_ι_Round_ι_validatorRemainingStake, 
				$ Л_stakes ->> RoundsBase_ι_StakeValue_ι_ordinary , 
				D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^  RoundsBase_ι_Round_ι_stake !-
        D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^  RoundsBase_ι_Round_ι_validatorStake !))
} )
	} else {
    (↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_reward := math->muldiv (! $ Л_stakeSum , 
        D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^  RoundsBase_ι_Round_ι_rewards ,
        D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^  RoundsBase_ι_Round_ι_stake !) ) >>
		(↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_participant ^^ DePoolLib_ι_Participant_ι_reward 
                           !+=  D2! LocalState_ι__returnOrReinvestForParticipant_Л_reward ) >>
		(↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_newStake 
    := $ ( Л_stakes ->> RoundsBase_ι_StakeValue_ι_ordinary ) !+ 
           (D2! LocalState_ι__returnOrReinvestForParticipant_Л_reward))
	}
) >> 
( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ^^  RoundsBase_ι_Round_ι_handledStakesAndRewards 
  !+= D2! LocalState_ι__returnOrReinvestForParticipant_Л_newStake ) >> f Л_stakes Л_stakeIsLost Л_isValidator Л_addr.
 

Definition DePoolContract_Ф__returnOrReinvestForParticipant_tailer2  (Л_stakes : RoundsBase_ι_StakeValue ) 
                                                                     (Л_stakeIsLost : XBool )  
                                                                     (Л_isValidator : XBool ) 
                                                                     (Л_addr : XAddress)
                                                                     (f: RoundsBase_ι_StakeValue -> XBool -> XBool -> XAddress -> LedgerT (RoundsBase_ι_Round # RoundsBase_ι_Round) )
                                                            : LedgerT ( RoundsBase_ι_Round # RoundsBase_ι_Round ) :=  
(↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_newVesting := 
                 $ ( Л_stakes ->> RoundsBase_ι_StakeValue_ι_vesting ) ) >> 

( If ( ( ↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newVesting ) ->hasValue )
then
{ (
	If ($ Л_stakeIsLost) then {
  (↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_params := 
             ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_newVesting ) ->get ) >>
   ( If ( $ Л_isValidator ) 
     then {
           U0! Л_delta := math->min2 (! ↑17 D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_params ) ^^ RoundsBase_ι_InvestParams_ι_amount ,
                                         ↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds !) ; 
           ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_params ^^ 
                                             RoundsBase_ι_InvestParams_ι_amount !-= $ Л_delta ) >>  
           ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds !-= $ Л_delta ) >> 
           ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ^^ RoundsBase_ι_Round_ι_validatorRemainingStake
                       !+= D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_params )
                                            ^^ RoundsBase_ι_InvestParams_ι_amount )
     } 
     else {
		( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_params ^^ 
                                             RoundsBase_ι_InvestParams_ι_amount := math->muldiv (! 
				D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^  RoundsBase_ι_Round_ι_unused !+
        D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^  RoundsBase_ι_Round_ι_recoveredStake !-
        D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^  RoundsBase_ι_Round_ι_validatorRemainingStake
              , 
				D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_params )
                                            ^^ RoundsBase_ι_InvestParams_ι_amount , 
				D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^  RoundsBase_ι_Round_ι_stake !-
        D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^  RoundsBase_ι_Round_ι_validatorStake !) )
} ) >>
 ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_newVesting ->set
                                                ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_params ) )
	}  ) >>

  ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ^^ RoundsBase_ι_Round_ι_handledStakesAndRewards !+=
  D1! ( ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_newVesting ) ->get  ) ^^ 
         RoundsBase_ι_InvestParams_ι_amount ) >>
  U0! Л_withdrawalVesting := $ default ;
  U0! {( Л_newVesting , Л_withdrawalVesting )} := DePoolContract_Ф_cutWithdrawalValue 
             (! ↑17 ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_newVesting ) ->get !) ;
  ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_newVesting := $ Л_newVesting ) >>
  (↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_newStake !+= $ Л_withdrawalVesting ) 
} ) >> f Л_stakes Л_stakeIsLost Л_isValidator Л_addr.


Definition DePoolContract_Ф__returnOrReinvestForParticipant_tailer3  
                   (Л_stakes : RoundsBase_ι_StakeValue) 
                   (Л_stakeIsLost : XBool )
                   (Л_isValidator : XBool )
                   (Л_addr : XAddress)
                   (f: RoundsBase_ι_StakeValue -> XBool -> XBool -> XAddress -> LedgerT (RoundsBase_ι_Round # RoundsBase_ι_Round) )
                                               : LedgerT ( RoundsBase_ι_Round # RoundsBase_ι_Round ) := 
(↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_attachedValue := $ xInt1) >>
(* uint64 curPause = math.min(participant.withdrawValue, newStake); *)
U0! Л_curPause := math->min2 (! (D1! (↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_participant) ^^ DePoolLib_ι_Participant_ι_withdrawValue) ,
								(↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newStake) !) ;
(* attachedValue += curPause; *)
( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_attachedValue !+= $Л_curPause ) >>
(* participant.withdrawValue -= curPause; *)
( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_participant ^^ DePoolLib_ι_Participant_ι_withdrawValue !-= 
                                 $Л_curPause ) >>
(* newStake -= curPause; *)
( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_newStake !-= $Л_curPause ) >>
(* if (newStake < m_minStake) { // whole stake is transferred to unused
	attachedValue += newStake;
	newStake = 0;
} *)
( If ( ( ↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newStake ) ?< 
                                          (↑12 D2! DePoolContract_ι_m_minStake ) ) then {
	( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_attachedValue !+= 
                           D2! LocalState_ι__returnOrReinvestForParticipant_Л_newStake ) >>
	( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_newStake := $xInt0 )
} ) >> f Л_stakes Л_stakeIsLost Л_isValidator Л_addr.

Definition DePoolContract_Ф__returnOrReinvestForParticipant_tailer4  
                                              (Л_stakes : RoundsBase_ι_StakeValue) 
                                              (Л_stakeIsLost : XBool )
                                              (Л_isValidator : XBool )
                                              (Л_addr : XAddress)
                                              (f: XAddress -> RoundsBase_ι_StakeValue -> LedgerT (RoundsBase_ι_Round # RoundsBase_ι_Round) )
                                               : LedgerT ( RoundsBase_ι_Round # RoundsBase_ι_Round ) := 
(↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_newLock := 
                 $ ( Л_stakes ->> RoundsBase_ι_StakeValue_ι_lock ) ) >> (* $ [( default , default )]. *) 

( If ( ( ↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newLock ) ->hasValue )
then
{ (
	If ($ Л_stakeIsLost) then {
  (↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_params := 
             ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_newLock ) ->get ) >>
   ( If ( $ Л_isValidator ) 
     then {
           U0! Л_delta := math->min2 (! ↑17 D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_params ) ^^ RoundsBase_ι_InvestParams_ι_amount ,
                                         ↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds !) ; 
           ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_params ^^ 
                                             RoundsBase_ι_InvestParams_ι_amount !-= $ Л_delta ) >>  
           ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds !-= $ Л_delta ) >> 
           ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ^^ RoundsBase_ι_Round_ι_validatorRemainingStake
                       !+= D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_params )
                                            ^^ RoundsBase_ι_InvestParams_ι_amount )
     } 
     else {
		( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_params ^^ 
                                             RoundsBase_ι_InvestParams_ι_amount := math->muldiv (! 
				D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^  RoundsBase_ι_Round_ι_unused !+
        D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^  RoundsBase_ι_Round_ι_recoveredStake !-
        D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^  RoundsBase_ι_Round_ι_validatorRemainingStake
              , 
				D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_params )
                                            ^^ RoundsBase_ι_InvestParams_ι_amount , 
				D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^  RoundsBase_ι_Round_ι_stake !-
        D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^  RoundsBase_ι_Round_ι_validatorStake !) )
} ) >>
 ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_newLock ->set
                                                ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_params ) )
	}  ) >>

  ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ^^ RoundsBase_ι_Round_ι_handledStakesAndRewards !+=
  D1! ( ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_newLock ) ->get  ) ^^ 
         RoundsBase_ι_InvestParams_ι_amount ) >>
  U0! Л_withdrawalLock := $ default ;
  U0! {( Л_newLock , Л_withdrawalLock )} := DePoolContract_Ф_cutWithdrawalValue 
             (! ↑17 ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_newLock ) ->get !) ;
  ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_newLock := $ Л_newLock ) >>
  (If  ( $Л_withdrawalLock ?!= $xInt0 ) then {
       (D1! ((↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newLock) ->get) ^^ RoundsBase_ι_InvestParams_ι_owner ) ->transfer 
            (! $Л_withdrawalLock  , $xBoolFalse, $ xInt1 !)
     } ) 
} )  >> f Л_addr Л_stakes.




(* if (m_poolClosed) {
	attachedValue += newStake;
	if (newVesting.hasValue()) {
		newVesting.get().owner.transfer(newVesting.get().amount, false, 1);
	}
	if (newLock.hasValue()) {
		newLock.get().owner.transfer(newLock.get().amount, false, 1);
	}
} else {
	if (newVesting.hasValue() && newVesting.get().amount == 0) newVesting.reset();
	if (newLock.hasValue() && newLock.get().amount == 0) newLock.reset();

	if (!participant.reinvest) {
		attachedValue += newStake;
		newStake = 0;
	}
	(round0, participant) = _addStakes(round0, participant, addr, newStake, newVesting, newLock);
} *)

Definition DePoolContract_Ф__returnOrReinvestForParticipant_tailer5 (Л_addr : XAddress) 
                                                                    (Л_stakes : RoundsBase_ι_StakeValue)
                            (f: XAddress -> RoundsBase_ι_StakeValue -> LedgerT (RoundsBase_ι_Round # RoundsBase_ι_Round) )
                            : LedgerT ( RoundsBase_ι_Round # RoundsBase_ι_Round ):= 
(If (↑12 D2! DePoolContract_ι_m_poolClosed) then { 
	(↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_attachedValue !+= D2! LocalState_ι__returnOrReinvestForParticipant_Л_newStake) >>
	(If ((↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newVesting) ->hasValue) then { 
	(D1! ((↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newVesting) ->get) ^^ RoundsBase_ι_InvestParams_ι_owner ) ->transfer 
                                (! D1! ((↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newVesting) ->get) ^^ RoundsBase_ι_InvestParams_ι_amount , $xBoolFalse, $ xInt1 !)
	}) >>
	(If ((↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newLock) ->hasValue) then { 
	(D1! ((↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newLock) ->get) ^^ RoundsBase_ι_InvestParams_ι_owner ) ->transfer 
            (! D1! ((↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newLock) ->get) ^^ RoundsBase_ι_InvestParams_ι_amount , $xBoolFalse, $ xInt1 !)
    }) 
 } else { 
	(If ((↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newVesting) ->hasValue) !& 
		(D1! ((↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newVesting) ->get) ^^ RoundsBase_ι_InvestParams_ι_amount ?== $xInt0)
	then { 
		 ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_newVesting ->reset 
	}) >>
	(If ((↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newLock) ->hasValue) !& 
		(D1! ((↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newLock) ->get) ^^ RoundsBase_ι_InvestParams_ι_amount ?== $xInt0)
	then { 
		↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_newLock ->reset 
	}) >>
	(If (D1! (↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_participant) ^^ DePoolLib_ι_Participant_ι_reinvest) then { 
		(↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_attachedValue !+= D2! LocalState_ι__returnOrReinvestForParticipant_Л_newStake) >>
		(↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_newStake := $xInt0)
	}) >>
	(↑↑17 U2! {( LocalState_ι__returnOrReinvestForParticipant_Л_round0, 
			    LocalState_ι__returnOrReinvestForParticipant_Л_participant )} := RoundsBase_Ф__addStakes (! (↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_round0) , 
				(↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_participant) ,
				$Л_addr ,
				(↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newStake) , 
				(↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newVesting) ,
				(↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newLock)   !) )
 
 }) >> f Л_addr Л_stakes.



 Definition DePoolContract_Ф__returnOrReinvestForParticipant_tailer6 (Л_addr : XAddress) 
                                                                     (Л_stakes : RoundsBase_ι_StakeValue): LedgerT ( RoundsBase_ι_Round # RoundsBase_ι_Round ) := 
 (* _setOrDeleteParticipant(addr, participant); *)
 ParticipantBase_Ф__setOrDeleteParticipant (! $Л_addr , (↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_participant)  !) >>
(* IParticipant(addr).onRoundComplete{value: attachedValue, bounce: false}(
	completedRound.id,
	reward,
	stakes.ordinary,
	stakes.vesting.hasValue() && stakes.vesting.get().isActive? stakes.vesting.get().amount : 0,
	stakes.lock.hasValue() && stakes.lock.get().isActive? stakes.lock.get().amount : 0,
	participant.reinvest,
	uint8(completedRound.completionReason)
); *)
 ( ->sendMessage {|| contractAddress := $ Л_addr ,
			   contractFunction :=  IParticipant_И_onRoundCompleteF (!! ↑17 D1! (D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2) ^^ RoundsBase_ι_Round_ι_id ,
																	   ↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_reward ,
																	   $ Л_stakes ->> RoundsBase_ι_StakeValue_ι_ordinary ,
																	   (($ Л_stakes ->> RoundsBase_ι_StakeValue_ι_vesting) ->hasValue ) ? 
																			  (D1! (($ Л_stakes ->> RoundsBase_ι_StakeValue_ι_vesting) ->get) ^^ RoundsBase_ι_InvestParams_ι_amount) ::: $xInt0, 
																	   (($ Л_stakes ->> RoundsBase_ι_StakeValue_ι_lock) ->hasValue ) ? 
																			  (D1! (($ Л_stakes ->> RoundsBase_ι_StakeValue_ι_lock) ->get) ^^ RoundsBase_ι_InvestParams_ι_amount) ::: $xInt0 ,
																	   D1! (↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_participant) ^^ DePoolLib_ι_Participant_ι_reinvest , 
																	   (completionReason2XInteger (!! ↑17 D1! (D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2) ^^ RoundsBase_ι_Round_ι_completionReason !!) ) 
			                                                          !!) ,
			   contractMessage := {|| messageValue := ↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_attachedValue , 
			                          messageBounce := $xBoolFalse ||} ||} ) >> 
(*  return (round0, round2); *)
 return# ( ↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_round0 , 
           ↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ).


(*      uint64 stakeSum = stakeSum(stakes);
        bool stakeIsLost = round2.completionReason == CompletionReason.ValidatorIsPunished;
        optional(DePoolLib.Participant) optParticipant = fetchParticipant(addr);
        require(optParticipant.hasValue(), InternalErrors.ERROR511);
        DePoolLib.Participant participant = optParticipant.get();
        --participant.roundQty;
        uint64 lostFunds = stakeIsLost? (round2.stake - round2.unused) - round2.recoveredStake : 0;  //header *)           

Lemma DePoolContract_Ф__returnOrReinvestForParticipant'_exec : forall
                                                                (l : Ledger)
                                                                ( Л_round2 : RoundsBase_ι_Round )
                                                                ( Л_round0 : RoundsBase_ι_Round )
                                                                ( Л_addr : XAddress )
                                                                ( Л_stakes : RoundsBase_ι_StakeValue ) 
                                                                ( Л_isValidator : XBool ) 
                                                                ( f : XBool -> XBool ->  RoundsBase_ι_StakeValue -> XInteger -> XAddress -> LedgerT (RoundsBase_ι_Round # RoundsBase_ι_Round) ),
exec_state (DePoolContract_Ф__returnOrReinvestForParticipant' Л_round2 Л_round0 Л_addr Л_stakes Л_isValidator f) l =

    let (stakeSum, l_sum) := run (↓ RoundsBase_Ф_stakeSum Л_stakes) l in
    let stakeIsLost : bool := eqb (Л_round2 ->> RoundsBase_ι_Round_ι_completionReason) RoundsBase_ι_CompletionReasonP_ι_ValidatorIsPunished in
    let optParticipant := eval_state (↓ ParticipantBase_Ф_fetchParticipant Л_addr) l_sum in
    let isSomeParticipant : bool := isSome optParticipant in
    let participant := maybeGet optParticipant in 
    let participant_newRoundQty :=
        {$ participant with (DePoolLib_ι_Participant_ι_roundQty, (participant ->> DePoolLib_ι_Participant_ι_roundQty) - 1 ) $} in 
    let lostFunds := if stakeIsLost
        then    (Л_round2 ->> RoundsBase_ι_Round_ι_stake  -
                 Л_round2 ->> RoundsBase_ι_Round_ι_unused)  -
                 Л_round2 ->> RoundsBase_ι_Round_ι_recoveredStake
        else 0 in 
    let l_local := {$ l_sum With (LocalState_ι__returnOrReinvestForParticipant_Л_round2, Л_round2);
                                 (LocalState_ι__returnOrReinvestForParticipant_Л_round0, Л_round0);
                                 (LocalState_ι__returnOrReinvestForParticipant_Л_participant, participant_newRoundQty);
                                 (LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds, lostFunds) $} in
    if  isSomeParticipant then                             
        exec_state (f stakeIsLost Л_isValidator Л_stakes stakeSum Л_addr) l_local
        else {$ l_sum With (LocalState_ι__returnOrReinvestForParticipant_Л_round2, Л_round2);
                           (LocalState_ι__returnOrReinvestForParticipant_Л_round0, Л_round0) $}.
Proof.
    intros. destruct l. 
  
    destruct Ledger_ι_DebugDePool, Ledger_ι_ValidatorBase, Ledger_ι_ProxyBase, Ledger_ι_ConfigParamsBase, Ledger_ι_ParticipantBase, 
    Ledger_ι_DePoolHelper, Ledger_ι_Errors, Ledger_ι_InternalErrors, Ledger_ι_DePoolLib, Ledger_ι_DePoolProxyContract, 
    Ledger_ι_RoundsBase, Ledger_ι_DePoolContract, Ledger_ι_DePool, Ledger_ι_Participant, Ledger_ι_TestElector, 
    Ledger_ι_VMState, Ledger_ι_LocalState.
  
    destruct Л_round2.
  
    compute. idtac.
  
    Time repeat (
    
    time match goal with
  
      | |- ?x =>
        match x with
               
        | context [if ?b then _ else _] =>  idtac "if..." b; 
                                            repeat rewrite ifSimpleState ; 
                                            repeat rewrite ifFunApply ;
                                              (* compute ; *)
                                              (* let rem := fresh "rem" in  *)
                                              (* set (rem:= b) ;  *)
                                            case_eq b ; 
                                            (* simpl;  *)
                                            intros                                                              
        | _ =>  idtac "solving..." x; tryif solve [auto] then idtac "solved" else idtac "not solved"
        end
  
    end) . idtac.

  match goal with 
  | |- ?x  => match x with 
              | context [RoundsBase_Ф_stakeSum Л_stakes] => remember (RoundsBase_Ф_stakeSum Л_stakes) as l
              end
  end.
  destruct l.
  
  match goal with 
  | |- ?x  => match x with 
              | context [p ?a] => remember (p a)
              end
  end.
  
  destruct p0; auto.

  Time repeat (
    
    time match goal with
  
      | |- ?x =>
        match x with
               
        | context [if ?b then _ else _] =>  idtac "if..." b; 
                                            repeat rewrite ifSimpleState ; 
                                            repeat rewrite ifFunApply ;
                                              (* compute ; *)
                                              (* let rem := fresh "rem" in  *)
                                              (* set (rem:= b) ;  *)
                                            case_eq b ; 
                                            (* simpl;  *)
                                            intros                                                              
        | _ =>  idtac "solving..." x; tryif solve [auto] then idtac "solved" else idtac "not solved"
        end
  
    end) . idtac.

  match goal with 
  | |- ?x  => match x with 
              | context [f ?a ?b ?c ?d ?e] => remember (f a b c d e) as l0
              end
  end.
  destruct l0.
  
  match goal with 
  | |- ?x  => match x with 
              | context [p0 ?a] => remember (p0 a)
              end
  end.

  destruct p1; auto.
  match goal with 
  | |- ?x  => match x with 
              | context [RoundsBase_Ф_stakeSum Л_stakes] => remember (RoundsBase_Ф_stakeSum Л_stakes) as l
              end
  end.
  destruct l.
  
  match goal with 
  | |- ?x  => match x with 
              | context [p ?a] => remember (p a)
              end
  end.
  
  destruct p0; auto.

  Time repeat (
    
    time match goal with
  
      | |- ?x =>
        match x with
               
        | context [if ?b then _ else _] =>  idtac "if..." b; 
                                            repeat rewrite ifSimpleState ; 
                                            repeat rewrite ifFunApply ;
                                              (* compute ; *)
                                              (* let rem := fresh "rem" in  *)
                                              (* set (rem:= b) ;  *)
                                            case_eq b ; 
                                            (* simpl;  *)
                                            intros                                                              
        | _ =>  idtac "solving..." x; tryif solve [auto] then idtac "solved" else idtac "not solved"
        end
  
    end) . idtac.

    match goal with 
    | |- ?x  => match x with 
                | context [f ?a ?b ?c ?d ?e] => remember (f a b c d e) as l0
                end
    end.
    destruct l0.
    
    match goal with 
    | |- ?x  => match x with 
                | context [p0 ?a] => remember (p0 a)
                end
    end.
  
    destruct p1; auto.

Qed.    


(* Definition DePoolContract_Ф__returnOrReinvestForParticipant_tailer1 ( Л_stakeIsLost: XBool ) 
                                                                    ( Л_isValidator : XBool )
                                                                    ( Л_stakes : RoundsBase_ι_StakeValue ) 
                                                                    ( Л_stakeSum: XInteger)
                                                                    (Л_addr : XAddress)
                                                                    ( f : RoundsBase_ι_StakeValue -> XBool -> XBool -> XAddress -> LedgerT (RoundsBase_ι_Round # RoundsBase_ι_Round) )
                                                  : LedgerT ( RoundsBase_ι_Round # RoundsBase_ι_Round ) :=  
(↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_newStake := $default) >>
(↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_reward := $default) >>

(
	If ($ Л_stakeIsLost) then {
   ( If ( $ Л_isValidator ) 
     then {
           ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_newStake := $ ( Л_stakes ->> RoundsBase_ι_StakeValue_ι_ordinary ) ) >>  
           U0! Л_delta := math->min2 (! ↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newStake ,
                                         ↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds !) ; 
           ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_newStake !-= $ Л_delta ) >>  
           ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds !-= $ Л_delta ) >> 
           ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ^^ RoundsBase_ι_Round_ι_validatorRemainingStake
                       !+= D2! LocalState_ι__returnOrReinvestForParticipant_Л_newStake )
     } 
     else {
		(↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_newStake := math->muldiv (! 
				D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^  RoundsBase_ι_Round_ι_unused , 
				$ Л_stakes ->> RoundsBase_ι_StakeValue_ι_ordinary , 
				D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^  RoundsBase_ι_Round_ι_stake !-
        D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^  RoundsBase_ι_Round_ι_validatorStake !))
} )
	} else {
    (↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_reward := math->muldiv (! $ Л_stakeSum , 
        D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^  RoundsBase_ι_Round_ι_rewards ,
        D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^  RoundsBase_ι_Round_ι_stake !) ) >>
		(↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_participant ^^ DePoolLib_ι_Participant_ι_reward 
                           !+=  D2! LocalState_ι__returnOrReinvestForParticipant_Л_reward ) >>
		(↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_newStake 
    := $ ( Л_stakes ->> RoundsBase_ι_StakeValue_ι_ordinary ) !+ 
           (D2! LocalState_ι__returnOrReinvestForParticipant_Л_reward))
	}
) >> 
( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ^^  RoundsBase_ι_Round_ι_handledStakesAndRewards 
  !+= D2! LocalState_ι__returnOrReinvestForParticipant_Л_newStake ) >> f Л_stakes Л_stakeIsLost Л_isValidator Л_addr. *)
(*  uint64 newStake;
        uint64 reward;
        if (stakeIsLost) {
            if (isValidator) {
                newStake = stakes.ordinary;
                uint64 delta = math.min(newStake, lostFunds);
                newStake -= delta;
                lostFunds -= delta;
                round2.validatorRemainingStake += newStake;
            } else {
                newStake = math.muldiv(
                    round2.unused + round2.recoveredStake - round2.validatorRemainingStake,
                    stakes.ordinary,
                    round2.stake - round2.validatorStake
                );
            }
        } else {
            reward = math.muldiv(stakeSum, round2.rewards, round2.stake);
            participant.reward += reward;
            newStake = stakes.ordinary + reward;
        }
        round2.handledStakesAndRewards += newStake;  //tailer1 *)


  Lemma DePoolContract_Ф__returnOrReinvestForParticipant_tailer1_exec : forall
                                                            (l : Ledger)
                                                            ( Л_stakeIsLost: XBool ) 
                                                            ( Л_isValidator : XBool )
                                                            ( Л_stakes : RoundsBase_ι_StakeValue ) 
                                                            ( Л_stakeSum: XInteger)
                                                            ( Л_addr : XAddress)
                                                            ( f : RoundsBase_ι_StakeValue -> XBool -> XBool -> XAddress -> LedgerT (RoundsBase_ι_Round # RoundsBase_ι_Round) ),

 exec_state (DePoolContract_Ф__returnOrReinvestForParticipant_tailer1 Л_stakeIsLost Л_isValidator Л_stakes Л_stakeSum Л_addr f) l =

let newStake := 0 in
let reward := 0 in
let lostFunds := eval_state (↑17 ε LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds) l in
let round2 :=  eval_state (↑17 ε LocalState_ι__returnOrReinvestForParticipant_Л_round2) l in
let participant := eval_state (↑17 ε LocalState_ι__returnOrReinvestForParticipant_Л_participant) l in
let newStake := if Л_stakeIsLost then 
                    if Л_isValidator then 
                        Л_stakes ->> RoundsBase_ι_StakeValue_ι_ordinary - (intMin ( Л_stakes ->> RoundsBase_ι_StakeValue_ι_ordinary) 
                                                                                  lostFunds )
                                     else (round2 ->> RoundsBase_ι_Round_ι_unused + 
                                           round2 ->> RoundsBase_ι_Round_ι_recoveredStake - 
                                           round2 ->> RoundsBase_ι_Round_ι_validatorRemainingStake) *  
                                           (Л_stakes ->> RoundsBase_ι_StakeValue_ι_ordinary) /
                                           (round2 ->> RoundsBase_ι_Round_ι_stake - round2 ->> RoundsBase_ι_Round_ι_validatorStake) 
                                 else Л_stakes ->> RoundsBase_ι_StakeValue_ι_ordinary + 
                                 Л_stakeSum *  (round2 ->> RoundsBase_ι_Round_ι_rewards) / (round2 ->> RoundsBase_ι_Round_ι_stake)  in
let  lostFunds :=   if Л_stakeIsLost then 
                        if Л_isValidator then lostFunds -  (intMin ( Л_stakes ->> RoundsBase_ι_StakeValue_ι_ordinary) lostFunds )      
                                         else lostFunds 
                                     else lostFunds in
let  reward :=  if Л_stakeIsLost then reward
                                 else Л_stakeSum *  (round2 ->> RoundsBase_ι_Round_ι_rewards) / (round2 ->> RoundsBase_ι_Round_ι_stake) in 
let  round2 :=  if Л_stakeIsLost then 
                        if Л_isValidator then  {$ round2 with RoundsBase_ι_Round_ι_validatorRemainingStake := round2 ->> RoundsBase_ι_Round_ι_validatorRemainingStake + newStake $}     
                                         else round2 
                                     else round2 in   
let participant :=   if Л_stakeIsLost then participant
                                     else {$participant with DePoolLib_ι_Participant_ι_reward := participant ->> DePoolLib_ι_Participant_ι_reward + reward $} in 
let round2 := {$round2 with RoundsBase_ι_Round_ι_handledStakesAndRewards :=  round2 ->> RoundsBase_ι_Round_ι_handledStakesAndRewards + newStake$} in

exec_state (f Л_stakes Л_stakeIsLost Л_isValidator Л_addr) {$ l With (LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds, lostFunds);
        (LocalState_ι__returnOrReinvestForParticipant_Л_round2, round2);
        (LocalState_ι__returnOrReinvestForParticipant_Л_participant, participant);
        (LocalState_ι__returnOrReinvestForParticipant_Л_newStake, newStake);
        (LocalState_ι__returnOrReinvestForParticipant_Л_reward, reward) $}.
Proof.
    intros. destruct l. 
  
    destruct Ledger_ι_DebugDePool, Ledger_ι_ValidatorBase, Ledger_ι_ProxyBase, Ledger_ι_ConfigParamsBase, Ledger_ι_ParticipantBase, 
    Ledger_ι_DePoolHelper, Ledger_ι_Errors, Ledger_ι_InternalErrors, Ledger_ι_DePoolLib, Ledger_ι_DePoolProxyContract, 
    Ledger_ι_RoundsBase, Ledger_ι_DePoolContract, Ledger_ι_DePool, Ledger_ι_Participant, Ledger_ι_TestElector, 
    Ledger_ι_VMState, Ledger_ι_LocalState.
  
    compute. idtac.
  
    Time repeat (
    
    time match goal with
  
      | |- ?x =>
        match x with
               
        | context [if ?b then _ else _] =>  idtac "if..." b; 
                                            repeat rewrite ifSimpleState ; 
                                            repeat rewrite ifFunApply ;                               
                                            case_eq b ; 
                                            (* simpl;  *)
                                            intros                                                              
        | _ =>  idtac "solving..." x; tryif solve [auto] then idtac "solved" else idtac "not solved"
        end
  
    end) . 
Qed.    

(* // upd vesting
        optional(InvestParams) newVesting = stakes.vesting;
        if (newVesting.hasValue()) {
            if (stakeIsLost) {
                InvestParams params = newVesting.get();
                if (isValidator) {
                    uint64 delta = math.min(params.amount, lostFunds);
                    params.amount -= delta;
                    lostFunds -= delta;
                    round2.validatorRemainingStake += params.amount;
                } else {
                    params.amount = math.muldiv(
                        round2.unused + round2.recoveredStake - round2.validatorRemainingStake,
                        params.amount,
                        round2.stake - round2.validatorStake
                    );
                }
                newVesting.set(params);
            }
            round2.handledStakesAndRewards += newVesting.get().amount;
            uint64 withdrawalVesting;
            (newVesting, withdrawalVesting) = cutWithdrawalValue(newVesting.get());
            newStake += withdrawalVesting;
        }   //tailer2 *)

  Lemma DePoolContract_Ф__returnOrReinvestForParticipant_tailer2_exec : forall
                                                            (l : Ledger)
                                                            (Л_stakes : RoundsBase_ι_StakeValue ) 
                                                            (Л_stakeIsLost : XBool )  
                                                            (Л_isValidator : XBool ) 
                                                            (Л_addr : XAddress)
                                                            (f: RoundsBase_ι_StakeValue -> XBool -> XBool -> XAddress -> LedgerT (RoundsBase_ι_Round # RoundsBase_ι_Round) ),

 exec_state (DePoolContract_Ф__returnOrReinvestForParticipant_tailer2 Л_stakes Л_stakeIsLost Л_isValidator Л_addr f) l = 

 let lostFunds := eval_state (↑17 ε LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds) l in
 let round2 :=  eval_state (↑17 ε LocalState_ι__returnOrReinvestForParticipant_Л_round2) l in
 let newStake :=  eval_state (↑17 ε LocalState_ι__returnOrReinvestForParticipant_Л_newStake) l in


    let optNewVesting :=  Л_stakes ->> RoundsBase_ι_StakeValue_ι_vesting in
    let isNewVesting := isSome optNewVesting in
    let newVesting := maybeGet optNewVesting in
    let oldVestingAmount := newVesting ->> RoundsBase_ι_InvestParams_ι_amount  in

    let deltaVestingValidator := intMin oldVestingAmount lostFunds in
    let newVestingAmountLostValidator := oldVestingAmount - deltaVestingValidator in
    let lostFundsVestingAfterDelta := lostFunds - deltaVestingValidator in
    let oldVestingValidatorRemainingStake := round2 ->> RoundsBase_ι_Round_ι_validatorRemainingStake  in
    let newVestingValidatorRemainingStake := oldVestingValidatorRemainingStake + newVestingAmountLostValidator in
    let newRound2VestingLostValidator := {$ round2 with
    (RoundsBase_ι_Round_ι_validatorRemainingStake, newVestingValidatorRemainingStake) $} in 

    let newVestingAmountLostNoValidator := 
        (round2 ->> RoundsBase_ι_Round_ι_unused  + round2 ->> RoundsBase_ι_Round_ι_recoveredStake - oldVestingValidatorRemainingStake) *
        oldVestingAmount /
        (round2 ->> RoundsBase_ι_Round_ι_stake - round2 ->> RoundsBase_ι_Round_ι_validatorStake ) in 

    let newVestingAmountLost := if Л_isValidator    then newVestingAmountLostValidator
                                                    else newVestingAmountLostNoValidator in
    let newVestingAfterLost :=
        {$ newVesting with (RoundsBase_ι_InvestParams_ι_amount , newVestingAmountLost) $} in

    let newVestingBeforeCommon := if stakeIsLost then newVestingAfterLost else newVesting in

    let lostFundsVestingBeforeCommon := if stakeIsLost then
                                            if Л_isValidator then lostFundsVestingAfterDelta
                                            else lostFunds
                                        else lostFunds in
    let round2VestingBeforeCommon := if stakeIsLost then
                                        if Л_isValidator then newRound2VestingLostValidator
                                            else round2
                                        else round2 in
    let newVestingAmountCommon := newVestingBeforeCommon ->> RoundsBase_ι_InvestParams_ι_amount  in

    let oldHandledStakesAndRewardsVesting :=
        RoundsBase_ι_Round_ι_handledStakesAndRewards round2VestingBeforeCommon in
    let newHandledStakesAndRewardsVesting := oldHandledStakesAndRewardsVesting + newVestingAmountCommon in

    let round2VestingAfterCommon := {$ round2VestingBeforeCommon with
        (RoundsBase_ι_Round_ι_handledStakesAndRewards , newHandledStakesAndRewardsVesting) $} in

    let (optNewVestingAfterCommonWithdrawalVestingAfterCommon,  stateVestingAfterCommon) :=
        run (↓ DePoolContract_Ф_cutWithdrawalValue newVestingBeforeCommon) l in

    let optNewVestingAfterCommon := fst optNewVestingAfterCommonWithdrawalVestingAfterCommon in
    let withdrawalVestingAfterCommon := snd optNewVestingAfterCommonWithdrawalVestingAfterCommon in
    
    let newStakeVestingAfterCommon := newStake_ordinary + withdrawalVestingAfterCommon in
    let newStake_vesting := if isNewVesting then newStakeVestingAfterCommon else newStake_ordinary in
    let reward_vesting := reward_ordinary in
    let lostFunds_vesting := if isNewVesting then lostFundsVestingBeforeCommon else lostFunds_ordinary in
    let participant_vesting := participant_ordinary in
    let round2_vesting := if isNewVesting then round2VestingAfterCommon else round2_ordinary in
    let state_vesting := if isNewVesting then stateVestingAfterCommon else l in
    let optNewVesting_vesting := if isNewVesting then optNewVestingAfterCommon else None in default.

    let initialAttachedValue := 1 in
    let oldWithdrawValuePause := DePoolLib_ι_Participant_ι_withdrawValue participant_vesting in
    let curPause := intMin oldWithdrawValuePause newStake_vesting in
    let attachedValueInPause := initialAttachedValue + curPause in
    let newWithdrawValuePause := oldWithdrawValuePause - curPause in
    let participant_pause := {$ participant_vesting with
        (DePoolLib_ι_Participant_ι_withdrawValue , newWithdrawValuePause) $} in
    let newStakeInPause := newStake_vesting - curPause in
    let m_minStake := eval_state (↑12 ε DePoolContract_ι_m_minStake) state_vesting in
    let isNewStakeBelowMin := newStakeInPause <? m_minStake in
    let newStake_pause := if isNewStakeBelowMin then 0 else newStakeInPause in
    let reward_pause := reward_vesting in
    let lostFunds_pause := lostFunds_vesting in
    let round2_pause := round2_vesting in
    let state_pause := state_vesting in
    let optNewVesting_pause := optNewVesting_vesting in
    let attachedValue_pause := if isNewStakeBelowMin    then attachedValueInPause + newStakeInPause 
                                                        else attachedValueInPause in

    let optNewLock := RoundsBase_ι_StakeValue_ι_lock Л_stakes in
    let isNewLock := isSome optNewLock in
    let newLock := maybeGet optNewLock in
    let lockAmount := RoundsBase_ι_InvestParams_ι_amount newLock in
    let deltaLock := intMin lockAmount lostFunds_pause in
    let lockAmountLostValidator := lockAmount - deltaLock in
    let lostFundsLockLostValidator := lostFunds_pause - deltaLock in
    let oldLockValidatorRemainingStake := RoundsBase_ι_Round_ι_validatorRemainingStake round2_pause in
    let newLockValidatorRemainingStake := oldLockValidatorRemainingStake + lockAmountLostValidator in
    let round2LockLostValidator := {$ round2_pause with
        (RoundsBase_ι_Round_ι_validatorRemainingStake ,  newLockValidatorRemainingStake) $} in
    let lockAmountLostNoValidator := intMulDiv
        (RoundsBase_ι_Round_ι_unused round2_pause + RoundsBase_ι_Round_ι_recoveredStake round2_pause -
            oldLockValidatorRemainingStake)
        lockAmount
        (RoundsBase_ι_Round_ι_stake round2_pause - RoundsBase_ι_Round_ι_validatorStake round2_pause) in
    let lockAmountLost := if Л_isValidator then lockAmountLostValidator else lockAmountLostNoValidator in
    let newLockLost := {$ newLock with (RoundsBase_ι_InvestParams_ι_amount , lockAmountLost) $} in
    let lostFundsLockLost := if Л_isValidator then lostFundsLockLostValidator else lostFunds_pause in
    let round2LockLost := if Л_isValidator then round2LockLostValidator else round2_pause in
    let newLockBeforeCommon := if stakeIsLost then newLockLost else newLock in
    let lostFundsLockBeforeCommon := if stakeIsLost then lostFundsLockLost else lostFunds_pause in
    let round2LockBeforeCommon := if stakeIsLost then round2LockLost else round2_pause in
    let lockAmountBeforeCommon := RoundsBase_ι_InvestParams_ι_amount newLockBeforeCommon in
    let oldHandledStakesAndRewardsLock :=
        RoundsBase_ι_Round_ι_handledStakesAndRewards round2LockBeforeCommon in
    let newHandledStakesAndRewardsLock := oldHandledStakesAndRewardsLock + lockAmountBeforeCommon in
    let round2LockAfterCommon := {$ round2LockBeforeCommon with
        (RoundsBase_ι_Round_ι_handledStakesAndRewards , newHandledStakesAndRewardsLock) $} in
    let optNewLockAfterCommonWithdrawalLockBeforeCommon :=
        eval_state (↓ DePoolContract_Ф_cutWithdrawalValue newLockBeforeCommon) state_pause in
    let stateLockBeforeCommon :=
        exec_state (↓ DePoolContract_Ф_cutWithdrawalValue newLockBeforeCommon) state_pause in
    let optNewLockAfterCommonWithdrawal := fst optNewLockAfterCommonWithdrawalLockBeforeCommon in
    let withdrawalLockBeforeCommon := snd optNewLockAfterCommonWithdrawalLockBeforeCommon in
    let lockOwner := RoundsBase_ι_InvestParams_ι_owner (maybeGet optNewLockAfterCommonWithdrawal) in
    let isWithdrawalNonZero := negb (withdrawalLockBeforeCommon =? 0) in
    let lockReturnState :=
        exec_state (tvm_transfer lockOwner withdrawalLockBeforeCommon false 1 default)
            stateLockBeforeCommon in
        (*exec_state (return! lockOwner ->transfer (! $ withdrawalLockBeforeCommon , $ xBoolFalse , $ xInt1 !))
        stateLockBeforeCommon in*)
    let stateLockAfterCommon := if isWithdrawalNonZero then lockReturnState else stateLockBeforeCommon in 
    let newStake_lock := newStake_pause in
    let reward_lock := reward_pause in
    let lostFunds_lock := if isNewLock then lostFundsLockBeforeCommon else lostFunds_pause in
    let round2_lock := if isNewLock then round2LockAfterCommon else round2_pause in
    let participant_lock := participant_pause in
    let state_lock := if isNewLock then stateLockAfterCommon else state_pause in 
    let optNewVesting_lock := optNewVesting_pause in
    let optNewLock_lock := if isNewLock then optNewLockAfterCommonWithdrawal else None in
    let attachedValue_lock := attachedValue_pause in

    let isPoolClosed : bool := eval_state (↑12 ε DePoolContract_ι_m_poolClosed) state_lock in
    let isNewVestingDistr := isSome optNewVesting_lock in
    let isNewLockDistr := isSome optNewLock_lock in
    let newVestingDistr := maybeGet optNewVesting_lock in
    let newLockDistr := maybeGet optNewLock_lock in
    let attachedValueDistrClosed := attachedValue_lock + newStake_lock in
    let vestingOwnerDistr := RoundsBase_ι_InvestParams_ι_owner newVestingDistr in
    let vestingAmountDistr := RoundsBase_ι_InvestParams_ι_amount newVestingDistr in
    let stateTransferVestingClosed :=
        exec_state ( tvm_transfer vestingOwnerDistr vestingAmountDistr false 1 default ) state_lock in
    let stateTransferVestingClosedAfter :=
        if isNewVestingDistr then stateTransferVestingClosed else state_lock in
    let lockOwnerDistr := RoundsBase_ι_InvestParams_ι_owner newLockDistr in
    let lockAmountDistr := RoundsBase_ι_InvestParams_ι_amount newLockDistr in
    let stateTransferLockClosed :=
    exec_state ( tvm_transfer lockOwnerDistr lockAmountDistr false 1 default ) stateTransferVestingClosedAfter in
    let stateTransferClosed :=
        if isNewLockDistr then stateTransferLockClosed else stateTransferVestingClosedAfter in
    let isNewVestingDistrIsZero := andb isNewVestingDistr (vestingAmountDistr =? 0) in
    let isNewLockDistrIsZero := andb isNewLockDistr (lockAmountDistr =? 0) in
    let optNewVestingDistr := if isNewVestingDistrIsZero then None else optNewVesting_lock in
    let optNewLockDistr := if isNewLockDistrIsZero then None else optNewLock_lock in
    let participantReinvest := DePoolLib_ι_Participant_ι_reinvest participant_lock in
    let attachedValueDistrOpenedNoReinvest := attachedValue_lock + newStake_lock in
    let attachedValueDistrOpened := if negb participantReinvest then attachedValueDistrOpenedNoReinvest
                                                                else attachedValue_lock in
    let newStakeDistrOpened := if negb participantReinvest then 0 else newStake_lock in
    let addStakesLedger :=
        ↓ RoundsBase_Ф__addStakes Л_round0 participant_lock Л_addr newStakeDistrOpened
            optNewVestingDistr optNewLockDistr in
    let stateTransferOpened := exec_state addStakesLedger state_lock in
    let round0ParticipantDistrOpened := eval_state addStakesLedger state_lock in
    let round0DistrOpened := fst round0ParticipantDistrOpened in
    let participantDistrOpened := snd round0ParticipantDistrOpened in
    let round0_distr : RoundsBase_ι_Round := if isPoolClosed then Л_round0 else round0DistrOpened in
    let round2_distr := round2_lock in
    let reward_distr := reward_lock in
    let participant_distr := if isPoolClosed then participant_lock else participantDistrOpened in
    let attachedValue_distr := if isPoolClosed then attachedValueDistrClosed else attachedValueDistrOpened in
    let state_distr := if isPoolClosed then stateTransferClosed else stateTransferOpened in

    let state_participant := exec_state
        (↓ ParticipantBase_Ф__setOrDeleteParticipant Л_addr participant_distr) state_distr in
    let oldMessages := eval_state (↑16 ε VMState_ι_messages) state_participant in
    let final_state := {$ state_participant With VMState_ι_messages :=  {|
        contractAddress := Л_addr ;
        contractFunction := IParticipant_И_onRoundCompleteF
            (RoundsBase_ι_Round_ι_id round2_distr) 
            reward_distr
            (RoundsBase_ι_StakeValue_ι_ordinary Л_stakes) 
            (RoundsBase_ι_InvestParams_ι_amount (maybeGet (RoundsBase_ι_StakeValue_ι_vesting Л_stakes)))
            (RoundsBase_ι_InvestParams_ι_amount (maybeGet (RoundsBase_ι_StakeValue_ι_lock Л_stakes)))
            (DePoolLib_ι_Participant_ι_reinvest participant_distr)
            (completionReason2XInteger (RoundsBase_ι_Round_ι_completionReason round2_distr)) ;
        contractMessage := {$ default with
            messageValue := attachedValue_distr $} 
    |} :: oldMessages $} in

    exec_state (DePoolContract_Ф__returnOrReinvestForParticipant
        Л_round2 Л_round0 Л_addr Л_stakes Л_isValidator) l =
        if isSomeParticipant then
        final_state
        else l.
Proof.
Abort.

Lemma DePoolContract_Ф__returnOrReinvestForParticipant_eval : forall
(l : Ledger)
( Л_round2 : RoundsBase_ι_Round )
( Л_round0 : RoundsBase_ι_Round )
( Л_addr : XAddress )
( Л_stakes : RoundsBase_ι_StakeValue ) 
( Л_isValidator : XBool ) ,
let stakeSum := eval_state (↓ RoundsBase_Ф_stakeSum Л_stakes) l in
let stakeIsLost := completionReasonEqb (RoundsBase_ι_Round_ι_completionReason Л_round2)
    RoundsBase_ι_CompletionReasonP_ι_ValidatorIsPunished in
let optParticipant := eval_state (↓ ParticipantBase_Ф_fetchParticipant Л_addr) l in
let isSomeParticipant := isSome optParticipant in
let participant := maybeGet optParticipant in
let oldRoundQty := DePoolLib_ι_Participant_ι_roundQty participant in
let newRoundQty := oldRoundQty - 1 in
let participant_newRoundQty :=
    {$ participant with (DePoolLib_ι_Participant_ι_roundQty, newRoundQty) $} in
let lostFunds := if stakeIsLost
    then    RoundsBase_ι_Round_ι_stake Л_round2 -
            RoundsBase_ι_Round_ι_unused Л_round2 -
            RoundsBase_ι_Round_ι_recoveredStake Л_round2
    else 0 in
let newStakeLostValidator := RoundsBase_ι_StakeValue_ι_ordinary Л_stakes in
let deltaOrdinary := intMin newStakeLostValidator lostFunds in
let newStakeLostValidatorAfterDelta := newStakeLostValidator - deltaOrdinary in
let lostFundsLostValidatorAfterDelta := lostFunds - deltaOrdinary in
let oldOrdinaryValidatorRemainingStake := RoundsBase_ι_Round_ι_validatorRemainingStake Л_round2 in
let newOrdinaryValidatorRemainingStake := oldOrdinaryValidatorRemainingStake +
    newStakeLostValidatorAfterDelta in
let newRound2OrdinaryLostValidator := {$ Л_round2 with
    (RoundsBase_ι_Round_ι_validatorRemainingStake, newOrdinaryValidatorRemainingStake) $} in
let newStakeLostRegular := intMulDiv
    (RoundsBase_ι_Round_ι_unused Л_round2 + RoundsBase_ι_Round_ι_recoveredStake Л_round2 -
        oldOrdinaryValidatorRemainingStake)
    (RoundsBase_ι_StakeValue_ι_ordinary Л_stakes)
    (RoundsBase_ι_Round_ι_stake Л_round2 - RoundsBase_ι_Round_ι_validatorStake Л_round2) in
let rewardNoLost := intMulDiv
    stakeSum
    (RoundsBase_ι_Round_ι_rewards Л_round2)
    (RoundsBase_ι_Round_ι_stake Л_round2) in
let oldParticipantReward := DePoolLib_ι_Participant_ι_reward participant_newRoundQty in
let newParticipantReward := oldParticipantReward + rewardNoLost in
let participant_afterReward := {$ participant_newRoundQty with
    (DePoolLib_ι_Participant_ι_reward , newParticipantReward) $} in
let newStakeNoLost := (RoundsBase_ι_StakeValue_ι_ordinary Л_stakes) + rewardNoLost in
let newStake_ordinary := if stakeIsLost then
                            if Л_isValidator then newStakeLostValidatorAfterDelta
                            else newStakeLostRegular
                        else newStakeNoLost in
let reward_ordinary := if stakeIsLost then
                        if Л_isValidator then 0
                        else 0
                    else rewardNoLost in
let lostFunds_ordinary := if stakeIsLost then
                    if Л_isValidator then lostFundsLostValidatorAfterDelta
                    else lostFunds
                else lostFunds in
let participant_ordinary := if stakeIsLost then
                    if Л_isValidator then participant_newRoundQty
                    else participant_newRoundQty
                else participant_afterReward in
let round2_ordinary := if stakeIsLost then
                if Л_isValidator then newRound2OrdinaryLostValidator
                else Л_round2
            else Л_round2 in
let oldHandledStakesAndRewards := RoundsBase_ι_Round_ι_handledStakesAndRewards round2_ordinary in
let newHandledStakesAndRewards := oldHandledStakesAndRewards + newStake_ordinary in
let round2_beforeVesting := {$ round2_ordinary with 
    (RoundsBase_ι_Round_ι_handledStakesAndRewards, newHandledStakesAndRewards) $} in
let optNewVesting := RoundsBase_ι_StakeValue_ι_vesting Л_stakes in
let isNewVesting := isSome optNewVesting in
let newVesting := maybeGet optNewVesting in
let oldVestingAmount := RoundsBase_ι_InvestParams_ι_amount newVesting in
let deltaVestingValidator := intMin oldVestingAmount lostFunds_ordinary in
let newVestingAmountLostValidator := oldVestingAmount - deltaVestingValidator in
let lostFundsVestingAfterDelta := lostFunds_ordinary - deltaVestingValidator in
let oldVestingValidatorRemainingStake := RoundsBase_ι_Round_ι_validatorRemainingStake round2_ordinary in
let newVestingValidatorRemainingStake := oldVestingValidatorRemainingStake + newVestingAmountLostValidator in
let newRound2VestingLostValidator := {$ round2_ordinary with
(RoundsBase_ι_Round_ι_validatorRemainingStake, newVestingValidatorRemainingStake) $} in
let newVestingAmountLostNoValidator := intMulDiv
    (RoundsBase_ι_Round_ι_unused round2_ordinary + RoundsBase_ι_Round_ι_recoveredStake round2_ordinary -
    oldVestingValidatorRemainingStake)
    oldVestingAmount
    (RoundsBase_ι_Round_ι_stake round2_ordinary - RoundsBase_ι_Round_ι_validatorStake round2_ordinary) in
let newVestingAmountLost := if Л_isValidator    then newVestingAmountLostValidator
                                                else newVestingAmountLostNoValidator in
let newVestingAfterLost :=
    {$ newVesting with (RoundsBase_ι_InvestParams_ι_amount , newVestingAmountLost) $} in
let newVestingBeforeCommon := if stakeIsLost then newVestingAfterLost else newVesting in
let lostFundsVestingBeforeCommon := if stakeIsLost then
                                        if Л_isValidator then lostFundsVestingAfterDelta
                                        else lostFunds_ordinary
                                    else lostFunds_ordinary in
let round2VestingBeforeCommon := if stakeIsLost then
                                    if Л_isValidator then newRound2VestingLostValidator
                                        else round2_ordinary
                                    else round2_ordinary in
let newVestingAmountCommon := RoundsBase_ι_InvestParams_ι_amount newVestingBeforeCommon in
let oldHandledStakesAndRewardsVesting :=
    RoundsBase_ι_Round_ι_handledStakesAndRewards round2VestingBeforeCommon in
let newHandledStakesAndRewardsVesting := oldHandledStakesAndRewardsVesting + newVestingAmountCommon in
let round2VestingAfterCommon := {$ round2VestingBeforeCommon with
    (RoundsBase_ι_Round_ι_handledStakesAndRewards , newHandledStakesAndRewardsVesting) $} in
let optNewVestingAfterCommonWithdrawalVestingAfterCommon  :=
    eval_state (↓ DePoolContract_Ф_cutWithdrawalValue newVestingBeforeCommon) l in
let stateVestingAfterCommon := exec_state (↓ DePoolContract_Ф_cutWithdrawalValue newVestingBeforeCommon) l in
let optNewVestingAfterCommon := fst optNewVestingAfterCommonWithdrawalVestingAfterCommon in
let withdrawalVestingAfterCommon := snd optNewVestingAfterCommonWithdrawalVestingAfterCommon in
let newStakeVestingAfterCommon := newStake_ordinary + withdrawalVestingAfterCommon in
let newStake_vesting := if isNewVesting then newStakeVestingAfterCommon else newStake_ordinary in
let reward_vesting := reward_ordinary in
let lostFunds_vesting := if isNewVesting then lostFundsVestingBeforeCommon else lostFunds_ordinary in
let participant_vesting := participant_ordinary in
let round2_vesting := if isNewVesting then round2VestingAfterCommon else round2_ordinary in
let state_vesting := if isNewVesting then stateVestingAfterCommon else l in
let optNewVesting_vesting := if isNewVesting then optNewVestingAfterCommon else None in

let initialAttachedValue := 1 in
let oldWithdrawValuePause := DePoolLib_ι_Participant_ι_withdrawValue participant_vesting in
let curPause := intMin oldWithdrawValuePause newStake_vesting in
let attachedValueInPause := initialAttachedValue + curPause in
let newWithdrawValuePause := oldWithdrawValuePause - curPause in
let participant_pause := {$ participant_vesting with
    (DePoolLib_ι_Participant_ι_withdrawValue , newWithdrawValuePause) $} in
let newStakeInPause := newStake_vesting - curPause in
let m_minStake := eval_state (↑12 ε DePoolContract_ι_m_minStake) state_vesting in
let isNewStakeBelowMin := newStakeInPause <? m_minStake in
let newStake_pause := if isNewStakeBelowMin then 0 else newStakeInPause in
let reward_pause := reward_vesting in
let lostFunds_pause := lostFunds_vesting in
let round2_pause := round2_vesting in
let state_pause := state_vesting in
let optNewVesting_pause := optNewVesting_vesting in
let attachedValue_pause := if isNewStakeBelowMin    then attachedValueInPause + newStakeInPause 
                                                    else attachedValueInPause in

let optNewLock := RoundsBase_ι_StakeValue_ι_lock Л_stakes in
let isNewLock := isSome optNewLock in
let newLock := maybeGet optNewLock in
let lockAmount := RoundsBase_ι_InvestParams_ι_amount newLock in
let deltaLock := intMin lockAmount lostFunds_pause in
let lockAmountLostValidator := lockAmount - deltaLock in
let lostFundsLockLostValidator := lostFunds_pause - deltaLock in
let oldLockValidatorRemainingStake := RoundsBase_ι_Round_ι_validatorRemainingStake round2_pause in
let newLockValidatorRemainingStake := oldLockValidatorRemainingStake + lockAmountLostValidator in
let round2LockLostValidator := {$ round2_pause with
    (RoundsBase_ι_Round_ι_validatorRemainingStake ,  newLockValidatorRemainingStake) $} in
let lockAmountLostNoValidator := intMulDiv
    (RoundsBase_ι_Round_ι_unused round2_pause + RoundsBase_ι_Round_ι_recoveredStake round2_pause -
        oldLockValidatorRemainingStake)
    lockAmount
    (RoundsBase_ι_Round_ι_stake round2_pause - RoundsBase_ι_Round_ι_validatorStake round2_pause) in
let lockAmountLost := if Л_isValidator then lockAmountLostValidator else lockAmountLostNoValidator in
let newLockLost := {$ newLock with (RoundsBase_ι_InvestParams_ι_amount , lockAmountLost) $} in
let lostFundsLockLost := if Л_isValidator then lostFundsLockLostValidator else lostFunds_pause in
let round2LockLost := if Л_isValidator then round2LockLostValidator else round2_pause in
let newLockBeforeCommon := if stakeIsLost then newLockLost else newLock in
let lostFundsLockBeforeCommon := if stakeIsLost then lostFundsLockLost else lostFunds_pause in
let round2LockBeforeCommon := if stakeIsLost then round2LockLost else round2_pause in
let lockAmountBeforeCommon := RoundsBase_ι_InvestParams_ι_amount newLockBeforeCommon in
let oldHandledStakesAndRewardsLock :=
    RoundsBase_ι_Round_ι_handledStakesAndRewards round2LockBeforeCommon in
let newHandledStakesAndRewardsLock := oldHandledStakesAndRewardsLock + lockAmountBeforeCommon in
let round2LockAfterCommon := {$ round2LockBeforeCommon with
    (RoundsBase_ι_Round_ι_handledStakesAndRewards , newHandledStakesAndRewardsLock) $} in
let optNewLockAfterCommonWithdrawalLockBeforeCommon :=
    eval_state (↓ DePoolContract_Ф_cutWithdrawalValue newLockBeforeCommon) state_pause in
let stateLockBeforeCommon :=
    exec_state (↓ DePoolContract_Ф_cutWithdrawalValue newLockBeforeCommon) state_pause in
let optNewLockAfterCommonWithdrawal := fst optNewLockAfterCommonWithdrawalLockBeforeCommon in
let withdrawalLockBeforeCommon := snd optNewLockAfterCommonWithdrawalLockBeforeCommon in
let lockOwner := RoundsBase_ι_InvestParams_ι_owner (maybeGet optNewLockAfterCommonWithdrawal) in
let isWithdrawalNonZero := negb (withdrawalLockBeforeCommon =? 0) in
let lockReturnState :=
    exec_state (tvm_transfer lockOwner withdrawalLockBeforeCommon false 1 default)
        stateLockBeforeCommon in
    (*exec_state (return! lockOwner ->transfer (! $ withdrawalLockBeforeCommon , $ xBoolFalse , $ xInt1 !))
    stateLockBeforeCommon in*)
let stateLockAfterCommon := if isWithdrawalNonZero then lockReturnState else stateLockBeforeCommon in 
let newStake_lock := newStake_pause in
let reward_lock := reward_pause in
let lostFunds_lock := if isNewLock then lostFundsLockBeforeCommon else lostFunds_pause in
let round2_lock := if isNewLock then round2LockAfterCommon else round2_pause in
let participant_lock := participant_pause in
let state_lock := if isNewLock then stateLockAfterCommon else state_pause in 
let optNewVesting_lock := optNewVesting_pause in
let optNewLock_lock := if isNewLock then optNewLockAfterCommonWithdrawal else None in
let attachedValue_lock := attachedValue_pause in

let isPoolClosed : bool := eval_state (↑12 ε DePoolContract_ι_m_poolClosed) state_lock in
let isNewVestingDistr := isSome optNewVesting_lock in
let isNewLockDistr := isSome optNewLock_lock in
let newVestingDistr := maybeGet optNewVesting_lock in
let newLockDistr := maybeGet optNewLock_lock in
let attachedValueDistrClosed := attachedValue_lock + newStake_lock in
let vestingOwnerDistr := RoundsBase_ι_InvestParams_ι_owner newVestingDistr in
let vestingAmountDistr := RoundsBase_ι_InvestParams_ι_amount newVestingDistr in
let stateTransferVestingClosed :=
    exec_state ( tvm_transfer vestingOwnerDistr vestingAmountDistr false 1 default ) state_lock in
let stateTransferVestingClosedAfter :=
    if isNewVestingDistr then stateTransferVestingClosed else state_lock in
let lockOwnerDistr := RoundsBase_ι_InvestParams_ι_owner newLockDistr in
let lockAmountDistr := RoundsBase_ι_InvestParams_ι_amount newLockDistr in
let stateTransferLockClosed :=
exec_state ( tvm_transfer lockOwnerDistr lockAmountDistr false 1 default ) stateTransferVestingClosedAfter in
let stateTransferClosed :=
    if isNewLockDistr then stateTransferLockClosed else stateTransferVestingClosedAfter in
let isNewVestingDistrIsZero := andb isNewVestingDistr (vestingAmountDistr =? 0) in
let isNewLockDistrIsZero := andb isNewLockDistr (lockAmountDistr =? 0) in
let optNewVestingDistr := if isNewVestingDistrIsZero then None else optNewVesting_lock in
let optNewLockDistr := if isNewLockDistrIsZero then None else optNewLock_lock in
let participantReinvest := DePoolLib_ι_Participant_ι_reinvest participant_lock in
let attachedValueDistrOpenedNoReinvest := attachedValue_lock + newStake_lock in
let attachedValueDistrOpened := if negb participantReinvest then attachedValueDistrOpenedNoReinvest
                                                            else attachedValue_lock in
let newStakeDistrOpened := if negb participantReinvest then 0 else newStake_lock in
let addStakesLedger :=
    ↓ RoundsBase_Ф__addStakes Л_round0 participant_lock Л_addr newStakeDistrOpened
        optNewVestingDistr optNewLockDistr in
let stateTransferOpened := exec_state addStakesLedger state_lock in
let round0ParticipantDistrOpened := eval_state addStakesLedger state_lock in
let round0DistrOpened := fst round0ParticipantDistrOpened in
let participantDistrOpened := snd round0ParticipantDistrOpened in
let round0_distr : RoundsBase_ι_Round := if isPoolClosed then Л_round0 else round0DistrOpened in
let round2_distr := round2_lock in
let reward_distr := reward_lock in
let participant_distr := if isPoolClosed then participant_lock else participantDistrOpened in
let attachedValue_distr := if isPoolClosed then attachedValueDistrClosed else attachedValueDistrOpened in
let state_distr := if isPoolClosed then stateTransferClosed else stateTransferOpened in

let state_participant := exec_state
    (↓ ParticipantBase_Ф__setOrDeleteParticipant Л_addr participant_distr) state_distr in
let oldMessages := eval_state (↑16 ε VMState_ι_messages) state_participant in
let final_state := {$ state_participant With VMState_ι_messages :=  {|
    contractAddress := Л_addr ;
    contractFunction := IParticipant_И_onRoundCompleteF
        (RoundsBase_ι_Round_ι_id round2_distr) 
        reward_distr
        (RoundsBase_ι_StakeValue_ι_ordinary Л_stakes) 
        (RoundsBase_ι_InvestParams_ι_amount (maybeGet (RoundsBase_ι_StakeValue_ι_vesting Л_stakes)))
        (RoundsBase_ι_InvestParams_ι_amount (maybeGet (RoundsBase_ι_StakeValue_ι_lock Л_stakes)))
        (DePoolLib_ι_Participant_ι_reinvest participant_distr)
        (completionReason2XInteger (RoundsBase_ι_Round_ι_completionReason round2_distr)) ;
    contractMessage := {$ default with
        messageValue := attachedValue_distr $} 
|} :: oldMessages $} in

eval_state (DePoolContract_Ф__returnOrReinvestForParticipant
    Л_round2 Л_round0 Л_addr Л_stakes Л_isValidator) l =
    if isSomeParticipant then
    Value (round0_distr , round2_distr)
    else Error (eval_state ( ↑8 ε InternalErrors_ι_ERROR511) l).
Proof.
Abort.

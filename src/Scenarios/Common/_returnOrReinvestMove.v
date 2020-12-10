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
Require Export depoolContract.Scenarios.Common._returnOrReinvestForParticipantMove.

Definition _returnOrReinvestForParticipantMover {X} :=
    Ledger -> RoundsBase_ι_Round -> RoundsBase_ι_Round -> RoundsBase_ι_StakeValue -> bool ->
    XAddress -> X.

Definition _returnOrReinvestForParticipantGenericMover {X} :=
    Ledger -> RoundsBase_ι_Round -> RoundsBase_ι_Round -> RoundsBase_ι_StakeValue -> bool ->
    XAddress -> X -> X.

Definition _returnOrReinvestValidatorRound {X}
                                            (l : Ledger)
                                            (f : _returnOrReinvestForParticipantMover)
                                            (r2 : RoundsBase_ι_Round)
                                            (x : X) :=
    let r0 := round0 l in
    let s := validatorStake l r2 in
    let addr := m_validatorWallet l in
    if(andb (negb (RoundsBase_ι_Round_ι_isValidatorStakeCompleted r2)) (isValidatorInRound l r2))
    then f l r0 r2 s true addr
    else x.

Definition _returnOrReinvestNonValidatorRound {X}
                                            (l : Ledger)
                                            (f : _returnOrReinvestForParticipantMover)
                                            (r2 : RoundsBase_ι_Round)
                                            (ss : XAddress * RoundsBase_ι_StakeValue)
                                            (x : X) :=
    let r0 := round0 l in
    let s := snd ss in
    let addr := fst ss in
    if(orb (RoundsBase_ι_Round_ι_isValidatorStakeCompleted r2) (negb (addr =? m_validatorWallet l)))
    then f l r0 r2 s false addr
    else x.

Definition _returnOrReinvestUpdateRoundAfterValidatorRound (l : Ledger)
                                                            (r2 : RoundsBase_ι_Round) :=
    {$ {$ r2 with
        RoundsBase_ι_Round_ι_handledStakesAndRewards :=
        _returnOrReinvestValidatorRound l
            _returnOrReinvestForParticipant_round2_handledStakesAndRewards r2
            (RoundsBase_ι_Round_ι_handledStakesAndRewards r2)
     $} with
     RoundsBase_ι_Round_ι_validatorRemainingStake :=
     _returnOrReinvestValidatorRound l
         _returnOrReinvestForParticipant_round2_validatorRemainingStake r2
         (RoundsBase_ι_Round_ι_validatorRemainingStake r2)
        $}.

Definition _returnOrReinvestUpdateRoundAfterNonValidatorRound (l : Ledger)
    (r2 : RoundsBase_ι_Round) (ss : XAddress * RoundsBase_ι_StakeValue) :=
    {$ {$ r2 with
    RoundsBase_ι_Round_ι_handledStakesAndRewards :=
    _returnOrReinvestNonValidatorRound l
    _returnOrReinvestForParticipant_round2_handledStakesAndRewards r2 ss
    (RoundsBase_ι_Round_ι_handledStakesAndRewards r2)
    $} with
    RoundsBase_ι_Round_ι_validatorRemainingStake :=
    _returnOrReinvestNonValidatorRound l
    _returnOrReinvestForParticipant_round2_validatorRemainingStake r2 ss
    (RoundsBase_ι_Round_ι_validatorRemainingStake r2)
    $}.

Definition _returnOrReinvestUpdateRound2AfterFullRound (l : Ledger)(r2 : RoundsBase_ι_Round) :=
    fold_left 
        (_returnOrReinvestUpdateRoundAfterNonValidatorRound l)
        (RoundsBase_ι_Round_ι_stakes r2)
        (_returnOrReinvestUpdateRoundAfterValidatorRound l r2).

Definition _returnOrReinvestGenericAfterFullRound {X} (l : Ledger)(r2 : RoundsBase_ι_Round)
    (x0 : X) (f : _returnOrReinvestForParticipantGenericMover) :=
    fold_left 
        (fun acc el => pair
             (f l (round0 l) (snd acc) (snd el) false (fst el) (fst acc))
            (_returnOrReinvestUpdateRoundAfterNonValidatorRound l (snd acc) el))
        (RoundsBase_ι_Round_ι_stakes r2)
        (pair (f l (round0 l) r2 (validatorStake l r2) true (m_validatorWallet l) x0)
            (_returnOrReinvestUpdateRoundAfterValidatorRound l r2)).

(*************************************Result*******************************************)

Definition _returnOrReinvest_round2_handledStakesAndRewards (l : Ledger)
                                                            (r2 : RoundsBase_ι_Round) :=
RoundsBase_ι_Round_ι_handledStakesAndRewards
    (_returnOrReinvestUpdateRound2AfterFullRound l r2).

Definition _returnOrReinvest_round2_validatorRemainingStake (l : Ledger)
                                                            (r2 : RoundsBase_ι_Round) :=
RoundsBase_ι_Round_ι_validatorRemainingStake (_returnOrReinvestUpdateRound2AfterFullRound l r2).

Definition _returnOrReinvest_round2_isValidatorStakeCompleted (l : Ledger)
                                                            (r2 : RoundsBase_ι_Round) := true.

Definition _returnOrReinvest_round0_stake(l : Ledger)(r2 : RoundsBase_ι_Round) :=
    fst ( _returnOrReinvestGenericAfterFullRound l r2 (RoundsBase_ι_Round_ι_stake (round0 l))
    (fun _l _r0 _r2 _s _v _a _x =>
        _returnOrReinvestForParticipant_round0_stake_diff _l (round0 l) _r2 _s _v _a  + _x)).

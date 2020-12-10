
Require Import Coq.Program.Basics.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Combinators.
Require Import omega.Omega.
Require Import Setoid.

Require Import FinProof.Common.
Require Import FinProof.CommonInstances.
Require Import FinProof.StateMonad2.
Require Import FinProof.StateMonadInstances.
Require Import FinProof.ProgrammingWith.
(* Require Import MultiSigWallet.Proofs.CPDT. *)

Require Import FinProof.CommonProofs.
Require Import depoolContract.ProofEnvironment.
Require Import depoolContract.DePoolClass.
Require Import depoolContract.SolidityNotations.

(* Require Import MultiSigWallet.MultiSigWalletFunctions.
Module MultiSigWalletFunctions := MultiSigWalletFunctions XTypesSig StateMonadSig.
Import MultiSigWalletFunctions. *)


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

Import DePoolSpec.
Import LedgerClass.
Import SolidityNotations.
Set Typeclasses Iterative Deepening.
Set Typeclasses Depth 10.

Require Import depoolContract.Lib.Tactics.


Local Open Scope struct_scope.
Local Open Scope Z_scope.
Local Open Scope solidity_scope.

Require Import Lists.List.
Import ListNotations.
Local Open Scope list_scope.

Existing Instance monadStateT.
Existing Instance monadStateStateT.
 
Lemma ledgerEq: forall (l l': Ledger) ,
(*  A l = A l' -> 
 C l = C l' ->  *)
 Ledger_ι_DebugDePool l = Ledger_ι_DebugDePool l' -> 
 Ledger_ι_ValidatorBase l = Ledger_ι_ValidatorBase l' -> 
 Ledger_ι_ProxyBase l = Ledger_ι_ProxyBase l' -> 
 Ledger_ι_ConfigParamsBase l = Ledger_ι_ConfigParamsBase l' -> 
 Ledger_ι_ParticipantBase l = Ledger_ι_ParticipantBase l' -> 
 Ledger_ι_DePoolHelper l = Ledger_ι_DePoolHelper l' -> 
 Ledger_ι_Errors l = Ledger_ι_Errors l' -> 
 Ledger_ι_InternalErrors l = Ledger_ι_InternalErrors l' -> 
 Ledger_ι_DePoolLib l = Ledger_ι_DePoolLib l' -> 
 Ledger_ι_DePoolProxyContract l = Ledger_ι_DePoolProxyContract l' -> 
 Ledger_ι_RoundsBase l = Ledger_ι_RoundsBase l' -> 
 Ledger_ι_DePoolContract l = Ledger_ι_DePoolContract l' -> 
 Ledger_ι_DePool l = Ledger_ι_DePool l' -> 
 Ledger_ι_Participant l = Ledger_ι_Participant l' -> 
 Ledger_ι_TestElector l = Ledger_ι_TestElector l' -> 
 Ledger_ι_VMState l = Ledger_ι_VMState l' -> 
 Ledger_ι_LocalState l = Ledger_ι_LocalState l' -> l = l' . 
Proof.
 intros. destruct l. destruct l'.
 simpl in H. simpl in * |-. 
 subst. auto.
Qed.

Lemma DePoolLib_ι_ParticipantEq : forall (l l': DePoolLib_ι_Participant) , 
 DePoolLib_ι_Participant_ι_roundQty l = DePoolLib_ι_Participant_ι_roundQty l' -> 
 DePoolLib_ι_Participant_ι_reward l = DePoolLib_ι_Participant_ι_reward l' -> 
 DePoolLib_ι_Participant_ι_haveVesting l = DePoolLib_ι_Participant_ι_haveVesting l' -> 
 DePoolLib_ι_Participant_ι_haveLock l = DePoolLib_ι_Participant_ι_haveLock l' -> 
 DePoolLib_ι_Participant_ι_reinvest l = DePoolLib_ι_Participant_ι_reinvest l' -> 
 DePoolLib_ι_Participant_ι_withdrawValue l = DePoolLib_ι_Participant_ι_withdrawValue l' -> l = l' . 
 Proof.
 intros. destruct l. destruct l'.
 simpl in H. simpl in * |-. 
 subst. auto.
Qed.
 
 Lemma DePoolLib_ι_RequestEq : forall (l l': DePoolLib_ι_Request) , 
 DePoolLib_ι_Request_ι_queryId l = DePoolLib_ι_Request_ι_queryId l' -> 
 DePoolLib_ι_Request_ι_validatorKey l = DePoolLib_ι_Request_ι_validatorKey l' -> 
 DePoolLib_ι_Request_ι_stakeAt l = DePoolLib_ι_Request_ι_stakeAt l' -> 
 DePoolLib_ι_Request_ι_maxFactor l = DePoolLib_ι_Request_ι_maxFactor l' -> 
 DePoolLib_ι_Request_ι_adnlAddr l = DePoolLib_ι_Request_ι_adnlAddr l' -> 
 DePoolLib_ι_Request_ι_signature l = DePoolLib_ι_Request_ι_signature l' -> l = l' . 
 Proof.
 intros. destruct l. destruct l'.
 simpl in H. simpl in * |-. 
 subst. auto.
Qed.
 
 Lemma ErrorsEq : forall (l l': Errors) , 
 Errors_ι_IS_NOT_OWNER l = Errors_ι_IS_NOT_OWNER l' -> 
 Errors_ι_IS_NOT_PROXY l = Errors_ι_IS_NOT_PROXY l' -> 
 Errors_ι_IS_EXT_MSG l = Errors_ι_IS_EXT_MSG l' -> 
 Errors_ι_IS_NOT_VALIDATOR l = Errors_ι_IS_NOT_VALIDATOR l' -> 
 Errors_ι_DEPOOL_IS_CLOSED l = Errors_ι_DEPOOL_IS_CLOSED l' -> 
 Errors_ι_NO_SUCH_PARTICIPANT l = Errors_ι_NO_SUCH_PARTICIPANT l' -> 
 Errors_ι_IS_NOT_DEPOOL l = Errors_ι_IS_NOT_DEPOOL l' -> 
 Errors_ι_INVALID_ROUND_STEP l = Errors_ι_INVALID_ROUND_STEP l' -> 
 Errors_ι_INVALID_QUERY_ID l = Errors_ι_INVALID_QUERY_ID l' -> 
 Errors_ι_IS_NOT_ELECTOR l = Errors_ι_IS_NOT_ELECTOR l' -> 
 Errors_ι_IS_NOT_OWNER_OR_SELF_CALL l = Errors_ι_IS_NOT_OWNER_OR_SELF_CALL l' -> 
 Errors_ι_BAD_STAKES l = Errors_ι_BAD_STAKES l' -> 
 Errors_ι_CONSTRUCTOR_NO_PUBKEY l = Errors_ι_CONSTRUCTOR_NO_PUBKEY l' -> 
 Errors_ι_VALIDATOR_IS_NOT_STD l = Errors_ι_VALIDATOR_IS_NOT_STD l' -> 
 Errors_ι_BAD_PART_REWARD l = Errors_ι_BAD_PART_REWARD l' -> 
 Errors_ι_BAD_MINIMUM_BALANCE l = Errors_ι_BAD_MINIMUM_BALANCE l' -> 
 Errors_ι_BAD_PROXY_CODE l = Errors_ι_BAD_PROXY_CODE l' -> 
 Errors_ι_NOT_WORKCHAIN0 l = Errors_ι_NOT_WORKCHAIN0 l' -> l = l' . 
 Proof.
 intros. destruct l. destruct l'.
 simpl in H. simpl in * |-. 
 subst. auto.
Qed. 
 
 Lemma InternalErrorsEq : forall (l l': InternalErrors) , 
 InternalErrors_ι_ERROR507 l = InternalErrors_ι_ERROR507 l' -> 
 InternalErrors_ι_ERROR508 l = InternalErrors_ι_ERROR508 l' -> 
 InternalErrors_ι_ERROR509 l = InternalErrors_ι_ERROR509 l' -> 
 InternalErrors_ι_ERROR511 l = InternalErrors_ι_ERROR511 l' -> 
 InternalErrors_ι_ERROR513 l = InternalErrors_ι_ERROR513 l' -> 
 InternalErrors_ι_ERROR516 l = InternalErrors_ι_ERROR516 l' -> 
 InternalErrors_ι_ERROR517 l = InternalErrors_ι_ERROR517 l' -> 
 InternalErrors_ι_ERROR518 l = InternalErrors_ι_ERROR518 l' -> 
 InternalErrors_ι_ERROR519 l = InternalErrors_ι_ERROR519 l' -> 
 InternalErrors_ι_ERROR521 l = InternalErrors_ι_ERROR521 l' -> 
 InternalErrors_ι_ERROR522 l = InternalErrors_ι_ERROR522 l' -> 
 InternalErrors_ι_ERROR523 l = InternalErrors_ι_ERROR523 l' -> 
 InternalErrors_ι_ERROR524 l = InternalErrors_ι_ERROR524 l' -> 
 InternalErrors_ι_ERROR525 l = InternalErrors_ι_ERROR525 l' -> 
 InternalErrors_ι_ERROR526 l = InternalErrors_ι_ERROR526 l' -> 
 InternalErrors_ι_ERROR527 l = InternalErrors_ι_ERROR527 l' -> 
 InternalErrors_ι_ERROR528 l = InternalErrors_ι_ERROR528 l' -> l = l' . 
 Proof.
 intros. destruct l. destruct l'.
 simpl in H. simpl in * |-. 
 subst. auto.
Qed. 

 Lemma DePoolLibEq : forall (l l': DePoolLib) , 
 DePoolLib_ι_PROXY_FEE l = DePoolLib_ι_PROXY_FEE l' -> 
 DePoolLib_ι_MIN_PROXY_BALANCE l = DePoolLib_ι_MIN_PROXY_BALANCE l' -> 
 DePoolLib_ι_PROXY_CONSTRUCTOR_FEE l = DePoolLib_ι_PROXY_CONSTRUCTOR_FEE l' -> 
 DePoolLib_ι_DEPOOL_CONSTRUCTOR_FEE l = DePoolLib_ι_DEPOOL_CONSTRUCTOR_FEE l' -> 
 DePoolLib_ι_ELECTOR_FEE l = DePoolLib_ι_ELECTOR_FEE l' -> 
 DePoolLib_ι_MAX_UINT64 l = DePoolLib_ι_MAX_UINT64 l' -> 
 DePoolLib_ι_MAX_TIME l = DePoolLib_ι_MAX_TIME l' -> 
 DePoolLib_ι_ELECTOR_UNFREEZE_LAG l = DePoolLib_ι_ELECTOR_UNFREEZE_LAG l' -> l = l' . 
 Proof.
 intros. destruct l. destruct l'.
 simpl in H. simpl in * |-. 
 subst. auto.
Qed. 
 
 Lemma DePoolEq : forall (l l': DePoolContract) , 
 DePoolContract_ι_STAKE_FEE l = DePoolContract_ι_STAKE_FEE l' -> 
 DePoolContract_ι_RET_OR_REINV_FEE l = DePoolContract_ι_RET_OR_REINV_FEE l' -> 
 DePoolContract_ι_MAX_MSGS_PER_TR l = DePoolContract_ι_MAX_MSGS_PER_TR l' -> 
 DePoolContract_ι_MAX_QTY_OF_OUT_ACTIONS l = DePoolContract_ι_MAX_QTY_OF_OUT_ACTIONS l' -> 
 DePoolContract_ι_VALUE_FOR_SELF_CALL l = DePoolContract_ι_VALUE_FOR_SELF_CALL l' -> 
 DePoolContract_ι_PROXY_CODE_HASH l = DePoolContract_ι_PROXY_CODE_HASH l' -> 
 DePoolContract_ι_STATUS_SUCCESS l = DePoolContract_ι_STATUS_SUCCESS l' -> 
 DePoolContract_ι_STATUS_STAKE_TOO_SMALL l = DePoolContract_ι_STATUS_STAKE_TOO_SMALL l' -> 
 DePoolContract_ι_STATUS_DEPOOL_CLOSED l = DePoolContract_ι_STATUS_DEPOOL_CLOSED l' -> 
 DePoolContract_ι_STATUS_NO_PARTICIPANT l = DePoolContract_ι_STATUS_NO_PARTICIPANT l' -> 
 DePoolContract_ι_STATUS_PARTICIPANT_HAVE_ALREADY_VESTING l = DePoolContract_ι_STATUS_PARTICIPANT_HAVE_ALREADY_VESTING l' -> 
 DePoolContract_ι_STATUS_WITHDRAWAL_PERIOD_GREATER_TOTAL_PERIOD l = DePoolContract_ι_STATUS_WITHDRAWAL_PERIOD_GREATER_TOTAL_PERIOD l' -> 
 DePoolContract_ι_STATUS_TOTAL_PERIOD_MORE_18YEARS l = DePoolContract_ι_STATUS_TOTAL_PERIOD_MORE_18YEARS l' -> 
 DePoolContract_ι_STATUS_WITHDRAWAL_PERIOD_IS_ZERO l = DePoolContract_ι_STATUS_WITHDRAWAL_PERIOD_IS_ZERO l' -> 
 DePoolContract_ι_STATUS_TOTAL_PERIOD_IS_NOT_DIVED_BY_WITHDRAWAL_PERIOD l = DePoolContract_ι_STATUS_TOTAL_PERIOD_IS_NOT_DIVED_BY_WITHDRAWAL_PERIOD l' -> 
 DePoolContract_ι_STATUS_PERIOD_PAYMENT_IS_ZERO l = DePoolContract_ι_STATUS_PERIOD_PAYMENT_IS_ZERO l' -> 
 DePoolContract_ι_STATUS_REMAINING_STAKE_LESS_THAN_MINIMAL l = DePoolContract_ι_STATUS_REMAINING_STAKE_LESS_THAN_MINIMAL l' -> 
 DePoolContract_ι_STATUS_PARTICIPANT_HAVE_ALREADY_LOCK l = DePoolContract_ι_STATUS_PARTICIPANT_HAVE_ALREADY_LOCK l' -> 
 DePoolContract_ι_STATUS_TRANSFER_AMOUNT_IS_TOO_BIG l = DePoolContract_ι_STATUS_TRANSFER_AMOUNT_IS_TOO_BIG l' -> 
 DePoolContract_ι_STATUS_TRANSFER_SELF l = DePoolContract_ι_STATUS_TRANSFER_SELF l' -> 
 DePoolContract_ι_STATUS_TRANSFER_TO_OR_FROM_VALIDATOR l = DePoolContract_ι_STATUS_TRANSFER_TO_OR_FROM_VALIDATOR l' -> 
 DePoolContract_ι_STATUS_FEE_TOO_SMALL l = DePoolContract_ι_STATUS_FEE_TOO_SMALL l' -> 
 DePoolContract_ι_STATUS_INVALID_ADDRESS l = DePoolContract_ι_STATUS_INVALID_ADDRESS l' -> 
 DePoolContract_ι_STATUS_INVALID_BENEFICIARY l = DePoolContract_ι_STATUS_INVALID_BENEFICIARY l' -> 
 DePoolContract_ι_STATUS_NO_ELECTION_ROUND l = DePoolContract_ι_STATUS_NO_ELECTION_ROUND l' -> 
 DePoolContract_ι_STATUS_INVALID_ELECTION_ID l = DePoolContract_ι_STATUS_INVALID_ELECTION_ID l' -> 
 DePoolContract_ι_m_poolClosed l = DePoolContract_ι_m_poolClosed l' -> 
 DePoolContract_ι_m_minStake l = DePoolContract_ι_m_minStake l' -> 
 DePoolContract_ι_m_validatorAssurance l = DePoolContract_ι_m_validatorAssurance l' -> 
 DePoolContract_ι_m_participantRewardFraction l = DePoolContract_ι_m_participantRewardFraction l' -> 
 DePoolContract_ι_m_validatorRewardFraction l = DePoolContract_ι_m_validatorRewardFraction l' -> 
 DePoolContract_ι_m_balanceThreshold l = DePoolContract_ι_m_balanceThreshold l' -> 
 DePoolContract_ι_CRITICAL_THRESHOLD l = DePoolContract_ι_CRITICAL_THRESHOLD l' -> l = l' . 
 Proof.
 intros. destruct l. destruct l'.
 simpl in H. simpl in * |-. 
 subst. auto.
Qed. 
 
 Lemma ValidatorBaseEq : forall (l l': ValidatorBase) , 
 ValidatorBase_ι_m_validatorWallet l = ValidatorBase_ι_m_validatorWallet l' -> l = l' . 
 Proof.
 intros. destruct l. destruct l'.
 simpl in H. simpl in * |-. 
 subst. auto.
Qed. 
 
 Lemma ProxyBaseEq : forall (l l': ProxyBase) , 
 ProxyBase_ι_m_proxies l = ProxyBase_ι_m_proxies l' -> l = l' . 
 Proof.
 intros. destruct l. destruct l'.
 simpl in H. simpl in * |-. 
 subst. auto.
Qed. 
 
 Lemma ParticipantBaseEq : forall (l l': ParticipantBase) , 
 ParticipantBase_ι_m_participants l = ParticipantBase_ι_m_participants l' -> l = l' . 
 Proof.
 intros. destruct l. destruct l'.
 simpl in H. simpl in * |-. 
 subst. auto.
Qed. 
 
 Lemma DePoolHelperEq : forall (l l': DePoolHelper) , 
 DePoolHelper_ι_TICKTOCK_FEE l = DePoolHelper_ι_TICKTOCK_FEE l' -> 
 DePoolHelper_ι__timerRate l = DePoolHelper_ι__timerRate l' -> 
 DePoolHelper_ι__fwdFee l = DePoolHelper_ι__fwdFee l' -> 
 DePoolHelper_ι__epsilon l = DePoolHelper_ι__epsilon l' -> 
 DePoolHelper_ι_m_dePoolPool l = DePoolHelper_ι_m_dePoolPool l' -> 
 DePoolHelper_ι_m_poolHistory l = DePoolHelper_ι_m_poolHistory l' -> 
 DePoolHelper_ι_m_timer l = DePoolHelper_ι_m_timer l' -> 
 DePoolHelper_ι_m_timeout l = DePoolHelper_ι_m_timeout l' -> l = l' . 
 Proof.
 intros. destruct l. destruct l'.
 simpl in H. simpl in * |-. 
 subst. auto.
Qed. 
 
 Lemma DePoolProxyContractEq : forall (l l': DePoolProxyContract) , 
 DePoolProxyContract_ι_ERROR_IS_NOT_DEPOOL l = DePoolProxyContract_ι_ERROR_IS_NOT_DEPOOL l' -> 
 DePoolProxyContract_ι_ERROR_BAD_BALANCE l = DePoolProxyContract_ι_ERROR_BAD_BALANCE l' -> 
 DePoolProxyContract_ι_m_dePool l = DePoolProxyContract_ι_m_dePool l' -> l = l' . 
 Proof.
 intros. destruct l. destruct l'.
 simpl in H. simpl in * |-. 
 subst. auto.
Qed. 

 Lemma InvestParamsEq : forall (l l': RoundsBase_ι_InvestParams) , 
 RoundsBase_ι_InvestParams_ι_amount l = RoundsBase_ι_InvestParams_ι_amount l' -> 
 RoundsBase_ι_InvestParams_ι_lastWithdrawalTime l = RoundsBase_ι_InvestParams_ι_lastWithdrawalTime l' -> 
 RoundsBase_ι_InvestParams_ι_withdrawalPeriod l = RoundsBase_ι_InvestParams_ι_withdrawalPeriod l' -> 
 RoundsBase_ι_InvestParams_ι_withdrawalValue l = RoundsBase_ι_InvestParams_ι_withdrawalValue l' -> 
 RoundsBase_ι_InvestParams_ι_owner l = RoundsBase_ι_InvestParams_ι_owner l' -> l = l' . 
 Proof.
 intros. destruct l. destruct l'.
 simpl in H. simpl in * |-. 
 subst. auto.
Qed. 
 
 Lemma StakeValueEq : forall (l l': RoundsBase_ι_StakeValue) , 
 RoundsBase_ι_StakeValue_ι_ordinary l = RoundsBase_ι_StakeValue_ι_ordinary l' -> 
 RoundsBase_ι_StakeValue_ι_vesting l = RoundsBase_ι_StakeValue_ι_vesting l' -> 
 RoundsBase_ι_StakeValue_ι_lock l = RoundsBase_ι_StakeValue_ι_lock l' -> l = l' . 
 Proof.
 intros. destruct l. destruct l'.
 simpl in H. simpl in * |-. 
 subst. auto.
Qed. 
 
Lemma RoundEq : forall (l l': RoundsBase_ι_Round) , 
 RoundsBase_ι_Round_ι_id l = RoundsBase_ι_Round_ι_id l' -> 
 RoundsBase_ι_Round_ι_supposedElectedAt l = RoundsBase_ι_Round_ι_supposedElectedAt l' -> 
 RoundsBase_ι_Round_ι_unfreeze l = RoundsBase_ι_Round_ι_unfreeze l' -> 
 RoundsBase_ι_Round_ι_stakeHeldFor l = RoundsBase_ι_Round_ι_stakeHeldFor l' -> 
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase l = RoundsBase_ι_Round_ι_vsetHashInElectionPhase l' -> 
 RoundsBase_ι_Round_ι_step l = RoundsBase_ι_Round_ι_step l' -> 
 RoundsBase_ι_Round_ι_completionReason l = RoundsBase_ι_Round_ι_completionReason l' -> 
 RoundsBase_ι_Round_ι_stake l = RoundsBase_ι_Round_ι_stake l' -> 
 RoundsBase_ι_Round_ι_recoveredStake l = RoundsBase_ι_Round_ι_recoveredStake l' -> 
 RoundsBase_ι_Round_ι_unused l = RoundsBase_ι_Round_ι_unused l' -> 
 RoundsBase_ι_Round_ι_isValidatorStakeCompleted l = RoundsBase_ι_Round_ι_isValidatorStakeCompleted l' -> 
 RoundsBase_ι_Round_ι_grossReward l = RoundsBase_ι_Round_ι_grossReward l' -> 
 RoundsBase_ι_Round_ι_rewards l = RoundsBase_ι_Round_ι_rewards l' -> 
 RoundsBase_ι_Round_ι_participantQty l = RoundsBase_ι_Round_ι_participantQty l' -> 
 RoundsBase_ι_Round_ι_stakes l = RoundsBase_ι_Round_ι_stakes l' -> 
 RoundsBase_ι_Round_ι_validatorStake l = RoundsBase_ι_Round_ι_validatorStake l' -> 
 RoundsBase_ι_Round_ι_validatorRemainingStake l = RoundsBase_ι_Round_ι_validatorRemainingStake l' -> 
 RoundsBase_ι_Round_ι_handledStakesAndRewards l = RoundsBase_ι_Round_ι_handledStakesAndRewards l' -> 
 RoundsBase_ι_Round_ι_validatorRequest l = RoundsBase_ι_Round_ι_validatorRequest l' -> 
 RoundsBase_ι_Round_ι_elector l = RoundsBase_ι_Round_ι_elector l' -> 
 RoundsBase_ι_Round_ι_proxy l = RoundsBase_ι_Round_ι_proxy l' -> l = l' . 
 Proof.
 intros. destruct l. destruct l'.
 simpl in H. simpl in * |-. 
 subst. auto.
Qed. 
 
 Lemma LastRoundInfoEq : forall (l l': DePool_ι_LastRoundInfo) , 
 DePool_ι_LastRoundInfo_ι_supposedElectedAt l = DePool_ι_LastRoundInfo_ι_supposedElectedAt l' -> 
 DePool_ι_LastRoundInfo_ι_participantRewardFraction l = DePool_ι_LastRoundInfo_ι_participantRewardFraction l' -> 
 DePool_ι_LastRoundInfo_ι_validatorRewardFraction l = DePool_ι_LastRoundInfo_ι_validatorRewardFraction l' -> 
 DePool_ι_LastRoundInfo_ι_participantQty l = DePool_ι_LastRoundInfo_ι_participantQty l' -> 
 DePool_ι_LastRoundInfo_ι_roundStake l = DePool_ι_LastRoundInfo_ι_roundStake l' -> 
 DePool_ι_LastRoundInfo_ι_validatorWallet l = DePool_ι_LastRoundInfo_ι_validatorWallet l' -> 
 DePool_ι_LastRoundInfo_ι_validatorPubkey l = DePool_ι_LastRoundInfo_ι_validatorPubkey l' -> 
 DePool_ι_LastRoundInfo_ι_validatorAssurance l = DePool_ι_LastRoundInfo_ι_validatorAssurance l' -> 
 DePool_ι_LastRoundInfo_ι_reward l = DePool_ι_LastRoundInfo_ι_reward l' -> 
 DePool_ι_LastRoundInfo_ι_reason l = DePool_ι_LastRoundInfo_ι_reason l' -> 
 DePool_ι_LastRoundInfo_ι_isDePoolClosed l = DePool_ι_LastRoundInfo_ι_isDePoolClosed l' -> l = l' . 
 Proof.
 intros. destruct l. destruct l'.
 simpl in H. simpl in * |-. 
 subst. auto.
Qed. 
 
Lemma RoundsBaseEq : forall (l l': RoundsBase) , 
 RoundsBase_ι_m_rounds l = RoundsBase_ι_m_rounds l' -> 
 RoundsBase_ι_m_roundQty l = RoundsBase_ι_m_roundQty l' -> 
 RoundsBase_ι_lastRoundInfo l = RoundsBase_ι_lastRoundInfo l' -> l = l' . 
 Proof.
 intros. destruct l. destruct l'.
 simpl in H. simpl in * |-. 
 subst. auto.
Qed. 
 
 Lemma RoundsBase_ι_TruncatedRoundEq : forall (l l': RoundsBase_ι_TruncatedRound) , 
 RoundsBase_ι_TruncatedRound_ι_id l = RoundsBase_ι_TruncatedRound_ι_id l' -> 
 RoundsBase_ι_TruncatedRound_ι_supposedElectedAt l = RoundsBase_ι_TruncatedRound_ι_supposedElectedAt l' -> 
 RoundsBase_ι_TruncatedRound_ι_unfreeze l = RoundsBase_ι_TruncatedRound_ι_unfreeze l' -> 
 RoundsBase_ι_TruncatedRound_ι_stakeHeldFor l = RoundsBase_ι_TruncatedRound_ι_stakeHeldFor l' -> 
 RoundsBase_ι_TruncatedRound_ι_vsetHashInElectionPhase l = RoundsBase_ι_TruncatedRound_ι_vsetHashInElectionPhase l' -> 
 RoundsBase_ι_TruncatedRound_ι_step l = RoundsBase_ι_TruncatedRound_ι_step l' -> 
 RoundsBase_ι_TruncatedRound_ι_completionReason l = RoundsBase_ι_TruncatedRound_ι_completionReason l' -> 
 RoundsBase_ι_TruncatedRound_ι_stake l = RoundsBase_ι_TruncatedRound_ι_stake l' -> 
 RoundsBase_ι_TruncatedRound_ι_recoveredStake l = RoundsBase_ι_TruncatedRound_ι_recoveredStake l' -> 
 RoundsBase_ι_TruncatedRound_ι_unused l = RoundsBase_ι_TruncatedRound_ι_unused l' -> 
 RoundsBase_ι_TruncatedRound_ι_isValidatorStakeCompleted l = RoundsBase_ι_TruncatedRound_ι_isValidatorStakeCompleted l' -> 
 RoundsBase_ι_TruncatedRound_ι_rewards l = RoundsBase_ι_TruncatedRound_ι_rewards l' -> 
 RoundsBase_ι_TruncatedRound_ι_participantQty l = RoundsBase_ι_TruncatedRound_ι_participantQty l' -> 
 RoundsBase_ι_TruncatedRound_ι_validatorStake l = RoundsBase_ι_TruncatedRound_ι_validatorStake l' -> 
 RoundsBase_ι_TruncatedRound_ι_validatorRemainingStake l = RoundsBase_ι_TruncatedRound_ι_validatorRemainingStake l' -> 
 RoundsBase_ι_TruncatedRound_ι_handledStakesAndRewards l = RoundsBase_ι_TruncatedRound_ι_handledStakesAndRewards l' ->  l = l'.
 Proof.
 intros. destruct l. destruct l'.
 simpl in H. simpl in * |-. 
 subst. auto.
Qed.  

 Lemma VMStateEq : forall (l l':  VMState ) , 
 
	VMState_ι_pubkey l = 
	VMState_ι_pubkey l' -> 
 
	VMState_ι_msg_pubkey l = 
	VMState_ι_msg_pubkey l' -> 
 
	VMState_ι_now l = 
	VMState_ι_now l' -> 
 
	VMState_ι_logstr l = 
	VMState_ι_logstr l' -> 
 
	VMState_ι_balance l = 
	VMState_ι_balance l' -> 
 
	VMState_ι_address l = 
	VMState_ι_address l' -> 
 
	VMState_ι_ltime l = 
	VMState_ι_ltime l' -> 
 
	VMState_ι_code l = 
	VMState_ι_code l' -> 
 VMState_ι_events l = VMState_ι_events l' -> 
 VMState_ι_savedDePoolContracts l = VMState_ι_savedDePoolContracts l' -> 
 VMState_ι_msg_sender l = VMState_ι_msg_sender l' -> 
 VMState_ι_msg_value l = VMState_ι_msg_value l' -> 
 VMState_ι_messages l = VMState_ι_messages l' ->
 VMState_ι_msg_data l = VMState_ι_msg_data l' ->
 VMState_ι_transactions l = VMState_ι_transactions l' ->
 l = l' . 
Proof.
 intros. destruct l. destruct l'.
 simpl in H. simpl in * |-. 
 subst. auto.
Qed.

Lemma LocalStateEq : forall (l l':  LocalState ) , 
LocalState_ι__addStakes_Л_participant l = LocalState_ι__addStakes_Л_participant  l' -> 
LocalState_ι__addStakes_Л_round  l = LocalState_ι__addStakes_Л_round   l' -> 
LocalState_ι__addStakes_Л_sv l = LocalState_ι__addStakes_Л_sv  l' -> 

LocalState_ι__returnOrReinvestForParticipant_Л_attachedValue l = LocalState_ι__returnOrReinvestForParticipant_Л_attachedValue  l' ->  
LocalState_ι__returnOrReinvestForParticipant_Л_newLock  l = LocalState_ι__returnOrReinvestForParticipant_Л_newLock  l' -> 
LocalState_ι__returnOrReinvestForParticipant_Л_newStake  l = LocalState_ι__returnOrReinvestForParticipant_Л_newStake  l' -> 
LocalState_ι__returnOrReinvestForParticipant_Л_newVesting  l = LocalState_ι__returnOrReinvestForParticipant_Л_newVesting   l' -> 
LocalState_ι__returnOrReinvestForParticipant_Л_participant  l = LocalState_ι__returnOrReinvestForParticipant_Л_participant  l' -> 
LocalState_ι__returnOrReinvestForParticipant_Л_reward  l = LocalState_ι__returnOrReinvestForParticipant_Л_reward  l' -> 
LocalState_ι__returnOrReinvestForParticipant_Л_round0  l = LocalState_ι__returnOrReinvestForParticipant_Л_round0  l' -> 


LocalState_ι__returnOrReinvest_Л_chunkSize  l = LocalState_ι__returnOrReinvest_Л_chunkSize  l' -> 
LocalState_ι__returnOrReinvest_Л_round2  l = LocalState_ι__returnOrReinvest_Л_round2  l' -> 
LocalState_ι__returnOrReinvest_Л_round0  l = LocalState_ι__returnOrReinvest_Л_round0   l' -> 
LocalState_ι__returnOrReinvest_Л_startIndex  l = LocalState_ι__returnOrReinvest_Л_startIndex  l' -> 

LocalState_ι_addVestingOrLock_Л_participant  l = LocalState_ι_addVestingOrLock_Л_participant  l' -> 
LocalState_ι_addVestingOrLock_Л_l  l = LocalState_ι_addVestingOrLock_Л_l  l' -> 
LocalState_ι_addVestingOrLock_Л_v l = LocalState_ι_addVestingOrLock_Л_v  l' -> 


LocalState_ι_completeRound_Л_i  l = LocalState_ι_completeRound_Л_i  l' -> 
LocalState_ι_completeRound_Л_msgQty  l = LocalState_ι_completeRound_Л_msgQty  l' -> 
LocalState_ι_completeRound_Л_restParticipant  l = LocalState_ι_completeRound_Л_restParticipant   l' -> 

LocalState_ι_cutWithdrawalValueAndActivateStake_Л_p  l = LocalState_ι_cutWithdrawalValueAndActivateStake_Л_p  l' -> 
LocalState_ι_cutWithdrawalValueAndActivateStake_Л_withdrawal  l = LocalState_ι_cutWithdrawalValueAndActivateStake_Л_withdrawal  l' -> 

LocalState_ι_getRounds_Л_pair  l = LocalState_ι_getRounds_Л_pair  l' -> 
LocalState_ι_getRounds_Л_rounds l = LocalState_ι_getRounds_Л_rounds  l' -> 

LocalState_ι_onFailToRecoverStake_Л_round  l = LocalState_ι_onFailToRecoverStake_Л_round  l' -> 

LocalState_ι_onSuccessToRecoverStake_Л_round  l = LocalState_ι_onSuccessToRecoverStake_Л_round  l' -> 

LocalState_ι_terminator_Л_round1  l = LocalState_ι_terminator_Л_round1  l' -> 

LocalState_ι_transferStakeInOneRound_Л_deltaDestinationStake  l = LocalState_ι_transferStakeInOneRound_Л_deltaDestinationStake  l' -> 
LocalState_ι_transferStakeInOneRound_Л_destinationParticipant  l = LocalState_ι_transferStakeInOneRound_Л_destinationParticipant  l' -> 
LocalState_ι_transferStakeInOneRound_Л_newSourceStake  l = LocalState_ι_transferStakeInOneRound_Л_newSourceStake  l' -> 
LocalState_ι_transferStakeInOneRound_Л_round  l = LocalState_ι_transferStakeInOneRound_Л_round  l' -> 
LocalState_ι_transferStakeInOneRound_Л_sourceParticipant  l = LocalState_ι_transferStakeInOneRound_Л_sourceParticipant  l' -> 
LocalState_ι_transferStakeInOneRound_Л_sourceStake  l = LocalState_ι_transferStakeInOneRound_Л_sourceStake  l' -> 

LocalState_ι_transferStake_Л_amount  l = LocalState_ι_transferStake_Л_amount  l' -> 
LocalState_ι_transferStake_Л_destParticipant  l = LocalState_ι_transferStake_Л_destParticipant  l' -> 
LocalState_ι_transferStake_Л_pair  l = LocalState_ι_transferStake_Л_pair l' -> 
LocalState_ι_transferStake_Л_rounds  l = LocalState_ι_transferStake_Л_rounds  l' -> 
LocalState_ι_transferStake_Л_srcParticipant  l = LocalState_ι_transferStake_Л_srcParticipant  l' -> 
LocalState_ι_transferStake_Л_totalSrcStake  l = LocalState_ι_transferStake_Л_totalSrcStake l' ->
LocalState_ι_transferStake_Л_transferred  l = LocalState_ι_transferStake_Л_transferred  l' ->  

LocalState_ι_updateRound2_Л_round2  l = LocalState_ι_updateRound2_Л_round2  l' -> 

LocalState_ι_updateRounds_Л_round0  l = LocalState_ι_updateRounds_Л_round0  l' -> 
LocalState_ι_updateRounds_Л_round1  l = LocalState_ι_updateRounds_Л_round1  l' -> 
LocalState_ι_updateRounds_Л_round2  l = LocalState_ι_updateRounds_Л_round2  l' -> 

LocalState_ι_withdrawStakeInPoolingRound_Л_participant  l = LocalState_ι_withdrawStakeInPoolingRound_Л_participant  l' -> 
LocalState_ι_withdrawStakeInPoolingRound_Л_round  l = LocalState_ι_withdrawStakeInPoolingRound_Л_round  l' -> 
LocalState_ι_withdrawStakeInPoolingRound_Л_sv  l = LocalState_ι_withdrawStakeInPoolingRound_Л_sv  l' -> 
LocalState_ι_withdrawStakeInPoolingRound_Л_targetAmount  l = LocalState_ι_withdrawStakeInPoolingRound_Л_targetAmount  l' -> 

LocalState_ι_constructor5_Л_ok l = LocalState_ι_constructor5_Л_ok l' -> 

LocalState_ι__returnOrReinvestForParticipant_Л_round2 l = LocalState_ι__returnOrReinvestForParticipant_Л_round2 l' ->
LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds l = LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds l' ->
LocalState_ι__returnOrReinvestForParticipant_Л_params l = LocalState_ι__returnOrReinvestForParticipant_Л_params l' ->
LocalState_ι_totalParticipantFunds_Л_stakes l = LocalState_ι_totalParticipantFunds_Л_stakes l' ->
LocalState_ι_totalParticipantFunds_Л_pair l = LocalState_ι_totalParticipantFunds_Л_pair l' ->
LocalState_ι_updateRounds_Л_roundPre0 l = LocalState_ι_updateRounds_Л_roundPre0 l' ->
LocalState_ι_cutDePoolReward_Л_reward l = LocalState_ι_cutDePoolReward_Л_reward l' ->
LocalState_ι_onBounce_Л_optRound l = LocalState_ι_onBounce_Л_optRound l' ->
LocalState_ι_startRoundCompleting_Л_round l = LocalState_ι_startRoundCompleting_Л_round l' ->
       l = l' .
Proof.
 intros. destruct l. destruct l'.
 simpl in H. simpl in * |-. 
 subst. auto.
Qed.

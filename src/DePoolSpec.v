
Require Import depoolContract.SolidityNotations.
Require Import depoolContract.ProofEnvironment. 
Require Import depoolContract.DePoolClass.


Module DePoolSpec (xt: XTypesSig) (sm: StateMonadSig).
Module LedgerClass := LedgerClass xt sm .
Import LedgerClass.
Import SolidityNotations.

Module Type DePoolSpecSig.
Import xt. Import sm.


Parameter DePoolContract_Ф__returnChange : LedgerT True .
Parameter DePoolContract_Ф__calcLastRoundInterest : XInteger64 -> XInteger64 -> LedgerT XInteger64 .
Parameter DePoolContract_Ф__sendError : XInteger32 -> XInteger64 -> LedgerT True .
Parameter DePoolContract_Ф__sendAccept : XInteger64 -> LedgerT True .
Parameter DePoolContract_Ф_cutWithdrawalValueAndActivateStake : RoundsBase_ι_InvestParams -> LedgerT ( (XMaybe RoundsBase_ι_InvestParams) # XInteger64 )%sol .
Parameter DePoolContract_Ф_onStakeAccept : XInteger64 -> XInteger32 -> XAddress -> LedgerT ( XErrorValue True XInteger ) .
Parameter DePoolContract_Ф_onStakeReject : XInteger64 -> XInteger32 -> XAddress -> LedgerT ( XErrorValue True XInteger ) .
(* Parameter DePool_Ф_Constructor2 : XInteger64 -> XAddress -> XAddress -> XAddress -> XInteger64 -> LedgerT True . *)
Parameter DePool_Ф_getParticipantInfo : XAddress -> LedgerT (XErrorValue ( XInteger64 # XInteger64 # XBool # XInteger64 # (XHMap XInteger64 XInteger64) # (XHMap XInteger64 RoundsBase_ι_InvestParams) # (XHMap XInteger64 RoundsBase_ι_InvestParams) ) XInteger)%sol.
Parameter ValidatorBase_Ф_Constructor2 : XAddress -> LedgerT True.
Parameter DePool_Ф_getDePoolInfo : LedgerT ( XInteger64 # XInteger64 # XInteger64 # XAddress # XAddress # XAddress # XBool # XInteger64 # XInteger64 # XInteger64 # XInteger64 # XInteger64 # XInteger64 # XInteger64 # XInteger64 # XInteger64 # XInteger64 # XInteger64 # XInteger64 # XInteger64 )%sol .
Parameter DePool_Ф_getParticipants : LedgerT (XArray XAddress) .
Parameter ProxyBase_Ф_Constructor3 : XAddress -> XAddress -> LedgerT True .
Parameter DePoolHelper_Ф_Constructor4 : XAddress -> LedgerT ( XErrorValue True XInteger ) .
Parameter ProxyBase_Ф_getProxy : XInteger64 -> LedgerT XAddress .
Parameter ProxyBase_Ф__recoverStake : XAddress -> XInteger64 -> XAddress -> LedgerT True .
Parameter ProxyBase_Ф__sendElectionRequest : XAddress -> XInteger64 -> XInteger64 -> DePoolLib_ι_Request -> XAddress -> LedgerT True .
Parameter ConfigParamsBase_Ф_getCurValidatorData : LedgerT ( XErrorValue ( XInteger256 # XInteger32 # XInteger32 )%sol XInteger ) .
Parameter ConfigParamsBase_Ф_getPrevValidatorHash : LedgerT ( XErrorValue XInteger XInteger ) .
Parameter ConfigParamsBase_Ф_roundTimeParams : LedgerT ( XErrorValue ( XInteger32 # XInteger32 # XInteger32 # XInteger32 )%sol XInteger ) .
Parameter ConfigParamsBase_Ф_getMaxStakeFactor : LedgerT ( XErrorValue XInteger32 XInteger ) .
Parameter ConfigParamsBase_Ф_getElector : LedgerT ( XErrorValue XAddress XInteger ) .
Parameter ParticipantBase_Ф__setOrDeleteParticipant : XAddress -> DePoolLib_ι_Participant -> LedgerT True .
Parameter DePoolProxyContract_Ф_Constructor5 : XAddress -> LedgerT ( XErrorValue True XInteger ) .
Parameter DePoolHelper_Ф_updateDePoolPoolAddress : XAddress -> LedgerT ( XErrorValue True XInteger ) .
Parameter DePoolHelper_Ф__settimer : XAddress -> XInteger -> LedgerT True .
Parameter DePoolHelper_Ф_sendTicktock : LedgerT ( XErrorValue True XInteger ) .
Parameter DePoolHelper_Ф_getDePoolPoolAddress : LedgerT XAddress .
Parameter DePoolHelper_Ф_getHistory : LedgerT (XHMap XInteger XAddress) .
Parameter DePoolHelper_Ф_onCodeUpgrade : LedgerT True .
Parameter DePoolContract_Ф_Constructor6 : XInteger64 -> XAddress -> XAddress -> XAddress -> XInteger64 -> LedgerT ( XErrorValue True XInteger )  .
Parameter DePoolProxyContract_Ф_process_new_stake : XInteger64 -> XInteger256 -> XInteger32 -> XInteger32 -> XInteger256 -> XList XInteger8 -> XAddress -> LedgerT ( XErrorValue True XInteger ) .
Parameter DePoolProxyContract_Ф_recover_stake : XInteger64 -> XAddress -> LedgerT ( XErrorValue True XInteger ) .
Parameter DePoolContract_Ф_onSuccessToRecoverStake : XInteger64 -> XAddress -> LedgerT ( XErrorValue True XInteger ) .
Parameter DePoolProxyContract_Ф_getProxyInfo : LedgerT ( XAddress # XInteger64 )%sol .
Parameter RoundsBase_Ф__addStakes : RoundsBase_ι_Round -> DePoolLib_ι_Participant -> XAddress -> XInteger64 -> XMaybe RoundsBase_ι_InvestParams -> XMaybe RoundsBase_ι_InvestParams -> LedgerT ( RoundsBase_ι_Round # DePoolLib_ι_Participant )%sol .
Parameter RoundsBase_Ф_activeAndNotStakeSum : RoundsBase_ι_StakeValue -> LedgerT XInteger64 .
Parameter RoundsBase_Ф_activeStakeSum : RoundsBase_ι_StakeValue -> LedgerT XInteger64 .
Parameter RoundsBase_Ф_toTruncatedRound : RoundsBase_ι_Round -> LedgerT RoundsBase_ι_TruncatedRound .
Parameter DePool_Ф_Constructor7 : XInteger64 -> XAddress -> XAddress -> XAddress -> XInteger64 -> LedgerT (XErrorValue True XInteger)  .
Parameter DePoolContract_Ф_onFailToRecoverStake : XInteger64 -> XAddress -> LedgerT ( XErrorValue True XInteger ) .
Parameter DePoolContract_Ф_ticktock : LedgerT ( XErrorValue True XInteger ) .
Parameter Participant_Ф_onRoundComplete : XInteger64 -> XInteger64 -> XInteger64 -> XInteger64 -> XInteger64 -> XBool -> XInteger8 -> LedgerT True .
Parameter Participant_Ф_receiveAnswer : XInteger32 -> XInteger64 -> LedgerT True .
Parameter Participant_Ф_onTransfer : XAddress -> XInteger128 -> LedgerT True .
Parameter Participant_Ф_sendTransaction : XAddress -> XInteger64 -> XBool -> XInteger16 -> TvmCell -> LedgerT ( XErrorValue True XInteger ) .
(* Parameter TestElector_Ф_Constructor8 : XInteger32 -> LedgerT True . *)
(* Parameter TestElector_Ф_getElectionId : LedgerT XInteger32 . *)
Parameter DePoolContract_Ф__returnOrReinvestForParticipant : RoundsBase_ι_Round -> RoundsBase_ι_Round -> XAddress -> RoundsBase_ι_StakeValue -> LedgerT ( XErrorValue RoundsBase_ι_Round XInteger ) .
Parameter DePoolContract_Ф__returnOrReinvest : RoundsBase_ι_Round -> XInteger8 -> LedgerT ( XErrorValue RoundsBase_ι_Round XInteger ) .
Parameter DePoolContract_Ф_calculateStakeWithAssert : XBool -> XInteger64 -> LedgerT  ( XInteger64 # XBool )%sol  .
Parameter DePoolContract_Ф_addOrdinaryStake : XBool -> LedgerT ( XErrorValue  True XInteger ) .
Parameter DePoolContract_Ф_removeOrdinaryStake : XInteger64 -> LedgerT ( XErrorValue True XInteger ) .
Parameter DePoolContract_Ф_addVestingOrLock : XAddress -> XInteger32 -> XInteger32 -> XBool -> LedgerT (XErrorValue  True XInteger) .
Parameter DePoolContract_Ф_withdrawPartAfterCompleting : XInteger64 -> LedgerT (XErrorValue True XInteger) .
Parameter DePoolContract_Ф_withdrawAllAfterCompleting : XBool -> LedgerT (XErrorValue  True XInteger) .
Parameter DePoolContract_Ф_transferStake : XAddress -> XInteger64 -> LedgerT ( XErrorValue  True XInteger ) .
Parameter DePoolContract_Ф_participateInElections : XInteger64 -> XInteger256 -> XInteger32 -> XInteger32 -> XInteger256 -> XList XInteger8 -> LedgerT ( XErrorValue True XInteger ) .
Parameter DePoolContract_Ф_updateRound2 : RoundsBase_ι_Round -> XInteger256 -> XInteger256 -> XInteger32 -> XInteger32 -> LedgerT RoundsBase_ι_Round .
Parameter DePoolContract_Ф_updateRounds :LedgerT (XErrorValue True XInteger) .
Parameter DePoolContract_Ф_completeRoundWithChunk : XInteger64 -> XInteger8 -> LedgerT ( XErrorValue True XInteger ) .
Parameter DePoolContract_Ф_completeRound : XInteger64 -> XInteger32 -> LedgerT ( XErrorValue True XInteger ) .
Parameter DePoolContract_Ф_acceptRewardAndStartRoundCompleting : RoundsBase_ι_Round -> XInteger64 -> LedgerT RoundsBase_ι_Round .
Parameter DePoolContract_Ф_terminator : LedgerT ( XErrorValue True XInteger ) .
Parameter DePoolContract_Ф_receiveFunds : LedgerT True .
Parameter DePoolHelper_Ф_onTimer : LedgerT True .
Parameter RoundsBase_Ф_getRounds : LedgerT (XHMap XInteger64 RoundsBase_ι_TruncatedRound) .
Parameter DebugDePool_Ф_getCurValidatorData2 : LedgerT ( XInteger256 # XInteger32 # XInteger32 )%sol .
Parameter DebugDePool_Ф_getPrevValidatorHash2 : LedgerT XInteger .
Parameter DebugDePool_Ф_Constructor1 : XInteger64 -> XAddress -> XAddress -> XAddress -> XInteger64 -> LedgerT True .
Parameter DePoolContract_Ф_startRoundCompleting : RoundsBase_ι_Round -> RoundsBase_ι_CompletionReason -> LedgerT RoundsBase_ι_Round .
Parameter DePoolContract_Ф_addVestingStake : XAddress -> XInteger32 -> XInteger32 -> LedgerT (XErrorValue True XInteger) .
Parameter DePoolContract_Ф_addLockStake : XAddress -> XInteger32 -> XInteger32 -> LedgerT (XErrorValue True XInteger) .
Parameter DePoolContract_Ф_generateRound : LedgerT RoundsBase_ι_Round .
Parameter DePoolHelper_Ф_initTimer : XAddress -> XInteger -> LedgerT ( XErrorValue True XInteger ) .
Parameter DePoolHelper_Ф_upgrade : TvmCell -> LedgerT ( XErrorValue True XInteger ) .
Parameter RoundsBase_Ф_transferStakeInOneRound : RoundsBase_ι_Round -> DePoolLib_ι_Participant -> DePoolLib_ι_Participant -> XAddress -> XAddress -> XInteger64 -> XInteger64 -> LedgerT ( RoundsBase_ι_Round # XInteger64 # XInteger64 # DePoolLib_ι_Participant # DePoolLib_ι_Participant )%sol .
Parameter RoundsBase_Ф_withdrawStakeInPoolingRound : DePoolLib_ι_Participant -> XAddress -> XInteger64 -> XInteger64 -> LedgerT ( XInteger64 # DePoolLib_ι_Participant )%sol .


End DePoolSpecSig.

End DePoolSpec.

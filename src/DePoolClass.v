Require Import Coq.Program.Basics.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Combinators.
Require Import FinProof.ProgrammingWith.

Local Open Scope record.
Local Open Scope program_scope. 

Require Import FinProof.Common.
Require Import FinProof.StateMonad2.
Require Import depoolContract.SolidityNotations.

Notation "·0"  := (Here)       (at level 60, right associativity). 
 Notation "·1":= (Next (·0))  (at level 60, right associativity). 
 Notation "·2":= (Next (·1))  (at level 60, right associativity). 
 Notation "·3":= (Next (·2))  (at level 60, right associativity). 
 Notation "·4":= (Next (·3))  (at level 60, right associativity). 
 Notation "·5":= (Next (·4))  (at level 60, right associativity). 
 Notation "·6":= (Next (·5))  (at level 60, right associativity). 
 Notation "·7":= (Next (·6))  (at level 60, right associativity). 
 Notation "·8":= (Next (·7))  (at level 60, right associativity). 
 Notation "·9":= (Next (·8))  (at level 60, right associativity). 
 Notation "·10":= (Next (·9))  (at level 60, right associativity). 
 Notation "·11":= (Next (·10))  (at level 60, right associativity). 
 Notation "·12":= (Next (·11))  (at level 60, right associativity). 
 Notation "·13":= (Next (·12))  (at level 60, right associativity). 
 Notation "·14":= (Next (·13))  (at level 60, right associativity). 
 Notation "·15":= (Next (·14))  (at level 60, right associativity). 
 Notation "·16":= (Next (·15))  (at level 60, right associativity). 
 Notation "·17":= (Next (·16))  (at level 60, right associativity). 
 Notation "·18":= (Next (·17))  (at level 60, right associativity). 
 Notation "·19":= (Next (·18))  (at level 60, right associativity). 
 Notation "·20":= (Next (·19))  (at level 60, right associativity). 
 Notation "·21":= (Next (·20))  (at level 60, right associativity). 
 Notation "·22":= (Next (·21))  (at level 60, right associativity). 
 Notation "·23":= (Next (·22))  (at level 60, right associativity). 
 Notation "·24":= (Next (·23))  (at level 60, right associativity). 
 Notation "·25":= (Next (·24))  (at level 60, right associativity). 
 Notation "·26":= (Next (·25))  (at level 60, right associativity). 
 Notation "·27":= (Next (·26))  (at level 60, right associativity). 
 Notation "·28":= (Next (·27))  (at level 60, right associativity). 
 Notation "·29":= (Next (·28))  (at level 60, right associativity). 
 Notation "·30":= (Next (·29))  (at level 60, right associativity). 
 Notation "·31":= (Next (·30))  (at level 60, right associativity). 
 Notation "·32":= (Next (·31))  (at level 60, right associativity). 
 Notation "·33":= (Next (·32))  (at level 60, right associativity). 
 Notation "·34":= (Next (·33))  (at level 60, right associativity). 
 Notation "·35":= (Next (·34))  (at level 60, right associativity). 
 Notation "·36":= (Next (·35))  (at level 60, right associativity). 
 Notation "·37":= (Next (·36))  (at level 60, right associativity). 
 Notation "·38":= (Next (·37))  (at level 60, right associativity). 
 Notation "·39":= (Next (·38))  (at level 60, right associativity). 
 Notation "·40":= (Next (·39))  (at level 60, right associativity). 
 Notation "·41":= (Next (·40))  (at level 60, right associativity). 
 Notation "·42":= (Next (·41))  (at level 60, right associativity). 
 Notation "·43":= (Next (·42))  (at level 60, right associativity). 
 Notation "·44":= (Next (·43))  (at level 60, right associativity). 
 Notation "·45":= (Next (·44))  (at level 60, right associativity). 
 Notation "·46":= (Next (·45))  (at level 60, right associativity). 
 Notation "·47":= (Next (·46))  (at level 60, right associativity). 
 Notation "·48":= (Next (·47))  (at level 60, right associativity). 
 Notation "·49":= (Next (·48))  (at level 60, right associativity). 
 Notation "·50":= (Next (·49))  (at level 60, right associativity). 
 Notation "·51":= (Next (·50))  (at level 60, right associativity). 
 Notation "·52":= (Next (·51))  (at level 60, right associativity). 
 Notation "·53":= (Next (·52))  (at level 60, right associativity). 
 Notation "·54":= (Next (·53))  (at level 60, right associativity). 
 Notation "·55":= (Next (·54))  (at level 60, right associativity). 
 Notation "·56":= (Next (·55))  (at level 60, right associativity). 
 Notation "·57":= (Next (·56))  (at level 60, right associativity). 
 Notation "·58":= (Next (·57))  (at level 60, right associativity). 
 Notation "·59":= (Next (·58))  (at level 60, right associativity). 
 Notation "·60":= (Next (·59))  (at level 60, right associativity). 
 Notation "·61":= (Next (·60))  (at level 60, right associativity). 
 Notation "·62":= (Next (·61))  (at level 60, right associativity). 
 Notation "·63":= (Next (·62))  (at level 60, right associativity). 
 Notation "·64":= (Next (·63))  (at level 60, right associativity). 
 Notation "·65":= (Next (·64))  (at level 60, right associativity). 
 Notation "·66":= (Next (·65))  (at level 60, right associativity). 
 Notation "·67":= (Next (·66))  (at level 60, right associativity). 
 Notation "·68":= (Next (·67))  (at level 60, right associativity). 
 Notation "·69":= (Next (·68))  (at level 60, right associativity). 
 Notation "·70":= (Next (·69))  (at level 60, right associativity). 
 Notation "·71":= (Next (·70))  (at level 60, right associativity). 
 Notation "·72":= (Next (·71))  (at level 60, right associativity). 
 Notation "·73":= (Next (·72))  (at level 60, right associativity). 
 Notation "·74":= (Next (·73))  (at level 60, right associativity). 
 Notation "·75":= (Next (·74))  (at level 60, right associativity). 
 Notation "·76":= (Next (·75))  (at level 60, right associativity). 
 Notation "·77":= (Next (·76))  (at level 60, right associativity). 
 Notation "·78":= (Next (·77))  (at level 60, right associativity). 
 Notation "·79":= (Next (·78))  (at level 60, right associativity). 
 Notation "·80":= (Next (·79))  (at level 60, right associativity). 
 Notation "·81":= (Next (·80))  (at level 60, right associativity). 
 Notation "·82":= (Next (·81))  (at level 60, right associativity). 
 Notation "·83":= (Next (·82))  (at level 60, right associativity). 
 Notation "·84":= (Next (·83))  (at level 60, right associativity). 
 Notation "·85":= (Next (·84))  (at level 60, right associativity). 
 Notation "·86":= (Next (·85))  (at level 60, right associativity). 
 Notation "·87":= (Next (·86))  (at level 60, right associativity). 
 Notation "·88":= (Next (·87))  (at level 60, right associativity). 
 Notation "·89":= (Next (·88))  (at level 60, right associativity). 
 Notation "·90":= (Next (·89))  (at level 60, right associativity). 
 Notation "·91":= (Next (·90))  (at level 60, right associativity). 
 Notation "·92":= (Next (·91))  (at level 60, right associativity). 
 Notation "·93":= (Next (·92))  (at level 60, right associativity). 
 Notation "·94":= (Next (·93))  (at level 60, right associativity). 
 Notation "·95":= (Next (·94))  (at level 60, right associativity). 
 Notation "·96":= (Next (·95))  (at level 60, right associativity). 
 Notation "·97":= (Next (·96))  (at level 60, right associativity). 
 Notation "·98":= (Next (·97))  (at level 60, right associativity). 
 Notation "·99":= (Next (·98))  (at level 60, right associativity). 
 Notation "·100":= (Next (·99))  (at level 60, right associativity). 
 Notation "·101":= (Next (·100))  (at level 60, right associativity). 
 Notation "·102":= (Next (·101))  (at level 60, right associativity). 
 Notation "·103":= (Next (·102))  (at level 60, right associativity). 
 Notation "·104":= (Next (·103))  (at level 60, right associativity). 
 Notation "·105":= (Next (·104))  (at level 60, right associativity). 
 Notation "·106":= (Next (·105))  (at level 60, right associativity). 
 Notation "·107":= (Next (·106))  (at level 60, right associativity). 
 Notation "·108":= (Next (·107))  (at level 60, right associativity). 
 Notation "·109":= (Next (·108))  (at level 60, right associativity). 
 Notation "·110":= (Next (·109))  (at level 60, right associativity). 
 Notation "·111":= (Next (·110))  (at level 60, right associativity). 
 Notation "·112":= (Next (·111))  (at level 60, right associativity). 
 Notation "·113":= (Next (·112))  (at level 60, right associativity). 
 Notation "·114":= (Next (·113))  (at level 60, right associativity). 
 Notation "·115":= (Next (·114))  (at level 60, right associativity). 
 Notation "·116":= (Next (·115))  (at level 60, right associativity). 
 Notation "·117":= (Next (·116))  (at level 60, right associativity). 
 Notation "·118":= (Next (·117))  (at level 60, right associativity). 
 Notation "·119":= (Next (·118))  (at level 60, right associativity). 
 Notation "·120":= (Next (·119))  (at level 60, right associativity). 
 Notation "·121":= (Next (·120))  (at level 60, right associativity). 
 Notation "·122":= (Next (·121))  (at level 60, right associativity). 
 Notation "·123":= (Next (·122))  (at level 60, right associativity). 
 Notation "·124":= (Next (·123))  (at level 60, right associativity). 
 Notation "·125":= (Next (·124))  (at level 60, right associativity). 
 Notation "·126":= (Next (·125))  (at level 60, right associativity). 
 Notation "·127":= (Next (·126))  (at level 60, right associativity). 
 Notation "·128":= (Next (·127))  (at level 60, right associativity). 
 Notation "·129":= (Next (·128))  (at level 60, right associativity). 
 Notation "·130":= (Next (·129))  (at level 60, right associativity). 
 Notation "·131":= (Next (·130))  (at level 60, right associativity). 
 Notation "·132":= (Next (·131))  (at level 60, right associativity). 
 Notation "·133":= (Next (·132))  (at level 60, right associativity). 
 Notation "·134":= (Next (·133))  (at level 60, right associativity). 
 Notation "·135":= (Next (·134))  (at level 60, right associativity). 
 Notation "·136":= (Next (·135))  (at level 60, right associativity). 
 Notation "·137":= (Next (·136))  (at level 60, right associativity). 
 Notation "·138":= (Next (·137))  (at level 60, right associativity). 
 Notation "·139":= (Next (·138))  (at level 60, right associativity). 
 Notation "·140":= (Next (·139))  (at level 60, right associativity). 
 Notation "·141":= (Next (·140))  (at level 60, right associativity). 
 Notation "·142":= (Next (·141))  (at level 60, right associativity). 
 Notation "·143":= (Next (·142))  (at level 60, right associativity). 
 Notation "·144":= (Next (·143))  (at level 60, right associativity). 
 Notation "·145":= (Next (·144))  (at level 60, right associativity). 
 Notation "·146":= (Next (·145))  (at level 60, right associativity). 
 Notation "·147":= (Next (·146))  (at level 60, right associativity). 
 Notation "·148":= (Next (·147))  (at level 60, right associativity). 
 Notation "·149":= (Next (·148))  (at level 60, right associativity). 
 Notation "·150":= (Next (·149))  (at level 60, right associativity). 
 Notation "·151":= (Next (·150))  (at level 60, right associativity). 
 Notation "·152":= (Next (·151))  (at level 60, right associativity). 
 Notation "·153":= (Next (·152))  (at level 60, right associativity). 
 Notation "·154":= (Next (·153))  (at level 60, right associativity). 
 Notation "·155":= (Next (·154))  (at level 60, right associativity). 
 Notation "·156":= (Next (·155))  (at level 60, right associativity). 
 Notation "·157":= (Next (·156))  (at level 60, right associativity). 
 Notation "·158":= (Next (·157))  (at level 60, right associativity). 
 Notation "·159":= (Next (·158))  (at level 60, right associativity). 
 Notation "·160":= (Next (·159))  (at level 60, right associativity). 
 Notation "·161":= (Next (·160))  (at level 60, right associativity). 
 Notation "·162":= (Next (·161))  (at level 60, right associativity). 
 Notation "·163":= (Next (·162))  (at level 60, right associativity). 
 Notation "·164":= (Next (·163))  (at level 60, right associativity). 
 Notation "·165":= (Next (·164))  (at level 60, right associativity). 
 Notation "·166":= (Next (·165))  (at level 60, right associativity). 
 Notation "·167":= (Next (·166))  (at level 60, right associativity). 
 Notation "·168":= (Next (·167))  (at level 60, right associativity). 
 Notation "·169":= (Next (·168))  (at level 60, right associativity). 
 Notation "·170":= (Next (·169))  (at level 60, right associativity). 
 Notation "·171":= (Next (·170))  (at level 60, right associativity). 
 Notation "·172":= (Next (·171))  (at level 60, right associativity). 
 Notation "·173":= (Next (·172))  (at level 60, right associativity). 
 Notation "·174":= (Next (·173))  (at level 60, right associativity). 
 Notation "·175":= (Next (·174))  (at level 60, right associativity). 
 Notation "·176":= (Next (·175))  (at level 60, right associativity). 
 Notation "·177":= (Next (·176))  (at level 60, right associativity). 
 Notation "·178":= (Next (·177))  (at level 60, right associativity). 
 Notation "·179":= (Next (·178))  (at level 60, right associativity). 
 Notation "·180":= (Next (·179))  (at level 60, right associativity). 
 Notation "·181":= (Next (·180))  (at level 60, right associativity). 
 Notation "·182":= (Next (·181))  (at level 60, right associativity). 
 Notation "·183":= (Next (·182))  (at level 60, right associativity). 
 Notation "·184":= (Next (·183))  (at level 60, right associativity). 
 Notation "·185":= (Next (·184))  (at level 60, right associativity). 
 Notation "·186":= (Next (·185))  (at level 60, right associativity). 
 Notation "·187":= (Next (·186))  (at level 60, right associativity). 
 Notation "·188":= (Next (·187))  (at level 60, right associativity). 
 Notation "·189":= (Next (·188))  (at level 60, right associativity). 
 Notation "·190":= (Next (·189))  (at level 60, right associativity). 
 Notation "·191":= (Next (·190))  (at level 60, right associativity). 
 Notation "·192":= (Next (·191))  (at level 60, right associativity). 
 Notation "·193":= (Next (·192))  (at level 60, right associativity). 
 Notation "·194":= (Next (·193))  (at level 60, right associativity). 
 Notation "·195":= (Next (·194))  (at level 60, right associativity). 
 Notation "·196":= (Next (·195))  (at level 60, right associativity). 
 Notation "·197":= (Next (·196))  (at level 60, right associativity). 
 Notation "·198":= (Next (·197))  (at level 60, right associativity). 
 Notation "·199":= (Next (·198))  (at level 60, right associativity). 
 Notation "·200":= (Next (·199))  (at level 60, right associativity). 
 Notation "·201":= (Next (·200))  (at level 60, right associativity). 
 Notation "·202":= (Next (·201))  (at level 60, right associativity). 
 Notation "·203":= (Next (·202))  (at level 60, right associativity). 
 Notation "·204":= (Next (·203))  (at level 60, right associativity). 
 Notation "·205":= (Next (·204))  (at level 60, right associativity). 
 Notation "·206":= (Next (·205))  (at level 60, right associativity). 
 Notation "·207":= (Next (·206))  (at level 60, right associativity). 
 Notation "·208":= (Next (·207))  (at level 60, right associativity). 
 Notation "·209":= (Next (·208))  (at level 60, right associativity). 
 Notation "·210":= (Next (·209))  (at level 60, right associativity). 
 Notation "·211":= (Next (·210))  (at level 60, right associativity). 
 Notation "·212":= (Next (·211))  (at level 60, right associativity). 
 Notation "·213":= (Next (·212))  (at level 60, right associativity). 
 Notation "·214":= (Next (·213))  (at level 60, right associativity). 
 Notation "·215":= (Next (·214))  (at level 60, right associativity). 
 Notation "·216":= (Next (·215))  (at level 60, right associativity). 
 Notation "·217":= (Next (·216))  (at level 60, right associativity). 
 Notation "·218":= (Next (·217))  (at level 60, right associativity). 
 Notation "·219":= (Next (·218))  (at level 60, right associativity). 
 Notation "·220":= (Next (·219))  (at level 60, right associativity). 
 Notation "·221":= (Next (·220))  (at level 60, right associativity). 
 Notation "·222":= (Next (·221))  (at level 60, right associativity). 
 Notation "·223":= (Next (·222))  (at level 60, right associativity). 
 Notation "·224":= (Next (·223))  (at level 60, right associativity). 
 Notation "·225":= (Next (·224))  (at level 60, right associativity). 
 Notation "·226":= (Next (·225))  (at level 60, right associativity). 
 Notation "·227":= (Next (·226))  (at level 60, right associativity). 
 Notation "·228":= (Next (·227))  (at level 60, right associativity). 
 Notation "·229":= (Next (·228))  (at level 60, right associativity). 
 Notation "·230":= (Next (·229))  (at level 60, right associativity). 
 Notation "·231":= (Next (·230))  (at level 60, right associativity). 
 Notation "·232":= (Next (·231))  (at level 60, right associativity). 
 Notation "·233":= (Next (·232))  (at level 60, right associativity). 
 Notation "·234":= (Next (·233))  (at level 60, right associativity). 
 Notation "·235":= (Next (·234))  (at level 60, right associativity). 
 Notation "·236":= (Next (·235))  (at level 60, right associativity). 
 Notation "·237":= (Next (·236))  (at level 60, right associativity). 
 Notation "·238":= (Next (·237))  (at level 60, right associativity). 
 Notation "·239":= (Next (·238))  (at level 60, right associativity). 
 Notation "·240":= (Next (·239))  (at level 60, right associativity). 
 Notation "·241":= (Next (·240))  (at level 60, right associativity). 
 Notation "·242":= (Next (·241))  (at level 60, right associativity). 
 Notation "·243":= (Next (·242))  (at level 60, right associativity). 
 Notation "·244":= (Next (·243))  (at level 60, right associativity). 
 Notation "·245":= (Next (·244))  (at level 60, right associativity). 
 Notation "·246":= (Next (·245))  (at level 60, right associativity). 
 Notation "·247":= (Next (·246))  (at level 60, right associativity). 
 Notation "·248":= (Next (·247))  (at level 60, right associativity). 
 Notation "·249":= (Next (·248))  (at level 60, right associativity). 
 Notation "·250":= (Next (·249))  (at level 60, right associativity). 
 

Section RecordsDefinitions.

Set Implicit Arguments.
Unset Strict Implicit.
Set Contextual Implicit.
Set Maximal Implicit Insertion.

Variables I I8 I16 I32 I64 I128 I256 : Type.
Variables A B C S: Type.
Variables L M: Type -> Type.
Variables HM P: Type -> Type -> Type.

Inductive ContractFunctionP  :=
| ContractFunctionDefault : ContractFunctionP
| DePoolContract_Ф_completeRoundF : I64 -> I32 -> ContractFunctionP
(* | DePoolContract_Ф_ticktockF : I64 -> I256 -> I32 -> I32 -> I256 -> I8 -> ContractFunctionP *)
| DePoolContract_Ф_completeRoundWithChunkF : I64 -> I8 -> ContractFunctionP
| DePoolContract_Ф_ticktockF : ContractFunctionP
| DePoolContract_Ф_onStakeAcceptF : I64 -> I32 -> A -> ContractFunctionP
| DePoolContract_Ф_onStakeRejectF : I64 -> I32 -> A -> ContractFunctionP
| DePoolContract_Ф_onSuccessToRecoverStakeF : I64 -> A -> ContractFunctionP
| DePoolContract_Ф_onFailToRecoverStakeF : I64 -> A -> ContractFunctionP
| DePoolContract_Ф_sendErrorF : I64 -> I32 -> ContractFunctionP
| DePoolContract_Ф_acceptRecoveredStakeF : I64 -> ContractFunctionP
| DePoolContract_Ф_terminatorF : ContractFunctionP 
 
| DePoolProxyContract_Ф_recover_stakeF : I64 -> A -> ContractFunctionP
| DePoolProxyContract_Ф_process_new_stakeF : I64 -> I256 -> I32 -> I32 -> I32 -> L I8 -> A -> ContractFunctionP

| ProxyBase_Ф_getProxyF : I64 -> ContractFunctionP

| IParticipant_И_receiveAnswerF : I32 -> I64 -> ContractFunctionP
| IParticipant_И_onRoundCompleteF : I64 -> I64 -> I64 -> I64 -> I64 -> B -> I8 -> ContractFunctionP
| IParticipant_И_onTransferF : A -> I128 -> ContractFunctionP

| ITimer_И_setTimerF : I -> ContractFunctionP

| IElector_И_process_new_stakeF : I64 -> I256 -> I32 -> I32 -> I32 -> L I8 -> ContractFunctionP
| IElector_И_recover_stakeF : I64 -> ContractFunctionP.


Record MessageStructP := MessageStructC
	{
		messageFlag: I8;
		messageBounce: B;
		messageValue: I256
	}.

(* Arguments MessageStructC [I8 I256 B].  *)	

Record ContractsFunctionWithMessageP := ContractsFunctionWithMessageC
	{
		contractAddress : A;
		contractFunction: ContractFunctionP ;
		contractMessage : MessageStructP 
	}.

(* Arguments ContractsFunctionWithMessageC [ I I8 I32 I64 I128 I256 B A L]. *)


Inductive RoundsBase_ι_RoundStepP := 
 | RoundsBase_ι_RoundStepP_ι_Pooling : RoundsBase_ι_RoundStepP 
 | RoundsBase_ι_RoundStepP_ι_WaitingValidatorRequest : RoundsBase_ι_RoundStepP 
 | RoundsBase_ι_RoundStepP_ι_WaitingIfStakeAccepted : RoundsBase_ι_RoundStepP 
 | RoundsBase_ι_RoundStepP_ι_WaitingValidationStart : RoundsBase_ι_RoundStepP 
 | RoundsBase_ι_RoundStepP_ι_WaitingIfValidatorWinElections : RoundsBase_ι_RoundStepP 
 | RoundsBase_ι_RoundStepP_ι_WaitingUnfreeze : RoundsBase_ι_RoundStepP 
 | RoundsBase_ι_RoundStepP_ι_WaitingReward : RoundsBase_ι_RoundStepP 
 | RoundsBase_ι_RoundStepP_ι_Completing : RoundsBase_ι_RoundStepP 
 | RoundsBase_ι_RoundStepP_ι_Completed : RoundsBase_ι_RoundStepP 
 | RoundsBase_ι_RoundStepP_ι_PrePooling : RoundsBase_ι_RoundStepP. 

 Definition RoundsBase_ι_RoundStep := RoundsBase_ι_RoundStepP.
 
 
 Inductive RoundsBase_ι_CompletionReasonP := 
 | RoundsBase_ι_CompletionReasonP_ι_Undefined : RoundsBase_ι_CompletionReasonP 
 | RoundsBase_ι_CompletionReasonP_ι_PoolClosed : RoundsBase_ι_CompletionReasonP 
 | RoundsBase_ι_CompletionReasonP_ι_FakeRound : RoundsBase_ι_CompletionReasonP 
 | RoundsBase_ι_CompletionReasonP_ι_ValidatorStakeIsTooSmall : RoundsBase_ι_CompletionReasonP 
 | RoundsBase_ι_CompletionReasonP_ι_StakeIsRejectedByElector : RoundsBase_ι_CompletionReasonP 
 | RoundsBase_ι_CompletionReasonP_ι_RewardIsReceived : RoundsBase_ι_CompletionReasonP 
 | RoundsBase_ι_CompletionReasonP_ι_ElectionsAreLost : RoundsBase_ι_CompletionReasonP 
 | RoundsBase_ι_CompletionReasonP_ι_ValidatorIsPunished : RoundsBase_ι_CompletionReasonP 
 | RoundsBase_ι_CompletionReasonP_ι_NoValidatorRequest : RoundsBase_ι_CompletionReasonP 
 | RoundsBase_ι_CompletionReasonP_ι_BadProxy : RoundsBase_ι_CompletionReasonP . 

 Definition RoundsBase_ι_CompletionReason := RoundsBase_ι_CompletionReasonP.
 
 

 
Record DebugDePoolP  := DebugDePoolC  { 
 	DebugDePool_ι_validators_elected_for : I32  ;   (* constant := 18_000  ;  *) 
 	DebugDePool_ι_elections_start_before : I32  ;   (* constant := 9_000  ;  *) 
 	DebugDePool_ι_elections_end_before : I32  ;   (* constant := 2_000  ;  *) 
 	DebugDePool_ι_stake_held_for : I32  ;   (* constant := 9_000  ;  *)  
 }. 
 
(*  Arguments DebugDePoolC  [  I32  ]   .  *)



(* // Represent info about last completed round
struct LastRoundInfo {
    uint32 supposedElectedAt;
    uint8 participantRewardFraction;
    uint8 validatorRewardFraction;
    uint32 participantQty;
    uint64 roundStake;
    address validatorWallet;
    uint256 validatorPubkey;
    uint64 validatorAssurance;
    uint64 reward;
    uint8 reason;
    bool isDePoolClosed;
} *)

Record DePool_ι_LastRoundInfoP := DePool_ι_LastRoundInfoC {
  DePool_ι_LastRoundInfo_ι_supposedElectedAt : I32 ;
  DePool_ι_LastRoundInfo_ι_participantRewardFraction : I8 ;
  DePool_ι_LastRoundInfo_ι_validatorRewardFraction : I8 ;
  DePool_ι_LastRoundInfo_ι_participantQty : I32 ;
  DePool_ι_LastRoundInfo_ι_roundStake : I64 ;
  DePool_ι_LastRoundInfo_ι_validatorWallet : A ;
  DePool_ι_LastRoundInfo_ι_validatorPubkey : I256 ;
  DePool_ι_LastRoundInfo_ι_validatorAssurance : I64 ;
  DePool_ι_LastRoundInfo_ι_reward : I64 ;
  DePool_ι_LastRoundInfo_ι_reason : RoundsBase_ι_CompletionReasonP ;
  DePool_ι_LastRoundInfo_ι_isDePoolClosed : B 
}.




Record DePoolLib_ι_ParticipantP := DePoolLib_ι_ParticipantC  { 
 	DePoolLib_ι_Participant_ι_roundQty : I8  ;  
 	DePoolLib_ι_Participant_ι_reward : I64  ;  
 	DePoolLib_ι_Participant_ι_haveVesting : B  ;  
 	DePoolLib_ι_Participant_ι_haveLock : B  ;  
 	DePoolLib_ι_Participant_ι_reinvest : B  ;  
 	DePoolLib_ι_Participant_ι_withdrawValue : I64   
  }  .  
 
 
(*  Arguments DePoolLib_ι_ParticipantC  [  I8 I64 B  ]   . *)

 Record ValidatorBaseP  := ValidatorBaseC  { 
 	ValidatorBase_ι_m_validatorWallet : A  
 } . 
 
(*  Arguments ValidatorBaseC  [  A  ]   .  *)

 Record ProxyBaseP := ProxyBaseC  { 
 	ProxyBase_ι_m_proxies : HM I A  
 }   . 
 
(* Arguments ProxyBaseC  [  I A  HM]   . *)

Record ParticipantBaseP  := ParticipantBaseC  { 
 	ParticipantBase_ι_m_participants : HM A DePoolLib_ι_ParticipantP   
 } . 
 
(*  Arguments ParticipantBaseC  [ HM A I8 I64 B ] .  *)

 Record DePoolHelperP  := DePoolHelperC  { 
 	DePoolHelper_ι_TICKTOCK_FEE : I  ;   (* constant := 1e9  ;  *) 
 	DePoolHelper_ι__timerRate : I  ;   (* constant := 400000  ;  *) 
 	DePoolHelper_ι__fwdFee : I  ;   (* constant := 1000000  ;  *) 
 	DePoolHelper_ι__epsilon : I  ;   (* constant := 1e9  ;  *) 
 	DePoolHelper_ι_m_dePoolPool : A  ; 
 	DePoolHelper_ι_m_poolHistory : HM I A  ; 
 	DePoolHelper_ι_m_timer : A  ; 
 	DePoolHelper_ι_m_timeout : I  
 
 }   . 
 

(*  Arguments DePoolHelperC  [  I A HM  ]   .  *)
 Record ErrorsP  := ErrorsC  { 
 	Errors_ι_IS_NOT_OWNER : I  ;   (* constant := 101  ;  *) 
 	Errors_ι_IS_NOT_PROXY : I  ;   (* constant := 107  ;  *) 
 	Errors_ι_IS_EXT_MSG : I  ;   (* constant := 108  ;  *) 
 	Errors_ι_IS_NOT_VALIDATOR : I  ;   (* constant := 113  ;  *) 
 	Errors_ι_DEPOOL_IS_CLOSED : I  ;   (* constant := 114  ;  *) 
 	Errors_ι_NO_SUCH_PARTICIPANT : I  ;   (* constant := 116  ;  *) 
 	Errors_ι_IS_NOT_DEPOOL : I  ;   (* constant := 120  ;  *) 
 	Errors_ι_INVALID_ROUND_STEP : I  ;   (* constant := 125  ;  *) 
 	Errors_ι_INVALID_QUERY_ID : I  ;   (* constant := 126  ;  *) 
	Errors_ι_IS_NOT_ELECTOR : I  ;   (* constant := 127  ;  *) 
 	Errors_ι_IS_NOT_OWNER_OR_SELF_CALL : I  ;   (* constant := 128  ;  *) 
	Errors_ι_BAD_STAKES : I8 ;
 	Errors_ι_CONSTRUCTOR_NO_PUBKEY : I8  ;   (* constant := 130  ;  *) 
	Errors_ι_VALIDATOR_IS_NOT_STD : I8 ;
	Errors_ι_BAD_PART_REWARD : I8 ;
 	Errors_ι_BAD_MINIMUM_BALANCE : I8 ;
	Errors_ι_BAD_PROXY_CODE : I8 ;
	Errors_ι_NOT_WORKCHAIN0 : I8 
 }   . 
 
(*  Arguments ErrorsC  [  I I8  ]   .  *)
 Record InternalErrorsP   := InternalErrorsC  { 
 	InternalErrors_ι_ERROR507 : I  ;   (* constant := 507  ;  *) 
 	InternalErrors_ι_ERROR508 : I  ;   (* constant := 508  ;  *) 
 	InternalErrors_ι_ERROR509 : I  ;   (* constant := 509  ;  *) 
 	InternalErrors_ι_ERROR511 : I  ;   (* constant := 511  ;  *) 
 	InternalErrors_ι_ERROR513 : I  ;   (* constant := 513  ;  *) 
 	InternalErrors_ι_ERROR516 : I  ;   (* constant := 516  ;  *) 
 	InternalErrors_ι_ERROR517 : I  ;   (* constant := 517  ;  *) 
 	InternalErrors_ι_ERROR518 : I  ;   (* constant := 518  ;  *) 
 	InternalErrors_ι_ERROR519 : I  ;   (* constant := 519  ;  *) 
 	InternalErrors_ι_ERROR521 : I  ;   (* constant := 521  ;  *) 
 	InternalErrors_ι_ERROR522 : I  ;   (* constant := 522  ;  *) 
 	InternalErrors_ι_ERROR523 : I  ;   (* constant := 523  ;  *) 
 	InternalErrors_ι_ERROR524 : I  ;   (* constant := 524  ;  *) 
 	InternalErrors_ι_ERROR525 : I  ;   (* constant := 525  ;  *) 
 	InternalErrors_ι_ERROR526 : I  ;   (* constant := 526  ;  *) 
 	InternalErrors_ι_ERROR527 : I  ;   (* constant := 527  ;  *) 
 	InternalErrors_ι_ERROR528 : I  ;   (* constant := 528  ;  *) 
 }   . 
 
(*  Arguments InternalErrorsC  [  I  ]   .  *)
  
 Record DePoolLib_ι_RequestP   := DePoolLib_ι_RequestC  { 
 	DePoolLib_ι_Request_ι_queryId : I64  ;  
 	DePoolLib_ι_Request_ι_validatorKey : I256  ;  
 	DePoolLib_ι_Request_ι_stakeAt : I32  ;  
 	DePoolLib_ι_Request_ι_maxFactor : I32  ;  
 	DePoolLib_ι_Request_ι_adnlAddr : I256  ;  
 	DePoolLib_ι_Request_ι_signature :  L I8   
  }  .  
 
 
(*  Arguments DePoolLib_ι_RequestC  [  I64 I256 I32 I8  L ]   . *)

 Record DePoolLibP   := DePoolLibC  { 
DePoolLib_ι_PROXY_FEE : I64  ;   (* constant := 0.09 ton  ;  *) 
DePoolLib_ι_ELECTOR_FEE : I64  ;   (* constant := 1 ton  ;  *) 
DePoolLib_ι_MAX_UINT64 : I64  ;   (* constant := 0xFFFF_FFFF_FFFF_FFFF  ;  *) 
DePoolLib_ι_MAX_TIME : I32  ;   (* constant := 0xFFFF_FFFF  ;  *) 
DePoolLib_ι_ELECTOR_UNFREEZE_LAG : I64  ;   (* constant := 1 minutes  ;  *) 
DePoolLib_ι_MIN_PROXY_BALANCE : I64  ;
DePoolLib_ι_PROXY_CONSTRUCTOR_FEE : I64 ;
DePoolLib_ι_DEPOOL_CONSTRUCTOR_FEE : I64
 }   . 
 
 (* Arguments DePoolLibC  [  I64 I32  ]   .  *)


 Record DePoolProxyContractP := DePoolProxyContractC  { 
 	DePoolProxyContract_ι_ERROR_IS_NOT_DEPOOL : I  ;   (* constant := 102  ;  *) 
 	DePoolProxyContract_ι_ERROR_BAD_BALANCE : I  ;   (* constant := 103  ;  *) 
 	DePoolProxyContract_ι_m_dePool : A  
 }   . 
 
(*  Arguments DePoolProxyContractC  [  I64 I A  ]   .  *)

 Record RoundsBase_ι_InvestParamsP  := RoundsBase_ι_InvestParamsC  { 
 	RoundsBase_ι_InvestParams_ι_amount : I64  ;  
 	RoundsBase_ι_InvestParams_ι_lastWithdrawalTime : I64  ;  
 	RoundsBase_ι_InvestParams_ι_withdrawalPeriod : I32  ;  
 	RoundsBase_ι_InvestParams_ι_withdrawalValue : I64  ;  
 	RoundsBase_ι_InvestParams_ι_owner : A   
  }  .  
 

 
(*  Arguments RoundsBase_ι_InvestParamsC  [  B I64 I32 A  ]   . *) 
 Record RoundsBase_ι_StakeValueP  := RoundsBase_ι_StakeValueC  { 
	 RoundsBase_ι_StakeValue_ι_ordinary : I64;
	 RoundsBase_ι_StakeValue_ι_vesting : M RoundsBase_ι_InvestParamsP ;
     RoundsBase_ι_StakeValue_ι_lock : M RoundsBase_ι_InvestParamsP 
    }  .  
 
 
(*  Arguments RoundsBase_ι_StakeValueC  [ B I64 I32 A M  ]   . *)


 Record RoundsBase_ι_RoundP := RoundsBase_ι_RoundC  { 
 	RoundsBase_ι_Round_ι_id : I64  ;  
 	RoundsBase_ι_Round_ι_supposedElectedAt : I32  ;  
 	RoundsBase_ι_Round_ι_unfreeze : I32  ;  
	RoundsBase_ι_Round_ι_stakeHeldFor : I32  ;
 	RoundsBase_ι_Round_ι_vsetHashInElectionPhase : I256  ;  
 	RoundsBase_ι_Round_ι_step : RoundsBase_ι_RoundStepP  ;  
 	RoundsBase_ι_Round_ι_completionReason : RoundsBase_ι_CompletionReasonP  ;  
 	RoundsBase_ι_Round_ι_stake : I64  ;  
	RoundsBase_ι_Round_ι_recoveredStake : I64 ;
	RoundsBase_ι_Round_ι_unused : I64  ;
	RoundsBase_ι_Round_ι_isValidatorStakeCompleted : B ;
	RoundsBase_ι_Round_ι_grossReward : I64 ;
 	RoundsBase_ι_Round_ι_rewards : I64  ;  
 	RoundsBase_ι_Round_ι_participantQty : I32  ;  
	RoundsBase_ι_Round_ι_stakes : HM A RoundsBase_ι_StakeValueP ;  
	RoundsBase_ι_Round_ι_validatorStake : I64;
	RoundsBase_ι_Round_ι_validatorRemainingStake : I64 ;
	RoundsBase_ι_Round_ι_handledStakesAndRewards : I64 ;
	RoundsBase_ι_Round_ι_validatorRequest : DePoolLib_ι_RequestP ;
  RoundsBase_ι_Round_ι_elector : A  ;  
 	RoundsBase_ι_Round_ι_proxy : A  
 } . 
 
(*  Arguments RoundsBase_ι_RoundC  [ I8 I64 I32 HM M L A I256 B] .  *)
	
 Record RoundsBase_ι_TruncatedRoundP  := RoundsBase_ι_TruncatedRoundC  { 
 	RoundsBase_ι_TruncatedRound_ι_id : I64  ;  
 	RoundsBase_ι_TruncatedRound_ι_supposedElectedAt : I32  ;  
 	RoundsBase_ι_TruncatedRound_ι_unfreeze : I32  ;  
	RoundsBase_ι_TruncatedRound_ι_stakeHeldFor : I32 ;
	RoundsBase_ι_TruncatedRound_ι_vsetHashInElectionPhase : I256 ;
 	RoundsBase_ι_TruncatedRound_ι_step : RoundsBase_ι_RoundStepP  ;  
 	RoundsBase_ι_TruncatedRound_ι_completionReason : RoundsBase_ι_CompletionReasonP  ;  
 	RoundsBase_ι_TruncatedRound_ι_stake : I64  ;  
	RoundsBase_ι_TruncatedRound_ι_recoveredStake : I64 ;
 	RoundsBase_ι_TruncatedRound_ι_unused : I64  ;  
	RoundsBase_ι_TruncatedRound_ι_isValidatorStakeCompleted : B ;
	RoundsBase_ι_TruncatedRound_ι_rewards : I64  ;  
 	RoundsBase_ι_TruncatedRound_ι_participantQty : I32  ;  
	RoundsBase_ι_TruncatedRound_ι_validatorStake : I64;
	RoundsBase_ι_TruncatedRound_ι_validatorRemainingStake : I64;
	RoundsBase_ι_TruncatedRound_ι_handledStakesAndRewards : I64
  } .  
 
(*  Arguments RoundsBase_ι_TruncatedRoundC  [ I64 I32 I256 B ] .  *)

Inductive LedgerEventP  := 
| NoEvent : LedgerEventP
| DePoolClosed : LedgerEventP
| roundStakeIsAccepted: I64 -> I32 -> LedgerEventP
| roundStakeIsRejected: I64 -> I32 -> LedgerEventP
| ProxyHasRejectedTheStake: I64 -> LedgerEventP
| ProxyHasRejectedRecoverRequest: I64 -> LedgerEventP
| RoundCompleted: RoundsBase_ι_TruncatedRoundP -> LedgerEventP
| StakeSigningRequested: I32 -> A -> LedgerEventP
| BadProxy : A -> LedgerEventP
| TooLowDePoolBalance : I -> LedgerEventP .

Record RoundsBaseP  := RoundsBaseC  { 
 	RoundsBase_ι_m_rounds : HM I64 RoundsBase_ι_RoundP  ; 
 	RoundsBase_ι_m_roundQty : I64  ;   (* := 0  ;  *) 
(* mapping(bool => LastRoundInfo) lastRoundInfo; *)
    RoundsBase_ι_lastRoundInfo : HM B DePool_ι_LastRoundInfoP 
 } . 
 
(*  Arguments RoundsBaseC  [ HM M L I8 I64 I32 A I256 B] . *)

 Record DePoolContractP   := DePoolContractC  { 
	DePoolContract_ι_STAKE_FEE : I64 ;
 	DePoolContract_ι_RET_OR_REINV_FEE : I64  ;   (* constant := 50 milliton  ;  *) 
 	DePoolContract_ι_MAX_MSGS_PER_TR : I8  ;   (* constant := 25  ;  *) 
 	DePoolContract_ι_MAX_QTY_OF_OUT_ACTIONS : I16  ;   (* constant := 250  ;  *) 
 	DePoolContract_ι_VALUE_FOR_SELF_CALL : I64  ;   (* constant := 1 ton  ;  *) 
	DePoolContract_ι_PROXY_CODE_HASH : I256 ;
 	DePoolContract_ι_STATUS_SUCCESS : I8  ;   (* constant := 0  ;  *) 
 	DePoolContract_ι_STATUS_STAKE_TOO_SMALL : I8  ;   (* constant := 1  ;  *) 
 	DePoolContract_ι_STATUS_DEPOOL_CLOSED : I8  ;   (* constant := 3  ;  *) 
 	DePoolContract_ι_STATUS_NO_PARTICIPANT : I8  ;   (* constant := 6  ;  *) 
 	DePoolContract_ι_STATUS_PARTICIPANT_HAVE_ALREADY_VESTING : I8  ;   (* constant := 9  ;  *) 
 	DePoolContract_ι_STATUS_WITHDRAWAL_PERIOD_GREATER_TOTAL_PERIOD : I8  ;   (* constant := 10  ;  *) 
 	DePoolContract_ι_STATUS_TOTAL_PERIOD_MORE_18YEARS : I8  ;   (* constant := 11  ;  *) 
 	DePoolContract_ι_STATUS_WITHDRAWAL_PERIOD_IS_ZERO : I8  ;   (* constant := 12  ;  *) 
 	DePoolContract_ι_STATUS_TOTAL_PERIOD_IS_NOT_DIVED_BY_WITHDRAWAL_PERIOD : I8  ;   (* constant := 13  ;  *) 
 	DePoolContract_ι_STATUS_PERIOD_PAYMENT_IS_ZERO : I8  ;   (* constant := 14  ;  *) 
 	DePoolContract_ι_STATUS_REMAINING_STAKE_LESS_THAN_MINIMAL : I8  ;   (* constant := 16  ;  *) 
 	DePoolContract_ι_STATUS_PARTICIPANT_HAVE_ALREADY_LOCK : I8  ;   (* constant := 17  ;  *) 
 	DePoolContract_ι_STATUS_TRANSFER_AMOUNT_IS_TOO_BIG : I8  ;   (* constant := 18  ;  *) 
 	DePoolContract_ι_STATUS_TRANSFER_SELF : I8  ;   (* constant := 19  ;  *) 
	DePoolContract_ι_STATUS_TRANSFER_TO_OR_FROM_VALIDATOR : I8 ;
	DePoolContract_ι_STATUS_FEE_TOO_SMALL : I8;
	DePoolContract_ι_STATUS_INVALID_ADDRESS : I8 ;   (* constant := 22  ;  *)
	DePoolContract_ι_STATUS_INVALID_BENEFICIARY : I8 ;   (* constant := 23  ;  *)
	DePoolContract_ι_STATUS_NO_ELECTION_ROUND : I8 ;   (* constant := 24  ;  *)
	DePoolContract_ι_STATUS_INVALID_ELECTION_ID : I8 ;   (* constant := 25  ;  *)
 	DePoolContract_ι_m_poolClosed : B  ; 
 	DePoolContract_ι_m_minStake : I64  ; 
	DePoolContract_ι_m_validatorAssurance : I64 ;
	DePoolContract_ι_m_participantRewardFraction : I8 ;
	DePoolContract_ι_m_validatorRewardFraction : I8 ;
	DePoolContract_ι_m_balanceThreshold : I64 ;
	DePoolContract_ι_CRITICAL_THRESHOLD : I64 (* constant := 5 ton  ;  *)
 }   . 


 
(*  Arguments DePoolContractC  [  I8 I64 I16 I32 B  ]   .  *)

Record TestElector_ι_ValidatorP   := TestElector_ι_ValidatorC  { 
 	TestElector_ι_Validator_ι_stake : I64  ;  
 	TestElector_ι_Validator_ι_key : I256  ;  
 	TestElector_ι_Validator_ι_reward : I64  ;  
 	TestElector_ι_Validator_ι_qid : I64  ;  
 	TestElector_ι_Validator_ι_factor : I32  ;  
 	TestElector_ι_Validator_ι_adnl : I256  ;  
 	TestElector_ι_Validator_ι_signature : I8   
  }  .  
 
 
(*  Arguments TestElector_ι_ValidatorC  [  I64 I256 I32 I8  ]   .  *)

 Record TestElectorP  := TestElectorC  { 
 	TestElector_ι_elections : HM I256  TestElector_ι_ValidatorP   ; 
 	TestElector_ι_electAt : I32  ; 
 	TestElector_ι_ELECTIONS_BEGIN_BEFORE : I32  ;   (* constant := 12  ;  *) 
 	TestElector_ι_ELECTIONS_END_BEFORE : I32  ;   (* constant := 6  ;  *) 
 	TestElector_ι_ELECTED_FOR : I32  ;   (* constant := 24  ;  *) 
 	TestElector_ι_STAKE_HELD_FOR : I32  ;   (* constant := 12  ;  *) 
 
 } . 
 
(*  Arguments TestElectorC  [ HM I32 I256 I64 I8 ]  .  *)

Record TransactionP  := TransactionC {
   txDest   : A ;
   txValue  : I256 ; 
   txBounce : B ;
   txFlags  : I8 ;
   txPayload: C 
}.  

(* Arguments TransactionC [ A I256 I8 C B ]. *)

(* Definition T1 := DebugDePool . 
 Definition T2 := ValidatorBase . 
 Definition T3 := ProxyBase . 
 Definition T4 := True . 
 Definition T5 := ParticipantBase . 
 Definition T6 := DePoolHelper . 
 Definition T7 := Errors . 
 Definition T8 := InternalErrors . 
 Definition T9 := DePoolLib . 
 Definition T10 := DePoolProxyContract .  
 Definition T11 := RoundsBase . 
 Definition T12 := DePoolContract . 
 Definition T13 := True . 
 Definition T14 := True . 
 Definition T15 := TestElector .*)

Record VMCommittedP :=  VMCommittedC {
	VMCommitted_ι_DebugDePool : DebugDePoolP ; 
	VMCommitted_ι_ValidatorBase : ValidatorBaseP ; 
	VMCommitted_ι_ProxyBase : ProxyBaseP  ; 
	VMCommitted_ι_ConfigParamsBase : True  ; 
	VMCommitted_ι_ParticipantBase : ParticipantBaseP   ; 
	VMCommitted_ι_DePoolHelper : DePoolHelperP   ; 
	VMCommitted_ι_Errors : ErrorsP   ; 
	VMCommitted_ι_InternalErrors : InternalErrorsP  ; 
	VMCommitted_ι_DePoolLib : DePoolLibP   ; 
	VMCommitted_ι_DePoolProxyContract : DePoolProxyContractP  ; 
	VMCommitted_ι_RoundsBase : RoundsBaseP  ; 
	VMCommitted_ι_DePoolContract : DePoolContractP  ;
	VMCommitted_ι_DePool : True  ; 
	VMCommitted_ι_Participant : True  ; 
	VMCommitted_ι_TestElector : TestElectorP   
}.


Record VMStateP  := VMStateC  { 
	VMState_ι_pubkey : I256  ; 
	VMState_ι_msg_pubkey : I256  ; 
	VMState_ι_now : I64  ; 
	VMState_ι_logstr : S  ; 
	VMState_ι_balance : I128  ; 
	VMState_ι_address : A  ; 
	VMState_ι_ltime : I256  ; 
	VMState_ι_code : C  ; 
    VMState_ι_events : L  LedgerEventP ;   
	VMState_ι_savedDePoolContracts :  VMCommittedP  ;
    VMState_ι_msg_sender : A  ; 
 	VMState_ι_msg_value : I256 ; 
	VMState_ι_messages: L ContractsFunctionWithMessageP;
	VMState_ι_msg_data : C  ; 
	VMState_ι_transactions : L TransactionP 
} . 

(* Arguments VMStateC  [ A I256 I64 S I128 C L I I8 I16 I32 B] .   *)

Load "LocalStateDefinition.v".
 
 Record LedgerP := LedgerC  { 
 	Ledger_ι_DebugDePool : DebugDePoolP  ; 
 	Ledger_ι_ValidatorBase : ValidatorBaseP  ; 
 	Ledger_ι_ProxyBase : ProxyBaseP ; 
 	Ledger_ι_ConfigParamsBase : True  ; 
 	Ledger_ι_ParticipantBase : ParticipantBaseP  ; 
 	Ledger_ι_DePoolHelper : DePoolHelperP ; 
 	Ledger_ι_Errors :  ErrorsP  ; 
 	Ledger_ι_InternalErrors : InternalErrorsP ; 
 	Ledger_ι_DePoolLib : DePoolLibP  ; 
 	Ledger_ι_DePoolProxyContract : DePoolProxyContractP  ; 
 	Ledger_ι_RoundsBase : RoundsBaseP   ; 
 	Ledger_ι_DePoolContract : DePoolContractP  ; 
 	Ledger_ι_DePool : True  ; 
 	Ledger_ι_Participant : True  ; 
 	Ledger_ι_TestElector : TestElectorP  ; 
 	Ledger_ι_VMState : VMStateP  ; 
 	Ledger_ι_LocalState : LocalStateP   
 }   . 
 
(* Arguments LedgerC [ I32 A HM P I8 I64 B I I256 I16 S I128 C L M ] . *)  
End RecordsDefinitions. 

Module LedgerClass (xt: XTypesSig) (sm: StateMonadSig) .
Module SolidityNotations := SolidityNotations.SolidityNotations xt sm.
Import SolidityNotations.
Existing Instance monadStateT. 
Existing Instance monadStateStateT.

(* Print DePool_ι_LastRoundInfoP. *)
Definition DePool_ι_LastRoundInfo := DePool_ι_LastRoundInfoP XInteger8 XInteger32 XInteger64 XInteger256 XAddress XBool .
(* Print ContractsFunctionWithMessageP. *)
Definition ContractsFunctionWithMessage := ContractsFunctionWithMessageP XInteger XInteger8 XInteger32 XInteger64 XInteger128 XInteger256 XAddress XBool XList.
(* Print MessageStructP. *)
Definition MessageStruct := MessageStructP XInteger8 XInteger256 XBool.
(* Print ContractFunctionP.  *)
Definition ContractFunction := ContractFunctionP XInteger XInteger8 XInteger32 XInteger64 XInteger128 XInteger256 XAddress XBool XList .
(* Print LedgerEventP. *)
Definition LedgerEvent := LedgerEventP XInteger XInteger32 XInteger64 XInteger256 XAddress XBool.

Instance RoundsBase_ι_RoundStep_default : XDefault RoundsBase_ι_RoundStep := { 
	default := RoundsBase_ι_RoundStepP_ι_Pooling } . 
	
Instance RoundsBase_ι_CompletionReason_default : XDefault RoundsBase_ι_CompletionReason := { 
	default := RoundsBase_ι_CompletionReasonP_ι_Undefined } . 

Instance event_default : XDefault LedgerEvent := 
{default:= NoEvent}.

Instance MessageStruct_default : XDefault MessageStruct :=
{default := MessageStructC default default default }.

Instance ContractFunction_default : XDefault ContractFunction :=
{default := ContractFunctionDefault}.

Instance ContractsFunctionWithMessage_default : XDefault ContractsFunctionWithMessage :=
{default := ContractsFunctionWithMessageC default default default}.

(* Check ContractsFunctionWithMessage.
Check MessageStruct. *)

Global Instance Struct_MessageStruct : Struct MessageStruct :=  { 
 	fields :=  [ 
 		@existT _ _ _ messageFlag , 
 		@existT _ _ _ messageBounce , 
 		@existT _ _ _ messageValue 
 	 ]   ;  
 	 ctor := MessageStructC 
 }   . 
Global Instance Acc_MessageStruct_ι_messageFlag : Accessor messageFlag :=  {  acc := ·0  }   . 
Global Instance Acc_MessageStruct_ι_messageBounce : Accessor messageBounce :=  {  acc := ·1  }   . 
Global Instance Acc_MessageStruct_ι_messageValue : Accessor messageValue :=  {  acc := ·2  }   . 

Global Instance Struct_ContractsFunctionWithMessage : Struct ContractsFunctionWithMessage :=  { 
 	fields :=  [ 
 		@existT _ _ _ contractAddress , 
 		@existT _ _ _ contractFunction, 
 		@existT _ _ _ contractMessage 
 	 ]   ;  
 	 ctor := ContractsFunctionWithMessageC 
 }   . 
Global Instance Acc_ContractsFunctionWithMessage_ι_contractAddress : Accessor contractAddress :=  {  acc := ·0  }   . 
Global Instance Acc_ContractsFunctionWithMessage_ι_contractFunction : Accessor contractFunction :=  {  acc := ·1  }   . 
Global Instance Acc_ContractsFunctionWithMessage_ι_contractMessage : Accessor contractMessage :=  {  acc := ·2  }   . 

Instance msgstruct_default: XDefault MessageStruct := {
	default := {| messageFlag := default; messageValue := default; messageBounce := default |}
}.


Global Instance Struct_DePool_ι_LastRoundInfo : Struct DePool_ι_LastRoundInfo := {
 	fields :=  [ 
 		@existT _ _ _ DePool_ι_LastRoundInfo_ι_supposedElectedAt ,
 		@existT _ _ _ DePool_ι_LastRoundInfo_ι_participantRewardFraction ,
 		@existT _ _ _ DePool_ι_LastRoundInfo_ι_validatorRewardFraction ,
 		@existT _ _ _ DePool_ι_LastRoundInfo_ι_participantQty  ,
 		@existT _ _ _ DePool_ι_LastRoundInfo_ι_roundStake ,
 		@existT _ _ _ DePool_ι_LastRoundInfo_ι_validatorWallet ,
 		@existT _ _ _ DePool_ι_LastRoundInfo_ι_validatorPubkey ,
 		@existT _ _ _ DePool_ι_LastRoundInfo_ι_validatorAssurance ,
 		@existT _ _ _ DePool_ι_LastRoundInfo_ι_reward ,
 		@existT _ _ _ DePool_ι_LastRoundInfo_ι_reason ,
 		@existT _ _ _ DePool_ι_LastRoundInfo_ι_isDePoolClosed  
 	 ]   ;  
 	 ctor := DePool_ι_LastRoundInfoC 
} .
Global Instance Acc_DePool_ι_LastRoundInfo_ι_supposedElectedAt  : Accessor DePool_ι_LastRoundInfo_ι_supposedElectedAt :=  {  acc := ·0  }   .
Global Instance Acc_DePool_ι_LastRoundInfo_ι_participantRewardFraction  : Accessor DePool_ι_LastRoundInfo_ι_participantRewardFraction :=  {  acc := ·1  }   .
Global Instance Acc_DePool_ι_LastRoundInfo_ι_validatorRewardFraction  : Accessor DePool_ι_LastRoundInfo_ι_validatorRewardFraction :=  {  acc := ·2  }   .
Global Instance Acc_DePool_ι_LastRoundInfo_ι_participantQty  : Accessor DePool_ι_LastRoundInfo_ι_participantQty :=  {  acc := ·3  }   .
Global Instance Acc_DePool_ι_LastRoundInfo_ι_roundStake  : Accessor DePool_ι_LastRoundInfo_ι_roundStake :=  {  acc := ·4  }   .
Global Instance Acc_DePool_ι_LastRoundInfo_ι_validatorWallet  : Accessor DePool_ι_LastRoundInfo_ι_validatorWallet :=  {  acc := ·5  }   .
Global Instance Acc_DePool_ι_LastRoundInfo_ι_validatorPubkey  : Accessor DePool_ι_LastRoundInfo_ι_validatorPubkey :=  {  acc := ·6  }   .
Global Instance Acc_DePool_ι_LastRoundInfo_ι_validatorAssurance  : Accessor DePool_ι_LastRoundInfo_ι_validatorAssurance :=  {  acc := ·7  }   .
Global Instance Acc_DePool_ι_LastRoundInfo_ι_reward  : Accessor DePool_ι_LastRoundInfo_ι_reward :=  {  acc := ·8  }   .
Global Instance Acc_DePool_ι_LastRoundInfo_ι_reason  : Accessor DePool_ι_LastRoundInfo_ι_reason  :=  {  acc := ·9  }   .
Global Instance Acc_DePool_ι_LastRoundInfo_ι_isDePoolClosed  : Accessor DePool_ι_LastRoundInfo_ι_isDePoolClosed  :=  {  acc := ·10  }   .

Instance DePool_ι_LastRoundInfo_default : XDefault DePool_ι_LastRoundInfo :=  {  
 	 default := DePool_ι_LastRoundInfoC default default default default default 
                                      default default default default default
                                      default
  }   . 



(* Print DebugDePoolP. *)
Definition DebugDePool := @DebugDePoolP XInteger32 . 
Global Instance Struct_DebugDePool : Struct DebugDePool :=  { 
 	fields :=  [ 
 		@existT _ _ _ DebugDePool_ι_validators_elected_for , 
 		@existT _ _ _ DebugDePool_ι_elections_start_before , 
 		@existT _ _ _ DebugDePool_ι_elections_end_before , 
 		@existT _ _ _ DebugDePool_ι_stake_held_for 
 
 	 ]   ;  
 	 ctor := DebugDePoolC  
 }   . 
Global Instance Acc_DebugDePool_ι_validators_elected_for : Accessor DebugDePool_ι_validators_elected_for :=  {  acc := ·0  }   . 
Global Instance Acc_DebugDePool_ι_elections_start_before : Accessor DebugDePool_ι_elections_start_before :=  {  acc := ·1  }   . 
Global Instance Acc_DebugDePool_ι_elections_end_before : Accessor DebugDePool_ι_elections_end_before :=  {  acc := ·2  }   . 
Global Instance Acc_DebugDePool_ι_stake_held_for : Accessor DebugDePool_ι_stake_held_for :=  {  acc := ·3  }   . 


Instance DebugDePool_default : XDefault DebugDePool :=  {  
 	 default := DebugDePoolC default default default default  
  }   . 
(* Definition DebugDePoolT := StateT DebugDePool . *) 
 
  
Definition ValidatorBase := @ValidatorBaseP XAddress . 
Global Instance Struct_ValidatorBase : Struct ValidatorBase :=  { 
 	fields :=  [ 
 		@existT _ _ _ ValidatorBase_ι_m_validatorWallet 
 
 	 ]   ;  
 	 ctor := ValidatorBaseC 
 }   . 
Global Instance Acc_ValidatorBase_ι_m_validatorWallet : Accessor ValidatorBase_ι_m_validatorWallet :=  {  acc := ·0  }   . 
Instance ValidatorBase_default : XDefault ValidatorBase :=  {  
 	 default := ValidatorBaseC default  
  }   . 
(* Definition ValidatorBaseT := StateT ValidatorBase . *) 
 
(* Print ProxyBaseP.  *) 
Definition ProxyBase := @ProxyBaseP XInteger XAddress XHMap. 
Global Instance Struct_ProxyBase : Struct ProxyBase :=  { 
 	fields :=  [ 
 		@existT _ _ _ ProxyBase_ι_m_proxies 
 
 	 ]   ;  
 	 ctor := ProxyBaseC 
 }   . 
Global Instance Acc_ProxyBase_ι_m_proxy0 : Accessor ProxyBase_ι_m_proxies :=  {  acc := ·0  }   . 
 
Instance ProxyBase_default : XDefault ProxyBase :=  {  
 	 default := ProxyBaseC default   
  }   . 
(* Definition ProxyBaseT := StateT ProxyBase . *) 
  
(* Print   ParticipantBaseP. *)
Definition ParticipantBase := @ParticipantBaseP XInteger8 XInteger64 XAddress XBool XHMap. 
Global Instance Struct_ParticipantBase : Struct ParticipantBase :=  { 
 	fields :=  [ 
 		@existT _ _ _ ParticipantBase_ι_m_participants 
 	 ]   ;  
 	 ctor := ParticipantBaseC 
 }   . 
Global Instance Acc_ParticipantBase_ι_m_participants : Accessor ParticipantBase_ι_m_participants :=  {  acc := ·0  }   . 
Instance ParticipantBase_default : XDefault ParticipantBase :=  {  
 	 default := ParticipantBaseC default  
  }   . 
(* Definition ParticipantBaseT := StateT ParticipantBase . *) 
 
  
Definition DePoolHelper := @DePoolHelperP XInteger XAddress XHMap . 
Global Instance Struct_DePoolHelper : Struct DePoolHelper :=  { 
 	fields :=  [ 
 		@existT _ _ _ DePoolHelper_ι_TICKTOCK_FEE , 
 		@existT _ _ _ DePoolHelper_ι__timerRate , 
 		@existT _ _ _ DePoolHelper_ι__fwdFee , 
 		@existT _ _ _ DePoolHelper_ι__epsilon , 
 		@existT _ _ _ DePoolHelper_ι_m_dePoolPool , 
 		@existT _ _ _ DePoolHelper_ι_m_poolHistory , 
 		@existT _ _ _ DePoolHelper_ι_m_timer , 
 		@existT _ _ _ DePoolHelper_ι_m_timeout 
 
 	 ]   ;  
 	 ctor := DePoolHelperC 
 }   . 
Global Instance Acc_DePoolHelper_ι_TICKTOCK_FEE : Accessor DePoolHelper_ι_TICKTOCK_FEE :=  {  acc := ·0  }   . 
Global Instance Acc_DePoolHelper_ι__timerRate : Accessor DePoolHelper_ι__timerRate :=  {  acc := ·1  }   . 
Global Instance Acc_DePoolHelper_ι__fwdFee : Accessor DePoolHelper_ι__fwdFee :=  {  acc := ·2  }   . 
Global Instance Acc_DePoolHelper_ι__epsilon : Accessor DePoolHelper_ι__epsilon :=  {  acc := ·3  }   . 
Global Instance Acc_DePoolHelper_ι_m_dePoolPool : Accessor DePoolHelper_ι_m_dePoolPool :=  {  acc := ·4  }   . 
Global Instance Acc_DePoolHelper_ι_m_poolHistory : Accessor DePoolHelper_ι_m_poolHistory :=  {  acc := ·5  }   . 
Global Instance Acc_DePoolHelper_ι_m_timer : Accessor DePoolHelper_ι_m_timer :=  {  acc := ·6  }   . 
Global Instance Acc_DePoolHelper_ι_m_timeout : Accessor DePoolHelper_ι_m_timeout :=  {  acc := ·7  }   . 
Instance DePoolHelper_default : XDefault DePoolHelper :=  {  
 	 default := DePoolHelperC default default default default default default default default  
  }   . 
(* Definition DePoolHelperT := StateT DePoolHelper . *) 

  
 Definition Errors := @ErrorsP XInteger XInteger8 . 
Global Instance Struct_Errors : Struct Errors :=  { 
 	fields :=  [ 
 		@existT _ _ _ Errors_ι_IS_NOT_OWNER , 
 		@existT _ _ _ Errors_ι_IS_NOT_PROXY , 
 		@existT _ _ _ Errors_ι_IS_EXT_MSG , 
 		@existT _ _ _ Errors_ι_IS_NOT_VALIDATOR , 
 		@existT _ _ _ Errors_ι_DEPOOL_IS_CLOSED , 
 		@existT _ _ _ Errors_ι_NO_SUCH_PARTICIPANT , 
 		@existT _ _ _ Errors_ι_IS_NOT_DEPOOL , 
 		@existT _ _ _ Errors_ι_INVALID_ROUND_STEP ,
 		@existT _ _ _ Errors_ι_INVALID_QUERY_ID , 
 		@existT _ _ _ Errors_ι_IS_NOT_ELECTOR , 
 		@existT _ _ _ Errors_ι_IS_NOT_OWNER_OR_SELF_CALL , 
		@existT _ _ _ Errors_ι_BAD_STAKES ,
 		@existT _ _ _ Errors_ι_CONSTRUCTOR_NO_PUBKEY , 
		@existT _ _ _ Errors_ι_VALIDATOR_IS_NOT_STD ,
		@existT _ _ _ Errors_ι_BAD_PART_REWARD ,
		@existT _ _ _ Errors_ι_BAD_MINIMUM_BALANCE ,
		@existT _ _ _ Errors_ι_BAD_PROXY_CODE ,
    @existT _ _ _ Errors_ι_NOT_WORKCHAIN0
 	 ]   ;  
 	 ctor := ErrorsC  
 }   . 
Global Instance Acc_Errors_ι_IS_NOT_OWNER : Accessor Errors_ι_IS_NOT_OWNER :=  {  acc := ·0  }   . 
Global Instance Acc_Errors_ι_IS_NOT_PROXY : Accessor Errors_ι_IS_NOT_PROXY :=  {  acc := ·1  }   . 
Global Instance Acc_Errors_ι_IS_EXT_MSG : Accessor Errors_ι_IS_EXT_MSG :=  {  acc := ·2  }   . 
Global Instance Acc_Errors_ι_IS_NOT_VALIDATOR : Accessor Errors_ι_IS_NOT_VALIDATOR :=  {  acc := ·3  }   . 
Global Instance Acc_Errors_ι_DEPOOL_IS_CLOSED : Accessor Errors_ι_DEPOOL_IS_CLOSED :=  {  acc := ·4  }   . 
Global Instance Acc_Errors_ι_NO_SUCH_PARTICIPANT : Accessor Errors_ι_NO_SUCH_PARTICIPANT :=  {  acc := ·5  }   . 
Global Instance Acc_Errors_ι_IS_NOT_DEPOOL : Accessor Errors_ι_IS_NOT_DEPOOL :=  {  acc := ·6 }   . 
Global Instance Acc_Errors_ι_INVALID_ROUND_STEP : Accessor Errors_ι_INVALID_ROUND_STEP :=  {  acc := ·7  }   . 
Global Instance Acc_Errors_ι_INVALID_QUERY_ID : Accessor Errors_ι_INVALID_QUERY_ID :=  {  acc := ·8  }   . 
Global Instance Acc_Errors_ι_IS_NOT_ELECTOR : Accessor Errors_ι_IS_NOT_ELECTOR :=  {  acc := ·9  }   . 
Global Instance Acc_Errors_ι_IS_NOT_OWNER_OR_SELF_CALL : Accessor Errors_ι_IS_NOT_OWNER_OR_SELF_CALL :=  {  acc := ·10  }   . 
Global Instance Acc_Errors_ι_BAD_STAKES : Accessor Errors_ι_BAD_STAKES :=  {  acc := ·11  }   . 
Global Instance Acc_Errors_ι_CONSTRUCTOR_NO_PUBKEY : Accessor Errors_ι_CONSTRUCTOR_NO_PUBKEY :=  {  acc := ·12  }   . 
Global Instance Acc_Errors_ι_VALIDATOR_IS_NOT_STD : Accessor Errors_ι_VALIDATOR_IS_NOT_STD :=  {  acc := ·13  }   . 
Global Instance Acc_Errors_ι_BAD_PART_REWARD : Accessor Errors_ι_BAD_PART_REWARD :=  {  acc := ·14  }   . 
Global Instance Acc_Errors_ι_BAD_MINIMUM_BALANCE : Accessor Errors_ι_BAD_MINIMUM_BALANCE :=  {  acc := ·15  }   . 
Global Instance Acc_Errors_ι_BAD_PROXY_CODE : Accessor Errors_ι_BAD_PROXY_CODE :=  {  acc := ·16  }   . 
Global Instance Acc_Errors_ι_NOT_WORKCHAIN0 : Accessor Errors_ι_NOT_WORKCHAIN0 :=  {  acc := ·17  }   . 


Instance Errors_default : XDefault Errors :=  {  
	  default := ErrorsC default default default default 
						           default default default default 
						           default default default default 
						           default default default default 
						           default default 
  }   . 
(* Definition ErrorsT := StateT Errors . *) 
 
  
Definition InternalErrors := @InternalErrorsP XInteger . 
Global Instance Struct_InternalErrors : Struct InternalErrors :=  { 
 	fields :=  [ 
 		@existT _ _ _ InternalErrors_ι_ERROR507 , 
 		@existT _ _ _ InternalErrors_ι_ERROR508 , 
 		@existT _ _ _ InternalErrors_ι_ERROR509 , 
 		@existT _ _ _ InternalErrors_ι_ERROR511 , 
 		@existT _ _ _ InternalErrors_ι_ERROR513 , 
 		@existT _ _ _ InternalErrors_ι_ERROR516 , 
 		@existT _ _ _ InternalErrors_ι_ERROR517 , 
 		@existT _ _ _ InternalErrors_ι_ERROR518 , 
 		@existT _ _ _ InternalErrors_ι_ERROR519 , 
 		@existT _ _ _ InternalErrors_ι_ERROR521 , 
 		@existT _ _ _ InternalErrors_ι_ERROR522 , 
 		@existT _ _ _ InternalErrors_ι_ERROR523 , 
 		@existT _ _ _ InternalErrors_ι_ERROR524 , 
 		@existT _ _ _ InternalErrors_ι_ERROR525 , 
 		@existT _ _ _ InternalErrors_ι_ERROR526 , 
 		@existT _ _ _ InternalErrors_ι_ERROR527 , 
 		@existT _ _ _ InternalErrors_ι_ERROR528 
 	 ]   ;  
 	 ctor := InternalErrorsC  
 }   . 
Global Instance Acc_InternalErrors_ι_ERROR507 : Accessor InternalErrors_ι_ERROR507 :=  {  acc := ·0  }   . 
Global Instance Acc_InternalErrors_ι_ERROR508 : Accessor InternalErrors_ι_ERROR508 :=  {  acc := ·1  }   . 
Global Instance Acc_InternalErrors_ι_ERROR509 : Accessor InternalErrors_ι_ERROR509 :=  {  acc := ·2  }   . 
Global Instance Acc_InternalErrors_ι_ERROR511 : Accessor InternalErrors_ι_ERROR511 :=  {  acc := ·3  }   . 
Global Instance Acc_InternalErrors_ι_ERROR513 : Accessor InternalErrors_ι_ERROR513 :=  {  acc := ·4  }   . 
Global Instance Acc_InternalErrors_ι_ERROR516 : Accessor InternalErrors_ι_ERROR516 :=  {  acc := ·5  }   . 
Global Instance Acc_InternalErrors_ι_ERROR517 : Accessor InternalErrors_ι_ERROR517 :=  {  acc := ·6  }   . 
Global Instance Acc_InternalErrors_ι_ERROR518 : Accessor InternalErrors_ι_ERROR518 :=  {  acc := ·7  }   . 
Global Instance Acc_InternalErrors_ι_ERROR519 : Accessor InternalErrors_ι_ERROR519 :=  {  acc := ·8  }   . 
Global Instance Acc_InternalErrors_ι_ERROR521 : Accessor InternalErrors_ι_ERROR521 :=  {  acc := ·9  }   . 
Global Instance Acc_InternalErrors_ι_ERROR522 : Accessor InternalErrors_ι_ERROR522 :=  {  acc := ·10  }   . 
Global Instance Acc_InternalErrors_ι_ERROR523 : Accessor InternalErrors_ι_ERROR523 :=  {  acc := ·11  }   . 
Global Instance Acc_InternalErrors_ι_ERROR524 : Accessor InternalErrors_ι_ERROR524 :=  {  acc := ·12  }   . 
Global Instance Acc_InternalErrors_ι_ERROR525 : Accessor InternalErrors_ι_ERROR525 :=  {  acc := ·13  }   . 
Global Instance Acc_InternalErrors_ι_ERROR526 : Accessor InternalErrors_ι_ERROR526 :=  {  acc := ·14  }   . 
Global Instance Acc_InternalErrors_ι_ERROR527 : Accessor InternalErrors_ι_ERROR527 :=  {  acc := ·15  }   . 
Global Instance Acc_InternalErrors_ι_ERROR528 : Accessor InternalErrors_ι_ERROR528 :=  {  acc := ·16  }   . 
Instance InternalErrors_default : XDefault InternalErrors :=  {  
 	 default := InternalErrorsC default default default default default default default default default default default default default default default default default  
  }   . 
(* Definition InternalErrorsT := StateT InternalErrors . *) 
 
(* Print   DePoolLib_ι_ParticipantP. *)
Definition DePoolLib_ι_Participant := @DePoolLib_ι_ParticipantP XInteger8 XInteger64 XBool . 
Definition DePoolLib_ι_Request := @DePoolLib_ι_RequestP XInteger8 XInteger32 XInteger64 XInteger256 XList. 
Definition DePoolLib := @DePoolLibP XInteger32 XInteger64. 
Bind Scope struct_scope with DePoolLib_ι_Participant  . 
Bind Scope struct_scope with DePoolLib_ι_Request  . 
Global Instance Struct_DePoolLib_ι_Participant : Struct DePoolLib_ι_Participant :=  {  
 	 fields :=  [  
 		@existT _ _ _ DePoolLib_ι_Participant_ι_roundQty , 
 		@existT _ _ _ DePoolLib_ι_Participant_ι_reward , 
 		@existT _ _ _ DePoolLib_ι_Participant_ι_haveVesting , 
 		@existT _ _ _ DePoolLib_ι_Participant_ι_haveLock , 
 		@existT _ _ _ DePoolLib_ι_Participant_ι_reinvest , 
 		@existT _ _ _ DePoolLib_ι_Participant_ι_withdrawValue 
 	  ]   ;  
 	 ctor := DePoolLib_ι_ParticipantC 
 }   . 
Global Instance Acc_DePoolLib_ι_Participant_ι_roundQty : Accessor DePoolLib_ι_Participant_ι_roundQty :=  {  acc := ·0  }   . 
Global Instance Acc_DePoolLib_ι_Participant_ι_reward : Accessor DePoolLib_ι_Participant_ι_reward :=  {  acc := ·1  }   . 
Global Instance Acc_DePoolLib_ι_Participant_ι_haveVesting : Accessor DePoolLib_ι_Participant_ι_haveVesting :=  {  acc := ·2  }   . 
Global Instance Acc_DePoolLib_ι_Participant_ι_haveLock : Accessor DePoolLib_ι_Participant_ι_haveLock :=  {  acc := ·3  }   . 
Global Instance Acc_DePoolLib_ι_Participant_ι_reinvest : Accessor DePoolLib_ι_Participant_ι_reinvest :=  {  acc := ·4  }   . 
Global Instance Acc_DePoolLib_ι_Participant_ι_withdrawValue : Accessor DePoolLib_ι_Participant_ι_withdrawValue :=  {  acc := ·5  }   . 
Global Instance Struct_DePoolLib_ι_Request : Struct DePoolLib_ι_Request :=  {  
 	 fields :=  [  
 		@existT _ _ _ DePoolLib_ι_Request_ι_queryId , 
 		@existT _ _ _ DePoolLib_ι_Request_ι_validatorKey , 
 		@existT _ _ _ DePoolLib_ι_Request_ι_stakeAt , 
 		@existT _ _ _ DePoolLib_ι_Request_ι_maxFactor , 
 		@existT _ _ _ DePoolLib_ι_Request_ι_adnlAddr , 
 		@existT _ _ _ DePoolLib_ι_Request_ι_signature 
 	  ]   ;  
 	 ctor := DePoolLib_ι_RequestC 
 }   . 
Global Instance Acc_DePoolLib_ι_Request_ι_queryId : Accessor DePoolLib_ι_Request_ι_queryId :=  {  acc := ·0  }   . 
Global Instance Acc_DePoolLib_ι_Request_ι_validatorKey : Accessor DePoolLib_ι_Request_ι_validatorKey :=  {  acc := ·1  }   . 
Global Instance Acc_DePoolLib_ι_Request_ι_stakeAt : Accessor DePoolLib_ι_Request_ι_stakeAt :=  {  acc := ·2  }   . 
Global Instance Acc_DePoolLib_ι_Request_ι_maxFactor : Accessor DePoolLib_ι_Request_ι_maxFactor :=  {  acc := ·3  }   . 
Global Instance Acc_DePoolLib_ι_Request_ι_adnlAddr : Accessor DePoolLib_ι_Request_ι_adnlAddr :=  {  acc := ·4  }   . 
Global Instance Acc_DePoolLib_ι_Request_ι_signature : Accessor DePoolLib_ι_Request_ι_signature :=  {  acc := ·5  }   . 
Global Instance Struct_DePoolLib : Struct DePoolLib :=  { 
 	fields :=  [ 
 		@existT _ _ _ DePoolLib_ι_PROXY_FEE , 
 		@existT _ _ _ DePoolLib_ι_ELECTOR_FEE , 
 		@existT _ _ _ DePoolLib_ι_MAX_UINT64 , 
 		@existT _ _ _ DePoolLib_ι_MAX_TIME , 
		@existT _ _ _ DePoolLib_ι_ELECTOR_UNFREEZE_LAG ,
		@existT _ _ _ DePoolLib_ι_MIN_PROXY_BALANCE ,
		@existT _ _ _ DePoolLib_ι_PROXY_CONSTRUCTOR_FEE ,
		@existT _ _ _ DePoolLib_ι_DEPOOL_CONSTRUCTOR_FEE
 	 ]   ;  
 	 ctor := DePoolLibC 
 }   . 
Global Instance Acc_DePoolLib_ι_PROXY_FEE : Accessor DePoolLib_ι_PROXY_FEE :=  {  acc := ·0  }   . 
Global Instance Acc_DePoolLib_ι_ELECTOR_FEE : Accessor DePoolLib_ι_ELECTOR_FEE :=  {  acc := ·1  }   . 
Global Instance Acc_DePoolLib_ι_MAX_UINT64 : Accessor DePoolLib_ι_MAX_UINT64 :=  {  acc := ·2  }   . 
Global Instance Acc_DePoolLib_ι_MAX_TIME : Accessor DePoolLib_ι_MAX_TIME :=  {  acc := ·3  }   . 
Global Instance Acc_DePoolLib_ι_ELECTOR_UNFREEZE_LAG : Accessor DePoolLib_ι_ELECTOR_UNFREEZE_LAG :=  {  acc := ·4  }   . 
Global Instance Acc_DePoolLib_ι_MIN_PROXY_BALANCE : Accessor DePoolLib_ι_MIN_PROXY_BALANCE :=  {  acc := ·5  }   . 
Global Instance Acc_DePoolLib_ι_PROXY_CONSTRUCTOR_FEE : Accessor DePoolLib_ι_PROXY_CONSTRUCTOR_FEE :=  {  acc := ·6  }   .
Global Instance Acc_DePoolLib_ι_DEPOOL_CONSTRUCTOR_FEE : Accessor DePoolLib_ι_DEPOOL_CONSTRUCTOR_FEE :=  {  acc := ·7  }   .


Instance DePoolLib_ι_Participant_default : XDefault DePoolLib_ι_Participant :=  {  
 	 default := DePoolLib_ι_ParticipantC default default default default default default 
  }   . 
Instance DePoolLib_ι_Request_default : XDefault DePoolLib_ι_Request :=  {  
 	 default := DePoolLib_ι_RequestC default default default default default default  
  }   . 
Instance DePoolLib_default : XDefault DePoolLib :=  {  
 	 default := DePoolLibC default default default default 
                         default default default default
  }   . 
(* Definition DePoolLibT := StateT DePoolLib . *) 
 
Print DePoolProxyContractP.
 Definition DePoolProxyContract := @DePoolProxyContractP XInteger (* XInteger64 *)  XAddress . 
Global Instance Struct_DePoolProxyContract : Struct DePoolProxyContract :=  { 
 	fields :=  [ 
 		@existT _ _ _ DePoolProxyContract_ι_ERROR_IS_NOT_DEPOOL , 
 		@existT _ _ _ DePoolProxyContract_ι_ERROR_BAD_BALANCE , 
 		@existT _ _ _ DePoolProxyContract_ι_m_dePool 
 
 	 ]   ;  
 	 ctor := DePoolProxyContractC 
 }   . 
Global Instance Acc_DePoolProxyContract_ι_ERROR_IS_NOT_DEPOOL : Accessor DePoolProxyContract_ι_ERROR_IS_NOT_DEPOOL :=  {  acc := ·0  }   . 
Global Instance Acc_DePoolProxyContract_ι_ERROR_BAD_BALANCE : Accessor DePoolProxyContract_ι_ERROR_BAD_BALANCE :=  {  acc := ·1  }   . 
Global Instance Acc_DePoolProxyContract_ι_m_dePool : Accessor DePoolProxyContract_ι_m_dePool :=  {  acc := ·2  }   . 
Instance DePoolProxyContract_default : XDefault DePoolProxyContract :=  {  
 	 default := DePoolProxyContractC default default default  
  }   . 
(* Definition DePoolProxyContractT := StateT DePoolProxyContract . *) 
 
  
 Definition RoundsBase_ι_InvestParams := @RoundsBase_ι_InvestParamsP XInteger32 XInteger64 XAddress . 
 Definition RoundsBase_ι_StakeValue := @RoundsBase_ι_StakeValueP  XInteger32 XInteger64  XAddress (* XBool *) XMaybe . 
 Definition RoundsBase_ι_Round := @RoundsBase_ι_RoundP XInteger8 XInteger32 XInteger64 XInteger256 XAddress XBool  XList XMaybe  XHMap . 
 Definition RoundsBase_ι_TruncatedRound := @RoundsBase_ι_TruncatedRoundP XInteger32 XInteger64 XInteger256 XBool. 
 Definition RoundsBase := @RoundsBaseP XInteger8 XInteger32 XInteger64 XInteger256 XAddress XBool   XList  XMaybe XHMap . 

 Bind Scope struct_scope with RoundsBase_ι_InvestParams  . 
 Bind Scope struct_scope with RoundsBase_ι_StakeValue  . 
 Bind Scope struct_scope with RoundsBase_ι_Round  . 
 Bind Scope struct_scope with RoundsBase_ι_TruncatedRound  . 
Global Instance Struct_RoundsBase_ι_InvestParams : Struct RoundsBase_ι_InvestParams :=  {  
 	 fields :=  [  
 	(* 	@existT _ _ _ RoundsBase_ι_InvestParams_ι_isActive ,  *)
 		@existT _ _ _ RoundsBase_ι_InvestParams_ι_amount , 
 		@existT _ _ _ RoundsBase_ι_InvestParams_ι_lastWithdrawalTime , 
 		@existT _ _ _ RoundsBase_ι_InvestParams_ι_withdrawalPeriod , 
 		@existT _ _ _ RoundsBase_ι_InvestParams_ι_withdrawalValue , 
 		@existT _ _ _ RoundsBase_ι_InvestParams_ι_owner 
 	  ]   ;  
 	 ctor := RoundsBase_ι_InvestParamsC 
 }   . 
(* Global Instance Acc_RoundsBase_ι_InvestParams_ι_isActive : Accessor RoundsBase_ι_InvestParams_ι_isActive :=  {  acc := ·0  }   . 
 *)Global Instance Acc_RoundsBase_ι_InvestParams_ι_amount : Accessor RoundsBase_ι_InvestParams_ι_amount :=  {  acc := ·0  }   . 
Global Instance Acc_RoundsBase_ι_InvestParams_ι_lastWithdrawalTime : Accessor RoundsBase_ι_InvestParams_ι_lastWithdrawalTime :=  {  acc := ·1  }   . 
Global Instance Acc_RoundsBase_ι_InvestParams_ι_withdrawalPeriod : Accessor RoundsBase_ι_InvestParams_ι_withdrawalPeriod :=  {  acc := ·2  }   . 
Global Instance Acc_RoundsBase_ι_InvestParams_ι_withdrawalValue : Accessor RoundsBase_ι_InvestParams_ι_withdrawalValue :=  {  acc := ·3  }   . 
Global Instance Acc_RoundsBase_ι_InvestParams_ι_owner : Accessor RoundsBase_ι_InvestParams_ι_owner :=  {  acc := ·4  }   . 
Global Instance Struct_RoundsBase_ι_StakeValue : Struct RoundsBase_ι_StakeValue :=  {  
 	 fields :=  [  
		 @existT _ _ _ RoundsBase_ι_StakeValue_ι_ordinary ,
		 @existT _ _ _ RoundsBase_ι_StakeValue_ι_vesting ,
		 @existT _ _ _ RoundsBase_ι_StakeValue_ι_lock
 	  ]   ;  
 	 ctor := RoundsBase_ι_StakeValueC 
 }   . 
Global Instance Acc_RoundsBase_ι_StakeValue_ι_ordinary : Accessor RoundsBase_ι_StakeValue_ι_ordinary :=  {  acc := ·0  }   .
Global Instance Acc_RoundsBase_ι_StakeValue_ι_vesting : Accessor RoundsBase_ι_StakeValue_ι_vesting :=  {  acc := ·1  }   .
Global Instance Acc_RoundsBase_ι_StakeValue_ι_lock : Accessor RoundsBase_ι_StakeValue_ι_lock :=  {  acc := ·2  }   . 

Global Instance Struct_RoundsBase_ι_Round : Struct RoundsBase_ι_Round :=  {  
 	 fields :=  [  
 		@existT _ _ _ RoundsBase_ι_Round_ι_id , 
 		@existT _ _ _ RoundsBase_ι_Round_ι_supposedElectedAt , 
 		@existT _ _ _ RoundsBase_ι_Round_ι_unfreeze , 
		@existT _ _ _ RoundsBase_ι_Round_ι_stakeHeldFor ,
 		@existT _ _ _ RoundsBase_ι_Round_ι_vsetHashInElectionPhase , 
 		@existT _ _ _ RoundsBase_ι_Round_ι_step , 
 		@existT _ _ _ RoundsBase_ι_Round_ι_completionReason , 
 		@existT _ _ _ RoundsBase_ι_Round_ι_stake , 
		@existT _ _ _ RoundsBase_ι_Round_ι_recoveredStake ,
		@existT _ _ _ RoundsBase_ι_Round_ι_unused ,
		@existT _ _ _ RoundsBase_ι_Round_ι_isValidatorStakeCompleted ,
		@existT _ _ _ RoundsBase_ι_Round_ι_grossReward ,
		@existT _ _ _ RoundsBase_ι_Round_ι_rewards , 
 		@existT _ _ _ RoundsBase_ι_Round_ι_participantQty , 
 		@existT _ _ _ RoundsBase_ι_Round_ι_stakes , 
		@existT _ _ _ RoundsBase_ι_Round_ι_validatorStake ,
		@existT _ _ _ RoundsBase_ι_Round_ι_validatorRemainingStake ,
		@existT _ _ _ RoundsBase_ι_Round_ι_handledStakesAndRewards ,
		@existT _ _ _ RoundsBase_ι_Round_ι_validatorRequest ,
 
 		@existT _ _ _ RoundsBase_ι_Round_ι_elector , 
 		@existT _ _ _ RoundsBase_ι_Round_ι_proxy 
	  ]   ;  
 	 ctor := RoundsBase_ι_RoundC 
 }   . 
Global Instance Acc_RoundsBase_ι_Round_ι_id : Accessor RoundsBase_ι_Round_ι_id :=  {  acc := ·0  }   . 
Global Instance Acc_RoundsBase_ι_Round_ι_supposedElectedAt : Accessor RoundsBase_ι_Round_ι_supposedElectedAt :=  {  acc := ·1  }   . 
Global Instance Acc_RoundsBase_ι_Round_ι_unfreeze : Accessor RoundsBase_ι_Round_ι_unfreeze :=  {  acc := ·2  }   . 
Global Instance Acc_RoundsBase_ι_Round_ι_stakeHeldFor : Accessor RoundsBase_ι_Round_ι_stakeHeldFor :=  {  acc := ·3  }   . 
Global Instance Acc_RoundsBase_ι_Round_ι_vsetHashInElectionPhase : Accessor RoundsBase_ι_Round_ι_vsetHashInElectionPhase :=  {  acc := ·4  }   . 
Global Instance Acc_RoundsBase_ι_Round_ι_step : Accessor RoundsBase_ι_Round_ι_step :=  {  acc := ·5  }   . 
Global Instance Acc_RoundsBase_ι_Round_ι_completionReason : Accessor RoundsBase_ι_Round_ι_completionReason :=  {  acc := ·6  }   . 
Global Instance Acc_RoundsBase_ι_Round_ι_stake : Accessor RoundsBase_ι_Round_ι_stake :=  {  acc := ·7  }   . 
Global Instance Acc_RoundsBase_ι_Round_ι_recoveredStake : Accessor RoundsBase_ι_Round_ι_recoveredStake :=  {  acc := ·8  }   . 
Global Instance Acc_RoundsBase_ι_Round_ι_unused : Accessor RoundsBase_ι_Round_ι_unused :=  {  acc := ·9  }   .
Global Instance Acc_RoundsBase_ι_Round_ι_isValidatorStakeCompleted : Accessor RoundsBase_ι_Round_ι_isValidatorStakeCompleted :=  {  acc := ·10  }   . 
Global Instance Acc_RoundsBase_ι_Round_ι_grossReward :  Accessor RoundsBase_ι_Round_ι_grossReward :=  {  acc := ·11  }   .
Global Instance Acc_RoundsBase_ι_Round_ι_rewards : Accessor RoundsBase_ι_Round_ι_rewards :=  {  acc := ·12  }   . 
Global Instance Acc_RoundsBase_ι_Round_ι_participantQty : Accessor RoundsBase_ι_Round_ι_participantQty :=  {  acc := ·13  }   . 
Global Instance Acc_RoundsBase_ι_Round_ι_stakes : Accessor RoundsBase_ι_Round_ι_stakes :=  {  acc := ·14  }   . 
Global Instance Acc_RoundsBase_ι_Round_ι_validatorStake : Accessor RoundsBase_ι_Round_ι_validatorStake :=  {  acc := ·15  }   . 
Global Instance Acc_RoundsBase_ι_Round_ι_validatorRemainingStake : Accessor RoundsBase_ι_Round_ι_validatorRemainingStake :=  {  acc := ·16  }   . 
Global Instance Acc_RoundsBase_ι_Round_ι_handledStakesAndRewards : Accessor RoundsBase_ι_Round_ι_handledStakesAndRewards :=  {  acc := ·17  }   .
Global Instance Acc_RoundsBase_ι_Round_ι_validatorRequest : Accessor RoundsBase_ι_Round_ι_validatorRequest :=  {  acc := ·18  }   . 
Global Instance Acc_RoundsBase_ι_Round_ι_elector : Accessor RoundsBase_ι_Round_ι_elector :=  {  acc := ·19  }   . 
Global Instance Acc_RoundsBase_ι_Round_ι_proxy : Accessor RoundsBase_ι_Round_ι_proxy :=  {  acc := ·20  }   . 

 
Global Instance Struct_RoundsBase_ι_TruncatedRound : Struct RoundsBase_ι_TruncatedRound :=  {  
 	 fields :=  [  
 		@existT _ _ _ RoundsBase_ι_TruncatedRound_ι_id , 
 		@existT _ _ _ RoundsBase_ι_TruncatedRound_ι_supposedElectedAt , 
 		@existT _ _ _ RoundsBase_ι_TruncatedRound_ι_unfreeze , 
		@existT _ _ _ RoundsBase_ι_TruncatedRound_ι_stakeHeldFor ,
		@existT _ _ _ RoundsBase_ι_TruncatedRound_ι_vsetHashInElectionPhase ,
 		@existT _ _ _ RoundsBase_ι_TruncatedRound_ι_step , 
 		@existT _ _ _ RoundsBase_ι_TruncatedRound_ι_completionReason , 
 		@existT _ _ _ RoundsBase_ι_TruncatedRound_ι_stake , 
		@existT _ _ _ RoundsBase_ι_TruncatedRound_ι_recoveredStake ,
		@existT _ _ _ RoundsBase_ι_TruncatedRound_ι_unused , 
 		@existT _ _ _ RoundsBase_ι_TruncatedRound_ι_isValidatorStakeCompleted ,
		@existT _ _ _ RoundsBase_ι_TruncatedRound_ι_rewards , 
 		@existT _ _ _ RoundsBase_ι_TruncatedRound_ι_participantQty , 
		@existT _ _ _ RoundsBase_ι_TruncatedRound_ι_validatorStake ,
		@existT _ _ _ RoundsBase_ι_TruncatedRound_ι_validatorRemainingStake ,
		@existT _ _ _ RoundsBase_ι_TruncatedRound_ι_handledStakesAndRewards 
 	  ]   ;  
 	 ctor := RoundsBase_ι_TruncatedRoundC 
 }   . 
Global Instance Acc_RoundsBase_ι_TruncatedRound_ι_id : Accessor RoundsBase_ι_TruncatedRound_ι_id :=  {  acc := ·0  }   . 
Global Instance Acc_RoundsBase_ι_TruncatedRound_ι_supposedElectedAt : Accessor RoundsBase_ι_TruncatedRound_ι_supposedElectedAt :=  {  acc := ·1  }   . 
Global Instance Acc_RoundsBase_ι_TruncatedRound_ι_unfreeze : Accessor RoundsBase_ι_TruncatedRound_ι_unfreeze :=  {  acc := ·2  }   . 
Global Instance Acc_RoundsBase_ι_TruncatedRound_ι_stakeHeldFor : Accessor RoundsBase_ι_TruncatedRound_ι_stakeHeldFor :=  {  acc := ·3  }   . 
Global Instance Acc_RoundsBase_ι_TruncatedRound_ι_vsetHashInElectionPhase : Accessor RoundsBase_ι_TruncatedRound_ι_vsetHashInElectionPhase :=  {  acc := ·4  }   . 
Global Instance Acc_RoundsBase_ι_TruncatedRound_ι_step : Accessor RoundsBase_ι_TruncatedRound_ι_step :=  {  acc := ·5  }   . 
Global Instance Acc_RoundsBase_ι_TruncatedRound_ι_completionReason : Accessor RoundsBase_ι_TruncatedRound_ι_completionReason :=  {  acc := ·6  }   . 
Global Instance Acc_RoundsBase_ι_TruncatedRound_ι_stake : Accessor RoundsBase_ι_TruncatedRound_ι_stake :=  {  acc := ·7  }   . 
Global Instance Acc_RoundsBase_ι_TruncatedRound_ι_recoveredStake : Accessor RoundsBase_ι_TruncatedRound_ι_recoveredStake :=  {  acc := ·8  }   . 
Global Instance Acc_RoundsBase_ι_TruncatedRound_ι_unused : Accessor RoundsBase_ι_TruncatedRound_ι_unused :=  {  acc := ·9  }   . 
Global Instance Acc_RoundsBase_ι_TruncatedRound_ι_isValidatorStakeCompleted : Accessor RoundsBase_ι_TruncatedRound_ι_isValidatorStakeCompleted :=  {  acc := ·10  }   . 
Global Instance Acc_RoundsBase_ι_TruncatedRound_ι_rewards : Accessor RoundsBase_ι_TruncatedRound_ι_rewards :=  {  acc := ·11  }   . 
Global Instance Acc_RoundsBase_ι_TruncatedRound_ι_participantQty : Accessor RoundsBase_ι_TruncatedRound_ι_participantQty :=  {  acc := ·12  }   . 
Global Instance Acc_RoundsBase_ι_TruncatedRound_ι_validatorStake : Accessor RoundsBase_ι_TruncatedRound_ι_validatorStake :=  {  acc := ·13  }   . 
Global Instance Acc_RoundsBase_ι_TruncatedRound_ι_validatorRemainingStake : Accessor RoundsBase_ι_TruncatedRound_ι_validatorRemainingStake :=  {  acc := ·14  }   . 
Global Instance Acc_RoundsBase_ι_TruncatedRound_ι_handledStakesAndRewards : Accessor RoundsBase_ι_TruncatedRound_ι_handledStakesAndRewards :=  {  acc := ·15  }   . 


Global Instance Struct_RoundsBase : Struct RoundsBase :=  { 
 	fields :=  [ 
 		@existT _ _ _ RoundsBase_ι_m_rounds , 
 		@existT _ _ _ RoundsBase_ι_m_roundQty ,
 		@existT _ _ _ RoundsBase_ι_lastRoundInfo
 	 ]   ;  
 	 ctor := RoundsBaseC 
 }   . 
Global Instance Acc_RoundsBase_ι_m_rounds : Accessor RoundsBase_ι_m_rounds :=  {  acc := ·0  }   . 
Global Instance Acc_RoundsBase_ι_m_roundQty : Accessor RoundsBase_ι_m_roundQty :=  {  acc := ·1  }   . 
Global Instance Acc_RoundsBase_ι_lastRoundInfo : Accessor RoundsBase_ι_lastRoundInfo := {  acc := ·2  }   . 

Instance RoundsBase_ι_InvestParams_default : XDefault RoundsBase_ι_InvestParams :=  {  
 	 default := RoundsBase_ι_InvestParamsC default default default default default (* default *)  
  }   . 
Instance RoundsBase_ι_StakeValue_default : XDefault RoundsBase_ι_StakeValue :=  {  
 	 default := RoundsBase_ι_StakeValueC default default default 
  }   . 

Instance RoundsBase_ι_Round_default : XDefault RoundsBase_ι_Round :=
 {
	  default := RoundsBase_ι_RoundC default default default default 
									 default default default default 
									 default default default default 
									 default default default default  
									 default default default default
                   default 
  }.

Instance RoundsBase_ι_TruncatedRound_default : XDefault RoundsBase_ι_TruncatedRound :=  {  
	  default := RoundsBase_ι_TruncatedRoundC default default default default 
												default default default default 
												default default default default  
												default default default default 
  }   . 
Instance RoundsBase_default : XDefault RoundsBase :=  {  
 	 default := RoundsBaseC default default default
  }   . 

(* Definition RoundsBaseT := StateT RoundsBase . *) 

Print DePoolContractP.

Definition DePoolContract := @DePoolContractP XInteger8 XInteger16 XInteger64 XInteger256 XBool . 


Global Instance Struct_DePoolContract : Struct DePoolContract :=  { 
 	fields :=  [ 
 		@existT _ _ _ DePoolContract_ι_STAKE_FEE , 
 		@existT _ _ _ DePoolContract_ι_RET_OR_REINV_FEE , 
 		@existT _ _ _ DePoolContract_ι_MAX_MSGS_PER_TR , 
 		@existT _ _ _ DePoolContract_ι_MAX_QTY_OF_OUT_ACTIONS , 
 		@existT _ _ _ DePoolContract_ι_VALUE_FOR_SELF_CALL , 
		@existT _ _ _ DePoolContract_ι_PROXY_CODE_HASH ,
 		@existT _ _ _ DePoolContract_ι_STATUS_SUCCESS , 
 		@existT _ _ _ DePoolContract_ι_STATUS_STAKE_TOO_SMALL , 
 		@existT _ _ _ DePoolContract_ι_STATUS_DEPOOL_CLOSED , 
 		@existT _ _ _ DePoolContract_ι_STATUS_NO_PARTICIPANT , 
 		@existT _ _ _ DePoolContract_ι_STATUS_PARTICIPANT_HAVE_ALREADY_VESTING , 
 		@existT _ _ _ DePoolContract_ι_STATUS_WITHDRAWAL_PERIOD_GREATER_TOTAL_PERIOD , 
 		@existT _ _ _ DePoolContract_ι_STATUS_TOTAL_PERIOD_MORE_18YEARS , 
 		@existT _ _ _ DePoolContract_ι_STATUS_WITHDRAWAL_PERIOD_IS_ZERO , 
 		@existT _ _ _ DePoolContract_ι_STATUS_TOTAL_PERIOD_IS_NOT_DIVED_BY_WITHDRAWAL_PERIOD , 
 		@existT _ _ _ DePoolContract_ι_STATUS_PERIOD_PAYMENT_IS_ZERO , 
 		@existT _ _ _ DePoolContract_ι_STATUS_REMAINING_STAKE_LESS_THAN_MINIMAL , 
 		@existT _ _ _ DePoolContract_ι_STATUS_PARTICIPANT_HAVE_ALREADY_LOCK , 
 		@existT _ _ _ DePoolContract_ι_STATUS_TRANSFER_AMOUNT_IS_TOO_BIG , 
 		@existT _ _ _ DePoolContract_ι_STATUS_TRANSFER_SELF , 
		@existT _ _ _ DePoolContract_ι_STATUS_TRANSFER_TO_OR_FROM_VALIDATOR ,
		@existT _ _ _ DePoolContract_ι_STATUS_FEE_TOO_SMALL ,
		@existT _ _ _ DePoolContract_ι_STATUS_INVALID_ADDRESS ,
		@existT _ _ _ DePoolContract_ι_STATUS_INVALID_BENEFICIARY ,
		@existT _ _ _ DePoolContract_ι_STATUS_NO_ELECTION_ROUND ,
		@existT _ _ _ DePoolContract_ι_STATUS_INVALID_ELECTION_ID ,
 		@existT _ _ _ DePoolContract_ι_m_poolClosed , 
 		@existT _ _ _ DePoolContract_ι_m_minStake , 
		@existT _ _ _ DePoolContract_ι_m_validatorAssurance ,
		@existT _ _ _ DePoolContract_ι_m_participantRewardFraction ,
		@existT _ _ _ DePoolContract_ι_m_validatorRewardFraction ,
		@existT _ _ _ DePoolContract_ι_m_balanceThreshold ,
		@existT _ _ _ DePoolContract_ι_CRITICAL_THRESHOLD
 	 ]   ;  
 	 ctor := DePoolContractC 
 }   . 

Global Instance Acc_DePoolContract_ι_STAKE_FEE : Accessor DePoolContract_ι_STAKE_FEE :=  {  acc := ·0  }   . 
Global Instance Acc_DePoolContract_ι_RET_OR_REINV_FEE : Accessor DePoolContract_ι_RET_OR_REINV_FEE :=  {  acc := ·1  }   . 
Global Instance Acc_DePoolContract_ι_MAX_MSGS_PER_TR : Accessor DePoolContract_ι_MAX_MSGS_PER_TR :=  {  acc := ·2  }   . 
Global Instance Acc_DePoolContract_ι_MAX_QTY_OF_OUT_ACTIONS : Accessor DePoolContract_ι_MAX_QTY_OF_OUT_ACTIONS :=  {  acc := ·3  }   . 
Global Instance Acc_DePoolContract_ι_VALUE_FOR_SELF_CALL : Accessor DePoolContract_ι_VALUE_FOR_SELF_CALL :=  {  acc := ·4  }   . 
Global Instance Acc_DePoolContract_ι_PROXY_CODE_HASH  : Accessor DePoolContract_ι_PROXY_CODE_HASH :=  {  acc := ·5  }   .
Global Instance Acc_DePoolContract_ι_STATUS_SUCCESS : Accessor DePoolContract_ι_STATUS_SUCCESS :=  {  acc := ·6  }   . 
Global Instance Acc_DePoolContract_ι_STATUS_STAKE_TOO_SMALL : Accessor DePoolContract_ι_STATUS_STAKE_TOO_SMALL :=  {  acc := ·7  }   . 
Global Instance Acc_DePoolContract_ι_STATUS_DEPOOL_CLOSED : Accessor DePoolContract_ι_STATUS_DEPOOL_CLOSED :=  {  acc := ·8  }   . 
Global Instance Acc_DePoolContract_ι_STATUS_NO_PARTICIPANT : Accessor DePoolContract_ι_STATUS_NO_PARTICIPANT :=  {  acc := ·9  }   . 
Global Instance Acc_DePoolContract_ι_STATUS_PARTICIPANT_HAVE_ALREADY_VESTING : Accessor DePoolContract_ι_STATUS_PARTICIPANT_HAVE_ALREADY_VESTING :=  {  acc := ·10  }   . 
Global Instance Acc_DePoolContract_ι_STATUS_WITHDRAWAL_PERIOD_GREATER_TOTAL_PERIOD : Accessor DePoolContract_ι_STATUS_WITHDRAWAL_PERIOD_GREATER_TOTAL_PERIOD :=  {  acc := ·11  }   . 
Global Instance Acc_DePoolContract_ι_STATUS_TOTAL_PERIOD_MORE_18YEARS : Accessor DePoolContract_ι_STATUS_TOTAL_PERIOD_MORE_18YEARS :=  {  acc := ·12  }   . 
Global Instance Acc_DePoolContract_ι_STATUS_WITHDRAWAL_PERIOD_IS_ZERO : Accessor DePoolContract_ι_STATUS_WITHDRAWAL_PERIOD_IS_ZERO :=  {  acc := ·12  }   . 
Global Instance Acc_DePoolContract_ι_STATUS_TOTAL_PERIOD_IS_NOT_DIVED_BY_WITHDRAWAL_PERIOD : Accessor DePoolContract_ι_STATUS_TOTAL_PERIOD_IS_NOT_DIVED_BY_WITHDRAWAL_PERIOD :=  {  acc := ·14  }   . 
Global Instance Acc_DePoolContract_ι_STATUS_PERIOD_PAYMENT_IS_ZERO : Accessor DePoolContract_ι_STATUS_PERIOD_PAYMENT_IS_ZERO :=  {  acc := ·15  }   . 
Global Instance Acc_DePoolContract_ι_STATUS_REMAINING_STAKE_LESS_THAN_MINIMAL : Accessor DePoolContract_ι_STATUS_REMAINING_STAKE_LESS_THAN_MINIMAL :=  {  acc := ·16  }   . 
Global Instance Acc_DePoolContract_ι_STATUS_PARTICIPANT_HAVE_ALREADY_LOCK : Accessor DePoolContract_ι_STATUS_PARTICIPANT_HAVE_ALREADY_LOCK :=  {  acc := ·17  }   . 
Global Instance Acc_DePoolContract_ι_STATUS_TRANSFER_AMOUNT_IS_TOO_BIG : Accessor DePoolContract_ι_STATUS_TRANSFER_AMOUNT_IS_TOO_BIG :=  {  acc := ·18  }   . 
Global Instance Acc_DePoolContract_ι_STATUS_TRANSFER_SELF : Accessor DePoolContract_ι_STATUS_TRANSFER_SELF :=  {  acc := ·19  }   . 
Global Instance Acc_DePoolContract_ι_STATUS_TRANSFER_TO_OR_FROM_VALIDATOR : Accessor DePoolContract_ι_STATUS_TRANSFER_TO_OR_FROM_VALIDATOR := {  acc := ·20  }   .
Global Instance Acc_DePoolContract_ι_STATUS_FEE_TOO_SMALL : Accessor DePoolContract_ι_STATUS_FEE_TOO_SMALL := {  acc := ·21 }   .
Global Instance Acc_DePoolContract_ι_STATUS_INVALID_ADDRESS : Accessor DePoolContract_ι_STATUS_INVALID_ADDRESS  := {  acc := ·22  }.
Global Instance Acc_DePoolContract_ι_STATUS_INVALID_BENEFICIARY : Accessor DePoolContract_ι_STATUS_INVALID_BENEFICIARY  := {  acc := ·23  }.
Global Instance Acc_DePoolContract_ι_STATUS_NO_ELECTION_ROUND : Accessor DePoolContract_ι_STATUS_NO_ELECTION_ROUND  := {  acc := ·24  }.
Global Instance Acc_DePoolContract_ι_STATUS_INVALID_ELECTION_ID : Accessor DePoolContract_ι_STATUS_INVALID_ELECTION_ID := {  acc := ·25  }.
Global Instance Acc_DePoolContract_ι_m_poolClosed : Accessor DePoolContract_ι_m_poolClosed :=  {  acc := ·26  }   . 
Global Instance Acc_DePoolContract_ι_m_minStake : Accessor DePoolContract_ι_m_minStake :=  {  acc := ·27  }   . 
Global Instance Acc_DePoolContract_ι_m_validatorAssurance : Accessor DePoolContract_ι_m_validatorAssurance := {  acc := ·28  }   .
Global Instance Acc_DePoolContract_ι_m_participantRewardFraction : Accessor DePoolContract_ι_m_participantRewardFraction := {  acc := ·29  }   .
Global Instance Acc_DePoolContract_ι_m_validatorRewardFraction : Accessor DePoolContract_ι_m_validatorRewardFraction := {  acc := ·30  }   .
Global Instance Acc_DePoolContract_ι_m_balanceThreshold : Accessor DePoolContract_ι_m_balanceThreshold := {  acc := ·31  }   .
Global Instance Acc_DePoolContract_ι_CRITICAL_THRESHOLD : Accessor DePoolContract_ι_CRITICAL_THRESHOLD  := {  acc := ·32  }.


Instance DePoolContract_default : XDefault DePoolContract :=  {  
	  default := DePoolContractC default default default default 
								               default default default default 
								               default default default default  
								               default default default default 
								               default default default default 
								               default default default default 
								               default default default default 
								               default default default default 
								               default 
  }   . 
(* Definition DePoolContractT := StateT DePoolContract . *) 
    
  
Definition TestElector_ι_Validator := @TestElector_ι_ValidatorP XInteger8 XInteger32 XInteger64 XInteger256. 
Definition TestElector := @TestElectorP XInteger8 XInteger32  XInteger64 XInteger256 XHMap . 
Bind Scope struct_scope with TestElector_ι_Validator  . 
Global Instance Struct_TestElector_ι_Validator : Struct TestElector_ι_Validator :=  {  
 	 fields :=  [  
 		@existT _ _ _ TestElector_ι_Validator_ι_stake , 
 		@existT _ _ _ TestElector_ι_Validator_ι_key , 
 		@existT _ _ _ TestElector_ι_Validator_ι_reward , 
 		@existT _ _ _ TestElector_ι_Validator_ι_qid , 
 		@existT _ _ _ TestElector_ι_Validator_ι_factor , 
 		@existT _ _ _ TestElector_ι_Validator_ι_adnl , 
 		@existT _ _ _ TestElector_ι_Validator_ι_signature 
 	  ]   ;  
 	 ctor := TestElector_ι_ValidatorC 
 }   . 
Global Instance Acc_TestElector_ι_Validator_ι_stake : Accessor TestElector_ι_Validator_ι_stake :=  {  acc := ·0  }   . 
Global Instance Acc_TestElector_ι_Validator_ι_key : Accessor TestElector_ι_Validator_ι_key :=  {  acc := ·1  }   . 
Global Instance Acc_TestElector_ι_Validator_ι_reward : Accessor TestElector_ι_Validator_ι_reward :=  {  acc := ·2  }   . 
Global Instance Acc_TestElector_ι_Validator_ι_qid : Accessor TestElector_ι_Validator_ι_qid :=  {  acc := ·3  }   . 
Global Instance Acc_TestElector_ι_Validator_ι_factor : Accessor TestElector_ι_Validator_ι_factor :=  {  acc := ·4  }   . 
Global Instance Acc_TestElector_ι_Validator_ι_adnl : Accessor TestElector_ι_Validator_ι_adnl :=  {  acc := ·5  }   . 
Global Instance Acc_TestElector_ι_Validator_ι_signature : Accessor TestElector_ι_Validator_ι_signature :=  {  acc := ·6  }   . 
Global Instance Struct_TestElector : Struct TestElector :=  { 
 	fields :=  [ 
 		@existT _ _ _ TestElector_ι_elections , 
 		@existT _ _ _ TestElector_ι_electAt , 
 		@existT _ _ _ TestElector_ι_ELECTIONS_BEGIN_BEFORE , 
 		@existT _ _ _ TestElector_ι_ELECTIONS_END_BEFORE , 
 		@existT _ _ _ TestElector_ι_ELECTED_FOR , 
 		@existT _ _ _ TestElector_ι_STAKE_HELD_FOR 
 
 	 ]   ;  
 	 ctor := TestElectorC 
 }   . 
Global Instance Acc_TestElector_ι_elections : Accessor TestElector_ι_elections :=  {  acc := ·0  }   . 
Global Instance Acc_TestElector_ι_electAt : Accessor TestElector_ι_electAt :=  {  acc := ·1  }   . 
Global Instance Acc_TestElector_ι_ELECTIONS_BEGIN_BEFORE : Accessor TestElector_ι_ELECTIONS_BEGIN_BEFORE :=  {  acc := ·2  }   . 
Global Instance Acc_TestElector_ι_ELECTIONS_END_BEFORE : Accessor TestElector_ι_ELECTIONS_END_BEFORE :=  {  acc := ·3  }   . 
Global Instance Acc_TestElector_ι_ELECTED_FOR : Accessor TestElector_ι_ELECTED_FOR :=  {  acc := ·4  }   . 
Global Instance Acc_TestElector_ι_STAKE_HELD_FOR : Accessor TestElector_ι_STAKE_HELD_FOR :=  {  acc := ·5  }   . 
Instance TestElector_ι_Validator_default : XDefault TestElector_ι_Validator :=  {  
 	 default := TestElector_ι_ValidatorC default default default default default default default  
  }   . 
Instance TestElector_default : XDefault TestElector :=  {  
 	 default := TestElectorC default default default default default default  
  }   . 
(* Definition TestElectorT := StateT TestElector . *) 



 

(* Print VMCommittedP. *)
Definition  VMCommitted := VMCommittedP XInteger XInteger8 XInteger16 XInteger32 XInteger64 XInteger256 XAddress XBool XList XMaybe XHMap.
Global Instance Struct_VMCommitted : Struct VMCommitted :=  { 
 	fields :=  [ 
		@existT _ _ _ VMCommitted_ι_DebugDePool ,
		@existT _ _ _ VMCommitted_ι_ValidatorBase ,
		@existT _ _ _ VMCommitted_ι_ProxyBase ,
		@existT _ _ _ VMCommitted_ι_ConfigParamsBase ,
		@existT _ _ _ VMCommitted_ι_ParticipantBase ,
		@existT _ _ _ VMCommitted_ι_DePoolHelper ,
		@existT _ _ _ VMCommitted_ι_Errors ,
		@existT _ _ _ VMCommitted_ι_InternalErrors ,
		@existT _ _ _ VMCommitted_ι_DePoolLib , 
		@existT _ _ _ VMCommitted_ι_DePoolProxyContract ,
		@existT _ _ _ VMCommitted_ι_RoundsBase ,
		@existT _ _ _ VMCommitted_ι_DePoolContract ,
		@existT _ _ _ VMCommitted_ι_DePool ,
		@existT _ _ _ VMCommitted_ι_Participant ,
		@existT _ _ _ VMCommitted_ι_TestElector 
 	 ]   ;  
 	 ctor := VMCommittedC 
 }   . 


Global Instance Acc_VMCommitted_ι_DebugDePool : Accessor VMCommitted_ι_DebugDePool := {  acc := ·0  }   . 
Global Instance Acc_VMCommitted_ι_ValidatorBase : Accessor VMCommitted_ι_ValidatorBase := {  acc := ·1  }   . 
Global Instance Acc_VMCommitted_ι_ProxyBase : Accessor VMCommitted_ι_ProxyBase := {  acc := ·2  }   . 
Global Instance Acc_VMCommitted_ι_ConfigParamsBase : Accessor VMCommitted_ι_ConfigParamsBase := {  acc := ·3  }   . 
Global Instance Acc_VMCommitted_ι_ParticipantBase : Accessor VMCommitted_ι_ParticipantBase := {  acc := ·4  }   . 
Global Instance Acc_VMCommitted_ι_DePoolHelper : Accessor VMCommitted_ι_DePoolHelper := {  acc := ·5  }   . 
Global Instance Acc_VMCommitted_ι_Errors : Accessor VMCommitted_ι_Errors := {  acc := ·6  }   . 
Global Instance Acc_VMCommitted_ι_InternalErrors : Accessor VMCommitted_ι_InternalErrors := {  acc := ·7  }   . 
Global Instance Acc_VMCommitted_ι_DePoolLib : Accessor  VMCommitted_ι_DePoolLib := {  acc := ·8  }   . 
Global Instance Acc_VMCommitted_ι_DePoolProxyContract : Accessor VMCommitted_ι_DePoolProxyContract := {  acc := ·9  }   . 
Global Instance Acc_VMCommitted_ι_RoundsBase : Accessor VMCommitted_ι_RoundsBase := {  acc := ·10  }   . 
Global Instance Acc_VMCommitted_ι_DePoolContract : Accessor VMCommitted_ι_DePoolContract := {  acc := ·11  }   . 
Global Instance Acc_VMCommitted_ι_DePool : Accessor VMCommitted_ι_DePool := {  acc := ·12 }   . 
Global Instance Acc_VMCommitted_ι_Participant : Accessor VMCommitted_ι_Participant := {  acc := ·13  }   . 
Global Instance Acc_VMCommitted_ι_TestElector : Accessor VMCommitted_ι_TestElector := {  acc := ·14  }   . 


Instance VMCommitted_default : XDefault VMCommitted :=  {  
	  default := VMCommittedC default default default default 
							   default default default default 
							   default default default default 
							   default default default
  }   . 
 
(* Print VMStateP. *) 
Definition VMState := @VMStateP XInteger XInteger8 XInteger16 XInteger32 XInteger64 XInteger128 XInteger256 XAddress XBool TvmCell XString XList XMaybe XHMap . 
Global Instance Struct_VMState : Struct VMState :=  { 
 	fields :=  [ 
 		@existT _ _ _ VMState_ι_pubkey , 
 		@existT _ _ _ VMState_ι_msg_pubkey , 
 		@existT _ _ _ VMState_ι_now , 
 		@existT _ _ _ VMState_ι_logstr , 
 		@existT _ _ _ VMState_ι_balance , 
 		@existT _ _ _ VMState_ι_address , 
 		@existT _ _ _ VMState_ι_ltime , 
 		@existT _ _ _ VMState_ι_code , 
 		@existT _ _ _ VMState_ι_events , 
		@existT _ _ _ VMState_ι_savedDePoolContracts , 
 		@existT _ _ _ VMState_ι_msg_sender , 
		@existT _ _ _ VMState_ι_msg_value ,
		@existT _ _ _ VMState_ι_messages , 
		@existT _ _ _ VMState_ι_msg_data , 
		@existT _ _ _ VMState_ι_transactions
 	 ]   ;  
 	 ctor := VMStateC 
 }   . 


Global Instance Acc_VMState_ι_pubkey : Accessor VMState_ι_pubkey :=  {  acc := ·0  }   . 
Global Instance Acc_VMState_ι_msg_pubkey : Accessor VMState_ι_msg_pubkey :=  {  acc := ·1  }   . 
Global Instance Acc_VMState_ι_now : Accessor VMState_ι_now :=  {  acc := ·2  }   . 
Global Instance Acc_VMState_ι_logstr : Accessor VMState_ι_logstr :=  {  acc := ·3  }   . 
Global Instance Acc_VMState_ι_balance : Accessor VMState_ι_balance :=  {  acc := ·4  }   . 
Global Instance Acc_VMState_ι_address : Accessor VMState_ι_address :=  {  acc := ·5  }   . 
Global Instance Acc_VMState_ι_ltime : Accessor VMState_ι_ltime :=  {  acc := ·6  }   . 
Global Instance Acc_VMState_ι_code : Accessor VMState_ι_code :=  {  acc := ·7  }   . 
Global Instance Acc_VMState_ι_events : Accessor VMState_ι_events :=  {  acc := ·8  }   . 
Global Instance Acc_VMState_ι_savedDePoolContract : Accessor VMState_ι_savedDePoolContracts :=  {  acc := ·9  }   . 
Global Instance Acc_VMState_ι_msg_sender : Accessor VMState_ι_msg_sender :=  {  acc := ·10  }   . 
Global Instance Acc_VMState_ι_msg_value : Accessor VMState_ι_msg_value :=  {  acc := ·11  }   . 
Global Instance Acc_VMState_ι_messages : Accessor VMState_ι_messages :=  {  acc := ·12  }   .
Global Instance Acc_VMState_ι_msg_data : Accessor VMState_ι_msg_data :=  {  acc := ·13  }   .
Global Instance Acc_VMState_ι_transactions : Accessor VMState_ι_transactions :=  {  acc := ·14  }   .


Instance stateT_default {X}`{XDefault X} : XDefault (forall S, StateT S X) := 
  {default := fun S => state_unit (S:=S) default}.

Instance VMState_default : XDefault VMState :=  {  
 	 default := VMStateC default default default default default default default default default default default default default default default
  }   . 

(* Print LocalStateP.  *)
Load "LocalStateInstances.v".
  
 
(* Print LedgerP.   
{I I8 I16 I32 I64 I128 I256 A B C S}%type_scope {L M HM P}%function_scope *)
Definition Ledger := @LedgerP XInteger  XInteger8 XInteger16 XInteger32 XInteger64 XInteger128 XInteger256 XAddress XBool TvmCell XString XList XMaybe XHMap XProd. 
Global Instance Struct_Ledger : Struct Ledger :=  { 
 	fields :=  [ 
 		@existT _ _ _ Ledger_ι_DebugDePool , 
 		@existT _ _ _ Ledger_ι_ValidatorBase , 
 		@existT _ _ _ Ledger_ι_ProxyBase , 
 		@existT _ _ _ Ledger_ι_ConfigParamsBase , 
 		@existT _ _ _ Ledger_ι_ParticipantBase , 
 		@existT _ _ _ Ledger_ι_DePoolHelper , 
 		@existT _ _ _ Ledger_ι_Errors , 
 		@existT _ _ _ Ledger_ι_InternalErrors , 
 		@existT _ _ _ Ledger_ι_DePoolLib , 
 		@existT _ _ _ Ledger_ι_DePoolProxyContract , 
 		@existT _ _ _ Ledger_ι_RoundsBase , 
 		@existT _ _ _ Ledger_ι_DePoolContract , 
 		@existT _ _ _ Ledger_ι_DePool , 
 		@existT _ _ _ Ledger_ι_Participant , 
 		@existT _ _ _ Ledger_ι_TestElector , 
 		@existT _ _ _ Ledger_ι_VMState , 
 		@existT _ _ _ Ledger_ι_LocalState 
 	 ]   ;  
 	 ctor := LedgerC 
 }   . 
Global Instance Acc_Ledger_ι_DebugDePool : Accessor Ledger_ι_DebugDePool :=  {  acc := ·0  }   . 
Global Instance Acc_Ledger_ι_ValidatorBase : Accessor Ledger_ι_ValidatorBase :=  {  acc := ·1  }   . 
Global Instance Acc_Ledger_ι_ProxyBase : Accessor Ledger_ι_ProxyBase :=  {  acc := ·2  }   . 
Global Instance Acc_Ledger_ι_ConfigParamsBase : Accessor Ledger_ι_ConfigParamsBase :=  {  acc := ·3  }   . 
Global Instance Acc_Ledger_ι_ParticipantBase : Accessor Ledger_ι_ParticipantBase :=  {  acc := ·4  }   . 
Global Instance Acc_Ledger_ι_DePoolHelper : Accessor Ledger_ι_DePoolHelper :=  {  acc := ·5  }   . 
Global Instance Acc_Ledger_ι_Errors : Accessor Ledger_ι_Errors :=  {  acc := ·6  }   . 
Global Instance Acc_Ledger_ι_InternalErrors : Accessor Ledger_ι_InternalErrors :=  {  acc := ·7  }   . 
Global Instance Acc_Ledger_ι_DePoolLib : Accessor Ledger_ι_DePoolLib :=  {  acc := ·8  }   . 
Global Instance Acc_Ledger_ι_DePoolProxyContract : Accessor Ledger_ι_DePoolProxyContract :=  {  acc := ·9  }   . 
Global Instance Acc_Ledger_ι_RoundsBase : Accessor Ledger_ι_RoundsBase :=  {  acc := ·10  }   . 
Global Instance Acc_Ledger_ι_DePoolContract : Accessor Ledger_ι_DePoolContract :=  {  acc := ·11  }   . 
Global Instance Acc_Ledger_ι_DePool : Accessor Ledger_ι_DePool :=  {  acc := ·12  }   . 
Global Instance Acc_Ledger_ι_Participant : Accessor Ledger_ι_Participant :=  {  acc := ·13  }   . 
Global Instance Acc_Ledger_ι_TestElector : Accessor Ledger_ι_TestElector :=  {  acc := ·14  }   . 
Global Instance Acc_Ledger_ι_VMState : Accessor Ledger_ι_VMState :=  {  acc := ·15  }   . 
Global Instance Acc_Ledger_ι_LocalState : Accessor Ledger_ι_LocalState :=  {  acc := ·16  }   . 
Instance Ledger_default : XDefault Ledger :=  {  
 	 default := LedgerC default default default default default default default default default default default default default default default default default  
  }   . 
 Definition LedgerT := StateT Ledger .  

 
Global Instance AccAcc_DebugDePool_ι_validators_elected_for : AccessorAccessor DebugDePool_ι_validators_elected_for :=  {  accacc := Ledger_ι_DebugDePool  }   . 
Global Instance AccAcc_DebugDePool_ι_elections_start_before : AccessorAccessor DebugDePool_ι_elections_start_before :=  {  accacc := Ledger_ι_DebugDePool  }   . 
Global Instance AccAcc_DebugDePool_ι_elections_end_before : AccessorAccessor DebugDePool_ι_elections_end_before :=  {  accacc := Ledger_ι_DebugDePool  }   . 
Global Instance AccAcc_DebugDePool_ι_stake_held_for : AccessorAccessor DebugDePool_ι_stake_held_for :=  {  accacc := Ledger_ι_DebugDePool  }   . 

Global Instance AccAcc_ValidatorBase_ι_m_validatorWallet : AccessorAccessor ValidatorBase_ι_m_validatorWallet :=  {  accacc := Ledger_ι_ValidatorBase  }   . 

Global Instance AccAcc_ProxyBase_ι_m_proxies : AccessorAccessor ProxyBase_ι_m_proxies :=  {  accacc := Ledger_ι_ProxyBase  }   . 

Global Instance AccAcc_ParticipantBase_ι_m_participants : AccessorAccessor ParticipantBase_ι_m_participants :=  {  accacc := Ledger_ι_ParticipantBase  }   . 

Global Instance AccAcc_DePoolHelper_ι_TICKTOCK_FEE : AccessorAccessor DePoolHelper_ι_TICKTOCK_FEE :=  {  accacc := Ledger_ι_DePoolHelper  }   . 
Global Instance AccAcc_DePoolHelper_ι__timerRate : AccessorAccessor DePoolHelper_ι__timerRate :=  {  accacc := Ledger_ι_DePoolHelper  }   . 
Global Instance AccAcc_DePoolHelper_ι__fwdFee : AccessorAccessor DePoolHelper_ι__fwdFee :=  {  accacc := Ledger_ι_DePoolHelper  }   . 
Global Instance AccAcc_DePoolHelper_ι__epsilon : AccessorAccessor DePoolHelper_ι__epsilon :=  {  accacc := Ledger_ι_DePoolHelper  }   . 
Global Instance AccAcc_DePoolHelper_ι_m_dePoolPool : AccessorAccessor DePoolHelper_ι_m_dePoolPool :=  {  accacc := Ledger_ι_DePoolHelper  }   . 
Global Instance AccAcc_DePoolHelper_ι_m_poolHistory : AccessorAccessor DePoolHelper_ι_m_poolHistory :=  {  accacc := Ledger_ι_DePoolHelper  }   . 
Global Instance AccAcc_DePoolHelper_ι_m_timer : AccessorAccessor DePoolHelper_ι_m_timer :=  {  accacc := Ledger_ι_DePoolHelper  }   . 
Global Instance AccAcc_DePoolHelper_ι_m_timeout : AccessorAccessor DePoolHelper_ι_m_timeout :=  {  accacc := Ledger_ι_DePoolHelper  }   . 

Global Instance AccAcc_Errors_ι_IS_NOT_OWNER : AccessorAccessor Errors_ι_IS_NOT_OWNER :=  {  accacc := Ledger_ι_Errors  }   . 
Global Instance AccAcc_Errors_ι_IS_NOT_PROXY : AccessorAccessor Errors_ι_IS_NOT_PROXY :=  {  accacc := Ledger_ι_Errors  }   . 
Global Instance AccAcc_Errors_ι_IS_EXT_MSG : AccessorAccessor Errors_ι_IS_EXT_MSG :=  {  accacc := Ledger_ι_Errors  }   . 
Global Instance AccAcc_Errors_ι_IS_NOT_VALIDATOR : AccessorAccessor Errors_ι_IS_NOT_VALIDATOR :=  {  accacc := Ledger_ι_Errors  }   . 
Global Instance AccAcc_Errors_ι_DEPOOL_IS_CLOSED : AccessorAccessor Errors_ι_DEPOOL_IS_CLOSED :=  {  accacc := Ledger_ι_Errors  }   . 
Global Instance AccAcc_Errors_ι_NO_SUCH_PARTICIPANT : AccessorAccessor Errors_ι_NO_SUCH_PARTICIPANT :=  {  accacc := Ledger_ι_Errors  }   . 
Global Instance AccAcc_Errors_ι_IS_NOT_DEPOOL : AccessorAccessor Errors_ι_IS_NOT_DEPOOL :=  {  accacc := Ledger_ι_Errors  }   . 
Global Instance AccAcc_Errors_ι_INVALID_ROUND_STEP : AccessorAccessor Errors_ι_INVALID_ROUND_STEP :=  {  accacc := Ledger_ι_Errors  }   . 
Global Instance AccAcc_Errors_ι_INVALID_QUERY_ID : AccessorAccessor Errors_ι_INVALID_QUERY_ID :=  {  accacc := Ledger_ι_Errors  }   . 
Global Instance AccAcc_Errors_ι_IS_NOT_ELECTOR : AccessorAccessor Errors_ι_IS_NOT_ELECTOR :=  {  accacc := Ledger_ι_Errors  }   . 
Global Instance AccAcc_Errors_ι_IS_NOT_OWNER_OR_SELF_CALL : AccessorAccessor Errors_ι_IS_NOT_OWNER_OR_SELF_CALL :=  {  accacc := Ledger_ι_Errors  }   . 
Global Instance AccAcc_Errors_ι_BAD_STAKES  : AccessorAccessor Errors_ι_BAD_STAKES :=  {  accacc := Ledger_ι_Errors  }   . 
Global Instance AccAcc_Errors_ι_CONSTRUCTOR_NO_PUBKEY : AccessorAccessor Errors_ι_CONSTRUCTOR_NO_PUBKEY :=  {  accacc := Ledger_ι_Errors  }   . 
Global Instance AccAcc_Errors_ι_VALIDATOR_IS_NOT_STD : AccessorAccessor Errors_ι_VALIDATOR_IS_NOT_STD :=  {  accacc := Ledger_ι_Errors  }   . 
Global Instance AccAcc_Errors_ι_BAD_PART_REWARD : AccessorAccessor Errors_ι_BAD_PART_REWARD :=  {  accacc := Ledger_ι_Errors  }   . 
Global Instance AccAcc_Errors_ι_BAD_MINIMUM_BALANCE : AccessorAccessor Errors_ι_BAD_MINIMUM_BALANCE :=  {  accacc := Ledger_ι_Errors  }   . 
Global Instance AccAcc_Errors_ι_BAD_PROXY_CODE : AccessorAccessor Errors_ι_BAD_PROXY_CODE :=  {  accacc := Ledger_ι_Errors  }   . 
Global Instance AccAcc_Errors_ι_NOT_WORKCHAIN0 : AccessorAccessor Errors_ι_NOT_WORKCHAIN0 :=  {  accacc := Ledger_ι_Errors  }   . 

Global Instance AccAcc_InternalErrors_ι_ERROR507 : AccessorAccessor InternalErrors_ι_ERROR507 :=  {  accacc := Ledger_ι_InternalErrors  }   . 
Global Instance AccAcc_InternalErrors_ι_ERROR508 : AccessorAccessor InternalErrors_ι_ERROR508 :=  {  accacc := Ledger_ι_InternalErrors  }   . 
Global Instance AccAcc_InternalErrors_ι_ERROR509 : AccessorAccessor InternalErrors_ι_ERROR509 :=  {  accacc := Ledger_ι_InternalErrors  }   . 
Global Instance AccAcc_InternalErrors_ι_ERROR511 : AccessorAccessor InternalErrors_ι_ERROR511 :=  {  accacc := Ledger_ι_InternalErrors  }   . 
Global Instance AccAcc_InternalErrors_ι_ERROR513 : AccessorAccessor InternalErrors_ι_ERROR513 :=  {  accacc := Ledger_ι_InternalErrors  }   . 
Global Instance AccAcc_InternalErrors_ι_ERROR516 : AccessorAccessor InternalErrors_ι_ERROR516 :=  {  accacc := Ledger_ι_InternalErrors  }   . 
Global Instance AccAcc_InternalErrors_ι_ERROR517 : AccessorAccessor InternalErrors_ι_ERROR517 :=  {  accacc := Ledger_ι_InternalErrors  }   . 
Global Instance AccAcc_InternalErrors_ι_ERROR518 : AccessorAccessor InternalErrors_ι_ERROR518 :=  {  accacc := Ledger_ι_InternalErrors  }   . 
Global Instance AccAcc_InternalErrors_ι_ERROR519 : AccessorAccessor InternalErrors_ι_ERROR519 :=  {  accacc := Ledger_ι_InternalErrors  }   . 
Global Instance AccAcc_InternalErrors_ι_ERROR521 : AccessorAccessor InternalErrors_ι_ERROR521 :=  {  accacc := Ledger_ι_InternalErrors  }   . 
Global Instance AccAcc_InternalErrors_ι_ERROR522 : AccessorAccessor InternalErrors_ι_ERROR522 :=  {  accacc := Ledger_ι_InternalErrors  }   . 
Global Instance AccAcc_InternalErrors_ι_ERROR523 : AccessorAccessor InternalErrors_ι_ERROR523 :=  {  accacc := Ledger_ι_InternalErrors  }   . 
Global Instance AccAcc_InternalErrors_ι_ERROR524 : AccessorAccessor InternalErrors_ι_ERROR524 :=  {  accacc := Ledger_ι_InternalErrors  }   . 
Global Instance AccAcc_InternalErrors_ι_ERROR525 : AccessorAccessor InternalErrors_ι_ERROR525 :=  {  accacc := Ledger_ι_InternalErrors  }   . 
Global Instance AccAcc_InternalErrors_ι_ERROR526 : AccessorAccessor InternalErrors_ι_ERROR526 :=  {  accacc := Ledger_ι_InternalErrors  }   . 
Global Instance AccAcc_InternalErrors_ι_ERROR527 : AccessorAccessor InternalErrors_ι_ERROR527 :=  {  accacc := Ledger_ι_InternalErrors  }   . 
Global Instance AccAcc_InternalErrors_ι_ERROR528 : AccessorAccessor InternalErrors_ι_ERROR528 :=  {  accacc := Ledger_ι_InternalErrors  }   . 

Global Instance AccAcc_DePoolLib_ι_PROXY_FEE : AccessorAccessor DePoolLib_ι_PROXY_FEE :=  {  accacc := Ledger_ι_DePoolLib  }   . 
Global Instance AccAcc_DePoolLib_ι_ELECTOR_FEE : AccessorAccessor DePoolLib_ι_ELECTOR_FEE :=  {  accacc := Ledger_ι_DePoolLib  }   . 
Global Instance AccAcc_DePoolLib_ι_MAX_UINT64 : AccessorAccessor DePoolLib_ι_MAX_UINT64 :=  {  accacc := Ledger_ι_DePoolLib  }   . 
Global Instance AccAcc_DePoolLib_ι_MAX_TIME : AccessorAccessor DePoolLib_ι_MAX_TIME :=  {  accacc := Ledger_ι_DePoolLib  }   . 
Global Instance AccAcc_DePoolLib_ι_ELECTOR_UNFREEZE_LAG : AccessorAccessor DePoolLib_ι_ELECTOR_UNFREEZE_LAG :=  {  accacc := Ledger_ι_DePoolLib  }   . 
Global Instance AccAcc_DePoolLib_ι_MIN_PROXY_BALANCE : AccessorAccessor DePoolLib_ι_MIN_PROXY_BALANCE :=  {  accacc := Ledger_ι_DePoolLib  }   . 
 
Global Instance AccAcc_DePoolProxyContract_ι_ERROR_IS_NOT_DEPOOL : AccessorAccessor DePoolProxyContract_ι_ERROR_IS_NOT_DEPOOL :=  {  accacc := Ledger_ι_DePoolProxyContract  }   . 
Global Instance AccAcc_DePoolProxyContract_ι_ERROR_BAD_BALANCE : AccessorAccessor DePoolProxyContract_ι_ERROR_BAD_BALANCE :=  {  accacc := Ledger_ι_DePoolProxyContract  }   . 
Global Instance AccAcc_DePoolProxyContract_ι_m_dePool : AccessorAccessor DePoolProxyContract_ι_m_dePool :=  {  accacc := Ledger_ι_DePoolProxyContract  }   . 

Global Instance AccAcc_RoundsBase_ι_m_rounds : AccessorAccessor RoundsBase_ι_m_rounds :=  {  accacc := Ledger_ι_RoundsBase }   . 
Global Instance AccAcc_RoundsBase_ι_m_roundQty : AccessorAccessor RoundsBase_ι_m_roundQty :=  {  accacc := Ledger_ι_RoundsBase  }   . 
 
Global Instance AccAcc_DePoolContract_ι_STAKE_FEE : AccessorAccessor DePoolContract_ι_STAKE_FEE :=  {  accacc := Ledger_ι_DePoolContract  }   . 
Global Instance AccAcc_DePoolContract_ι_RET_OR_REINV_FEE : AccessorAccessor  DePoolContract_ι_RET_OR_REINV_FEE :=  {  accacc := Ledger_ι_DePoolContract  }   . 
Global Instance AccAcc_DePoolContract_ι_MAX_MSGS_PER_TR : AccessorAccessor DePoolContract_ι_MAX_MSGS_PER_TR :=  {  accacc := Ledger_ι_DePoolContract  }   . 
Global Instance AccAcc_DePoolContract_ι_MAX_QTY_OF_OUT_ACTIONS : AccessorAccessor DePoolContract_ι_MAX_QTY_OF_OUT_ACTIONS :=  {  accacc := Ledger_ι_DePoolContract  }   . 
Global Instance AccAcc_DePoolContract_ι_VALUE_FOR_SELF_CALL : AccessorAccessor DePoolContract_ι_VALUE_FOR_SELF_CALL :=  {  accacc := Ledger_ι_DePoolContract  }   . 
Global Instance AccAcc_DePoolContract_ι_PROXY_CODE_HASH : AccessorAccessor DePoolContract_ι_PROXY_CODE_HASH :=  {  accacc := Ledger_ι_DePoolContract  }   . 
Global Instance AccAcc_DePoolContract_ι_STATUS_SUCCESS : AccessorAccessor DePoolContract_ι_STATUS_SUCCESS :=  {  accacc := Ledger_ι_DePoolContract  }   . 
Global Instance AccAcc_DePoolContract_ι_STATUS_STAKE_TOO_SMALL : AccessorAccessor DePoolContract_ι_STATUS_STAKE_TOO_SMALL :=  {  accacc := Ledger_ι_DePoolContract  }   . 
Global Instance AccAcc_DePoolContract_ι_STATUS_DEPOOL_CLOSED : AccessorAccessor DePoolContract_ι_STATUS_DEPOOL_CLOSED :=  {  accacc := Ledger_ι_DePoolContract  }   . 
Global Instance AccAcc_DePoolContract_ι_STATUS_NO_PARTICIPANT : AccessorAccessor DePoolContract_ι_STATUS_NO_PARTICIPANT :=  {  accacc := Ledger_ι_DePoolContract  }   . 
Global Instance AccAcc_DePoolContract_ι_STATUS_PARTICIPANT_HAVE_ALREADY_VESTING : AccessorAccessor DePoolContract_ι_STATUS_PARTICIPANT_HAVE_ALREADY_VESTING :=  {  accacc := Ledger_ι_DePoolContract  }   . 
Global Instance AccAcc_DePoolContract_ι_STATUS_WITHDRAWAL_PERIOD_GREATER_TOTAL_PERIOD : AccessorAccessor DePoolContract_ι_STATUS_WITHDRAWAL_PERIOD_GREATER_TOTAL_PERIOD :=  {  accacc := Ledger_ι_DePoolContract  }   . 
Global Instance AccAcc_DePoolContract_ι_STATUS_TOTAL_PERIOD_MORE_18YEARS : AccessorAccessor DePoolContract_ι_STATUS_TOTAL_PERIOD_MORE_18YEARS :=  {  accacc := Ledger_ι_DePoolContract  }   . 
Global Instance AccAcc_DePoolContract_ι_STATUS_WITHDRAWAL_PERIOD_IS_ZERO : AccessorAccessor DePoolContract_ι_STATUS_WITHDRAWAL_PERIOD_IS_ZERO :=  {  accacc := Ledger_ι_DePoolContract  }   . 
Global Instance AccAcc_DePoolContract_ι_STATUS_TOTAL_PERIOD_IS_NOT_DIVED_BY_WITHDRAWAL_PERIOD : AccessorAccessor DePoolContract_ι_STATUS_TOTAL_PERIOD_IS_NOT_DIVED_BY_WITHDRAWAL_PERIOD :=  {  accacc := Ledger_ι_DePoolContract  }   . 
Global Instance AccAcc_DePoolContract_ι_STATUS_PERIOD_PAYMENT_IS_ZERO : AccessorAccessor DePoolContract_ι_STATUS_PERIOD_PAYMENT_IS_ZERO :=  {  accacc := Ledger_ι_DePoolContract  }   . 
Global Instance AccAcc_DePoolContract_ι_STATUS_REMAINING_STAKE_LESS_THAN_MINIMAL : AccessorAccessor DePoolContract_ι_STATUS_REMAINING_STAKE_LESS_THAN_MINIMAL :=  {  accacc := Ledger_ι_DePoolContract  }   . 
Global Instance AccAcc_DePoolContract_ι_STATUS_PARTICIPANT_HAVE_ALREADY_LOCK : AccessorAccessor DePoolContract_ι_STATUS_PARTICIPANT_HAVE_ALREADY_LOCK :=  {  accacc := Ledger_ι_DePoolContract  }   . 
Global Instance AccAcc_DePoolContract_ι_STATUS_TRANSFER_AMOUNT_IS_TOO_BIG : AccessorAccessor DePoolContract_ι_STATUS_TRANSFER_AMOUNT_IS_TOO_BIG :=  {  accacc := Ledger_ι_DePoolContract  }   . 
Global Instance AccAcc_DePoolContract_ι_STATUS_TRANSFER_SELF : AccessorAccessor DePoolContract_ι_STATUS_TRANSFER_SELF :=  {  accacc := Ledger_ι_DePoolContract  }   . 
Global Instance AccAcc_DePoolContract_ι_STATUS_TRANSFER_TO_OR_FROM_VALIDATOR : AccessorAccessor DePoolContract_ι_STATUS_TRANSFER_TO_OR_FROM_VALIDATOR :=  {  accacc := Ledger_ι_DePoolContract  }   . 
Global Instance AccAcc_DePoolContract_ι_STATUS_FEE_TOO_SMALL : AccessorAccessor DePoolContract_ι_STATUS_FEE_TOO_SMALL :=  {  accacc := Ledger_ι_DePoolContract  }   . 
Global Instance AccAcc_DePoolContract_ι_STATUS_INVALID_ADDRESS : AccessorAccessor DePoolContract_ι_STATUS_INVALID_ADDRESS :=  {  accacc := Ledger_ι_DePoolContract  }   . 
Global Instance AccAcc_DePoolContract_ι_STATUS_INVALID_BENEFICIARY : AccessorAccessor DePoolContract_ι_STATUS_INVALID_BENEFICIARY :=  {  accacc := Ledger_ι_DePoolContract  }   . 
Global Instance AccAcc_DePoolContract_ι_STATUS_NO_ELECTION_ROUND : AccessorAccessor DePoolContract_ι_STATUS_NO_ELECTION_ROUND :=  {  accacc := Ledger_ι_DePoolContract  }   . 
Global Instance AccAcc_DePoolContract_ι_STATUS_INVALID_ELECTION_ID : AccessorAccessor DePoolContract_ι_STATUS_INVALID_ELECTION_ID :=  {  accacc := Ledger_ι_DePoolContract  }   . 
Global Instance AccAcc_DePoolContract_ι_m_poolClosed : AccessorAccessor DePoolContract_ι_m_poolClosed :=  {  accacc := Ledger_ι_DePoolContract  }   . 
Global Instance AccAcc_DePoolContract_ι_m_minStake : AccessorAccessor DePoolContract_ι_m_minStake :=  {  accacc := Ledger_ι_DePoolContract  }   . 
Global Instance AccAcc_DePoolContract_ι_m_validatorAssurance : AccessorAccessor DePoolContract_ι_m_validatorAssurance :=  {  accacc := Ledger_ι_DePoolContract  }   . 
Global Instance AccAcc_DePoolContract_ι_m_participantRewardFraction : AccessorAccessor DePoolContract_ι_m_participantRewardFraction :=  {  accacc := Ledger_ι_DePoolContract  }   . 

Global Instance AccAcc_DePoolContract_ι_m_validatorRewardFraction : AccessorAccessor DePoolContract_ι_m_validatorRewardFraction :=  {  accacc := Ledger_ι_DePoolContract  }   . 
Global Instance AccAcc_DePoolContract_ι_m_balanceThreshold : AccessorAccessor DePoolContract_ι_m_balanceThreshold :=  {  accacc := Ledger_ι_DePoolContract  }   . 
Global Instance AccAcc_DePoolContract_ι_CRITICAL_THRESHOLD : AccessorAccessor DePoolContract_ι_CRITICAL_THRESHOLD :=  {  accacc := Ledger_ι_DePoolContract  }   . 


Global Instance AccAcc_VMState_ι_pubkey : AccessorAccessor VMState_ι_pubkey :=  {  accacc := Ledger_ι_VMState  }   . 
Global Instance AccAcc_VMState_ι_msg_pubkey : AccessorAccessor VMState_ι_msg_pubkey :=  {  accacc := Ledger_ι_VMState  }   . 
Global Instance AccAcc_VMState_ι_now : AccessorAccessor VMState_ι_now :=  {  accacc := Ledger_ι_VMState  }   . 
Global Instance AccAcc_VMState_ι_logstr : AccessorAccessor VMState_ι_logstr :=  {  accacc := Ledger_ι_VMState  }   . 
Global Instance AccAcc_VMState_ι_balance : AccessorAccessor VMState_ι_balance :=  {  accacc := Ledger_ι_VMState  }   . 
Global Instance AccAcc_VMState_ι_address : AccessorAccessor VMState_ι_address :=  {  accacc := Ledger_ι_VMState  }   . 
Global Instance AccAcc_VMState_ι_ltime : AccessorAccessor VMState_ι_ltime :=  {  accacc := Ledger_ι_VMState  }   . 
Global Instance AccAcc_VMState_ι_code : AccessorAccessor VMState_ι_code :=  {  accacc := Ledger_ι_VMState  }   . 
Global Instance AccAcc_VMState_ι_events : AccessorAccessor VMState_ι_events :=  {  accacc := Ledger_ι_VMState  }   . 
Global Instance AccAcc_VMState_ι_savedDePoolContract : AccessorAccessor VMState_ι_savedDePoolContracts :=  {  accacc := Ledger_ι_VMState  }   . 
Global Instance AccAcc_VMState_ι_msg_sender : AccessorAccessor VMState_ι_msg_sender :=  {  accacc := Ledger_ι_VMState  }   . 
Global Instance AccAcc_VMState_ι_msg_value : AccessorAccessor VMState_ι_msg_value :=  {  accacc := Ledger_ι_VMState  }   . 
Global Instance AccAcc_VMState_ι_messages : AccessorAccessor VMState_ι_messages :=  {  accacc := Ledger_ι_VMState  }   .
Global Instance AccAcc_VMState_ι_msg_data : AccessorAccessor VMState_ι_msg_data :=  {  accacc := Ledger_ι_VMState  }   .
Global Instance AccAcc_VMState_ι_transactions : AccessorAccessor VMState_ι_transactions :=  {  accacc := Ledger_ι_VMState  }   .

Global Instance AccAcc_LocalState_ι__addStakes_Л_participant  : AccessorAccessor LocalState_ι__addStakes_Л_participant :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι__addStakes_Л_round   : AccessorAccessor LocalState_ι__addStakes_Л_round :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι__addStakes_Л_sv  : AccessorAccessor LocalState_ι__addStakes_Л_sv :=  {  accacc := Ledger_ι_LocalState  }   . 

Global Instance AccAcc_LocalState_ι__returnOrReinvestForParticipant_Л_attachedValue  : AccessorAccessor LocalState_ι__returnOrReinvestForParticipant_Л_attachedValue :=  {  accacc := Ledger_ι_LocalState  }   .  
Global Instance AccAcc_LocalState_ι__returnOrReinvestForParticipant_Л_newLock  : AccessorAccessor LocalState_ι__returnOrReinvestForParticipant_Л_newLock :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι__returnOrReinvestForParticipant_Л_newStake  : AccessorAccessor LocalState_ι__returnOrReinvestForParticipant_Л_newStake :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι__returnOrReinvestForParticipant_Л_newVesting   : AccessorAccessor LocalState_ι__returnOrReinvestForParticipant_Л_newVesting :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι__returnOrReinvestForParticipant_Л_participant  : AccessorAccessor LocalState_ι__returnOrReinvestForParticipant_Л_participant :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι__returnOrReinvestForParticipant_Л_reward  : AccessorAccessor LocalState_ι__returnOrReinvestForParticipant_Л_reward :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι__returnOrReinvestForParticipant_Л_round0  : AccessorAccessor LocalState_ι__returnOrReinvestForParticipant_Л_round0 :=  {  accacc := Ledger_ι_LocalState  }   . 

Global Instance AccAcc_LocalState_ι__returnOrReinvestForParticipant_Л_round2  : AccessorAccessor LocalState_ι__returnOrReinvestForParticipant_Л_round2 :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds  : AccessorAccessor LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι__returnOrReinvestForParticipant_Л_params  : AccessorAccessor LocalState_ι__returnOrReinvestForParticipant_Л_params :=  {  accacc := Ledger_ι_LocalState  }   . 


Global Instance AccAcc_LocalState_ι__returnOrReinvest_Л_chunkSize  : AccessorAccessor LocalState_ι__returnOrReinvest_Л_chunkSize :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι__returnOrReinvest_Л_round2  : AccessorAccessor LocalState_ι__returnOrReinvest_Л_round2 :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι__returnOrReinvest_Л_round0   : AccessorAccessor LocalState_ι__returnOrReinvest_Л_round0 :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι__returnOrReinvest_Л_startIndex  : AccessorAccessor LocalState_ι__returnOrReinvest_Л_startIndex :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι_addVestingOrLock_Л_participant  : AccessorAccessor LocalState_ι_addVestingOrLock_Л_participant :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι_addVestingOrLock_Л_l  : AccessorAccessor LocalState_ι_addVestingOrLock_Л_l :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι_addVestingOrLock_Л_v  : AccessorAccessor LocalState_ι_addVestingOrLock_Л_v :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι_completeRound_Л_i  : AccessorAccessor LocalState_ι_completeRound_Л_i :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι_completeRound_Л_msgQty  : AccessorAccessor LocalState_ι_completeRound_Л_msgQty :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι_completeRound_Л_restParticipant   : AccessorAccessor LocalState_ι_completeRound_Л_restParticipant :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι_cutWithdrawalValueAndActivateStake_Л_p  : AccessorAccessor LocalState_ι_cutWithdrawalValueAndActivateStake_Л_p :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι_cutWithdrawalValueAndActivateStake_Л_withdrawal  : AccessorAccessor LocalState_ι_cutWithdrawalValueAndActivateStake_Л_withdrawal :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι_getRounds_Л_pair  : AccessorAccessor LocalState_ι_getRounds_Л_pair :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι_getRounds_Л_rounds  : AccessorAccessor LocalState_ι_getRounds_Л_rounds :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι_onFailToRecoverStake_Л_round  : AccessorAccessor LocalState_ι_onFailToRecoverStake_Л_round :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι_onSuccessToRecoverStake_Л_round  : AccessorAccessor LocalState_ι_onSuccessToRecoverStake_Л_round :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι_terminator_Л_round1  : AccessorAccessor LocalState_ι_terminator_Л_round1 :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι_transferStakeInOneRound_Л_deltaDestinationStake  : AccessorAccessor LocalState_ι_transferStakeInOneRound_Л_deltaDestinationStake :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι_transferStakeInOneRound_Л_destinationParticipant  : AccessorAccessor LocalState_ι_transferStakeInOneRound_Л_destinationParticipant :=  {  accacc := Ledger_ι_LocalState }   . 
Global Instance AccAcc_LocalState_ι_transferStakeInOneRound_Л_newSourceStake  : AccessorAccessor LocalState_ι_transferStakeInOneRound_Л_newSourceStake :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι_transferStakeInOneRound_Л_round  : AccessorAccessor LocalState_ι_transferStakeInOneRound_Л_round :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι_transferStakeInOneRound_Л_sourceParticipant  : AccessorAccessor LocalState_ι_transferStakeInOneRound_Л_sourceParticipant :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι_transferStakeInOneRound_Л_sourceStake  : AccessorAccessor LocalState_ι_transferStakeInOneRound_Л_sourceStake :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι_transferStake_Л_destParticipant  : AccessorAccessor LocalState_ι_transferStake_Л_destParticipant :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι_transferStake_Л_pair   : AccessorAccessor LocalState_ι_transferStake_Л_pair :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι_transferStake_Л_rounds  : AccessorAccessor LocalState_ι_transferStake_Л_rounds :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι_transferStake_Л_srcParticipant  : AccessorAccessor LocalState_ι_transferStake_Л_srcParticipant :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι_transferStake_Л_totalSrcStake  : AccessorAccessor LocalState_ι_transferStake_Л_totalSrcStake :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι_transferStake_Л_transferred  : AccessorAccessor LocalState_ι_transferStake_Л_transferred :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι_updateRound2_Л_round2  : AccessorAccessor LocalState_ι_updateRound2_Л_round2 :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι_updateRounds_Л_round0  : AccessorAccessor LocalState_ι_updateRounds_Л_round0 :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι_updateRounds_Л_round1  : AccessorAccessor LocalState_ι_updateRounds_Л_round1 :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι_updateRounds_Л_round2  : AccessorAccessor LocalState_ι_updateRounds_Л_round2 :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι_withdrawStakeInPoolingRound_Л_participant  : AccessorAccessor LocalState_ι_withdrawStakeInPoolingRound_Л_participant :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι_withdrawStakeInPoolingRound_Л_round  : AccessorAccessor LocalState_ι_withdrawStakeInPoolingRound_Л_round :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι_withdrawStakeInPoolingRound_Л_sv  : AccessorAccessor LocalState_ι_withdrawStakeInPoolingRound_Л_sv :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι_withdrawStakeInPoolingRound_Л_targetAmount  : AccessorAccessor LocalState_ι_withdrawStakeInPoolingRound_Л_targetAmount := {  accacc := Ledger_ι_LocalState  } .



(* 1 *)
(*embeddedType for all Accessors *)


Unset Implicit Arguments.
Set Strict Implicit.
Unset Contextual Implicit.
Unset Maximal Implicit Insertion.

Definition projEmbed_Accessor {U T}{f: T -> U}`{s: Struct T}`{a: @Accessor T U s f}: T -> U := f.
Definition injEmbed_Accessor {U T}{f: T -> U}`{s: Struct T}`{a: @Accessor T U s f} (x: U) (t: T): T := {$ t with f := x $}.

 
 Definition T1 := DebugDePool . 
 Definition T2 := ValidatorBase . 
 Definition T3 := ProxyBase . 
 Definition T4 := True . 
 Definition T5 := ParticipantBase . 
 Definition T6 := DePoolHelper . 
 Definition T7 := Errors . 
 Definition T8 := InternalErrors . 
 Definition T9 := DePoolLib . 
 Definition T10 := DePoolProxyContract .  
 Definition T11 := RoundsBase . 
 Definition T12 := DePoolContract . 
 Definition T13 := True . 
 Definition T14 := True . 
 Definition T15 := TestElector . 
 Definition T16 := VMState . 
 Definition T17 := LocalState . 
 
 
 Definition projEmbed_T1 : Ledger -> T1 := projEmbed_Accessor . 
 Definition injEmbed_T1 : T1 -> Ledger -> Ledger := injEmbed_Accessor . 
 
 Lemma projinj_T1 : forall ( t : T1 ) ( s : Ledger ) , 
 projEmbed_T1 ( injEmbed_T1 t s ) = t . 
 Proof.
 intros. compute. auto.
Qed. 
 
 Lemma injproj_T1 : forall ( s : Ledger ) , injEmbed_T1 ( projEmbed_T1 s ) s = s . Proof.
 intros. destruct s. compute. auto.
Qed. 
 Lemma injinj_T1 : forall ( t1 t2 : T1 ) ( s : Ledger ) , 
 injEmbed_T1 t1 ( injEmbed_T1 t2 s) = 
 injEmbed_T1 t1 s . 
 Proof.
 intros. destruct s. compute. auto.
Qed. 
 
 Instance embeddedT1 : EmbeddedType Ledger T1 := 
 {
 projEmbed := projEmbed_T1 ; 
 injEmbed := injEmbed_T1 ; 
 projinj := projinj_T1 ; 
 injproj := injproj_T1 ; 
 injinj  := injinj_T1 ; 
 } . 
 
 
 Definition projEmbed_T2 : Ledger -> T2 := projEmbed_Accessor . 
 Definition injEmbed_T2 : T2 -> Ledger -> Ledger := injEmbed_Accessor . 
 
 Lemma projinj_T2 : forall ( t : T2 ) ( s : Ledger ) , 
 projEmbed_T2 ( injEmbed_T2 t s ) = t . 
 Proof.
 intros. compute. auto.
Qed. 
 
 Lemma injproj_T2 : forall ( s : Ledger ) , injEmbed_T2 ( projEmbed_T2 s ) s = s . Proof.
 intros. destruct s. compute. auto.
Qed. 
 Lemma injinj_T2 : forall ( t1 t2 : T2 ) ( s : Ledger ) , 
 injEmbed_T2 t1 ( injEmbed_T2 t2 s) = 
 injEmbed_T2 t1 s . 
 Proof.
 intros. destruct s. compute. auto.
Qed. 
 
 Instance embeddedT2 : EmbeddedType Ledger T2 := 
 {
 projEmbed := projEmbed_T2 ; 
 injEmbed := injEmbed_T2 ; 
 projinj := projinj_T2 ; 
 injproj := injproj_T2 ; 
 injinj  := injinj_T2 ; 
 } . 
 
 
 
 Definition projEmbed_T3 : Ledger -> T3 := projEmbed_Accessor . 
 Definition injEmbed_T3 : T3 -> Ledger -> Ledger := injEmbed_Accessor . 
 
 Lemma projinj_T3 : forall ( t : T3 ) ( s : Ledger ) , 
 projEmbed_T3 ( injEmbed_T3 t s ) = t . 
 Proof.
 intros. compute. auto.
Qed. 
 
 Lemma injproj_T3 : forall ( s : Ledger ) , injEmbed_T3 ( projEmbed_T3 s ) s = s . Proof.
 intros. destruct s. compute. auto.
Qed. 
 Lemma injinj_T3 : forall ( t1 t2 : T3 ) ( s : Ledger ) , 
 injEmbed_T3 t1 ( injEmbed_T3 t2 s) = 
 injEmbed_T3 t1 s . 
 Proof.
 intros. destruct s. compute. auto.
Qed. 
 
 Instance embeddedT3 : EmbeddedType Ledger T3 := 
 {
 projEmbed := projEmbed_T3 ; 
 injEmbed := injEmbed_T3 ; 
 projinj := projinj_T3 ; 
 injproj := injproj_T3 ; 
 injinj  := injinj_T3 ; 
 } . 
 
 
 
 Definition projEmbed_T4 : Ledger -> T4 := projEmbed_Accessor (a:=Acc_Ledger_ι_ConfigParamsBase). 
 Definition injEmbed_T4 : T4 -> Ledger -> Ledger := injEmbed_Accessor (a:=Acc_Ledger_ι_ConfigParamsBase). 
 
 Lemma projinj_T4 : forall ( t : T4 ) ( s : Ledger ) , 
 projEmbed_T4 ( injEmbed_T4 t s ) = t . 
 Proof.
 intros. compute. auto.
Qed. 
 
 Lemma injproj_T4 : forall ( s : Ledger ) , injEmbed_T4 ( projEmbed_T4 s ) s = s . Proof.
 intros. destruct s. compute. auto.
Qed. 
 Lemma injinj_T4 : forall ( t1 t2 : T4 ) ( s : Ledger ) , 
 injEmbed_T4 t1 ( injEmbed_T4 t2 s) = 
 injEmbed_T4 t1 s . 
 Proof.
 intros. destruct s. compute. auto.
Qed. 
 
 Instance embeddedT4 : EmbeddedType Ledger T4 := 
 {
 projEmbed := projEmbed_T4 ; 
 injEmbed := injEmbed_T4 ; 
 projinj := projinj_T4 ; 
 injproj := injproj_T4 ; 
 injinj  := injinj_T4 ; 
 } . 
 
 
 
 Definition projEmbed_T5 : Ledger -> T5 := projEmbed_Accessor . 
 Definition injEmbed_T5 : T5 -> Ledger -> Ledger := injEmbed_Accessor . 
 
 Lemma projinj_T5 : forall ( t : T5 ) ( s : Ledger ) , 
 projEmbed_T5 ( injEmbed_T5 t s ) = t . 
 Proof.
 intros. compute. auto.
Qed. 
 
 Lemma injproj_T5 : forall ( s : Ledger ) , injEmbed_T5 ( projEmbed_T5 s ) s = s . Proof.
 intros. destruct s. compute. auto.
Qed. 
 Lemma injinj_T5 : forall ( t1 t2 : T5 ) ( s : Ledger ) , 
 injEmbed_T5 t1 ( injEmbed_T5 t2 s) = 
 injEmbed_T5 t1 s . 
 Proof.
 intros. destruct s. compute. auto.
Qed. 
 
 Instance embeddedT5 : EmbeddedType Ledger T5 := 
 {
 projEmbed := projEmbed_T5 ; 
 injEmbed := injEmbed_T5 ; 
 projinj := projinj_T5 ; 
 injproj := injproj_T5 ; 
 injinj  := injinj_T5 ; 
 } . 
 
 
 
 Definition projEmbed_T6 : Ledger -> T6 := projEmbed_Accessor . 
 Definition injEmbed_T6 : T6 -> Ledger -> Ledger := injEmbed_Accessor . 
 
 Lemma projinj_T6 : forall ( t : T6 ) ( s : Ledger ) , 
 projEmbed_T6 ( injEmbed_T6 t s ) = t . 
 Proof.
 intros. compute. auto.
Qed. 
 
 Lemma injproj_T6 : forall ( s : Ledger ) , injEmbed_T6 ( projEmbed_T6 s ) s = s . Proof.
 intros. destruct s. compute. auto.
Qed. 
 Lemma injinj_T6 : forall ( t1 t2 : T6 ) ( s : Ledger ) , 
 injEmbed_T6 t1 ( injEmbed_T6 t2 s) = 
 injEmbed_T6 t1 s . 
 Proof.
 intros. destruct s. compute. auto.
Qed. 
 
 Instance embeddedT6 : EmbeddedType Ledger T6 := 
 {
 projEmbed := projEmbed_T6 ; 
 injEmbed := injEmbed_T6 ; 
 projinj := projinj_T6 ; 
 injproj := injproj_T6 ; 
 injinj  := injinj_T6 ; 
 } . 
 
 
 
 Definition projEmbed_T7 : Ledger -> T7 := projEmbed_Accessor . 
 Definition injEmbed_T7 : T7 -> Ledger -> Ledger := injEmbed_Accessor . 
 
 Lemma projinj_T7 : forall ( t : T7 ) ( s : Ledger ) , 
 projEmbed_T7 ( injEmbed_T7 t s ) = t . 
 Proof.
 intros. compute. auto.
Qed. 
 
 Lemma injproj_T7 : forall ( s : Ledger ) , injEmbed_T7 ( projEmbed_T7 s ) s = s . Proof.
 intros. destruct s. compute. auto.
Qed. 
 Lemma injinj_T7 : forall ( t1 t2 : T7 ) ( s : Ledger ) , 
 injEmbed_T7 t1 ( injEmbed_T7 t2 s) = 
 injEmbed_T7 t1 s . 
 Proof.
 intros. destruct s. compute. auto.
Qed. 
 
 Instance embeddedT7 : EmbeddedType Ledger T7 := 
 {
 projEmbed := projEmbed_T7 ; 
 injEmbed := injEmbed_T7 ; 
 projinj := projinj_T7 ; 
 injproj := injproj_T7 ; 
 injinj  := injinj_T7 ; 
 } . 
 
 
 
 Definition projEmbed_T8 : Ledger -> T8 := projEmbed_Accessor . 
 Definition injEmbed_T8 : T8 -> Ledger -> Ledger := injEmbed_Accessor . 
 
 Lemma projinj_T8 : forall ( t : T8 ) ( s : Ledger ) , 
 projEmbed_T8 ( injEmbed_T8 t s ) = t . 
 Proof.
 intros. compute. auto.
Qed. 
 
 Lemma injproj_T8 : forall ( s : Ledger ) , injEmbed_T8 ( projEmbed_T8 s ) s = s . Proof.
 intros. destruct s. compute. auto.
Qed. 
 Lemma injinj_T8 : forall ( t1 t2 : T8 ) ( s : Ledger ) , 
 injEmbed_T8 t1 ( injEmbed_T8 t2 s) = 
 injEmbed_T8 t1 s . 
 Proof.
 intros. destruct s. compute. auto.
Qed. 
 
 Instance embeddedT8 : EmbeddedType Ledger T8 := 
 {
 projEmbed := projEmbed_T8 ; 
 injEmbed := injEmbed_T8 ; 
 projinj := projinj_T8 ; 
 injproj := injproj_T8 ; 
 injinj  := injinj_T8 ; 
 } . 
 
 
 
 Definition projEmbed_T9 : Ledger -> T9 := projEmbed_Accessor . 
 Definition injEmbed_T9 : T9 -> Ledger -> Ledger := injEmbed_Accessor . 
 
 Lemma projinj_T9 : forall ( t : T9 ) ( s : Ledger ) , 
 projEmbed_T9 ( injEmbed_T9 t s ) = t . 
 Proof.
 intros. compute. auto.
Qed. 
 
 Lemma injproj_T9 : forall ( s : Ledger ) , injEmbed_T9 ( projEmbed_T9 s ) s = s . Proof.
 intros. destruct s. compute. auto.
Qed. 
 Lemma injinj_T9 : forall ( t1 t2 : T9 ) ( s : Ledger ) , 
 injEmbed_T9 t1 ( injEmbed_T9 t2 s) = 
 injEmbed_T9 t1 s . 
 Proof.
 intros. destruct s. compute. auto.
Qed. 
 
 Instance embeddedT9 : EmbeddedType Ledger T9 := 
 {
 projEmbed := projEmbed_T9 ; 
 injEmbed := injEmbed_T9 ; 
 projinj := projinj_T9 ; 
 injproj := injproj_T9 ; 
 injinj  := injinj_T9 ; 
 } . 
 
 
 
 Definition projEmbed_T10 : Ledger -> T10 := projEmbed_Accessor . 
 Definition injEmbed_T10 : T10 -> Ledger -> Ledger := injEmbed_Accessor . 
 
 Lemma projinj_T10 : forall ( t : T10 ) ( s : Ledger ) , 
 projEmbed_T10 ( injEmbed_T10 t s ) = t . 
 Proof.
 intros. compute. auto.
Qed. 
 
 Lemma injproj_T10 : forall ( s : Ledger ) , injEmbed_T10 ( projEmbed_T10 s ) s = s . Proof.
 intros. destruct s. compute. auto.
Qed. 
 Lemma injinj_T10 : forall ( t1 t2 : T10 ) ( s : Ledger ) , 
 injEmbed_T10 t1 ( injEmbed_T10 t2 s) = 
 injEmbed_T10 t1 s . 
 Proof.
 intros. destruct s. compute. auto.
Qed. 
 
 Instance embeddedT10 : EmbeddedType Ledger T10 := 
 {
 projEmbed := projEmbed_T10 ; 
 injEmbed := injEmbed_T10 ; 
 projinj := projinj_T10 ; 
 injproj := injproj_T10 ; 
 injinj  := injinj_T10 ; 
 } . 
 
 
 
 Definition projEmbed_T11 : Ledger -> T11 := projEmbed_Accessor . 
 Definition injEmbed_T11 : T11 -> Ledger -> Ledger := injEmbed_Accessor . 
 
 Lemma projinj_T11 : forall ( t : T11 ) ( s : Ledger ) , 
 projEmbed_T11 ( injEmbed_T11 t s ) = t . 
 Proof.
 intros. compute. auto.
Qed. 
 
 Lemma injproj_T11 : forall ( s : Ledger ) , injEmbed_T11 ( projEmbed_T11 s ) s = s . Proof.
 intros. destruct s. compute. auto.
Qed. 
 Lemma injinj_T11 : forall ( t1 t2 : T11 ) ( s : Ledger ) , 
 injEmbed_T11 t1 ( injEmbed_T11 t2 s) = 
 injEmbed_T11 t1 s . 
 Proof.
 intros. destruct s. compute. auto.
Qed. 
 
 Instance embeddedT11 : EmbeddedType Ledger T11 := 
 {
 projEmbed := projEmbed_T11 ; 
 injEmbed := injEmbed_T11 ; 
 projinj := projinj_T11 ; 
 injproj := injproj_T11 ; 
 injinj  := injinj_T11 ; 
 } . 
 
 
 
 Definition projEmbed_T12 : Ledger -> T12 := projEmbed_Accessor . 
 Definition injEmbed_T12 : T12 -> Ledger -> Ledger := injEmbed_Accessor . 
 
 Lemma projinj_T12 : forall ( t : T12 ) ( s : Ledger ) , 
 projEmbed_T12 ( injEmbed_T12 t s ) = t . 
 Proof.
 intros. compute. auto.
Qed. 
 
 Lemma injproj_T12 : forall ( s : Ledger ) , injEmbed_T12 ( projEmbed_T12 s ) s = s . Proof.
 intros. destruct s. compute. auto.
Qed. 
 Lemma injinj_T12 : forall ( t1 t2 : T12 ) ( s : Ledger ) , 
 injEmbed_T12 t1 ( injEmbed_T12 t2 s) = 
 injEmbed_T12 t1 s . 
 Proof.
 intros. destruct s. compute. auto.
Qed. 
 
 Instance embeddedT12 : EmbeddedType Ledger T12 := 
 {
 projEmbed := projEmbed_T12 ; 
 injEmbed := injEmbed_T12 ; 
 projinj := projinj_T12 ; 
 injproj := injproj_T12 ; 
 injinj  := injinj_T12 ; 
 } . 
 
 
 
 Definition projEmbed_T13 : Ledger -> T13 := projEmbed_Accessor (a:=Acc_Ledger_ι_DePool). 
 Definition injEmbed_T13 : T13 -> Ledger -> Ledger := injEmbed_Accessor (a:=Acc_Ledger_ι_DePool). 
 
 Lemma projinj_T13 : forall ( t : T13 ) ( s : Ledger ) , 
 projEmbed_T13 ( injEmbed_T13 t s ) = t . 
 Proof.
 intros. compute. auto.
Qed. 
 
 Lemma injproj_T13 : forall ( s : Ledger ) , injEmbed_T13 ( projEmbed_T13 s ) s = s . Proof.
 intros. destruct s. compute. auto.
Qed. 
 Lemma injinj_T13 : forall ( t1 t2 : T13 ) ( s : Ledger ) , 
 injEmbed_T13 t1 ( injEmbed_T13 t2 s) = 
 injEmbed_T13 t1 s . 
 Proof.
 intros. destruct s. compute. auto.
Qed. 
 
 Instance embeddedT13 : EmbeddedType Ledger T13 := 
 {
 projEmbed := projEmbed_T13 ; 
 injEmbed := injEmbed_T13 ; 
 projinj := projinj_T13 ; 
 injproj := injproj_T13 ; 
 injinj  := injinj_T13 ; 
 } . 
 
 
 
 Definition projEmbed_T14 : Ledger -> T14 := projEmbed_Accessor (a:=Acc_Ledger_ι_Participant). 
 Definition injEmbed_T14 : T14 -> Ledger -> Ledger := injEmbed_Accessor (a:=Acc_Ledger_ι_Participant). 
 
 Lemma projinj_T14 : forall ( t : T14 ) ( s : Ledger ) , 
 projEmbed_T14 ( injEmbed_T14 t s ) = t . 
 Proof.
 intros. compute. auto.
Qed. 
 
 Lemma injproj_T14 : forall ( s : Ledger ) , injEmbed_T14 ( projEmbed_T14 s ) s = s . Proof.
 intros. destruct s. compute. auto.
Qed. 
 Lemma injinj_T14 : forall ( t1 t2 : T14 ) ( s : Ledger ) , 
 injEmbed_T14 t1 ( injEmbed_T14 t2 s) = 
 injEmbed_T14 t1 s . 
 Proof.
 intros. destruct s. compute. auto.
Qed. 
 
 Instance embeddedT14 : EmbeddedType Ledger T14 := 
 {
 projEmbed := projEmbed_T14 ; 
 injEmbed := injEmbed_T14 ; 
 projinj := projinj_T14 ; 
 injproj := injproj_T14 ; 
 injinj  := injinj_T14 ; 
 } . 
 
 
 
 Definition projEmbed_T15 : Ledger -> T15 := projEmbed_Accessor . 
 Definition injEmbed_T15 : T15 -> Ledger -> Ledger := injEmbed_Accessor . 
 
 Lemma projinj_T15 : forall ( t : T15 ) ( s : Ledger ) , 
 projEmbed_T15 ( injEmbed_T15 t s ) = t . 
 Proof.
 intros. compute. auto.
Qed. 
 
 Lemma injproj_T15 : forall ( s : Ledger ) , injEmbed_T15 ( projEmbed_T15 s ) s = s . Proof.
 intros. destruct s. compute. auto.
Qed. 
 Lemma injinj_T15 : forall ( t1 t2 : T15 ) ( s : Ledger ) , 
 injEmbed_T15 t1 ( injEmbed_T15 t2 s) = 
 injEmbed_T15 t1 s . 
 Proof.
 intros. destruct s. compute. auto.
Qed. 
 
 Instance embeddedT15 : EmbeddedType Ledger T15 := 
 {
 projEmbed := projEmbed_T15 ; 
 injEmbed := injEmbed_T15 ; 
 projinj := projinj_T15 ; 
 injproj := injproj_T15 ; 
 injinj  := injinj_T15 ; 
 } . 
 
 
 
 Definition projEmbed_T16 : Ledger -> T16 := projEmbed_Accessor . 
 Definition injEmbed_T16 : T16 -> Ledger -> Ledger := injEmbed_Accessor . 
 
 Lemma projinj_T16 : forall ( t : T16 ) ( s : Ledger ) , 
 projEmbed_T16 ( injEmbed_T16 t s ) = t . 
 Proof.
 intros. compute. auto.
Qed. 
 
 Lemma injproj_T16 : forall ( s : Ledger ) , injEmbed_T16 ( projEmbed_T16 s ) s = s . Proof.
 intros. destruct s. compute. auto.
Qed. 
 Lemma injinj_T16 : forall ( t1 t2 : T16 ) ( s : Ledger ) , 
 injEmbed_T16 t1 ( injEmbed_T16 t2 s) = 
 injEmbed_T16 t1 s . 
 Proof.
 intros. destruct s. compute. auto.
Qed. 
 
 Instance embeddedT16 : EmbeddedType Ledger T16 := 
 {
 projEmbed := projEmbed_T16 ; 
 injEmbed := injEmbed_T16 ; 
 projinj := projinj_T16 ; 
 injproj := injproj_T16 ; 
 injinj  := injinj_T16 ; 
 } . 
 
 
 
 Definition projEmbed_T17 : Ledger -> T17 := projEmbed_Accessor . 
 Definition injEmbed_T17 : T17 -> Ledger -> Ledger := injEmbed_Accessor . 
 
 Lemma projinj_T17 : forall ( t : T17 ) ( s : Ledger ) , 
 projEmbed_T17 ( injEmbed_T17 t s ) = t . 
 Proof.
 intros. compute. auto.
Qed. 
 
 Lemma injproj_T17 : forall ( s : Ledger ) , injEmbed_T17 ( projEmbed_T17 s ) s = s . Proof.
 intros. destruct s. compute. auto.
Qed. 
 Lemma injinj_T17 : forall ( t1 t2 : T17 ) ( s : Ledger ) , 
 injEmbed_T17 t1 ( injEmbed_T17 t2 s) = 
 injEmbed_T17 t1 s . 
 Proof.
 intros. destruct s. compute. auto.
Qed. 
 
 Instance embeddedT17 : EmbeddedType Ledger T17 := 
 {
 projEmbed := projEmbed_T17 ; 
 injEmbed := injEmbed_T17 ; 
 projinj := projinj_T17 ; 
 injproj := injproj_T17 ; 
 injinj  := injinj_T17 ; 
 } . 
 
Lemma injcommute_T1_T2: forall  (u:T2) (t:T1)  (s:Ledger), 
      ( injEmbed u ( injEmbed t s ) ) = ( injEmbed t ( injEmbed u s ) ).
Proof.
 intros. compute. auto.
Qed.

Instance InjectCommutableStates_T1_T2: 
         @InjectCommutableStates Ledger T1 T2 
               := 
{
  injcommute := injcommute_T1_T2
}.
Definition embeddedProduct_T1_T2 := 
           @embeddedProduct Ledger T1 T2 
                 InjectCommutableStates_T1_T2.
Existing Instance embeddedProduct_T1_T2.
 
Lemma injcommute_T1xT2_T3: 
               forall ( u : T3 ) ( t :  T1 * T2  ) 
                      ( s:Ledger ), 
      ( injEmbed u ( injEmbed t s ) ) = ( injEmbed t ( injEmbed u s ) ).
Proof.
 intros. compute. auto.
Qed.

Instance InjectCommutableStates_T1xT2_T3 : 
@InjectCommutableStates Ledger (  T1 * T2  ) T3 := 
{
  injcommute := injcommute_T1xT2_T3 
}.

Definition embeddedProduct_T1xT2_T3 := 
           @embeddedProduct Ledger (  T1 * T2  ) T3
  
           InjectCommutableStates_T1xT2_T3.

Existing Instance embeddedProduct_T1xT2_T3 .
 
Lemma injcommute_T1xT2xT3_T4: 
               forall ( u : T4 ) ( t :  T1 * T2 * T3  ) 
                      ( s:Ledger ), 
      ( injEmbed (EmbeddedType:=embeddedT4) u ( injEmbed t s ) ) = ( injEmbed t ( injEmbed (EmbeddedType:=embeddedT4) u s ) ).
Proof.
 intros. compute. auto.
Qed.

(* Print InjectCommutableStates. *)

Instance InjectCommutableStates_T1xT2xT3_T4 : 
@InjectCommutableStates Ledger (  T1 * T2 * T3  ) T4 := 
{
(* 	embeddedTypeT := ; *)
	embeddedTypeU := embeddedT4;
  injcommute := injcommute_T1xT2xT3_T4 
}.

Definition embeddedProduct_T1xT2xT3_T4 := 
           @embeddedProduct Ledger (  T1 * T2 * T3  ) T4
  
           InjectCommutableStates_T1xT2xT3_T4.

Existing Instance embeddedProduct_T1xT2xT3_T4 .
 
Lemma injcommute_T1xT2xT3xT4_T5: 
               forall ( u : T5 ) ( t :  T1 * T2 * T3 * T4  ) 
                      ( s:Ledger ), 
      ( injEmbed u ( injEmbed t s ) ) = ( injEmbed t ( injEmbed u s ) ).
Proof.
 intros. compute. auto.
Qed.

Instance InjectCommutableStates_T1xT2xT3xT4_T5 : 
@InjectCommutableStates Ledger (  T1 * T2 * T3 * T4  ) T5 := 
{
  injcommute := injcommute_T1xT2xT3xT4_T5 
}.

Definition embeddedProduct_T1xT2xT3xT4_T5 := 
           @embeddedProduct Ledger (  T1 * T2 * T3 * T4  ) T5
  
           InjectCommutableStates_T1xT2xT3xT4_T5.

Existing Instance embeddedProduct_T1xT2xT3xT4_T5 .
 
Lemma injcommute_T1xT2xT3xT4xT5_T6: 
               forall ( u : T6 ) ( t :  T1 * T2 * T3 * T4 * T5  ) 
                      ( s:Ledger ), 
      ( injEmbed u ( injEmbed t s ) ) = ( injEmbed t ( injEmbed u s ) ).
Proof.
 intros. compute. auto.
Qed.

Instance InjectCommutableStates_T1xT2xT3xT4xT5_T6 : 
@InjectCommutableStates Ledger (  T1 * T2 * T3 * T4 * T5  ) T6 := 
{
  injcommute := injcommute_T1xT2xT3xT4xT5_T6 
}.

Definition embeddedProduct_T1xT2xT3xT4xT5_T6 := 
           @embeddedProduct Ledger (  T1 * T2 * T3 * T4 * T5  ) T6
  
           InjectCommutableStates_T1xT2xT3xT4xT5_T6.

Existing Instance embeddedProduct_T1xT2xT3xT4xT5_T6 .
 
Lemma injcommute_T1xT2xT3xT4xT5xT6_T7: 
               forall ( u : T7 ) ( t :  T1 * T2 * T3 * T4 * T5 * T6  ) 
                      ( s:Ledger ), 
      ( injEmbed u ( injEmbed t s ) ) = ( injEmbed t ( injEmbed u s ) ).
Proof.
 intros. compute. auto.
Qed.

Instance InjectCommutableStates_T1xT2xT3xT4xT5xT6_T7 : 
@InjectCommutableStates Ledger (  T1 * T2 * T3 * T4 * T5 * T6  ) T7 := 
{
  injcommute := injcommute_T1xT2xT3xT4xT5xT6_T7 
}.

Definition embeddedProduct_T1xT2xT3xT4xT5xT6_T7 := 
           @embeddedProduct Ledger (  T1 * T2 * T3 * T4 * T5 * T6  ) T7
  
           InjectCommutableStates_T1xT2xT3xT4xT5xT6_T7.

Existing Instance embeddedProduct_T1xT2xT3xT4xT5xT6_T7 .
 
Lemma injcommute_T1xT2xT3xT4xT5xT6xT7_T8: 
               forall ( u : T8 ) ( t :  T1 * T2 * T3 * T4 * T5 * T6 * T7  ) 
                      ( s:Ledger ), 
      ( injEmbed u ( injEmbed t s ) ) = ( injEmbed t ( injEmbed u s ) ).
Proof.
 intros. compute. auto.
Qed.

Instance InjectCommutableStates_T1xT2xT3xT4xT5xT6xT7_T8 : 
@InjectCommutableStates Ledger (  T1 * T2 * T3 * T4 * T5 * T6 * T7  ) T8 := 
{
  injcommute := injcommute_T1xT2xT3xT4xT5xT6xT7_T8 
}.

Definition embeddedProduct_T1xT2xT3xT4xT5xT6xT7_T8 := 
           @embeddedProduct Ledger (  T1 * T2 * T3 * T4 * T5 * T6 * T7  ) T8
  
           InjectCommutableStates_T1xT2xT3xT4xT5xT6xT7_T8.

Existing Instance embeddedProduct_T1xT2xT3xT4xT5xT6xT7_T8 .
 
Lemma injcommute_T1xT2xT3xT4xT5xT6xT7xT8_T9: 
               forall ( u : T9 ) ( t :  T1 * T2 * T3 * T4 * T5 * T6 * T7 * T8  ) 
                      ( s:Ledger ), 
      ( injEmbed u ( injEmbed t s ) ) = ( injEmbed t ( injEmbed u s ) ).
Proof.
 intros. compute. auto.
Qed.

Instance InjectCommutableStates_T1xT2xT3xT4xT5xT6xT7xT8_T9 : 
@InjectCommutableStates Ledger (  T1 * T2 * T3 * T4 * T5 * T6 * T7 * T8  ) T9 := 
{
  injcommute := injcommute_T1xT2xT3xT4xT5xT6xT7xT8_T9 
}.

Definition embeddedProduct_T1xT2xT3xT4xT5xT6xT7xT8_T9 := 
           @embeddedProduct Ledger (  T1 * T2 * T3 * T4 * T5 * T6 * T7 * T8  ) T9
  
           InjectCommutableStates_T1xT2xT3xT4xT5xT6xT7xT8_T9.

Existing Instance embeddedProduct_T1xT2xT3xT4xT5xT6xT7xT8_T9 .
 
Lemma injcommute_T1xT2xT3xT4xT5xT6xT7xT8xT9_T10: 
               forall ( u : T10 ) ( t :  T1 * T2 * T3 * T4 * T5 * T6 * T7 * T8 * T9  ) 
                      ( s:Ledger ), 
      ( injEmbed u ( injEmbed t s ) ) = ( injEmbed t ( injEmbed u s ) ).
Proof.
 intros. compute. auto.
Qed.

Instance InjectCommutableStates_T1xT2xT3xT4xT5xT6xT7xT8xT9_T10 : 
@InjectCommutableStates Ledger (  T1 * T2 * T3 * T4 * T5 * T6 * T7 * T8 * T9  ) T10 := 
{
  injcommute := injcommute_T1xT2xT3xT4xT5xT6xT7xT8xT9_T10 
}.

Definition embeddedProduct_T1xT2xT3xT4xT5xT6xT7xT8xT9_T10 := 
           @embeddedProduct Ledger (  T1 * T2 * T3 * T4 * T5 * T6 * T7 * T8 * T9  ) T10
  
           InjectCommutableStates_T1xT2xT3xT4xT5xT6xT7xT8xT9_T10.

Existing Instance embeddedProduct_T1xT2xT3xT4xT5xT6xT7xT8xT9_T10 .
 
Lemma injcommute_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10_T11: 
               forall ( u : T11 ) ( t :  T1 * T2 * T3 * T4 * T5 * T6 * T7 * T8 * T9 * T10  ) 
                      ( s:Ledger ), 
      ( injEmbed u ( injEmbed t s ) ) = ( injEmbed t ( injEmbed u s ) ).
Proof.
 intros. compute. auto.
Qed.

Instance InjectCommutableStates_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10_T11 : 
@InjectCommutableStates Ledger (  T1 * T2 * T3 * T4 * T5 * T6 * T7 * T8 * T9 * T10  ) T11 := 
{
  injcommute := injcommute_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10_T11 
}.

Definition embeddedProduct_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10_T11 := 
           @embeddedProduct Ledger (  T1 * T2 * T3 * T4 * T5 * T6 * T7 * T8 * T9 * T10  ) T11
  
           InjectCommutableStates_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10_T11.

Existing Instance embeddedProduct_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10_T11 .
 
Lemma injcommute_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11_T12: 
               forall ( u : T12 ) ( t :  T1 * T2 * T3 * T4 * T5 * T6 * T7 * T8 * T9 * T10 * T11  ) 
                      ( s:Ledger ), 
      ( injEmbed u ( injEmbed t s ) ) = ( injEmbed t ( injEmbed u s ) ).
Proof.
 intros. compute. auto.
Qed.

Instance InjectCommutableStates_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11_T12 : 
@InjectCommutableStates Ledger (  T1 * T2 * T3 * T4 * T5 * T6 * T7 * T8 * T9 * T10 * T11  ) T12 := 
{
  injcommute := injcommute_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11_T12 
}.

Definition embeddedProduct_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11_T12 := 
           @embeddedProduct Ledger (  T1 * T2 * T3 * T4 * T5 * T6 * T7 * T8 * T9 * T10 * T11  ) T12
  
           InjectCommutableStates_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11_T12.

Existing Instance embeddedProduct_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11_T12 .

(* Print  injEmbed. *)
 
Lemma injcommute_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11xT12_T13: 
               forall ( u : T13 ) ( t :  T1 * T2 * T3 * T4 * T5 * T6 * T7 * T8 * T9 * T10 * T11 * T12  ) 
                      ( s:Ledger ), 
      ( injEmbed (EmbeddedType:=embeddedT13) u ( injEmbed t s ) ) = ( injEmbed t ( injEmbed (EmbeddedType:=embeddedT13) u s ) ).
Proof.
 intros. compute. auto.
Qed.

Instance InjectCommutableStates_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11xT12_T13 : 
@InjectCommutableStates Ledger (  T1 * T2 * T3 * T4 * T5 * T6 * T7 * T8 * T9 * T10 * T11 * T12  ) T13 := 
{
	embeddedTypeU := embeddedT13;
  injcommute := injcommute_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11xT12_T13 
}.

Definition embeddedProduct_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11xT12_T13 := 
           @embeddedProduct Ledger (  T1 * T2 * T3 * T4 * T5 * T6 * T7 * T8 * T9 * T10 * T11 * T12  ) T13
  
           InjectCommutableStates_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11xT12_T13.

Existing Instance embeddedProduct_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11xT12_T13 .
 
Lemma injcommute_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11xT12xT13_T14: 
               forall ( u : T14 ) ( t :  T1 * T2 * T3 * T4 * T5 * T6 * T7 * T8 * T9 * T10 * T11 * T12 * T13  ) 
                      ( s:Ledger ), 
      ( injEmbed (EmbeddedType:=embeddedT14) u ( injEmbed t s ) ) = ( injEmbed t ( injEmbed (EmbeddedType:=embeddedT14) u s ) ).
Proof.
 intros. compute. auto.
Qed.

Instance InjectCommutableStates_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11xT12xT13_T14 : 
@InjectCommutableStates Ledger (  T1 * T2 * T3 * T4 * T5 * T6 * T7 * T8 * T9 * T10 * T11 * T12 * T13  ) T14 := 
{
	embeddedTypeU := embeddedT14;
  injcommute := injcommute_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11xT12xT13_T14 
}.

Definition embeddedProduct_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11xT12xT13_T14 := 
           @embeddedProduct Ledger (  T1 * T2 * T3 * T4 * T5 * T6 * T7 * T8 * T9 * T10 * T11 * T12 * T13  ) T14
  
           InjectCommutableStates_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11xT12xT13_T14.

Existing Instance embeddedProduct_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11xT12xT13_T14 .
 
Lemma injcommute_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11xT12xT13xT14_T15: 
               forall ( u : T15 ) ( t :  T1 * T2 * T3 * T4 * T5 * T6 * T7 * T8 * T9 * T10 * T11 * T12 * T13 * T14  ) 
                      ( s:Ledger ), 
      ( injEmbed u ( injEmbed t s ) ) = ( injEmbed t ( injEmbed u s ) ).
Proof.
 intros. compute. auto.
Qed.

Instance InjectCommutableStates_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11xT12xT13xT14_T15 : 
@InjectCommutableStates Ledger (  T1 * T2 * T3 * T4 * T5 * T6 * T7 * T8 * T9 * T10 * T11 * T12 * T13 * T14  ) T15 := 
{
  injcommute := injcommute_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11xT12xT13xT14_T15 
}.

Definition embeddedProduct_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11xT12xT13xT14_T15 := 
           @embeddedProduct Ledger (  T1 * T2 * T3 * T4 * T5 * T6 * T7 * T8 * T9 * T10 * T11 * T12 * T13 * T14  ) T15
  
           InjectCommutableStates_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11xT12xT13xT14_T15.

Existing Instance embeddedProduct_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11xT12xT13xT14_T15 .

(* Print projEmbed. *)
Definition projEmbed_VMCommitted (l: Ledger) :  VMCommitted := 
	let p := projEmbed (EmbeddedType:=embeddedProduct_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11xT12xT13xT14_T15) l in
	{|
	VMCommitted_ι_DebugDePool :=   (fst ∘ fst ∘ fst ∘ fst ∘ fst ∘ fst ∘ fst ∘ fst ∘ fst ∘ fst ∘ fst ∘ fst ∘ fst ∘ fst) p ; 
	VMCommitted_ι_ValidatorBase := (snd ∘ fst ∘ fst ∘ fst ∘ fst ∘ fst ∘ fst ∘ fst ∘ fst ∘ fst ∘ fst ∘ fst ∘ fst ∘ fst) p ; 
	VMCommitted_ι_ProxyBase :=        (snd ∘ fst ∘ fst ∘ fst ∘ fst ∘ fst ∘ fst ∘ fst ∘ fst ∘ fst ∘ fst ∘ fst ∘ fst) p ; 
	VMCommitted_ι_ConfigParamsBase := (snd ∘ fst ∘ fst ∘ fst ∘ fst ∘ fst ∘ fst ∘ fst ∘ fst ∘ fst ∘ fst ∘ fst) p ; 
	VMCommitted_ι_ParticipantBase := (snd ∘ fst ∘ fst ∘ fst ∘ fst ∘ fst ∘ fst ∘ fst ∘ fst ∘ fst ∘ fst) p ; 
	VMCommitted_ι_DePoolHelper := (snd ∘ fst ∘ fst ∘ fst ∘ fst ∘ fst ∘ fst ∘ fst ∘ fst ∘ fst) p ; 
	VMCommitted_ι_Errors :=  (snd ∘ fst ∘ fst ∘ fst ∘ fst ∘ fst ∘ fst ∘ fst ∘ fst) p ; 
	VMCommitted_ι_InternalErrors :=  (snd ∘ fst ∘ fst ∘ fst ∘ fst ∘ fst ∘ fst ∘ fst) p ; 
	VMCommitted_ι_DePoolLib :=  (snd ∘ fst ∘ fst ∘ fst ∘ fst ∘ fst ∘ fst) p ; 
	VMCommitted_ι_DePoolProxyContract :=  (snd ∘ fst ∘ fst ∘ fst ∘ fst ∘ fst) p ; 
	VMCommitted_ι_RoundsBase :=  (snd  ∘ fst ∘ fst ∘ fst ∘ fst) p ; 
	VMCommitted_ι_DePoolContract :=  (snd ∘ fst ∘ fst ∘ fst) p ; 
	VMCommitted_ι_DePool := (snd ∘ fst ∘ fst) p ; 
	VMCommitted_ι_Participant := (snd ∘ fst) p ; 
	VMCommitted_ι_TestElector := snd p 
	|}.

Definition injEmbed_VMCommitted (v : VMCommitted) (l: Ledger):  Ledger :=
	injEmbed (EmbeddedType:=embeddedProduct_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11xT12xT13xT14_T15) 
			  (VMCommitted_ι_DebugDePool v, VMCommitted_ι_ValidatorBase v,
			  VMCommitted_ι_ProxyBase v, VMCommitted_ι_ConfigParamsBase v,
			  VMCommitted_ι_ParticipantBase v, VMCommitted_ι_DePoolHelper v,
			  VMCommitted_ι_Errors v, VMCommitted_ι_InternalErrors v, 
			  VMCommitted_ι_DePoolLib v, VMCommitted_ι_DePoolProxyContract v,
			  VMCommitted_ι_RoundsBase v, VMCommitted_ι_DePoolContract v,
			  VMCommitted_ι_DePool v, VMCommitted_ι_Participant v,
			  VMCommitted_ι_TestElector v) l.
 
 Lemma projinj_VMCommitted : forall ( t : VMCommitted ) ( s : Ledger ) , 
 projEmbed_VMCommitted ( injEmbed_VMCommitted t s ) = t . 
 Proof.
 intros. compute. destruct t. auto.
Qed. 
 
 Lemma injproj_VMCommitted : forall ( s : Ledger ) , injEmbed_VMCommitted ( projEmbed_VMCommitted s ) s = s . 
 Proof.
 intros. destruct s. compute. auto.
Qed. 

 Lemma injinj_VMCommitted : forall ( t1 t2 : VMCommitted ) ( s : Ledger ) , 
 injEmbed_VMCommitted t1 ( injEmbed_VMCommitted t2 s) = 
 injEmbed_VMCommitted t1 s . 
 Proof.
 intros. destruct s. compute. destruct t1. auto.
Qed. 
 
 Instance embedded_VMCommitted : EmbeddedType Ledger VMCommitted := 
 {
 projEmbed := projEmbed_VMCommitted ; 
 injEmbed := injEmbed_VMCommitted ; 
 projinj := projinj_VMCommitted ; 
 injproj := injproj_VMCommitted ; 
 injinj  := injinj_VMCommitted ; 
 } .


Lemma injcommute_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11xT12xT13xT14xT15_T16: 
               forall ( u : T16 ) ( t :  T1 * T2 * T3 * T4 * T5 * T6 * T7 * T8 * T9 * T10 * T11 * T12 * T13 * T14 * T15  ) 
                      ( s:Ledger ), 
      ( injEmbed u ( injEmbed t s ) ) = ( injEmbed t ( injEmbed u s ) ).
Proof.
 intros. compute. auto.
Qed.

Instance InjectCommutableStates_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11xT12xT13xT14xT15_T16 : 
@InjectCommutableStates Ledger (  T1 * T2 * T3 * T4 * T5 * T6 * T7 * T8 * T9 * T10 * T11 * T12 * T13 * T14 * T15  ) T16 := 
{
  injcommute := injcommute_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11xT12xT13xT14xT15_T16 
}.

Definition embeddedProduct_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11xT12xT13xT14xT15_T16 := 
           @embeddedProduct Ledger (  T1 * T2 * T3 * T4 * T5 * T6 * T7 * T8 * T9 * T10 * T11 * T12 * T13 * T14 * T15  ) T16
  
           InjectCommutableStates_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11xT12xT13xT14xT15_T16.

Existing Instance embeddedProduct_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11xT12xT13xT14xT15_T16 .
 
Lemma injcommute_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11xT12xT13xT14xT15xT16_T17: 
               forall ( u : T17 ) ( t :  T1 * T2 * T3 * T4 * T5 * T6 * T7 * T8 * T9 * T10 * T11 * T12 * T13 * T14 * T15 * T16  ) 
                      ( s:Ledger ), 
      ( injEmbed u ( injEmbed t s ) ) = ( injEmbed t ( injEmbed u s ) ).
Proof.
 intros. compute. auto.
Qed.

Instance InjectCommutableStates_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11xT12xT13xT14xT15xT16_T17 : 
@InjectCommutableStates Ledger (  T1 * T2 * T3 * T4 * T5 * T6 * T7 * T8 * T9 * T10 * T11 * T12 * T13 * T14 * T15 * T16  ) T17 := 
{
  injcommute := injcommute_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11xT12xT13xT14xT15xT16_T17 
}.

Definition embeddedProduct_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11xT12xT13xT14xT15xT16_T17 := 
           @embeddedProduct Ledger (  T1 * T2 * T3 * T4 * T5 * T6 * T7 * T8 * T9 * T10 * T11 * T12 * T13 * T14 * T15 * T16  ) T17
  
           InjectCommutableStates_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11xT12xT13xT14xT15xT16_T17.

Existing Instance embeddedProduct_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11xT12xT13xT14xT15xT16_T17 .
 
(* Axiom fullState_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11xT12xT13xT14xT15xT16_T17 : forall s s0, 
      injEmbed ( T:=(  T1 * T2 * T3 * T4 * T5 * T6 * T7 * T8 * T9 * T10 * T11 * T12 * T13 * T14 * T15 * T16  ) ) 
(projEmbed s) (injEmbed (T:= T17 ) (projEmbed s) s0) = s. *)
Lemma fullState_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11xT12xT13xT14xT15xT16_T17 : forall s s0, 
      injEmbed ( T:=(  T1 * T2 * T3 * T4 * T5 * T6 * T7 * T8 * T9 * T10 * T11 * T12 * T13 * T14 * T15 * T16  ) ) 
(projEmbed s) (injEmbed (T:= T17 ) (projEmbed s) s0) = s.
Proof.
  intros. compute. destruct s.
  auto.
Qed. 

Instance FullState_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11xT12xT13xT14xT15xT16_T17 : 
         FullState Ledger ( T1 * T2 * T3 * T4 * T5 * T6 * T7 * T8 * T9 * T10 * T11 * T12 * T13 * T14 * T15 * T16  ) T17 := 
{
  injComm := InjectCommutableStates_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11xT12xT13xT14xT15xT16_T17 ;
  fullState := fullState_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11xT12xT13xT14xT15xT16_T17 
}. 

(* Print liftEmbeddedState. *)

Notation "'↑ε17' m":= (liftEmbeddedState ( H := embeddedT17 ) ( ε m )%sol ) (at level 10, left associativity): solidity_scope. 
Notation "'↑ε16' m":= (liftEmbeddedState ( H := embeddedT16 ) ( ε m )%sol ) (at level 10, left associativity): solidity_scope.  
Notation "'↑ε15' m":= (liftEmbeddedState ( H := embeddedT15 ) ( ε m )%sol ) (at level 10, left associativity): solidity_scope. 
Notation "'↑ε14' m":= (liftEmbeddedState ( H := embeddedT14 ) ( ε m )%sol ) (at level 10, left associativity): solidity_scope. 
Notation "'↑ε13' m":= (liftEmbeddedState ( H := embeddedT13 ) ( ε m )%sol ) (at level 10, left associativity): solidity_scope. 
Notation "'↑ε12' m":= (liftEmbeddedState ( H := embeddedT12 ) ( ε m )%sol ) (at level 10, left associativity): solidity_scope. 
Notation "'↑ε11' m":= (liftEmbeddedState ( H := embeddedT11 ) ( ε m )%sol ) (at level 10, left associativity): solidity_scope. 
Notation "'↑ε10' m":= (liftEmbeddedState ( H := embeddedT10 ) ( ε m )%sol ) (at level 10, left associativity): solidity_scope. 
Notation "'↑ε9' m":= (liftEmbeddedState ( H := embeddedT9 ) ( ε m )%sol ) (at level 10, left associativity): solidity_scope. 
Notation "'↑ε8' m":= (liftEmbeddedState ( H := embeddedT8 ) ( ε m )%sol ) (at level 10, left associativity): solidity_scope. 
Notation "'↑ε7' m":= (liftEmbeddedState ( H := embeddedT7 ) ( ε m )%sol ) (at level 10, left associativity): solidity_scope. 
Notation "'↑ε6' m":= (liftEmbeddedState ( H := embeddedT6 ) ( ε m )%sol ) (at level 10, left associativity): solidity_scope. 
Notation "'↑ε5' m":= (liftEmbeddedState ( H := embeddedT5 ) ( ε m )%sol ) (at level 10, left associativity): solidity_scope. 
Notation "'↑ε4' m":= (liftEmbeddedState ( H := embeddedT4 ) ( ε m )%sol ) (at level 10, left associativity): solidity_scope. 
Notation "'↑ε3' m":= (liftEmbeddedState ( H := embeddedT3 ) ( ε m )%sol ) (at level 10, left associativity): solidity_scope. 
Notation "'↑ε2' m":= (liftEmbeddedState ( H := embeddedT2 ) ( ε m )%sol ) (at level 10, left associativity): solidity_scope. 
Notation "'↑ε1' m":= (liftEmbeddedState ( H := embeddedT1 ) ( ε m )%sol ) (at level 10, left associativity): solidity_scope. 

Notation "'↑17' m":= (liftEmbeddedState ( H := embeddedT17 ) ( m ) ) (at level 10, left associativity): solidity_scope. 
Notation "'↑16' m":= (liftEmbeddedState ( H := embeddedT16 ) ( m ) ) (at level 10, left associativity): solidity_scope. 
Notation "'↑15' m":= (liftEmbeddedState ( H := embeddedT15 ) ( m ) ) (at level 10, left associativity): solidity_scope. 
Notation "'↑14' m":= (liftEmbeddedState ( H := embeddedT14 ) ( m ) ) (at level 10, left associativity): solidity_scope. 
Notation "'↑13' m":= (liftEmbeddedState ( H := embeddedT13 ) ( m ) ) (at level 10, left associativity): solidity_scope. 
Notation "'↑12' m":= (liftEmbeddedState ( H := embeddedT12 ) ( m ) ) (at level 10, left associativity): solidity_scope. 
Notation "'↑11' m":= (liftEmbeddedState ( H := embeddedT11 ) ( m ) ) (at level 10, left associativity): solidity_scope. 
Notation "'↑10' m":= (liftEmbeddedState ( H := embeddedT10 ) ( m ) ) (at level 10, left associativity): solidity_scope. 
Notation "'↑9' m":= (liftEmbeddedState ( H := embeddedT9 ) ( m ) ) (at level 10, left associativity): solidity_scope. 
Notation "'↑8' m":= (liftEmbeddedState ( H := embeddedT8 ) ( m ) ) (at level 10, left associativity): solidity_scope. 
Notation "'↑7' m":= (liftEmbeddedState ( H := embeddedT7 ) ( m ) ) (at level 10, left associativity): solidity_scope. 
Notation "'↑6' m":= (liftEmbeddedState ( H := embeddedT6 ) ( m ) ) (at level 10, left associativity): solidity_scope. 
Notation "'↑5' m":= (liftEmbeddedState ( H := embeddedT5 ) ( m ) ) (at level 10, left associativity): solidity_scope. 
Notation "'↑4' m":= (liftEmbeddedState ( H := embeddedT4 ) ( m ) ) (at level 10, left associativity): solidity_scope. 
Notation "'↑3' m":= (liftEmbeddedState ( H := embeddedT3 ) ( m ) ) (at level 10, left associativity): solidity_scope. 
Notation "'↑2' m":= (liftEmbeddedState ( H := embeddedT2 ) ( m ) ) (at level 10, left associativity): solidity_scope. 
Notation "'↑1' m":= (liftEmbeddedState ( H := embeddedT1 ) ( m ) ) (at level 10, left associativity): solidity_scope. 
Notation "'↑0' m " := ( liftEmbeddedState ( H :=  embeddedProduct_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11xT12xT13xT14xT15_T16 ) ( m )) (at level 10, left associativity): solidity_scope. 
 
Notation "'↑↑17'":= (liftEmbeddedState ( H := embeddedT17 )  ) (at level 32, left associativity): solidity_scope. 
Notation "'↑↑16'":= (liftEmbeddedState ( H := embeddedT16 )  ) (at level 32, left associativity): solidity_scope. 
Notation "'↑↑15'":= (liftEmbeddedState ( H := embeddedT15 )  ) (at level 32, left associativity): solidity_scope. 
Notation "'↑↑14'":= (liftEmbeddedState ( H := embeddedT14 )  ) (at level 32, left associativity): solidity_scope. 
Notation "'↑↑13'":= (liftEmbeddedState ( H := embeddedT13 )  ) (at level 32, left associativity): solidity_scope. 
Notation "'↑↑12'":= (liftEmbeddedState ( H := embeddedT12 )  ) (at level 32, left associativity): solidity_scope. 
Notation "'↑↑11'":= (liftEmbeddedState ( H := embeddedT11 )  ) (at level 32, left associativity): solidity_scope. 
Notation "'↑↑10'":= (liftEmbeddedState ( H := embeddedT10 )  ) (at level 32, left associativity): solidity_scope. 
Notation "'↑↑9'":= (liftEmbeddedState ( H := embeddedT9 )  ) (at level 32, left associativity): solidity_scope. 
Notation "'↑↑8'":= (liftEmbeddedState ( H := embeddedT8 )  ) (at level 32, left associativity): solidity_scope. 
Notation "'↑↑7'":= (liftEmbeddedState ( H := embeddedT7 )  ) (at level 32, left associativity): solidity_scope. 
Notation "'↑↑6'":= (liftEmbeddedState ( H := embeddedT6 )  ) (at level 32, left associativity): solidity_scope. 
Notation "'↑↑5'":= (liftEmbeddedState ( H := embeddedT5 )  ) (at level 32, left associativity): solidity_scope. 
Notation "'↑↑4'":= (liftEmbeddedState ( H := embeddedT4 )  ) (at level 32, left associativity): solidity_scope. 
Notation "'↑↑3'":= (liftEmbeddedState ( H := embeddedT3 )  ) (at level 32, left associativity): solidity_scope. 
Notation "'↑↑2'":= (liftEmbeddedState ( H := embeddedT2 )  ) (at level 32, left associativity): solidity_scope. 
Notation "'↑↑1'":= (liftEmbeddedState ( H := embeddedT1 )  ) (at level 32, left associativity): solidity_scope. 
Notation "'↑↑0'" := ( liftEmbeddedState ( H :=  embeddedProduct_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11xT12xT13xT14xT15_T16 ) ) (at level 32, left associativity): solidity_scope. 

Variable local0: LocalState.

(* Print callEmbeddedStateAdj. *)

Notation "↓ m" := (callEmbeddedStateAdj m local0 (H0 :=  FullState_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11xT12xT13xT14xT15xT16_T17)) (at level 31, left associativity): solidity_scope.

(* Notation " '↑↑1' n '^^' m " := ( do a ← (↑5 n  ) ; return! ( m a )  )%sol(at level 10, left associativity): solidity_scope.
Notation " '↑↑2' n '^^' m " := ( do a ← (↑11 n  ) ; return! ( m a )  )%sol(at level 10, left associativity): solidity_scope.
Notation " '↑↑3' n '^^' m " := ( do a ← (↑17 n  ) ; return! ( m a )  )%sol(at level 10, left associativity): solidity_scope.
Notation " '↑↑4' n '^^' m " := ( do a ← (↑17 n  ) ; return! ( m a )  )%sol(at level 10, left associativity): solidity_scope.
 *)

 Definition completionReasonEqb (cr1 cr2: RoundsBase_ι_CompletionReason) : XBool :=
	match cr1, cr2 with
	| RoundsBase_ι_CompletionReasonP_ι_Undefined, RoundsBase_ι_CompletionReasonP_ι_Undefined => xBoolTrue
	| RoundsBase_ι_CompletionReasonP_ι_PoolClosed, RoundsBase_ι_CompletionReasonP_ι_PoolClosed => xBoolTrue
	| RoundsBase_ι_CompletionReasonP_ι_FakeRound, RoundsBase_ι_CompletionReasonP_ι_FakeRound => xBoolTrue
	| RoundsBase_ι_CompletionReasonP_ι_ValidatorStakeIsTooSmall, RoundsBase_ι_CompletionReasonP_ι_ValidatorStakeIsTooSmall => xBoolTrue
	| RoundsBase_ι_CompletionReasonP_ι_StakeIsRejectedByElector, RoundsBase_ι_CompletionReasonP_ι_StakeIsRejectedByElector => xBoolTrue
	| RoundsBase_ι_CompletionReasonP_ι_RewardIsReceived, RoundsBase_ι_CompletionReasonP_ι_RewardIsReceived => xBoolTrue
	| RoundsBase_ι_CompletionReasonP_ι_ElectionsAreLost, RoundsBase_ι_CompletionReasonP_ι_ElectionsAreLost => xBoolTrue
	| RoundsBase_ι_CompletionReasonP_ι_ValidatorIsPunished, RoundsBase_ι_CompletionReasonP_ι_ValidatorIsPunished => xBoolTrue
	| RoundsBase_ι_CompletionReasonP_ι_NoValidatorRequest, RoundsBase_ι_CompletionReasonP_ι_NoValidatorRequest => xBoolTrue
	| RoundsBase_ι_CompletionReasonP_ι_BadProxy, RoundsBase_ι_CompletionReasonP_ι_BadProxy => xBoolTrue
	| _, _ => xBoolFalse
	end.

Global Instance completionReasonEquable: XBoolEquable XBool RoundsBase_ι_CompletionReason	:= { eqb:= completionReasonEqb }.


Definition completionReason2XInteger (cr: RoundsBase_ι_CompletionReason) : XInteger := 
	match cr with
	| RoundsBase_ι_CompletionReasonP_ι_Undefined => xInt0
	| RoundsBase_ι_CompletionReasonP_ι_PoolClosed => xInt1
	| RoundsBase_ι_CompletionReasonP_ι_FakeRound => xInt2
	| RoundsBase_ι_CompletionReasonP_ι_ValidatorStakeIsTooSmall => xInt3
	| RoundsBase_ι_CompletionReasonP_ι_StakeIsRejectedByElector => xInt4
	| RoundsBase_ι_CompletionReasonP_ι_RewardIsReceived => xInt5
	| RoundsBase_ι_CompletionReasonP_ι_ElectionsAreLost => xInt6
	| RoundsBase_ι_CompletionReasonP_ι_ValidatorIsPunished => xInt7
	| RoundsBase_ι_CompletionReasonP_ι_NoValidatorRequest => xInt8
	| RoundsBase_ι_CompletionReasonP_ι_BadProxy => xInt9
	end	.

Global Instance completionReasonIntegerable : XIntegerable XInteger RoundsBase_ι_CompletionReason :=
 { toInteger := completionReason2XInteger }.
	
Definition roundStepEqb (cr1 cr2: RoundsBase_ι_RoundStep) : XBool :=
	match cr1, cr2 with
	| RoundsBase_ι_RoundStepP_ι_Pooling, RoundsBase_ι_RoundStepP_ι_Pooling => xBoolTrue
	| RoundsBase_ι_RoundStepP_ι_WaitingValidatorRequest, RoundsBase_ι_RoundStepP_ι_WaitingValidatorRequest => xBoolTrue
	| RoundsBase_ι_RoundStepP_ι_WaitingIfStakeAccepted, RoundsBase_ι_RoundStepP_ι_WaitingIfStakeAccepted => xBoolTrue
	| RoundsBase_ι_RoundStepP_ι_WaitingValidationStart, RoundsBase_ι_RoundStepP_ι_WaitingValidationStart => xBoolTrue
	| RoundsBase_ι_RoundStepP_ι_WaitingIfValidatorWinElections, RoundsBase_ι_RoundStepP_ι_WaitingIfValidatorWinElections => xBoolTrue
	| RoundsBase_ι_RoundStepP_ι_WaitingUnfreeze, RoundsBase_ι_RoundStepP_ι_WaitingUnfreeze => xBoolTrue
	| RoundsBase_ι_RoundStepP_ι_WaitingReward, RoundsBase_ι_RoundStepP_ι_WaitingReward => xBoolTrue
	| RoundsBase_ι_RoundStepP_ι_Completing, RoundsBase_ι_RoundStepP_ι_Completing => xBoolTrue
	| RoundsBase_ι_RoundStepP_ι_Completed, RoundsBase_ι_RoundStepP_ι_Completed => xBoolTrue
	| RoundsBase_ι_RoundStepP_ι_PrePooling, RoundsBase_ι_RoundStepP_ι_PrePooling => xBoolTrue
	| _, _ => xBoolFalse
	end.

Global Instance roudStepEquable: XBoolEquable XBool RoundsBase_ι_RoundStep	:= { eqb:= roundStepEqb }.

Definition eventEqb (e1 e2: LedgerEvent): XBool := xBoolFalse.

End LedgerClass .

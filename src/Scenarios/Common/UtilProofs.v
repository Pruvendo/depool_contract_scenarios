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

Require Export Coq.micromega.Lia.

Lemma div_neg_neg_or : forall a b, a / b < 0 -> (a < 0 \/ b < 0).
Proof.
intros. case_eq (a <? 0). intros. apply Zlt_is_lt_bool in H0. left. assumption.
intros. assert (a < 0 \/ 0 <= a) by apply Z.neg_nonneg_cases. inversion H1.
apply Zlt_is_lt_bool in H2. congruence.
case_eq (b <? 0). intros. apply Zlt_is_lt_bool in H3. right. assumption.
intros. assert (b < 0 \/ 0 <= b) by apply Z.neg_nonneg_cases. inversion H4.
apply Zlt_is_lt_bool in H5. congruence. apply Z.lt_eq_cases in H5. inversion H5.
assert (0 <= a / b). apply Z.div_pos ; assumption. omega. rewrite <- H6 in H.
rewrite Zdiv_0_r in H. omega.
Qed.

Lemma neg_lt0b_ge0 : forall a, (a <? 0) = false -> a = 0 \/ 0 < a.
Proof.
intros. assert (a < 0 \/ 0 <= a) by apply Z.neg_nonneg_cases. inversion H0.
apply Zlt_is_lt_bool in H1. congruence. omega.
Qed.

Definition non_neg_zlist (l : list Z) := Forall (Z.le 0) l.
Definition pos_zlist (l : list Z) := Forall (Z.lt 0) l.

Lemma sum_z_eq_z_add_z_0 : forall (l : list Z)(z : Z),
    fold_left Z.add l z = z + fold_left Z.add l 0.
Proof.
intro l. induction l. simpl. lia. intros. simpl. rewrite IHl.
rewrite IHl with (z := a). lia.
Qed.

Lemma sum_not_neg_not_neg : forall (l : list Z),
    non_neg_zlist l ->
    0 <= fold_left Z.add l 0.
Proof.
intros. induction l. simpl. lia. simpl. rewrite sum_z_eq_z_add_z_0.
unfold non_neg_zlist in H. inversion H. unfold non_neg_zlist in IHl.
apply IHl in H3. apply Z.add_nonneg_nonneg ; assumption.
Qed.

Lemma element_less_sum : forall (l : list Z)(z : Z),
    non_neg_zlist l ->
    In z l -> 
    z <= fold_left Z.add l 0.
Proof.
intro l. induction l. intros. simpl. inversion H0. intros. inversion H0.
rewrite H1. simpl. rewrite sum_z_eq_z_add_z_0. replace z with (z + 0) at 1.
apply Z.add_le_mono_l. apply sum_not_neg_not_neg. unfold non_neg_zlist in H.
inversion H. unfold non_neg_zlist. assumption. lia. simpl. rewrite sum_z_eq_z_add_z_0.
assert(forall m n p, 0 <= n -> m <= p -> m <= n + p) by lia.
apply H2. unfold non_neg_zlist in H. inversion H. assumption. apply IHl.
unfold non_neg_zlist in *. inversion H. assumption. assumption.
Qed.

Lemma ForAll_map : forall (X Y : Type) (f : Y -> Prop) (g : X -> Y) ( l : list X),
Forall f (map g l) <-> Forall (compose f g) l.
Proof.
intros. split. intros. induction l. simpl in H. auto.
apply CommonProofs.Forall_cons. apply CommonProofs.Forall_cons in H.
inversion H. split. auto. apply IHl. unfold map. assumption.
intros. induction l. simpl. auto. apply CommonProofs.Forall_cons. split.
apply CommonProofs.Forall_cons in H. inversion H. auto.
unfold map in IHl. apply IHl. apply CommonProofs.Forall_cons in H.
inversion H. assumption.
Qed.

Lemma in_map_exists : forall (A B : Type) (l : list A) (s : B)  (f : A -> B) ,
    In s (map f l) ->
    (exists k, In k l /\ s = f k).
Proof.
intro A. intro B. intro l. induction l. intros. inversion H. intros.
simpl in H. inversion H. exists a. split. simpl. left. reflexivity.
symmetry. assumption. apply IHl in H0. inversion H0. exists x. inversion H1.
split. simpl. right. assumption. assumption.
Qed.

Lemma sub_sub_min_non_neg_l : forall m n,
    0 <= n ->
    0 <= n - intMin n m.
Proof.
intros. unfold intMin. simpl. case_eq (n <=? m) ; intros . lia.
apply Zle_minus_le_0. apply Z.leb_gt in H0. apply Z.lt_le_incl. assumption.
Qed.

Lemma intMin_sym : forall m n, intMin n m = intMin m n.
Proof.
intros. unfold intMin. simpl. case_eq (n <=? m) ; intros ; case_eq (m <=? n) ;
intros ; try reflexivity . apply Zle_bool_imp_le in H. apply Zle_bool_imp_le in H0.
apply Z.le_antisymm ; assumption. apply Z.leb_gt in H. apply Z.leb_gt in H0. lia.
Qed.

Lemma sub_sub_min_non_neg_r : forall m n,
    0 <= n ->
    0 <= n - intMin m n.
Proof.
intros. rewrite intMin_sym. apply sub_sub_min_non_neg_l. assumption.
Qed.

Lemma min_lte_l : forall n m,
    intMin n m <= n.
Proof.
intros.  unfold intMin. simpl. case_eq(n <=? m). lia. intros. apply Z.leb_gt in H. lia.
Qed.

Lemma min_lte_r : forall n m,
    intMin n m <= m.
Proof.
intros. rewrite intMin_sym. apply min_lte_l.
Qed.

Lemma min_n_m : forall n m,
    intMin n m = n \/ intMin n m = m.
Proof.
intros. unfold intMin. simpl. case_eq(n <=? m) ; intros. left. reflexivity.
right. reflexivity.
Qed.

Lemma min_gte_0 : forall n m,
    0 <= n ->
    0 <= m ->
    0 <= intMin n m.
Proof.
intros. assert (intMin n m = n \/ intMin n m = m) by apply min_n_m.
inversion H1 ; rewrite H2; assumption.
Qed.

Lemma add_le_2 : forall n1 n2 m1 m2 p,
    n1 <= m1 ->
    n2 <= m2 ->
    m1 + m2 <= p ->
    n1 + n2 <= p.
Proof.
intros. apply Z.le_trans with (m := m1 + m2). apply Z.add_le_mono ; assumption. assumption.
Qed.

Lemma add_le_3 : forall n1 n2 n3 m1 m2 m3 p,
    n1 <= m1 ->
    n2 <= m2 ->
    n3 <= m3 ->
    m1 + m2 + m3 <= p ->
    n1 + n2 + n3 <= p.
Proof.
intros. apply add_le_2 with (m1 := m1 + m2)(m2 := m3).
apply add_le_2 with (m1 := m1)(m2 := m2). assumption. assumption. lia.
assumption. assumption.
Qed.

Lemma intMulDiv_le_full : forall a b c,
    0 <= a ->
    0 <= b ->
    a <= c ->
    0 < c ->
    intMulDiv a b c <= b.
Proof.
intros. unfold intMulDiv. simpl. rewrite <- Z_div_mult with (b := c).
setoid_rewrite Z.mul_comm at 2. apply Z_div_le. lia. apply Z.mul_le_mono_nonneg_r.
assumption. assumption. lia.
Qed.

Lemma intMulDiv_le_a : forall a b c,
    0 <= a ->
    b <= c ->
    0 < c ->
    intMulDiv a b c <= a.
Proof.
intros. unfold intMulDiv. simpl. rewrite <- Z_div_mult with (a:=a)(b:=c) at 2.
apply Z.div_le_mono. assumption. apply Zmult_le_compat_l ; assumption. lia.
Qed.

Lemma intMulDiv_ge_0 : forall a b c,
    0 <= a ->
    0 <= b ->
    0 < c ->
    0 <= intMulDiv a b c.
Proof.
intros. unfold intMulDiv. simpl. apply Z_div_pos. lia. lia.
Qed.

Lemma pos_zlist_is_non_neg_zlist : forall (l : list Z),
    pos_zlist l -> non_neg_zlist l.
Proof.
intros. induction l. unfold non_neg_zlist. apply Forall_nil. apply Forall_cons.
inversion H. lia. unfold non_neg_zlist in IHl. apply IHl. apply Forall_inv_tail in H.
unfold pos_zlist. assumption.
Qed.

Lemma forall_f_to_g : forall (X : Type) (f g : X -> Prop) (l : list X),
    (forall x, f x -> g x) -> Forall f l -> Forall g l.
Proof.
intros. induction l. apply Forall_nil. apply ForallCons in H0. inversion H0.
apply Forall_cons. apply H. assumption. apply IHl. assumption.
Qed.

Lemma element_strictly_less_sum : forall (l : list Z),
    pos_zlist l ->
    (1 < length l)%nat ->
    Forall (Z.gt (fold_left Z.add l 0)) l.
Proof.
intros. induction l. inversion H0.
simpl. rewrite sum_z_eq_z_add_z_0. apply Forall_cons. rewrite <- Z.add_0_r.
apply Z.lt_gt. apply Zplus_lt_compat_l. destruct l. inversion H0. inversion H2.
simpl. rewrite sum_z_eq_z_add_z_0. apply Z.add_pos_nonneg. inversion H.
inversion H4. assumption. apply sum_not_neg_not_neg. apply pos_zlist_is_non_neg_zlist.
inversion H. inversion H4. unfold pos_zlist. assumption. induction l.
simpl in *. lia. clear IHl0. induction l. simpl in *. apply Forall_cons.
apply Z.lt_gt. replace a0 with (0 + a0) at 1. inversion H. apply Z.add_lt_le_mono.
assumption. lia. lia. apply Forall_nil.
apply forall_f_to_g with (f := Z.gt (fold_left Z.add (a0 :: a1 :: l) 0)). intros.
apply Z.gt_lt in H1. apply Z.lt_gt. replace x with (0 + x). apply Z.add_lt_mono.
inversion H. assumption. assumption. lia. apply IHl. inversion H. unfold pos_zlist.
assumption. simpl. lia.
Qed.

Lemma pos_zlist_assoc : forall (l : list Z) a b ,
    pos_zlist (a :: b :: l) ->
    pos_zlist (b :: a :: l).
Proof.
intros. inversion_clear H. inversion_clear H1.
unfold pos_zlist. apply Forall_cons. assumption. apply Forall_cons. assumption. assumption.
Qed.

Lemma pos_zlist_sum_is_pos_not_empty : forall (l : list Z),
    pos_zlist l ->
    (0 < length l)%nat ->
    0 < (fold_left Z.add l 0).
Proof.
intros. destruct l. inversion H0. clear H0. induction l. simpl. unfold pos_zlist in H.
apply (Forall_one(a := z)) in H. assumption. simpl.
rewrite sum_z_eq_z_add_z_0. apply pos_zlist_assoc in H. inversion_clear H. apply IHl in H1.
simpl in H1. rewrite sum_z_eq_z_add_z_0 in H1. lia.
Qed.

Lemma matchOpt_exists : forall (X : Type) (o : option X),
    match o with | Some _ => true | _ => false end = true <->
    exists z, o = Some z.
Proof.
intros. split. intros. destruct o. exists x. reflexivity. discriminate.
intros. inversion H. destruct o. reflexivity. discriminate.
Qed.

Lemma len_one_as_list_one : forall (X : Type) (l : list X),
    (1 = length l)%nat <->
    exists x, l = [x].
Proof.
intros. split. intros. destruct l. inversion H. destruct l. exists x. reflexivity.
inversion H. intros. inversion H. rewrite H0. auto.
Qed.

Lemma isSome_false_default : forall (X : Type) (x : XMaybe X)`{XDefault X},
xMaybeIsSome x = xBoolFalse -> maybeGet x = default.
Proof.
intros. unfold xMaybeIsSome in H0. destruct x. discriminate. compute. reflexivity.
Qed.
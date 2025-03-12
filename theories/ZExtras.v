Require Import ZArith.

Fixpoint Ztruncate (sz : nat) (x : Z) :=
  match sz with
  | 0 => 0%Z
  | 1 => if Z.odd x then (-1)%Z else 0%Z
  | S sz =>
    if Z.odd x
    then Z.succ_double (Ztruncate sz (Z.div2 x))
    else Z.double (Ztruncate sz (Z.div2 x))
  end.

Lemma Ztruncate_S_S : forall sz x,
  Ztruncate (S (S sz)) x =
    if Z.odd x
    then Z.succ_double (Ztruncate (S sz) (Z.div2 x))
    else Z.double (Ztruncate (S sz) (Z.div2 x)).
Proof. intros. reflexivity. Qed.

Lemma Ztruncate_wrap : forall sz x,
  Ztruncate (S sz) x = ((x + 2 ^ Z.of_nat sz) mod 2 ^ Z.of_nat (S sz) - 2 ^ Z.of_nat sz)%Z.
Proof.
  intros sz.
  induction sz; intros x.
  - cbn. rewrite Zmod_even, Z.add_1_r, Z.even_succ.
    destruct (Z.odd x); reflexivity.
  - rewrite Ztruncate_S_S.
    rewrite Nat2Z.inj_succ, Nat2Z.inj_succ.
    rewrite Z.pow_succ_r by apply Nat2Z.is_nonneg.
    rewrite Z.pow_succ_r by apply Nat2Z.is_nonneg.
    rewrite Z.rem_mul_r;
    [|discriminate|apply Z.pow_pos_nonneg; [apply Z.lt_0_2|apply Nat2Z.is_nonneg]].
    rewrite Z.mul_comm, Z_mod_plus_full, Zmod_odd.
    rewrite Z.div_add, <- Z.div2_div by discriminate.
    rewrite <- Z.add_sub_assoc, (Z.mul_comm _ 2), <- Z.mul_sub_distr_l.
    destruct (Z.odd x).
    + rewrite Z.add_comm, <- Z.succ_double_spec.
      f_equal. apply IHsz.
    + rewrite Z.add_0_l. rewrite <- (Z.double_spec (_ - _)%Z).
      f_equal. apply IHsz.
Qed.

Lemma Zsucc_double_spec' : forall x, Z.succ_double x = Z.succ (Z.double x).
Proof. intros x. destruct x; reflexivity. Qed.

Lemma Zsucc_double_not_zero : forall x, Z.succ_double x <> 0%Z.
Proof. intros x. destruct x; discriminate. Qed.

Lemma Zdouble_inj : forall (x y : Z),
  Z.double x = Z.double y -> x = y.
Proof.
  intros x y.
  destruct x, y; intros H; try discriminate.
  - reflexivity.
  - f_equal. injection H as H. apply H.
  - f_equal. injection H as H. apply H.
Qed.

Lemma Zsucc_double_inj : forall (x y : Z),
  Z.succ_double x = Z.succ_double y -> x = y.
Proof.
  intros x y H.
  apply Zdouble_inj, Z.succ_inj.
  rewrite <- Zsucc_double_spec', <- Zsucc_double_spec'.
  apply H.
Qed.

Lemma Zdouble_not_odd : forall (x : Z), Z.odd (Z.double x) = false.
Proof. intros x. destruct x; reflexivity. Qed.

Lemma Zsucc_double_odd : forall (x : Z),
  Z.odd (Z.succ_double x) = true.
Proof.
  intros x.
  destruct x; [reflexivity|reflexivity|].
  destruct p; reflexivity.
Qed.

Lemma Zdiv2_double : forall (x : Z), Z.div2 (Z.double x) = x.
Proof. intros x. destruct x; reflexivity. Qed.

Lemma Zdiv2_succ_double : forall (x : Z),
  Z.div2 (Z.succ_double x) = x.
Proof.
  intros x.
  destruct x; [reflexivity|reflexivity|].
  destruct p; [reflexivity| |reflexivity].
  cbn. f_equal. apply Pos.succ_pred_double.
Qed.

Lemma Zdouble_neq_succ_double : forall x y,
  Z.double x <> Z.succ_double y.
Proof.
  intros x y H.
  destruct x, y; try discriminate.
  destruct p, p0; discriminate.
Qed.

Lemma Pos_div2_up_pred_double : forall p,
  Pos.div2_up (Pos.pred_double p) = p.
Proof.
  intros p.
  destruct p.
  - reflexivity.
  - cbn. rewrite Pos.pred_double_spec, Pos.succ_pred by discriminate.
    reflexivity.
  - reflexivity.
Qed.

Lemma Zdiv2_succ_distr : forall x,
  Z.div2 (Z.succ x) = (Z.div2 x + Z.b2z (Z.odd x))%Z.
Proof.
  intros x.
  destruct x.
  - reflexivity.
  - destruct p.
    + cbn. rewrite Pos.add_1_r. reflexivity.
    + reflexivity.
    + reflexivity.
  - destruct p.
    + cbn. rewrite Z.pos_sub_lt by apply Pos.lt_1_succ.
      rewrite <- Pos.pred_sub, Pos.pred_succ.
      reflexivity.
    + cbn. rewrite Pos_div2_up_pred_double.
      reflexivity.
    + reflexivity.
Qed.

Lemma Zdiv2_pred : forall x,
  Z.div2 (Z.pred x) = (Z.div2 x - Z.b2z (Z.even x))%Z.
Proof.
  intros x.
  destruct x.
  - reflexivity.
  - destruct p.
    + reflexivity.
    + destruct p; reflexivity.
    + reflexivity.
  - destruct p.
    + reflexivity.
    + cbn. rewrite Pos.add_1_r. reflexivity.
    + reflexivity.
Qed.

Lemma Zdiv2_add_distr : forall x y,
  Z.div2 (x + y)%Z = (Z.div2 x + Z.div2 y + Z.b2z (Z.odd x && Z.odd y))%Z.
Proof.
  intros x y.
  rewrite Z.div2_div.
  replace (x + y)%Z with (x + y + (Z.b2z false))%Z by apply (Z.add_comm _ 0%Z).
  rewrite Z.add_carry_div2.
  rewrite Bool.orb_false_r.
  rewrite <- 2 Z.div2_div.
  rewrite 2 Z.bit0_odd.
  reflexivity.
Qed.
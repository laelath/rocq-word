Require Import NArith.

Fixpoint Ntruncate (n : nat) (x : N) :=
  match n with
  | 0 => N0
  | S n' =>
    if N.odd x
    then N.succ_double (Ntruncate n' (N.div2 x))
    else N.double (Ntruncate n' (N.div2 x))
  end.



Lemma Ntruncate_0 : forall n,
  Ntruncate n 0%N = 0%N.
Proof.
  intros n.
  induction n.
  - reflexivity.
  - cbn. rewrite IHn. reflexivity.
Qed.

Lemma Ntruncate_mod_pow_2 : forall n x,
  Ntruncate n x = N.modulo x (N.pow 2 (N.of_nat n)).
Proof.
  intros n.
  induction n; intros x.
  - cbn. apply eq_sym, N.mod_1_r.
  - rewrite Nat2N.inj_succ.
    rewrite N.pow_succ_r'.
    rewrite N.Div0.mod_mul_r.
    rewrite <- N.bit0_mod.
    rewrite N.bit0_odd.
    rewrite <- N.div2_div.
    rewrite <- N.double_spec.
    rewrite <- IHn.
    cbn.
    destruct (N.odd x).
    + rewrite N.add_comm, <- N.succ_double_spec. reflexivity.
    + reflexivity.
Qed.

Lemma Ndouble_not_odd : forall x,
  N.odd (N.double x) = false.
Proof. intros []; reflexivity. Qed.

Lemma Nsucc_double_odd : forall x,
  N.odd (N.succ_double x) = true.
Proof. intros []; reflexivity. Qed.

Lemma Ndouble_even : forall x,
  N.even (N.double x) = true.
Proof. intros []; reflexivity. Qed.

Lemma Nsucc_double_not_even : forall x,
  N.even (N.succ_double x) = false.
Proof. intros []; reflexivity. Qed.

Lemma Ndouble_truncate : forall n x,
  N.double (Ntruncate n x) = Ntruncate (S n) (N.double x).
Proof.
  intros.
  cbn.
  rewrite Ndouble_not_odd, N.div2_double.
  reflexivity.
Qed.

Lemma Nsucc_double_truncate : forall n x,
  N.succ_double (Ntruncate n x) = Ntruncate (S n) (N.succ_double x).
Proof.
  intros.
  cbn.
  rewrite Nsucc_double_odd, N.div2_succ_double.
  reflexivity.
Qed.

Lemma Ndouble_succ_distr : forall n,
  N.double (N.succ n) = N.succ (N.succ (N.double n)).
Proof.
  intros n.
  destruct n.
  - reflexivity.
  - reflexivity.
Qed.

Lemma Nsucc_double_spec' : forall n,
  N.succ_double n = N.succ (N.double n).
Proof.
  intros n.
  destruct n.
  - reflexivity.
  - reflexivity.
Qed.

Lemma Ntruncate_idemp : forall n x,
  (Ntruncate n (Ntruncate n x)) = Ntruncate n x.
Proof.
  intros n.
  induction n; intros x.
  - reflexivity.
  - cbn.
    destruct (N.odd x).
    + rewrite Nsucc_double_odd, N.div2_succ_double.
      f_equal.
      apply IHn.
    + rewrite Ndouble_not_odd, N.div2_double.
      f_equal.
      apply IHn.
Qed.

Lemma Nsucc_div2_distr : forall n,
  N.div2 (N.succ (N.succ n)) = N.succ (N.div2 n).
Proof.
  intros n.
  destruct n; [reflexivity|].
  destruct p; reflexivity.
Qed.

Lemma Ndiv2_succ_distr : forall n,
  N.div2 (N.succ n) = (N.div2 n + N.b2n (N.odd n))%N.
Proof.
  intros n.
  destruct n.
  - reflexivity.
  - destruct p.
    + rewrite N.add_1_r. reflexivity.
    + reflexivity.
    + reflexivity.
Qed.

Lemma Ndouble_div2 : forall n,
  N.double (N.div2 n) = (n - N.b2n (N.odd n))%N.
Proof.
  intros n.
  destruct n.
  - reflexivity.
  - destruct p; reflexivity.
Qed.

Lemma Nsucc_double_div2 : forall n,
  N.succ_double (N.div2 n) = (n + N.b2n (N.even n))%N.
Proof.
  intros n.
  destruct n.
  - reflexivity.
  - destruct p; reflexivity.
Qed.

Lemma Ndiv2_add_distr : forall n m,
  N.div2 (n + m)%N = (N.div2 n + N.div2 m + N.b2n (N.odd n && N.odd m))%N.
Proof.
  intros n m.
  rewrite N.div2_div.
  replace (n + m)%N with (n + m + (N.b2n false))%N by apply (N.add_comm _ 0%N).
  rewrite N.add_carry_div2.
  rewrite Bool.orb_false_r.
  rewrite <- N.div2_div, <- N.div2_div.
  rewrite N.bit0_odd, N.bit0_odd.
  reflexivity.
Qed.

Lemma Ndiv2_mul_distr_l : forall n m,
  N.div2 (n * m)%N = (N.div2 n * m + N.b2n (N.odd n) * N.div2 m)%N.
Proof.
  intros n m.
  rewrite (N.div2_odd n) at 1.
  rewrite N.mul_add_distr_r, Ndiv2_add_distr.
  rewrite <- N.double_spec, <- N.double_mul, N.div2_double, Ndouble_not_odd, N.add_0_r.
  destruct (N.odd n).
  - rewrite N.mul_1_l, N.mul_1_l.
    reflexivity.
  - reflexivity.
Qed.

Lemma Ndiv2_mul_distr : forall n m,
  N.div2 (n * m)%N =
  (N.double (N.div2 n * N.div2 m)
   + N.b2n (N.odd m) * N.div2 n
   + N.b2n (N.odd n) * N.div2 m)%N.
Proof.
  intros n m.
  rewrite Ndiv2_mul_distr_l, <- (N.div2_double (N.div2 n * m)%N).
  rewrite N.double_mul, N.mul_comm, Ndiv2_mul_distr_l, N.mul_comm, <- N.double_mul.
  rewrite N.div2_double.
  reflexivity.
Qed.

Lemma Nsucc_truncate_idemp : forall n x,
  Ntruncate n (N.succ (Ntruncate n x)) = Ntruncate n (N.succ x).
Proof.
  intros n.
  induction n; intros x.
  - reflexivity.
  - cbn. rewrite (N.odd_succ x), <- (N.negb_odd x).
    destruct (N.odd x) eqn:E; cbn.
    + rewrite N.odd_succ, Nsucc_double_not_even.
      rewrite Nsucc_double_spec', Nsucc_div2_distr, N.div2_double, IHn.
      rewrite Ndiv2_succ_distr, E, N.add_1_r.
      reflexivity.
    + rewrite N.odd_succ, Ndouble_even.
      rewrite <- Nsucc_double_spec', N.div2_succ_double, Ntruncate_idemp.
      rewrite Ndiv2_succ_distr, E, N.add_0_r.
      reflexivity.
Qed.

Lemma Nadd_truncate_idemp_l : forall n x y,
  Ntruncate n (Ntruncate n x + y)%N = Ntruncate n (x + y)%N.
Proof.
  intros n.
  induction n; intros x y.
  - reflexivity.
  - cbn.
    rewrite N.odd_add, N.odd_add.
    destruct (N.odd x) eqn:Ex, (N.odd y) eqn:Ey.
    + rewrite Nsucc_double_odd.
      cbn. f_equal.
      rewrite Ndiv2_add_distr, Ndiv2_add_distr.
      rewrite N.div2_succ_double, Nsucc_double_odd, Ex, Ey, N.add_1_r, N.add_1_r.
      rewrite <- Nsucc_truncate_idemp, <- (Nsucc_truncate_idemp _ (_ + _)%N).
      f_equal. f_equal. apply IHn.
    + rewrite Nsucc_double_odd.
      cbn. f_equal.
      rewrite Ndiv2_add_distr, Ndiv2_add_distr.
      rewrite N.div2_succ_double, Ex, Ey, Bool.andb_false_r, N.add_0_r, N.add_0_r.
      apply IHn.
    + rewrite Ndouble_not_odd.
      cbn. f_equal.
      rewrite Ndiv2_add_distr, Ndiv2_add_distr.
      rewrite N.div2_double, Ndouble_not_odd, Ex, N.add_0_r, N.add_0_r.
      apply IHn.
    + rewrite Ndouble_not_odd.
      cbn. f_equal.
      rewrite Ndiv2_add_distr, Ndiv2_add_distr.
      rewrite N.div2_double, Ndouble_not_odd, Ex, N.add_0_r, N.add_0_r.
      apply IHn.
Qed.

Lemma Nsucc_double_not_0 : forall n,
  N.succ_double n <> 0%N.
Proof.
  intros n Heq.
  destruct n; [discriminate Heq|].
  destruct p; discriminate Heq.
Qed.

Lemma Ndouble_neq_succ_double : forall n m,
  N.double n <> N.succ_double m.
Proof. intros [] []; discriminate. Qed.
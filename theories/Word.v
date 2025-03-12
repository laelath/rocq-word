From Coq Require Import Equalities NArith ZArith.

From Word Require Import NExtras ZExtras.

From Word Require Export WordDef.

Local Open Scope word_scope.

Module Word.

Include WordDef.Word.

Ltac destruct_word_0 v :=
  pattern v; apply case0; clear v.

Ltac destruct_word_S v :=
  pattern v; apply caseS; clear v; intros v.

Ltac destruct_word v :=
  match type of v with
  | word 0 => destruct_word_0 v
  | _ => destruct_word_S v
  end.

Definition eq {sz} := @Logic.eq (word sz).
Definition eq_equiv {sz} := @eq_equivalence (word sz).

Definition lt {sz} (x y : word sz) := compare x y = Lt.
Definition le {sz} (x y : word sz) := compare x y <> Gt.

Infix "<" := lt : word_scope.
Infix "<=" := le : word_scope.

Definition word_0_Wnil : forall (x : word 0), x = Wnil :=
  fun x => match x with
    | Wnil => eq_refl
    end.

Definition word_0_eq : forall (x y : word 0), x = y :=
  fun x y => match x, y with
    | Wnil, Wnil => eq_refl
    end.

Lemma W0_inj : forall {n} (x y : word n),
  W0 x = W0 y -> x = y.
Proof.
  intros n x y Heq.
  injection Heq as Heq.
  apply (Eqdep_dec.inj_pair2_eq_dec _ PeanoNat.Nat.eq_dec), Heq.
Qed.

Lemma W1_inj : forall {n} (x y : word n),
  W1 x = W1 y -> x = y.
Proof.
  intros n x y Heq.
  injection Heq as Heq.
  apply (Eqdep_dec.inj_pair2_eq_dec _ PeanoNat.Nat.eq_dec), Heq.
Qed.

Lemma neq_W0 : forall {n} (x y : word n),
  x <> y -> W0 x <> W0 y.
Proof.
  intros n x y Hneq Heq.
  apply Hneq, W0_inj, Heq.
Qed.

Lemma neq_W1 : forall {n} (x y : word n),
  x <> y -> W1 x <> W1 y.
Proof.
  intros n x y Hneq Heq.
  apply Hneq, W1_inj, Heq.
Qed.

Lemma eqb_refl : forall {n} (x : word n),
  eqb x x = true.
Proof.
  intros n x.
  induction x.
  - reflexivity.
  - apply IHx.
  - apply IHx.
Qed.

Lemma eqb_eq : forall {n} (x y : word n),
  eqb x y = true <-> x = y.
Proof.
  intros n x y.
  split; [|intros H; rewrite H; apply eqb_refl].
  generalize dependent y.
  generalize dependent x.
  induction n; intros x y.
  - intros. apply word_0_eq.
  - destruct_word x; destruct_word y; intros Heqb.
    + f_equal. apply IHn, Heqb.
    + discriminate Heqb.
    + discriminate Heqb.
    + f_equal. apply IHn, Heqb.
Qed.

Lemma eqb_neq : forall {n} (x y : word n),
  eqb x y = false <-> x <> y.
Proof.
  intros n.
  induction n; intros x y.
  - destruct_word_0 x.
    destruct_word_0 y.
    split.
    + discriminate.
    + contradiction.
  - destruct_word_S x;
    destruct_word_S y;
    split; intros H;
    try reflexivity;
    try discriminate.
    + apply neq_W0, IHn, H.
    + apply IHn. intros Heq. apply H, f_equal, Heq.
    + apply neq_W1, IHn, H.
    + apply IHn. intros Heq. apply H, f_equal, Heq.
Qed.

Lemma eqb_sym : forall {n} (x y : word n),
  eqb x y = eqb y x.
Proof.
  intros n.
  induction n; intros x y.
  - destruct_word_0 x.
    destruct_word_0 y.
    reflexivity.
  - destruct_word_S x;
    destruct_word_S y.
    + apply IHn.
    + reflexivity.
    + reflexivity.
    + apply IHn.
Qed.

Lemma eq_dec : forall {sz} (x y : word sz),
  {x = y} + {x <> y}.
Proof.
  intros sz x y.
  destruct (eqb x y) eqn:E.
  - left. apply eqb_eq, E.
  - right. apply eqb_neq, E.
Qed.

Lemma compare_refl : forall {sz} (x : word sz),
  compare x x = Eq.
Proof.
  intros sz x.
  induction x.
  - reflexivity.
  - apply IHx.
  - apply IHx.
Qed.

Lemma compare_cont_antisym : forall {sz} (x y : word sz) c,
  compare_cont c x y = CompOpp (compare_cont (CompOpp c) y x).
Proof.
  intros sz.
  induction sz; intros x y c; destruct_word x; destruct_word y; try apply IHsz.
  apply eq_sym, CompOpp_involutive.
Qed.

Lemma compare_antisym : forall {sz} (x y : word sz),
  compare x y = CompOpp (compare y x).
Proof.
  intros sz x y.
  apply compare_cont_antisym.
Qed.

Lemma compare_cont_neq : forall {sz} (x y : word sz) c,
  c <> Eq -> compare_cont c x y <> Eq.
Proof.
  intros sz.
  induction sz; intros x y c H; destruct_word x; destruct_word y.
  - apply H.
  - apply IHsz, H.
  - apply IHsz. discriminate.
  - apply IHsz. discriminate.
  - apply IHsz, H.
Qed.

Lemma compare_eq : forall {sz} (x y : word sz),
  compare x y = Eq <-> x = y.
Proof.
  intros sz.
  induction sz; intros x y; split.
  - intros. apply word_0_eq.
  - intros H. rewrite H. apply compare_refl.
  - destruct_word x; destruct_word y; intros Hcomp.
    + f_equal. apply IHsz, Hcomp.
    + exfalso. apply (compare_cont_neq x y Lt), Hcomp. discriminate.
    + exfalso. apply (compare_cont_neq x y Gt), Hcomp. discriminate.
    + f_equal. apply IHsz, Hcomp.
  - intros H. rewrite H. apply compare_refl.
Qed.

Lemma compare_neq : forall {sz} (x y : word sz),
  compare x y <> Eq <-> x <> y.
Proof.
  intros sz x y.
  split.
  - intros Hcomp Heq.
    apply Hcomp.
    rewrite Heq.
    apply compare_refl.
  - intros Hneq Hcomp.
    apply Hneq, compare_eq, Hcomp.
Qed.

Lemma eqb_compare : forall {sz} (x y : word sz),
  eqb x y = match compare x y with Eq => true | _ => false end.
Proof.
  intros sz.
  induction sz; intros x y; destruct_word x; destruct_word y.
  - reflexivity.
  - apply IHsz.
  - cbn. destruct (compare_cont Lt x y) eqn:?.
    + exfalso. apply (compare_cont_neq x y Lt), Heqc.
      discriminate.
    + reflexivity.
    + reflexivity.
  - cbn. destruct (compare_cont Gt x y) eqn:?.
    + exfalso. apply (compare_cont_neq x y Gt), Heqc.
      discriminate.
    + reflexivity.
    + reflexivity.
  - apply IHsz.
Qed.

Lemma ltb_compare : forall {sz} (x y : word sz),
  ltb x y = match compare x y with Lt => true | _ => false end.
Proof. reflexivity. Qed.

Lemma leb_compare : forall {sz} (x y : word sz),
  leb x y = match compare x y with Gt => false | _ => true end.
Proof. reflexivity. Qed.

Lemma lt_antirefl : forall {sz} (x : word sz),
  ~ (lt x x).
Proof.
  intros sz x.
  unfold lt.
  rewrite compare_refl.
  discriminate.
Qed.

Lemma compare_cont_neq_ignore : forall {sz c1 c3} c2 (x y : word sz),
  x <> y -> compare_cont c2 x y = c1 -> compare_cont c3 x y = c1.
Proof.
  intros sz.
  induction sz; intros c1 c3 c2 x y.
  - intros Hneq. exfalso. apply Hneq, word_0_eq.
  - destruct_word x; destruct_word y; cbn; intros Hneq Hcompare.
    + eapply IHsz, Hcompare.
      intros Heq.
      apply Hneq, f_equal, Heq.
    + apply Hcompare.
    + apply Hcompare.
    + eapply IHsz, Hcompare.
      intros Heq.
      apply Hneq, f_equal, Heq.
Qed.

Lemma compare_cont_eq : forall {sz c} (x : word sz),
  compare_cont c x x = c.
Proof.
  intros sz c x.
  induction x.
  - reflexivity.
  - apply IHx.
  - apply IHx.
Qed.

Lemma compare_cont_trans : forall {sz} c c' (x y z : word sz),
  compare_cont c x y = c' ->
  compare_cont c y z = c' ->
  compare_cont c x z = c'.
Proof.
  intros sz.
  induction sz; intros c c' x y z.
  - destruct_word x.
    intros H _.
    apply H.
  - destruct_word x; destruct_word y; destruct_word z; cbn; intros Hxy Hyz.
    + apply IHsz with (y := y); assumption.
    + destruct (eq_dec x y) as [Heq|Hneq].
      * rewrite Heq.
        apply Hyz.
      * apply IHsz with (y := y); [|assumption].
        apply (compare_cont_neq_ignore c _ _ Hneq), Hxy.
    + destruct (eq_dec x y) as [Heqxy|Hneqxy].
      * rewrite Heqxy.
        destruct (eq_dec y z) as [Heqyz|Hneqyz].
        { rewrite Heqxy in Hxy.
          rewrite compare_cont_eq in Hxy.
          rewrite Heqyz in Hyz.
          rewrite compare_cont_eq in Hyz.
          rewrite <- Hxy in Hyz.
          discriminate. }
        { apply (compare_cont_neq_ignore Gt _ _ Hneqyz), Hyz. }
      * destruct (eq_dec y z) as [Heqyz|Hneqyz].
        { rewrite <- Heqyz.
          apply (compare_cont_neq_ignore Lt _ _ Hneqxy), Hxy. }
        { apply IHsz with (y := y).
          - apply (compare_cont_neq_ignore Lt _ _ Hneqxy), Hxy.
          - apply (compare_cont_neq_ignore Gt _ _ Hneqyz), Hyz. }
    + destruct (eq_dec y z) as [Heq|Hneq].
      * rewrite <- Heq.
        apply Hxy.
      * apply IHsz with (y := y); [apply Hxy|].
        apply (compare_cont_neq_ignore c _ _ Hneq), Hyz.
    + destruct (eq_dec y z) as [Heq|Hneq].
      * rewrite <- Heq.
        apply Hxy.
      * apply IHsz with (y := y); [apply Hxy|].
        apply (compare_cont_neq_ignore c _ _ Hneq), Hyz.
    + destruct (eq_dec x y) as [Heqxy|Hneqxy].
      * rewrite Heqxy.
        destruct (eq_dec y z) as [Heqyz|Hneqyz].
        { rewrite Heqxy in Hxy.
          rewrite compare_cont_eq in Hxy.
          rewrite Heqyz in Hyz.
          rewrite compare_cont_eq in Hyz.
          rewrite <- Hxy in Hyz.
          discriminate. }
        { apply (compare_cont_neq_ignore Lt _ _ Hneqyz), Hyz. }
      * destruct (eq_dec y z) as [Heqyz|Hneqyz].
        { rewrite <- Heqyz.
          apply (compare_cont_neq_ignore Gt _ _ Hneqxy), Hxy. }
        { apply IHsz with (y := y).
          - apply (compare_cont_neq_ignore Gt _ _ Hneqxy), Hxy.
          - apply (compare_cont_neq_ignore Lt _ _ Hneqyz), Hyz. }
    + destruct (eq_dec x y) as [Heq|Hneq].
      * rewrite Heq.
        apply Hyz.
      * apply IHsz with (y := y); [|apply Hyz].
        apply (compare_cont_neq_ignore c _ _ Hneq), Hxy.
    + apply IHsz with (y := y); assumption.
Qed.

Lemma compare_trans : forall {sz} c (x y z : word sz),
  compare x y = c -> compare y z = c -> compare x z = c.
Proof.
  intros sz c.
  apply compare_cont_trans.
Qed.

Lemma compare_trans_eq_l : forall {sz} c (x y z : word sz),
  compare x y = Eq -> compare y z = c -> compare x z = c.
Proof.
  intros sz c x y z Heq Hyz.
  apply compare_eq in Heq.
  rewrite Heq.
  apply Hyz.
Qed.

Lemma compare_trans_eq_r : forall {sz} c (x y z : word sz),
  compare x y = c -> compare y z = Eq -> compare x z = c.
Proof.
  intros sz c x y z Hxy Heq.
  apply compare_eq in Heq.
  rewrite <- Heq.
  apply Hxy.
Qed.

Lemma lt_trans : forall {sz} (x y z : word sz),
  lt x y -> lt y z -> lt x z.
Proof.
  intros sz.
  apply compare_trans.
Qed.

Lemma le_refl : forall {sz} (x : word sz),
  le x x.
Proof.
  intros sz x.
  unfold le.
  rewrite compare_refl.
  discriminate.
Qed.

Lemma le_trans : forall {sz} (x y z : word sz),
  le x y -> le y z -> le x z.
Proof.
  unfold le.
  intros sz x y z Hxy Hyz.
  destruct (y ?= z) eqn:Eyz.
  - apply compare_eq in Eyz.
    rewrite <- Eyz.
    apply Hxy.
  - destruct (x ?= y) eqn:Exy.
    + apply compare_eq in Exy.
      rewrite Exy, Eyz.
      discriminate.
    + rewrite lt_trans with (y := y); assumption.
    + contradiction.
  - contradiction.
Qed.

Lemma le_lt_trans : forall {sz} (x y z : word sz),
  le x y -> lt y z -> lt x z.
Proof.
  unfold le, lt.
  intros sz x y z Hxy Hyz.
  destruct (x ?= y) eqn:Exy.
  - apply compare_trans_eq_l with (y := y); assumption.
  - apply compare_trans with (y := y); assumption.
  - contradiction.
Qed.

Lemma lt_le_trans : forall {sz} (x y z : word sz),
  lt x y -> le y z -> lt x z.
Proof.
  unfold le, lt.
  intros sz x y z Hxy Hyz.
  destruct (y ?= z) eqn:Exy.
  - apply compare_trans_eq_r with (y := y); assumption.
  - apply compare_trans with (y := y); assumption.
  - contradiction.
Qed.



Lemma append_split : forall sz1 {sz2} (w : word (sz1 + sz2)),
  append (take sz1 w) (drop sz1 w) = w.
Proof.
  intros sz1.
  induction sz1; intros sz2 w.
  - reflexivity.
  - cbn in w.
    destruct_word w.
    + cbn. f_equal. apply IHsz1.
    + cbn. f_equal. apply IHsz1.
Qed.

Lemma split_spec : forall sz1 {sz2} (w : word (sz1 + sz2)),
  split sz1 w = (take sz1 w, drop sz1 w).
Proof.
  intros sz1.
  induction sz1; intros sz2 w.
  - reflexivity.
  - cbn in w.
    destruct_word w.
    + cbn. rewrite IHsz1. reflexivity.
    + cbn. rewrite IHsz1. reflexivity.
Qed.

Lemma take_spec : forall sz1 {sz2} (w : word (sz1 + sz2)),
  take sz1 w = fst (split sz1 w).
Proof.
  intros.
  rewrite split_spec.
  reflexivity.
Qed.

Lemma drop_spec : forall sz1 {sz2} (w : word (sz1 + sz2)),
  drop sz1 w = snd (split sz1 w).
Proof.
  intros.
  rewrite split_spec.
  reflexivity.
Qed.



Lemma succ_inj : forall {sz} (x y : word sz),
  succ x = succ y -> x = y.
Proof.
  intros sz.
  induction sz; intros x y.
  - intros. apply word_0_eq.
  - destruct_word_S x; destruct_word_S y.
    + intros H. f_equal. apply W1_inj, H.
    + discriminate.
    + discriminate.
    + intros H. f_equal. apply IHsz, W0_inj, H.
Qed.

Lemma pred_inj : forall {sz} (x y : word sz),
  pred x = pred y -> x = y.
Proof.
  intros sz.
  induction sz; intros x y.
  - intros. apply word_0_eq.
  - destruct_word_S x; destruct_word_S y.
    + intros H. f_equal. apply IHsz, W1_inj, H.
    + discriminate.
    + discriminate.
    + intros H. f_equal. apply W0_inj, H.
Qed.

Lemma neg_inj : forall {sz} (x y : word sz),
  neg x = neg y -> x = y.
Proof.
  intros sz.
  induction sz; intros x y.
  - intros. apply word_0_eq.
  - destruct_word_S x; destruct_word_S y.
    + intros H. f_equal. apply IHsz, W1_inj, H.
    + discriminate.
    + discriminate.
    + intros H. f_equal. apply IHsz, W0_inj, H.
Qed.

Lemma opp_inj : forall {sz} (x y : word sz),
  opp x = opp y -> x = y.
Proof. intros. apply neg_inj, succ_inj, H. Qed.

Lemma pred_succ : forall {n} (x : word n),
  pred (succ x) = x.
Proof.
  intros n x.
  induction x.
  - reflexivity.
  - reflexivity.
  - simpl. f_equal. apply IHx.
Qed.

Lemma succ_pred : forall {n} (x : word n),
  succ (pred x) = x.
Proof.
  intros n x.
  induction x.
  - reflexivity.
  - simpl. f_equal. apply IHx.
  - reflexivity.
Qed.

Lemma add_sub_inv_full : forall {n m} (x : word n) (y : word m),
  sub (add x y) y = x /\ sub_carry (add_carry x y) y = x.
Proof.
  intros n m x.
  generalize dependent m.
  induction x; intros m y.
  - split; reflexivity.
  - destruct y.
    + split; reflexivity.
    + simpl. split; f_equal; apply IHx.
    + simpl. split; f_equal; apply IHx.
  - destruct y.
    + split; [reflexivity|]. simpl. f_equal. apply pred_succ.
    + simpl. split; f_equal; apply IHx.
    + simpl. split; f_equal; apply IHx.
Qed.

Lemma add_sub_inv : forall {n m} (x : word n) (y : word m), sub (add x y) y = x.
Proof. intros. apply add_sub_inv_full. Qed.

Lemma sub_add_inv_full : forall {n m} (x : word n) (y : word m),
  add (sub x y) y = x /\ add_carry (sub_carry x y) y = x.
Proof.
  intros n m x.
  generalize dependent m.
  induction x; intros m y.
  - split; reflexivity.
  - destruct y.
    + split; [reflexivity|]. simpl. f_equal. apply succ_pred.
    + simpl. split; f_equal; apply IHx.
    + simpl. split; f_equal; apply IHx.
  - destruct y.
    + split; reflexivity.
    + simpl. split; f_equal; apply IHx.
    + simpl. split; f_equal; apply IHx.
Qed.

Lemma sub_add_inv : forall {n m} (x : word n) (y : word m), add (sub x y) y = x.
Proof. intros. apply sub_add_inv_full. Qed.

Lemma add_carry_succ : forall {n m} (x : word n) (y : word m),
  add_carry x y = succ (add x y).
Proof.
  intros n m x.
  generalize dependent m.
  induction x; intros m y.
  - reflexivity.
  - destruct y.
    + reflexivity.
    + reflexivity.
    + simpl. f_equal. apply IHx.
  - destruct y.
    + reflexivity.
    + simpl. f_equal. apply IHx.
    + reflexivity.
Qed.

Lemma add_carry_succ_l : forall {n m} (x : word n) (y : word m),
  add_carry x y = add (succ x) y.
Proof.
  intros n m x.
  generalize dependent m.
  induction x; intros m y.
  - reflexivity.
  - reflexivity.
  - destruct y.
    + reflexivity.
    + simpl. f_equal. apply IHx.
    + simpl. f_equal. apply IHx.
Qed.

Lemma add_carry_succ_r : forall {n} (x y : word n),
  add_carry x y = add x (succ y).
Proof.
  intros n.
  induction n; intros x y.
  - apply word_0_eq.
  - destruct_word_S x;
    destruct_word_S y.
    + reflexivity.
    + simpl. f_equal. apply IHn.
    + reflexivity.
    + simpl. f_equal. apply IHn.
Qed.

Lemma sub_carry_pred : forall {n m} (x : word n) (y : word m),
  sub_carry x y = pred (sub x y).
Proof.
  intros n m x.
  generalize dependent m.
  induction x; intros m y.
  - reflexivity.
  - destruct y.
    + reflexivity.
    + simpl. f_equal. apply IHx.
    + reflexivity.
  - destruct y.
    + reflexivity.
    + reflexivity.
    + simpl. f_equal. apply IHx.
Qed.

Lemma add_zero_r : forall {n m} (x : word n),
  add x (zero m) = x.
Proof.
  intros n m x.
  generalize dependent m.
  induction x; intros m.
  - reflexivity.
  - destruct m.
    + reflexivity.
    + simpl. f_equal. apply IHx.
  - destruct m.
    + reflexivity.
    + simpl. f_equal. apply IHx.
Qed.

Lemma sub_zero_r : forall {n m} (x : word n),
  sub x (zero m) = x.
Proof.
  intros n m x.
  rewrite <- (@add_zero_r n m) at 1.
  apply sub_add_inv.
Qed.

Lemma add_carry_zero_r : forall {n m} (x : word n),
  add_carry x (zero m) = succ x.
Proof.
  intros n m x.
  generalize dependent m.
  induction x; intros m.
  - reflexivity.
  - destruct m.
    + reflexivity.
    + simpl. f_equal. apply add_zero_r.
  - destruct m.
    + reflexivity.
    + simpl. f_equal. apply IHx.
Qed.

Lemma sub_carry_zero_r : forall {n m} (x : word n),
  sub_carry x (zero m) = pred x.
Proof.
  intros n m x.
  generalize dependent m.
  induction x; intros m.
  - reflexivity.
  - destruct m.
    + reflexivity.
    + simpl. f_equal. apply IHx.
  - destruct m.
    + reflexivity.
    + simpl. f_equal. apply sub_zero_r.
Qed.

Lemma add_one_r : forall {n m} (x : word n),
  add x (one m) = succ x.
Proof.
  intros n m x.
  destruct x.
  - reflexivity.
  - simpl. f_equal. apply add_zero_r.
  - simpl. f_equal. apply add_carry_zero_r.
Qed.

Lemma sub_one_r : forall {n m} (x : word n),
  sub x (one m) = pred x.
Proof.
  intros n m x.
  destruct x.
  - reflexivity.
  - simpl. f_equal. apply sub_carry_zero_r.
  - simpl. f_equal. apply sub_zero_r.
Qed.

Lemma add_ones_r : forall {sz} (x : word sz),
  add x (ones sz) = pred x.
Proof.
  intros sz x.
  induction x.
  - reflexivity.
  - cbn. f_equal. apply IHx.
  - cbn. f_equal. rewrite add_carry_succ, <- succ_pred. f_equal. apply IHx.
Qed.

Lemma sub_ones_r : forall {sz} (x : word sz),
  sub x (ones sz) = succ x.
Proof.
  intros sz x.
  induction x.
  - reflexivity.
  - cbn. f_equal. rewrite sub_carry_pred, <- pred_succ. f_equal. apply IHx.
  - cbn. f_equal. apply IHx.
Qed.

Lemma add_comm_full : forall {n} (x y : word n),
  add x y = add y x /\ add_carry x y = add_carry y x.
Proof.
  intros n.
  induction n; intros x y.
  - split; apply word_0_eq.
  - destruct_word_S x; destruct_word_S y; simpl; split; f_equal; apply IHn.
Qed.

Lemma add_comm : forall {n} (x y : word n), add x y = add y x.
Proof. intros n. apply add_comm_full. Qed.

Lemma succ_add_distr_l : forall {n m} (x : word n) (y : word m),
  succ (add x y) = add (succ x) y.
Proof.
  intros n m x y.
  rewrite <- add_carry_succ.
  apply add_carry_succ_l.
Qed.

Lemma succ_add_distr_r : forall {n} (x y : word n),
  succ (add x y) = add x (succ y).
Proof.
  intros n x y.
  rewrite (add_comm x (succ y)).
  rewrite <- succ_add_distr_l.
  rewrite (add_comm y x).
  reflexivity.
Qed.

Lemma succ_add_W0_r : forall {n m} (x : word n) (y : word m),
  succ (add x (W0 y)) = add x (W1 y).
Proof.
  intros n m x y.
  destruct x.
  - reflexivity.
  - reflexivity.
  - simpl. f_equal. apply eq_sym, add_carry_succ.
Qed.

Lemma add_swap : forall {n m o} (x : word n) (y : word m) (z : word o),
  add (add x y) z = add (add x z) y.
Proof.
  intros n m o x.
  generalize dependent o.
  generalize dependent m.
  induction x; intros m o y z.
  - reflexivity.
  - destruct y, z; simpl; f_equal; try apply IHx.
    rewrite add_carry_succ, add_carry_succ.
    f_equal. apply IHx.
  - destruct y, z; simpl; f_equal; try apply IHx.
    + rewrite add_carry_succ, add_carry_succ, <- succ_add_distr_l.
      f_equal. apply IHx.
    + rewrite add_carry_succ, add_carry_succ, <- succ_add_distr_l.
      f_equal. apply IHx.
    + rewrite add_carry_succ, add_carry_succ, <- succ_add_distr_l, <- succ_add_distr_l.
      f_equal. apply IHx.
Qed.

Lemma add_assoc : forall {n m} (x y : word n) (z : word m),
  add x (add y z) = add (add x y) z.
Proof.
  intros n m x y z.
  replace (add x y) with (add y x) by apply add_comm.
  rewrite add_swap.
  apply add_comm.
Qed.

Lemma sub_def : forall {n} (x y : word n),
  sub x y = add x (opp y).
Proof.
  intros n.
  induction n; intros x y.
  - apply word_0_eq.
  - destruct_word_S x;
    destruct_word_S y;
    simpl; f_equal.
    + apply IHn.
    + rewrite sub_carry_pred.
      rewrite IHn.
      unfold opp, twos_comp.
      rewrite <- succ_add_distr_r.
      rewrite pred_succ.
      reflexivity.
    + apply IHn.
    + rewrite add_carry_succ.
      rewrite succ_add_distr_r.
      apply IHn.
Qed.

Lemma opp_def : forall {n} (x : word n),
  add x (opp x) = zero n.
Proof.
  intros n x.
  induction x.
  - reflexivity.
  - simpl. f_equal. apply IHx.
  - simpl. f_equal.
    rewrite add_carry_succ.
    rewrite succ_add_distr_r.
    apply IHx.
Qed.

Lemma add_Wnil_r : forall {n} (x : word n),
  add x Wnil = x.
Proof.
  intros n x.
  destruct x; reflexivity.
Qed.

Lemma mul_Wnil_r : forall {n} (x : word n),
  mul x Wnil = zero n.
Proof.
  intros n x.
  induction x.
  - reflexivity.
  - simpl. f_equal. apply IHx.
  - simpl. f_equal. apply IHx.
Qed.

Lemma mul_zero_l : forall {n m} (y : word m),
  mul (zero n) y = zero n.
Proof.
  intros n.
  induction n; intros m y.
  - reflexivity.
  - simpl. f_equal. apply IHn.
Qed.

Lemma mul_zero_r : forall {n m} (x : word n),
  mul x (zero m) = zero n.
Proof.
  intros n m x.
  generalize dependent m.
  induction x; intros m.
  - reflexivity.
  - simpl. f_equal. apply IHx.
  - destruct m.
    + simpl. f_equal. apply mul_Wnil_r.
    + simpl. f_equal. rewrite add_zero_r. apply IHx.
Qed.

Lemma mul_one_r : forall {n m} (x : word n),
  mul x (one m) = x.
Proof.
  intros n m x.
  generalize dependent m.
  induction x; intros m.
  - reflexivity.
  - simpl. f_equal. apply IHx.
  - simpl. f_equal. rewrite add_zero_r. apply IHx.
Qed.


Fixpoint double {n} (x : word n) :=
  match x with
  | Wnil => Wnil
  | W0 x' => W0 (double x')
  | W1 x' => W0 (succ (double x'))
  end.

Lemma double_zero : forall {n},
  double (zero n) = zero n.
Proof.
  intros n.
  induction n.
  - reflexivity.
  - simpl. f_equal. apply IHn.
Qed.

Lemma double_succ_distr : forall {n} (x : word n),
  double (succ x) = succ (succ (double x)).
Proof.
  intros n x.
  induction x.
  - reflexivity.
  - reflexivity.
  - simpl. f_equal. apply IHx.
Qed.

Lemma double_add_distr : forall {n m} (x : word n) (y : word m),
  double (add x y) = add (double x) (W0 y).
Proof.
  intros n m x.
  generalize dependent m.
  induction x; intros m y.
  - split; reflexivity.
  - destruct y; simpl; f_equal.
    + apply eq_sym, add_Wnil_r.
    + apply IHx.
    + rewrite IHx.
      rewrite succ_add_W0_r.
      reflexivity.
  - destruct y; simpl; f_equal.
    + apply eq_sym, add_Wnil_r.
    + rewrite IHx.
      rewrite succ_add_distr_l.
      reflexivity.
    + rewrite add_carry_succ.
      rewrite double_succ_distr, IHx.
      rewrite succ_add_W0_r.
      rewrite succ_add_distr_l.
      reflexivity.
Qed.

Lemma double_add_distr' : forall {n} (x y : word n),
  double (add x y) = add (double x) (double y).
Proof.
  intros n.
  induction n; intros x y.
  - apply word_0_eq.
  - destruct_word_S x;
    destruct_word_S y;
    simpl; f_equal.
    + apply IHn.
    + rewrite <- succ_add_distr_r.
      f_equal. apply IHn.
    + rewrite <- succ_add_distr_l.
      f_equal. apply IHn.
    + rewrite add_carry_succ.
      rewrite double_succ_distr.
      rewrite <- succ_add_distr_r, <- succ_add_distr_l.
      f_equal. f_equal. apply IHn.
Qed.

Lemma mul_W0_r : forall {n m} (x : word n) (y : word m),
  mul x (W0 y) = double (mul x y).
Proof.
  intros n m x.
  generalize dependent m.
  induction x; intros m y.
  - apply word_0_eq.
  - simpl. f_equal. apply IHx.
  - destruct y.
    + simpl. f_equal.
      rewrite mul_Wnil_r, add_Wnil_r.
      replace (W0 Wnil) with (zero 1) by reflexivity.
      rewrite mul_zero_r, double_zero.
      reflexivity.
    + simpl. f_equal.
      rewrite IHx.
      rewrite double_add_distr.
      reflexivity.
    + simpl. f_equal.
      rewrite IHx.
      rewrite double_add_distr.
      rewrite succ_add_W0_r.
      reflexivity.
Qed.

Lemma mul_W1_r : forall {n m} (x : word n) (y : word m),
  mul x (W1 y) = add (double (mul x y)) x.
Proof.
  intros n m x.
  generalize dependent m.
  induction x; intros m y.
  - reflexivity.
  - destruct y; simpl; f_equal.
    + rewrite mul_Wnil_r, double_zero, add_comm, add_zero_r.
      apply (@mul_one_r sz 0).
    + apply IHx.
    + apply IHx.
  - destruct y; simpl; f_equal.
    + rewrite mul_Wnil_r, double_zero, add_comm, add_zero_r.
      rewrite add_Wnil_r.
      apply (@mul_one_r sz 0).
    + rewrite double_add_distr, add_swap.
      f_equal. apply IHx.
    + rewrite double_add_distr, succ_add_W0_r, add_swap.
      f_equal. apply IHx.
Qed.

Lemma add_W0_r : forall {n m} (x : word n) (y : word m),
  add x (W0 y) = add (add x y) y .
Proof.
  intros n m x.
  generalize dependent m.
  induction x; intros m y.
  - reflexivity.
  - destruct y; simpl; f_equal.
    + apply add_Wnil_r.
    + apply IHx.
    + rewrite add_carry_succ.
      rewrite <- succ_add_W0_r.
      f_equal.
      apply IHx.
  - destruct y; simpl; f_equal.
    + apply add_Wnil_r.
    + apply IHx.
    + rewrite <- succ_add_W0_r.
      rewrite add_carry_succ, <- succ_add_distr_l.
      f_equal.
      apply IHx.
Qed.

Lemma mul_succ_l : forall {n m} (x : word n) (y : word m),
  mul (succ x) y = add (mul x y) y.
Proof.
  intros n m x.
  generalize dependent m.
  induction x; intros m y.
  - reflexivity.
  - reflexivity.
  - destruct y.
    + simpl. rewrite mul_Wnil_r, mul_Wnil_r.
      reflexivity.
    + simpl. f_equal. rewrite IHx.
      apply add_W0_r.
    + simpl. f_equal. rewrite IHx.
      rewrite <- succ_add_W0_r.
      rewrite add_carry_succ.
      f_equal.
      apply add_W0_r.
Qed.

Lemma double_mul_distr_l : forall {n m} (x : word n) (y : word m),
  double (mul x y) = mul (double x) y.
Proof.
  intros n m x.
  generalize dependent m.
  induction x; intros m y.
  - reflexivity.
  - simpl. f_equal. apply IHx.
  - destruct y.
    + simpl. f_equal.
      rewrite mul_Wnil_r, mul_Wnil_r.
      apply double_zero.
    + simpl. f_equal.
      rewrite double_add_distr, mul_succ_l.
      f_equal. apply IHx.
    + simpl. f_equal.
      rewrite double_add_distr, mul_succ_l.
      rewrite succ_add_W0_r.
      f_equal. apply IHx.
Qed.

Lemma mul_comm : forall {n} (x y : word n),
  mul x y = mul y x.
Proof.
  intros n.
  induction n; intros x y.
  - apply word_0_eq.
  - destruct_word_S x;
    destruct_word_S y;
    simpl; f_equal.
    + rewrite mul_W0_r, mul_W0_r.
      f_equal. apply IHn.
    + rewrite mul_W0_r, mul_W1_r.
      f_equal. f_equal. apply IHn.
    + rewrite mul_W0_r, mul_W1_r.
      f_equal. f_equal. apply IHn.
    + rewrite mul_W1_r, mul_W1_r.
      rewrite add_swap.
      f_equal. f_equal. f_equal. apply IHn.
Qed.

Lemma mul_add_distr_l : forall {n m} (x : word n) (y : word n) (z : word m),
  mul (add x y) z = add (mul x z) (mul y z).
Proof.
  intros n.
  induction n; intros m x y z.
  - apply word_0_eq.
  - destruct_word_S x;
    destruct_word_S y; [simpl; f_equal; apply IHn| | |];
    destruct z; simpl; f_equal.
    + apply IHn.
    + rewrite add_assoc. f_equal. apply IHn.
    + rewrite add_assoc. f_equal. apply IHn.
    + apply IHn.
    + rewrite add_swap. f_equal. apply IHn.
    + rewrite add_swap. f_equal. apply IHn.
    + rewrite mul_Wnil_r, mul_Wnil_r, mul_Wnil_r.
      apply eq_sym, add_zero_r.
    + rewrite add_carry_succ.
      rewrite mul_W0_r, double_mul_distr_l, double_succ_distr, double_add_distr'.
      rewrite succ_add_distr_l, succ_add_distr_r.
      rewrite mul_W0_r, double_mul_distr_l, <- mul_succ_l.
      rewrite mul_W0_r, double_mul_distr_l, <- mul_succ_l.
      apply IHn.
    + rewrite add_carry_succ, add_carry_succ.
      rewrite mul_W1_r, <- succ_add_distr_r. f_equal.
      rewrite double_mul_distr_l, double_succ_distr, mul_succ_l.
      rewrite (add_swap _ z), (add_swap _ z). f_equal.
      rewrite mul_succ_l, (add_swap _ z), (add_assoc _ _ z). f_equal.
      rewrite <- double_mul_distr_l, <- mul_W1_r.
      apply IHn.
Qed.

Lemma mul_swap : forall {n m o} (x : word n) (y : word m) (z : word o),
  mul (mul x y) z = mul (mul x z) y.
Proof.
  intros n.
  induction n; intros m o x y z.
  - apply word_0_eq.
  - destruct_word_S x; [simpl; f_equal; apply IHn|].
    destruct y, z; simpl; f_equal.
    + rewrite mul_Wnil_r, mul_Wnil_r.
      apply mul_zero_l.
    + rewrite mul_Wnil_r, mul_Wnil_r.
      apply mul_zero_l.
    + rewrite mul_Wnil_r, mul_Wnil_r.
      apply eq_sym, mul_zero_l.
    + rewrite mul_W0_r, mul_W0_r, mul_W0_r, mul_W0_r.
      f_equal.
      rewrite double_mul_distr_l, double_mul_distr_l.
      rewrite <- mul_succ_l, <- mul_succ_l.
      apply IHn.
    + rewrite mul_W0_r, mul_W0_r.
      rewrite (double_mul_distr_l x y).
      rewrite <- mul_succ_l.
      rewrite double_mul_distr_l.
      rewrite <- mul_succ_l.
      rewrite double_add_distr.
      rewrite succ_add_W0_r.
      rewrite double_mul_distr_l.
      rewrite <- mul_succ_l.
      apply IHn.
    + rewrite mul_Wnil_r, mul_Wnil_r.
      apply eq_sym, mul_zero_l.
    + rewrite mul_W0_r, mul_W0_r.
      rewrite (double_mul_distr_l x z).
      rewrite <- mul_succ_l.
      rewrite double_mul_distr_l.
      rewrite <- mul_succ_l.
      rewrite double_add_distr.
      rewrite succ_add_W0_r.
      rewrite double_mul_distr_l.
      rewrite <- mul_succ_l.
      apply IHn.
    + rewrite (mul_W1_r _ y), (mul_W1_r _ y).
      rewrite add_swap, double_mul_distr_l.
      rewrite <- mul_succ_l.
      rewrite double_mul_distr_l.
      rewrite add_swap.
      rewrite <- mul_succ_l.
      rewrite double_add_distr.
      rewrite succ_add_W0_r.
      rewrite double_mul_distr_l.
      rewrite <- mul_succ_l.
      rewrite mul_add_distr_l.
      rewrite <- add_assoc.
      f_equal.
      apply IHn.
Qed.

Lemma mul_assoc : forall {n m} (x y : word n) (z : word m),
  mul x (mul y z) = mul (mul x y) z.
Proof.
  intros n m x y z.
  replace (mul x y) with (mul y x) by apply mul_comm.
  rewrite mul_swap.
  apply mul_comm.
Qed.

Lemma WordRing0 : ring_theory Wnil Wnil add mul sub opp eq.
Proof. constructor; intros; apply word_0_eq. Qed.

Lemma WordRingS sz : ring_theory (zero (S sz)) (one sz) add mul sub opp eq.
Proof.
  constructor.
  - intros x. rewrite add_comm. apply add_zero_r.
  - apply add_comm.
  - apply add_assoc.
  - intros x. rewrite mul_comm. apply mul_one_r.
  - apply mul_comm.
  - apply mul_assoc.
  - apply mul_add_distr_l.
  - apply sub_def.
  - apply opp_def.
Qed.

Lemma WordRing sz : ring_theory (zero sz) (one' sz) add mul sub opp eq.
Proof.
  destruct sz.
  - apply WordRing0.
  - apply WordRingS.
Qed.

Lemma zext_spec : forall {sz1} (x : word sz1) sz2,
  zext x sz2 = append x (zero sz2).
Proof.
  intros sz1 x sz2.
  induction x.
  - reflexivity.
  - cbn. f_equal. apply IHx.
  - cbn. f_equal. apply IHx.
Qed.

Lemma sext_spec : forall {sz1} (x : word sz1) sz2,
  sext x sz2 = append x (if msb' x then ones sz2 else zero sz2).
Proof.
  intros sz1 x sz2.
  destruct sz1.
  { destruct_word x. reflexivity. }
  induction sz1.
  - destruct_word x; destruct_word x; reflexivity.
  - destruct_word x; cbn; f_equal; apply IHsz1.
Qed.

Lemma add_zext_r : forall {sz1 sz2 sz3} (x : word sz1) (y : word sz2),
  add x (zext y sz3) = add x y.
Proof.
  intros sz1 sz2 sz3 x.
  generalize dependent sz2.
  induction x; intros sz2 y.
  - reflexivity.
  - destruct y; cbn.
    + destruct sz3; cbn.
      * reflexivity.
      * f_equal. apply add_zero_r.
    + f_equal. apply IHx.
    + f_equal. apply IHx.
  - destruct y; cbn.
    + destruct sz3; cbn.
      * reflexivity.
      * f_equal. apply add_zero_r.
    + f_equal. apply IHx.
    + f_equal.
      rewrite add_carry_succ, add_carry_succ.
      f_equal.
      apply IHx.
Qed.

Lemma add_take : forall {sz1} (x : word sz1) {sz2} (y : word (sz1 + sz2)),
  add x (take sz1 y) = add x y.
Proof.
  intros sz1 x.
  induction x; intros sz2 y.
  - reflexivity.
  - cbn in y.
    destruct_word y; cbn; f_equal; apply IHx.
  - cbn in y.
    destruct_word y; cbn; f_equal.
    + apply IHx.
    + rewrite add_carry_succ, add_carry_succ.
      f_equal.
      apply IHx.
Qed.

Lemma mul_take : forall {sz1} (x : word sz1) {sz2} (y : word (sz1 + sz2)),
  mul x (take sz1 y) = mul x y.
Proof.
  intros sz1.
  induction sz1; intros x sz2 y.
  - apply word_0_eq.
  - cbn in y.
    destruct_word x; destruct_word y; cbn; f_equal.
    + rewrite mul_W0_r, mul_W0_r.
      rewrite double_mul_distr_l, double_mul_distr_l.
      apply IHsz1.
    + rewrite mul_W1_r, mul_W1_r.
      f_equal.
      rewrite double_mul_distr_l, double_mul_distr_l.
      apply IHsz1.
    + rewrite add_take.
      f_equal.
      rewrite mul_W0_r, mul_W0_r.
      rewrite double_mul_distr_l, double_mul_distr_l.
      apply IHsz1.
    + rewrite add_take.
      f_equal.
      rewrite mul_W1_r, mul_W1_r.
      f_equal.
      rewrite double_mul_distr_l, double_mul_distr_l.
      apply IHsz1.
Qed.

Lemma mul_ext_spec : forall {sz1 sz2} (x : word sz1) (y : word sz2),
  mul_ext x y = mul (zext x sz2) y.
Proof.
  intros sz1 sz2 x.
  generalize dependent sz2.
  induction x; intros sz2 y.
  - apply eq_sym, mul_zero_l.
  - cbn. f_equal. apply IHx.
  - destruct y; cbn; f_equal.
    + apply IHx.
    + f_equal. apply IHx.
    + f_equal. apply IHx.
Qed.

Lemma add_eq_rect : forall {sz1} (x : word sz1) {sz2} (y : word sz2) sz3 (H : sz2 = sz3),
  add x (eq_rect sz2 word y sz3 H) = add x y.
Proof.
  intros sz1 x sz2 y sz3 H.
  eapply eq_trans; [|eapply eq_trans].
  - apply eq_sym, (map_subst_map (fun _ => sz1) (fun sz (z : word sz) => add x z)).
  - apply eq_sym, (rew_map word (fun _ => sz1)).
  - apply rew_const.
Qed.

Lemma mul_eq_rect : forall {sz1} (x : word sz1) {sz2} (y : word sz2) sz3 (H : sz2 = sz3),
  mul x (eq_rect sz2 word y sz3 H) = mul x y.
Proof.
  intros sz1 x sz2 y sz3 H.
  eapply eq_trans; [|eapply eq_trans].
  - apply eq_sym, (map_subst_map (fun _ => sz1) (fun sz (z : word sz) => mul x z)).
  - apply eq_sym, (rew_map word (fun _ => sz1)).
  - apply rew_const.
Qed.

Lemma zero_len_add : forall sz1 sz2,
  zero (sz1 + sz2)%nat = append (zero sz1) (zero sz2).
Proof.
  intros sz1 sz2.
  induction sz1.
  - reflexivity.
  - cbn. f_equal. apply IHsz1.
Qed.

Lemma take_zero : forall sz1 sz2, take sz1 (zero (sz1 + sz2)%nat) = zero sz1.
Proof.
  intros sz1 sz2.
  induction sz1.
  - reflexivity.
  - cbn. f_equal. apply IHsz1.
Qed.

Lemma ones_len_add : forall sz1 sz2,
  ones (sz1 + sz2)%nat = append (ones sz1) (ones sz2).
Proof.
  intros sz1 sz2.
  induction sz1.
  - reflexivity.
  - cbn. f_equal. apply IHsz1.
Qed.

Lemma take_ones : forall sz1 sz2, take sz1 (ones (sz1 + sz2)%nat) = ones sz1.
Proof.
  intros sz1 sz2.
  induction sz1.
  - reflexivity.
  - cbn. f_equal. apply IHsz1.
Qed.

Lemma take_append : forall {sz1 sz2} (x : word sz1) (y : word sz2),
  take sz1 (append x y) = x.
Proof.
  intros sz1 sz2 x y.
  induction x.
  - reflexivity.
  - cbn. f_equal. apply IHx.
  - cbn. f_equal. apply IHx.
Qed.

Lemma drop_append : forall {sz1 sz2} (x : word sz1) (y : word sz2),
  drop sz1 (append x y) = y.
Proof.
  intros sz1 sz2 x y.
  induction x.
  - reflexivity.
  - apply IHx.
  - apply IHx.
Qed.

Lemma mul_append : forall {sz1 sz2} (x y : word sz1) (z : word sz2),
  mul x (append y z) = mul x y.
Proof.
  intros.
  rewrite <- mul_take, take_append.
  reflexivity.
Qed.

Fixpoint nat_add_assoc n m p : (n + m + p = n + (m + p))%nat :=
  match n with
  | O => eq_refl
  | S n => f_equal S (nat_add_assoc n m p)
  end.

Lemma append_assoc_1' : forall {sz1 sz2 sz3} (x : word sz1) (y : word sz2) (z : word sz3),
  append x (append y z) = eq_rect _ word (append (append x y) z) _ (nat_add_assoc _ _ _).
Proof.
  intros sz1 sz2 sz3 x y z.
  induction x.
  - reflexivity.
  - cbn. rewrite map_subst_map. f_equal. apply IHx.
  - cbn. rewrite map_subst_map. f_equal. apply IHx.
Qed.

Lemma append_assoc_1 : forall {sz1 sz2 sz3} (x : word sz1) (y : word sz2) (z : word sz3),
  forall (pf : (sz1 + sz2 + sz3 = sz1 + (sz2 + sz3))%nat),
  append x (append y z) = eq_rect _ word (append (append x y) z) _ pf.
Proof.
  intros sz1 sz2 sz3 x y z pf.
  rewrite Eqdep_dec.UIP_dec with (p1 := pf) (p2 := nat_add_assoc _ _ _) by apply Nat.eq_dec.
  apply append_assoc_1'.
Qed.

Lemma append_assoc_2' : forall {sz1 sz2 sz3} (x : word sz1) (y : word sz2) (z : word sz3),
  append (append x y) z = eq_rect_r word (append x (append y z)) (nat_add_assoc _ _ _).
Proof.
  unfold eq_rect_r.
  intros sz1 sz2 sz3 x y z.
  induction x.
  - reflexivity.
  - cbn. rewrite eq_sym_map_distr, map_subst_map. f_equal. apply IHx.
  - cbn. rewrite eq_sym_map_distr, map_subst_map. f_equal. apply IHx.
Qed.

Lemma append_assoc_2 : forall {sz1 sz2 sz3} (x : word sz1) (y : word sz2) (z : word sz3),
  forall (pf : (sz1 + (sz2 + sz3) = sz1 + sz2 + sz3)%nat),
  append (append x y) z = eq_rect _ word (append x (append y z)) _ pf.
Proof.
  intros sz1 sz2 sz3 x y z pf.
  rewrite Eqdep_dec.UIP_dec with (p1 := pf) (p2 := eq_sym (nat_add_assoc _ _ _)) by apply Nat.eq_dec.
  apply append_assoc_2'.
Qed.

Fixpoint nat_add_zero_r n : n = (n + 0)%nat :=
  match n with
  | O => eq_refl
  | S n => f_equal S (nat_add_zero_r n)
  end.

Lemma sext_zero : forall {sz} (x : word sz),
  sext x 0 = eq_rect _ word x _ (nat_add_zero_r sz).
Proof.
  intros sz x.
  induction x.
  - reflexivity.
  - destruct sz; cbn.
    + apply f_equal, word_0_eq.
    + cbn. rewrite map_subst_map. f_equal. apply IHx.
  - destruct sz; cbn.
    + apply f_equal, word_0_eq.
    + cbn. rewrite map_subst_map. f_equal. apply IHx.
Qed.

Lemma eq_rect_append_distr_l : forall {sz1 sz1' sz2}
    (x : word sz1) (y : word sz2) (pf : sz1 = sz1'),
  eq_rect _ word (append x y) _ (f_equal (fun sz => (sz + sz2)%nat) pf)
  = append (eq_rect _ word x _ pf) y.
Proof.
  intros.
  apply map_subst_map with (f := fun sz => (sz + sz2)%nat)
                           (g := fun sz (z : word sz) => append z y).
Qed.

Lemma mul_sext_add : forall {sz1 sz2 sz3} (x : word (sz1 + sz2)) (y : word sz2),
  mul x (sext y (sz1 + sz3)) = mul x (sext y sz1).
Proof.
  intros sz1 sz2 sz3 x y.
  rewrite sext_spec, sext_spec.
  destruct (msb' y).
  - rewrite ones_len_add, append_assoc_1', mul_eq_rect.
    rewrite <- mul_eq_rect with (H := f_equal (fun x => (x + sz3)%nat) (Nat.add_comm sz2 sz1)).
    rewrite eq_rect_append_distr_l, mul_append, mul_eq_rect.
    reflexivity.
  - rewrite zero_len_add, append_assoc_1', mul_eq_rect.
    rewrite <- mul_eq_rect with (H := f_equal (fun x => (x + sz3)%nat) (Nat.add_comm sz2 sz1)).
    rewrite eq_rect_append_distr_l, mul_append, mul_eq_rect.
    reflexivity.
Qed.


Lemma mul_sext_r : forall {sz} (x y : word sz) n,
  mul x (sext y n) = mul x y.
Proof.
  intros sz x y n.
  rewrite sext_spec.
  apply mul_append.
Qed.

Lemma sext_W0 : forall {sz} (x : word sz) n,
  sext x~0 n = (sext x n)~0.
Proof.
  intros sz x n.
  destruct x; reflexivity.
Qed.

Lemma sext_W1 : forall {sz} (x : word sz) n,
  sext x~1 n = (match sz as sz', x in word sz' return word (sz' + n)%nat with
                | 0, _ => ones n
                | S _, x => sext x n
                end)~1.
Proof.
  intros sz x n.
  destruct x; reflexivity.
Qed.

Lemma mul_sext_spec : forall {sz1 sz2} (x : word sz1) (y : word sz2),
  mul_sext x y = mul (sext x sz2) (sext y sz1).
Proof.
  intros sz1 sz2 x.
  generalize dependent sz2.
  induction x; intros sz2 y.
  - cbn. apply eq_sym, mul_zero_l.
  - destruct sz; cbn; f_equal.
    + apply eq_sym, mul_zero_l.
    + eapply eq_trans; [apply IHx|].
      rewrite <- (Nat.add_1_r (S sz)).
      apply eq_sym, (mul_sext_add (sext x sz2)).
  - destruct sz; cbn; destruct y.
    + reflexivity.
    + rewrite sext_W0 at 1 2.
      f_equal. f_equal.
      apply eq_sym, mul_sext_r.
    + destruct sz; [reflexivity|].
      rewrite sext_W1 at 1 2.
      f_equal. f_equal.
      apply eq_sym, mul_sext_r.
    + cbn. f_equal. f_equal.
      (* cursed cursed cursed *)
      change (zero sz)~0~0 with (zero (S (S sz))).
      rewrite mul_zero_r.
      change (S (sz + 0)%nat) with (S sz + 0)%nat.
      rewrite <- @mul_zero_r with (x := sext x 0) (m := S sz).
      apply IHx.
    + rewrite sext_W0 at 1 2.
      f_equal. f_equal.
      replace (S (S sz)) with (S sz + 1)%nat by apply Nat.add_1_r.
      rewrite mul_sext_add with (x := sext x (S sz0)).
      apply IHx.
    + rewrite sext_W1 at 1 2.
      f_equal. f_equal.
      replace (S (S sz)) with (S sz + 1)%nat by apply Nat.add_1_r.
      rewrite mul_sext_add with (x := sext x (S sz0)).
      apply IHx.
Qed.

Lemma take_succ : forall {sz1 sz2} (x : word (sz1 + sz2)%nat),
  take sz1 (succ x) = succ (take sz1 x).
Proof.
  intros sz1.
  induction sz1; intros sz2 x.
  - reflexivity.
  - cbn in x.
    destruct_word x; cbn; f_equal.
    apply IHsz1.
Qed.

Lemma take_add : forall {sz1 sz2} (x : word (sz1 + sz2)%nat) {sz3} (y : word sz3),
  take sz1 (add x y) = add (take sz1 x) y.
Proof.
  intros sz1.
  induction sz1; intros sz2 x sz3 y.
  - reflexivity.
  - cbn in x.
    destruct_word x; destruct y; cbn; f_equal.
    + apply IHsz1.
    + apply IHsz1.
    + apply IHsz1.
    + rewrite add_carry_succ, add_carry_succ.
      rewrite take_succ.
      f_equal.
      apply IHsz1.
Qed.

Lemma take_mul : forall {sz1 sz2} (x : word (sz1 + sz2)%nat) {sz3} (y : word sz3),
  take sz1 (mul x y) = mul (take sz1 x) y.
Proof.
  intros sz1.
  induction sz1; intros sz2 x sz3 y.
  - reflexivity.
  - cbn in x.
    destruct_word x.
    + cbn. f_equal. apply IHsz1.
    + destruct y; cbn; f_equal.
      * apply IHsz1.
      * rewrite take_add.
        f_equal.
        apply IHsz1.
      * rewrite take_add.
        f_equal.
        apply IHsz1.
Qed.

Lemma take_mul_ext : forall {sz1} (x : word sz1) {sz2} (y : word sz2),
  take sz1 (mul_ext x y) = mul x y.
Proof.
  intros.
  rewrite mul_ext_spec, take_mul, zext_spec, take_append.
  reflexivity.
Qed.


Lemma nat_le_split : forall (n m : nat), (n <= m -> exists p, n + p = m)%nat.
Proof.
  intros n m.
  induction m; intros H.
  - exists 0. inversion H. reflexivity.
  - inversion H.
    + exists 0. apply Nat.add_0_r.
    + apply IHm in H1 as [p H1].
      exists (S p).
      rewrite Nat.add_succ_r.
      f_equal.
      apply H1.
Qed.

Lemma take_mul_sext : forall {sz1} (x : word sz1) {sz2} (y : word sz2),
  take sz1 (mul_sext x y) = mul x (sext y (sz1 - sz2)%nat).
Proof.
  intros.
  rewrite mul_sext_spec, take_mul, sext_spec, take_append.
  destruct (Nat.le_gt_cases sz2 sz1).
  - generalize x. clear x.
    replace (sext y sz1) with
      (eq_rect _ word (sext y (sz1 - sz2 + sz2)) (sz2 + sz1)%nat
              (f_equal _ (Nat.sub_add sz2 sz1 H)))
      by (rewrite Nat.sub_add; reflexivity).
    rewrite <- Nat.sub_add with (n := sz2) (m := sz1) by apply H.
    rewrite Nat.add_sub.
    intros x.
    rewrite mul_eq_rect, sext_spec, sext_spec.
    destruct (msb' y).
    + rewrite ones_len_add.
      rewrite append_assoc_1', mul_eq_rect.
      rewrite <- mul_eq_rect
        with (H := f_equal (fun x => (x + sz2)%nat) (Nat.add_comm sz2 (sz1 - sz2)%nat)).
      rewrite eq_rect_append_distr_l, mul_append, mul_eq_rect.
      reflexivity.
    + rewrite zero_len_add.
      rewrite append_assoc_1', mul_eq_rect.
      rewrite <- mul_eq_rect
        with (H := f_equal (fun x => (x + sz2)%nat) (Nat.add_comm sz2 (sz1 - sz2)%nat)).
      rewrite eq_rect_append_distr_l, mul_append, mul_eq_rect.
      reflexivity.
  - apply Nat.lt_le_incl, nat_le_split in H as H'.
    destruct H' as [sz3 Heq].
    apply Nat.sub_0_le in H.
    rewrite H.
    generalize y. clear y.
    rewrite <- Heq.
    intros y.
    rewrite sext_zero, mul_eq_rect.
    rewrite <- append_split with (w := y), sext_spec.
    rewrite append_assoc_2'.
    unfold eq_rect_r.
    rewrite mul_eq_rect.
    rewrite mul_append, mul_append.
    reflexivity.
Qed.


End Word.

Add Ring word8_ring : (Word.WordRing 8) (decidable (fun x y => (proj1 (@Word.eqb_eq 8 x y)))).
Add Ring word16_ring : (Word.WordRing 16) (decidable (fun x y => (proj1 (@Word.eqb_eq 16 x y)))).
Add Ring word32_ring : (Word.WordRing 32) (decidable (fun x y => (proj1 (@Word.eqb_eq 32 x y)))).
Add Ring word64_ring : (Word.WordRing 64) (decidable (fun x y => (proj1 (@Word.eqb_eq 64 x y)))).
Add Ring word128_ring : (Word.WordRing 128) (decidable (fun x y => (proj1 (@Word.eqb_eq 128 x y)))).

Infix "+" := Word.add : word_scope.
Infix "-" := Word.sub : word_scope.
Infix "*" := Word.mul : word_scope.
(*Infix "^" := Word.pow : word_scope.*)

Infix "?=" := Word.compare (at level 70, no associativity) : word_scope.
Infix "?s=" := Word.scompare (at level 70, no associativity) : word_scope.

Infix "<=" := Word.le : word_scope.
Infix "<" := Word.lt : word_scope.

(*
Infix "<=s" := Word.sle : word_scope.
Infix "<s" := Word.slt : word_scope.
*)

Infix "=?" := Word.eqb (at level 70, no associativity) : word_scope.
Infix "<=?" := Word.leb (at level 70, no associativity) : word_scope.
Infix "<?" := Word.ltb (at level 70, no associativity) : word_scope.

Notation "x <= y <= z" := (x <= y /\ y <= z) : word_scope.
Notation "x <= y < z" := (x <= y /\ y < z) : word_scope.
Notation "x < y < z" := (x < y /\ y < z) : word_scope.
Notation "x < y <= z" := (x < y /\ y <= z) : word_scope.

Ltac destruct_word x := Word.destruct_word x.



Module N2Word.

Lemma id : forall {n} (x : word n),
  Word.of_N (Word.to_N x) = x.
Proof.
  intros n x.
  induction x.
  - reflexivity.
  - simpl. destruct (Word.to_N x).
    + rewrite <- IHx. reflexivity.
    + rewrite <- IHx. reflexivity.
  - simpl. destruct (Word.to_N x).
    + rewrite <- IHx. reflexivity.
    + rewrite <- IHx. reflexivity.
Qed.

Lemma eq_0_iff : forall {n} x,
  @Word.of_N n x = Word.zero n <-> Ntruncate n x = 0%N.
Proof.
  intros n.
  induction n; intros x.
  - split; reflexivity.
  - cbn. destruct (N.odd x); split; intros H.
    + discriminate.
    + exfalso.
      eapply Nsucc_double_not_0, H.
    + apply (@f_equal _ _ N.double _ (N.double 0%N)), IHn, Word.W0_inj, H.
    + apply f_equal, IHn, N.double_inj, H.
Qed.

Lemma inj_iff' : forall {n} (x y : N),
  @Word.of_N n x = @Word.of_N n y <-> Ntruncate n x = Ntruncate n y.
Proof.
  intros n.
  induction n; intros x y.
  - split; reflexivity.
  - cbn. destruct (N.odd x), (N.odd y); cbn; split; intros H.
    + apply f_equal, IHn, Word.W1_inj, H.
    + apply f_equal, IHn, N.succ_double_inj, H.
    + discriminate H.
    + exfalso.
      eapply Ndouble_neq_succ_double, eq_sym, H.
    + discriminate H.
    + exfalso.
      eapply Ndouble_neq_succ_double, H.
    + apply f_equal, IHn, Word.W0_inj, H.
    + apply f_equal, IHn, N.double_inj, H.
Qed.

Lemma inj_iff : forall {n} (x y : N),
  @Word.of_N n x = @Word.of_N n y <-> (x mod 2 ^ N.of_nat n = y mod 2 ^ N.of_nat n)%N.
Proof.
  intros.
  rewrite <- Ntruncate_mod_pow_2, <- Ntruncate_mod_pow_2.
  apply inj_iff'.
Qed.

Lemma inj_0 : forall {n}, @Word.of_N n 0%N = Word.zero n.
Proof.
  intros n.
  induction n.
  - reflexivity.
  - cbn. f_equal. apply IHn.
Qed.

Lemma inj_1 : forall {n}, @Word.of_N (S n) 1%N = Word.one n.
Proof.
  intros n.
  cbn.
  rewrite inj_0.
  reflexivity.
Qed.

Lemma inj_succ : forall {n} (x : N),
  @Word.of_N n (N.succ x) = Word.succ (@Word.of_N n x).
Proof.
  intros n.
  induction n; intros x.
  - reflexivity.
  - cbn.
    rewrite N.odd_succ, <- N.negb_odd, Ndiv2_succ_distr.
    destruct (N.odd x); cbn; f_equal.
    + rewrite N.add_1_r.
      apply IHn.
    + rewrite N.add_0_r.
      reflexivity.
Qed.

Lemma inj_add : forall {n} (x y : N),
  @Word.of_N n (x + y)%N = Word.add (@Word.of_N n x) (@Word.of_N n y).
Proof.
  intros n.
  induction n; intros x y.
  - reflexivity.
  - cbn.
    rewrite N.odd_add, Ndiv2_add_distr.
    destruct (N.odd x), (N.odd y); cbn; f_equal.
    + rewrite N.add_1_r, inj_succ, Word.add_carry_succ. f_equal. apply IHn.
    + rewrite N.add_0_r. apply IHn.
    + rewrite N.add_0_r. apply IHn.
    + rewrite N.add_0_r. apply IHn.
Qed.

Lemma inj_double : forall {n} (x : N),
  @Word.of_N n (N.double x) = Word.double (@Word.of_N n x).
Proof.
  intros n.
  induction n; intros x.
  - reflexivity.
  - cbn.
    rewrite Ndouble_not_odd, N.div2_double.
    destruct (N.odd x) eqn:Ex.
    + cbn. f_equal. rewrite <- IHn, <- inj_succ, <- Nsucc_double_spec'.
      rewrite Nsucc_double_div2, <- N.negb_odd, Ex, N.add_0_r.
      reflexivity.
    + cbn. f_equal. rewrite <- IHn, Ndouble_div2, Ex, N.sub_0_r.
      reflexivity.
Qed.

Lemma inj_mul : forall {n} (x y : N),
  @Word.of_N n (x * y)%N = Word.mul (@Word.of_N n x) (@Word.of_N n y).
Proof.
  intros n.
  induction n; intros x y.
  - reflexivity.
  - cbn.
    rewrite N.odd_mul.
    destruct (N.odd x) eqn:Ex, (N.odd y) eqn:Ey; cbn; f_equal.
    + rewrite Word.mul_W1_r, Ndiv2_mul_distr, Ex, Ey, N.mul_1_l, N.mul_1_l.
      rewrite inj_add, inj_add, inj_double.
      f_equal. f_equal. f_equal.
      apply IHn.
    + rewrite Word.mul_W0_r, Ndiv2_mul_distr, Ex, Ey, N.mul_1_l, N.add_0_r.
      rewrite inj_add, inj_double.
      f_equal. f_equal.
      apply IHn.
    + rewrite Word.mul_W1_r, Ndiv2_mul_distr, Ex, Ey, N.add_0_r, N.mul_1_l.
      rewrite inj_add, inj_double.
      f_equal. f_equal.
      apply IHn.
    + rewrite Word.mul_W0_r, Ndiv2_mul_distr, Ex, Ey, N.add_0_r, N.add_0_r.
      rewrite inj_double.
      f_equal.
      apply IHn.
Qed.


Lemma inj_mul_ext : forall {n m} (x y : N),
  @Word.of_N (n + m) (x * y)%N = Word.mul_ext (@Word.of_N n x) (@Word.of_N m y).
Proof.
Abort.

End N2Word.



Module Word2N.

Lemma inj_iff : forall {n} (x y : word n),
  Word.to_N x = Word.to_N y <-> x = y.
Proof.
  intros n.
  induction n; intros x y.
  - Word.destruct_word_0 x.
    Word.destruct_word_0 y.
    split; reflexivity.
  - Word.destruct_word_S x;
    Word.destruct_word_S y;
    cbn; split; intros H.
    + f_equal. apply IHn, N.double_inj, H.
    + f_equal. apply IHn, Word.W0_inj, H.
    + destruct (Word.to_N x); destruct (Word.to_N y); discriminate.
    + discriminate.
    + destruct (Word.to_N x); destruct (Word.to_N y); discriminate.
    + discriminate.
    + f_equal. apply IHn, N.succ_double_inj, H.
    + f_equal. apply IHn, Word.W1_inj, H.
Qed.

Lemma inj_0 : forall {n}, Word.to_N (Word.zero n) = 0%N.
Proof.
  intros n.
  induction n.
  - reflexivity.
  - cbn. rewrite IHn. reflexivity.
Qed.

Lemma inj_1 : forall {n}, Word.to_N (Word.one n) = 1%N.
Proof.
  intros n.
  cbn.
  rewrite inj_0.
  reflexivity.
Qed.

Lemma id' : forall {n} (x : N),
  Word.to_N (@Word.of_N n x) = Ntruncate n x.
Proof.
  intros n.
  induction n; intros x.
  - reflexivity.
  - cbn.
    destruct (N.odd x).
    + cbn. f_equal. apply IHn.
    + cbn. f_equal. apply IHn.
Qed.

Lemma id : forall {n} (x : N),
  Word.to_N (@Word.of_N n x) = (x mod 2 ^ N.of_nat n)%N.
Proof.
  intros.
  rewrite <- Ntruncate_mod_pow_2.
  apply id'.
Qed.

Lemma truncate_to_N : forall {n} (x : word n),
  Ntruncate n (Word.to_N x) = Word.to_N x.
Proof.
  intros n.
  induction n; intros x.
  - Word.destruct_word_0 x. reflexivity.
  - Word.destruct_word_S x; cbn.
    + rewrite Ndouble_not_odd, N.div2_double.
      apply f_equal, IHn.
    + rewrite Nsucc_double_odd, N.div2_succ_double.
      apply f_equal, IHn.
Qed.

Lemma inj_succ' : forall {n} (x : word n),
  Word.to_N (Word.succ x) = Ntruncate n (N.succ (Word.to_N x)).
Proof.
  intros n.
  induction n; intros x.
  - Word.destruct_word_0 x. reflexivity.
  - Word.destruct_word_S x; cbn.
    + rewrite N.odd_succ, Ndouble_even.
      rewrite <- Nsucc_double_spec', N.div2_succ_double.
      apply f_equal, eq_sym, truncate_to_N.
    + rewrite N.odd_succ, Nsucc_double_not_even.
      rewrite Nsucc_double_spec', <- Ndouble_succ_distr, N.div2_double.
      f_equal.
      apply IHn.
Qed.

Lemma inj_add' : forall {n m} (x : word n) (y : word m),
  Word.to_N (Word.add x y) = Ntruncate n (Word.to_N x + Word.to_N y)%N.
Proof.
  intros n.
  induction n; intros m x y.
  - Word.destruct_word_0 x.
    reflexivity.
  - Word.destruct_word_S x;
    destruct y;
    cbn.
    + rewrite N.add_0_r, Ndouble_not_odd, N.div2_double, truncate_to_N.
      reflexivity.
    + rewrite <- N.double_add, Ndouble_not_odd, N.div2_double.
      apply f_equal, IHn.
    + rewrite <- N.succ_double_add, Nsucc_double_odd, N.div2_succ_double.
      apply f_equal, IHn.
    + rewrite N.add_0_r, Nsucc_double_odd, N.div2_succ_double, truncate_to_N.
      reflexivity.
    + rewrite N.add_comm, <- N.succ_double_add, N.add_comm, Nsucc_double_odd, N.div2_succ_double.
      apply f_equal, IHn.
    + rewrite N.succ_double_spec, <- (N.double_spec (Word.to_N x)), N.add_1_r, N.add_succ_l.
      rewrite N.succ_double_spec, <- (N.double_spec (Word.to_N y)), N.add_1_r, N.add_succ_r.
      rewrite <- N.double_add, N.odd_succ, N.even_succ, Ndouble_not_odd.
      rewrite Nsucc_div2_distr, N.div2_double.
      rewrite Word.add_carry_succ, inj_succ', IHn.
      apply f_equal, Nsucc_truncate_idemp.
Qed.

Lemma inj_add : forall {n m} (x : word n) (y : word m),
  Word.to_N (Word.add x y) = ((Word.to_N x + Word.to_N y) mod 2 ^ N.of_nat n)%N.
Proof.
  intros.
  rewrite <- Ntruncate_mod_pow_2.
  apply inj_add'.
Qed.

Lemma inj_double' : forall {n} (x : word n),
  Word.to_N (Word.double x) = Ntruncate n (N.double (Word.to_N x)).
Proof.
  intros n.
  induction n; intros x.
  - Word.destruct_word_0 x. reflexivity.
  - cbn. rewrite Ndouble_not_odd, N.div2_double.
    Word.destruct_word_S x; cbn; f_equal.
    + apply IHn.
    + rewrite Nsucc_double_spec', <- Nsucc_truncate_idemp, inj_succ'.
      f_equal. f_equal. apply IHn.
Qed.

Lemma inj_double : forall {n} (x : word n),
  Word.to_N (Word.double x) = (N.double (Word.to_N x) mod 2 ^ N.of_nat n)%N.
Proof.
  intros.
  rewrite <- Ntruncate_mod_pow_2.
  apply inj_double'.
Qed.

Lemma inj_mul' : forall {n m} (x : word n) (y : word m),
  Word.to_N (Word.mul x y) = Ntruncate n (Word.to_N x * Word.to_N y)%N.
Proof.
  intros n.
  induction n; intros m x y.
  - Word.destruct_word_0 x. reflexivity.
  - Word.destruct_word_S x;
    destruct y;
    cbn.
    + rewrite N.mul_0_r. cbn.
      rewrite Word.mul_Wnil_r, inj_0, Ntruncate_0.
      reflexivity.
    + rewrite <- N.double_mul, Ndouble_not_odd, N.div2_double.
      apply f_equal, IHn.
    + rewrite <- N.double_mul, Ndouble_not_odd, N.div2_double.
      apply f_equal, IHn.
    + rewrite N.mul_0_r. cbn.
      rewrite Word.mul_Wnil_r, inj_0, Ntruncate_0.
      reflexivity.
    + rewrite N.mul_comm, <- N.double_mul, Ndouble_not_odd, N.div2_double, N.mul_comm.
      f_equal.
      rewrite N.succ_double_mul, <- N.double_mul, N.mul_comm, N.double_mul, N.mul_comm.
      rewrite inj_add', IHn.
      apply Nadd_truncate_idemp_l.
    + rewrite N.succ_double_mul, <- N.double_mul.
      rewrite N.odd_add, Ndouble_not_odd, Nsucc_double_odd.
      cbn. f_equal.
      rewrite <- N.succ_double_add, N.div2_succ_double.
      rewrite inj_add', IHn.
      apply Nadd_truncate_idemp_l.
Qed.

Lemma inj_mul : forall {n m} (x : word n) (y : word m),
  Word.to_N (Word.mul x y) = ((Word.to_N x * Word.to_N y) mod 2 ^ (N.of_nat n))%N.
Proof.
  intros.
  rewrite <- Ntruncate_mod_pow_2.
  apply inj_mul'.
Qed.

Lemma inj_zext : forall {sz1} (x : word sz1) sz2,
  Word.to_N (Word.zext x sz2) = Word.to_N x.
Proof.
  intros sz1 x sz2.
  induction x.
  - apply inj_0.
  - cbn. f_equal. apply IHx.
  - cbn. f_equal. apply IHx.
Qed.

Lemma to_N_lt : forall {sz} (x : word sz),
  (Word.to_N x < 2 ^ N.of_nat sz)%N.
Proof.
  intros sz x.
  induction x.
  - apply N.lt_0_1.
  - rewrite Nat2N.inj_succ.
    cbn.
    rewrite N.pow_succ_r', N.double_spec.
    apply N.mul_lt_mono_pos_l; [apply N.lt_0_2|].
    apply IHx.
  - rewrite Nat2N.inj_succ.
    cbn.
    rewrite N.pow_succ_r', N.succ_double_spec.
    apply N.double_above, IHx.
Qed.

Lemma inj_mul_ext : forall {n m} (x : word n) (y : word m),
  Word.to_N (Word.mul_ext x y) = (Word.to_N x * Word.to_N y)%N.
Proof.
  intros n m x y.
  rewrite Word.mul_ext_spec, inj_mul, inj_zext.
  apply N.mod_small.
  rewrite Nat2N.inj_add, N.pow_add_r.
  apply N.mul_lt_mono; apply to_N_lt.
Qed.

End Word2N.



Module Z2Word.

Lemma id : forall {n} (x : word n),
  Word.of_Z (Word.to_Z x) = x.
Proof.
  intros sz x.
  induction x.
  - reflexivity.
  - cbn. destruct sz.
    + cbn. f_equal. apply IHx.
    + rewrite Zdouble_not_odd, Zdiv2_double.
      f_equal. apply IHx.
  - cbn. destruct sz.
    + cbn. f_equal. apply IHx.
    + rewrite Zsucc_double_odd, Zdiv2_succ_double.
      f_equal. apply IHx.
Qed.

Lemma eq_0_iff : forall {sz} x,
  @Word.of_Z sz x = Word.zero sz <-> Ztruncate sz x = 0%Z.
Proof.
  intros sz.
  induction sz; intros x.
  - split; reflexivity.
  - cbn. destruct (Z.odd x); split; intros H.
    + discriminate.
    + destruct sz; [discriminate|].
      exfalso.
      eapply Zsucc_double_not_zero, H.
    + destruct sz; [reflexivity|].
      apply (@f_equal _ _ Z.double _ (Z.double 0%Z)), IHsz, Word.W0_inj, H.
    + f_equal. apply IHsz.
      destruct sz; [reflexivity|].
      apply Zdouble_inj, H.
Qed.

Lemma inj_iff' : forall {sz} (x y : Z),
  @Word.of_Z sz x = @Word.of_Z sz y <-> Ztruncate sz x = Ztruncate sz y.
Proof.
  intros sz.
  induction sz; intros x y.
  - split; reflexivity.
  - cbn.
    destruct (Z.odd x), (Z.odd y).
    + destruct sz; [split; reflexivity|].
      split; intros H; f_equal.
      * apply IHsz, Word.W1_inj, H.
      * apply IHsz, Zsucc_double_inj, H.
    + split; [discriminate|].
      destruct sz; [discriminate|].
      intros H. exfalso. eapply Zdouble_neq_succ_double, eq_sym, H.
    + split; [discriminate|].
      destruct sz; [discriminate|].
      intros H. exfalso. eapply Zdouble_neq_succ_double, H.
    + destruct sz; [split; reflexivity|].
      split; intros H; f_equal.
      * apply IHsz, Word.W0_inj, H.
      * apply IHsz, Zdouble_inj, H.
Qed.

Lemma inj_iff : forall {sz} (x y : Z),
  @Word.of_Z (S sz) x = @Word.of_Z (S sz) y <->
  ((x + 2 ^ Z.of_nat sz) mod 2 ^ Z.of_nat (S sz) - 2 ^ Z.of_nat sz =
   (y + 2 ^ Z.of_nat sz) mod 2 ^ Z.of_nat (S sz) - 2 ^ Z.of_nat sz)%Z.
Proof.
  intros sz x y.
  rewrite <- Ztruncate_wrap, <- Ztruncate_wrap.
  apply inj_iff'.
Qed.

Lemma inj_0 : forall {sz}, @Word.of_Z sz 0%Z = Word.zero sz.
Proof.
  intros sz.
  induction sz.
  - apply Word.word_0_eq.
  - cbn. f_equal. apply IHsz.
Qed.

Lemma inj_1 : forall {sz}, @Word.of_Z (S sz) 1%Z = Word.one sz.
Proof.
  intros sz.
  destruct sz.
  - reflexivity.
  - cbn. unfold Word.one. f_equal. cbn. f_equal. apply inj_0.
Qed.

Lemma inj_minus_1 : forall {sz}, @Word.of_Z sz (-1)%Z = Word.ones sz.
Proof.
  intros sz.
  induction sz.
  - reflexivity.
  - cbn. f_equal. apply IHsz.
Qed.

Lemma inj_succ : forall {sz} (x : Z),
  @Word.of_Z sz (Z.succ x) = Word.succ (@Word.of_Z sz x).
Proof.
  intros sz.
  induction sz; intros x.
  - reflexivity.
  - cbn.
    rewrite Z.odd_succ, <- Z.negb_odd, Zdiv2_succ_distr.
    destruct (Z.odd x); cbn; f_equal.
    + rewrite Z.add_1_r.
      apply IHsz.
    + rewrite Z.add_0_r.
      reflexivity.
Qed.

Lemma inj_pred : forall {sz} (x : Z),
  @Word.of_Z sz (Z.pred x) = Word.pred (@Word.of_Z sz x).
Proof.
  intros sz.
  induction sz; intros x.
  - reflexivity.
  - cbn. rewrite Z.odd_pred, Zdiv2_pred, <- Z.negb_odd.
    destruct (Z.odd x); cbn; f_equal.
    + rewrite Z.sub_0_r. reflexivity.
    + rewrite Z.sub_1_r. apply IHsz.
Qed.

Lemma inj_opp : forall {sz} (x : Z),
  @Word.of_Z sz (Z.opp x) = Word.opp (@Word.of_Z sz x).
Proof.
  intros sz.
  induction sz; intros x.
  - reflexivity.
  - cbn. rewrite Z.odd_opp, Z.div2_div, Z.div2_div.
    destruct (Z.odd x) eqn:E; cbn; f_equal.
    + rewrite Z.div_opp_l_nz; [|discriminate|rewrite Zmod_odd, E; discriminate].
      rewrite Z.sub_1_r, inj_pred, <- Word.pred_succ.
      f_equal. apply IHsz.
    + rewrite Z.div_opp_l_z; [|discriminate|rewrite Zmod_odd, E; reflexivity].
      apply IHsz.
Qed.

Lemma inj_add : forall {sz} (x y : Z),
  @Word.of_Z sz (x + y)%Z = Word.add (@Word.of_Z sz x) (@Word.of_Z sz y).
Proof.
  intros sz.
  induction sz; intros x y.
  - reflexivity.
  - cbn.
    rewrite Z.odd_add, Zdiv2_add_distr.
    destruct (Z.odd x), (Z.odd y); cbn; f_equal.
    + rewrite Z.add_1_r, inj_succ, Word.add_carry_succ. f_equal. apply IHsz.
    + rewrite Z.add_0_r. apply IHsz.
    + rewrite Z.add_0_r. apply IHsz.
    + rewrite Z.add_0_r. apply IHsz.
Qed.

Lemma Zdouble_div2 : forall (x : Z),
  Z.double (Z.div2 x) = (x - Z.b2z (Z.odd x))%Z.
Proof.
  intros x.
  destruct x.
  - reflexivity.
  - destruct p; reflexivity.
  - destruct p; reflexivity.
  Qed.

Lemma inj_double : forall {sz} (x : Z),
  @Word.of_Z sz (Z.double x) = Word.double (@Word.of_Z sz x).
Proof.
  intros sz.
  induction sz; intros x.
  - reflexivity.
  - cbn.
    rewrite Zdouble_not_odd, Zdiv2_double.
    destruct (Z.odd x) eqn:Ex.
    + cbn. f_equal. rewrite <- IHsz, <- inj_succ.
      f_equal.
      rewrite Zdouble_div2, Ex.
      cbn. rewrite Z.sub_1_r, Z.succ_pred.
      reflexivity.
    + cbn. f_equal. rewrite <- IHsz.
      f_equal.
      rewrite Zdouble_div2, Ex.
      cbn.
      rewrite Z.sub_0_r.
      reflexivity.
Qed.

Lemma Zdiv2_mul_distr_l : forall (x y : Z),
  Z.div2 (x * y)%Z = (Z.div2 x * y + Z.b2z (Z.odd x) * Z.div2 y)%Z.
Proof.
  intros x y.
  rewrite (Z.div2_odd x) at 1.
  rewrite Z.mul_add_distr_r, Zdiv2_add_distr.
  rewrite <- Z.mul_assoc, <- Z.double_spec.
  rewrite Zdiv2_double, Zdouble_not_odd.
  rewrite Z.add_0_r.
  unfold Z.b2z.
  destruct (Z.odd x).
  - rewrite 2 Z.mul_1_l.
    reflexivity.
  - rewrite 2 Z.mul_0_l.
    reflexivity.
Qed.

Lemma Zdiv2_mul_distr : forall (x y : Z),
  Z.div2 (x * y)%Z =
  (Z.double (Z.div2 x * Z.div2 y)
   + Z.b2z (Z.odd y) * Z.div2 x
   + Z.b2z (Z.odd x) * Z.div2 y)%Z.
Proof.
  intros.
  rewrite Zdiv2_mul_distr_l.
  rewrite (Z.div2_odd y) at 1.
  rewrite Z.mul_add_distr_l.
  rewrite Z.mul_assoc, (Z.mul_comm _ 2), <- Z.mul_assoc, <- Z.double_spec.
  rewrite (Z.mul_comm _ (Z.b2z _)).
  reflexivity.
Qed.

Lemma inj_mul : forall {sz} (x y : Z),
  @Word.of_Z sz (x * y)%Z = Word.mul (@Word.of_Z sz x) (@Word.of_Z sz y).
Proof.
  intros sz.
  induction sz; intros x y.
  - reflexivity.
  - cbn.
    rewrite Z.odd_mul.
    destruct (Z.odd x) eqn:Ex, (Z.odd y) eqn:Ey; cbn; f_equal.
    + rewrite Word.mul_W1_r, Zdiv2_mul_distr, Ex, Ey, Z.mul_1_l, Z.mul_1_l.
      rewrite inj_add, inj_add, inj_double.
      f_equal. f_equal. f_equal.
      apply IHsz.
    + rewrite Word.mul_W0_r, Zdiv2_mul_distr, Ex, Ey, Z.mul_1_l, Z.add_0_r.
      rewrite inj_add, inj_double.
      f_equal. f_equal.
      apply IHsz.
    + rewrite Word.mul_W1_r, Zdiv2_mul_distr, Ex, Ey, Z.add_0_r, Z.mul_1_l.
      rewrite inj_add, inj_double.
      f_equal. f_equal.
      apply IHsz.
    + rewrite Word.mul_W0_r, Zdiv2_mul_distr, Ex, Ey, Z.add_0_r, Z.add_0_r.
      rewrite inj_double.
      f_equal.
      apply IHsz.
Qed.

End Z2Word.



Module Word2Z.
End Word2Z.

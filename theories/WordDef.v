Require Import NArith ZArith.

Inductive word : nat -> Type :=
| Wnil : word 0
| W0 : forall {sz}, word sz -> word (S sz)
| W1 : forall {sz}, word sz -> word (S sz).

Declare Scope word_scope.
Delimit Scope word_scope with word.
Bind Scope word_scope with word.

Notation "w ~ 1" := (W1 w)
 (at level 7, left associativity, format "w '~' '1'") : word_scope.
Notation "w ~ 0" := (W0 w)
 (at level 7, left associativity, format "w '~' '0'") : word_scope.

Local Open Scope word_scope.

Module Word.

Definition t {sz} := word sz.

Definition case0 (P : word 0 -> Type) (H : P Wnil) x : P x :=
  match x in word 0 with
  | Wnil => H
  end.

Definition caseS {sz} (x : word (S sz)) :
    forall (P : word (S sz) -> Type)
           (H0 : forall x, P (@W0 sz x))
           (H1 : forall x, P (@W1 sz x)),
      P x :=
  match x with
  | W0 t => fun P H0 H1 => H0 t
  | W1 t => fun P H0 H1 => H1 t
  end.

Definition caseS' {sz} P H0 H1 (x : word (S sz)) := caseS x P H0 H1.

Fixpoint zero sz :=
  match sz with
  | 0 => Wnil
  | S sz => W0 (zero sz)
  end.

Definition one sz :=
  W1 (zero sz).

Definition one' sz :=
  match sz with
  | 0 => Wnil
  | S sz => one sz
  end.

Fixpoint ones sz :=
  match sz with
  | 0 => Wnil
  | S sz => W1 (ones sz)
  end.

Fixpoint zext {sz1} (x : word sz1) sz2 : word (sz1 + sz2) :=
  match x with
  | Wnil => zero sz2
  | W0 x => W0 (zext x sz2)
  | W1 x => W1 (zext x sz2)
  end.

Fixpoint sext {sz1} (x : word sz1) sz2 : word (sz1 + sz2) :=
  match x with
  | Wnil => zero sz2
  | @W0 0 _ => W0 (zero sz2)
  | @W1 0 _ => W1 (ones sz2)
  | @W0 (S _) x => W0 (sext x sz2)
  | @W1 (S _) x => W1 (sext x sz2)
  end.

Fixpoint compare_cont (r : comparison) {sz1 sz2} (x : word sz1) (y : word sz2) :=
  match x, y with
  | Wnil, _ | _, Wnil => r
  | W0 x, W0 y | W1 x, W1 y => compare_cont r x y
  | W0 x, W1 y => compare_cont Lt x y
  | W1 x, W0 y => compare_cont Gt x y
  end.

Definition compare {sz} := @compare_cont Eq sz sz.

Infix "?=" := compare (at level 70, no associativity) : word_scope.

Fixpoint scompare_cont (r : comparison) {sz1 sz2} (x : word sz1) (y : word sz2) :=
  match x, y with
  | Wnil, _ | _, Wnil => r
  | @W0 0 _, @W0 0 _ => r
  | @W1 0 _, @W0 0 _ => Lt
  | @W0 0 _, @W1 0 _ => Gt
  | @W1 0 _, @W1 0 _ => match r with Lt => Gt | Eq => Eq | Gt => Lt end
  | W0 x, W0 y | W1 x, W1 y => scompare_cont r x y
  | W0 x, W1 y => scompare_cont Lt x y
  | W1 x, W0 y => scompare_cont Gt x y
  end.

Definition scompare {sz} := @scompare_cont Eq sz sz.

Infix "?s=" := scompare (at level 70, no associativity) : word_scope.

Fixpoint eqb' {sz1 sz2} (x : word sz1) (y : word sz2) :=
  match x, y with
  | Wnil, Wnil => true
  | W0 x, W0 y | W1 x, W1 y => eqb' x y
  | _, _ => false
  end.

Definition eqb {sz} := @eqb' sz sz.

Definition leb {sz} (x y : word sz) :=
  match compare x y with
  | Gt => false
  | _ => true
  end.

Definition ltb {sz} (x y : word sz) :=
  match compare x y with
  | Lt => true
  | _ => false
  end.

Infix "=?" := eqb (at level 70, no associativity) : word_scope.
Infix "<=?" := leb (at level 70, no associativity) : word_scope.
Infix "<?" := ltb (at level 70, no associativity) : word_scope.

Definition lesb {sz} (x y : word sz) :=
  match compare x y with
  | Gt => false
  | _ => true
  end.

Definition ltsb {sz} (x y : word sz) :=
  match compare x y with
  | Lt => true
  | _ => false
  end.

Infix "<=s?" := leb (at level 70, no associativity) : word_scope.
Infix "<s?" := ltb (at level 70, no associativity) : word_scope.


(** Minimum and Maximum *)

Definition max {sz} (n m : word sz) :=
  match n ?= m with
    | Eq | Gt => n
    | Lt => m
  end.

Definition min {sz} (n m : word sz) :=
  match n ?= m with
    | Eq | Lt => n
    | Gt => m
  end.


(** indexing/destructing ops *)

Definition tl {sz} (x : word (S sz)) : word sz :=
  match x with
  | W0 x => x
  | W1 x => x
  end.

Definition lsb {sz} (x : word (S sz)) : bool :=
  match x with
  | W0 _ => false
  | W1 _ => true
  end.

Definition lsb' {sz} (x : word sz) : bool :=
  match x with
  | Wnil => false
  | W0 _ => false
  | W1 _ => true
  end.

Fixpoint msb {sz} (x : word (S sz)) :=
  match x with
  | @W0 0 x => false
  | @W1 0 x => true
  | @W0 (S sz) x | @W1 (S sz) x => msb x
  end.

Definition msb' {sz} : word sz -> bool :=
  match sz with
  | 0 => fun _ => false
  | S _ => fun x => msb x
  end.

Fixpoint split {sz2} sz1 : word (sz1 + sz2) -> word sz1 * word sz2 :=
  match sz1 with
  | 0 => fun x => (Wnil, x)
  | S sz1 =>
    fun x =>
      (match x in word (S sz) return sz = sz1 + sz2 -> word (S sz1) * word sz2 with
       | W0 x => fun p => let (x1, x2) := split sz1 (eq_rect _ word x (sz1 + sz2) p) in (W0 x1, x2)
       | W1 x => fun p => let (x1, x2) := split sz1 (eq_rect _ word x (sz1 + sz2) p) in (W1 x1, x2)
       end) eq_refl
  end.

Fixpoint take {sz2} sz1 : word (sz1 + sz2) -> word sz1 :=
  match sz1 with
  | 0 => fun _ => Wnil
  | S sz1 =>
    fun x =>
      (match x in word (S sz) return sz = sz1 + sz2 -> word (S sz1) with
       | W0 x => fun p => W0 (take sz1 (eq_rect _ word x (sz1 + sz2) p))
       | W1 x => fun p => W1 (take sz1 (eq_rect _ word x (sz1 + sz2) p))
       end) eq_refl
  end.

Fixpoint drop {sz2} sz1 : word (sz1 + sz2) -> word sz2 :=
  match sz1 with
  | 0 => fun x => x
  | S sz1 => fun x => drop sz1 (tl x)
  end.

Fixpoint append {sz1} (x : word sz1) : forall {sz2}, word sz2 -> word (sz1 + sz2) :=
  match x with
  | Wnil => fun _ y => y
  | W0 x => fun _ y => W0 (append x y)
  | W1 x => fun _ y => W1 (append x y)
  end.

Fixpoint neg {sz} (x : word sz) :=
  match x with
  | Wnil => Wnil
  | W0 x' => W1 (neg x')
  | W1 x' => W0 (neg x')
  end.

Fixpoint lor {sz1} (x : word sz1) {sz2} (y : word sz2) : word sz1 :=
  match x, y with
  | Wnil ,_ => Wnil
  | x, Wnil => x
  | W0 x, W0 y => W0 (lor x y)
  | W1 x, W0 y | W0 x, W1 y | W1 x, W1 y => W1 (lor x y)
  end.

Fixpoint land {sz1} (x : word sz1) {sz2} (y : word sz2) : word sz1 :=
  match x, y with
  | Wnil ,_ => Wnil
  | @W0 sz _, Wnil | @W1 sz _, Wnil => zero (S sz)
  | W0 x, W0 y | W1 x, W0 y | W0 x, W1 y => W0 (land x y)
  | W1 x, W1 y => W1 (land x y)
  end.

Fixpoint lxor {sz1} (x : word sz1) {sz2} (y : word sz2) : word sz1 :=
  match x, y with
  | Wnil ,_ => Wnil
  | x, Wnil => x
  | W0 x, W0 y | W1 x, W1 y => W0 (lxor x y)
  | W1 x, W0 y | W0 x, W1 y => W1 (lxor x y)
  end.

Fixpoint succ {sz} (x : word sz) :=
  match x with
  | Wnil => Wnil
  | W0 x' => W1 x'
  | W1 x' => W0 (succ x')
  end.

Fixpoint pred {sz} (x : word sz) :=
  match x with
  | Wnil => Wnil
  | W0 x' => W1 (pred x')
  | W1 x' => W0 x'
  end.

Definition twos_comp {sz} (x : word sz) :=
  succ (neg x).

Definition opp {sz} := @twos_comp sz.

Notation "- x" := (opp x) : word_scope.

Fixpoint add {sz1 sz2} (x : word sz1) (y : word sz2) :=
  match x, y with
  | Wnil, _ => Wnil
  | x, Wnil => x
  | W0 x', W0 y' => W0 (add x' y')
  | W1 x', W0 y' => W1 (add x' y')
  | W0 x', W1 y' => W1 (add x' y')
  | W1 x', W1 y' => W0 (add_carry x' y')
  end

with add_carry {sz1 sz2} (x : word sz1) (y : word sz2) :=
  match x, y with
  | Wnil, _ => Wnil
  | x, Wnil => succ x
  | W0 x', W0 y' => W1 (add x' y')
  | W1 x', W0 y' => W0 (add_carry x' y')
  | W0 x', W1 y' => W0 (add_carry x' y')
  | W1 x', W1 y' => W1 (add_carry x' y')
  end.

Infix "+" := add : word_scope.

(*
Fixpoint add_ext {sz} (x : word sz) : word sz -> word (S sz) :=
  match x in word n return word n -> _ with
  | Wnil => fun _ => Wnil~0
  | @W0 sz x => fun y =>
    (match y in word (S n) return n = sz -> _ with
     | y~0 => fun p => (add_ext x (eq_rect _ word y sz p))~0
     | y~1 => fun p => (add_ext x (eq_rect _ word y sz p))~1
     end) eq_refl
  | @W1 sz x => fun y =>
    (match y in word (S n) return n = sz -> _ with
     | y~0 => fun p => (add_ext x (eq_rect _ word y sz p))~0
     | y~1 => fun p => (add_carry_ext x (eq_rect _ word y sz p))~1
     end) eq_refl
  end

with add_carry_ext {sz} (x : word sz) :=
  match x in word sz return word sz -> _ with
  | Wnil => fun _ => Wnil~1
  | @W0 sz x => fun y =>
    (match y in word (S n) return n = sz -> _ with
     | y~0 => fun p => (add_ext x (eq_rect _ word y sz p))~1
     | y~1 => fun p => (add_carry_ext x (eq_rect _ word y sz p))~0
     end) eq_refl
  | @W1 sz x => fun y =>
    (match y in word (S n) return n = sz -> _ with
     | y~0 => fun p => (add_carry_ext x (eq_rect _ word y sz p))~0
     | y~1 => fun p => (add_carry_ext x (eq_rect _ word y sz p))~1
     end) eq_refl
  end.
*)


Fixpoint sub {sz1 sz2} (x : word sz1) (y : word sz2) :=
  match x, y with
  | Wnil, _ => Wnil
  | x, Wnil => x
  | W0 x', W0 y' => W0 (sub x' y')
  | W1 x', W0 y' => W1 (sub x' y')
  | W0 x', W1 y' => W1 (sub_carry x' y')
  | W1 x', W1 y' => W0 (sub x' y')
  end

with sub_carry {sz1 sz2} (x : word sz1) (y : word sz2) :=
  match x, y with
  | Wnil, _ => Wnil
  | x, Wnil => pred x
  | W0 x', W0 y' => W1 (sub_carry x' y')
  | W1 x', W0 y' => W0 (sub x' y')
  | W0 x', W1 y' => W0 (sub_carry x' y')
  | W1 x', W1 y' => W1 (sub_carry x' y')
  end.

Infix "-" := sub : word_scope.

(*
Fixpoint sub_ext {sz} (x : word sz) : word sz -> word (S sz) :=
  match x in word n return word n -> _ with
  | Wnil => fun _ => Wnil~0
  | @W0 sz x => fun y =>
    (match y in word (S n) return n = sz -> _ with
     | y~0 => fun p => (sub_ext x (eq_rect _ word y sz p))~0
     | y~1 => fun p => (sub_carry_ext x (eq_rect _ word y sz p))~1
     end) eq_refl
  | @W1 sz x => fun y =>
    (match y in word (S n) return n = sz -> _ with
     | y~0 => fun p => (sub_ext x (eq_rect _ word y sz p))~1
     | y~1 => fun p => (sub_ext x (eq_rect _ word y sz p))~0
     end) eq_refl
  end

with sub_carry_ext {sz} (x : word sz) :=
  match x in word sz return word sz -> _ with
  | Wnil => fun _ => Wnil~1
  | @W0 sz x => fun y =>
    (match y in word (S n) return n = sz -> _ with
     | y~0 => fun p => (sub_carry_ext x (eq_rect _ word y sz p))~1
     | y~1 => fun p => (sub_carry_ext x (eq_rect _ word y sz p))~0
     end) eq_refl
  | @W1 sz x => fun y =>
    (match y in word (S n) return n = sz -> _ with
     | y~0 => fun p => (sub_ext x (eq_rect _ word y sz p))~0
     | y~1 => fun p => (sub_carry_ext x (eq_rect _ word y sz p))~1
     end) eq_refl
  end.
*)


Fixpoint mul {sz1 sz2} (x : word sz1) (y : word sz2) :=
  match x with
  | Wnil => Wnil
  | W0 x' => W0 (mul x' y)
  | W1 x' => add (W0 (mul x' y)) y
  end.

Infix "*" := mul : word_scope.

Fixpoint mul_ext {sz1 sz2} (x : word sz1) (y : word sz2) : word (sz1 + sz2) :=
  match x in word n return word (n + sz2) with
  | Wnil => zero sz2
  | W0 x => W0 (mul_ext x y)
  | W1 x => add (W0 (mul_ext x y)) y
  end.

Fixpoint mul_sext {sz1 sz2} (x : word sz1) (y : word sz2) : word (sz1 + sz2) :=
  match x in word n return word (n + sz2) with
  | Wnil => zero sz2
  | @W0 0 _ => W0 (zero sz2)
  | @W1 0 _ => add (W0 (mul (ones sz2) y)) (sext y sz1)
  | @W0 (S _) x => W0 (mul_sext x y)
  | @W1 (S _) x => add (W0 (mul_sext x y)) (sext y sz1)
  end.



Fixpoint to_N {sz} (x : word sz) : N :=
  match x with
  | Wnil => N0
  | W0 x' => N.double (to_N x')
  | W1 x' => N.succ_double (to_N x')
  end.

Fixpoint of_N {sz} (x : N) : word sz :=
  match sz with
  | 0 => Wnil
  | S n' =>
    if N.odd x
    then W1 (of_N (N.div2 x))
    else W0 (of_N (N.div2 x))
  end.

Fixpoint to_Z {sz} (x : word sz) : Z :=
  match x with
  | Wnil => 0
  | @W0 0 x => 0
  | @W1 0 x => -1
  | @W0 (S _) x => Z.double (to_Z x)
  | @W1 (S _) x => Z.succ_double (to_Z x)
  end.

Fixpoint of_Z {sz} (x : Z) : word sz :=
  match sz with
  | 0 => Wnil
  | S sz =>
    if Z.odd x
    then W1 (of_Z (Z.div2 x))
    else W0 (of_Z (Z.div2 x))
  end.

End Word.
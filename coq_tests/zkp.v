
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Arith.
Require Import Omega.

(* Some simple notations. *)
Notation " [ ] " := nil.
Notation " [ x ] " := (cons x nil).
Notation " [ x ; .. ; y ] " := (cons x .. (cons y nil) ..).
Infix "==n" := beq_nat (no associativity, at level 50).

(* Define our notion of languages. *)

Inductive bit :=
  | bzero
  | bone.

Definition bits := list bit.

Inductive language : Type :=
  | l_from_prop (prop : bits -> Prop) : language.

Inductive in_language : language -> bits -> Prop :=
  | in_l (lang : language) (b: bits)
      (proof : (match lang with l_from_prop prop => prop end b)) :
      in_language lang b.

Inductive language_family : Type :=
  | lf_from_prop : (language -> Prop) -> language_family.

Definition affine_bounded (f : nat -> nat) := exists a b, forall n, f n <= a * n + b.
Definition poly_bounded (f : nat -> nat) := exists power a b, forall n, f n <= a * pow n power + b.

(* Some proofs about being bounded. *)

Ltac change_rhs_to z :=
  let rw_f := fresh "rw" in
  match goal with
  | [ |- _ ?x ?y ] => assert (y = z) as rw_f;
      [ try ring | rewrite rw_f; clear rw_f ]
  end.

Ltac change_lhs_to z :=
  let rw_f := fresh "rw" in
  match goal with
  | [ |- _ ?x ?y ] => assert (x = z) as rw_f;
      [ try ring | rewrite rw_f; clear rw_f ]
  end.

Ltac manipulate_lhs_bound bigger_y :=
  match goal with
  | [ |- ?x + ?y <= ?z ] => apply le_trans with (n := x + y) (m := x + bigger_y) (p := z);
      [ apply plus_le_compat_l | ]
  | [ |- ?x * ?y <= ?z ] => apply le_trans with (n := x * y) (m := x * bigger_y) (p := z);
      [ apply mult_le_compat_l | ]
  end.

About le_plus_trans.

Lemma le_plus_trans_l : forall n m p, n <= m -> n <= p + m.
Proof.
  pose proof mult_comm.
  pose proof le_plus_trans.
  firstorder.
Qed.

Lemma mult_nonzero_no_smaller_l : forall n m p, n <= m -> p <> 0 -> n <= p * m.
Proof.
  induction p; firstorder; simpl; firstorder.
Qed.

Lemma mult_nonzero_no_smaller_r : forall n m p, n <= m -> p <> 0 -> n <= m * p.
  intros.
  rewrite mult_comm.
  pose proof mult_nonzero_no_smaller_l.
  firstorder.
Qed.

Ltac le_zoom :=
  match goal with
  | [ _ : ?x |- ?x ] => assumption
  | [ |- ?x <= ?x ] => reflexivity
  | [ |- ?x <= ?y ] => omega
  | [ |- ?x + _ <= ?x + _ ] => apply plus_le_compat_l with (p := x); try le_zoom
  | [ |- _ + ?x <= _ + ?x ] => apply plus_le_compat_r with (p := x); try le_zoom
  | [ |- ?x * _ <= ?x * _ ] => apply mult_le_compat_l with (p := x); try le_zoom
  | [ |- _ * ?x <= _ * ?x ] => apply mult_le_compat_r with (p := x); try le_zoom
  | [ a : ?x <> 0 |- _ <= ?x * _ ] => apply mult_nonzero_no_smaller_l; try le_zoom
  | [ a : ?x <> 0 |- _ <= _ * ?x ] => apply mult_nonzero_no_smaller_r; try le_zoom
  | [ |- _ ^ ?x <= _ ^ ?x ] => apply Nat.pow_le_mono_l; try le_zoom
  | [ |- ?x ^ _ <= ?x ^ _ ] => apply Nat.pow_le_mono_r; le_zoom
  | [ |- ?x1 + ?x2 <= ?y1 + ?y2 ] => apply plus_le_compat; le_zoom
  | [ |- ?x1 * ?x2 <= ?y1 * ?y2 ] => apply mult_le_compat; le_zoom
  | [ a : ?x <= ?y |- ?x <= ?z ] => apply le_trans with (m := y); try le_zoom
  | [ |- _ <= _ + ?x ] => apply le_plus_trans with (p := x); le_zoom; fail
  | [ |- _ <= ?x + _ ] => apply le_plus_trans_l with (p := x); le_zoom; fail
  end.

Theorem affine_explicit : forall a b, affine_bounded (fun n => a * n + b).
Proof.
  pose proof le_refl.
  firstorder.
Qed.

Theorem affine_is_poly : forall f, affine_bounded f -> poly_bounded f.
Proof.
  firstorder.
  exists 1. exists x. exists x0.
  intro.
  simpl.
  rewrite mult_1_r.
  firstorder.
Qed.

Theorem affine_add : forall f1 f2, affine_bounded f1 -> affine_bounded f2 -> affine_bounded (fun n => f1 n + f2 n).
Proof.
  firstorder.
  rename x into a1. rename x1 into b1. rename x0 into a2. rename x2 into b2.
  exists (a1 + a2).
  exists (b1 + b2).
  intro.
  specialize (H n).
  specialize (H0 n).
  change_rhs_to ((a1 * n + b1) + (a2 * n + b2)).
  le_zoom.
Qed.

Theorem affine_rescale : forall f c, affine_bounded f -> affine_bounded (fun n => c * f n).
Proof.
  firstorder.
  rename x into a. rename x0 into b.
  exists (c * a).
  exists (c * b).
  intro.
  specialize (H n).
  rewrite <- mult_assoc.
  rewrite <- mult_plus_distr_l.
  le_zoom.
Qed.

Theorem affine_composition : forall f1 f2, affine_bounded f1 -> affine_bounded f2 -> affine_bounded (fun n => f1 (f2 n)).
Proof.
  firstorder.
  rename x into a1. rename x1 into b1. rename x0 into a2. rename x2 into b2.
  exists (a1 * a2).
  exists (b1 + a1 * b2).
  intros.
  specialize (H (f2 n)).
  specialize (H0 n).
  assert (a1 * f2 n + b1 <= a1 * (a2 * n + b2) + b1). { le_zoom. }
  change_rhs_to (a1 * (a2 * n + b2) + b1).
  le_zoom.
Qed.

(* I couldn't immediately find this in the library... *)
Lemma dumb_arith : forall a b, b <> 0 -> a <= a * b.
Proof.
  intros.
  induction a; try rewrite mult_succ_l; omega.
Qed.

(* Because exponentiation is weird around zero, we typically convert to this form after taking inputs. *)
Definition poly_bounded_exp_positive (f : nat -> nat) := exists power a b, power <> 0 /\ forall n, f n <= a * pow n power + b.

Theorem poly_explicit : forall e a b, poly_bounded (fun n => a * n^e + b).
Proof.
  intros.
  exists e. exists a. exists b.
  firstorder.
Qed.

Lemma poly_bounded_exponent_can_be_nonzero : forall f, poly_bounded f -> poly_bounded_exp_positive f.
Proof.
  firstorder.
  rename x into e.
  rename x0 into a.
  rename x1 into b.
  destruct e.
  {
    exists 1.
    exists a.
    exists (a + b).
    split.
    omega.
    intros.
    specialize (H n).
    rewrite Nat.pow_1_r.
    rewrite pow_0_r in H.
    rewrite mult_1_r in H.
    le_zoom.
  }
  rename e into e'.
  remember (S e') as e.
  exists e.
  exists a.
  exists b.
  split.
  omega.
  assumption.
Qed.

(* As a convenience, apply this first when taking two poly bounded functions. *)
Lemma two_function_apply_me : forall p,
  (forall f1 f2, poly_bounded_exp_positive f1 -> poly_bounded_exp_positive f2 -> (p f1 f2)) ->
  (forall f1 f2, poly_bounded f1 -> poly_bounded f2 -> (p f1 f2)).
Proof.
  pose proof poly_bounded_exponent_can_be_nonzero.
  firstorder.
Qed.

Lemma pow_exponent_sum_makes_no_smaller : forall n e1 e2, e1 <> 0 -> n^e1 <= n^(e1 + e2).
Proof.
  firstorder.
  induction e2.
  rewrite plus_0_r.
  reflexivity.
  rewrite plus_comm.
  simpl.
  rewrite plus_comm.
  destruct n.
  {
    pose proof Nat.pow_0_l.
    firstorder.
  }
  {
    rewrite <- mult_1_l at 1.
    le_zoom.
  }
Qed. 

Theorem poly_add : forall f1 f2, poly_bounded f1 -> poly_bounded f2 -> poly_bounded (fun n => f1 n + f2 n).
Proof.
  apply two_function_apply_me.
  firstorder.
  rename x into e1.
  rename x0 into e2.
  rename x1 into a1.
  rename x2 into a2.
  rename x3 into b1.
  rename x4 into b2.
  (* Give bounds. These are extremely loose. *)
  exists (e1 + e2).
  exists (a1 + a2).
  exists (b1 + b2).
  intro.
  specialize (H1 n).
  specialize (H2 n).
  (* Begin proof proper. *)
  change_rhs_to ((a1 * n^(e1 + e2) + b1) +
                 (a2 * n^(e1 + e2) + b2)).
  pose proof pow_exponent_sum_makes_no_smaller n.
  apply plus_le_compat; le_zoom.
  { firstorder. }
  {
    rewrite plus_comm.
    firstorder.
  }
Qed.

Lemma zero's_powers_are_small : forall n, 0 ^ n <= 1.
Proof.
  destruct n; simpl; omega.
Qed.

Theorem poly_mul : forall f1 f2, poly_bounded f1 -> poly_bounded f2 -> poly_bounded (fun n => f1 n * f2 n).
Proof.
  apply two_function_apply_me.
  firstorder.
  rename x into e1.
  rename x0 into e2.
  rename x1 into a1.
  rename x2 into a2.
  rename x3 into b1.
  rename x4 into b2.
  (* The bounds on a polynomial multiplication. *)
  exists (e1 + e2).
  remember (a1 * a2 + b1 * a2 + b2 * a1) as a'.
  exists (a').
  exists (b1 * b2).
  intro.
  specialize (H1 n).
  specialize (H2 n).

  apply le_trans with (m := (a1 * n^e1 + b1) * (a2 * n^e2 + b2)).
  le_zoom.

  change_lhs_to (
    (a1 * a2 * n^e1 * n^e2) +
    (a1 * n^e1 * b2) +
    (a2 * n^e2 * b1) +
    (b1 * b2)
  ).
  le_zoom.

  rewrite Nat.pow_add_r.
  rewrite Heqa'.
  change_rhs_to (
    (a1 * a2 * n^e1 * n^e2) +
    (a1 * n^e1 * n^e2 * b2) +
    (a2 * n^e1 * n^e2 * b1)
  ).

  destruct n.
  {
    repeat rewrite Nat.pow_0_l; try assumption.
    le_zoom.
  }
  rename n into n'.
  remember (S n') as n.

  assert (n <> 0) as n_nonzero. omega.
  pose proof Nat.pow_nonzero n e1 n_nonzero.
  pose proof Nat.pow_nonzero n e2 n_nonzero.
  le_zoom.
Qed.

Theorem poly_exp : forall f exp, poly_bounded f -> poly_bounded (fun n => (f n) ^ exp).
Proof.
  intros.
  induction exp.
  {
    exists 0. exists 1. exists 0.
    firstorder.
  }
  apply poly_mul; assumption.
Qed.

Theorem poly_composition : forall f1 f2, poly_bounded f1 -> poly_bounded f2 -> poly_bounded (fun n => f1 (f2 n)).
Proof.
  intros.
  repeat destruct H.
  rename x into e.
  rename x0 into a.
  rename x1 into b.
  assert (poly_bounded (fun n => a * (f2 n)^e + b)).
  {
    apply poly_add.
    apply poly_mul.
    exists 0. exists 1. exists a.
    firstorder.
    apply poly_exp.
    assumption.
    exists 0. exists 1. exists b.
    firstorder.
  }
  repeat destruct H1.
  rename x into final_e.
  rename x0 into final_a.
  rename x1 into final_b.
  exists final_e.
  exists final_a.
  exists final_b.
  intro.
  specialize (H (f2 n)).
  le_zoom.
  firstorder.
Qed.

Lemma identity_is_poly_bounded : poly_bounded (fun n : nat => n).
Proof.
  exists 1. exists 1. exists 0.
  intro.
  simpl.
  omega.
Qed.

Lemma successor_is_poly_bounded : poly_bounded S.
Proof.
  exists 1. exists 1. exists 1.
  intro.
  simpl.
  omega.
Qed.

Ltac prove_poly_bounded := 
  match goal with
  | [ _ : poly_bounded ?f |- poly_bounded ?f ] => assumption
  | [ |- poly_bounded (fun _ : nat => ?c) ] => exact (poly_explicit 0 0 c)
  | [ |- poly_bounded (fun n : nat => n) ] => exact identity_is_poly_bounded
  | [ |- poly_bounded S ] => exact successor_is_poly_bounded
  | [ |- poly_bounded (?x ?y) ] => simpl; try prove_poly_bounded
  | [ |- poly_bounded (fun n : nat => ?x * ?y) ] => apply poly_mul; try prove_poly_bounded
  | [ |- poly_bounded (fun n : nat => ?x + ?y) ] => apply poly_add; try prove_poly_bounded
  | [ |- poly_bounded (fun n : nat => ?x ^ ?c) ] => apply poly_exp; try prove_poly_bounded
  | [ |- poly_bounded (fun n : nat => (?x ?y)) ] => simpl; apply poly_composition; try prove_poly_bounded
  end.

Example asdf : forall f, poly_bounded f ->
  poly_bounded (fun n => 3 * n * (f n * 3) + (f (n + f 2 * f n) * 6)^3).
Proof.
  intros.
  prove_poly_bounded.
Qed.

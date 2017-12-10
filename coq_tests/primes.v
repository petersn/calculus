(* Proof of the infinitude of the primes. *)

Require Import Omega.

Definition divides a b := exists k, b = k * a.
Definition prime p := 2 <= p /\ forall k, divides k p -> (k = 1 \/ k = p).

Lemma divides_trans : forall a b c, divides a b -> divides b c -> divides a c.
Proof.
  firstorder. exists (x * x0). subst.
  rewrite mult_assoc_reverse. reflexivity.
Qed.

Lemma divides_mul : forall a b c, divides a b -> divides a (c * b).
Proof.
  intros. destruct H. exists (c * x). subst.
  rewrite Nat.mul_assoc. reflexivity.
Qed.

Lemma divides_smaller : forall a b, b <> 0 -> divides a b -> a <= b.
Proof.
  intros a b H div.
  destruct div.
  pose proof mult_O_le a x.
  firstorder; subst; omega.
Qed.

Lemma not_divides_is_prime : forall p, 2 <= p -> (forall n, 1 < n < p -> ~ divides n p) -> prime p.
Proof.
  intros. split; try assumption. intros.
  destruct (le_gt_dec k p).
  {
    destruct (eq_nat_dec k p); try auto.
    destruct (eq_nat_dec k 0).
    - firstorder. subst. omega.
    - destruct (eq_nat_dec k 1); auto; apply (H0 k) in H1; firstorder.
  }
  - pose proof divides_smaller; firstorder.
Qed.

Definition prop_dec {T} (P : T -> Prop) := forall k, { P k } + { ~ P k }.

Lemma search bound P : prop_dec P -> { exists k, k <= bound /\ P k } + { forall k, k <= bound -> ~ P k }.
Proof.
  intro H.
  induction bound.
  {
    destruct (H 0).
    - left. exists 0. firstorder.
    - right. intros. assert (k = 0). firstorder. subst. assumption.
  } {
    destruct (H (S bound)).
    - left. exists (S bound). firstorder.
    - destruct IHbound;
        [ | right; intros; destruct (eq_nat_dec k (S bound)) ];
        subst; firstorder.
  }
Qed.

Ltac perform_search bound P :=
  let hyp := fresh "hyp" in
  let result := fresh "result" in
  assert (prop_dec P) as hyp;
  [ unfold prop_dec; intros | pose proof search bound P hyp as result; clear hyp ].

Theorem divides_dec : forall a b, { divides a b } + { ~ divides a b }.
Proof.
  intros.
  (* First handle the a = 0 case. *)
  destruct (eq_nat_dec a 0). { destruct (eq_nat_dec b 0); subst; firstorder. }
  (* Search for a divisor. *)
  perform_search b (fun k => b = k * a).
  { destruct (eq_nat_dec b (k * a)); firstorder. }
  destruct result;
    [ | right; intro; firstorder; destruct (le_gt_dec x b);
      [ | pose proof mult_O_le x a as hyp; rewrite mult_comm in hyp ] ];
        firstorder.
Qed.

Lemma proper_divisor_prime_dec : forall n, 2 <= n -> { exists k, 1 < k < n /\ divides k n } + { prime n }.
Proof.
  intros.
  perform_search n (fun k => 1 < k < n /\ divides k n).
  - pose proof divides_dec. destruct (lt_dec 1 k); destruct (lt_dec k n); firstorder.
  - destruct result;
      [ | right; apply not_divides_is_prime; intros;
        [ | specialize (n0 n1); intro; apply n0 ] ]; firstorder.
Qed.

Lemma prime_divisor : forall n, 2 <= n -> exists p, divides p n /\ prime p.
Proof.
  assert (forall bound n, n <= bound -> 2 <= n -> exists p, divides p n /\ prime p);
    [ induction bound; intros;
      try destruct (proper_divisor_prime_dec n);
      try destruct e as [ div ];
      try destruct (IHbound div);
      try pose proof (divides_trans x div n) | ]; firstorder.
Qed.

Lemma successor_not_divisible : forall a b, 2 <= a -> divides a b -> ~ divides a (S b).
Proof.
  intros a b abig div1 div2. firstorder. subst.
  pose proof mult_le_compat_r as compat.
  destruct (lt_dec x0 x);
    [ specialize (compat (S x0) x a l); rewrite <- H in compat; simpl in compat |
      specialize (compat x x0 a) ]; firstorder.
Qed.

Fixpoint factorial n :=
  match n with
    | 0 => 1
    | S n' => n * factorial n'
  end.

Lemma factorial_divisible : forall n k, 1 <= k <= n -> divides k (factorial n).
Proof.
  induction n; intros; [ | destruct (eq_nat_dec k (S n));
    [ exists (factorial n); subst; rewrite Nat.mul_comm | apply divides_mul ] ];
      firstorder.
Qed.

Lemma factorial_at_least_one : forall n, 1 <= factorial n.
  induction n; try apply le_plus_trans; firstorder.
Qed.

Theorem primes_infinite : forall n, exists p, p > n /\ prime p.
Proof.
  intros.
  (* Construct the result. *)
  assert (2 <= S (factorial n)) as hyp.
  { pose proof factorial_at_least_one n. omega. }
  apply (prime_divisor (S (factorial n))) in hyp.
  destruct hyp as [ P [ Hdiv Hprime ] ].
  (* Do case analysis on P. *)
  pose proof factorial_divisible n P.
  pose proof successor_not_divisible P (factorial n).
  assert (1 <= P); destruct (le_gt_dec P n); firstorder.
Qed.

(* Ancillary decider, if of interest. *)

Lemma prime_dec : forall n, { prime n } + { ~ prime n }.
Proof.
  intros.
  destruct (le_dec 2 n) as [ hyp | ]; firstorder.
  destruct (proper_divisor_prime_dec n hyp); firstorder.
Qed.

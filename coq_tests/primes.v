
Require Import Omega.
Require Import Arith.
Require Import Lists.List.

Definition divides a b := exists k, b = k * a.
Definition prime p := 2 <= p /\ forall k, divides k p -> (k = 1 \/ k = p).
Definition cant_be_factored p := (2 <= p /\ ~ (exists a b, 2 <= a /\ 2 <= b /\ p = a * b)).
Definition not_divisible_by_lesser p := (2 <= p /\ forall k, 1 < k -> k < p -> ~ divides k p).

Lemma div_trans : forall a b c, divides a b -> divides b c -> divides a c.
Proof. {
  unfold divides.
  firstorder.
  subst.
  exists (x0 * x).
  rewrite <- mult_assoc.
  reflexivity.
} Qed.

Lemma div_mult_compat : forall a b c, divides a b -> divides a (c * b).
Proof. {
  firstorder.
  subst.
  exists (c * x).
  rewrite mult_assoc.
  reflexivity.
} Qed.

Fixpoint divides_decider_helper (a b k : nat) : bool :=
  match k with
  | 0 => beq_nat b 0
  | S k' => if beq_nat (k * a) b then true else
             divides_decider_helper a b k'
  end.

Definition divides_decider (a b : nat) : bool := divides_decider_helper a b b.

Lemma at_least_as_big : forall a b, b <> 0 -> a <= a * b.
Proof. {
  intros.
  induction a.
  omega.
  rewrite mult_succ_l.
  assert (S a = 1 + a) as succ_obv.
  auto.
  rewrite succ_obv.
  rewrite plus_comm.
  apply plus_le_compat.
  assumption.
  omega.
} Qed.

Lemma never_bigger : forall a b k, b <> 0 -> b < k -> k * a <> b.
Proof. {
  intros.
  destruct a.
  rewrite mult_0_r.
  intuition.
  remember (S a) as y.
  assert (y <> 0).
  rewrite Heqy.
  auto.
  assert (k <= k * y).
  apply at_least_as_big.
  assumption.
  omega.
} Qed.

Lemma searching_is_good_enough :
  forall a b, (forall k, k <= b -> k * a <> b) -> ~(divides a b).
Proof. {
  intros.
  assert (b <> 0).
  destruct b.

  {
    intuition.
    specialize (H 0).
    auto.
  }
  {
    auto.
  }

  unfold divides.
  intro.
  destruct H1.
  assert ({x <= b} + {x > b}).
  apply le_gt_dec.
  destruct H2; specialize (H x).

  {
    apply (H l).
    auto.
  }

  {
    apply (never_bigger a b x); omega.
  }
} Qed.

Theorem divides_decider_helper_true_means : forall a b k, divides_decider_helper a b k = true -> divides a b.
Proof. {
  induction k.

  {
    unfold divides_decider_helper.
    intros.
    assert (b = 0).
    destruct b.
    auto.
    unfold beq_nat in H.
    exfalso.
    intuition.
    exists 0.
    auto.
  }
  {
    unfold divides_decider_helper.
    case_eq (beq_nat (S k * a) b).
    {
      intros.
      apply beq_nat_true in H.
      exists (S k).
      omega.
    }
    {
      intro.
      apply IHk.
    }
  }
} Qed.

Theorem divides_decider_helper_false_means : forall a b k, divides_decider_helper a b k = false -> forall c, c <= k -> c * a <> b.
Proof. {
  induction k.
  {
    simpl.
    rewrite beq_nat_false_iff.
    intros.
    destruct c.
    omega.
    exfalso.
    intuition.
  }
  {
    unfold divides_decider_helper.
    case_eq (beq_nat (S k * a) b).
    {
      intros.
      exfalso.
      intuition.
    }
    {
      intros.
      rewrite beq_nat_false_iff in H.
      apply le_lt_eq_dec in H1.
      destruct H1.
      apply IHk.
      apply H0.
      omega.
      rewrite <- e in H.
      assumption.
    }
  }
} Qed.

Theorem divides_decider_good : forall a b, if divides_decider a b then divides a b else ~ divides a b.
Proof. {
  intros.
  case_eq (divides_decider a b); unfold divides_decider.
  {
    apply divides_decider_helper_true_means.
  }
  {
    intros.
    apply searching_is_good_enough.
    apply divides_decider_helper_false_means.
    assumption.
  }
} Qed.

Theorem divides_decider_is_true_or_false : forall a b, {divides_decider a b = true} + {divides_decider a b = false}.
Proof. {
  firstorder.
} Qed.

Theorem divides_dec : forall a b, {divides a b} + {~divides a b}.
Proof. {
  intros.
  case_eq (divides_decider a b); unfold divides_decider.
  { 
    intro.
    left.
    eapply divides_decider_helper_true_means.
    eassumption.
  }
  { 
    intro.
    right.
    apply searching_is_good_enough.
    apply divides_decider_helper_false_means.
    assumption.
  }
} Qed.

Lemma divides_means_divides_decider_is_true : forall a b, divides a b -> divides_decider a b = true.
Proof. {
  intros.  
  destruct (divides_decider_is_true_or_false a b).
  assumption.
  pose proof divides_decider_good a b.
  rewrite e in H0.
  contradiction.
} Qed.

Theorem you_divide_folks_you_multiplied_to_make_l : forall a b c, c = a * b -> divides a c.
Proof. {
  intros.
  exists b.
  rewrite mult_comm.
  assumption.
} Qed.

Theorem you_divide_folks_you_multiplied_to_make_r : forall a b c, c = a * b -> divides b c.
Proof. {
  intros.
  exists a.
  assumption.
} Qed.

Lemma square_is_bigger : forall x, 2 <= x -> x < x * x.
Proof. {
  intros.
  induction x; firstorder.
  rewrite mult_succ_l.
  rewrite mult_succ_r.
  unfold lt.
  destruct (eq_nat_dec x 1).
  {
    subst.
    omega.
  }
  {
    assert (2 <= x).
    omega.
    pose proof IHx H0.
    omega.
  }
} Qed.

Lemma only_zero_and_one_square_to_themselves : forall x, x = x * x -> x <= 1.
Proof. {
  intros.
  destruct (eq_nat_dec x 0).
  omega.
  destruct (eq_nat_dec x 1).
  omega.
  destruct (le_dec 2 x).
  pose proof square_is_bigger x l.
  pose proof NPeano.Nat.lt_neq x (x * x) H0.
  contradiction.
  omega.
} Qed.

Theorem primes_cant_be_factored : forall p, prime p -> cant_be_factored p.
Proof. {
  (* Proof of implication to the right. *)
  firstorder.
  intro.
  firstorder.
  rename x into a.
  rename x0 into b.
  pose proof H0 a as a_conv.
  pose proof H0 b as b_conv.
  pose proof you_divide_folks_you_multiplied_to_make_l a b p as a_div.
  pose proof you_divide_folks_you_multiplied_to_make_r a b p as b_div.
  pose proof a_conv (a_div H3).
  pose proof b_conv (b_div H3).
  clear a_conv b_conv a_div b_div.
  firstorder.
  rewrite H4 in H3.
  rewrite H5 in H3.
  pose proof only_zero_and_one_square_to_themselves p H3.
  omega.
} Qed.

Theorem cant_be_factored_is_prime : forall p, cant_be_factored p -> prime p.
Proof. {
  firstorder.
  pose proof H0 x.
  clear H0.
  firstorder.
  pose proof H0 k.
  clear H0.
  firstorder.
  destruct (eq_nat_dec k 0).
  {
    subst.
    omega.
  }
  destruct (eq_nat_dec k 1).
  {
    subst.
    omega.
  }
  assert (2 <= k).
  omega.
  clear n.
  destruct (eq_nat_dec k p).
  {
    firstorder.
  }
  Lemma multiplication_requires_big_inputs :
    forall a b c, 2 <= c -> c = a * b -> 2 <= b -> b <> c -> 2 <= a.
  Proof. {
    intros.
    destruct (eq_nat_dec a 0).
    {
      rewrite e in H0.
      simpl in H0.
      omega.
    }
    {
      destruct (eq_nat_dec a 1).
      {
        rewrite e in H0.
        simpl in H0.
        rewrite <- plus_n_O in H0.
        omega.
      }
      {
        omega.
      }
    }
  } Qed.
  pose proof multiplication_requires_big_inputs x k p.
  omega.
} Qed.

Theorem prime_is_not_divisible : forall p, prime p -> not_divisible_by_lesser p.
Proof. {
  firstorder.
} Qed.

Lemma neither_is_nonzero : forall a b c, c = a * b -> 2 <= c -> (a <> 0 /\ b <> 0).
Proof. {
  firstorder; intro; subst; omega.
} Qed.

Lemma involved_in_factorization_means_in_range :
  forall a b c, c = a * b -> 2 <= c -> a <> 1 -> b <> 1 -> (1 < a /\ a < c).
Proof. {
  intros.
  pose proof neither_is_nonzero a b c H H0.
  pose proof proj1 H3.
  pose proof proj2 H3.
  clear H3.
  firstorder.
  assert (2 <= a). omega.
  assert (2 <= b). omega.
  destruct b.
  omega.
  rewrite mult_succ_r in H.
  subst.
  destruct (eq_nat_dec (a * b) 0).
  {
    pose proof mult_is_O a b.
    omega.
  }
  remember (a * b) as c.
  omega.
} Qed.

Theorem not_divisible_is_prime : forall p, not_divisible_by_lesser p -> prime p.
Proof. {
  firstorder.
  pose proof H0 k.
  destruct (eq_nat_dec k 1).
  { left. assumption. }
  {
    destruct (eq_nat_dec k p).
    { right. assumption. }
    {
      rewrite mult_comm in H1.
      pose proof involved_in_factorization_means_in_range k x p H1 H n.
      destruct (eq_nat_dec x 1).
      {
        clear H0.
        subst.
        omega.
      }
      {
        pose proof H3 n1.
        pose proof H2 (proj1 H4) (proj2 H4) as not_divides.
        unfold divides in not_divides.
        rewrite mult_comm in H1.
        pose proof (ex_intro (fun x => p = x * k) x H1) as divisibility.
        pose proof not_divides divisibility.
        exfalso.
        assumption.
      }
    }
  }
} Qed.

Theorem zero_not_prime : ~ prime 0.
Proof. {
    intro.
    firstorder.
    omega.
} Qed.

Theorem one_not_prime : ~ prime 1.
Proof. {
    intro.
    firstorder.
    omega.
} Qed.

Theorem two_prime : prime 2.
Proof. {
  pose proof not_divisible_is_prime 2.
  unfold not_divisible_by_lesser in H.
  pose proof le_n 2.
  firstorder.
} Qed.

Theorem three_prime : prime 3.
Proof. {
  apply cant_be_factored_is_prime.
  firstorder.
  intro.
  firstorder.
  assert (2 * 2 <= x * x0).
  apply mult_le_compat; assumption.
  omega.
} Qed.

Fixpoint list_max (l : list nat) : nat :=
  match l with
  | hd :: tl => max hd (list_max tl)
  | nil => 0
  end.

Lemma no_elements_bigger_than_max : forall l k, list_max l < k -> ~ In k l.
Proof. {
  intros.
  induction l.
  {
    simpl.
    firstorder.
  }
  {
    unfold list_max in H.
    fold list_max in H.
    simpl.
    destruct (eq_nat_dec a k).
    {
      rewrite e in H.
      SearchAbout (_ <= max _ _).
      pose proof Max.le_max_l k (list_max l).
      omega.
    }
    {
      intro.
      firstorder.
      apply NPeano.Nat.max_lub_lt_iff in H.
      firstorder.
    }
  }
} Qed.

(*
    simpl.
    intro.
    simpl in H.
    (* First we establish a <> k, thus showing (In k l) via H0. *)
    firstorder; subst; unfold lt in H; rewrite Max.succ_max_distr in H.
    {
      pose proof Max.max_lub_l (S k) (S (list_max l)) k H.
      omega.
    }
    {
      pose proof Max.max_lub_r (S a) (S (list_max l)) k H.
      exact (IHl H1 H0).
    }
  }
} Qed.
*)

Definition infinitely_many_primes := forall k, exists p, k <= p /\ prime p.
Definition list_of_all_primes_is_bad := forall l : list nat, (forall p, In p l -> prime p) -> (forall p, prime p -> In p l) -> False.

Theorem primes_equiv_one : infinitely_many_primes -> list_of_all_primes_is_bad.
Proof. {
  unfold list_of_all_primes_is_bad.
  intros.
  pose proof no_elements_bigger_than_max l.
  clear H0.
  firstorder.
} Qed.

Lemma divides_means_no_greater : forall a b, b <> 0 -> divides a b -> a <= b.
Proof. {
  firstorder.
  subst.
  assert (x <> 0).
  {
    intro.
    subst.
    simpl in H.
    omega.
  }
  assert (1 <= x).
  omega.
  assert (a * 1 <= a * x).
  apply mult_le_compat; try omega.
  rewrite mult_comm with (n := a) (m := x) in H2.
  omega.
} Qed.

Fixpoint sum_up' (n : nat) : nat :=
  match n with
  | 0 => 0
  | S k => n + sum_up' k
  end.

Fixpoint sum_up (n : nat) : nat.
Proof.
  destruct (eq_nat_dec n 0).
  {
    exact 0.
  }
  {
    destruct n.
    omega.
    exact (n + sum_up n).
  }
Defined.

Fixpoint prime_prover_innerloop n (k : nat) (lower : 1 < k) (upper : k < n) :
  (forall x, k <= x -> x < n -> ~ divides x n) -> { prime n } + { ~ prime n }.
Proof.
  intro.
  rename H into good_so_far.
  (* Handle the simple case where k = 2, in which case we're done. *)
  destruct (eq_nat_dec k 2).
  {
    left.
    apply not_divisible_is_prime.
    subst.
    assert (2 <= n).
    omega.
    cbv [not_divisible_by_lesser].
    firstorder.
  }
  (* Otherwise, decrement k, and keep going. *)
  destruct k.
  omega.
  destruct (le_dec 2 n).
  { 
    assert (1 < k) as new_lower.
    omega.
    assert (k < n) as new_upper.
    omega.
    destruct (divides_dec k n).
    {
      (* In the case where 2 <= n, and k does indeed divide n, then we report not prime. *)
      right.
      intro.
      remember H as is_prime.
      unfold prime in H.
      pose proof proj2 H.
      pose proof H0 k d.
      pose proof prime_is_not_divisible n is_prime.
      cbv [not_divisible_by_lesser] in H2.
      pose proof (proj2 H2) k new_lower new_upper.
      exact (H3 d).
    }
    {
      (* Perform this call inductively. *)
      assert (forall x, k <= x -> x < n -> ~ divides x n) as still_good.
      {
        intros.
        destruct (eq_nat_dec k x).
        {
          subst.
          firstorder.
        }
        apply good_so_far.
        omega.
        omega.
      }
      exact (prime_prover_innerloop n k new_lower new_upper still_good).
    }
  }
  {
    right.
    firstorder.
  }
Defined.

Theorem prime_dec : forall n, { prime n } + { ~ prime n }.
Proof. {
  intros.
  destruct n.
  right.
  apply zero_not_prime.
  destruct (eq_nat_dec n 0).
  {
    right.
    subst.
    apply one_not_prime.
  }
  assert (2 <= S n).
  omega.
  destruct (eq_nat_dec n 1).
  {
    left.
    subst.
    apply two_prime.
  }
  destruct (divides_dec n (S n)).
  {
    right.
    firstorder.
  }
  {
    apply (prime_prover_innerloop (S n) n).
    omega.
    omega.
    intros.
    assert (x = n).
    omega.
    subst.
    assumption.
  }
} Defined.

(* Fixpoint composites_can_be_factored : forall n, 2 <= n -> (~ prime n) -> exists a b, (2 <= a /\ 2 <= b /\ n = a * b). *)

Theorem if_one_divisor_is_proper_so_is_the_other :
  forall a b c, 2 <= c -> c = a * b -> 2 <= b -> b < c -> (2 <= a < c).
Proof.
  intros.
  destruct (le_lt_dec a 1).
  {
    destruct (eq_nat_dec a 0).
    subst.
    omega.
    assert (a = 1).
    omega.
    subst.
    omega.
  }
  firstorder.
  assert (a <> 1) as a_nz. omega.
  assert (b <> 1) as b_nz. omega.
  pose proof involved_in_factorization_means_in_range a b c H0 H a_nz b_nz.
  firstorder.
Qed.

Definition has_prop_div n := exists a, (2 <= a /\ a < n /\ divides a n).

Theorem no_prop_div_is_prime : forall n, 2 <= n -> (~ has_prop_div n) -> prime n.
Proof.
  intros.
  apply not_divisible_is_prime.
  firstorder.
Qed.

Theorem composites_have_at_least_one_proper_divisor :
  forall n, 2 <= n -> (~ prime n) -> has_prop_div n.
Proof.
  intros.
  Fixpoint divisor_finder (n search_bound : nat) :
    (2 <= n) ->
    (forall x, search_bound < x -> x < n -> ~ divides x n) ->
    { has_prop_div n } + { ~ has_prop_div n }.
  Proof.
    intros.
    destruct search_bound.
    {
      clear divisor_finder.
      specialize (H0 1).
      assert (0 < 1). omega.
      pose proof H0 H1 H.
      clear H0.
      firstorder.
      pose proof (H0 n).
      omega.
    }
    {
      (* Get some basic facts. *)
      (* fact 1: search_bound < n *)
      destruct (le_lt_dec n (S search_bound)).
      {
        specialize (divisor_finder n search_bound H).
        assert (forall x, search_bound < x -> x < n -> ~ divides x n).
        intros.
        omega.
        exact (divisor_finder H1).
      }
      (* fact 2: search_bound <> 0 *)
      destruct (eq_nat_dec search_bound 0).
      {
        subst.
        right.
        cbv [has_prop_div].
        clear divisor_finder.
        intro.
        destruct H1.
        firstorder.
      }
      (* Now we check whether or not (S search_bound) actually divides n. *)
      destruct (divides_dec (S search_bound) n).
      {
        (* If so, then we have a proper divisor. *)
        left.
        cbv [has_prop_div].
        pose proof d as d'.
        destruct d.
        (* In particular, it's the divisor x. *)
        exists x.
        (* Now we show properness. *)
        assert (2 <= S search_bound) as rf.
        omega.
        pose proof if_one_divisor_is_proper_so_is_the_other x (S search_bound) n H H1 rf l.
        clear divisor_finder H0.
        firstorder.
        apply you_divide_folks_you_multiplied_to_make_l with (b := (S search_bound)).
        assumption.
      }
      (* Do the recursive call. *)
      assert (forall x, search_bound < x -> x < n -> ~ divides x n).
      {
        intros.
        destruct (eq_nat_dec x (S search_bound)).
        {
          subst.
          assumption.
        }
        specialize (H0 x).
        clear divisor_finder n1.
        firstorder.
      }
      exact (divisor_finder n search_bound H H1).
    }
  Defined.
  assert (forall x, n < x -> x < n -> ~ divides x n) as initial_proof.
  { intros. omega. }
  pose proof divisor_finder n n H initial_proof as decided.
  destruct decided.
  assumption.
  apply no_prop_div_is_prime in n0.
  contradiction.
  assumption.
Qed.

Theorem composites_can_be_factored : forall n, 2 <= n -> (~ prime n) -> exists a b, (2 <= a /\ 2 <= b /\ n = a * b).
Proof. {
  intros.
  pose proof composites_have_at_least_one_proper_divisor n H H0.
  firstorder.
  exists x0.
  exists x.
  pose proof if_one_divisor_is_proper_so_is_the_other x0 x n.
  firstorder.
} Qed.

(* We now implement a simple trial division function, and prove that it decides primality. *)
Fixpoint is_prime_helper n k : bool :=
  match k with
  | 1 => true
  | _ => if divides_decider k n then false else
    match k with
    | 2 => true
    | S k' => is_prime_helper n k'
    | _ => false (* Set that one is not prime. *)
    end 
  end.

Fixpoint is_prime (n : nat) : bool :=
  is_prime_helper n (n - 1). 

(*
Theorem is_prime_helper_means_search : forall n k, 2 <= n -> is_prime_helper n k = true -> (forall t, 1 < t -> t <= k -> ~ divides t n).
Proof. {
  intros.
  induction k.
  {
    omega.
  }
  {
    intro.
    (* Blow away the k = 0 case immediately. *)
    destruct (eq_nat_dec k 0).
    omega.
    destruct (eq_nat_dec k 1).
    {
      firstorder.
      subst.
      assert (t = 2).
      omega.
      subst.
      simpl in H0.
      assert (divides 2 (x * 2)).
      exists x.
      reflexivity.
      pose proof divides_means_divides_decider_is_true 2 (x * 2) H3.
      rewrite H4 in H0.
      firstorder.
    }
    (* Now we handle the main meat -- the inductive case when 2 <= k. *)
    {
      firstorder.
      simpl in H0.
      
      destruct (eq_nat_dec t k).
      subst t.
Admitted.
*)

Theorem everyone_is_divisible_by_a_prime_strong_induction : forall level, forall n, n <= level -> 2 <= n -> exists p, prime p /\ divides p n.
Proof. {
  induction level; intros.
  omega.
  destruct (prime_dec n).
  {
    (* In the case where the number itself is prime, just return it. *)
    exists n.
    firstorder.
  }
  {
    (* Otherwise, recurse on a random factor. *)
    SearchAbout prime.
    pose proof composites_can_be_factored n H0 n0.
    destruct H1.
    destruct H1.
    destruct H1.
    destruct H2.
    assert (x <= n).
    rewrite H3.
    apply at_least_as_big.
    omega.
    destruct (eq_nat_dec x n).
    {
      subst x.
      pose proof NPeano.Nat.mul_id_r n x0.
      assert (n <> 0).
      omega.
      omega.
    }
    assert (x <= level).
    omega.
    (* Recurse on the left factor right here. *)
    pose proof IHlevel x H5 H1.
    destruct H6.
    destruct H6.
    pose proof div_trans x1 x n.
    pose proof you_divide_folks_you_multiplied_to_make_l x x0 n H3.
    pose proof H8 H7 H9.
    exists x1.
    exact (conj H6 H10).
  }
} Qed.

Theorem everyone_is_divisible_by_a_prime : forall n, 2 <= n -> exists p, prime p /\ divides p n.
Proof. {
  intro.
  exact (everyone_is_divisible_by_a_prime_strong_induction n n (le_n n)).
} Qed.

Theorem not_divisible_by_any_prime_means_prime :
  forall p, 2 <= p -> (forall check, prime check -> check < p -> ~ divides check p) -> prime p.
Proof. {
  intros.
  pose proof everyone_is_divisible_by_a_prime p H.
  destruct H1.
  destruct H1.
  destruct (eq_nat_dec x p).
  {
    rewrite e in H1.
    assumption.
  }
  {
    assert (x <= p).
    apply divides_means_no_greater.
    omega.
    assumption.
    assert (x < p).
    omega.
    pose proof H0 x H1 H4.
    contradiction.
  }
} Qed.

Fixpoint list_product (l : list nat) : nat :=
  match l with
  | nil => 1
  | hd :: tl => hd * list_product tl
  end.

Theorem list_product_divisible_by_all : forall l n, (In n l) -> divides n (list_product l).
Proof. {
  intros.
  induction l.
  {
    simpl in H.
    exfalso.
    assumption.
  }
  simpl.
  destruct H.
  {
    subst a.
    apply you_divide_folks_you_multiplied_to_make_l with (a := n) (b := list_product l) (c := (n * list_product l)).
    reflexivity.
  }
  {
    apply IHl in H.
    apply div_mult_compat.
    assumption.
  }
} Qed.

Theorem primes_equiv_two : list_of_all_primes_is_bad -> infinitely_many_primes.
Proof. {
  (* TODO. I think this actually requires me to implement a next_prime, and prove it works... *)

Abort.

Theorem incrementing_breaks_divisibility : forall a b, 2 <= a -> 2 <= b -> divides a b -> ~ divides a (S b).
Proof. {
  intros.
  intro.
  firstorder.
  rename x into div_old.
  rename x0 into div_new.
  destruct (eq_nat_dec div_old div_new).
  {
    subst.
    omega.
  }
  {
    destruct (le_lt_dec div_old div_new).
    {
      assert (div_old < div_new) as l'. omega.
      clear l.
      rename l' into l.
      Lemma product_made_bigger : forall a b c, a < b -> a * c + c <= b * c.
      Proof.
        intros.
        unfold lt in H.
        rewrite <- mult_succ_l.
        apply mult_le_compat; omega.
      Qed.
      pose proof product_made_bigger div_old div_new a l.
      rewrite <- H1 in H3.
      rewrite <- H2 in H3.
      omega.
    }
    {
      pose proof mult_lt_compat_r div_new div_old a.
      firstorder.
    }
  }
} Qed.

Theorem list_product_not_zero :
  forall l, (~ In 0 l) -> list_product l <> 0.
Proof. {
  firstorder.
  induction l; simpl.
  omega.
  simpl in H.
  firstorder.
  apply NPeano.Nat.neq_mul_0.
  firstorder.
} Qed.

Theorem list_max_le_list_product_when_list_contains_no_one :
  forall l, (~ In 0 l) -> list_max l <= list_product l.
Proof. {
  intros.
  induction l.
  {
    simpl.
    omega.
  }
  {
    simpl in H.
    apply Decidable.not_or in H.
    destruct H.

    simpl.
    apply NPeano.Nat.max_lub.
    {
      pose proof list_product_not_zero l.
      apply H1 in H0.
      apply at_least_as_big; assumption.
    }
    {
      simpl in H.
      apply IHl in H0.
      rewrite <- mult_1_l at 1.
      apply mult_le_compat; omega.
    }
  }
} Qed.

(*
(* I had a hard time finding a standard library result for this... *)
Theorem multiplying_by_at_least_two_makes_strictly_bigger :
  forall a b, 2 <= b -> a <> 0 -> a < a * b.
Proof.
  intros.
Admitted.
*)

(* apply NPeano.Nat.mult_lt_mono_noneg. *)

(*
Theorem list_product_bigger_than_max_when_list_contains_more_than_one_element_and_no_one :
  forall l, 1 < length l -> (~ In 0 l) -> (~ In 1 l) -> list_max l < list_product l.
Proof.
  intros.
  induction l.
  { auto. }
  simpl.
  simpl in H0.
  simpl in H1.
  apply Decidable.not_or in H0.
  apply Decidable.not_or in H1.
  destruct H0.
  destruct H1.
  assert (2 <= a).
  omega.

  (* We now massage our inductive hypothesis. *)
  assert (1 < length l).
  {
    destruct (eq_nat_dec (length l) 0).
    {
      destruct l.
      simpl in H.
      omega.
      simpl in e.
      omega.
    }
    destruct (eq_nat_dec (length l) 1).
    {
      admit.
    }
    omega.
  }
  firstorder.

  assert (2 <= list_product l).
  {
    destruct l.
    { firstorder. }
    simpl.
    simpl in H2.
    simpl in H3.
    apply Decidable.not_or in H2.
    apply Decidable.not_or in H3.
    destruct H2.
    destruct H3.
    assert (2 <= n).
    omega.
    pose proof list_product_not_zero l H7.
    rewrite <- mult_1_r at 1.
    apply mult_le_compat; omega.
  }

  destruct (Max.max_spec a (list_max l)) as [ case_lt | case_gte ].
  {
    destruct case_lt.
    rewrite H9.
    rewrite <- mult_1_l with (n := list_max l).
    SearchAbout (_ * _ < _ * _).
    apply NPeano.Nat.mul_lt_mono_nonneg; omega.
  }
  {
    destruct case_gte.
    rewrite H9.
    
(*    apply NPeano.Nat.mul_lt_mono_nonneg. *)
    admit.
  }

Admitted.
*)

Theorem there_are_at_least_two_primes :
  forall l, (forall p, prime p -> In p l) -> 2 <= length l.
Proof. {
  intros.
  pose proof H 2 two_prime.
  pose proof H 3 three_prime.
  destruct (eq_nat_dec (length l) 0).
  {
    assert (l = nil).
    destruct l.
    auto.
    simpl in e.
    omega.
    subst l.
    simpl in H0.
    contradiction.
  }
  destruct (eq_nat_dec (length l) 1).
  {
    destruct l.
    {
      simpl in e.
      omega.
    }
    {
      destruct l.
      {
        simpl in H0.
        simpl in H1.
        firstorder.
      }
      simpl in e.
      omega.
    }
  }
  omega.
} Qed.

Theorem asdf : 0 = 1 -> False.
Proof.
  discriminate.
Qed.

Print asdf.

Theorem list_of_all_primes_is_bad' : list_of_all_primes_is_bad.
Proof.
  cbv [list_of_all_primes_is_bad].
  intros.
  remember (list_product l) as prod.
  pose proof list_product_divisible_by_all l.
  remember (S (list_product l)) as new_prime.
  assert (prime new_prime).
  apply not_divisible_by_any_prime_means_prime.
  subst.
  assert (~ In 0 l).
  firstorder.
  pose proof list_product_not_zero l H2.
  omega.
  intros.
  rewrite Heqnew_prime.
  apply incrementing_breaks_divisibility.
  pose proof H2.
  cbv [prime] in H4.
  exact (proj1 H4).
  firstorder.
  assert (In check l).
  auto.
  exact (H1 check H4).
  pose proof (H0 new_prime H2).
  (* However, we now show that new_prime cannot be in the list, because it's bigger than the maximum. *)
  pose proof list_max_le_list_product_when_list_contains_no_one as prod_big.
  pose proof there_are_at_least_two_primes l H0 as at_least_two_primes.
  pose proof prod_big l.
  
  pose proof no_elements_bigger_than_max l as no_bigger.
  assert (forall p, (~ prime p) -> (~ In p l)) as exclusion.
  {
    intros.
    intro.
    exact (H5 (H p H6)).
  }
  pose proof H4 (exclusion 0 zero_not_prime). (* (exclusion 1 one_not_prime). *)
  assert (list_max l < S (list_product l)) as final_sizing.
  omega.
  subst new_prime.
  exact ((no_bigger (S (list_product l)) final_sizing) H3).
Qed.

Definition prime_list_for k l := (In k l -> prime k) /\ (prime k -> In k l).

Theorem no_number_beyond_which_no_primes : ~ exists k, forall n, n > k -> ~ prime n.
Proof.
  intro.
  destruct H as [prime_bound].
  (* Given a prime bound k, we can construct a list of all primes. *)
  (* Here up_to starts at prime_bound, and with nil, and counts down to zero. *)
  Fixpoint make_list_of_primes prime_bound up_to so_far (up_to_constraint : up_to <= prime_bound) :
    (forall n,
     ((S up_to) <= n -> n <= prime_bound -> prime n -> In n so_far) /\
     (In n so_far -> prime n) /\
     (prime_bound < n -> ~ In n so_far)) ->
    exists l, (forall n,
     (n <= prime_bound -> prime n -> In n l) /\
     (In n l -> prime n) /\
     (prime_bound < n -> ~ In n l)).
  Proof.
    intro.
    (* Start by destructing on up_to. *)
    destruct up_to.
    {
      clear make_list_of_primes. (* No recursive calls in this branch! *)
      exists so_far.
      intro.
      split.
      {
        intros.
        assert (1 <= n).
        { unfold prime in H1. apply proj1 in H1. omega. }
        firstorder.
      }
      {
        exact (proj2 (H n)).
      }
    }
    {
      assert (up_to <= prime_bound) as up_to_constraint'. omega.
      (* Here we test if up_to is a prime, and if so, add it into the list. *)
      destruct (prime_dec (S up_to)).
      {
        remember ((S up_to) :: so_far) as new_list.
        (* Prove that our new list provides updated conditions. *)
        assert (forall n,
          (S up_to <= n ->
           n <= prime_bound -> prime n -> In n new_list) /\
          (In n new_list -> prime n) /\
          (prime_bound < n -> ~ In n new_list)) as preconditions.
        {
          intro.
          split.
          {
            intros.
            destruct (eq_nat_dec (S up_to) n).
            {
              subst.
              simpl.
              left.
              reflexivity.
            }
            {
              assert (S (S up_to) <= n). omega.
              pose proof H n.
              clear make_list_of_primes H.
              intros.
              rewrite Heqnew_list.
              right.
              firstorder.
            }
          }
          {
            clear make_list_of_primes.
            split.
            {
              rewrite Heqnew_list.
              simpl.
              intro.
              destruct H0.
              { rewrite H0 in p. assumption. }
              {
                specialize (H n).
                apply proj2 in H.
                apply proj1 in H.
                apply H in H0.
                assumption.
              }
            }
            {
              intro.
              rewrite Heqnew_list.
              simpl.
              intro.
              destruct H1.
              {
                omega. 
              }
              {
                pose proof (proj2 (proj2 (H n)) H0).
                contradiction.
              }
            }
          }
        }
        (* Do a recursive call! *)
        exact (make_list_of_primes prime_bound up_to new_list up_to_constraint' preconditions).
      }
      {
        rename n into p.
        (* If the number isn't prime, then we're fine as is, pretty much. *)
        rename so_far into new_list.
        assert (forall n,
          (S up_to <= n ->
           n <= prime_bound -> prime n -> In n new_list) /\
          (In n new_list -> prime n) /\
          (prime_bound < n -> ~ In n new_list)) as preconditions.
        {
          intro.
          split.
          {
            intros.
            destruct (eq_nat_dec (S up_to) n).
            {
              subst.
              contradiction.
            }
            {
              assert (S (S up_to) <= n). omega.
              pose proof H n.
              clear make_list_of_primes H.
              intros.
              exact (proj1 H4 H3 H1 H2).
            }
          }
          {
            exact (proj2 (H n)).
          }
        }
        (* Do a recursive call! *)
        exact (make_list_of_primes prime_bound up_to new_list up_to_constraint' preconditions).
      }
    } 
  Defined.

(*
  Theorem make_list_of_primes prime_bound up_to so_far :
    (forall n,
     ((S up_to) <= n -> n <= prime_bound -> prime n -> In n so_far) /\
     (In n so_far -> prime n) /\
     (prime_bound < n -> ~ In n so_far)) ->
    exists l, (forall n,
     (n <= prime_bound -> prime n -> In n l) /\
     (In n l -> prime n) /\
     (prime_bound < n -> ~ In n l)).
  Proof.
  Admitted.
*)

  assert (forall n,
           ((S prime_bound) <= n -> n <= prime_bound -> prime n -> In n nil) /\
           (In n nil -> prime n) /\
           (prime_bound < n -> ~ In n nil)) as base_case.
  {
    intros.
    firstorder.
  }
  assert (prime_bound <= prime_bound) as up_to_constraint. omega.
  pose proof make_list_of_primes prime_bound prime_bound nil up_to_constraint base_case as list_of_all_primes.
  clear base_case.
  destruct list_of_all_primes as [prime_list].
  rename H0 into prime_list_good.

  assert (forall p, (In p prime_list -> prime p) /\ (prime p -> In p prime_list)).
  {
    intros.
    split; intro.
    {
      exact (proj1 (proj2 (prime_list_good p)) H0).
    }
    {
      pose proof proj1 (prime_list_good p).
      destruct (le_lt_dec p prime_bound); firstorder.
    }
  }

  assert (forall p, In p prime_list -> prime p) as cond1.
  {
    intro.
    specialize (H0 p).
    destruct H0.
    assumption.
  }
  assert (forall p, prime p -> In p prime_list) as cond2.
  {
    intro.
    specialize (H0 p).
    destruct H0.
    assumption.
  }
  exact (list_of_all_primes_is_bad' prime_list cond1 cond2).
Qed.

Theorem the_thing : forall l, ~ (forall p, In p l <-> prime p).
Proof.
  pose proof list_of_all_primes_is_bad'.
  unfold list_of_all_primes_is_bad in H.
  intros.
  intro.
  assert (forall p, In p l -> prime p) as bad1.
  clear H.
  firstorder.
  assert (forall p, prime p -> In p l) as bad2.
  clear H.
  firstorder.
  exact (H l bad1 bad2).
Qed.

Theorem always_not_not_a_bigger_prime : forall n, ~ ~ exists p, p > n /\ prime p.
Proof.
  pose proof no_number_beyond_which_no_primes.
  firstorder.
Qed.

Theorem there_is_always_a_bigger_prime : forall n, exists p, n < p /\ prime p.
Proof.
  intros.
  rename n into prime_bound.
  assert (forall n,
           ((S prime_bound) <= n -> n <= prime_bound -> prime n -> In n nil) /\
           (In n nil -> prime n) /\
           (prime_bound < n -> ~ In n nil)) as base_case.
  {
    intros.
    firstorder.
    omega.
  }
  assert (prime_bound <= prime_bound) as up_to_constraint. omega.
  pose proof make_list_of_primes prime_bound prime_bound nil up_to_constraint base_case as list_of_all_primes.
  clear base_case.
  destruct list_of_all_primes as [prime_list].
  remember (S (list_product prime_list)) as big_number.
  pose proof everyone_is_divisible_by_a_prime big_number.

  assert (~ In 0 prime_list) as prime_list_has_no_zero.
  {
    intro.
    specialize (H 0).
    firstorder.
  }
  pose proof list_product_not_zero prime_list prime_list_has_no_zero as lp_nz.
  assert (2 <= big_number) as two_le_big_number.
  omega.

  apply H0 in two_le_big_number.
  destruct two_le_big_number.
  destruct H1.
  rename x into new_prime.
  exists new_prime.
  split.
  Focus 2.
  assumption.

  (* We'll show prime_bound < new_prime by first showing that new_prime isn't in prime_list. *)
  assert (~ In new_prime prime_list).
  Focus 2.

  pose proof proj1 (H new_prime).
  destruct (le_lt_dec new_prime prime_bound).
  pose proof H4 l H1.
  contradiction.
  assumption.

  intro.

  assert (~ divides new_prime (list_product prime_list)).
  {
    intro.
    pose proof proj1 H1 as two_le_new_prime.
    assert (~ In 0 prime_list) as zero_not_in_prime_list.
    {
      intro.
      pose proof proj1 (proj2 (H 0)) H5.
      pose proof zero_not_prime.
      contradiction.
    }
    pose proof list_product_not_zero prime_list zero_not_in_prime_list as prod_nz.
    SearchAbout divides le.
    pose proof divides_means_no_greater new_prime (list_product prime_list) prod_nz H4.
    assert (2 <= list_product prime_list) as two_le_prod. omega.
    pose proof incrementing_breaks_divisibility new_prime (list_product prime_list) two_le_new_prime two_le_prod H4.
    subst.
    contradiction.
  }

  pose proof list_product_divisible_by_all prime_list new_prime.
  firstorder.
Qed.

(* This comment is to work around a bug in company coq. *)
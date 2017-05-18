
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Arith.
Require Import Omega.

Add LoadPath ".".
Require Import well_founded.

(* Some simple notations. *)
Notation " [ ] " := nil.
Notation " [ x ] " := (cons x nil).
Notation " x :: y " := (cons x y).
Notation " [ x ; .. ; y ] " := (cons x .. (cons y nil) ..).
Infix "==n" := beq_nat (no associativity, at level 50).

(* Define our notion of languages. *)

Inductive bit :=
  | B_zero
  | B_one.

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

(* Define some computational semantics. *)

Inductive stack_program :=
  | ISeq (p1 p2 : stack_program)
  | IPush (stack b : bit) (c : stack_program)
  | ILoop (stack : bit) (l : stack_program) (c : stack_program)
  | IAccept
  | IReject.

Definition indexed_pop (index : bit) (stack1 stack2 : bits) : bit * bits * bits :=
  match index with
  | B_zero =>
    match stack1 with
    | nil => (B_zero, stack1, stack2)
    | x :: stack1' => (x, stack1', stack2)
    end
  | B_one =>
    match stack2 with
    | nil => (B_zero, stack1, stack2)
    | x :: stack2' => (x, stack1, stack2')
    end
  end.

Fixpoint small_step_helper (p : stack_program) (stack1 stack2 : bits) : (stack_program * bits * bits) :=
  match p with
  | ISeq p1 p2 =>
    match small_step_helper p1 stack1 stack2 with
    | (_, stack1', stack2') =>
      (p2, stack1', stack2')
    end
  | IPush index b c =>
    match index with
    | B_zero => (c, b :: stack1, stack2)
    | B_one  => (c, stack1, b :: stack2)
    end
  | ILoop index l c =>
    match indexed_pop index stack1 stack2 with
    | (popped_bit, stack1', stack2') =>
      match popped_bit with
      | B_zero => (c, stack1', stack2')
      | B_one  => ((ISeq l (ILoop index l c)), stack1', stack2')
      end
    end
  | IAccept | IReject => (p, stack1, stack2)
  end.

Definition small_step (state : (stack_program * bits * bits)) : (stack_program * bits * bits) :=
  match state with
  | pair (pair p stack1) stack2 =>
    small_step_helper p stack1 stack2
  end.

Fixpoint perform_n_steps n state :=
  match n with
  | 0 => state
  | S n' => small_step (perform_n_steps n' state)
  end.

Notation " 'PushA' 0 " := (IPush B_zero B_zero).
Notation " 'PushA' 1 " := (IPush B_zero B_one).
Notation " 'PushB' 0 " := (IPush B_one B_zero).
Notation " 'PushB' 1 " := (IPush B_one B_one).
Notation " 'LoopA' " := (ILoop B_zero).
Notation " 'LoopB' " := (ILoop B_one).
Notation " a ; b " := (ISeq (a IReject) b) (at level 50).

Definition tiny_prog : stack_program := IReject.

Definition prog1 : stack_program :=
  PushB 0 ; PushA 1 IReject.

Definition prog2 : stack_program :=
  PushA 1; LoopA (PushA 1 IReject) IReject.

Definition is_work_state (program : stack_program * bits * bits) : Prop :=
  let p := fst (fst program) in
  p <> IAccept /\ p <> IReject.

Definition is_halt_state (program : stack_program * bits * bits) : Prop :=
  let p := fst (fst program) in
  p = IAccept \/ p = IReject.

Definition always_halts program : Prop :=
  forall input, exists n,
    let final_state := perform_n_steps n (program, input, []) in
    is_halt_state final_state.

Lemma halt_stays_halted :
  forall triplet, is_halt_state triplet -> is_halt_state (small_step triplet).
Proof.
  intros.
  unfold small_step.
  destruct triplet.
  destruct p.
  destruct s; unfold is_halt_state in H; firstorder; simpl in H; discriminate.
Qed.

Lemma performing_steps_sums :
  forall triplet n m, perform_n_steps n (perform_n_steps m triplet) = perform_n_steps (n + m) triplet.
Proof.
  intros.
  induction n; simpl; try rewrite IHn; reflexivity.
Qed.

Lemma halt_stays_halted_forever :
  forall triplet, is_halt_state triplet -> forall n, is_halt_state (perform_n_steps n triplet).
Proof.
  intros.
  induction n.
  { assumption. }
  {
    simpl.
    exact (halt_stays_halted (perform_n_steps n triplet) IHn).
  }
Qed.

Lemma le_decomp : forall a b, a <= b -> exists k, b = a + k.
Proof.
  intros.
  induction b.
  { exists 0. omega. }
  {
    destruct (eq_nat_dec a (S b)).
    { exists 0. omega. }
    {
      assert (a <= b). omega.
      firstorder.
      exists (S x).
      omega.
    }
  }
Qed.

Lemma halt_stays_halted_forever_alt :
  forall triplet n m, n <= m -> is_halt_state (perform_n_steps n triplet) -> is_halt_state (perform_n_steps m triplet).
Proof.
  intros.
  pose proof le_decomp n m H as decomp.
  destruct decomp.
  pose proof halt_stays_halted_forever (perform_n_steps n triplet) H0 x as big.
  rewrite performing_steps_sums in big.
  subst.
  rewrite plus_comm.
  assumption.
Qed.

Lemma work_halt_contradict : forall state, is_work_state state -> is_halt_state state -> False.
Proof.
  destruct state.
  destruct p.
  destruct s; firstorder.
Qed.

Theorem always_working_means_doesnt_halt :
  forall program,
    (exists input, forall n, exists n0, n <= n0 /\ is_work_state (perform_n_steps n0 (program, input, []))) ->
    ~ always_halts program.
Proof.
  intros.
  destruct H.
  rename x into input.
  intro.
  unfold always_halts in H0.
  specialize (H0 input).
  destruct H0.
  rename x into point_at_which_halts.
  specialize (H point_at_which_halts).
  destruct H.
  rename x into still_working.
  destruct H.
  pose proof le_decomp point_at_which_halts still_working H.
  destruct H2.
  subst.
  remember (perform_n_steps point_at_which_halts (program, input, [])) as halted.
  pose proof halt_stays_halted_forever halted H0.
  rewrite Heqhalted in H2.
  specialize (H2 x).
  rewrite performing_steps_sums in H2.
  rewrite plus_comm in H1.
  pose proof work_halt_contradict.
  firstorder.
Qed.

Theorem tiny_halting : always_halts tiny_prog.
Proof.
  unfold always_halts.
  intros.
  exists 0.
  simpl.
  right.
  reflexivity.
Qed.

Theorem halting1 : always_halts prog1.
Proof.
  unfold always_halts.
  intros.
  exists 2.
  simpl.
  right.
  reflexivity.
Defined.

(* Begin code to convert always-halting stack machines into functions. *)

Definition halts_at_n_predicate (p : stack_program) (stack1 stack2 : bits) (n : nat) : bool :=
  let state := fst (fst (perform_n_steps n (p, stack1, stack2))) in
  match state with
  | IAccept | IReject => true
  | _ => false
  end.

Lemma wtf : forall (t1 t2 : Type) (f : t1 -> t2) (a b : t1), a = b -> f a = f b.
Proof.
  intros.
  f_equal.
  assumption.
Qed.

Print wtf.
Unset Implicit Arguments.
Print f_equal.

Print eq_refl.

Compute (@eq_refl).

Lemma dumb : forall (p1 p2 : Prop), (p1 = p2) -> (p2 -> p1).
Proof.
  firstorder.
  rewrite H.
  assumption.
Qed.

Theorem always_halts_means_many (p : stack_program) : always_halts p -> forall stack1, many_trues (halts_at_n_predicate p stack1 []).
Proof.
  intros.
  unfold many_trues.
  intros.
  rename n into requested_point.
  unfold always_halts in H.
  specialize (H stack1).
  destruct H.
  rename x into halting_point.
  destruct (le_gt_dec requested_point halting_point).
  {
    exists halting_point.
    firstorder; unfold halts_at_n_predicate; setoid_rewrite H; reflexivity.
  }
  {
    exists requested_point.
    split; [ omega |].
    apply halt_stays_halted_forever_alt with (m := requested_point) in H.
    firstorder; unfold halts_at_n_predicate; setoid_rewrite H; reflexivity.
    omega.
  }
Defined.

Definition run_to_completion (p : stack_program) (halting : always_halts p) (stack1 : bits) : stack_program * bits * bits.
  refine ((Fix (gen_call_r_wf
    (halts_at_n_predicate p stack1 [])
    (always_halts_means_many p halting stack1)) (fun nat => _) _) 2).
  intros.

  (* We now proceed to define our function. *)
  intros.
  rename x into step_number.
  (* We now check if the function actually halts after x steps. *)
  remember (halts_at_n_predicate p stack1 [] step_number) as answer.
  destruct answer.
  {
    exact (perform_n_steps step_number (p, stack1, [])).
  }
  {
    specialize (H (S step_number)).
    unfold gen_call_r in H.

    Lemma my_eq_sym : forall (A : Type) (x y : A), x = y -> y = x.
    Proof.
      exact (fun (A : Type) (x y : A) (H : x = y) =>
match H in (_ = y0) return (y0 = x) with
| eq_refl => eq_refl
end).
    Defined.

    apply my_eq_sym in Heqanswer.
    exact (H (conj Heqanswer (eq_refl (S step_number)))).
  }
Defined.

Theorem only_one_answer : forall p input n m,
  let comp1 := perform_n_steps n (p, input, []) in
  let comp2 := perform_n_steps m (p, input, []) in
  is_halt_state comp1 -> is_halt_state comp2 -> comp1 = comp2.
Proof.
  intros.
  subst comp1 comp2.
  (* TODO: Prove for n <= m, then handle general case. *)
Admitted.

Theorem run_to_completion_correct (p : stack_program) (input : bits) :
  forall halting_proof n, is_halt_state (perform_n_steps n (p, input, [])) ->
  run_to_completion p halting_proof input = perform_n_steps n (p, input, []).
Proof.
  intros.
  unfold run_to_completion.
  cbv.

(* *)

Require Import Arith.

Fixpoint sum_up_to (n : nat) :=
  match n with
  | 0 => 0
  | S n' => n + sum_up_to n'
  end.

Theorem fact : forall n, 2 * sum_up_to n = n * (n + 1).
Proof.
  intros.
  induction n.
  {
    (* Prove the base case. *)
    reflexivity.
  }
  {
    (* Prove the inductive case. *)
    (* Unfold the definition of sum_up_to and refold it once,
       to effectively pull the +1 out of its argument. *)
    unfold sum_up_to.
    fold sum_up_to.
    (* Distribute multiplication once, so our inductive
       hypothesis exactly fits a subterm. *)
    rewrite mult_plus_distr_l.
    (* Rewrite using our inductive hypothesis. *)
    rewrite IHn.
    (* Now that sum_up_to is eliminated, simple
       semi-ring properties suffice. *)
    ring.
  }
Qed.

Print fact.
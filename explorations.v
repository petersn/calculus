
(*
	Here's a weird example.
	Naively, one would hope that whenever a proof term p exists, that we could instead complete the proof by replacing random subterms with holes, and refining the result.
	Then, in each subgoal we could exact whatever was removed from that hole (modulo whatever unification has already solved/partially solved), and complete the proof.
	This simply doesn't hold when one hole appears in the scope of a binder whose value is determined by another hole.
	As an example:
*)
Theorem six_factors : exists a b, a * b = 6.
Proof.
  exists 2. exists 3.
  exact eq_refl.
Qed.

Theorem six_factors' : exists a b, a * b = 6.
Proof.
  (* Let us expand out this proof term with lets to form binders, with which we statically pick the factors once out front. *)
  exact (
    let a' := 2 in
    let b' := 3 in 
    ex_intro (fun a : nat => exists b : nat, a * b = 6) a'
      (ex_intro (fun b : nat => a' * b = 6) b' eq_refl)
  ).
Qed.

Theorem six_factors'' : exists a b, a * b = 6.
Proof.
  (* Now let us repeat the same, only using refine. *)
  refine (
    let a' := _ in
    let b' := _ in 
    ex_intro (fun a : nat => exists b : nat, a * b = 6) a'
      (ex_intro (fun b : nat => a' * b = 6) b' _)
  ).
  (* Here filling in these holes with 2, 3, and eq_refl respectively solves the problem. *)
  (* However, as each hole is nested inside a binder formed with another hole, this information isn't carried between the goals, and the proof becomes impossible from this point. *)
  (* To demonstrate this, we will attempt to fill in the holes correctly: *)
  exact 2.
  exact 3.
  (* Unsolvable goal: a' * b' = 6, where a' and b' are just naturals. *)
  admit.
Qed.

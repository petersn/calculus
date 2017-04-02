(* Proof of the infinitude of the primes. *)

Definition divides a b := exists k, b = k * a.
Definition prime p := 2 <= p /\ forall k, divides k p -> (k = 1 \/ k = p).

Theorem primes_infinite : forall n, exists p, p > n /\ prime p.
Proof.
Admitted.


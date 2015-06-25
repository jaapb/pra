Require Import pra.QuoteTerm.

(* Primality of natural numbers *)
Definition divides (n m : nat) : Prop := exists k : nat, k <= m /\ k * n = m.

Definition prime (n : nat) : Prop :=
  n > 1 /\ (forall d : nat, d <= n -> divides d n -> (d = 1 \/ d = n)).

Theorem prime_test: prime 61.
Proof.
  unfold prime. unfold divides. Time PRA.
Qed.

Theorem prime_test2: ~(prime 60).
Proof.
  unfold prime. unfold divides. Time PRA.
Qed.

Theorem prime_test3: ~(prime 100).
Proof.
  unfold prime. unfold divides. Time PRA.
Qed.

Theorem prime_test4: prime 101.
Proof.
  unfold prime. unfold divides. Time PRA.
Qed.


(* Primality of integers with ZArith *)
Definition zdivides (n m : Z) : Prop :=
  exists k : Z, ((k > 0)%Z /\ (k <= m)%Z) /\ (k * n)%Z = m.

Definition zprime (n : Z) : Prop :=
  (n > 1)%Z /\ (forall d : Z,
  (d > 0)%Z /\ (d <= n)%Z -> zdivides d n -> (d = 1%Z \/ d = n)).

Theorem zprime_test: zprime 61.
Proof.
  unfold zprime. unfold zdivides. Time PRA.
Qed.

Theorem zprime_test2: ~(zprime 60).
Proof.
  unfold zprime. unfold zdivides. Time PRA.
Qed.

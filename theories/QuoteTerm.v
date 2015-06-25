Require Export List.
Require Export pra.

Declare ML Module "quoteTerm".

Lemma ok1 : forall p : form, istrue (checkValid p) -> isValid p.
Proof.
  intros.
  elim (ok p).
  auto.
Qed.

Ltac PRA :=
  quotegoal; apply ok1; simpl; auto.

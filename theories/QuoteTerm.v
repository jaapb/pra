Require Export List.
Require Export pra.pra.

Declare ML Module "pra_plugin".

Lemma ok1 : forall p : form, istrue (checkValid p) -> isValid p.
Proof.
  intros.
  elim (ok p).
  auto.
Qed.

Ltac PRA :=
  quotegoal; apply ok1; simpl; auto.

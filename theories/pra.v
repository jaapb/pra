Require Export Arith.
Require Export ZArith.
Require Export List.

(*** The Succ function ***)
(* Succ x y l means that x and y occur directly after each other in the list l *)

Fixpoint Succ (A: Set) (x: A) (y: A) (l: list A) {struct l}: Prop :=
  match l with
  | nil => False
  | hd :: tl => match tl with
                      | nil => False
                      | hd2 :: tl2 => ((x = hd) /\ (y = hd2)) \/ (Succ A x y tl)
                      end
  end.

(***  Primitive Recursive Arithmetic  ***)

Inductive form : Set :=
  | f_lt : nat -> nat -> form
  | f_le : nat -> nat -> form
  | f_eq : nat -> nat -> form
  | f_p_eq: (nat * nat) -> (nat * nat) -> form
  | f_ge : nat -> nat -> form
  | f_gt : nat -> nat -> form
  | f_zlt : Z -> Z -> form
  | f_zle : Z -> Z -> form
  | f_zeq : Z -> Z -> form
  | f_p_zeq: (Z * Z) -> (Z * Z) -> form
  | f_zge : Z -> Z -> form
  | f_zgt : Z -> Z -> form
  | f_not : form -> form
  | f_and : form -> form -> form
  | f_or : form -> form -> form
  | f_imp : form -> form -> form
  | f_all : nat -> (nat -> form) -> form
  | f_ex : nat -> (nat -> form) -> form
  | f_all_el : list nat -> (nat -> form) -> form
  | f_ex_el : list nat -> (nat -> form) -> form
  | f_in : nat -> list nat -> form
  | f_p_in : (nat * nat) -> list (nat * nat) -> form
  | f_succ: nat -> nat -> list nat -> form
	| f_zsucc: Z -> Z -> list Z -> form
  | f_zall : Z -> (Z -> form) -> form
  | f_zex : Z -> (Z -> form) -> form
  | f_zall_el : list Z -> (Z -> form) -> form
  | f_zex_el : list Z -> (Z -> form) -> form
  | f_zin : Z -> list Z -> form
  | f_p_zin : (Z * Z) -> list (Z * Z) -> form.

(***  Boolean logic  ***)

Fixpoint b_le (n : nat) : nat -> bool :=
  match n with
  | O => fun m : nat => true
  | S x => fun m : nat => match m with
                          | O => false
                          | S y => b_le x y
                          end
  end.

Fixpoint b_eq (n m : nat) {struct m} : bool :=
  match n, m with
  | O, O => true
  | O, S y => false
  | S x, O => false
  | S x, S y => b_eq x y
  end.

Definition b_lt (n m : nat) := b_le (S n) m.
Definition b_ge (n m : nat) := b_le m n.
Definition b_gt (n m : nat) := b_lt m n.

Definition b_not (x : bool) :=
  match x with
  | true => false
  | false => true
  end.
Definition b_and (x y : bool) :=
  match x with
  | true => y
  | false => false
  end.
Definition b_or (x y : bool) := match x with
                                | true => true
                                | false => y
                                end.
Definition b_imp (x y : bool) := match x with
                                 | true => y
                                 | false => true
                                 end.

Definition b_p_eq (n m: nat * nat): bool :=
  match n, m with
  | pair n1 n2, pair m1 m2 => b_and (b_eq n1 m1) (b_eq n2 m2)
  end.

Fixpoint b_all (b : nat) (f : nat -> bool) {struct b} : bool :=
  match b with
  | O => (f O)
  | S m => b_and (f (S m)) (b_all m f)
  end.

Fixpoint b_ex (b : nat) (f : nat -> bool) {struct b} : bool :=
  match b with
  | O => (f O)
  | S m => b_or (f (S m)) (b_ex m f)
  end.

Fixpoint b_all_el (l : list nat) (f : nat -> bool) {struct l} : bool :=
  match l with
  | nil => true
  | hd :: tl => b_and (f hd) (b_all_el tl f)
  end.

Fixpoint b_ex_el (l : list nat) (f : nat -> bool) {struct l} : bool :=
  match l with
  | nil => false
  | hd :: tl => b_or (f hd) (b_ex_el tl f)
  end.

Fixpoint b_in (n: nat) (l: list nat) {struct l}: bool :=
  match l with
  | nil => false
  | hd :: tl => b_or (b_eq hd n) (b_in n tl)
  end.

Fixpoint b_p_in (p: nat * nat) (l: list (nat * nat)) {struct l}: bool :=
  match l with
  | nil => false
  | hd :: tl => b_or (b_p_eq hd p) (b_p_in p tl)
  end.

Fixpoint b_succ (x y: nat) (l: list nat) {struct l} : bool :=
  match l with
  | nil => false
  | hd :: tl => match tl with
                      | nil => false
                      | hd2 :: tl2 => (b_or (b_and (b_eq hd x) (b_eq hd2 y)) (b_succ x y tl))
                      end
  end.

Fixpoint b_pos_less (x y : positive) (r : bool) {struct x} : bool :=
  match x with
  | xO x' =>
      match y with
      | xO y' => b_pos_less x' y' r
      | xI y' => b_pos_less x' y' true
      | xH => false
      end
  | xI x' =>
      match y with
      | xO y' => b_pos_less x' y' false
      | xI y' => b_pos_less x' y' r
      | xH => false
      end
  | xH => match y with
          | xO y' => true
          | xI y' => true
          | xH => r
          end
  end.


Fixpoint b_pos_eq (x y : positive) {struct x} : bool :=
  match x with
  | xO x' =>
      match y with
      | xO y' => b_pos_eq x' y'
      | xI y' => false
      | xH => false
      end
  | xI x' =>
      match y with
      | xO y' => false
      | xI y' => b_pos_eq x' y'
      | xH => false
      end
  | xH => match y with
          | xO y' => false
          | xI y' => false
          | xH => true
          end
  end.

Definition b_zeq (x y : Z) : bool :=
  match x with
  | Zpos x' =>
      match y with
      | Zpos y' => b_pos_eq x' y'
      | Zneg y' => false
      | Z0 => false
      end
  | Zneg x' =>
      match y with
      | Zpos y' => false
      | Zneg y' => b_pos_eq x' y'
      | Z0 => false
      end
  | Z0 => match y with
          | Zpos y' => false
          | Zneg y' => false
          | Z0 => true
          end
  end.

Definition b_p_zeq (p q: Z * Z) : bool :=
  match p, q with
     pair p1 p2, pair q1 q2 => (b_and (b_zeq p1 q1) (b_zeq p2 q2))
  end.
  
Definition b_zle (x y : Z) : bool :=
  match x with
  | Zpos x' =>
      match y with
      | Zpos y' => b_pos_less x' y' true
      | Zneg y' => false
      | Z0 => false
      end
  | Zneg x' =>
      match y with
      | Zpos y' => true
      | Zneg y' => b_pos_less y' x' true
      | Z0 => true
      end
  | Z0 => match y with
          | Zpos y' => true
          | Zneg y' => false
          | Z0 => true
          end
  end.

Definition b_zlt (x y : Z) : bool :=
  match x with
  | Zpos x' =>
      match y with
      | Zpos y' => b_pos_less x' y' false
      | Zneg y' => false
      | Z0 => false
      end
  | Zneg x' =>
      match y with
      | Zpos y' => true
      | Zneg y' => b_pos_less y' x' false
      | Z0 => true
      end
  | Z0 => match y with
          | Zpos y' => true
          | Zneg y' => false
          | Z0 => false
          end
  end.

Definition b_zgt (x y : Z) : bool :=
  match x with
  | Zpos x' =>
      match y with
      | Zpos y' => b_pos_less y' x' false
      | Zneg y' => true
      | Z0 => true
      end
  | Zneg x' =>
      match y with
      | Zpos y' => false
      | Zneg y' => b_pos_less x' y' false
      | Z0 => false
      end
  | Z0 => match y with
          | Zpos y' => false
          | Zneg y' => true
          | Z0 => false
          end
  end.

Definition b_zge (x y : Z) : bool :=
  match x with
  | Zpos x' =>
      match y with
      | Zpos y' => b_pos_less y' x' true
      | Zneg y' => true
      | Z0 => true
      end
  | Zneg x' =>
      match y with
      | Zpos y' => false
      | Zneg y' => b_pos_less x' y' true
      | Z0 => false
      end
  | Z0 => match y with
          | Zpos y' => false
          | Zneg y' => true
          | Z0 => true
          end
  end.

Fixpoint b_all_nat (n: nat) (f: Z -> bool) {struct n}: bool :=
  match n with
  | O => true
  | S n' => b_and (f (Zpos (P_of_succ_nat n'))) (b_all_nat n' f)
  end.

Definition b_zall (n : Z) (f : Z -> bool) : bool :=
  match n with
  | Z0 => true
  | Zneg x => true
  | Zpos p => b_all_nat (nat_of_P p) f
  end.

Fixpoint b_ex_nat (n : nat) (f : Z -> bool) {struct n} : bool :=
  match n with
  | O => false
  | S n' => b_or (f (Zpos (P_of_succ_nat n'))) (b_ex_nat n' f)
  end.

Definition b_zex (n : Z) (f : Z -> bool) : bool :=
  match n with
  | Z0 => false
  | Zneg x => false
  | Zpos p => b_ex_nat (nat_of_P p) f
  end.

Fixpoint b_zall_el (l : list Z) (f : Z -> bool) {struct l} : bool :=
  match l with
  | nil => true
  | hd :: tl => b_and (f hd) (b_zall_el tl f)
  end.

Fixpoint b_zex_el (l : list Z) (f : Z -> bool) {struct l} : bool :=
  match l with
  | nil => false
  | hd :: tl => b_or (f hd) (b_zex_el tl f)
  end.

Fixpoint b_zin (z: Z) (l: list Z) {struct l}: bool :=
  match l with
  | nil => false
  | hd :: tl => b_or (b_zeq z hd) (b_zin z tl)
  end.

Fixpoint b_p_zin (p: Z * Z) (l: list (Z * Z)) {struct l} : bool :=
  match l with
  | nil => false
  | hd :: tl => b_or (b_p_zeq p hd) (b_p_zin p tl)
  end.

Fixpoint b_zsucc (x y: Z) (l: list Z) {struct l} : bool :=
  match l with
  | nil => false
  | hd :: tl => match tl with
                      | nil => false
                      | hd2 :: tl2 => (b_or (b_and (b_zeq hd x) (b_zeq hd2 y)) (b_zsucc x y tl))
                      end
  end.

(***  Translate form to bool  ***)

Fixpoint checkValid (p : form) : bool :=
  match p with
  | f_lt s t => b_lt s t
  | f_le s t => b_le s t
  | f_eq s t => b_eq s t
  | f_p_eq s t => b_p_eq s t
  | f_ge s t => b_ge s t
  | f_gt s t => b_gt s t
  | f_zlt s t => b_zlt s t
  | f_zle s t => b_zle s t
  | f_zeq s t => b_zeq s t
  | f_p_zeq s t => b_p_zeq s t
  | f_zge s t => b_zge s t
  | f_zgt s t => b_zgt s t
  | f_not q => b_not (checkValid q)
  | f_and q r => b_and (checkValid q) (checkValid r)
  | f_or q r => b_or (checkValid q) (checkValid r)
  | f_imp q r => b_imp (checkValid q) (checkValid r)
  | f_all t f => b_all t (fun y : nat => checkValid (f y))
  | f_ex t f => b_ex t (fun y : nat => checkValid (f y))
  | f_all_el l f => b_all_el l (fun y : nat => checkValid (f y))
  | f_ex_el l f => b_ex_el l (fun y : nat => checkValid (f y))
  | f_in n l => b_in n l
  | f_p_in n l => b_p_in n l
  | f_succ s t l => b_succ s t l
	| f_zsucc s t l => b_zsucc s t l
  | f_zall n p => b_zall n (fun s : Z => checkValid (p s))
  | f_zex n p => b_zex n (fun s : Z => checkValid (p s))
  | f_zall_el l p => b_zall_el l (fun s : Z => checkValid (p s))
  | f_zex_el l p => b_zex_el l (fun s : Z => checkValid (p s))
  | f_zin z l => b_zin z l
  | f_p_zin p l => b_p_zin p l
  end.

(***  Translate form to Prop  ***)

Fixpoint isValid (p : form) : Prop :=
  match p with
  | f_lt s t => s < t
  | f_le s t => s <= t
  | f_eq s t => s = t
  | f_p_eq s t => s = t
  | f_ge s t => s >= t
  | f_gt s t => s > t
  | f_zlt s t => (s < t)%Z
  | f_zle s t => (s <= t)%Z
  | f_zeq s t => s = t
  | f_p_zeq s t => s = t
  | f_zge s t => (s >= t)%Z
  | f_zgt s t => (s > t)%Z
  | f_not q => ~ isValid q
  | f_and q r => isValid q /\ isValid r
  | f_or q r => isValid q \/ isValid r
  | f_imp q r => isValid q -> isValid r
  | f_all t f => forall y : nat, y <= t -> isValid (f y)
  | f_ex t f => exists y : nat, y <= t /\ isValid (f y)
  | f_all_el l f => forall y : nat, In y l -> isValid (f y)
  | f_ex_el l f => exists y : nat, In y l /\ isValid (f y)
  | f_in n l => (In n l)
  | f_p_in p l => (In p l)
  | f_succ s t l => Succ nat s t l
	| f_zsucc s t l => Succ Z s t l
  | f_zall n f => forall s : Z, (s > 0)%Z /\ (s <= n)%Z -> isValid (f s)
  | f_zex n f => exists s : Z, ((s > 0)%Z /\ (s <= n)%Z) /\ isValid (f s)
  | f_zall_el l f => forall s : Z, In s l -> isValid (f s)
  | f_zex_el l f => exists s : Z, In s l /\ isValid (f s)
  | f_zin z l => (In z l)
  | f_p_zin p l => (In p l)
  end.

(***  Translate bool to Prop  ***)

Definition istrue (x : bool) := if x then True else False.

Lemma b_and_intro :
 forall x y : bool, istrue x -> istrue y -> istrue (b_and x y).
Proof.
   intro x. case x. simpl in |- *. tauto. simpl in |- *. tauto.
Qed.

Lemma b_and_elim1 : forall x y : bool, istrue (b_and x y) -> istrue x.
Proof.
   intro x. case x. simpl in |- *. tauto. simpl in |- *. tauto.
Qed.

Lemma b_and_elim2 : forall x y : bool, istrue (b_and x y) -> istrue y.
Proof.
   intro x. case x. simpl in |- *. tauto. simpl in |- *. tauto.
Qed.

Lemma b_or_intro1 : forall x y : bool, istrue x -> istrue (b_or x y).
Proof.
   intro x. case x. simpl in |- *. tauto. simpl in |- *. tauto.
Qed.

Lemma b_or_intro2 : forall x y : bool, istrue y -> istrue (b_or x y).
Proof.
   intro x. case x. simpl in |- *. tauto. simpl in |- *. tauto.
Qed.

Lemma b_or_elim :
 forall x y : bool, istrue (b_or x y) -> istrue x \/ istrue y.
Proof.
   intro x. case x. simpl in |- *. tauto. simpl in |- *. tauto.
Qed.

Lemma bpl_false_true :
 forall p q : positive,
 istrue (b_pos_less p q false) -> istrue (b_pos_less p q true).
Proof.
  simple induction p.
    simple induction q.
      intros. apply (H p1). apply H1.
      intros. apply H1.
      contradiction.
    simple induction q.
      intro. intro. simpl in |- *. trivial.
      intro. intro. simpl in |- *. apply (H p1).
      contradiction.
    intros. case q.
      simpl in |- *. trivial.
      simpl in |- *. trivial.
      simpl in |- *. trivial.
Qed.

Lemma bpl_true_false :
 forall p q : positive,
 istrue (b_pos_less p q true) -> istrue (b_pos_less p q false) \/ p = q.
Proof.
  double induction p q.
    intros. elim (H0 p0).
      intros. left. simpl in |- *. apply H2.
      intros. right. elim H2. reflexivity.
      simpl in H1. apply H1.
    intros. elim (H0 p0).
      intros. simpl in |- *. left. apply H2.
      intros. simpl in H1. left. simpl in |- *. apply H1.
      simpl in H1. apply bpl_false_true. apply H1.
    intros. simpl in H0. contradiction.
    intros. simpl in H1. left. simpl in |- *. apply H1.
    intros. elim (H0 p0).
      intros. simpl in |- *. left. apply H2.
      intros. right. elim H2. reflexivity.
      simpl in H1. apply H1.
    intros. simpl in H0. contradiction.
    intros. simpl in |- *. left. trivial.
    intros. simpl in |- *. left. trivial.
    intros. right. reflexivity.
Qed.

Lemma bpl_inductive1 :
 forall p0 p1 : positive,
 (Zpos p1 <= Zpos p0)%Z ->
 ((Zpos p1 < Zpos p0)%Z -> istrue (b_pos_less p1 p0 false)) ->
 (istrue (b_pos_less p1 p0 false) -> (Zpos p1 < Zpos p0)%Z) ->
 istrue (b_pos_less p1 p0 true).
Proof.
  double induction p0 p1.
    intros. simpl in |- *. apply H0.
      apply H1.
      apply H2.
      apply H3.
    intros. apply bpl_false_true. apply H2. elim (Zle_lt_or_eq (Zpos (xO p)) (Zpos (xI p2))).
      trivial.
      intros. discriminate H4.
      exact H1.
    intros. simpl in |- *. trivial.
    intros. simpl in |- *. apply H2. elim (Zle_lt_or_eq (Zpos (xI p)) (Zpos (xO p2))).
      trivial.
      intros. discriminate H4.
      exact H1.
    intros. simpl in |- *. apply H0.
      apply H1.
      apply H2.
      apply H3.
    intros. simpl in |- *. trivial.
    intro. case p.
      intros. change (4 * Zpos p2 + 3 <= 1)%Z in H0. absurd (4 * Zpos p2 + 3 <= 1)%Z.
        compute in |- *. auto.
        apply H0.
      intros. change (4 * Zpos p2 + 2 <= 1)%Z in H0. absurd (4 * Zpos p2 + 2 <= 1)%Z.
        compute in |- *. auto.
        apply H0.
      intros. absurd (3 <= 1)%Z.
        compute in |- *. auto.
        apply H0.
    intro. case p.
      intros. change (4 * Zpos p2 + 2 <= 1)%Z in H0. absurd (4 * Zpos p2 + 2 <= 1)%Z.
        compute in |- *. auto.
        apply H0.
      intros. change (4 * Zpos p2 <= 1)%Z in H0. simpl in |- *. simpl in H1. apply H1. change (4 * Zpos p2 < 1)%Z in |- *. omega.
      intros. absurd (2 <= 1)%Z.
        auto.
        apply H0.
    intros. simpl in |- *. trivial.
Qed.

Lemma bpl_inductive2 :
 forall p0 p1 : positive,
 istrue (b_pos_less p1 p0 true) ->
 ((Zpos p1 < Zpos p0)%Z -> istrue (b_pos_less p1 p0 false)) ->
 (istrue (b_pos_less p1 p0 false) -> (Zpos p1 < Zpos p0)%Z) ->
 (Zpos p1 <= Zpos p0)%Z.
Proof.
  double induction p0 p1.
    intros. change (Zpos p <= Zpos p2)%Z in |- *. apply H0. apply H1.
    intros. simpl in H2. apply H2. apply H4.
    intros. apply H3.  simpl in |- *. apply H4.
    intros. apply Zlt_le_weak. apply H3. simpl in |- *. simpl in H1. apply H1.
    intros. apply Zlt_le_weak. apply H2. simpl in |- *. trivial.
    intros. apply Zlt_le_weak. apply H3. simpl in |- *. simpl in H1. apply H1.
    intros. change (Zpos p <= Zpos p2)%Z in |- *. apply H0. apply H1. apply H2. apply H3.
    intros. apply Zlt_le_weak. apply H2. simpl in |- *. trivial.
    intros. simpl in H0. contradiction.
    intros. simpl in H0. contradiction.
    intros. omega.
Qed.

Lemma pos_lt :
 forall p q : positive, (Zpos p < Zpos q)%Z <-> istrue (b_pos_less p q false).
Proof.
  double induction p q.
    intros. split.
      intros. simpl in |- *. elim (H0 p0). intros. apply H2. apply H1.
      intros. change (Zpos p1 < Zpos p0)%Z in |- *. elim (H0 p0). intros. apply H3. apply H1.
    intros. split. 
      intros. simpl in |- *. elim (H0 p0). intros. apply H2. change (Zpos (xO p1) < Zpos (xO p0))%Z in |- *. apply Zlt_trans with (Zpos (xI p1)). 
        replace (Zpos (xI p1)) with (Zsucc (Zpos (xO p1))). 
          apply Zle_lt_succ. omega. 
          trivial.
          exact H1.
      intros. elim (H0 p0). intros. assert (Zpos p1 < Zpos p0)%Z. 
        apply H3. apply H1. 
        change (2 * Zpos p1 + 1 < 2 * Zpos p0)%Z in |- *. omega.
    intros. split.
      intros. compute in H0. discriminate H0.
      intros. simpl in H0. contradiction.
    intros. split.
      intro. assert (Zpos p1 <= Zpos p0)%Z.
        change (2 * Zpos p1 < 2 * Zpos p0 + 1)%Z in H1. omega.
          simpl in |- *. elim (H0 p0). intros. apply bpl_inductive1. apply H2. 
        apply H3. 
        apply H4. 
      intro. simpl in H1. elim (H0 p0). intros. assert (Zpos p1 <= Zpos p0)%Z. 
        apply bpl_inductive2. apply H1. apply H2. apply H3. change (2 * Zpos p1 < 2 * Zpos p0 + 1)%Z in |- *. omega. 
    intros. split.
      intros. simpl in |- *. elim (H0 p0). intros. apply H2. apply H1. 
      intros. elim (H0 p0). intros. apply H3. apply H1. 
    intros. split.
      intros. compute in H0. discriminate H0.
      intros. simpl in H0. contradiction.
    intros. split.
      intros. simpl in |- *. trivial.
      intros. compute in |- *. reflexivity.
    intros. split.
      intros. simpl in |- *. trivial.
      intros. compute in |- *. reflexivity.
    intros. split.
      intros. compute in H. discriminate H. 
      intros. simpl in H. contradiction.
Qed.

Lemma pos_eq : forall p q : positive, p = q <-> istrue (b_pos_eq p q).
Proof.
  double induction p q.
    intros. split.
      intros. elim H1. simpl in |- *. elim (H0 p1). intros. apply H2. reflexivity.
      intros. simpl in H1. elim (H0 p0). intros. assert (p1 = p0). 
        apply H3. apply H1.
        elim H4. reflexivity.
    intros. split.
      intros. discriminate H1.
      intros. simpl in H1. contradiction.
    intros. split.
      intros. discriminate H0.
      intros. simpl in H0. contradiction.
    intros. split.
      intros. discriminate H1.
      intros. simpl in H1. contradiction.
    intros. split.
      intros. elim H1. simpl in |- *. elim (H0 p1). intros. apply H2. reflexivity.
      intros. simpl in H1. elim (H0 p0). intros. assert (p1 = p0).
        apply H3. apply H1.
        elim H4. reflexivity.
    intros. split.
      intros. discriminate H0.
      intros. simpl in H0. contradiction.
    intros. split.
      intros. discriminate H0.
      intros. simpl in H0. contradiction.
    intros. split.
      intros. discriminate H0.
      intros. simpl in H0. contradiction.
    intros. split.
      intros. simpl in |- *. trivial.
      intros. reflexivity.
Qed.

Lemma b_zlt_le : forall s t : Z, istrue (b_zlt s t) -> istrue (b_zle s t).
Proof.
  double induction s t.
    intros. simpl in |- *. trivial.
    intros. simpl in |- *. trivial.
    intros. simpl in H. contradiction.
    intros. simpl in H. contradiction.
    intros. simpl in |- *. simpl in H. apply bpl_false_true. apply H. 
    intros. simpl in H. contradiction.
    intros. simpl in |- *. trivial.
    intros. simpl in |- *. trivial.
    intros. simpl in |- *. simpl in H. apply bpl_false_true. apply H.
Qed.

Lemma b_zle_lt_or_eq :
 forall s t : Z,
 istrue (b_zle s t) -> istrue (b_zlt s t) \/ istrue (b_zeq s t).
  double induction s t.
    intros. right. trivial.
    intros. left. trivial.
    intros. simpl in H. contradiction.
    intros. simpl in H. contradiction.
    intros. simpl in |- *. simpl in H. elim (bpl_true_false p0 p). intros.
      left. apply H0.
      intros. right. elim (pos_eq p0 p). intros. apply H1. apply H0.
      apply H.
    intros. simpl in H. contradiction.
    intros. simpl in |- *. left. trivial. 
    intros. simpl in |- *. left. trivial.
    intros. simpl in |- *. simpl in H. elim (bpl_true_false p p0). intros. 
      left. apply H0.
      intros. right. elim (pos_eq p0 p). intros. apply H1. elim H0. reflexivity.
      apply H.
Qed.

Lemma b_zlt_gt : forall s t : Z, istrue (b_zlt s t) <-> istrue (b_zgt t s).
Proof.
  double induction s t.
    intros. simpl in |- *. tauto.
    intros. simpl in |- *. tauto.
    intros. simpl in |- *. tauto. 
    intros. simpl in |- *. tauto. 
    intros. simpl in |- *. tauto.
    intros. simpl in |- *. tauto.
    intros. simpl in |- *. tauto.
    intros. simpl in |- *. tauto.
    intros. simpl in |- *. tauto.
Qed.

Lemma b_zle_ge : forall s t : Z, istrue (b_zle s t) <-> istrue (b_zge t s).
Proof.
  double induction s t.
    intros. simpl in |- *. tauto.
    intros. simpl in |- *. tauto.
    intros. simpl in |- *. tauto.
    intros. simpl in |- *. tauto.
    intros. simpl in |- *. tauto.
    intros. simpl in |- *. tauto.
    intros. simpl in |- *. tauto.
    intros. simpl in |- *. tauto.
    intros. simpl in |- *. tauto.
Qed.

(***  Correctness  ***)

Lemma leok : forall s t : nat, s <= t <-> istrue (b_le s t).
Proof.
   simple induction s.
      simple induction t.
         simpl in |- *. split.
            trivial.
            auto.
         intros t1 IHt1. simpl in |- *. split.
            auto.
            (* Auto.  Werkt hier niet meer in 6.2... *)
            intro. apply le_S. apply lt_n_Sm_le. apply lt_O_Sn.
      intros s1 IHs1. simple induction t.
         simpl in |- *. split.
            exact (le_Sn_O s1).
            tauto.
         intros t1 IHt1. simpl in |- *. case (IHs1 t1). split.
            intro. apply H. apply le_S_n. assumption.
            intro. apply le_n_S. apply H0. assumption.
Qed.

Lemma eqok : forall s t : nat, s = t <-> istrue (b_eq s t).
Proof.
   simple induction s.
      simple induction t.
         simpl in |- *. split.
            trivial.
            auto.
         intros t1 IHt1. simpl in |- *. split.
            intro H. discriminate H.
            tauto.
      intros s1 IHs1. simple induction t.
         simpl in |- *. split.
            intro H. discriminate H.
            tauto.
         intros t1 IHt1. simpl in |- *. case (IHs1 t1). split.
            intro. apply H. injection H1. tauto.
            intro. rewrite H0. reflexivity. assumption.
Qed.

Lemma ltok : forall s t : nat, s < t <-> istrue (b_lt s t).
Proof.
   intros s t. unfold lt, b_lt in |- *. exact (leok (S s) t).
Qed.

Lemma geok : forall s t : nat, s >= t <-> istrue (b_ge s t).
Proof.
   intros s t. unfold ge, b_ge in |- *. exact (leok t s).
Qed.

Lemma gtok : forall s t : nat, s > t <-> istrue (b_gt s t).
Proof.
   intros s t. unfold gt, b_gt in |- *. exact (ltok t s).
Qed.

Lemma notok :
 forall (p : Prop) (a : bool), (p <-> istrue a) -> (~ p <-> istrue (b_not a)).
Proof.
   intros p a. case a. simpl in |- *. split. case H. intros. apply H2. apply H1.
   tauto. tauto. simpl in |- *. split. tauto. case H. tauto.
Qed.

Lemma andok :
 forall (p q : Prop) (a b : bool),
 (p <-> istrue a) -> (q <-> istrue b) -> (p /\ q <-> istrue (b_and a b)).
Proof.
   intros p q a b. case a. case b. simpl in |- *. tauto. simpl in |- *. tauto.
   case b. simpl in |- *. tauto. simpl in |- *. tauto.
Qed.

Lemma orok :
 forall (p q : Prop) (a b : bool),
 (p <-> istrue a) -> (q <-> istrue b) -> (p \/ q <-> istrue (b_or a b)).
Proof.
   intros p q a b. case a. case b. simpl in |- *. tauto. simpl in |- *. tauto.
   case b. simpl in |- *. tauto. simpl in |- *. tauto.
Qed.

Lemma impok :
 forall (p q : Prop) (a b : bool),
 (p <-> istrue a) -> (q <-> istrue b) -> ((p -> q) <-> istrue (b_imp a b)).
Proof.
   intros p q a b. case a. case b. simpl in |- *. tauto.
   simpl in |- *. split. intros. case H0. intros. apply H2. apply H1. case H.
   intros. apply H5. trivial. intros. case H1.
   case b. simpl in |- *. tauto. simpl in |- *. tauto.
Qed.

Lemma peqok : forall s t : (nat * nat), s = t <-> istrue (b_p_eq s t).
Proof.
  simple induction s.
    simple induction t.
      split.
         intros. simpl. elim (andok (a = a0) (b = b0) (b_eq a a0) (b_eq b b0)). 
            intros. apply H0. inversion H. split.
              trivial.
              trivial.
            apply eqok. 
            apply eqok.
         intros. elim (andok (a = a0) (b = b0) (b_eq a a0) (b_eq b b0)).
            intros. elim H1. 
              intros. replace a0 with a. replace b0 with b. trivial.
              apply H.
           apply eqok. 
           apply eqok.
Qed.

Lemma allok :
 forall (n : nat) (p : nat -> Prop) (f : nat -> bool),
 (forall x : nat, p x <-> istrue (f x)) ->
 ((forall x : nat, x <= n -> p x) <-> istrue (b_all n f)).
Proof.
   simple induction n.
   simpl. intros. split.
      intros. elim (H 0). intros. apply H1. apply H0. trivial.
      intros. replace x with 0. 
         elim (H 0). intros. apply H3. apply H0.
         apply le_n_O_eq. apply H1.
  simpl. intros. split.
     case (H p f).
       assumption.
       intros. apply b_and_intro. 
          case (H0 (S n0)). intros. apply H4. apply H3. trivial.
          apply H1. intros. apply H3. apply le_S. assumption.
       intros. case (H0 x). intros. apply H4. case (le_lt_or_eq x (S n0)).
          assumption.
          intro. elim (H p f). 
             intros. apply H3. apply H7. apply (b_and_elim2 (f (S n0)) (b_all n0 f)). apply H1.
             apply lt_n_Sm_le. assumption.
             assumption. 
          intros. rewrite H5. apply (b_and_elim1 (f (S n0)) (b_all n0 f)). assumption.
Qed.

Lemma exok :
 forall (n : nat) (p : nat -> Prop) (f : nat -> bool),
 (forall x : nat, p x <-> istrue (f x)) ->
 ((exists x : nat, x <= n /\ p x) <-> istrue (b_ex n f)).
Proof.
   simple induction n.
   simpl. intros. split.
      intros. case H0. intros. case H1. intros. case (le_lt_or_eq x 0).
        assumption.
        intros. absurd (x < 0).
          apply (lt_n_O x).
          assumption.
        intros. replace x with 0 in H3. elim (H 0). intros. apply H5. assumption.
       intros. exists 0. split.
         trivial.
         elim (H 0). intros. apply H2. assumption.
  simpl. intros. split.
     intros.  elim H1. intros. elim H2. intros. elim (le_lt_or_eq x (S n0)). 
       intros. apply (b_or_intro2 (f (S n0)) (b_ex n0 f)). elim (H p f). 
          intros. apply H6. exists x. split.
             apply lt_n_Sm_le. assumption.       
             assumption.
          assumption.
       intros. apply (b_or_intro1 (f (S n0)) (b_ex n0 f)). replace (S n0) with x.  elim (H0 x). intros. apply H6. assumption.
       apply H3.
    intros. elim (b_or_elim (f (S n0)) (b_ex n0 f)). 
       intros. exists (S n0). split.
          trivial.
          elim (H0 (S n0)). intros. apply H4. assumption.
       intros. elim (H p f). 
         intros. elim H4. intros. exists x. elim H5. intros. split.
            apply le_S. assumption.
            assumption.
         assumption.
         assumption.
      assumption.
Qed.

Lemma allelok :
 forall (l : list nat) (p : nat -> Prop) (f : nat -> bool),
 (forall x : nat, p x <-> istrue (f x)) ->
 ((forall x : nat, In x l -> p x) <-> istrue (b_all_el l f)).
Proof.
  induction l.
    split. 
      simpl in |- *. trivial.
      simpl in |- *. contradiction.
    intros. elim (IHl p f). 
      split.
        simpl in |- *. intros. apply b_and_intro. 
          elim (H a). intros. apply H3. apply H2. left. trivial.
          intros. apply H0. intros. apply (H2 x). right. exact H3.
        intros. elim H3.
          intros. replace x with a. elim (H a). intros. apply H6. apply (b_and_elim1 (f a) (b_all_el l f)). apply H2.
          apply H1. apply (b_and_elim2 (f a)). apply H2.
      exact H. 
Qed.

Lemma exelok :
 forall (l : list nat) (p : nat -> Prop) (f : nat -> bool),
 (forall x : nat, p x <-> istrue (f x)) ->
 ((exists x : nat, In x l /\ p x) <-> istrue (b_ex_el l f)).
Proof.
  induction l.
    split.
      simpl in |- *. intros. elim H0. intros. elim H1. intros. exact H2.
      simpl in |- *. contradiction.
    intros. elim (IHl p f).
      split.
        intros. simpl in |- *. elim H2. intros. elim H3. intros. elim H4.
          intros. apply b_or_intro1. replace a with x. elim (H x). intros. apply H7. exact H5.
          intros. apply b_or_intro2. apply H0. exists x. split.
            exact H6.
            exact H5.
        simpl in |- *. intros. case (b_or_elim (f a) (b_ex_el l f)). 
          exact H2.
          intros. exists a. split.
            left. trivial.
            elim (H a). intros. apply H5. exact H3.
          intros. elim H1.
            intros. exists x. elim H4. intros. split.
              right. exact H5.
              exact H6.
            exact H3.
      exact H.
Qed.

Lemma inok : forall (n: nat) (l: list nat), (In n l) <-> istrue (b_in n l).
Proof.
  intros. split.
    intros. induction l.
      simpl. trivial.
      simpl. elim H.
        intros. apply b_or_intro1. elim (eqok a n). intros. apply H1. apply H0.
        intros. apply b_or_intro2. apply IHl. apply H0.
    intros. induction l.
      trivial.
      simpl in H. elim (b_or_elim (b_eq a n) (b_in n l)).
        intros. simpl. left. elim (eqok a n). intros. apply H2. apply H0.
        intros. simpl. right. apply IHl. apply H0.
        apply H.
Qed.
 
Lemma pinok : forall (p: nat * nat) (l: list (nat * nat)), (In p l) <-> istrue (b_p_in p l).
Proof.
  intros. split.
     intros. induction l.
        simpl. trivial.
        simpl. elim H. 
          intros. apply b_or_intro1. elim (peqok a p). intros. apply H1. apply H0.
          intros. apply b_or_intro2. apply IHl. apply H0. 
     intros. induction l. 
       trivial. 
       simpl in H. elim (b_or_elim (b_p_eq a p) (b_p_in p l)). 
          intros. simpl. left. elim (peqok a p). intros. apply H2. apply H0. 
          intros. simpl. right. apply IHl. apply H0.
          apply H.
Qed.

Lemma succok : forall (x y: nat) (l: list nat), 
  (Succ nat x y l) <-> (istrue (b_succ x y l)).
Proof.
  intros. split.
     intros. induction l.                 
        simpl in H. contradiction.
        induction l. 
           simpl in H. contradiction.
           elim H. 
              intros. simpl. apply b_or_intro1. elim H0. intros. apply b_and_intro. 
                elim (eqok a x). intros. apply H3. replace x with a. trivial.
                elim (eqok a0 y). intros. apply H3. replace y with a0. trivial.
              intros. simpl. apply b_or_intro2. change (istrue (b_succ x y (a0::l))).  apply IHl. apply H0.
     intros. induction l.
        simpl in H. contradiction.
        induction l.
           simpl in H. contradiction.
           elim (b_or_elim (b_and (b_eq a x) (b_eq a0 y)) (b_succ x y (a0::l))). 
              intros. simpl. left. split.
                 symmetry. elim (eqok a x). intros. apply H2. apply (b_and_elim1 (b_eq a x) (b_eq a0 y)). apply H0.
                 symmetry. elim (eqok a0 y). intros. apply H2. apply (b_and_elim2 (b_eq a x) (b_eq a0 y)). apply H0.
              intros. simpl. right. change (Succ nat x y (a0::l)). apply IHl. apply H0.
           apply H. 
Qed.

Lemma zltok : forall s t : Z, (s < t)%Z <-> istrue (b_zlt s t).
Proof.
  simple induction s.
    simple induction t. 
      (* ZERO < ZERO *)
      simpl in |- *. split.
        apply Zlt_irrefl.
        contradiction. 
      (* ZERO < POS *)
      simpl in |- *. split.
        trivial.
        intros. apply Zgt_lt. apply Zorder.Zgt_pos_0. 
      (* ZERO < NEG *)
      simpl in |- *. split.
        apply Zle_not_lt. apply Zlt_le_weak. apply Zorder.Zlt_neg_0.
        contradiction.
    simple induction t.
      (* POS < ZERO *)
      simpl in |- *. split.
        apply Zle_not_lt. apply Zlt_le_weak. apply Zgt_lt. apply Zorder.Zgt_pos_0.
        contradiction.
      (* POS < POS *)
      simpl in |- *. intro. apply pos_lt. 
      (* POS < NEG *)
      intros. split.
        intros. compute in H. discriminate H. 
        intros. simpl in H. contradiction.
    simple induction t.
      (* NEG < ZERO *)
      simpl in |- *. split.
        trivial.
        intros. compute in |- *. reflexivity.
      (* NEG < POS *)
      simpl in |- *. split.
        trivial.
        intros. compute in |- *. reflexivity.
      (* NEG < NEG *)
      intros. simpl in |- *. replace (Zneg p) with (- Zpos p)%Z. 
        replace (Zneg p0) with (- Zpos p0)%Z. 
          elim (pos_lt p0 p). intros. split.
            intros. apply H. change ((Zpos p0 ?= Zpos p)%Z = Datatypes.Lt) in |- *. rewrite Zcompare_opp. exact H1.
            intros. change ((- Zpos p ?= - Zpos p0)%Z = Datatypes.Lt) in |- *. rewrite <- Zcompare_opp. apply H0. exact H1.
	    rewrite <- Zopp_neg. apply Zopp_involutive. 
            rewrite <- Zopp_neg. apply Zopp_involutive. 
Qed.

Lemma zeqok : forall s t : Z, s = t <-> istrue (b_zeq s t).
Proof.
  double induction s t.
    split.
      intros. simpl in |- *. trivial.
      intros. reflexivity.
    intros. split.
      intros. discriminate H.
      intros. simpl in H. contradiction.
    intros. split. 
      intros. discriminate H. 
      intros. simpl in H. contradiction.
    intros. split.
      intros. discriminate H.
      intros. simpl in H. contradiction.
    intros. split.
      intros. simpl in |- *. elim (pos_eq p0 p). intros. apply H0. injection H. trivial.
      intros. elim (pos_eq p0 p). intros. assert (p0 = p).
        apply H1. apply H.
        elim H2. reflexivity.
    intros. split.
      intros. discriminate H.
      intros. simpl in H. contradiction.
    intros. split.
      intros. discriminate H.
      intros. simpl in H. contradiction.
    intros. split.
      intros. discriminate H.
      intros. simpl in H. contradiction.
    intros. split.
      intros. simpl in |- *. elim (pos_eq p0 p). intros. apply H0. injection H. trivial.
      intros. elim (pos_eq p0 p). intros. assert (p0 = p).
        apply H1. apply H.
        elim H2. reflexivity.
Qed.

Lemma pzeqok : forall s t : (Z * Z), s = t <-> istrue (b_p_zeq s t).
Proof.
  intros. split.
     elim s. elim t. intros. elim H. 
        simpl. apply b_and_intro. 
           elim (zeqok a0 a0). intros. apply H0. trivial.
           elim (zeqok b0 b0). intros. apply H0. trivial. 
    elim s. elim t. intros. simpl in H. replace a with a0. replace b with b0. trivial.
       elim (zeqok b0 b). intros. apply H1. apply (b_and_elim2 (b_zeq a0 a) (b_zeq b0 b)). apply H.
       elim (zeqok a0 a). intros. apply H1. apply (b_and_elim1 (b_zeq a0 a) (b_zeq b0 b)). apply H.
Qed.

Lemma zleok : forall s t : Z, (s <= t)%Z <-> istrue (b_zle s t).
Proof.
  intros. split.
    intros. elim (Zle_lt_or_eq s t). 
      intros. elim (zltok s t). intros. apply b_zlt_le. apply H1. apply H0.
      intros. elim H0. case s.
        simpl in |- *. trivial.
        simpl in |- *. intros. induction p.
          simpl in |- *. apply IHp.
          simpl in |- *. apply IHp. 
          simpl in |- *. trivial.
      intros. simpl in |- *. induction p.
        simpl in |- *. apply IHp.
        simpl in |- *. apply IHp.
        simpl in |- *. trivial.
      apply H.
    intros. elim (b_zle_lt_or_eq s t). 
      intros. apply Zlt_le_weak. elim (zltok s t). intros. apply H2.  apply H0.
      intros. elim (zeqok s t). intros. replace t with s.
        apply Zeq_le. reflexivity.
        apply H2. apply H0.
      apply H.
Qed.

Lemma zgtok : forall s t : Z, (s > t)%Z <-> istrue (b_zgt s t).
Proof.
  intros. elim (b_zlt_gt t s). intros. split.
    intros. apply H. assert (t < s)%Z. 
      apply Zgt_lt. apply H1.
      elim (zltok t s). intros. apply H3. apply H2.
    intros. apply Zlt_gt. elim (zltok t s). intros. apply H3. apply H0. apply H1.
Qed.

Lemma zgeok : forall s t : Z, (s >= t)%Z <-> istrue (b_zge s t).
Proof.
  intros. elim (b_zle_ge t s). intros. split.
    intros. apply H. assert (t <= s)%Z.
      apply Zge_le. apply H1.
      elim (zleok t s). intros. apply H3. apply H2.
    intros. apply Zle_ge. elim (zleok t s). intros. apply H3. apply H0. apply H1.
Qed.

Theorem allnatok :
 forall (n : nat) (p : Z -> Prop) (f : Z -> bool),
 (forall x : positive, p (Zpos x) <-> istrue (f (Zpos x))) ->
 ((forall x : positive, (Zpos x < Zpos (P_of_succ_nat n))%Z -> p (Zpos x)) <->
  istrue (b_all_nat n f)).
Proof.
  intros. split.
    intros. induction n as [| n Hrecn].
      intros. simpl in |- *. trivial.
      intros. simpl in |- *. apply b_and_intro. 
        elim (H (P_of_succ_nat n)). intros. apply H1. apply H0. simpl in |- *. rewrite Zpos_succ_morphism. apply Zlt_succ. 
        apply Hrecn. intros. apply H0. simpl in |- *. rewrite Zpos_succ_morphism. apply Zlt_lt_succ. assumption.
      intros. elim (H x). intros. apply H3. induction n as [| n Hrecn].
        absurd (Zpos x < Zsucc 0)%Z. 
          apply Zle_not_lt. apply Zgt_le_succ. apply Zorder.Zgt_pos_0. 
          apply H1.
      elim
       (andok (istrue (f (Zpos (P_of_succ_nat n)))) 
          (istrue (b_all_nat n f)) (f (Zpos (P_of_succ_nat n)))
          (b_all_nat n f)).
        intros. elim H5.
          intros. elim (Zle_lt_or_eq (Zpos x) (Zpos (P_of_succ_nat n))).
            intros. apply Hrecn.
              apply H7.
              apply H8.
            intros. rewrite H8. apply H6.
            simpl in H1. rewrite Zpos_succ_morphism in H1. apply Zlt_succ_le. apply H1.
          apply H0.
        tauto.
        tauto.
Qed.

Theorem zallok :
 forall (z : Z) (p : Z -> Prop) (f : Z -> bool),
 (forall x : Z, p x <-> istrue (f x)) ->
 ((forall x : Z, (x > 0)%Z /\ (x <= z)%Z -> p x) <-> istrue (b_zall z f)).
Proof.
  intros. split.
    intros. induction z as [| p0| p0].
      simpl in |- *. trivial.
      simpl in |- *. elim (allnatok (nat_of_P p0) p f). 
        intros. apply H1. intros. apply H0. split.
          apply Zorder.Zgt_pos_0.
          rewrite P_of_succ_nat_o_nat_of_P_eq_succ in H3. rewrite Zpos_succ_morphism in H3. apply Zlt_succ_le. apply H3.
        intros. apply H.
      simpl in |- *. trivial.
    intros. induction z as [| p0| p0].
      elim H1. intros. absurd (x <= 0)%Z.
        apply Zlt_not_le. apply Zgt_lt. apply H2.
        apply H3.
      induction x as [| p1| p1].
        elim H1. intros. absurd (0 > 0)%Z.
          apply Zgt_irrefl. 
          apply H2.
        simpl in H0. elim (allnatok (nat_of_P p0) p f).
          intros. apply H3.
            apply H0.
            rewrite P_of_succ_nat_o_nat_of_P_eq_succ. rewrite Zpos_succ_morphism. apply Zle_lt_succ. elim H1. intros. apply H5.
          intros. apply H.
        elim H1. intros. absurd (Zneg p1 > 0)%Z.
          apply Zle_not_gt. apply Zlt_le_weak. apply Zorder.Zlt_neg_0.
          apply H2.
      elim H1. intros. absurd (x <= Zneg p0)%Z.
        apply Zlt_not_le. apply Zgt_lt. apply Zgt_trans with 0%Z.
          apply H2.
          apply Zlt_gt. apply Zorder.Zlt_neg_0.
        apply H3. 
Qed.

Theorem exnatok :
 forall (n : nat) (p : Z -> Prop) (f : Z -> bool),
 (forall x : positive, p (Zpos x) <-> istrue (f (Zpos x))) ->
 ((exists x : positive, (Zpos x < Zpos (P_of_succ_nat n))%Z /\ p (Zpos x)) <->
  istrue (b_ex_nat n f)).
Proof.
  simple induction n.
  simpl in |- *. split.
    intros. elim H0. intros. elim H1. intros. absurd (Zpos x < Zsucc 0)%Z.
      apply Zle_not_lt. apply Zgt_le_succ. apply Zorder.Zgt_pos_0.
      apply H2.
    tauto.
  simpl in |- *. intros. case (H p f). assumption. split.
    intros. case H3. intros. case H4. intros. case (Zle_lt_or_eq (Zpos x) (Zpos (P_of_succ_nat n0))).
      apply Zlt_succ_le. rewrite Zpos_succ_morphism in H5. apply H5.
      intros. apply b_or_intro2. apply H1. exists x. split.
        apply H7.
        apply H6.
      intros. apply b_or_intro1. rewrite <- H7. case (H0 x). intros. apply H8. assumption.
    intros. case (b_or_elim (f (Zpos (P_of_succ_nat n0))) (b_ex_nat n0 f)).
      apply H3.
      intros. exists (P_of_succ_nat n0). split.
        rewrite Zpos_succ_morphism. apply Zlt_succ.
        case (H0 (P_of_succ_nat n0)). tauto.
      intros. case (H2 H4). intros. case H5. intros. exists x. split.
      rewrite Zpos_succ_morphism. apply Zlt_lt_succ. apply H6. apply H7.
Qed.

Theorem zexok :
 forall (z : Z) (p : Z -> Prop) (f : Z -> bool),
 (forall x : Z, p x <-> istrue (f x)) ->
 ((exists x : Z, ((x > 0)%Z /\ (x <= z)%Z) /\ p x) <-> istrue (b_zex z f)).
Proof.
  intros. split.
    intros. induction z as [| p0| p0].
      case H0. intros. case H1. intros. case H2. intros. absurd (x <= 0)%Z.
        apply Zlt_not_le. apply Zgt_lt. apply H4.
        apply H5.
      simpl in |- *. elim (exnatok (nat_of_P p0) p f).
        intros. apply H1. case H0. intros. case H3. intros. case H4. intros. induction x as [| p1| p1].
          absurd (0 > 0)%Z.
            apply Zgt_irrefl.
            apply H6.
          exists p1. split.
            rewrite P_of_succ_nat_o_nat_of_P_eq_succ. rewrite Zpos_succ_morphism. apply Zle_lt_succ. assumption.
            apply H5.
          absurd (Zneg p1 > 0)%Z.
            apply Zle_not_gt. apply Zlt_le_weak. apply Zorder.Zlt_neg_0.
            apply H6.
        intros.
      apply H. 
    case H0. intros. case H1. intros. case H2. intros. absurd (x <= Zneg p0)%Z.
      apply Zlt_not_le. apply Zgt_lt. apply Zgt_trans with 0%Z.
        apply H4.
        apply Zlt_gt. apply Zorder.Zlt_neg_0.
      apply H5.
  intros. induction z as [| p0| p0].
    simpl in H0. contradiction.
    simpl in H0. elim (exnatok (nat_of_P p0) p f).
      intros. case H2.
        apply H0.
        intros. exists (Zpos x). case H3. intros. split.
          split.
            apply Zorder.Zgt_pos_0.
            rewrite P_of_succ_nat_o_nat_of_P_eq_succ in H4. rewrite Zpos_succ_morphism in H4. apply Zlt_succ_le. apply H4.
          apply H5.
      intros. apply H.
    simpl in H0. contradiction.
Qed.

Lemma zallelok :
 forall (l : list Z) (p : Z -> Prop) (f : Z -> bool),
 (forall x : Z, p x <-> istrue (f x)) ->
 ((forall x : Z, In x l -> p x) <-> istrue (b_zall_el l f)).
Proof.
  intros. induction l as [| a l Hrecl].
    split. intros.
      simpl in |- *. trivial.
      simpl in |- *. contradiction.
    intros. elim Hrecl. intros.
      split.
        simpl in |- *. intros. apply b_and_intro.
          elim (H a). intros. apply H3. apply H2. left. reflexivity.
          apply H0. intros. apply H2. right. exact H3.
        simpl in |- *. intros. elim H3. 
          intros. elim H4. elim (H a). intros. apply H6. apply (b_and_elim1 (f a) (b_zall_el l f)). apply H2.
          apply H1. apply (b_and_elim2 (f a)). apply H2.
Qed.

Lemma zexelok :
 forall (l : list Z) (p : Z -> Prop) (f : Z -> bool),
 (forall x : Z, p x <-> istrue (f x)) ->
 ((exists x : Z, In x l /\ p x) <-> istrue (b_zex_el l f)).
Proof.
  intros. induction l as [| a l Hrecl].
    split.
      intros. simpl in |- *. elim H0. intros. elim H1. intros. simpl in H2. assumption.
      simpl in |- *. contradiction.
    split.
      intros. simpl in |- *. elim H0. intros. elim H1. intros. elim H2.
        intros. apply b_or_intro1. replace a with x. elim (H x). intros. apply H5. assumption.
        intros. apply b_or_intro2. elim Hrecl. intros. apply H5. exists x. split.
          assumption.
          assumption.
      intros. simpl in H0. elim (b_or_elim (f a) (b_zex_el l f)). 
        intros. exists a. split.
          simpl in |- *. left. reflexivity.
          elim (H a). intros. apply H3. assumption.
        intros. elim Hrecl. intros. elim H3.
          intros. exists x. elim H4. intros. split.
            simpl in |- *. right. assumption.
            assumption.
          assumption.
      assumption.
Qed.

Lemma zinok: forall (z: Z) (l: list Z), (In z l) <-> istrue (b_zin z l).
Proof.
  intros. split.
    intros. induction l.
      simpl. trivial.
      simpl. elim H.
        intros. apply b_or_intro1. elim (zeqok z a). intros. apply H1. symmetry. apply H0.
        intros. apply b_or_intro2. apply IHl. apply H0.
    intros. induction l.
      simpl. trivial.
      simpl. simpl in H. elim (b_or_elim (b_zeq z a) (b_zin z l)).
        intros. left. elim (zeqok z a). intros. symmetry. apply H2. apply H0.
        intros. right. apply IHl. apply H0.
        apply H.
Qed.

Lemma pzinok: forall (p: Z * Z) (l: list (Z * Z)), (In p l) <-> istrue (b_p_zin p l).
Proof.
  intros. split.
     intros. induction l.      
        simpl in H. contradiction.
        simpl. elim H. 
           intros. apply b_or_intro1. elim (pzeqok p a). intros. apply H1. symmetry. apply H0.
           intros. apply b_or_intro2. apply IHl. apply H0.
     intros. induction l.  
        simpl in H. contradiction.
        simpl. simpl in H. elim (b_or_elim (b_p_zeq p a) (b_p_zin p l)).
           intros. left. elim (pzeqok p a). intros. symmetry. apply H2. apply H0.
           intros. right. apply IHl. apply H0.
          apply H.
Qed.

Lemma zsuccok : forall (x y: Z) (l: list Z), 
  (Succ Z x y l) <-> (istrue (b_zsucc x y l)).
Proof.
  intros. split.
     intros. induction l.
        simpl in H. contradiction.
        induction l.
           simpl in H. contradiction.
           elim H.
              intros. simpl. apply b_or_intro1. elim H0. intros. apply b_and_intro.
                 elim (zeqok a x). intros. apply H3. replace x with a. trivial.
                 elim (zeqok a0 y). intros. apply H3. replace y with a0. trivial.
              intros. simpl. apply b_or_intro2. change (istrue (b_zsucc x y (a0::l))). apply IHl. apply H0.
    intros. induction l.
       simpl in H. contradiction.
        induction l.
           simpl in H. contradiction.
           elim (b_or_elim (b_and (b_zeq a x) (b_zeq a0 y)) (b_zsucc x y (a0::l))).
              intros. simpl. left. split.
                 symmetry. elim (zeqok a x). intros. apply H2. apply (b_and_elim1 (b_zeq a x) (b_zeq a0 y)). apply H0.
                 symmetry. elim (zeqok a0 y). intros. apply H2. apply (b_and_elim2 (b_zeq a x) (b_zeq a0 y)). apply H0.
             intros. simpl. right. change (Succ Z x y (a0::l)). apply IHl. apply H0.
           apply H.
Qed.

Theorem ok : forall p : form, isValid p <-> istrue (checkValid p).
Proof.
  simple induction p.
    intros. exact (ltok n n0).
    intros. exact (leok n n0).
    intros. exact (eqok n n0).
    intros. exact (peqok p0 p1).    
    intros. exact (geok n n0).
    intros. exact (gtok n n0).
    intros. exact (zltok z z0). 
    intros. exact (zleok z z0).
    intros. exact (zeqok z z0).
    intros. exact (pzeqok p0 p1).
    intros. exact (zgeok z z0).  
    intros. exact (zgtok z z0). 
    intros. exact (notok (isValid f) (checkValid f) H).
    intros. exact (andok (isValid f) (isValid f0) (checkValid f) (checkValid f0) H H0). 
    intros. exact (orok (isValid f) (isValid f0) (checkValid f) (checkValid f0) H H0).
    intros. exact (impok (isValid f) (isValid f0) (checkValid f) (checkValid f0) H H0).
    intros. exact
  (allok n (fun y : nat => isValid (f y)) (fun y : nat => checkValid (f y))
     (fun x : nat => H x)).  
    intros. exact
  (exok n (fun y : nat => isValid (f y)) (fun y : nat => checkValid (f y))
     (fun x : nat => H x)).
    intros. exact
  (allelok l (fun y : nat => isValid (f y)) (fun y : nat => checkValid (f y))
     (fun x : nat => H x)).
    intros. exact
  (exelok l (fun y : nat => isValid (f y)) (fun y : nat => checkValid (f y))
     (fun x : nat => H x)).
    intros. exact (inok n l).
    intros. exact (pinok p0 l).
    intros. exact (succok n n0 l). 
    intros. exact (zsuccok z z0 l).
    intros. exact
  (zallok z (fun y : Z => isValid (f y)) (fun y : Z => checkValid (f y))
     (fun x : Z => H x)).  
    intros. exact
  (zexok z (fun y : Z => isValid (f y)) (fun y : Z => checkValid (f y))
     (fun x : Z => H x)).
    intros. exact
  (zallelok l (fun y : Z => isValid (f y)) (fun y : Z => checkValid (f y))
     (fun x : Z => H x)).
    intros. exact
  (zexelok l (fun y : Z => isValid (f y)) (fun y : Z => checkValid (f y))
     (fun x : Z => H x)).
    intros. exact (zinok z l).
    intros. exact (pzinok p0 l).
Qed.

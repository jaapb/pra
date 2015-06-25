Require Import QuoteTerm.

Definition is_path (p: list Z) (n: Z) (e: list (Z * Z)): Prop :=
  (forall x: Z, (In x p) -> (x > 0)%Z /\ (x <= n)%Z) /\
  (forall x: Z, (In x p) -> (forall y: Z, (In y p) -> Succ Z x y p -> (In (x, y) e))).

Definition is_hamilton_path (p: list Z) (n: Z) (e: list (Z * Z)): Prop :=
  is_path p n e /\ forall x: Z, (x > 0)%Z /\ (x <= n)%Z -> (In x p) /\ (Z_of_nat (length p)) = n.

Definition is_euler_path (p: list Z) (n: Z) (e: list (Z * Z)): Prop :=
  is_path p n e /\ forall x: Z, (x > 0)%Z /\ (x <= n)%Z ->
    forall y: Z, (y > 0)%Z /\ (y <= n)%Z -> (In (x, y) e) -> Succ Z x y p.

Definition is_connected (n: Z) (e: list (Z * Z)): Prop :=
  forall x: Z, (x > 0)%Z /\ (x <= n)%Z -> forall y: Z, (y > 0)%Z /\ (y <= n)%Z -> x <> y -> (In (x, y) e).

Definition tri: list (Z * Z) := ((1,2)::(2,3)::(3,1)::nil)%Z.
Definition tri2: list (Z * Z) := ((1,2)::(2,1)::(1,3)::(3,1)::(2,3)::(3,2)::nil)%Z.
Definition tri_path := (1::2::3::nil)%Z.
Definition tri_path2 := (1::2::3::1::nil)%Z.

Theorem bla: is_path tri_path 3 tri.
 unfold is_path. unfold tri_path. PRA.
Qed.

Theorem bla1: is_hamilton_path tri_path 3 tri.
  unfold is_hamilton_path. unfold is_path. unfold tri_path. PRA.
Qed.

Theorem bla1a: is_euler_path tri_path2 3 tri.
  unfold is_euler_path. unfold is_path. PRA.
Qed.

Theorem bla2: ~ is_connected 3 tri.
  unfold is_connected. PRA.
Qed.

Theorem bla2a: is_connected 3 tri2.
  unfold is_connected. PRA.
Qed.


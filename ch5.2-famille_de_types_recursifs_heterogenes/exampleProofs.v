Require Import Arith Omega.

Inductive even : nat -> Prop :=
  ev0 : even 0
| ev2 : forall n, even n -> even (S (S n)).

Check ev0.

Check ev2 0 ev0.

Check ev2 2 (ev2 0 ev0).

Check ev2 4 (ev2 2 (ev2 0 ev0)).

Lemma mult2_even : forall n, even (2 * n).
induction n as [ | n IHm].
  exact ev0.
replace(2 * S n) with (S (S (2 * n))) by ring.
apply ev2.
assumption.
Qed.







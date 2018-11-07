Require Import Arith Omega.

Inductive even : nat -> Prop :=
  ev0 : even 0
| ev2 : forall n, even n -> even (S (S n)).

Lemma even_mult2 : forall n, even n -> exists k, n = 2 * k.
Proof.
induction 1.
  exists 0; reflexivity.
destruct IHeven as [k pk].
exists (S k).
rewrite pk.
ring.
Qed.






Require Import FunInd List ZArith Arith.

Fixpoint mod3 n :=
  match n with S (S (S p )) => mod3 p | x => x end.

Functional Scheme mod3_ind := Induction for mod3 Sort Prop.
Functional Scheme mod3_rec := Induction for mod3 Sort Set.

Lemma mod3_bound : forall n, mod3 n <=2.
Proof. intros n; functional induction mod3 n; omega. Qed.

Definition div3' (n : nat) : {p | 3 * p + mod3 n = n}.
functional induction mod3 n; try (exists 0; reflexivity).
destruct IHn0 as [v qv].
exists (S v).
pattern p at 2; rewrite <- qv.
ring.
Defined.

Compute let (v, _) := div3' 100 in v.











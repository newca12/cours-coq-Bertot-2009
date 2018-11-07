Require Import List ZArith Arith.

Fixpoint mod2 (n : nat) :=
  match n with S (S p) => mod2 p | x => x end.

Lemma div2_step : forall n d, 2 * d + mod2 n = n ->
         2 * (S d) + mod2 (S (S n)) = S (S n).
Proof. intros n d H; simpl; rewrite <- H at 2; ring. Qed.

Fixpoint div2' (n : nat) : {p | 2 * p + mod2 n = n} :=
  match n return {p | 2 * p + mod2 n = n} with
    0 => exist _ 0 (refl_equal 0)
  | 1 => exist (fun v => 2 * v + mod2 1 = 1) 0 (refl_equal 1)
  | S (S p) => match div2' p with
                 exist _ d h => exist _ (S d) (div2_step p d h)
               end
  end.

Definition div2 n := match div2' n with exist _ v _ => v end.

Compute div2 101.

Lemma div2P : forall n, 2 * div2 n + mod2 n =n.
Proof.
intros n.
unfold div2.
case (div2' n).
intros x h; exact h.
Qed.

Compute div2' 5.






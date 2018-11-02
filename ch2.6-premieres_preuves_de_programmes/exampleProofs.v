Require Import List.

Inductive sorted : list nat -> Prop :=
 snil : sorted nil
| ssingle : forall x, sorted (x::nil)
| scons : forall x y l, x <= y -> sorted (y::l) -> sorted (x::y::l).

Lemma sorted_app : forall l, sorted l -> forall l1 l2 a b, l = l1++a::b::l2 -> a <= b.
Proof.
intros l H; induction H.
intros [ | c l'] l2 a b H'.
 discriminate.
discriminate.
intros [ | c [ | d l']]; discriminate.
intros [ | c l'] l2 a b H'.
injection H'.
intros; subst. auto.
assert (H'' : y :: l = l'++a::b::l2).
injection H'; intros; subst.
assumption.
apply IHsorted in H''.
assumption.
Qed.







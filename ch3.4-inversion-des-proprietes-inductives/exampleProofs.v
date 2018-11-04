(*
Require Import List Arith.

Inductive sorted : list nat -> Prop :=
 snil : sorted nil
| ssingle : forall x, sorted (x::nil)
| scons : forall x y l, x <= y -> sorted (y::l) -> sorted (x::y::l).

Lemma first_two_elements : forall a b l', sorted (a :: b :: l') -> a <= b.
Proof.
intros a b l' H.
inversion H.
*)
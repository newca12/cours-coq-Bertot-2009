Require Import List Arith Omega.

Inductive nbt : Type :=
  L | N (x : nat) (t1 t2 : nbt).

Check L.

Check N.

Check N 2 L (N 3 L L).

Compute match N 2 L (N 3 L L) with L => true | N y t t' => false end.

Compute match N 2 L (N 3 L L) with L => 0 | N y t t' => y end.

Compute match N 2 L (N 3 L L) with L => L | N y t t' => t' end.

Inductive bt (A : Type) :=
  L' | N' (x:A)(t1 t2:bt A).

Check L'.

Check N' nat 2 (L' nat) (N' nat 3 (L' nat) (L' nat)).

(**
asymmetric patterns disabled
https://coq.inria.fr/refman/addendum/extended-pattern-matching.html
*)

Compute match N' nat 2 (L' nat) (N' nat 3 (L' nat) (L' nat)) with
          L' _ => L' nat
        | N' _ x t t' => t'
        end.
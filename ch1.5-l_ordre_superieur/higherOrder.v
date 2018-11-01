Require Import Arith List.

Fixpoint insert (cmp: nat -> nat -> bool)(x : nat)(l : list nat) :=
  match l with
    nil => x::nil
	| a::l' => if cmp x a then x::a::l' else a::insert cmp x l'
  end.

Fixpoint sort (cmp : nat -> nat -> bool) (l : list nat) :=
  match l with nil => nil | x :: l' => insert cmp x (sort cmp l') end.

Check sort.

Check sort leb.

Definition sort_increasing := sort leb.

Compute sort_increasing (3::4::2::1::11::nil).

Definition sort_decreasing := sort (fun x y => leb y x).

Compute sort_decreasing (3::4::2::1::11::nil).

Check leb.

Check leb 3.

Compute leb 3 4.

Compute (leb 3) 4.


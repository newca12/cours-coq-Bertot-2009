Require Import List.

Fixpoint every_other_even A (l : list A) :=
  match l with nil => nil | _::nil => nil | a::b::l' => b::every_other_even A l' end.

Compute every_other_even nat (3::2::1::4::6::8::nil).

(**
Syntax changed
Implicit keyword removed
*)

Arguments every_other_even [A].

Compute every_other_even (3::2::1::4::6::8::nil).

Definition every_other_odd A (l : list A) :=
  match l with nil => nil | a::l' => a::every_other_even l' end.


Fixpoint merge A (odds evens : list A) :=
  match odds, evens with
    a::l,b::l' => a::b::merge A l l'
  | nil, l => l
  | l, nil => l
  end.

Arguments every_other_odd [A].

Arguments merge [A].

Compute let l :=  (3::2::1::4::6::8::nil) in
  merge (every_other_odd l) (every_other_even l).
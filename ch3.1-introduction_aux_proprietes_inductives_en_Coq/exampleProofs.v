Require Import List Arith.

Inductive sorted : list nat -> Prop :=
 snil : sorted nil
| ssingle : forall x, sorted (x::nil)
| scons : forall x y l, x <= y -> sorted (y::l) -> sorted (x::y::l).

Fixpoint insert x l :=
  match l with nil => x::nil | y::l' => if leb x y then x::l else y::insert x l' end.

Lemma insert_sorted : forall x l, sorted l -> sorted (insert x l).
Proof.
intros x l H; induction H.
  simpl.
  apply ssingle.
 simpl.
 case_eq (leb x x0).
  intros xlx0.
  apply scons.
SearchAbout leb.
   apply leb_complete. assumption.
  apply ssingle.
 intros x0lx.
 apply leb_complete_conv in x0lx.
 apply scons. apply lt_le_weak. assumption.
 apply ssingle.
simpl in IHsorted |- *.
case_eq (leb x x0).
 intros xlx0.
 apply scons.
  apply leb_complete. assumption.
 apply scons.
  assumption.
 assumption.
intros x0lx.
destruct (leb x y).
 apply scons.
  apply leb_complete_conv in x0lx. apply lt_le_weak. assumption.
 assumption.
apply scons. assumption. assumption.
Qed.

Fixpoint sort l := match l with nil => nil | a::l' => insert a (sort l') end.

Lemma sort_sorted : forall l, sorted (sort l).
Proof.
induction l.
  simpl. apply snil.
simpl. apply insert_sorted. assumption.
Qed.

Eval compute in sort (1::4::3::2::nil).






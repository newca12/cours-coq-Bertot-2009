Require Import Bool List ZArith String Ascii.

Fixpoint insert (A : Type) (cmp: A -> A -> bool)(x : A)(l : list A) :=
  match l with
    nil => x::nil
	| a ::l' => if cmp x a then x::a::l' else a::insert A cmp x l'
  end.

Fixpoint sort (A : Type) (cmp : A -> A -> bool) (l : list A) :=
  match l with nil => nil | x :: l' => insert A cmp x (sort A cmp l') end.

Check insert.

Check sort nat leb.

Definition sort_nat_incr := sort nat leb.

Compute sort_nat_incr (3::4::2::1::11::nil).

Coercion N_of_ascii : ascii >-> N.
Definition ascii_leb (a b : ascii) :=
  match Ncompare a b with Gt => false | _ => true end.

Fixpoint string_lex (s t : string) : bool :=
  match s, t with
    String a s', String b t' =>
      (ascii_leb a b && (negb (ascii_leb b a))) ||
      (ascii_leb a b && ascii_leb b a && string_lex s' t')
  | EmptyString, _ => true
  | _, EmptyString => false
  end.

Definition sort_lex := sort string string_lex.

Open Scope string_scope.

Compute sort string string_lex ("The"::"quick"::"red"::"fox"::"jumps"::"over"::"the"::"lazy"::"brown"::"dog"::nil).




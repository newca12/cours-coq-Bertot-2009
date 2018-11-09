Require Import ZArith Zwf Wellfounded.
Open Scope Z_scope.

Definition p1Zwf (x y : Z * Z) := Zwf 1 (fst x) (fst y).


(*
Lemma p1Zwf_well_founded : well_founded p1Zwf.
Proof. apply wf_inverse_image; apply (Zwf_well_founded 1). Qed.
*)

Theorem gcd_decr : forall x : Z * Z, 1 <= fst x -> 1 <= fst x /\ fst (snd x mod fst x, snd x) < fst x.
Proof. intros x xpos; destruct (Z_mod_lt (snd x) (fst x)); destruct x; simpl in * |- *; omega. Qed.

Definition gcd_F :forall x, (forall x', p1Zwf x' x -> Z) -> Z := fun x gcdr =>
    let a := fst x in let b := snd x in
    match Z_lt_le_dec a 1 with
      left _ => b
    | right apos =>
      let x' := b mod a in
       gcdr (x', a) (gcd_decr x apos)
   end.

(*
Definition gcd := Fix p1Zwf_well_founded (fun _ => Z) gcd_F.
*)

Check Fix_eq.

Lemma gcd_FP : forall x (f g : forall y, p1Zwf y x -> Z),
                   (forall y p, f y p = g y p) -> gcd_F x f = gcd_F x g.

Proof.
intros x f g P; unfold gcd_F; destruct x as [a b]; simpl.
destruct (Z_lt_le_dec a 1); auto.
Qed.

(*
Lemma gcd_fxp : forall x, gcd x = gcd_f x (fun y _ => gcd_y).
Proof.
 apply (Fix_eq p1Zwf_well_founded _ _ gcd_FP).
Qed.


Lemma gcd_12_21 : gcd (12,21) = 3.
Proof.
rewrite gcd_fxp; unfold gcd_F at 1; simpl.
replace (21 mod 12) with 9 by reflexivity.
rewrite gcd_fxp; unfold gcd_F at 1; simpl.
replace (12 mod 9) with 3 by reflexivity.
rewrite gcd_fxp; unfold gcd_F at 1; simpl.
replace (9 mod 3) with 0 by reflexivity.
rewrite gcd_fxp; unfold gcd_F at 1; simpl.
reflexivity.
Qed.


Functional Scheme gcd_F_ind := Induction for gcd_F Sort Prop.

Lemma gcd_is_divisor : forall p, 0 <= fst p -> 0 <= snd p ->
     exists k, exists l, fst p = k * gcd p /\ snd p = l * gcd p.
intros p; induction p using (well_founded_ind p1Zwf_well_founded).
destruct p as [a b]; simpl; intros a0 b0; rewrite gcd_fxp.
functional induction (gcd_F (a, b) (fun y _ => gcd y)).
  simpl in * |- *; exists 0; exists 1; split; omega.
simpl in * |- *.
destruct (H (b mod a, a) (gcd_decr (a,b) apos)) as [k [l [pk pl]]].
  destruct (Z_mod_lt b a); simpl; [omega | assumption].
 assumption.
exists l; exists (b / a * l + k);split; [ assumption | ].
rewrite Zmult_plus_distr_l <- Zmult_assoc, <- pl, <- pk; simpl.
rewrite Zmult_comm; apply Z_div_mod_eq; omega.
Qed.

*)
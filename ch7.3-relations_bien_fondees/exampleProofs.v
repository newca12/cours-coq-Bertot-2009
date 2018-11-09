Inductive bttree (A : Type) : Type :=
  L (a : A) | B (t1 t2 : bttree A) | T (t1 t2 t3 : bttree A).

Inductive blt(A : Type ) : bttree A -> bttree A -> Prop :=
  Lt1 : forall x y, blt A x (B A x y)
| Lt2 : forall x y, blt A y (B A x y)
| Lt3 : forall x y z, blt A x (T A x y z)
| Lt4 : forall x y z, blt A y (T A x y z)
| Lt5 : forall x y z, blt A z (T A x y z).

Lemma blt_wf : forall A, well_founded (blt A).
Proof.
intros A.
unfold well_founded.
induction a.
  apply Acc_intro.
  intros y predy.
  solve[inversion predy].
 apply Acc_intro.
 intros y predy.
 inversion predy.
  assumption.
 assumption.

apply Acc_intro; intros y predy; inversion predy; assumption.
Qed.






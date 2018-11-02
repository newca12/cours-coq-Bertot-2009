Lemma and_commute : forall a b: Prop, a /\ b -> b /\ a.
Proof.

intros a b.
intros H.
split.
destruct H as [Ha Hb].
exact Hb.
destruct H as [Ha Hb].
exact Ha.
Qed.





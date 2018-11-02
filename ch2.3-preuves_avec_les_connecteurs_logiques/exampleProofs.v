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

Check and_commute.

Lemma example :
  forall P Q : nat -> Prop, (forall x, P x -> Q x) /\ (exists x, ~Q x) ->
    ~forall x, P x \/ Q x.
Proof.
intros P Q.
intros H.
destruct H as [Hi He].
destruct He as [y Hy].
intros Ho.
case Hy.
destruct (Ho y) as [Hp | Hq].
apply Hi.
exact Hp.
exact Hq.
Qed.
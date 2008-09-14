Definition even x := exists y, x=2*y.
Definition odd x := exists y, x=2*y+1.

Lemma comeon : forall x, S x = x + 1.
  intro.
  elim x.
  simpl.
  reflexivity.
  intros.
  replace (S n + 1) with (S (n + 1)).
  rewrite <- H.
  trivial.
  simpl.
  trivial.
  Qed.

Lemma evensucc : forall x, even x -> odd (S x).
  intros.
  destruct H.
  exists x0.
  symmetry in H.
  rewrite H.
  elim x.
  simpl.
  trivial.
  intros.
  apply comeon.
  Qed.

Lemma sseven : forall x, even x -> even (S (S x)).
  induction x.
  intro.
  red.
  red in H.
  exists 1.
  simpl.
  trivial.
  intros.
  red.
  red in H.
  elim H.
  intros.
  exists (S x0).
  rewrite H0.
  simpl.
  auto.
  Qed.
  
Lemma oddsucc : forall x, odd x -> even (S x).
  intros.
  destruct H.
  replace (2*x0+1) with (S (2*x0)) in H.
  red.
  exists (S x0).
  simpl.
  simpl in H.
  replace (x0 + S (x0 + 0)) with (S (x0 + (x0 + 0))).
  rewrite <- H.
  trivial.
  auto.
  apply comeon.
  Qed.

Theorem evenodd : forall x, even x \/ odd x.
  intro.
  elim x.
  
  left.
    exists 0.
    simpl.
    trivial.
  intros.
  elim H.
  right.
  apply evensucc.
  exact H0.
  left.
  apply oddsucc.
  exact H0.
  Qed.
  
Axiom extensionality : forall A B (f g : A->B), (forall x, f x = g x) -> f = g.
Axiom biimplication : forall (P Q : Prop), (P <-> Q) -> P = Q.

Record Monoid (a:Type) : Type := 
  mkMonoid {
    mempty : a ;
    mappend : a -> a -> a ;
    left_unit : forall x, mappend mempty x = x ;
    right_unit : forall x, mappend x mempty = x ;
    assoc : forall x y z, mappend (mappend x y) z = mappend x (mappend y z)
  }.

Section prop_monoid.
  Variable A:Type.
  Let Rel := A -> A -> Prop.
  Let mempty : Rel := fun x y => x = y.
  Let mappend (r r' : Rel) := fun x y =>  exists a:A, r x a /\ r' a y.

  Lemma rel_left_unit : forall x, mappend mempty x = x.
   unfold mappend, mempty.
   intros.
   apply extensionality ; intro ; apply extensionality ; intro.
   apply biimplication ; split ; intros.
    destruct H.
     destruct H.
      rewrite H.
       assumption.
    exists x0.
     auto.
  Qed.

  Lemma rel_right_unit : forall x, mappend x mempty = x.
   unfold mappend, mempty.
   intros.
   apply extensionality ; intro ; apply extensionality ; intro.
   apply biimplication ; split ; intros.
    destruct H.
     destruct H.
      rewrite <- H0.
       assumption.
     exists x1.
      auto.
  Qed.

  Lemma rel_assoc : forall x y z, mappend (mappend x y) z = mappend x (mappend y z).
   unfold mappend; intros.
   apply extensionality ; intro ; apply extensionality ; intro.
   apply biimplication ; split ; intro.
    destruct H ; destruct H ; destruct H ; destruct H.
     exists x3 ; split.
      assumption.
      exists x2 ; split ; assumption.
    destruct H ; destruct H ; destruct H0 ; destruct H0.
     exists x3 ; split.
      exists x2 ; split ; assumption.
      assumption.
   Qed.

   Definition RelMonoid := mkMonoid Rel mempty mappend rel_left_unit rel_right_unit rel_assoc.
End prop_monoid.
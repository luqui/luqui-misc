Set Implicit Arguments.

Module Type FutureTheory.
  Axiom Time : Type.

  Axiom TimeLT : Time -> Time -> Type.
  Notation "A :< B" := (TimeLT A B) (at level 30, no associativity).

  Axiom transitive : forall a b c, (a :< b) -> (b :< c) -> (a :< c).
  Axiom antisym : forall a b, (a :< b) -> (b :< a) -> a = b.
  Axiom reflexive : forall a, a :< a.

  Definition UpperBound a b sup := (a :< sup * b :< sup)%type.
  Definition LowerBound a b inf := (inf :< a * inf :< b)%type.
  Definition LeastUpperBound a b sup :=
     (UpperBound a b sup * (forall s', UpperBound a b s' -> sup :< s'))%type.
  Definition GreatestLowerBound a b inf :=
     (LowerBound a b inf * (forall i', LowerBound a b i' -> i' :< inf))%type.

  Axiom lub : Time -> Time -> Time. 
  Axiom islub : forall a b, LeastUpperBound a b (lub a b).
  Axiom glb : Time -> Time -> Time.
  Axiom isglb : forall a b, GreatestLowerBound a b (glb a b).

  Axiom Future : Time -> Type -> Type.

  Axiom pure : forall t a, a -> Future t a.
  Axiom ap : forall t a b, Future t (a -> b) -> Future t a -> Future t b.
  Axiom deduce : forall t t' a, (t :< t') -> Future t' (Future t a -> a).

  Axiom quasitotality : forall t t', Future (glb t t') (t :< t' + t' :< t).
End FutureTheory.

Module FutureFacts (FT : FutureTheory).
  Import FT.
  Lemma project : forall t t' a, (t :< t') -> Future t a -> Future t' a.
   intros.
   refine (ap (deduce a X) (pure t' X0)).
  Defined.

  Lemma join : forall t t' sup a, UpperBound t t' sup -> 
                                            Future t (Future t' a) -> Future sup a.
   intros.
   destruct X.
   apply (project (a:=Future t' a) t0) in X0.
   exact (ap (deduce _ t1) X0).
  Defined.
End FutureFacts.
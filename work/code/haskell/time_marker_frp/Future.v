Set Implicit Arguments.

Module Type FutureTheory.
  (* The type of Time.  Typically some sort of fractional,
   * but it is not stirctly required. We could have "discrete FRP" :- *)
  Axiom Time : Type.

  (* Causality relation on Time: roughly, "before" *)
  Axiom TimeLT : Time -> Time -> Type.
  Notation "A :< B" := (TimeLT A B) (at level 30, no associativity).

  (* Here we say that (:<) is a partial order.  It is in fact a total order, but
   * with a caveat.  See "quasitotality" below. *) 
  Axiom transitive : forall a b c, (a :< b) -> (b :< c) -> (a :< c).
  Axiom antisym : forall a b, (a :< b) -> (b :< a) -> a = b.
  Axiom reflexive : forall a, a :< a.

  Definition LowerBound a b inf := (inf :< a * inf :< b)%type.
  Definition GreatestLowerBound a b inf :=
     (LowerBound a b inf * (forall i', LowerBound a b i' -> i' :< inf))%type.

  (* Every two elements have a greatest lower bound 
    * (obviously, it's just the minimum) *)
  Axiom glb : Time -> Time -> Time.
  Axiom isglb : forall a b, GreatestLowerBound a b (glb a b).

  (* Future t a  is a value of type a which is known at and after time t.
   * For reasoning, we will employ the intuitive idea that types are propositions,
   * so you can also think of this as "at time t, a is known" *)
  Axiom Future : Time -> Type -> Type.

  (* If we know a absolutely, then we know it at any time *)
  Axiom pure : forall a t, a -> Future t a.
  (* We can apply modus ponens at any single time *)
  Axiom ap : forall t a b, Future t (a -> b) -> Future t a -> Future t b.
  (* Deduction: this says that we know something after its time.  
   * More verbosely, at time t', if we know we know something at an earlier
   * time, then we know it now *)
  Axiom deduce : forall t t' a, (t :< t') -> Future t' (Future t a -> a).

  Definition mapF A B t (f:A->B) fut := ap (pure t f) fut.

  (* To weed out the clutter:  this property is:
   *  ap deduce (mapF pure f) = f
   *)
  Axiom prop_identity : forall t t' a (f:Future t' a), forall (h : t :< t'), 
         ap (deduce _ h) (mapF (pure _) f) = f.
  Axiom prop_pure_commute : forall a t (x:Future t a), pure t x = mapF (pure t) x.
  
  (* The following law is the analogue to the monad associativity, but for deduce
    * instead of join.  I'm rather unhappy with the complexity of its statement, in
    * particular the appearance of transitive  (requiring witness_extension).
    * Stated succinctly, the law is:
      ap deduce . ap deduce = ap deduce . mapF (ap deduce) *)
  Axiom prop_assoc : forall a ta tb tc (x:Future tc (Future tb (Future ta a))), forall (Hab : ta :< tb) (Hbc : tb :< tc),
    ap (deduce _ (transitive Hab Hbc)) (ap (deduce _ Hbc) x) 
    = ap (deduce _ Hbc) (mapF (ap (deduce _ Hab)) x).

  (* Here's the trickiest one.  This says that we can only perform a comparison
   * on two times after one of them has already occurred.  It's strange, because
   * before one of them occurs, the glb might be less than both of them, but
   * after one occurs, we know that the glb was one of them.
   *)
  Axiom quasitotality : forall t t', Future (glb t t') (t :< t' + t' :< t).
End FutureTheory.



Module FutureFacts (FT : FutureTheory).
  Import FT.
  (* If we know something at t, then we know it at all later times *)
  Definition project : forall t t' a, (t :< t') -> Future t a -> Future t' a.
   intros.
   refine (ap (deduce a X) (pure t' X0)).
  Defined.
  
  Definition UpperBound t t' sup := (t :< sup * t' :< sup)%type.

  (* If at time t we know that we will know a at time t', then after both t
   * and t'  (any upper bound of t and t') we know a.
   *)
  Definition join : forall t t' sup a, UpperBound t t' sup -> 
                                            Future t (Future t' a) -> Future sup a.
   intros.
   destruct X.
   apply (project (a:=Future t' a) t0) in X0.
   exact (ap (deduce _ t1) X0).
  Defined.

  (* A restricted variant of join for just at the same time *)
  Definition rjoin : forall t a, Future t (Future t a) -> Future t a.
   intros t a.
   assert (UpperBound t t t).
    split ; exact (reflexive t).
   refine (join X).
  Defined.

  (* It would seem that mapF, join, and pure make Future t a monad.  Let's check *)
  Section Monad_Laws.
  
  Hypothesis extensionality : forall a b (f g : a -> b), (forall x, f x = g x) -> f = g.
  Hypothesis witness_extension : forall a b (x : a :< b) (y : a :< b), x = y.

  Property monad_leftunit : forall a t (x:Future t a), rjoin (pure t x) = x.
   intros.
   unfold rjoin.
   unfold join.
   unfold project.
   rewrite prop_pure_commute.
   rewrite prop_identity.
   rewrite prop_pure_commute.
   rewrite prop_identity.
   trivial.
  Qed.

  Property monad_rightunit : forall a t (x:Future t a), rjoin (mapF (pure t) x) = x.
   intros.
   unfold rjoin, join, project.
   rewrite <- prop_pure_commute.
   rewrite prop_pure_commute.
   rewrite prop_identity.
   rewrite prop_pure_commute.
   rewrite prop_identity.
   trivial.
  Qed.

  Property monad_assoc : forall a t (x:Future t (Future t (Future t a))), 
     rjoin (rjoin x) = rjoin (mapF (rjoin (a:=a)) x).
   intros.
   unfold rjoin, join, project.
   rewrite prop_pure_commute.
   rewrite prop_identity.
   rewrite prop_pure_commute.
   rewrite prop_identity.
   rewrite prop_pure_commute.
   rewrite prop_identity.
   cut ((fun X0 => ap (deduce a (reflexive t)) (ap (deduce (Future t a) (reflexive t)) (pure t X0)))
         = (fun X0 => ap (deduce _ (reflexive t)) X0)).
   intro.
   rewrite H.
   clear H.
   replace (fun X0 => ap (deduce a (reflexive t)) X0) with (ap (deduce a (reflexive t))).
   pose (witness_extension (reflexive t) (transitive (reflexive t) (reflexive t))).
   pattern (reflexive t) at 1.
   rewrite e.
   refine (prop_assoc x _ _).
   
   apply extensionality ; trivial.
   apply extensionality.
   intros.
   rewrite prop_pure_commute.
   rewrite prop_identity.
   trivial.
  Qed.
  
  End Monad_Laws.
   
End FutureFacts.
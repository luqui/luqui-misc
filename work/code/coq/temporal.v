Set Implicit Arguments.

Axiom Time : Type.
Axiom TimeLT : Time -> Time -> Prop.
Notation "A :< B" := (TimeLT A B) (at level 15, no associativity).

Axiom lt_irrelevance : forall t t' (a b : t :< t'), a = b.

Axiom reflexive : forall t, t :< t.
Axiom transitive : forall t u v, (t :< u) -> (u :< v) -> (t :< v).
Axiom antisym : forall t u, (t :< u) -> (u :< t) -> t = u.

Definition LowerBound t u lb := lb :< t /\ lb :< u.
Definition GreatestLowerBound t u glb := LowerBound t u glb /\ (forall lb, LowerBound t u lb -> lb :< glb).

Axiom glb : Time -> Time -> Time.
Axiom glb_glb : forall t u, GreatestLowerBound t u (glb t u).

(* A future is a constant function from [t,∞) *) 
Definition Future t a := { f : forall t', (t :< t') -> a | forall t' n' t'' n'', f t' n' = f t'' n'' }.

(* Times are linearly ordered, but it is not known which is the 
 * lesser until one of them has passed *)
Axiom observable_total : forall t t', Future (glb t t') (t :< t' \/ t' :< t).
Axiom quasitotal : forall t t', ~(~(t :< t') /\ ~(t' :< t)). 

Lemma glb_linear : forall t u, t :< u -> glb t u = t.
 intros.
 apply antisym.
  exact (proj1 (proj1 (glb_glb t u))).
  apply (proj2 (glb_glb t u)) ; split.
   apply reflexive.
   assumption.
Qed.

Lemma lowerbound_symmetric : forall t u lb, LowerBound t u lb -> LowerBound u t lb.
 unfold LowerBound ; intros.
 destruct H ; split ; assumption.
Qed.

Lemma glb_unique : forall t u lb lb', GreatestLowerBound t u lb -> GreatestLowerBound t u lb' -> lb = lb'.
 intros.
 destruct H.
 destruct H0.
 apply antisym.
  apply H2 ; split.
   exact (proj1 H).
   exact (proj2 H).
  apply H1 ; split.
   exact (proj1 H0).
   exact (proj2 H0).
Qed.

Lemma glb_symmetric : forall t u, glb t u = glb u t.
 intros.
 refine (glb_unique (t:=t) (u:=u) _ _).
  exact (glb_glb t u).
  destruct (glb_glb u t).
   split.
    split.
     exact (proj2 H).
     exact (proj1 H).
    intros.
     exact (H0 _ (lowerbound_symmetric H1)).
Qed.

Section quasitotal_2.
  Variables (t t' : Time).

  Let f : forall t'0 : Time, glb t t' :< t'0 -> glb t t' = t \/ glb t t' = t'.
   intros.
   destruct (observable_total t t').
    pose (glb_glb t t').
    destruct (x t (proj1 (proj1 (glb_glb t t')))).
     left. apply glb_linear. assumption.
     right. rewrite glb_symmetric. apply glb_linear. assumption.
  Defined.
   
  Lemma quasitotal_2 : Future (glb t t') (glb t t' = t \/ glb t t' = t').
   unfold Future ; intros.
   destruct (observable_total t t').
   exists f ; intros.
   unfold f.
   set (o := x t (proj1 (proj1 (glb_glb t t')))).
   case o ; trivial.
  Qed.
End quasitotal_2.

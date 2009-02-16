Require Import Coq.Program.Tactics.

Inductive Ty :=
| TyNat : Ty
| TyArrow : Ty -> Ty -> Ty.

Fixpoint reify (ty:Ty) : Type :=
  match ty with
  | TyNat => nat
  | TyArrow dom cod => reify dom -> reify cod
  end.

Program Fixpoint ty_dec (x y : Ty) : (x = y) + (x <> y) :=
  match x with
  | TyNat => match y with
                    | TyNat => inl _ (refl_equal x)
                    | TyArrow dom cod => inr _ _
                    end
  | TyArrow dom cod => match y with
                                       | TyNat => inr _ _
                                       | TyArrow dom' cod' => 
                                          match ty_dec dom dom' with
                                          | inl r => match ty_dec cod cod' with
                                                           | inl r' => inl _ _
                                                           | inr r' => inr _ _
                                                           end
                                          | inr r => inr _ _
                                          end
                                       end
  end.

Next Obligation.
  rewrite r ; rewrite r' ; trivial.
Defined.

Definition ty_dec' : forall (x y : Ty), (x = y) + (x <> y).
 intro.
 induction x ; intro.
 destruct y.
 left ; trivial.
 right ; discriminate.
 destruct y.
 right ; discriminate.
 destruct (IHx1 y1).
 destruct (IHx2 y2).
 rewrite e ; rewrite e0.
 left ; trivial.
 right ; injection ; contradiction.
 right ; injection ; contradiction.
Defined.

Definition Value := { ty : Ty & reify ty }.

Definition tryApp : Value -> Value -> option Value.
  intros [fty fv] [xty xv].
  destruct fty.
   exact None.
  destruct (ty_dec' fty1 xty).
   rewrite e in fv.
   simpl reify in fv.
   apply Some.
   exists fty2.
   exact (fv xv).
   exact None.
Defined.

Definition succ : Value.
 exists (TyArrow TyNat TyNat).
 red.
 exact S.
Defined.

Definition zero : Value.
 exists TyNat.
 red.
 exact O.
Defined.

Eval compute in tryApp succ zero.
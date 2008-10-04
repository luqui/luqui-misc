(* A program demonstrating how to specify infinite axiom schemata.
 * This program directly introduces all classical tautologies; i.e. if every
 * assigment of true and false to the variables in a formula is valid, 
 * the the formula is an axiom.

 * It does this by building a data structure representing formulae, and
 * then specifying the interpretation of that structure as a "real" Prop.
 * The only axiom, "classical_tautologies", says that if the data structure
 * is a tautology, then its interpretation is an axiom.

 * Finally, simply to demonstrate the technique, we show that the law of 
 * excluded middle is a consequence of this schema.
*)

Require Import Arith.

Inductive Formula : Type :=
| FNot : Formula -> Formula
| FOr  : Formula -> Formula -> Formula
| FVar : nat -> Formula.

Definition bnot (b:bool) :=
  match b with | true => false | false => true end.

Definition bor (b:bool) (b':bool) :=
  match b with | true => true | false => b' end.

Definition eval : (nat -> bool) -> Formula -> bool.
 intros.
 induction H0.
  exact (bnot IHFormula).
  exact (bor IHFormula1 IHFormula2).
  exact (H n).
Defined.

Definition isTauto (f:Formula) := forall subst, eval subst f = true.

Definition max : nat -> nat -> nat.
  intros x y.
  SearchAbout le.
  elim (le_lt_dec x y) ; intro.
   exact y.
   exact x.
Defined.

Definition maxidx : Formula -> nat.
  intro.
  induction H.
   exact IHFormula.
   exact (max IHFormula1 IHFormula2).
   exact n.
Defined.

Definition dec_eq_nat : forall m n : nat, { m = n } + { m <> n }.
  intros.
  destruct (gt_eq_gt_dec m n).
  destruct s.
  right.
  unfold not ; intro.
  rewrite H in g.
  exact (gt_irrefl n g).
  left ; exact e.
  right.
  unfold not ; intro.
  rewrite H in g.
  exact (gt_irrefl n g).
Defined.

Definition allocate : nat -> ((nat -> Prop) -> Prop) -> Prop.
  intro var.
  induction var.
   intro cc.
    exact (cc (fun x => False)).
   intro cc.
    refine (all (A:=Prop) _) ; intro Var.
    apply cc ; intro x.
    destruct (dec_eq_nat x var).
     exact Var.
     exact (IHvar cc).
Defined.


Definition evalProp : (nat -> Prop) -> Formula -> Prop.
  intros subst f.
  induction f.
   exact (~IHf).
   exact (IHf1 \/ IHf2).
   exact (subst n).
Defined.

Definition interpret : Formula -> Prop.
  intro f.
  apply (allocate (S (maxidx f))) ; intro subst.
  exact (evalProp subst f).
Defined.

Axiom classical_tautologies : forall f, isTauto f -> interpret f.

Definition exmid_formula := FOr (FVar 0) (FNot (FVar 0)).

Lemma bool_exmid : forall b, { b = true } + { b = false }.
 intros.
 case b ; auto.
Qed.

Lemma exmid_tauto : isTauto exmid_formula.
 unfold isTauto.
 intro.
 destruct (bool_exmid (subst 0)) ; simpl ; rewrite e ; auto.
Qed.

Theorem exmid : forall P, (P \/ ~P).
  pose (cand := classical_tautologies exmid_formula exmid_tauto).
  intros.
  unfold interpret in cand.
  simpl in cand.
  pose (inst _ P cand).
  simpl in o.
  assumption.
Qed.
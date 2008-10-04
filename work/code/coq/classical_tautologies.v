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

(* Not on booleans (should be in a library somewhere) *)
Definition bnot (b:bool) :=
  match b with | true => false | false => true end.

(* Or on booleans *)
Definition bor (b:bool) (b':bool) :=
  match b with | true => true | false => b' end.

(* Take a substitution function (variable "names" into booleans)
 * and evaluate whether the formula's value is true or false *)
Definition eval : (nat -> bool) -> Formula -> bool.
 intros.
 induction H0.
  (* FNot case *)
  exact (bnot IHFormula).
  (* FOr case *)
  exact (bor IHFormula1 IHFormula2).
  (* FVar case *)
  exact (H n).
Defined.

(* Property expressing whether f represents a classical tautology:
 * If the value of the expression is true under every substitution
 * function, then it is a tautology *)
Definition isTauto (f:Formula) := forall subst, eval subst f = true.

(* Maximum of two numbers *)
Definition max : nat -> nat -> nat.
  intros x y.
  elim (le_lt_dec x y) ; intro.
   exact y.
   exact x.
Defined.

(* Find the maximum index of any referenced variable in the formula. *)
Definition maxidx : Formula -> nat.
  intro.
  induction H.
   (* FNot case *)
   exact IHFormula.
   (* FOr case *)
   exact (max IHFormula1 IHFormula2).
   (* FVar case *)
   exact n.
Defined.

(* Compare two numbers for equality (come on, why the fuck isn't
 * this in the library!) *)
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

(* Takes a number n of variables to allocate, and generates
 * a universal quantifier for each variable, and maps that
 * variable into a substitution function. For example:  
 * 
 * allocate 2 (fun subst => subst 0 \/ subst 1)
 * Evaluates to:
 * forall X Y, X \/ Y.
 *)
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

(* Evaluate a formula given a substitution of Properties
 * (rather than simply booleans) and returns whether its
 * valuation is true under that substition (again as a
 * "real" Prop, rather than a bool)
 *)
Definition evalProp : (nat -> Prop) -> Formula -> Prop.
  intros subst f.
  induction f.
   exact (~IHf).
   exact (IHf1 \/ IHf2).
   exact (subst n).
Defined.

(* Takes a formula, universally quanitifes all variables,
 * and returns the interpretation as a Prop. *)
Definition interpret : Formula -> Prop.
  intro f.
  apply (allocate (S (maxidx f))) ; intro subst.
  exact (evalProp subst f).
Defined.

(* The axiom.  This says that if f is a tautology on booleans,
 * then we accept its interpretation as an axiom on Props.
 *)
Axiom classical_tautologies : forall f, isTauto f -> interpret f.

(* The encoding of the law of excluded middle: forall P, P \/ ~P *)
Definition exmid_formula := FOr (FVar 0) (FNot (FVar 0)).

(* Excluded middle holds on booleans (because it is a simple inductive
 * type.
 *)
Lemma bool_exmid : forall b, { b = true } + { b = false }.
 intros.
 case b ; auto.
Qed.

(* Show that exmid_formula is a tautology on booleans.  This is done
 * by analyzing the cases of subst 0, where subst is the substitution
 * function.  We don't care about any of the other (infinitely many)
 * values of subst.
 *)
Lemma exmid_tauto : isTauto exmid_formula.
 unfold isTauto.
 intro.
 destruct (bool_exmid (subst 0)) ; simpl ; rewrite e ; auto.
Qed.

(* Prove the law of excluded middle from the classical_tautologies
 * axiom.
 *)
Theorem exmid : forall P, (P \/ ~P).
  pose (cand := classical_tautologies exmid_formula exmid_tauto).
  intros.
  unfold interpret in cand.
  simpl in cand.
  pose (inst _ P cand).
  simpl in o.
  assumption.
Qed.

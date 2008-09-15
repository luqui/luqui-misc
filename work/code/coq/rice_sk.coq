(* This is a formal proof of Rice's theorem for SK calculus.  Rice's theorem
implies the halting problem.  

Precisely, it is "there is no complete, nontrivial predicate".  That is, if you have
a function f which returns either true or false for every input, then that function
has to be trivial; i.e. it has to return the same thing for all inputs.

This implies the halting problem, since the oracle machine is a nontrivial predicate.
I tried to formalize the halting problem directly in terms of normal forms, but
the axiomatization I used made that very difficult (or impossible); i.e. I said that
two convertible terms are *equal*, so talking about "forms" was not possible.
That is, SKKK is not in normal form, but it is equal to K, which is in normal form,
so obviously the concept of normal form is ill-defined in this axiomatization.

And it's my first real proof in Coq.  Yaay!

- Luke Palmer, 2008-09-15
*)

Set Implicit Arguments.

Axiom T:Set.
Axiom S:T.
Axiom K:T.
Axiom App : T->T->T.

(* The standard reduction rule for S *)
Axiom s_elim : forall x y z, App (App (App S x) y) z = App (App x z) (App y z).
(* And the one for K *)
Axiom k_elim : forall x y, App (App K x) y = x.
(* Extensionality of functions *)
Axiom eta : forall a b, (forall x, App a x = App b x) -> a = b.
(* Minimal axiom to avoid the trivial theory (where all functions are equal) *)
Axiom s_noteq_k : S <> K.

Lemma eta_contra : forall a b, (exists x, App a x <> App b x) -> a <> b.
 intros.
 change (a = b -> False); intro.
 elim H; intros.
 apply (f_equal (fun k => App k x)) in H0.
 contradiction.
Qed.

Definition I := App (App S K) K.
Lemma i_elim : forall x, App I x = x.
 intro.
 unfold I.
 rewrite s_elim.
 rewrite k_elim.
 trivial.
Qed.

Lemma i_noteq_s : I <> S.
 apply eta_contra ; exists K.
 apply eta_contra ; exists K.
 apply eta_contra ; exists S.
 rewrite i_elim.
 rewrite k_elim.
 fold I.
 rewrite i_elim.
 apply (sym_not_eq).
 exact s_noteq_k.
Qed.

Lemma i_noteq_k : I <> K.
 apply eta_contra ; exists I.
 apply eta_contra ; exists S.
 rewrite i_elim.
 rewrite i_elim.
 rewrite k_elim.
 apply sym_not_eq.
 exact i_noteq_s.
Qed.

(* Y = S (K (S I I)) (S (S (K S) K) (K (S I I))) *)

Coercion App : T >-> Funclass.

Definition Y := S (K (S I I)) (S (S (K S) K) (K (S I I))).

Ltac rs := rewrite s_elim.
Ltac rk := rewrite k_elim.
Ltac ri := rewrite i_elim.

Definition ynorm (x:T) := x (x (S I I (S (K x) (S I I)))).

Lemma ynorm_left : forall x, Y x = ynorm x.
 intro.
 unfold Y.
 rs. rk. rs. ri. rs. rs. rk. rs. rk. 
 rk. rs. ri. rs. rk.
 trivial.
Qed.

Lemma ynorm_right : forall (x:T), x (Y x) = ynorm x.
 intro.
 unfold Y.
 rs. rk. rs. ri. rs. rs. rk. rs. rk. rk.
 trivial.
Qed.

Lemma fixpoint : forall x, Y x = x (Y x).
 intro.
 pattern Y at 1 ; rewrite ynorm_right.
 rewrite ynorm_left.
 trivial.
Qed.


(* A complete predicate returns true (K) or false (K I) for every input *)
Definition complete (y:T) := forall x, y x = K \/ y x = K I.

(* A nontrivial predicate doesn't return the same thing for all inputs;
   i.e. returns true (K) for one and false (K I) for another. *)
Definition nontrivial (y:T) := (exists a, y a = K) /\ (exists b, y b = K I).

Lemma k_noteq_ki : K <> K I.
 apply eta_contra ; exists S.
 apply eta_contra ; exists I.
 rk. rk. ri.
 apply (sym_not_eq).
 exact (i_noteq_s).
Qed.

(* There is no complete predicate with the property P K = K I and P (K I) = K. *)
Lemma rice_hint : (exists P, complete P /\ P K = K I /\ P (K I) = K) -> False.
(* no complete P, P K = KI, P KI = K:
    P (fix P) = K or P (fix P) = KI
    if P (fix P) = K
      fix P = P (fix P)
      fix P = K or fix P = KI
      P (fix P) = K so fix P = KI = P (fix P) = K  (!)
    if P (fix P) = KI
      fix P = P (fix P)
      fix P = K or fix P = KI
      P (Fix P) = KI so fix P = K = P (fix P) = KI (!)
*)
 intro.
 destruct H.
 destruct H.
 destruct H0.
 rename x into P.
 unfold complete in H.
 pose (H (Y P)).
 destruct o.

  (* P (fix P) = K *)
  pose H2.
  rewrite <- fixpoint in e.
  pattern K at 1 in H0 ; rewrite <- e in H0.
  pose k_noteq_ki.
  apply sym_equal in H2.
  pose (trans_equal H2 H0).
  contradiction.

  (* P (fix P) = K I *)
  pose H2.
  rewrite <- fixpoint in e.
  rewrite <- e in H1.
  apply sym_equal in H1.
  pose (trans_equal H1 H2).
  pose k_noteq_ki.
  contradiction.
Qed.


Definition compose := S (K S) K.
Lemma compose_really_does : forall f g x, compose f g x = f (g x).
 intros.
 unfold compose.
 rs. rk. rs. rk. trivial.
Qed.

Definition flip := S (S (K (S (K S) K)) S) (K K).
Lemma flip_really_does : forall f x y, flip f x y = f y x.
 intros.
 unfold flip.
 rs. rs. rk. rs. rk. rs. rk. rs. rk. rk. trivial.
Qed.

Definition ap := flip I.
Lemma ap_really_does : forall x y, ap x y = y x.
 intros.
 unfold ap.
 rewrite flip_really_does.
 ri. trivial.
Qed.

Lemma complete_carry : forall P x, complete P -> complete (compose P x).
 intros.
 unfold complete in H.
 unfold complete.
 intros.
 pose (H (x x0)).
 destruct o.
 left.
 rewrite compose_really_does.
 assumption.
 right.
 rewrite compose_really_does.
 assumption.
Qed.

(* Rice's theorem: there is no complete, nontrivial predicate.  We assume
    there is, and then construct the impossible predicate of rice_hint,
    named P' in the proof below. *)
Theorem rice : (exists P, complete P /\ nontrivial P) -> False.
(* P a = K, P b = K I
    let P' x = P (x b a)   (if x then b else a)
    P' K = P b = K I
    P' (K I) = P a = K
    P' completeness follows from P's completeness
*)
 intro.
 destruct H.
 destruct H.
 unfold nontrivial in H0.
 destruct H0.
 destruct H0 ; rename x0 into a.
 destruct H1 ; rename x0 into b.
 rename x into P.
 pose (P' := compose (compose P (ap a)) (ap b)).
 cut (P' K = K I). intro.
 cut (P' (K I) = K). intro.
 pose rice_hint.
 destruct f.
 exists P'.
 pose (complete_carry (ap a) H).
 pose (complete_carry (ap b) c).
 replace (compose (compose P (ap a)) (ap b)) with P' in c0.
 split.
 assumption.
 split.
 assumption.
 assumption.
 
 trivial.
 unfold P'.
 rewrite compose_really_does.
 rewrite compose_really_does.
 rewrite ap_really_does.
 rewrite ap_really_does.
 rk. ri.
 assumption.
 unfold P'.
 rewrite compose_really_does.
 rewrite compose_really_does.
 rewrite ap_really_does.
 rewrite ap_really_does.
 rk.
 assumption.
Qed.
 
 

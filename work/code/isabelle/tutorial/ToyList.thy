theory ToyList
imports PreList
begin

datatype 'a list = Nil                ("[]")
                 | Cons 'a "'a list"  (infixr "#" 65)

consts app :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"  (infixr "@" 65)
       rev :: "'a list \<Rightarrow> 'a list"

primrec
 "[] @ ys       = ys"
 "(x # xs) @ ys = x # (xs @ ys)"

primrec
 "rev [] = []"
 "rev (x # xs) = (rev xs) @ (x # [])"

lemma app_Nil2 [simp]: "xs @ [] = xs"
  apply(induct_tac xs)
  apply(auto)
done

lemma app_assoc [simp]: "(xs @ ys) @ zs = xs @ (ys @ zs)"
  apply(induct_tac xs)
  apply(auto)
done

lemma rev_app [simp]: "rev(xs @ ys) = rev ys @ rev xs"
  apply(induct_tac xs)
  apply(auto)
done

theorem rev_rev [simp]: "rev (rev xs) = xs"
  apply(induct_tac xs)
  apply(auto)
done

end
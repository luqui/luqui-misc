theory BoolEx
imports Main
begin

datatype boolex = Const bool | Var nat | Neg boolex
                | And boolex boolex

consts "value" :: "boolex \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> bool"
primrec
 "value (Const b)  env = b"
 "value (Var x)    env = env x"
 "value (Neg b)    env = (\<not> value b env)"
 "value (And b c)  env = (value b env \<and> value c env)"

datatype ifex = CIF bool | VIF nat | IF ifex ifex ifex

consts valif :: "ifex \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> bool"
primrec
 "valif (CIF b) env = b"
 "valif (VIF x) env = env x"
 "valif (IF b t e) env = (if valif b env then valif t env 
                                         else valif e env)"

consts bool2if :: "boolex \<Rightarrow> ifex"
primrec
 "bool2if (Const b) = CIF b"
 "bool2if (Var x) = VIF x"
 "bool2if (Neg b) = IF (bool2if b) (CIF False) (CIF True)"
 "bool2if (And b c) = IF (bool2if b) (bool2if c) (CIF False)"

lemma bool2if_preserve: "valif (bool2if b) env = value b env"
  apply(induct_tac b)
  apply(auto)
done

consts normif :: "ifex \<Rightarrow> ifex \<Rightarrow> ifex \<Rightarrow> ifex"
primrec 
 "normif (CIF b) t e = IF (CIF b) t e"
 "normif (VIF x) t e = IF (VIF x) t e"
 "normif (IF b t e) tt ee = normif b (normif t tt ee) (normif e tt ee)"

consts norm :: "ifex \<Rightarrow> ifex"
primrec
 "norm (CIF b) = CIF b"
 "norm (VIF x) = VIF x"
 "norm (IF b t e) = normif b (norm t) (norm e)"

lemma [simp]: "\<forall> t e. valif (normif b t e) env = valif (IF b t e) env"
  apply(induct_tac b)
  apply(auto)
done

theorem norm_preserve: "valif (norm b) env = valif b env"
  apply(induct_tac b)
  apply(auto)
done

consts normalForm :: "ifex \<Rightarrow> bool"
primrec
 "normalForm (CIF b) = True"
 "normalForm (VIF x) = True"
 "normalForm (IF b t e) = (normalForm t \<and> normalForm e \<and>
                          (case b of CIF _ \<Rightarrow> True | VIF _ \<Rightarrow> True | IF _ _ _ \<Rightarrow> False))"

lemma [simp]: "\<forall> t e. normalForm (normif b t e) = (normalForm t \<and> normalForm e)"
  apply(induct_tac b)
  apply(auto)
done

end



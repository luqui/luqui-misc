theory Exercises
imports Main
begin

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

consts mirror :: "'a tree \<Rightarrow> 'a tree"

primrec
 "mirror Tip = Tip"
 "mirror (Node l x r) = Node (mirror r) x (mirror l)"

lemma mirror_mirror [simp]: "mirror (mirror t) = t"
  apply(induct_tac t)
  apply(auto)
done

consts flatten :: "'a tree \<Rightarrow> 'a list"

primrec
 "flatten Tip = []"
 "flatten (Node l x r) = flatten l @ [x] @ flatten r"

lemma flatten_mirror: "flatten (mirror t) = rev (flatten t)"
  apply(induct_tac t)
  apply(auto)
done

end



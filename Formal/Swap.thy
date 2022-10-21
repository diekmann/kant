theory Swap
imports Main
begin

section\<open>Swap\<close>

definition swap :: "'a \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" where
  "swap a b f \<equiv> f(a:=f b, b:= f a)"

lemma swap1[simp]: "swap a b (swap a b f) = f"
  by(simp add: swap_def)
lemma swap2[simp]: "swap b a (swap a b f) = f"
  by(simp add: swap_def)
lemma swap_id[simp]: "swap a a f = f"
  by(simp add: swap_def)
lemma "f_swapped = (swap a b f) \<Longrightarrow> f_swapped a = f b \<and> f_swapped b = f a"
  by(simp add: swap_def)
lemma swap_symmetric: "swap a b = swap b a"
  by(simp add: fun_eq_iff swap_def)
lemma map_swap_none: "a \<notin> set P \<Longrightarrow> b \<notin> set P \<Longrightarrow> map (swap a b f) P = map f P"
  by(simp add: swap_def)
lemma map_swap_one: "a \<notin> set P \<Longrightarrow>  map (swap a b f) P = map (f(b:=f a)) P"
  by(simp add: swap_def)
lemma swap_a: "swap a b f a = f b"
  by(simp add: swap_def)
lemma swap_b: "swap a b f b = f a"
  by(simp add: swap_def)
lemma sum_swap_none: "a \<notin> P \<Longrightarrow> b \<notin> P \<Longrightarrow> sum (swap a b f) P = sum f P"
  apply(simp add: swap_def)
  by (smt (verit, best) fun_upd_other sum.cong)
lemma swap_nothing: "a \<noteq> p1 \<Longrightarrow> a \<noteq> p2 \<Longrightarrow> swap p1 p2 f a = f a"
  by(simp add: swap_def)


end
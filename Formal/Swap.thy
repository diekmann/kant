theory Swap
imports Main Helper
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


thm sum.remove
lemma sum_swap_a: "finite P \<Longrightarrow> a \<notin> P \<Longrightarrow> b \<in> P \<Longrightarrow> sum (swap a b f) P = f a + sum f (P - {b})"
  apply(subst sum.remove[of P b])
  by(simp_all add: swap_b sum_swap_none)

lemma sum_list_swap: "p1 \<in> set P \<Longrightarrow> p2 \<in> set P \<Longrightarrow> distinct P \<Longrightarrow>
        sum_list (map (swap p1 p2 f) P) = sum_list (map (f::'a\<Rightarrow>int) P)"
  apply(simp add: sum_list_map_eq_sum_count_int)
  apply(simp add: count_list_distinct)
  thm sum.cong
  apply(induction P arbitrary: p1 p2)
   apply(simp)
  apply(simp)
  apply(elim disjE)
     apply(simp_all)
    apply(simp add: swap_a sum_swap_a sum.remove[symmetric]; fail)
   apply(simp add: swap_symmetric swap_a sum_swap_a sum.remove[symmetric]; fail)
  apply(rule swap_nothing)
  by auto

end
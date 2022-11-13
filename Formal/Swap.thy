theory Swap
imports Helper
begin

section\<open>Swap\<close>

definition swap :: \<open>'a \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b\<close> where
  \<open>swap a b f \<equiv> f(a:=f b, b:= f a)\<close>

lemma swap1[simp]: \<open>swap a b (swap a b f) = f\<close>
  by(simp add: swap_def)
lemma swap2[simp]: \<open>swap b a (swap a b f) = f\<close>
  by(simp add: swap_def)
lemma swap3: "(swap p1 p2 swap) p1 p2 x = x" (*wow, types*)
  by(simp add: swap_def)
lemma swap4: "(swap p2 p1 swap) p1 p2 x = x" (*wow, types*)
  by(simp add: swap_def)
lemma swap_id[simp]: \<open>swap a a f = f\<close>
  by(simp add: swap_def)
lemma \<open>f_swapped = (swap a b f) \<Longrightarrow> f_swapped a = f b \<and> f_swapped b = f a\<close>
  by(simp add: swap_def)
lemma swap_symmetric: \<open>swap a b = swap b a\<close>
  by(simp add: fun_eq_iff swap_def)
lemma map_swap_none: \<open>a \<notin> set P \<Longrightarrow> b \<notin> set P \<Longrightarrow> map (swap a b f) P = map f P\<close>
  by(simp add: swap_def)
lemma map_swap_one: \<open>a \<notin> set P \<Longrightarrow>  map (swap a b f) P = map (f(b:=f a)) P\<close>
  by(simp add: swap_def)
lemma swap_a: \<open>swap a b f a = f b\<close>
  by(simp add: swap_def)
lemma swap_b: \<open>swap a b f b = f a\<close>
  by(simp add: swap_def)
lemma sum_swap_none: \<open>a \<notin> P \<Longrightarrow> b \<notin> P \<Longrightarrow> sum (swap a b f) P = sum f P\<close>
  apply(rule sum.cong, simp)
  apply(simp add: swap_def)
  by fastforce
lemma swap_nothing: \<open>a \<noteq> p1 \<Longrightarrow> a \<noteq> p2 \<Longrightarrow> swap p1 p2 f a = f a\<close>
  by(simp add: swap_def)

lemma swap_forall: \<open>(\<forall>p. P (swap p1 p2 a p) (swap p1 p2 b p)) \<longleftrightarrow> (\<forall>p. P (a p) (b p))\<close>
  by (metis swap_a swap_b swap_nothing)

thm sum.remove
lemma sum_swap_a: \<open>finite P \<Longrightarrow> a \<notin> P \<Longrightarrow> b \<in> P \<Longrightarrow> sum (swap a b f) P = f a + sum f (P - {b})\<close>
  apply(subst sum.remove[of \<open>P\<close> \<open>b\<close>])
  by(simp_all add: swap_b sum_swap_none)

lemma sum_list_swap: \<open>p1 \<in> set P \<Longrightarrow> p2 \<in> set P \<Longrightarrow> distinct P \<Longrightarrow>
        sum_list (map (swap p1 p2 f) P) = sum_list (map (f::'a\<Rightarrow>int) P)\<close>
  apply(simp add: sum_list_map_eq_sum_count_int)
  apply(simp add: count_list_distinct)
  thm sum.cong
  apply(induction \<open>P\<close> arbitrary: \<open>p1\<close> \<open>p2\<close>)
   apply(simp)
  apply(simp)
  apply(elim disjE)
     apply(simp_all)
    apply(simp add: swap_a sum_swap_a sum.remove[symmetric]; fail)
   apply(simp add: swap_symmetric swap_a sum_swap_a sum.remove[symmetric]; fail)
  apply(rule swap_nothing)
  by auto


lemma min_list_swap_int:
  fixes f::"'person \<Rightarrow> int"
  shows "p1 \<in> set ps \<Longrightarrow> p2 \<in> set ps \<Longrightarrow> min_list (map (swap p1 p2 f) ps) = min_list (map f ps)"
  apply(cases "ps = []")
   apply(simp; fail)
  apply(simp add: min_list_Min)
  apply(cases "p1 = p2")
   apply(simp)
  by (smt (verit, best) List.finite_set Min_in Min_le arg_min_list_in f_arg_min_list_f finite_imageI imageE image_eqI image_is_empty swap2 swap_a swap_b swap_nothing)

lemma min_list_swap_int_enum:
  fixes f::"'person::enum \<Rightarrow> int"
  shows "min_list (map (swap p1 p2 f) enum_class.enum) = min_list (map f enum_class.enum)"
  apply(subst min_list_swap_int)
  by(simp_all add: enum_class.enum_UNIV)

end
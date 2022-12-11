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
lemma swap3: \<open>(swap p1 p2 swap) p1 p2 x = x\<close> (*wow, types*)
  by(simp add: swap_def)
lemma swap4: \<open>(swap p2 p1 swap) p1 p2 x = x\<close> (*wow, types*)
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

lemma swap_id_comp: \<open>swap a a = id\<close>
  by(simp add: fun_eq_iff)
lemma swap_fun_comp_id:
  \<open>swap p1 p2 (f \<circ> swap p1 p2 (f \<circ> kons)) = f \<circ> (f \<circ> kons)\<close>
  apply(simp add: comp_def fun_eq_iff)
  apply(simp add: swap_def)
  done
lemma swap_fun_map_comp_id:
  \<open>swap p1 p2 (map (swap p1 p2) \<circ> swap p1 p2 (map (swap p1 p2) \<circ> kons)) = kons\<close>
  apply(simp add: comp_def fun_eq_iff)
  apply(simp add: swap_def swap_id_comp)
  by (simp add: map_idI)


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
  fixes f::\<open>'person \<Rightarrow> int\<close>
  shows \<open>p1 \<in> set ps \<Longrightarrow> p2 \<in> set ps \<Longrightarrow> min_list (map (swap p1 p2 f) ps) = min_list (map f ps)\<close>
  apply(cases \<open>ps = []\<close>)
   apply(simp; fail)
  apply(simp add: min_list_Min)
  apply(cases \<open>p1 = p2\<close>)
   apply(simp)
  by (smt (verit, best) List.finite_set Min_in Min_le arg_min_list_in f_arg_min_list_f finite_imageI imageE image_eqI image_is_empty swap2 swap_a swap_b swap_nothing)

lemma min_list_swap_int_enum:
  fixes f::\<open>'person::enum \<Rightarrow> int\<close>
  shows \<open>min_list (map (swap p1 p2 f) enum_class.enum) = min_list (map f enum_class.enum)\<close>
  apply(subst min_list_swap_int)
  by(simp_all add: enum_class.enum_UNIV)

lemma remove1_swap:
  \<open>remove1 (swap p1 p2 a) (map (swap p1 p2) ks)
    = map (swap p1 p2) (remove1 a ks)\<close>
  apply(induction \<open>ks\<close>)
   apply(simp)
  apply(simp)
  by (metis swap2)

lemma remove1_swap2:
  \<open>map (swap p1 p2) (remove1 (swap p1 p2 a) (map (swap p1 p2) ks))
    =  remove1 a ks\<close>
  apply(induction \<open>ks\<close>)
   apply(simp)
  apply(simp add: comp_def)
  by (metis (mono_tags, lifting) swap2)

lemma swap_if_move_inner:
  \<open>swap p2 p1 (\<lambda>p. if P p then A p else B p)
    = (\<lambda>p. if P (swap p2 p1 id p) then A (swap p2 p1 id p) else B (swap p2 p1 id p))\<close>
  by(simp add: swap_def fun_eq_iff)
  
lemma swap_id_in_set:
  \<open>swap p2 p1 id x \<in> swap p1 p2 id ` A \<longleftrightarrow> x \<in> A\<close>
  by (smt (verit, best) id_def image_iff swap_b swap_nothing swap_symmetric)




(*TODO: baut swap eine Permutation und gibt es darauf lemmata?*)
lemma "distinct [p1,p2,p3,p4] \<Longrightarrow> swap p1 p2 (swap p3 p4 welt) = swap p3 p4 (swap p1 p2 welt)"
  by(auto simp add: swap_def)

lemma swap_comm: "p1 \<noteq> p3 \<Longrightarrow> p1 \<noteq> p4 \<Longrightarrow> p2 \<noteq> p3 \<Longrightarrow> p2 \<noteq> p4 \<Longrightarrow>
  swap p1 p2 (swap p3 p4 welt) = swap p3 p4 (swap p1 p2 welt)"
  by(auto simp add: swap_def)

lemma swap_unrelated_im_kreis:
  "p \<noteq> p1 \<Longrightarrow> p \<noteq> p2 \<Longrightarrow>
    swap p2 p (swap p1 p2 (swap p p1 (swap p1 p2 welt))) = welt"
  by(simp add: swap_def)

end
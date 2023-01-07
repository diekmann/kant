theory Swap
imports Helper "HOL-Combinatorics.Transposition" BeispielTac
begin

section\<open>Swap\<close>
text\<open>In diesem Abschnitt werden wir eine swap Funktion bauen,
welche es erlaubt Eigenschaften von Personen auszutauschen.
Wenn wir beispielsweise eine Funktion haben welche Personen ihren Besitz zuordnet,
beispielsweise \<^term_type>\<open>besitz :: 'person \<Rightarrow> int\<close>,
so soll die swap Funktion es erlauben, den Besitz von zwei Personen \<^term_type>\<open>p1::'person\<close> und
\<^term_type>\<open>p2::'person\<close> zu vertauschen.
So soll \<^term>\<open>swap (p1::'person) (p2::'person) (besitz :: 'person \<Rightarrow> int)\<close>
die \<^term>\<open>besitz :: 'person \<Rightarrow> int\<close> Funktion zurückgeben,
allerdings mit dem Besitz von \<^term>\<open>p1::'person\<close> und \<^term>\<open>p2::'person\<close> vertauscht.
\<close>

(*
Initially, I introduced my own swap implementation as `swap a b f = f(a:=f b, b:= f a)`.
But then I found that Isabelle/HOL already provides this implementation.
*)

definition swap :: \<open>'a \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b\<close> where
  \<open>swap a b f \<equiv> Fun.swap a b f\<close>

beispiel \<open>swap a b f = f(a:=f b, b:= f a)\<close>
  by (simp add: Fun.swap_def swap_def)

lemma swap1[simp]: \<open>swap a b (swap a b f) = f\<close>
  by (simp add: swap_def swap_nilpotent)
lemma swap2[simp]: \<open>swap b a (swap a b f) = f\<close>
  by (simp add: swap_def swap_nilpotent transpose_commute)

beispiel \<open>(swap p1 p2 swap) p1 p2 x = x\<close> (*wow, types*)
  by(simp add: swap_def)
beispiel \<open>(swap p2 p1 swap) p1 p2 x = x\<close> (*wow, types*)
  by(simp add: swap_def)

lemma swap_id[simp]: \<open>swap a a f = f\<close>
  by(simp add: swap_def)

beispiel \<open>f_swapped = (swap a b f) \<Longrightarrow> f_swapped a = f b \<and> f_swapped b = f a\<close>
  by(simp add: swap_def)

(*TODO rename*)
lemma swap_symmetric: \<open>swap a b = swap b a\<close>
  unfolding swap_def
  by (simp add: swap_commute)
lemma map_swap_none: \<open>a \<notin> set P \<Longrightarrow> b \<notin> set P \<Longrightarrow> map (swap a b f) P = map f P\<close>
  by (simp add: swap_def Fun.swap_def)

lemma map_swap_one: \<open>a \<notin> set P \<Longrightarrow>  map (swap a b f) P = map (f(b:=f a)) P\<close>
  by(simp add: swap_def Fun.swap_def)

lemma swap_a: \<open>swap a b f a = f b\<close>
  by(simp add: swap_def)
lemma swap_b: \<open>swap a b f b = f a\<close>
  by(simp add: swap_def)

lemma sum_swap_none: \<open>a \<notin> P \<Longrightarrow> b \<notin> P \<Longrightarrow> sum (swap a b f) P = sum f P\<close>
  apply(rule sum.cong, simp)
  apply(simp add: swap_def Fun.swap_def)
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
  apply(simp add: swap_def)
  by (metis transpose_involutory)

(*
whenever a prove can be solved by (metis swap_a swap_b swap_nothing)
maybe by(rule swap_cases, simp_all add: swap_a swap_b swap_nothing)
can be faster
*)
lemma swap_cases:
  \<open>(p = p1 \<Longrightarrow> P (f p2)) \<Longrightarrow> (p = p2 \<Longrightarrow> P (f p1)) \<Longrightarrow> (p \<noteq> p1 \<Longrightarrow> p \<noteq> p2 \<Longrightarrow> P (f p))\<Longrightarrow> P (swap p1 p2 f p)\<close>
apply(case_tac \<open>p=p1\<close>, simp add: swap_a)
apply(case_tac \<open>p=p2\<close>, simp add: swap_b)
apply(simp add: swap_nothing)
done

lemma swap_in_set_of_functions:
  \<open>swap p2 p1 x \<in> A \<longleftrightarrow> x \<in> swap p1 p2 ` A\<close>
  using image_iff by fastforce

lemma swap_image: \<open>p1 \<in> A \<Longrightarrow> p2 \<in> A \<Longrightarrow> swap p1 p2 f ` A = f ` A\<close>
  apply(simp add: image_def)
  apply(rule Collect_cong)
  by (metis swap_a swap_b swap_nothing)

lemma swap_id_eq_simp: \<open>swap p1 p2 id a = swap p1 p2 id b \<longleftrightarrow> a = b\<close>
  by (metis id_apply swap_a swap_nothing swap_symmetric)

lemma swap_id_in_set:
  \<open>swap p2 p1 id x \<in> swap p1 p2 id ` A \<longleftrightarrow> x \<in> A\<close>
  apply(simp add: image_iff)
  by (simp add: swap_id_eq_simp swap_symmetric) 

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
   apply(simp; fail)
  apply(rule arg_cong[where f=\<open>Min\<close>])
  apply(simp add: swap_image)
  done

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



lemma swap_fun_swap_id: \<open>swap p1 p2 konsens (swap p1 p2 id p) = konsens p\<close>
  apply(cases \<open>p=p1\<close>)
   apply(simp add: swap_a swap_b)
  apply(cases \<open>p=p2\<close>)
   apply(simp add: swap_a swap_b)
  by(simp add: swap_nothing)


(*TODO: baut swap eine Permutation und gibt es darauf lemmata?
TODO: HOL-Combinatorics.Permutations
*)
lemma \<open>distinct [p1,p2,p3,p4] \<Longrightarrow> swap p1 p2 (swap p3 p4 welt) = swap p3 p4 (swap p1 p2 welt)\<close>
  by(auto simp add: swap_def Fun.swap_def)

lemma swap_comm: \<open>p1 \<noteq> p3 \<Longrightarrow> p1 \<noteq> p4 \<Longrightarrow> p2 \<noteq> p3 \<Longrightarrow> p2 \<noteq> p4 \<Longrightarrow>
  swap p1 p2 (swap p3 p4 welt) = swap p3 p4 (swap p1 p2 welt)\<close>
  by(auto simp add: swap_def Fun.swap_def)

lemma swap_unrelated_im_kreis:
  \<open>p \<noteq> p1 \<Longrightarrow> p \<noteq> p2 \<Longrightarrow>
    swap p2 p (swap p1 p2 (swap p p1 (swap p1 p2 welt))) = welt\<close>
  by(simp add: swap_def Fun.swap_def)

end
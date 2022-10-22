theory Helper
imports Main
begin

section\<open>Hillfslemmata\<close>


thm sum_list_map_eq_sum_count
lemma helper_sum_int_if: "a \<notin> set P \<Longrightarrow>
(\<Sum>x\<in>set P. int (if a = x then A1 x else A2 x) * B x) =
  (\<Sum>x\<in>set P. int (A2 x) * B x)"
  by (smt (verit, del_insts) sum.cong)
lemma sum_list_map_eq_sum_count_int:
  fixes f :: "'a \<Rightarrow> int"
  shows "sum_list (map f xs) = sum (\<lambda>x. (int (count_list xs x)) * f x) (set xs)"
proof(induction xs)
  case (Cons x xs)
  show ?case (is "?l = ?r")
  proof cases
    assume "x \<in> set xs"
    have XXX: "(\<Sum>xa\<in>set xs - {x}. int (if x = xa then count_list xs xa + 1 else count_list xs xa) * f xa)
  = (\<Sum>xa\<in>set xs - {x}. int (count_list xs xa) * f xa)"
      thm helper_sum_int_if
      by (smt (verit, ccfv_SIG) Diff_insert_absorb \<open>x \<in> set xs\<close> mk_disjoint_insert sum.cong) 
    have "?l = f x + (\<Sum>x\<in>set xs. (int (count_list xs x)) * f x)" by (simp add: Cons.IH)
    also have "set xs = insert x (set xs - {x})" using \<open>x \<in> set xs\<close>by blast
    also have "f x + (\<Sum>x\<in>insert x (set xs - {x}). (int (count_list xs x)) * f x) = ?r"
      apply(simp add: sum.insert_remove XXX)
      by (simp add: mult.commute ring_class.ring_distribs(1))
    finally show ?thesis .
  next
    assume "x \<notin> set xs"
    hence "\<And>xa. xa \<in> set xs \<Longrightarrow> x \<noteq> xa" by blast
    thus ?thesis by (simp add: Cons.IH \<open>x \<notin> set xs\<close>)
  qed
qed simp
  
lemma count_list_distinct: "distinct P \<Longrightarrow> x \<in> set P \<Longrightarrow> count_list P x = 1"
  apply(induction P)
   apply(simp; fail)
  by(auto)


end
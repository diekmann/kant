theory Helper
imports Main
begin

section\<open>Hilfslemmata\<close>


lemma helper_sum_int_if: \<open>a \<notin> set P \<Longrightarrow>
(\<Sum>x\<in>set P. int (if a = x then A1 x else A2 x) * B x) =
  (\<Sum>x\<in>set P. int (A2 x) * B x)\<close>
  apply(rule sum.cong, simp)
  by fastforce

lemma sum_list_map_eq_sum_count_int:
  fixes f :: \<open>'a \<Rightarrow> int\<close>
  shows \<open>sum_list (map f xs) = sum (\<lambda>x. (int (count_list xs x)) * f x) (set xs)\<close>
proof(induction \<open>xs\<close>)
  case (Cons x xs)
  show \<open>?case\<close> (is \<open>?l = ?r\<close>)
  proof cases
    assume \<open>x \<in> set xs\<close>
    have XXX: \<open>(\<Sum>xa\<in>set xs - {x}. int (if x = xa then count_list xs xa + 1 else count_list xs xa) * f xa)
  = (\<Sum>xa\<in>set xs - {x}. int (count_list xs xa) * f xa)\<close>
      thm helper_sum_int_if
      apply(rule sum.cong, simp)
      by auto
    have \<open>?l = f x + (\<Sum>x\<in>set xs. (int (count_list xs x)) * f x)\<close> by (simp add: Cons.IH)
    also have \<open>set xs = insert x (set xs - {x})\<close> using \<open>x \<in> set xs\<close>by blast
    also have \<open>f x + (\<Sum>x\<in>insert x (set xs - {x}). (int (count_list xs x)) * f x) = ?r\<close>
      apply(simp add: sum.insert_remove XXX)
      by (simp add: mult.commute ring_class.ring_distribs(1))
    finally show \<open>?thesis\<close> .
  next
    assume \<open>x \<notin> set xs\<close>
    hence \<open>\<And>xa. xa \<in> set xs \<Longrightarrow> x \<noteq> xa\<close> by blast
    thus \<open>?thesis\<close> by (simp add: Cons.IH \<open>x \<notin> set xs\<close>)
  qed
qed simp

lemma count_list_distinct: \<open>distinct P \<Longrightarrow> x \<in> set P \<Longrightarrow> count_list P x = 1\<close>
  apply(induction \<open>P\<close>)
   apply(simp; fail)
  by(auto)



text\<open>For some reason, I like \<^const>\<open>List.map_filter\<close>. But standard library support is poor.\<close>
lemma List_map_filter_as_comprehension:
  "List.map_filter f xs = [the (f x). x \<leftarrow> xs, f x \<noteq> None]"
  by(induction xs) (simp add: List.map_filter_def)+
lemma List_map_filter_as_foldr:
  "List.map_filter f xs = foldr (\<lambda>x acc. case f x of Some a \<Rightarrow> a#acc | None \<Rightarrow> acc) xs []"
  apply(induction xs)
  apply(simp add: List.map_filter_def)
  apply(simp add: List.map_filter_def)
  apply(safe, simp)
  done

end
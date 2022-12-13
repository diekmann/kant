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


lemma is_singleton_the_elem_as_set: "is_singleton A \<Longrightarrow> the_elem A = a \<longleftrightarrow> A = {a}"
  apply(rule iffI)
   apply (simp add: is_singleton_the_elem)
  apply(simp add: the_elem_def)
  done

(*the simplifier loops with this one, sometimes. If it loops, apply(elim is_singletonE) first.*)
lemma singleton_set_to_all: "{a \<in> A. P a} = {b} \<longleftrightarrow> (\<forall>a. (a \<in> A \<and> P a) = (a = b))"
  by fastforce

lemma singleton_set_to_all2: "A = {b} \<longleftrightarrow> (\<forall>a. (a \<in> A) = (a = b))"
  by fastforce



text\<open>For some reason, I like \<^const>\<open>List.map_filter\<close>. But standard library support is poor.\<close>
lemma List_map_filter_as_comprehension:
  \<open>List.map_filter f xs = [the (f x). x \<leftarrow> xs, f x \<noteq> None]\<close>
  by(induction \<open>xs\<close>) (simp add: List.map_filter_def)+
lemma List_map_filter_as_foldr:
  \<open>List.map_filter f xs = foldr (\<lambda>x acc. case f x of Some a \<Rightarrow> a#acc | None \<Rightarrow> acc) xs []\<close>
  apply(induction \<open>xs\<close>)
  apply(simp add: List.map_filter_def)
  apply(simp add: List.map_filter_def)
  apply(safe, simp)
  done




lemma concat_map_if: "concat (map (\<lambda>x. if P x then [x] else []) xs) = filter P xs"
  by(induction xs) auto


lemma fold_fun_update_call_helper:
  \<open>p \<notin> set xs \<Longrightarrow> fold (\<lambda>x acc. acc(x := f x)) xs start p = start p\<close>
  by(induction \<open>xs\<close> arbitrary: \<open>start\<close>) simp+

lemma fold_fun_update_call:
  \<open>p \<in> set xs \<Longrightarrow> distinct xs \<Longrightarrow> fold (\<lambda>x acc. acc(x := f x)) xs start p = f p\<close>
  apply(induction \<open>xs\<close> arbitrary: \<open>start\<close>)
   apply(simp; fail)
  apply(simp)
  apply(safe)
   apply(simp add: fold_fun_update_call_helper; fail)
  apply(simp)
  done

lemma fold_enum_fun_update_call:
  \<open>fold (\<lambda>x acc. acc(x := f x)) Enum.enum start p = f p\<close>
  apply(rule fold_fun_update_call)
   apply(simp add: enum_class.enum_UNIV)
  apply(simp add: enum_class.enum_distinct)
  done

lemma fold_enum_fun_update:
  \<open>fold (\<lambda>x acc. acc(x := f x)) Enum.enum start = f\<close>
  using fold_enum_fun_update_call by auto  
end
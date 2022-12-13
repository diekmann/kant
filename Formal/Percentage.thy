theory Percentage
  imports HOL.Real
begin

section\<open>Implementation Detail: Percentage Type\<close>

(*thx pruvisto!*)
typedef percentage = \<open>{0..(1::real)}\<close>
  morphisms real_of_percentage Abs_percentage
  by auto

setup_lifting type_definition_percentage

instantiation percentage :: \<open>zero\<close>
begin
  lift_definition zero_percentage :: \<open>percentage\<close> is \<open>0 :: real\<close>
    by auto
  instance ..
end

instantiation percentage :: \<open>monoid_mult\<close>
begin
  lift_definition one_percentage :: \<open>percentage\<close> is \<open>1 :: real\<close>
    by auto

  lift_definition times_percentage :: \<open>percentage \<Rightarrow> percentage \<Rightarrow> percentage\<close> is \<open>(*) :: real \<Rightarrow> _\<close>
    by (auto simp: mult_le_one)

  instance
    by standard (transfer; simp; fail)+
end


text\<open>A \<^term>\<open>Abs_percentage 0.1\<close> would give a "Abstraction violation" in a value command.
So here is some magic to make code work.\<close>
definition percentage :: \<open>real \<Rightarrow> percentage\<close> where
  \<open>percentage p \<equiv> if p \<le> 0 then 0 else if p \<ge> 1 then 1 else Abs_percentage p\<close>

lemma percentage_code [code abstract]:
  \<open>real_of_percentage (percentage p) = (if p \<le> 0 then 0 else if p \<ge> 1 then 1 else p)\<close>
  unfolding percentage_def
  by (simp add: Abs_percentage_inverse one_percentage.rep_eq zero_percentage.rep_eq)

value[code] \<open>percentage 0.1\<close> (*no longer an error*)
lemma \<open>real_of_percentage (percentage 0.1) * (25::real) = 2.5\<close> by eval
lemma \<open>(25::real) * real_of_percentage (percentage 0.1) = 2.5\<close> by eval

text\<open>And now we get rid of explicit calls to \<^const>\<open>real_of_percentage\<close>\<close>
declare [[coercion \<open>real_of_percentage :: percentage \<Rightarrow> real\<close>]]

lemma \<open>(percentage 0.1) * (25::real) = 2.5\<close> by eval
lemma \<open>(25::real) * (percentage 0.1) = 2.5\<close> by eval
lemma \<open>(percentage 0.1) * (25::nat) = 2.5\<close> by eval
lemma \<open>(25::nat) * (percentage 0.1) = 2.5\<close> by eval


lemma percentage_range:
  fixes p :: \<open>percentage\<close>
  shows \<open>0 \<le> p \<and> p \<le> 1\<close>
  using real_of_percentage by auto

lemma real_of_percentage_range:
  \<open>0 \<le> real_of_percentage p\<close>
  \<open>real_of_percentage p \<le> 1\<close>
  by(simp add: percentage_range)+

(*will cause simplifier looping*)
lemma percentage_min_max_simps:
    \<open>real_of_percentage p = min 1 p\<close>
    \<open>real_of_percentage p = max 0 p\<close>
  by (simp add: percentage_range)+

lemma real_of_percentage_mult:
  \<open>real a * real_of_percentage p \<le> a\<close>
  \<open>real_of_percentage p * real a \<le> a\<close>
  by (simp add: mult.commute mult_left_le percentage_range)+

lemma percentage_percentage_mult_right:
  fixes a p ::\<open>percentage\<close>
  shows \<open>a * p \<le> a\<close>
  by (simp add: mult_right_le_one_le real_of_percentage_range times_percentage.rep_eq)
lemma percentage_percentage_mult_left:
  fixes a p ::\<open>percentage\<close>
  shows \<open>p * a \<le> a\<close>
  by (simp add: mult.commute percentage_percentage_mult_right mult_right_le_one_le percentage_range times_percentage.rep_eq)

lemma percentage_real_pos_mult_right:
  \<open>a \<ge> 0 \<Longrightarrow> a * real_of_percentage p \<le> a\<close>
  by (simp add: mult_left_le percentage_range)

lemma percentage_real_pos_mult_left:
  \<open>a \<ge> 0 \<Longrightarrow> real_of_percentage p * a \<le> a\<close>
  by (simp add: mult_left_le_one_le percentage_range)

lemma percentage_mult_right_mono:
  fixes a b p :: \<open>percentage\<close>
  shows \<open>a \<le> b \<Longrightarrow> a * p \<le> b * p\<close>
  by transfer (simp add: mult_right_mono)

lemma percentage_real_mult_right_mono:
  fixes p :: \<open>percentage\<close> and a b :: \<open>real\<close>
  shows \<open>a \<le> b \<Longrightarrow> a * p \<le> b * p\<close>
  by transfer (simp add: mult_right_mono)

lemma percentage_real_diff_mult_right_mono:
  \<open>a \<le> b \<Longrightarrow> a - a * (real_of_percentage p) \<le> b - b * (real_of_percentage p)\<close>
proof -
  assume a: \<open>a \<le> b\<close>
  have \<open>0 \<le> b - a\<close> by (simp add: a)
  hence \<open>(b - a) * real_of_percentage p \<le> b - a\<close>
    by (simp add: percentage_real_pos_mult_right)
  with a show \<open>?thesis\<close>
    by (simp add: a left_diff_distrib')
qed

lemma percentage_nat_diff_mult_right_mono: (*warning: coertion*)
  fixes p :: \<open>percentage\<close> and a b :: \<open>nat\<close>
  shows \<open>(a :: nat) \<le> b \<Longrightarrow> a - a * p \<le> b - b * p\<close>
  by (simp add: percentage_real_diff_mult_right_mono)

  
lemma percentage_add_limit_helper:
  "a \<ge> 0 \<Longrightarrow> b \<le> c - a \<Longrightarrow> a * real_of_percentage prozent + b \<le> c"
by (metis add.commute le_diff_eq order_trans percentage_real_pos_mult_right) 
end
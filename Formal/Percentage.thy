theory Percentage
  imports HOL.Real
begin

section\<open>Implementation Detail: Percentage Type\<close>

(*thx pruvisto!*)
typedef percentage = "{0..(1::real)}"
  morphisms real_of_percentage Abs_percentage
  by auto

setup_lifting type_definition_percentage

instantiation percentage :: zero
begin
  lift_definition zero_percentage :: percentage is "0 :: real"
    by auto
  instance ..
end

instantiation percentage :: monoid_mult
begin
  lift_definition one_percentage :: percentage is "1 :: real"
    by auto
  
  lift_definition times_percentage :: "percentage \<Rightarrow> percentage \<Rightarrow> percentage" is "(*) :: real \<Rightarrow> _"
    by (auto simp: mult_le_one)
  
  instance
    by standard (transfer; simp; fail)+
end


text\<open>A \<^term>\<open>Abs_percentage 0.1\<close> would give a "Abstraction violation" in a value command.
So here is some magic to make code work.\<close>
definition percentage :: "real \<Rightarrow> percentage" where
  "percentage p \<equiv> if p \<le> 0 then 0 else if p \<ge> 1 then 1 else Abs_percentage p"

lemma percentage_code [code abstract]:
  "real_of_percentage (percentage p) = (if p \<le> 0 then 0 else if p \<ge> 1 then 1 else p)"
  unfolding percentage_def
  by (simp add: Abs_percentage_inverse one_percentage.rep_eq zero_percentage.rep_eq)

value[code] "percentage 0.1" (*no longer an error*)
lemma "real_of_percentage (percentage 0.1) * (25::real) = 2.5" by eval
lemma "(25::real) * real_of_percentage (percentage 0.1) = 2.5" by eval

text\<open>And now we get rid of explicit calls to \<^const>\<open>real_of_percentage\<close>\<close>
declare [[coercion "real_of_percentage :: percentage \<Rightarrow> real"]]

lemma "(percentage 0.1) * (25::real) = 2.5" by eval
lemma "(25::real) * (percentage 0.1) = 2.5" by eval
lemma "(percentage 0.1) * (25::nat) = 2.5" by eval
lemma "(25::nat) * (percentage 0.1) = 2.5" by eval


lemma percentage_range:
  fixes p :: percentage
  shows "0 \<le> p \<and> p \<le> 1"
  using real_of_percentage by auto

lemma real_of_percentage_range:
  "0 \<le> real_of_percentage p"
  "real_of_percentage p \<le> 1"
  by(simp add: percentage_range)+

(*will cause simplifier looping*)
lemma percentage_min_max_simps:
    "real_of_percentage p = min 1 p"
    "real_of_percentage p = max 0 p"
  by (simp add: percentage_range)+

lemma real_of_percentage_mult:
  "real a * real_of_percentage p \<le> a"
  "real_of_percentage p * real a \<le> a"
  by (simp add: mult.commute mult_left_le percentage_range)+

lemma percentage_percentage_mult_right:
  fixes a p ::percentage
  shows "a * p \<le> a"
  by (simp add: mult_right_le_one_le real_of_percentage_range times_percentage.rep_eq)
lemma percentage_percentage_mult_left:
  fixes a p ::percentage
  shows "p * a \<le> a"
  by (simp add: mult.commute percentage_percentage_mult_right mult_right_le_one_le percentage_range times_percentage.rep_eq)
lemma percentage_real_pos_mult_right:
  fixes p::percentage and a :: real
  shows "a \<ge> 0 \<Longrightarrow> a * (real_of_percentage p) \<le> a"
  by (simp add: mult_left_le percentage_range)
lemma percentage_real_pos_mult_left:
  fixes p::percentage and a :: real
  shows "a \<ge> 0 \<Longrightarrow> (real_of_percentage p) * a \<le> a"
  by (simp add: mult_left_le_one_le percentage_range)

lemma percentage_mult_right_mono:
  fixes a b p ::percentage
  shows "a \<le> b \<Longrightarrow> a * p \<le> b * p"
proof -
  show "a \<le> b \<Longrightarrow> ?thesis"
    by (simp add: mult_right_mono real_of_percentage_range(1) times_percentage.rep_eq)
qed

lemma percentage_real_mult_right_mono:
  fixes p ::percentage and a b :: real
  shows "a \<le> b \<Longrightarrow> a * p \<le> b * p"
proof -
  show "a \<le> b \<Longrightarrow> ?thesis"
    by (simp add: mult_right_mono real_of_percentage_range(1) times_percentage.rep_eq)
qed

lemma percentage_real_diff_mult_right_mono:
  fixes p::percentage and a b :: real
  shows "a \<le> b \<Longrightarrow> a - a * (real_of_percentage p) \<le> b - b * (real_of_percentage p)"
proof -
  assume a: "a \<le> b"
  have "0 \<le> b - a" by (simp add: a)
  hence "(b - a) * real_of_percentage p \<le> b - a"
    by (simp add: percentage_real_pos_mult_right)
  with a show ?thesis
    by (simp add: a left_diff_distrib')
qed

lemma percentage_nat_diff_mult_right_mono: (*warning: coertion*)
  fixes p::percentage
    and a b :: nat
  shows "a \<le> b \<Longrightarrow> a - a * p \<le> b - b * p"
  by (simp add: percentage_real_diff_mult_right_mono)

end
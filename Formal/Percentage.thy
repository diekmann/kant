theory Percentage
  imports HOL.Real
begin

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

end
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

lemma real_of_percentage_mult:
  "real a * real_of_percentage p \<le> a"
  "real_of_percentage p * real a \<le> a"
  by (simp add: mult.commute mult_left_le percentage_range)+

lemma percentage_mult_right_mono: fixes p::percentage
      shows "a \<le> b \<Longrightarrow> a * p \<le>  b * p"
proof -
  show "a \<le> b \<Longrightarrow> ?thesis"
    by (simp add: mult_right_mono real_of_percentage_range(1) times_percentage.rep_eq)
qed

lemma percentage_nat_diff_mult_right_mono: fixes p::percentage
        and a b :: nat
      shows "a \<le> b \<Longrightarrow> a - a * p \<le> b - b * p"
proof -
  (*Why and how does this work?*)
  have XXX: "a \<le> b \<Longrightarrow> min (real b) a = a" by simp
  from percentage_mult_right_mono show "a \<le> b \<Longrightarrow> ?thesis"
    by (metis diff_ge_0_iff_ge mult.right_neutral mult_right_mono
        of_nat_le_iff percentage_range right_diff_distrib')

qed

(*      assume \<open>e1 \<le> zone\<close>
      have e1: "min (real zone) e1 = e1" using True by simp
      have e1zonediff:
       "e1 - e1 * prozent \<le> zone - zone * prozent"
        by (metis (no_types, opaque_lifting) diff_ge_0_iff_ge e1 min.bounded_iff
            mult.right_neutral mult_right_mono nle_le percentage_range
            right_diff_distrib')*)

(* assume \<open>e1 \<le> zone\<close>
      have e1: "min (real zone) e1 = e1" using True by simp
      have e1zonediff:
       "e1 - e1 * prozent \<le> zone - zone * prozent"*)
end
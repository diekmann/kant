theory Xor
  imports Main
begin

section\<open>XOR\<close>
text\<open>Entweder Oder\<close>
definition xor :: "bool \<Rightarrow> bool \<Rightarrow> bool" (infixr "\<oplus>" 59) where
  "a \<oplus> b \<equiv> \<not> (a \<longleftrightarrow> b)"

lemma "(a \<oplus> b) = (\<not> (a \<longleftrightarrow> b))" by(simp add: xor_def)
lemma xor2: "(a \<oplus> b) = ((a \<and> \<not>b) \<or> (\<not>a \<and> b))" by(auto simp add: xor_def)
lemma xor3: "(a \<oplus> b) = (a \<noteq> b)" by(auto simp add: xor_def)
lemma xor4: "(a \<oplus> b) = (a = (\<not>b))" by(auto simp add: xor_def)
lemma xor5: "(a \<oplus> b) = ((a \<or> b) \<and> \<not>(a \<and> b))" by(auto simp add: xor_def)

text\<open>Entweder-Oder ist stärker als nur Oder:\<close>
lemma xor_imp_or: "a \<oplus> b \<Longrightarrow> a \<or> b"
  by(simp add: xor5)

end
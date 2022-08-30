theory BeispielPerson
imports Main
begin

section\<open>Beispiel Person\<close>
text\<open>Eine Beispielbevölkerung.
Wir müssen \<^class>\<open>enum\<close> implementieren, damit wür über alle persosn iterieren können.
\<close>

datatype person = Alice | Bob | Carol | Eve

lemma UNIV_person: "UNIV = {Alice, Bob, Carol, Eve}"
  by(auto intro:person.exhaust UNIV_eq_I)

instantiation person :: enum
begin
  definition "enum_person \<equiv> [Alice, Bob, Carol, Eve]"
  definition "enum_all_person P \<longleftrightarrow> P Alice \<and> P Bob \<and> P Carol \<and> P Eve"
  definition "enum_ex_person P \<longleftrightarrow> P Alice \<or> P Bob \<or> P Carol \<or> P Eve"

instance proof
  qed (simp_all only: enum_person_def enum_all_person_def enum_ex_person_def UNIV_person, simp_all)
end

end
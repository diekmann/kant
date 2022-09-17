theory BeispielPerson
imports Main
begin

section\<open>Beispiel Person\<close>
text\<open>Eine Beispielbevölkerung.
Wir müssen \<^class>\<open>enum\<close> implementieren, damit wür über alle persosn iterieren können.
\<close>

datatype person = Alice | Bob | Carol | Eve

lemma UNIV_person: \<open>UNIV = {Alice, Bob, Carol, Eve}\<close>
  by(auto intro:person.exhaust UNIV_eq_I)

instantiation person :: \<open>enum\<close>
begin
  definition \<open>enum_person \<equiv> [Alice, Bob, Carol, Eve]\<close>
  definition \<open>enum_all_person P \<longleftrightarrow> P Alice \<and> P Bob \<and> P Carol \<and> P Eve\<close>
  definition \<open>enum_ex_person P \<longleftrightarrow> P Alice \<or> P Bob \<or> P Carol \<or> P Eve\<close>

instance proof
  qed (simp_all only: enum_person_def enum_all_person_def enum_ex_person_def UNIV_person, simp_all)
end

text\<open>Also makes maps partially executable.\<close>
lemma \<open>dom [Alice \<mapsto> (3::nat), Carol \<mapsto> 6] = {Alice, Carol}\<close> by eval

(*TODO: use https://www.isa-afp.org/entries/Generic_Deriving.html to get a linorder?
value "sorted_list_of_set {Alice, Carol}"
*)

end
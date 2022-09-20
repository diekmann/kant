theory BeispielPerson
imports Main
begin

section\<open>Beispiel Person\<close>
text\<open>Eine Beispielbevölkerung.\<close>

datatype person = Alice | Bob | Carol | Eve

text\<open>Unsere Bevölkerung ist sehr endlich:\<close>
lemma UNIV_person: \<open>UNIV = {Alice, Bob, Carol, Eve}\<close>
  by(auto intro:person.exhaust UNIV_eq_I)

text\<open>Wir werden unterscheiden:
  \<^item> \<^typ>\<open>'person\<close>: generischer Typ, erlaub es jedes Modell einer Person und Bevölkerung zu haben.
  \<^item> \<^typ>\<open>person\<close>: Unser minimaler Beispielstyp, bestehend aus \<^const>\<open>Alice\<close>, \<^const>\<open>Bob\<close>, ...
\<close>

(*<*)
text\<open>
Technisch müssen wir \<^class>\<open>enum\<close> implementieren, damit wir über alle Personen iterieren können.
Ansonsten würden nur Beweise funktionieren, aber keine ausführbaren Beispiele.
\<close>
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
(*>*)

end
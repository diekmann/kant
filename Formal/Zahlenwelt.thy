theory Zahlenwelt
imports Simulation
begin

datatype person = Alice | Bob | Carol | Eve

lemma UNIV_person: "UNIV = {Alice, Bob, Carol, Eve}"
  by(auto intro:person.exhaust UNIV_eq_I)

text\<open>Wenn die Welt sich durch eine Zahl darstellen lässt, ...\<close>
datatype zahlenwelt = Zahlenwelt
        nat \<comment>\<open>verbleibend: Ressourcen sind endlich. Verbleibende Ressourcen in der Welt.\<close>
        "person \<Rightarrow> int option" \<comment>\<open>besitz: Besitz jeder Person.\<close>

fun gesamtbesitz :: "zahlenwelt \<Rightarrow> int" where
  "gesamtbesitz (Zahlenwelt _ besitz) = sum_list (List.map_filter besitz [Alice, Bob, Carol, Eve])"

lemma "gesamtbesitz (Zahlenwelt 42 [Alice \<mapsto> 4, Carol \<mapsto> 8]) = 12" by eval
lemma "gesamtbesitz (Zahlenwelt 42 [Alice \<mapsto> 4, Carol \<mapsto> 4]) = 8" by eval

fun abbauen :: "nat \<Rightarrow> person \<Rightarrow> zahlenwelt \<Rightarrow> zahlenwelt" where
  "abbauen i p (Zahlenwelt verbleibend besitz) =
    Zahlenwelt
      (verbleibend - i)
      (case besitz p
        of None \<Rightarrow> besitz(p \<mapsto> int i)
         | Some b \<Rightarrow> besitz(p \<mapsto> b + int i))"

text\<open>
Mehr ist mehr gut.
Globaler Fortschritt erlaubt stehlen, solange dabei nichts vernichtet wird.


Groesser (>) anstelle (\<ge>) ist hier echt spannend!
Es sagt, dass wir nicht handeln duerfen, wenn andere nicht die möglichkeit haben!!
Das \<ge> ist kein strenger Fortschritt, eher kein Rueckschritt.
\<close>
fun globaler_fortschritt :: "zahlenwelt handlung \<Rightarrow> bool" where
  "globaler_fortschritt (Handlung vor nach) \<longleftrightarrow> (gesamtbesitz nach) \<ge> (gesamtbesitz vor)"

text\<open>Dieser globale Fortschritt sollte eigentlich allgemeines Gesetz werden und die
Maxime sollte individuelle Bereicherung sein (und die unsichtbare Hand macht den Rest. YOLO).\<close>


end
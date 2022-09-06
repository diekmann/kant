theory Zahlenwelt
imports Simulation Gesetze BeispielPerson
begin

section\<open>Beispiel: Zahlenwelt\<close>

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


Größer (>) anstelle (>=) ist hier echt spannend!
Es sagt, dass wir nicht handeln duerfen, wenn andere nicht die Möglichkeit haben!!
Das >= ist kein strenger Fortschritt, eher kein Rückschritt.
\<close>
fun globaler_fortschritt :: "zahlenwelt handlung \<Rightarrow> bool" where
  "globaler_fortschritt (Handlung vor nach) \<longleftrightarrow> (gesamtbesitz nach) \<ge> (gesamtbesitz vor)"

text\<open>Dieser globale Fortschritt sollte eigentlich allgemeines Gesetz werden und die
Maxime sollte individuelle Bereicherung sein (und die unsichtbare Hand macht den Rest. YOLO).\<close>


fun meins :: "person \<Rightarrow> zahlenwelt \<Rightarrow> int" where
  "meins p (Zahlenwelt verbleibend besitz) = the_default (besitz p) 0"

fun individueller_fortschritt :: "person \<Rightarrow> zahlenwelt handlung \<Rightarrow> bool" where
  "individueller_fortschritt p (Handlung vor nach) \<longleftrightarrow> (meins p nach) \<ge> (meins p vor)"

(*TODO: Eigentlich wollen wir Fortschritt in ALLEN möglichen Welten.*)

definition maxime_zahlenfortschritt :: "(person, zahlenwelt) maxime" where
  "maxime_zahlenfortschritt \<equiv> Maxime (\<lambda>ich. individueller_fortschritt ich)"
(*Interessant: hard-coded Alice anstelle von 'ich'.*)

definition "sc \<equiv> SimConsts
    Alice
    maxime_zahlenfortschritt
    (\<lambda>h. case_law_ableiten (map_handlung
          (\<lambda>w. case w of Zahlenwelt verbleibend besitz \<Rightarrow> (verbleibend, show_map besitz))
            h))" (*make printable*)
definition "initialwelt \<equiv> Zahlenwelt 42 [Alice \<mapsto> 5, Bob \<mapsto> 10]"

definition "beispiel_case_law h \<equiv> simulateOne sc 20 h initialwelt (Gesetz {})"

value \<open>beispiel_case_law (HandlungF (abbauen 5))\<close>
end
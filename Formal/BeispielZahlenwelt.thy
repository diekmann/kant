theory BeispielZahlenwelt
imports Simulation Gesetze BeispielPerson
begin

section\<open>Beispiel: Zahlenwelt\<close>

text\<open>Wenn die Welt sich durch eine Zahl darstellen lässt, ...\<close>
datatype zahlenwelt = Zahlenwelt
        "person \<Rightarrow> int option" \<comment> \<open>besitz: Besitz jeder Person.\<close>

fun gesamtbesitz :: "zahlenwelt \<Rightarrow> int" where
  "gesamtbesitz (Zahlenwelt besitz) = sum_list (List.map_filter besitz [Alice, Bob, Carol, Eve])"

lemma "gesamtbesitz (Zahlenwelt [Alice \<mapsto> 4, Carol \<mapsto> 8]) = 12" by eval
lemma "gesamtbesitz (Zahlenwelt [Alice \<mapsto> 4, Carol \<mapsto> 4]) = 8" by eval

fun abbauen :: "nat \<Rightarrow> person \<Rightarrow> zahlenwelt \<Rightarrow> zahlenwelt" where
  "abbauen i p (Zahlenwelt besitz) =
    Zahlenwelt
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
  "meins p (Zahlenwelt besitz) = the_default (besitz p) 0"

fun individueller_fortschritt :: "person \<Rightarrow> zahlenwelt handlung \<Rightarrow> bool" where
  "individueller_fortschritt p (Handlung vor nach) \<longleftrightarrow> (meins p nach) \<ge> (meins p vor)"

(*TODO: Eigentlich wollen wir Fortschritt in ALLEN möglichen Welten.*)

definition maxime_zahlenfortschritt :: "(person, zahlenwelt) maxime" where
  "maxime_zahlenfortschritt \<equiv> Maxime (\<lambda>ich. individueller_fortschritt ich)"
(*Interessant: hard-coded Alice anstelle von 'ich'.*)

fun delta_zahlenwelt :: "(zahlenwelt, person, int) delta" where
  "delta_zahlenwelt (Handlung (Zahlenwelt vor_besitz) (Zahlenwelt nach_besitz)) =
      Aenderung.delta_num_map (Handlung vor_besitz nach_besitz)"

definition "sc \<equiv> SimConsts
    Alice
    maxime_zahlenfortschritt
    (printable_case_law_ableiten_absolut
      (\<lambda>w. case w of Zahlenwelt besitz \<Rightarrow> show_map besitz))"
definition "sc' \<equiv> SimConsts
    Alice
    maxime_zahlenfortschritt
    (case_law_ableiten_relativ delta_zahlenwelt)"

definition "initialwelt \<equiv> Zahlenwelt [Alice \<mapsto> 5, Bob \<mapsto> 10]"

definition "beispiel_case_law h \<equiv> simulateOne sc 10 h initialwelt (Gesetz {})"
definition "beispiel_case_law' h \<equiv> simulateOne sc' 20 h initialwelt (Gesetz {})"

lemma \<open>beispiel_case_law (HandlungF (abbauen 5))
=
Gesetz
  {(Paragraph 10,
    Rechtsnorm (Tatbestand ([(Alice, 50), (Bob, 10)], [(Alice, 55), (Bob, 10)]))
     (Rechtsfolge Erlaubnis)),
   (Paragraph 9,
    Rechtsnorm (Tatbestand ([(Alice, 45), (Bob, 10)], [(Alice, 50), (Bob, 10)]))
     (Rechtsfolge Erlaubnis)),
   (Paragraph 8,
    Rechtsnorm (Tatbestand ([(Alice, 40), (Bob, 10)], [(Alice, 45), (Bob, 10)]))
     (Rechtsfolge Erlaubnis)),
   (Paragraph 7,
    Rechtsnorm (Tatbestand ([(Alice, 35), (Bob, 10)], [(Alice, 40), (Bob, 10)]))
     (Rechtsfolge Erlaubnis)),
   (Paragraph 6,
    Rechtsnorm (Tatbestand ([(Alice, 30), (Bob, 10)], [(Alice, 35), (Bob, 10)]))
     (Rechtsfolge Erlaubnis)),
   (Paragraph 5,
    Rechtsnorm (Tatbestand ([(Alice, 25), (Bob, 10)], [(Alice, 30), (Bob, 10)]))
     (Rechtsfolge Erlaubnis)),
   (Paragraph 4,
    Rechtsnorm (Tatbestand ([(Alice, 20), (Bob, 10)], [(Alice, 25), (Bob, 10)]))
     (Rechtsfolge Erlaubnis)),
   (Paragraph 3,
    Rechtsnorm (Tatbestand ([(Alice, 15), (Bob, 10)], [(Alice, 20), (Bob, 10)]))
     (Rechtsfolge Erlaubnis)),
   (Paragraph 2,
    Rechtsnorm (Tatbestand ([(Alice, 10), (Bob, 10)], [(Alice, 15), (Bob, 10)]))
     (Rechtsfolge Erlaubnis)),
   (Paragraph 1,
    Rechtsnorm (Tatbestand ([(Alice, 5), (Bob, 10)], [(Alice, 10), (Bob, 10)]))
     (Rechtsfolge Erlaubnis))}
\<close> by eval

lemma \<open>beispiel_case_law' (HandlungF (abbauen 5)) =
  Gesetz
  {(Paragraph 1, Rechtsnorm (Tatbestand [Gewinnt Alice 5]) (Rechtsfolge Erlaubnis))}\<close>
  by eval
end
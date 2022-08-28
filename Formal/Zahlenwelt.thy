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

(*Cool, this definition is WRONG if 2 folks have the same besitz -_- *)
fun gesamtbesitz :: "zahlenwelt \<Rightarrow> int" where
  "gesamtbesitz (Zahlenwelt _ besitz) = sum_list (List.map_filter besitz [Alice, Bob, Carol, Eve])"

(*TODO: is there a library function for this?*)
fun the_default :: "'a option \<Rightarrow> 'a \<Rightarrow> 'a" where
  "the_default None def = def"
| "the_default (Some a) _ = a"

code_thms gesamtbesitz

(*TODO: in Gesetz.thy ist prg_set_deconstruct und ich sollte eine generische ExecutableSet helper thy machen.*)
(*iterate over person only*)
lemma XXX: "{b. \<exists>p. (besitz p) = Some b} = {b. Some b \<in> range besitz}"
  by (metis rangeE range_eqI)
lemma map_filter_id: "S = set s \<Longrightarrow> {b. Some b \<in> S} = set (List.map_filter id s)"
  apply(simp add: map_filter_def)
  apply(simp add: image_def)
  apply(rule Collect_cong)
  by auto

value "gesamtbesitz (Zahlenwelt 42 [Alice \<mapsto> 4, Carol \<mapsto> 8])"

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


Groesser (>) anstelle (>=) ist hier echt spannend!
Es sagt, dass wir nicht handeln duerfen, wenn andere nicht die möglichkeit haben!!
Das >= ist kein strenger Fortschritt, eher kein Rueckschritt.
\<close>
fun globaler_fortschritt :: "zahlenwelt handlung \<Rightarrow> Bool" where
  "globaler_fortschritt (H.Handlung vorher nachher) =
    (gesamtbesitz nachher) >= (gesamtbesitz vorher)"
    where gesamtbesitz w = M.foldl' (+) 0 (besitz w)

text\<open>Dieser globale Fortschritt sollte eigentlich allgemeines Gesetz werden und die
Maxime sollte individuelle Bereicherung sein (und die unsichtbare Hand macht den Rest. YOLO).\<close>


end
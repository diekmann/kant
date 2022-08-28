theory Zahlenwelt
imports Simulation
begin

datatype person = Alice | Bob | Carol | Eve

text\<open>Wenn die Welt sich durch eine Zahl darstellen lässt, ...\<close>
datatype zahlenwelt = Zahlenwelt
        nat \<comment>\<open>verbleibend: Ressourcen sind endlich. Verbleibende Ressourcen in der Welt.\<close>
        "person \<Rightarrow> int option" \<comment>\<open>besitz: Besitz jeder Person.\<close>

fun gesamtbesitz :: "zahlenwelt \<Rightarrow> int" where
  "gesamtbesitz (Zahlenwelt _ besitz) = \<Sum> {b. \<exists>p. (besitz p) = Some b}"

(*TODO: is there a library function for this?*)
fun the_default :: "'a option \<Rightarrow> 'a \<Rightarrow> 'a" where
  "the_default None def = def"
| "the_default (Some a) _ = a"

code_thms gesamtbesitz

(*iterate over person only*)
lemma XXX: "{b. \<exists>p. (besitz p) = Some b} = {b. Some b \<in> range besitz}"
  by (metis rangeE range_eqI)
  

thm Collect_code enum_UNIV
term Collect
lemma "{b. \<exists>p. (besitz p) = Some b} = Collect (\<lambda> b. \<exists> p. besitz p = Some b)"
  by simp
lemma "{b. \<exists>p. (besitz p) = Some b} = 
        set (map (the \<circ> besitz) (filter (\<lambda>p. case (besitz p) of Some _ \<Rightarrow> True | _ \<Rightarrow> False) [Alice, Bob, Carol, Eve]))"
  apply(simp)
  oops

lemma [code_unfold]:
  "gesamtbesitz (Zahlenwelt verbleibend besitz) =
    foldl (\<lambda>acc p. acc + (the_default (besitz p) 0)) 0 [Alice, Bob, Carol, Eve]"
proof -
  thm Collect_code enum_UNIV
  have "{b. \<exists>p. (besitz p) = Some b} = Collect (\<lambda> b. \<exists> p. besitz p = Some b)"
    by simp
  
  show ?thesis
    apply(simp)
    apply(simp add: XXX)
  sorry (*TODO!!!!!!!!!!!!!!!!!!!!*)
qed

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
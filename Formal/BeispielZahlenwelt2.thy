theory BeispielZahlenwelt2
imports Zahlenwelt BeispielPerson Aenderung KategorischerImperativ
begin

section\<open>Beispiel: Zahlenwelt2\<close>

text\<open>Konsens laut \<^url>\<open>https://de.wikipedia.org/wiki/Konsens#Konsens_im_Rechtssystem\<close>:
"die Übereinstimmung der Willenserklärungen beider Vertragspartner über die Punkte des Vertrages"\<close>


record zahlenwelt =
  besitz :: \<open>person \<Rightarrow> int\<close>
  konsens :: \<open>person \<Rightarrow> (person, int) aenderung set list\<close> (*TODO: wie modelliere ich das*)
  staatsbesitz :: \<open>int\<close> \<comment>\<open>Der Staat ist keine natürliche Person und damit besonders.\<close>
  umwelt :: \<open>int\<close>

(*\<^url>[Alice := 5, Bob := 10, Carol := -3]*)
definition initialwelt :: zahlenwelt
  where
"initialwelt \<equiv> \<lparr>
  besitz = \<^url>[Alice := 5, Bob := 10, Carol := -3],
  konsens = (\<lambda>_. [])(
    Alice := [{Gewinnt Alice 3}, {Gewinnt Alice 3, Verliert Bob 3}],
    Bob := [{Verliert Bob 3,Gewinnt Alice 3}]),
  staatsbesitz = 9000,
  umwelt = 600
 \<rparr>"

definition hat_konsens :: "zahlenwelt handlung \<Rightarrow> bool"
where
  "hat_konsens h \<equiv>
    let delta = delta_num_fun (map_handlung besitz h) in
     \<forall>p \<in> set (betroffene delta). set delta \<in> set ((konsens (vorher h)) p)"


text\<open>Eine Handlung die keine Änderung bewirkt hat keine Betroffenen und damit immer Konsens.\<close>
lemma "hat_konsens (handeln p welt (Handlungsabsicht (\<lambda>p w. Some w)))"
  apply(simp add: hat_konsens_def Let_def)
  apply(simp add: handeln_def nachher_handeln.simps enum_person_def delta_num_same)
  apply(code_simp)
  done
  
lemma "hat_konsens (handeln Alice initialwelt
        (Handlungsabsicht (\<lambda>p w. Some (w\<lparr> besitz := (besitz w)(Alice += 3)(Bob -= 3) \<rparr>))))"
  by eval
lemma "\<not> hat_konsens (handeln Alice initialwelt
          (Handlungsabsicht (\<lambda>p w. Some (w\<lparr> besitz := (besitz w)(Alice += 4)(Bob -= 4) \<rparr>))))"
  by eval

fun zahlenwps :: \<open>person \<Rightarrow> person \<Rightarrow> zahlenwelt \<Rightarrow> zahlenwelt\<close> where
  \<open>zahlenwps p1 p2 welt =  welt\<lparr> besitz := swap p1 p2 (besitz welt) \<rparr>\<close>
(*TODO: auch den konsens swappen?*)


definition einloesen :: "(person, int) aenderung list \<Rightarrow> zahlenwelt \<Rightarrow> zahlenwelt option" where
  "einloesen delta w \<equiv> Some w"


text\<open>Ressourcen können nicht aus dem Nichts erschaffen werden.\<close>
fun abbauen :: \<open>nat \<Rightarrow> person \<Rightarrow> zahlenwelt \<Rightarrow> zahlenwelt option\<close> where
  \<open>abbauen i p welt = Some (welt\<lparr> besitz := (besitz welt)(p += int i), umwelt := (umwelt welt) - int i \<rparr>)\<close>

lemma \<open>wohlgeformte_handlungsabsicht zahlenwps welt (Handlungsabsicht (abbauen n))\<close>
  apply(case_tac \<open>welt\<close>, simp add: wohlgeformte_handlungsabsicht.simps)
  apply(simp add: swap_def)
  done


(*Ich glaube ich brauche eine Disjunktion von Maximen*)

end
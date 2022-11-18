theory BeispielZahlenwelt2
imports Zahlenwelt BeispielPerson KategorischerImperativ
begin

section\<open>Beispiel: Zahlenwelt2\<close>

record zahlenwelt =
  besitz :: \<open>person \<Rightarrow> int\<close>
  konsens :: \<open>unit\<close> (*TODO: wie modelliere ich das*)
  staatsbesitz :: \<open>int\<close> \<comment>\<open>Der Staat ist keine natürliche Person und damit besonders.\<close>
  umwelt :: \<open>int\<close>


fun zahlenwps :: \<open>person \<Rightarrow> person \<Rightarrow> zahlenwelt \<Rightarrow> zahlenwelt\<close> where
  \<open>zahlenwps p1 p2 welt =  welt\<lparr> besitz := swap p1 p2 (besitz welt) \<rparr>\<close>

text\<open>Ressourcen können nicht aus dem Nichts erschaffen werden.\<close>
fun abbauen :: \<open>nat \<Rightarrow> person \<Rightarrow> zahlenwelt \<Rightarrow> zahlenwelt option\<close> where
  \<open>abbauen i p welt = Some (welt\<lparr> besitz := (besitz welt)(p += int i), umwelt := (umwelt welt) - int i \<rparr>)\<close>

lemma \<open>wohlgeformte_handlungsabsicht zahlenwps welt (Handlungsabsicht (abbauen n))\<close>
  apply(case_tac \<open>welt\<close>, simp add: wohlgeformte_handlungsabsicht.simps)
  apply(simp add: swap_def)
  done



end
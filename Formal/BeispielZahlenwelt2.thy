theory BeispielZahlenwelt2
imports Zahlenwelt BeispielPerson Aenderung KategorischerImperativ
begin

section\<open>Beispiel: Zahlenwelt2\<close>

record zahlenwelt =
  besitz :: \<open>person \<Rightarrow> int\<close>
  konsens :: \<open>person \<Rightarrow> (person, int) abmachung list\<close>
  staatsbesitz :: \<open>int\<close> \<comment>\<open>Der Staat ist keine natürliche Person und damit besonders.\<close>
  umwelt :: \<open>int\<close>

definition initialwelt :: zahlenwelt
  where
"initialwelt \<equiv> \<lparr>
  besitz = \<^url>[Alice := 5, Bob := 10, Carol := -3],
  konsens = (\<lambda>_. [])(
    Alice := [to_abmachung [Gewinnt Alice 3], to_abmachung [Gewinnt Alice 3, Verliert Bob 3]],
    Bob := [to_abmachung [Gewinnt Alice 3, Verliert Bob 3]]),
  staatsbesitz = 9000,
  umwelt = 600
 \<rparr>"



text\<open>Mein persönlicher Besitz:\<close>
fun meins :: \<open>person \<Rightarrow> zahlenwelt \<Rightarrow> int\<close> where
  \<open>meins p welt = (besitz welt) p\<close>

lemma \<open>meins Carol initialwelt = -3\<close> by eval

(*<*)
definition zahlenwps :: \<open>person \<Rightarrow> person \<Rightarrow> zahlenwelt \<Rightarrow> zahlenwelt\<close> where
  \<open>zahlenwps p1 p2 welt = 
      welt\<lparr> besitz := swap p1 p2 (besitz welt),
            konsens := konsensswap p1 p2 (konsens welt) \<rparr>\<close>


lemma \<open>zahlenwps Alice Bob initialwelt
= \<lparr>
  besitz = \<^url>[Alice := 10, Bob := 5, Carol := -3],
  konsens = (\<lambda>_. [])(
    Alice := [to_abmachung [Gewinnt Bob 3, Verliert Alice 3]],
    Bob := [to_abmachung [Gewinnt Bob 3], to_abmachung [Gewinnt Bob 3, Verliert Alice 3]]),
  staatsbesitz = 9000,
  umwelt = 600
 \<rparr>\<close> by eval


lemma \<open>zahlenwps Alice Carol initialwelt
= \<lparr>
  besitz = \<^url>[Alice := -3, Bob := 10, Carol := 5],
  konsens = (\<lambda>_. [])(
    Bob := [to_abmachung [Gewinnt Carol 3, Verliert Bob 3]],
    Carol := [to_abmachung [Gewinnt Carol 3], to_abmachung [Gewinnt Carol 3, Verliert Bob 3]]),
  staatsbesitz = 9000,
  umwelt = 600
 \<rparr>\<close> by eval



lemma zahlenwps_id: "zahlenwps p1 p2 (zahlenwps p1 p2 welt) = welt"
  by(simp add: zahlenwps_def)

lemma zahlenwps_sym: "zahlenwps p1 p2 = zahlenwps p2 p1"
  apply(simp add: fun_eq_iff zahlenwps_def)
  by (simp add: swap_symmetric konsensswap_sym)
(*>*)


(*TODO: partial upstream*)
definition enthaelt_konsens :: "(person, int) abmachung \<Rightarrow> zahlenwelt \<Rightarrow> bool"
where
  "enthaelt_konsens abmachung welt \<equiv> \<forall>betroffene_person \<in> set (abmachungs_betroffene abmachung).
      abmachung \<in> set (konsens welt betroffene_person)"

lemma enthaelt_konsens_swap:
  "enthaelt_konsens (swap p1 p2 a) (zahlenwps p1 p2 welt) = enthaelt_konsens a welt" 
  apply(simp add: enthaelt_konsens_def abmachungs_betroffene_is_dom)
  apply(simp add: abmachung_dom_swap)
  apply(simp add: zahlenwps_def)
  apply(cases welt, simp)
  apply(simp add: konsensswap_def comp_def)
  by (smt (z3) id_apply image_def list.set_map mem_Collect_eq swap2 swap_a swap_b swap_nothing)


(*
Wenn das delta hier nicht genau das delta ist wie von hat_konsens berechnet ist das exploitable.

Also `to_abmachung (delta_num_fun (map_handlung besitz h))` muss eindeutig genau das richtige
reverse engineeren.

TODO: `to_abmachung (delta_num_fu` ersetzen durch direktes Funktion bauen!
*)
definition hat_konsens :: "zahlenwelt handlung \<Rightarrow> bool"
where
  "hat_konsens h \<equiv>
    let abmachung = to_abmachung (delta_num_fun (map_handlung besitz h))
    in enthaelt_konsens abmachung (vorher h)"


lemma "hat_konsens (map_handlung (zahlenwps p1 p2) h) = hat_konsens h"
  apply(cases h, rename_tac vor nach, simp)
  apply(simp add: hat_konsens_def)
  oops (*erst funktion updaten*)


text\<open>Eine Handlung die keine Änderung bewirkt hat keine Betroffenen und damit immer Konsens.\<close>
lemma "hat_konsens (handeln p welt (Handlungsabsicht (\<lambda>p w. Some w)))"
  apply(simp add: hat_konsens_def Let_def)
  apply(simp add: handeln_def nachher_handeln.simps enum_person_def delta_num_same)
  apply(code_simp)
  done
  
lemma "hat_konsens (handeln Alice initialwelt
        (Handlungsabsicht (\<lambda>p w. Some (w\<lparr> besitz := \<lbrakk>\<lbrakk>(besitz w)(Alice += 3)\<rbrakk>(Bob -= 3)\<rbrakk> \<rparr>))))"
  by eval
lemma "\<not> hat_konsens (handeln Alice initialwelt
          (Handlungsabsicht (\<lambda>p w. Some (w\<lparr> besitz := \<lbrakk>\<lbrakk>(besitz w)(Alice += 4)\<rbrakk>(Bob -= 4)\<rbrakk> \<rparr>))))"
  by eval



term Aenderung.abmachung_ausfuehren

definition abmachung_ausfuehren
  :: "(person, int) abmachung \<Rightarrow> zahlenwelt \<Rightarrow> zahlenwelt"
where
  "abmachung_ausfuehren abmachung welt \<equiv> welt\<lparr> besitz := Aenderung.abmachung_ausfuehren abmachung (besitz welt) \<rparr>"

lemma\<open>abmachung_ausfuehren (to_abmachung [Gewinnt Alice 3]) initialwelt
  = initialwelt\<lparr> besitz := \<lbrakk>(besitz initialwelt)(Alice += 3)\<rbrakk>\<rparr>\<close>
  by eval



definition abmachung_einloesen :: "(person, int) abmachung \<Rightarrow> zahlenwelt \<Rightarrow> zahlenwelt option" where
  "abmachung_einloesen delta welt \<equiv> 
  if enthaelt_konsens delta welt
  then Some ((abmachung_ausfuehren delta welt)\<lparr> konsens := konsens_entfernen delta (konsens welt)\<rparr>)
  else None"



lemma\<open>abmachung_einloesen (to_abmachung [Gewinnt Alice 3, Verliert Bob 3]) initialwelt
 = Some
  \<lparr>
    besitz = \<^url>[Alice := 8, Bob := 7, Carol := -3],
    konsens = (\<lambda>_. [])(
      Alice := [to_abmachung [Gewinnt Alice 3]],
      Bob := []),
    staatsbesitz = 9000,
    umwelt = 600
   \<rparr>\<close>
  by eval

lemma\<open>abmachung_einloesen (to_abmachung [Gewinnt Alice 3]) initialwelt
 = Some
  \<lparr>
    besitz = \<^url>[Alice := 8, Bob := 10, Carol := -3],
    konsens = (\<lambda>_. [])(
      Alice := [to_abmachung [Gewinnt Alice 3, Verliert Bob 3]],
      Bob := [to_abmachung [Gewinnt Alice 3, Verliert Bob 3]]),
    staatsbesitz = 9000,
    umwelt = 600
   \<rparr>\<close>
  by eval

lemma\<open>abmachung_einloesen (to_abmachung [Verliert Bob 3]) initialwelt = None\<close>
  by eval

(*Welllllll*)
lemma "\<not> wohlgeformte_handlungsabsicht zahlenwps initialwelt
         (Handlungsabsicht (\<lambda>p w. abmachung_einloesen (to_abmachung [Gewinnt Alice 3]) w))"
  by eval


(*ignoriert groesstenteils die handelnde person, nur um die Abmachung zu suchen*)
definition existierende_abmachung_einloesen :: "person \<Rightarrow> zahlenwelt \<Rightarrow> zahlenwelt option" where
  "existierende_abmachung_einloesen p welt \<equiv> 
  case (konsens welt) p
  of [] \<Rightarrow> None
  |  d#_ \<Rightarrow> abmachung_einloesen d welt"

lemma "wohlgeformte_handlungsabsicht zahlenwps initialwelt
         (Handlungsabsicht existierende_abmachung_einloesen)"
  by eval

(*<*)
lemma zahlenwelt_abmachung_ausfuehren_swap:
  "(BeispielZahlenwelt2.abmachung_ausfuehren (swap p1 p2 a) (zahlenwps p1 p2 welt)) =
       zahlenwps p2 p1 (BeispielZahlenwelt2.abmachung_ausfuehren a welt)"
    apply(simp add: BeispielZahlenwelt2.abmachung_ausfuehren_def)
  by(simp add: zahlenwps_def abmachung_ausfuehren_swap konsensswap_sym)

lemma existierende_abmachung_einloesen_map_zahlenwps:
  "map_option (zahlenwps p2 p1) (existierende_abmachung_einloesen p2 (zahlenwps p1 p2 welt)) =
    existierende_abmachung_einloesen p1 welt"
  apply(simp add: existierende_abmachung_einloesen_def)
  apply(simp add: zahlenwps_def swap_b konsensswap_def)
  apply(case_tac "konsens welt p1")
   apply(simp; fail)
  apply(simp)
  apply(simp add: abmachung_einloesen_def enthaelt_konsens_swap)
  apply(safe)
  apply(simp add: zahlenwelt_abmachung_ausfuehren_swap)
  apply(simp add: zahlenwps_def konsens_entfernen_konsensswap)
  done
(*>*)

text\<open>Auch in jeder welt gilt:\<close>
lemma "wohlgeformte_handlungsabsicht zahlenwps welt
         (Handlungsabsicht existierende_abmachung_einloesen)"
  apply(simp add: wohlgeformte_handlungsabsicht.simps)
  apply(cases welt, simp)
  using existierende_abmachung_einloesen_map_zahlenwps by simp



text\<open>Es ist nur möglich, wenn alle Betroffenen auch zustimmen.
Es is beispielsweise nicht möglich, dass \<^const>\<open>Alice\<close> eine Handlung
ausführt, die \<^const>\<open>Carol\<close> betrifft, ohne deren Zustimmung.\<close>
lemma "\<not> ausfuehrbar Alice
  \<lparr>
    besitz = \<^url>[Alice := 5, Bob := 10, Carol := -3],
    konsens = (\<lambda>_. [])(
      Alice := [to_abmachung [Verliert Carol 3]]
      ),
    staatsbesitz = 9000,
    umwelt = 600
  \<rparr>
  (Handlungsabsicht existierende_abmachung_einloesen)"
  by eval
text\<open>Nur wenn \<^const>\<open>Carol\<close> zustimmt wird die Handlung möglich.\<close>
lemma "ausfuehrbar Alice
  \<lparr>
    besitz = \<^url>[Alice := 5, Bob := 10, Carol := -3],
    konsens = (\<lambda>_. [])(
      Alice := [to_abmachung [Verliert Carol 3]],
      Carol := [to_abmachung [Verliert Carol 3]]
      ),
    staatsbesitz = 9000,
    umwelt = 600
  \<rparr>
  (Handlungsabsicht existierende_abmachung_einloesen)"
  by eval

(*bissal doof:*)
text\<open>Da \<^const>\<open>Alice\<close> nicht betroffen is, bleibt \<^term>\<open>[Verliert Carol 3]\<close> bei \<^const>\<open>Alice\<close> übrig.\<close>
lemma "nachher_handeln Alice
  \<lparr>
    besitz = \<^url>[Alice := 5, Bob := 10, Carol := -3],
    konsens = (\<lambda>_. [])(
      Alice := [to_abmachung [Verliert Carol 3]],
      Carol := [to_abmachung [Verliert Carol 3]]
      ),
    staatsbesitz = 9000,
    umwelt = 600
  \<rparr>
  (Handlungsabsicht existierende_abmachung_einloesen)
= \<lparr>
    besitz = \<^url>[Alice := 5, Bob := 10, Carol := -6],
    konsens = (\<lambda>_. [])(
      Alice := [to_abmachung [Verliert Carol 3]],
      Carol := []
      ),
    staatsbesitz = 9000,
    umwelt = 600
  \<rparr>"
  by eval







text\<open>Ressourcen können nicht aus dem Nichts erschaffen werden.\<close>
fun abbauen :: \<open>nat \<Rightarrow> person \<Rightarrow> zahlenwelt \<Rightarrow> zahlenwelt option\<close> where
  \<open>abbauen i p welt = Some (welt\<lparr> besitz := \<lbrakk>(besitz welt)(p += int i)\<rbrakk>, umwelt := (umwelt welt) - int i \<rparr>)\<close>

lemma \<open>wohlgeformte_handlungsabsicht zahlenwps welt (Handlungsabsicht (abbauen n))\<close>
  apply(case_tac \<open>welt\<close>, simp add: wohlgeformte_handlungsabsicht.simps)
  apply(simp add: zahlenwps_def swap_def)
  by (simp add: konsensswap_sym)

lemma \<open>wohlgeformte_handlungsabsicht zahlenwps initialwelt (Handlungsabsicht (abbauen n))\<close>
  by(code_simp)







fun reset :: \<open>person \<Rightarrow> zahlenwelt \<Rightarrow> zahlenwelt option\<close> where
  \<open>reset ich welt = Some (welt\<lparr> besitz := \<lambda> _. 0\<rparr>)\<close>


lemma \<open>wohlgeformte_handlungsabsicht zahlenwps welt (Handlungsabsicht reset)\<close>
  apply(simp add: wohlgeformte_handlungsabsicht.simps handeln_def nachher_handeln.simps)
  apply(simp add: zahlenwps_def konsensswap_sym)
  apply(simp add: swap_def fun_eq_iff)
  done
  

fun alles_kaputt_machen :: \<open>person \<Rightarrow> zahlenwelt \<Rightarrow> zahlenwelt option\<close> where
  \<open>alles_kaputt_machen ich welt = Some (welt\<lparr> besitz := \<lambda> _. Min ((besitz welt) ` UNIV) - 1 \<rparr>)\<close>

lemma alles_kaputt_machen_code[code]:
  \<open>alles_kaputt_machen ich welt =
   Some (welt\<lparr> besitz := (\<lambda>_. min_list (map (besitz welt) enum_class.enum) -1)\<rparr>)\<close>
  apply(cases \<open>welt\<close>, simp add: alles_kaputt_machen_code_help)
  done




fun unmoeglich :: \<open>person \<Rightarrow> zahlenwelt \<Rightarrow> zahlenwelt option\<close> where
  \<open>unmoeglich _ _ = None\<close>





fun individueller_fortschritt :: \<open>person \<Rightarrow> zahlenwelt handlung \<Rightarrow> bool\<close> where
  \<open>individueller_fortschritt p (Handlung vor nach) \<longleftrightarrow> (meins p vor) \<le> (meins p nach)\<close>

definition maxime_altruistischer_fortschritt :: \<open>(person, zahlenwelt) maxime\<close> where
  \<open>maxime_altruistischer_fortschritt \<equiv>
      Maxime (\<lambda>ich h. \<forall>pX. individueller_fortschritt pX h)\<close>



(*existierende_abmachung_einloesen macht, dass die Maxime nicht erfuellt.*)
value[simp] \<open>erzeuge_beispiel
  zahlenwps initialwelt
  [Handlungsabsicht (abbauen 5),
   Handlungsabsicht existierende_abmachung_einloesen,
   Handlungsabsicht reset,
   Handlungsabsicht alles_kaputt_machen,
   Handlungsabsicht unmoeglich]
  maxime_altruistischer_fortschritt\<close>


(*TODO:
  1) das reverse-engineered delta muss genau dem delta in der welt entsprechen
     (das sollte der neue function map typ providen).
  2) es muss getestet werden, dass die Abmachung auch eingeloest wurde, also aus dem konsens entfernt wurde
*)
definition maxime_hatte_konsens :: "(person, zahlenwelt) maxime" where
  \<open>maxime_hatte_konsens \<equiv> Maxime (\<lambda>ich h. hat_konsens h)\<close>


lemma \<open>\<forall>h \<in> set (alle_moeglichen_handlungen initialwelt [Handlungsabsicht existierende_abmachung_einloesen]).
 wohlgeformte_maxime_auf
    h zahlenwps 
    maxime_hatte_konsens\<close> by eval


lemma "wohlgeformte_maxime zahlenwps maxime_hatte_konsens"
  apply(simp add: wohlgeformte_maxime_def wohlgeformte_maxime_auf_def maxime_hatte_konsens_def)
  oops

lemma \<open>erzeuge_beispiel
  zahlenwps initialwelt
  [Handlungsabsicht existierende_abmachung_einloesen]
  maxime_hatte_konsens
= Some
  \<lparr>bsp_welt = initialwelt,
   bsp_erfuellte_maxime = Some maxime_hatte_konsens,
   bsp_erlaubte_handlungen = [Handlungsabsicht existierende_abmachung_einloesen],
   bsp_verbotene_handlungen = []\<rparr>\<close>
  by beispiel

lemma \<open>erzeuge_beispiel
  zahlenwps initialwelt
  [Handlungsabsicht (abbauen 5),
   Handlungsabsicht reset,
   Handlungsabsicht alles_kaputt_machen,
   Handlungsabsicht unmoeglich]
  maxime_altruistischer_fortschritt
= Some
  \<lparr>bsp_welt = initialwelt,
   bsp_erfuellte_maxime = Some maxime_altruistischer_fortschritt,
   bsp_erlaubte_handlungen = [Handlungsabsicht (abbauen 5), Handlungsabsicht unmoeglich],
   bsp_verbotene_handlungen = [Handlungsabsicht reset, Handlungsabsicht alles_kaputt_machen]\<rparr>\<close>
  by beispiel

(*TODO: MaximeDisj beweisen.

Irgendwie will ich, dass die ausgewaehlte maxime dann fuer eine Handlung gefixed ist.

Ich frage mich ja, ob MaximeDisj hier wirklich funktioniert
oder nur in dieser einen Welt.
*)
lemma \<open>erzeuge_beispiel
  zahlenwps initialwelt
  [Handlungsabsicht (abbauen 5),
   Handlungsabsicht existierende_abmachung_einloesen,
   Handlungsabsicht reset,
   Handlungsabsicht alles_kaputt_machen,
   Handlungsabsicht unmoeglich]
  (MaximeDisj maxime_altruistischer_fortschritt maxime_hatte_konsens)
= Some
  \<lparr>bsp_welt = initialwelt,
   bsp_erfuellte_maxime = Some (MaximeDisj maxime_altruistischer_fortschritt maxime_hatte_konsens),
   bsp_erlaubte_handlungen = [Handlungsabsicht (abbauen 5), Handlungsabsicht existierende_abmachung_einloesen, Handlungsabsicht unmoeglich],
   bsp_verbotene_handlungen = [Handlungsabsicht reset, Handlungsabsicht alles_kaputt_machen]\<rparr>\<close>
  by beispiel

end
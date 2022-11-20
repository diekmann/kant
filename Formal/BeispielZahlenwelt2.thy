theory BeispielZahlenwelt2
imports Zahlenwelt BeispielPerson Aenderung KategorischerImperativ
begin

section\<open>Beispiel: Zahlenwelt2\<close>

text\<open>Konsens laut \<^url>\<open>https://de.wikipedia.org/wiki/Konsens#Konsens_im_Rechtssystem\<close>:
"die Übereinstimmung der Willenserklärungen beider Vertragspartner über die Punkte des Vertrages"\<close>

(*TODO: (person, int) aenderung list muss ne map werden. So vong eindeutige Darstellung here.
aber irgendwie sieht das mit Listen erstmal schoener aus.*)
(*TODO: also ich muss da wirklich ne map reinpacken. Das ist mir zu doof so.
Und dann halt conversion funktionen zum showen und einlesen
*)
type_synonym  ('person, 'etwas) abmachung = "('person, 'etwas) aenderung list"

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
    Alice := [[Gewinnt Alice 3], [Gewinnt Alice 3, Verliert Bob 3]],
    Bob := [[Gewinnt Alice 3, Verliert Bob 3]]),
  staatsbesitz = 9000,
  umwelt = 600
 \<rparr>"



text\<open>Mein persönlicher Besitz:\<close>
fun meins :: \<open>person \<Rightarrow> zahlenwelt \<Rightarrow> int\<close> where
  \<open>meins p welt = (besitz welt) p\<close>

lemma \<open>meins Carol initialwelt = -3\<close> by eval




definition zahlenwps :: \<open>person \<Rightarrow> person \<Rightarrow> zahlenwelt \<Rightarrow> zahlenwelt\<close> where
  \<open>zahlenwps p1 p2 welt = 
      welt\<lparr> besitz := swap p1 p2 (besitz welt),
            konsens := swap p1 p2 ((map (map (aenderung_swap p1 p2))) \<circ> (konsens welt)) \<rparr>\<close>
(*TODO: brauche konsens swap helper*)

lemma \<open>zahlenwps Alice Bob initialwelt
= \<lparr>
  besitz = \<^url>[Alice := 10, Bob := 5, Carol := -3],
  konsens = (\<lambda>_. [])(
    Alice := [[Gewinnt Bob 3, Verliert Alice 3]],
    Bob := [[Gewinnt Bob 3], [Gewinnt Bob 3, Verliert Alice 3]]),
  staatsbesitz = 9000,
  umwelt = 600
 \<rparr>\<close> by eval


lemma \<open>zahlenwps Alice Carol initialwelt
= \<lparr>
  besitz = \<^url>[Alice := -3, Bob := 10, Carol := 5],
  konsens = (\<lambda>_. [])(
    Bob := [[Gewinnt Carol 3, Verliert Bob 3]],
    Carol := [[Gewinnt Carol 3], [Gewinnt Carol 3, Verliert Bob 3]]),
  staatsbesitz = 9000,
  umwelt = 600
 \<rparr>\<close> by eval



lemma map_map_aenderung_swap:
  "map (map (aenderung_swap p1 p2)) \<circ> (map (map (aenderung_swap p1 p2)) \<circ> kons) = kons"
  by(simp add: fun_eq_iff aenderung_swap_id comp_def)

lemma swap_map_map_aenderung_swap:
  "swap p2 p1 (map (map (aenderung_swap p2 p1)) \<circ> swap p1 p2 (map (map (aenderung_swap p1 p2)) \<circ> kons))
  = kons"
  apply(subst aenderung_swap_sym)
  apply(subst swap_symmetric)
  apply(subst swap_fun_comp_id)
  apply(simp add: map_map_aenderung_swap)
  done

lemma zahlenwps_id: "zahlenwps p2 p1 (zahlenwps p1 p2 welt) = welt"
  apply(simp add: zahlenwps_def)
  apply(simp add: swap_map_map_aenderung_swap)
  done






(*TODO: brauch lemmata?*)
definition aenderung_minimize
  :: "('person::enum, 'etwas::{ord,zero,plus,minus,uminus}) aenderung list \<Rightarrow> ('person, 'etwas) aenderung list"
  where
"aenderung_minimize as \<equiv> List.map_filter (aenderung_map as) Enum.enum"

lemma\<open>aenderung_minimize [Verliert Alice (2::int), Gewinnt Bob 3, Gewinnt Eve 3, Gewinnt Alice 2, Gewinnt Carol 2, Verliert Eve 1]
= [Gewinnt Bob 3, Gewinnt Carol 2, Gewinnt Eve 2]\<close> by eval


(*Das wier hier vie aenderung_minimize normalisieren muessen ist echt doof*)
definition enthaelt_konsens :: "(person, int) abmachung \<Rightarrow> zahlenwelt \<Rightarrow> bool"
where
  "enthaelt_konsens delta welt \<equiv> \<forall>p \<in> set (betroffene delta).
      (aenderung_minimize delta) \<in> set (map aenderung_minimize (konsens welt p))"




(*da der datentyp fuer konsens nicht eindeutig ist, kann das doof werden, ...*)
(*
Wenn das delta hier nicht genau das delta ist wie von hat_konsens berechnet ist das exploitable.*)
definition hat_konsens :: "zahlenwelt handlung \<Rightarrow> bool"
where
  "hat_konsens h \<equiv>
    let delta = delta_num_fun (map_handlung besitz h)
    in enthaelt_konsens delta (vorher h)"


lemma "enthaelt_konsens (TODOSWAP delta) (zahlenwps p1 p2 welt) = enthaelt_konsens delta welt" 
  apply(simp add: enthaelt_konsens_def)
  oops
lemma "hat_konsens (map_handlung (zahlenwps p1 p2) h) = hat_konsens h"
  apply(cases h, rename_tac vor nach, simp)
  apply(simp add: hat_konsens_def)
  oops


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




term aenderung_ausfuehren
definition aenderung_ausfuehren
  :: "(person, int) abmachung \<Rightarrow> zahlenwelt \<Rightarrow> zahlenwelt"
where
  "aenderung_ausfuehren delta welt \<equiv> welt\<lparr> besitz := Aenderung.aenderung_ausfuehren delta (besitz welt) \<rparr>"

lemma\<open>aenderung_ausfuehren [Gewinnt Alice 3] initialwelt
  = initialwelt\<lparr> besitz := (besitz initialwelt)(Alice += 3)\<rparr>\<close>
  by eval

value\<open>remove1 3 [1::int,3,5,2,3]\<close>
value\<open>remove1 9 [1::int,3,5,2,3]\<close>



definition konsens_entfernen
 :: "('person, 'etwas) abmachung \<Rightarrow> ('person \<Rightarrow> ('person, 'etwas) abmachung list)
   \<Rightarrow> 'person \<Rightarrow> ('person, 'etwas) abmachung list"
 where
"konsens_entfernen delta kons = fold (\<lambda>p k. k(p := remove1 delta (k p))) (betroffene delta) kons"

(*TODO: upstream und testen*)

lemma \<open>konsens_entfernen [Gewinnt Alice 3, Verliert Bob 3] (konsens initialwelt)
  = (\<lambda>_. [])(
    Alice := [[Gewinnt Alice 3]],
    Bob := [])\<close>
  by eval

(*TODO:

Damit die Handlungsabsicht wohlgeformt wird sollte ich vermutlich nur
eine Person angeben und wir loesen dann konsent[0] ein.
*)
definition abmachung_einloesen :: "(person, int) abmachung \<Rightarrow> zahlenwelt \<Rightarrow> zahlenwelt option" where
  "abmachung_einloesen delta welt \<equiv> 
  if enthaelt_konsens delta welt
  then Some ((aenderung_ausfuehren delta welt)\<lparr> konsens := konsens_entfernen delta (konsens welt)\<rparr>)
  else None"



lemma\<open>abmachung_einloesen [Gewinnt Alice 3, Verliert Bob 3] initialwelt
 = Some
  \<lparr>
    besitz = \<^url>[Alice := 8, Bob := 7, Carol := -3],
    konsens = (\<lambda>_. [])(
      Alice := [[Gewinnt Alice 3]],
      Bob := []),
    staatsbesitz = 9000,
    umwelt = 600
   \<rparr>\<close>
  by eval

lemma\<open>abmachung_einloesen [Gewinnt Alice 3] initialwelt
 = Some
  \<lparr>
    besitz = \<^url>[Alice := 8, Bob := 10, Carol := -3],
    konsens = (\<lambda>_. [])(
      Alice := [[Gewinnt Alice 3, Verliert Bob 3]],
      Bob := [[Gewinnt Alice 3, Verliert Bob 3]]),
    staatsbesitz = 9000,
    umwelt = 600
   \<rparr>\<close>
  by eval

lemma\<open>abmachung_einloesen [Verliert Bob 3] initialwelt = None\<close>
  by eval

(*Welllllll*)
lemma "\<not> wohlgeformte_handlungsabsicht zahlenwps initialwelt
         (Handlungsabsicht (\<lambda>p w. abmachung_einloesen [Gewinnt Alice 3] w))"
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

(*TODO: upstream und vereinfachen!*)
lemma swap_aenderung_ausfuehren:
  "swap p1 p2 (Aenderung.aenderung_ausfuehren a bes)
      = Aenderung.aenderung_ausfuehren (map (aenderung_swap p1 p2) a) (swap p1 p2 bes)"
  apply(induction a arbitrary: bes)
   apply(simp)
  apply(simp)
  apply(case_tac a1)
  subgoal
    apply(simp)
    apply(simp add: aenderung_swap_def, safe)
      apply (simp_all add: fun_upd_twist swap_def)
    done
  apply(simp)
    apply(simp add: aenderung_swap_def, safe)
    apply (simp_all add: fun_upd_twist swap_def)
  done

lemma "swap p1 p2 (map (map (aenderung_swap p1 p2)) \<circ> konsens_entfernen a kons) =
            konsens_entfernen (map (aenderung_swap p1 p2) a)
             (swap p1 p2 (map (map (aenderung_swap p1 p2)) \<circ> kons))"
  apply(simp add: konsens_entfernen_def comp_def)
  apply(induction a)
   apply(simp add: betroffene_def)
  apply(simp)
  oops

lemma "map_option (zahlenwps p1 p2) (existierende_abmachung_einloesen p1 welt)
  = existierende_abmachung_einloesen p2 (zahlenwps p1 p2 welt)"
  apply(simp add: existierende_abmachung_einloesen_def)
  apply(simp add: zahlenwps_def swap_b)
  apply(case_tac "konsens welt p1")
   apply(simp; fail)
  apply(simp)
  apply(simp add: abmachung_einloesen_def)
  apply(safe)
  apply(simp add: BeispielZahlenwelt2.aenderung_ausfuehren_def)
  apply(simp add: zahlenwps_def)
    apply(simp add: swap_aenderung_ausfuehren)
  oops

lemma "wohlgeformte_handlungsabsicht zahlenwps welt
         (Handlungsabsicht existierende_abmachung_einloesen)"
  apply(simp add: wohlgeformte_handlungsabsicht.simps)
  apply(cases welt, simp)
  oops(*TODO*)



text\<open>Es ist nur möglich, wenn alle Betroffenen auch zustimmen.
Es is beispielsweise nicht möglich, dass \<^const>\<open>Alice\<close> eine Handlung
ausführt, die \<^const>\<open>Carol\<close> betrifft, ohne deren Zustimmung.\<close>
lemma "\<not> ausfuehrbar Alice
  \<lparr>
    besitz = \<^url>[Alice := 5, Bob := 10, Carol := -3],
    konsens = (\<lambda>_. [])(
      Alice := [[Verliert Carol 3]]
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
      Alice := [[Verliert Carol 3]],
      Carol := [[Verliert Carol 3]]
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
      Alice := [[Verliert Carol 3]],
      Carol := [[Verliert Carol 3]]
      ),
    staatsbesitz = 9000,
    umwelt = 600
  \<rparr>
  (Handlungsabsicht existierende_abmachung_einloesen)
= \<lparr>
    besitz = \<^url>[Alice := 5, Bob := 10, Carol := -6],
    konsens = (\<lambda>_. [])(
      Alice := [[Verliert Carol 3]],
      Carol := []
      ),
    staatsbesitz = 9000,
    umwelt = 600
  \<rparr>"
  by eval







text\<open>Ressourcen können nicht aus dem Nichts erschaffen werden.\<close>
fun abbauen :: \<open>nat \<Rightarrow> person \<Rightarrow> zahlenwelt \<Rightarrow> zahlenwelt option\<close> where
  \<open>abbauen i p welt = Some (welt\<lparr> besitz := (besitz welt)(p += int i), umwelt := (umwelt welt) - int i \<rparr>)\<close>

lemma \<open>wohlgeformte_handlungsabsicht zahlenwps welt (Handlungsabsicht (abbauen n))\<close>
  apply(case_tac \<open>welt\<close>, simp add: wohlgeformte_handlungsabsicht.simps)
  apply(simp add: zahlenwps_def swap_def)
  (*das galt mal und hier brauche ich lemmata*)
  oops

lemma \<open>wohlgeformte_handlungsabsicht zahlenwps initialwelt (Handlungsabsicht (abbauen n))\<close>
  by(code_simp)







fun reset :: \<open>person \<Rightarrow> zahlenwelt \<Rightarrow> zahlenwelt option\<close> where
  \<open>reset ich welt = Some (welt\<lparr> besitz := \<lambda> _. 0\<rparr>)\<close>


lemma \<open>wohlgeformte_handlungsabsicht zahlenwps welt (Handlungsabsicht reset)\<close>
  apply(simp add: wohlgeformte_handlungsabsicht.simps handeln_def nachher_handeln.simps)
  apply(simp add: zahlenwps_def)
  apply(simp add: swap_map_map_aenderung_swap)
  apply(cases welt, simp)
  apply(simp add: swap_def fun_eq_iff)
  done
  

fun alles_kaputt_machen :: \<open>person \<Rightarrow> zahlenwelt \<Rightarrow> zahlenwelt option\<close> where
  \<open>alles_kaputt_machen ich welt = Some (welt\<lparr> besitz := \<lambda> _. Min ((besitz welt) ` UNIV) - 1 \<rparr>)\<close>

lemma alles_kaputt_machen_code[code]:
  \<open>alles_kaputt_machen ich welt =
   Some (welt\<lparr> besitz := (\<lambda>_. min_list (map (besitz welt) enum_class.enum) -1)\<rparr>)\<close>
  apply(cases \<open>welt\<close>, simp add: alles_kaputt_machen_code_help)
  done


(*Ich glaube ich brauche eine Disjunktion von Maximen*)
fun MaximeDisj
  :: "('person, 'welt) maxime \<Rightarrow> ('person, 'welt) maxime \<Rightarrow> ('person, 'welt) maxime"
  where
"MaximeDisj (Maxime m1) (Maxime m2) = Maxime (\<lambda>p h. m1 p h \<and> m2 p h)"



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
   Handlungsabsicht alles_kaputt_machen]
  maxime_altruistischer_fortschritt\<close>


(*TODO:
  1) das reverse-engineered delta muss genau dem delta in der welt entsprechen
  2) es muss getestet werden, dass die Abmachung auch eingeloest wurde, also aus dem konsens entfernt wurde
*)
definition maxime_hatte_konsens :: "(person, zahlenwelt) maxime" where
  \<open>maxime_hatte_konsens \<equiv> Maxime (\<lambda>ich h. hat_konsens h)\<close>


lemma \<open>\<forall>h \<in> set (alle_moeglichen_handlungen initialwelt [Handlungsabsicht existierende_abmachung_einloesen]).
 wohlgeformte_maxime_auf
    h zahlenwps 
    maxime_hatte_konsens\<close> by eval



value[simp] \<open>erzeuge_beispiel
  zahlenwps initialwelt
  [Handlungsabsicht existierende_abmachung_einloesen]
  maxime_hatte_konsens\<close>

lemma "wohlgeformte_maxime zahlenwps maxime_hatte_konsens"
  apply(simp add: wohlgeformte_maxime_def wohlgeformte_maxime_auf_def maxime_hatte_konsens_def)
  oops

value[simp] \<open>erzeuge_beispiel
  zahlenwps initialwelt
  [Handlungsabsicht (abbauen 5),
   Handlungsabsicht reset,
   Handlungsabsicht alles_kaputt_machen]
  (maxime_altruistischer_fortschritt)\<close>

(*Also das MaximeDisj funktioniert nicht so wie erwartet.
Irgendwie will ich, dass die ausgewaehlte maxime dann fuer eine Handlung gefixed ist.
In isolation funktionieren die Beispiele ja (Some maxime), aber in kombination nicht.
*)
value[simp] \<open>erzeuge_beispiel
  zahlenwps initialwelt
  [Handlungsabsicht (abbauen 5),
   Handlungsabsicht existierende_abmachung_einloesen,
   Handlungsabsicht reset,
   Handlungsabsicht alles_kaputt_machen]
  (MaximeDisj maxime_altruistischer_fortschritt maxime_hatte_konsens)\<close>


end
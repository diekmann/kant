theory BeispielZahlenwelt2
imports Zahlenwelt BeispielPerson Aenderung KategorischerImperativ
begin

section\<open>Beispiel: Zahlenwelt2\<close>

text\<open>Konsens laut \<^url>\<open>https://de.wikipedia.org/wiki/Konsens#Konsens_im_Rechtssystem\<close>:
"die Übereinstimmung der Willenserklärungen beider Vertragspartner über die Punkte des Vertrages"\<close>

(*TODO: (person, int) aenderung list muss ne map werden. So vong eindeutige Darstellung here.
aber irgendwie sieht das mit Listen erstmal schoener aus.*)
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


definition enthaelt_konsens :: "(person, int) abmachung \<Rightarrow> zahlenwelt \<Rightarrow> bool"
where
  "enthaelt_konsens delta welt \<equiv> \<forall>p \<in> set (betroffene delta). delta \<in> set (konsens welt p)"


(*da der datentyp fuer konsens nicht eindeutig ist, kann das doof werden, ...*)
(*
Wenn das delta hier nicht genau das delta ist wie von hat_konsens berechnet ist das exploitable.*)
definition hat_konsens :: "zahlenwelt handlung \<Rightarrow> bool"
where
  "hat_konsens h \<equiv>
    let delta = delta_num_fun (map_handlung besitz h)
    in enthaelt_konsens delta (vorher h)"


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







text\<open>Ressourcen können nicht aus dem Nichts erschaffen werden.\<close>
fun abbauen :: \<open>nat \<Rightarrow> person \<Rightarrow> zahlenwelt \<Rightarrow> zahlenwelt option\<close> where
  \<open>abbauen i p welt = Some (welt\<lparr> besitz := (besitz welt)(p += int i), umwelt := (umwelt welt) - int i \<rparr>)\<close>

lemma \<open>wohlgeformte_handlungsabsicht zahlenwps welt (Handlungsabsicht (abbauen n))\<close>
  apply(case_tac \<open>welt\<close>, simp add: wohlgeformte_handlungsabsicht.simps)
  apply(simp add: zahlenwps_def swap_def)
  (*das galt mal und hier brauche ich lemmata*)
  done


(*Ich glaube ich brauche eine Disjunktion von Maximen*)

end
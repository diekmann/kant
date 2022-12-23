theory BeispielZahlenwelt2
imports Zahlenwelt BeispielPerson Aenderung KategorischerImperativ
begin

section\<open>Beispiel: Zahlenwelt2\<close>
text\<open>In diesem Abschnitt werden wir ein weiteres Beispiel sehen.\<close>

text\<open>Dieses Beispiel ist ähnlich zum Beispiel Zahlenwelt in Abschnitt \ref{sec:bspzahlenwelt}.
Allerdings führen wir einige Erweiterungen ein:
  \<^item> Jeder Person wird weiterhin ihr Besitz zugeordnet.
  \<^item> Neben dem Besitz gibt es auch ein Modell von Konsens.
    Dabei soll Konsens die Liste aller bereits getroffenen Abmachungen darstellen,
    bzw modellieren, zu was die Leute bereit wären.
    So lässt sich beispielsweise Schenken (Besitzübergang mit Konsens)
    von Stehlen (Besitzübergang ohne Konsens) unterscheiden.
  \<^item> Es gibt eine spezielle Entität, nämlich den Staat.
    Diese Entität ist nicht in der Menge der natürlichen Personen enthalten.
    Dies erlaubt es z.B. den Staat in Handlungsabsichten hardzucoden und
    gleichzeitig eine wohlgeformte Handlungsabsicht zu haben.
    TODO: machen
  \<^item> Als weitere spezielle Entität wird die Umwelt eingeführt.
    TODO: auch ein Beispiel damit.
\<close>

record zahlenwelt =
  besitz :: \<open>person \<Rightarrow> int\<close>
  konsens :: \<open>(person, int) globaler_konsens\<close>
  staatsbesitz :: \<open>int\<close> \<comment>\<open>Der Staat ist keine natürliche Person und damit besonders.\<close>
  umwelt :: \<open>int\<close>

definition initialwelt :: \<open>zahlenwelt\<close>
  where
\<open>initialwelt \<equiv> \<lparr>
  besitz = \<^url>[Alice := 5, Bob := 10, Carol := -3],
  konsens = (\<lambda>_. [])(
    Alice := [to_abmachung [Gewinnt Alice 3], to_abmachung [Gewinnt Alice 3, Verliert Bob 3]],
    Bob := [to_abmachung [Gewinnt Alice 3, Verliert Bob 3]]),
  staatsbesitz = 9000,
  umwelt = 600
 \<rparr>\<close>



text\<open>Mein persönlicher Besitz:\<close>
fun meins :: \<open>person \<Rightarrow> zahlenwelt \<Rightarrow> int\<close> where
  \<open>meins p welt = (besitz welt) p\<close>

beispiel \<open>meins Carol initialwelt = -3\<close> by eval

(*<*)
definition zahlenwps :: \<open>person \<Rightarrow> person \<Rightarrow> zahlenwelt \<Rightarrow> zahlenwelt\<close> where
  \<open>zahlenwps p1 p2 welt = 
      welt\<lparr> besitz := swap p1 p2 (besitz welt),
            konsens := konsensswap p1 p2 (konsens welt) \<rparr>\<close>


beispiel \<open>zahlenwps Alice Bob initialwelt
= \<lparr>
  besitz = \<^url>[Alice := 10, Bob := 5, Carol := -3],
  konsens = (\<lambda>_. [])(
    Alice := [to_abmachung [Gewinnt Bob 3, Verliert Alice 3]],
    Bob := [to_abmachung [Gewinnt Bob 3], to_abmachung [Gewinnt Bob 3, Verliert Alice 3]]),
  staatsbesitz = 9000,
  umwelt = 600
 \<rparr>\<close> by eval


beispiel \<open>zahlenwps Alice Carol initialwelt
= \<lparr>
  besitz = \<^url>[Alice := -3, Bob := 10, Carol := 5],
  konsens = (\<lambda>_. [])(
    Bob := [to_abmachung [Gewinnt Carol 3, Verliert Bob 3]],
    Carol := [to_abmachung [Gewinnt Carol 3], to_abmachung [Gewinnt Carol 3, Verliert Bob 3]]),
  staatsbesitz = 9000,
  umwelt = 600
 \<rparr>\<close> by eval

(*<*)
lemma zahlenwps_id: \<open>zahlenwps p1 p2 (zahlenwps p1 p2 welt) = welt\<close>
  by(simp add: zahlenwps_def)

lemma zahlenwps_sym: \<open>zahlenwps p1 p2 = zahlenwps p2 p1\<close>
  apply(simp add: fun_eq_iff zahlenwps_def)
  by (simp add: swap_symmetric konsensswap_sym)

lemma zahlenwps_same: \<open>zahlenwps p p w = w\<close>
  by(cases \<open>w\<close>, simp add: zahlenwps_def)

lemma besitz_zahlenwps: \<open>besitz (zahlenwps p1 p2 welt) p2 = besitz welt p1\<close>
  apply(cases \<open>welt\<close>, simp add: zahlenwps_def)
  by (simp add: swap_b)

lemma besitz_zahlenwps_nothing: \<open>pX \<noteq> p1 \<Longrightarrow>
       pX \<noteq> p2 \<Longrightarrow>
       besitz (zahlenwps p1 p2 welt) pX = besitz welt pX\<close>
  apply(cases \<open>welt\<close>, simp add: zahlenwps_def)
  by (simp add: swap_nothing)
(*>*)


definition enthaelt_konsens :: \<open>(person, int) abmachung \<Rightarrow> zahlenwelt \<Rightarrow> bool\<close>
where
  \<open>enthaelt_konsens abmachung welt \<equiv> Aenderung.enthaelt_konsens abmachung (konsens welt)\<close>

lemma enthaelt_konsens_swap:
  \<open>enthaelt_konsens (swap p1 p2 a) (zahlenwps p1 p2 welt) = enthaelt_konsens a welt\<close> 
  by(simp add: enthaelt_konsens_def zahlenwps_def Aenderung.enthaelt_konsens_swap)
(*>*)


text\<open>Wenn \<^const>\<open>reverse_engineer_abmachung\<close> hier nicht genau die gleiche Abmachung
berechnet wie später eingelöst, dann wird das ganze exploitable.
Da eine \<^typ>\<open>('person, 'etwas) abmachung\<close> aber eine eindeutige Darstellung sein sollte,
müsst das so funktionieren.\<close>
definition hat_konsens :: \<open>zahlenwelt handlung \<Rightarrow> bool\<close>
where
  \<open>hat_konsens h \<equiv>
    let abmachung = reverse_engineer_abmachung (map_handlung besitz h)
    in enthaelt_konsens abmachung (vorher h)\<close>


(*<*)
lemma hat_konsens_swap:
  \<open>hat_konsens (map_handlung (zahlenwps p1 p2) h) = hat_konsens h\<close>
  apply(cases \<open>h\<close>, rename_tac vor nach, simp)
  apply(simp add: hat_konsens_def)
  apply(case_tac \<open>vor\<close>, case_tac \<open>nach\<close>, simp add: zahlenwps_def)
  apply(simp add: reverse_engineer_abmachung_swap)
  by (simp add: Aenderung.enthaelt_konsens_swap BeispielZahlenwelt2.enthaelt_konsens_def)

lemma hat_konsens_swap_nachher_handeln:
  \<open>hat_konsens (Handlung (zahlenwps p1 p2 welt) (nachher_handeln p1 (zahlenwps p1 p2 welt) ha)) =
    hat_konsens (Handlung welt (zahlenwps p1 p2 (nachher_handeln p1 (zahlenwps p2 p1 welt) ha)))\<close>
  apply (metis (no_types, opaque_lifting) handlung.map hat_konsens_swap zahlenwps_id zahlenwps_sym)
  done

lemma hat_konsens_noop: \<open>hat_konsens (Handlung welt welt)\<close>
  apply(simp add: hat_konsens_def reverse_engineer_abmachung_same)
  by(code_simp)

lemma nicht_ausfuehrbar_hat_konsens:
  \<open>\<not> ausfuehrbar p welt ha \<Longrightarrow> hat_konsens (handeln p welt ha)\<close>
  apply(simp add: handeln_def nicht_ausfuehrbar_nachher_handeln hat_konsens_noop)
  done
(*>*)


text\<open>Eine Handlung die keine Änderung bewirkt hat keine Betroffenen und damit immer Konsens.\<close>
lemma \<open>hat_konsens (handeln p welt (Handlungsabsicht (\<lambda>p w. Some w)))\<close>
  apply(simp add: hat_konsens_def Let_def)
  apply(simp add: handeln_def nachher_handeln.simps reverse_engineer_abmachung_same)
  apply(code_simp)
  done
  
beispiel \<open>hat_konsens (handeln Alice initialwelt
        (Handlungsabsicht (\<lambda>p w. Some (w\<lparr> besitz := \<lbrakk>\<lbrakk>(besitz w)(Alice += 3)\<rbrakk>(Bob -= 3)\<rbrakk> \<rparr>))))\<close>
  by eval
beispiel \<open>\<not> hat_konsens (handeln Alice initialwelt
          (Handlungsabsicht (\<lambda>p w. Some (w\<lparr> besitz := \<lbrakk>\<lbrakk>(besitz w)(Alice += 4)\<rbrakk>(Bob -= 4)\<rbrakk> \<rparr>))))\<close>
  by eval



definition abmachung_ausfuehren
  :: \<open>(person, int) abmachung \<Rightarrow> zahlenwelt \<Rightarrow> zahlenwelt\<close>
where
  \<open>abmachung_ausfuehren abmachung welt \<equiv>
    welt\<lparr> besitz := Aenderung.abmachung_ausfuehren abmachung (besitz welt) \<rparr>\<close>

beispiel \<open>abmachung_ausfuehren (to_abmachung [Gewinnt Alice 3]) initialwelt
  = initialwelt\<lparr> besitz := \<lbrakk>(besitz initialwelt)(Alice += 3)\<rbrakk>\<rparr>\<close>
  by eval


text\<open>Um eine \<^typ>\<open>(person, int) abmachung\<close> einzulösen wird diese erst ausgeführt
und danach aus dem globalen Konsens entfernt, damit die Abmachung
nicht mehrfach eingelöst werden kann.\<close>
definition abmachung_einloesen :: \<open>(person, int) abmachung \<Rightarrow> zahlenwelt \<Rightarrow> zahlenwelt option\<close> where
  \<open>abmachung_einloesen delta welt \<equiv> 
  if enthaelt_konsens delta welt
  then Some ((abmachung_ausfuehren delta welt)\<lparr> konsens := konsens_entfernen delta (konsens welt)\<rparr>)
  else None\<close>


beispiel \<open>abmachung_einloesen (to_abmachung [Gewinnt Alice 3, Verliert Bob 3]) initialwelt
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

beispiel \<open>abmachung_einloesen (to_abmachung [Gewinnt Alice 3]) initialwelt
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

beispiel \<open>abmachung_einloesen (to_abmachung [Verliert Bob 3]) initialwelt = None\<close>
  by eval

(*<*)
lemma abmachung_einloesen_some_entahelt_konsens:
  \<open>abmachung_einloesen a welt = Some welt' \<Longrightarrow> enthaelt_konsens a welt\<close>
  by(simp add: abmachung_einloesen_def split: if_split_asm)

lemma abmachung_einloesen_reverse_engineer:
  \<open>abmachung_einloesen a welt = Some welt'
    \<Longrightarrow> reverse_engineer_abmachung (Handlung (besitz welt) (besitz welt')) = a\<close>
  apply(simp add: abmachung_einloesen_def split: if_split_asm)
  apply(simp add: abmachung_ausfuehren_def)
  apply(simp add: reverse_engineer_abmachung)
  by force

lemma zahlenwelt_abmachung_ausfuehren_swap:
  \<open>(BeispielZahlenwelt2.abmachung_ausfuehren (swap p1 p2 a) (zahlenwps p1 p2 welt)) =
       zahlenwps p2 p1 (BeispielZahlenwelt2.abmachung_ausfuehren a welt)\<close>
    apply(simp add: BeispielZahlenwelt2.abmachung_ausfuehren_def)
  by(simp add: zahlenwps_def abmachung_ausfuehren_swap konsensswap_sym)

lemma abmachung_einloesen_zahlenwps_pullout:
  \<open>abmachung_einloesen (swap p1 p2 a) (zahlenwps p1 p2 welt)
    = map_option (zahlenwps p2 p1) (abmachung_einloesen a welt)\<close>
  apply(simp add: abmachung_einloesen_def enthaelt_konsens_swap)
  apply(clarsimp)
  apply(simp add: zahlenwelt_abmachung_ausfuehren_swap)
  apply(simp add: zahlenwps_def konsens_entfernen_konsensswap)
  by (metis konsens_entfernen_konsensswap konsensswap_id)
(*>*)


text\<open>Die Handlungsabsicht \<^const>\<open>abmachung_einloesen\<close> stellt keine
\<^const>\<open>wohlgeformte_handlungsabsicht\<close> dar, da in der Abmachung Personen
hardcedoded sind.
\<close>
beispiel \<open>\<not> wohlgeformte_handlungsabsicht zahlenwps initialwelt
         (Handlungsabsicht (\<lambda>p w. abmachung_einloesen (to_abmachung [Gewinnt Alice 3]) w))\<close>
  by eval


text\<open>Wir können aber schnell eine wohlgeformte Handlungsabsicht daraus bauen,
indem wir nicht die Abmachung an sich in die Handlungsabsicht hardcoden,
sondern indem wir eine bestehende Abmachung in der Welt referenzieren.\<close>
definition existierende_abmachung_einloesen :: \<open>person \<Rightarrow> zahlenwelt \<Rightarrow> zahlenwelt option\<close> where
  \<open>existierende_abmachung_einloesen p welt \<equiv> 
  case (konsens welt) p
  of [] \<Rightarrow> None
  |  d#_ \<Rightarrow> abmachung_einloesen d welt\<close>

lemma \<open>wohlgeformte_handlungsabsicht zahlenwps initialwelt
         (Handlungsabsicht existierende_abmachung_einloesen)\<close>
  by eval

(*<*)

lemma existierende_abmachung_einloesen_map_zahlenwps:
  \<open>map_option (zahlenwps p2 p1) (existierende_abmachung_einloesen p2 (zahlenwps p1 p2 welt)) =
    existierende_abmachung_einloesen p1 welt\<close>
  apply(simp add: existierende_abmachung_einloesen_def)
  apply(simp add: zahlenwps_def swap_b konsensswap_def)
  apply(case_tac \<open>konsens welt p1\<close>)
   apply(simp; fail)
  apply(simp)
  using abmachung_einloesen_zahlenwps_pullout
  by (metis swap2 swap_symmetric zahlenwps_id)

lemma existierende_abmachung_einloesen_zahlenwps_pullout:
  \<open>existierende_abmachung_einloesen p (zahlenwps p1 p2 welt)
    = map_option (zahlenwps p2 p1) (existierende_abmachung_einloesen (swap p1 p2 id p) welt)\<close>
  apply(cases \<open>p = p1\<close>)
  apply(simp add: swap_a)
  apply (metis existierende_abmachung_einloesen_map_zahlenwps zahlenwps_id)
  apply(cases \<open>p = p2\<close>)
  apply(simp add: swap_b)
   apply (metis existierende_abmachung_einloesen_map_zahlenwps zahlenwps_id zahlenwps_sym)
  apply(simp add: swap_nothing)

  apply(simp add: existierende_abmachung_einloesen_def)
  apply(simp add: zahlenwps_def konsensswap_def swap_nothing)
  apply(case_tac \<open>konsens welt p\<close>)
   apply(simp; fail)
  apply(simp)
  using abmachung_einloesen_zahlenwps_pullout by simp
(*>*)

text\<open>In jeder Welt ist damit die Handlungsabsicht wohlgeformt.\<close>
lemma \<open>wohlgeformte_handlungsabsicht zahlenwps welt
         (Handlungsabsicht existierende_abmachung_einloesen)\<close>
  apply(simp add: wohlgeformte_handlungsabsicht.simps)
  apply(cases \<open>welt\<close>, simp)
  using existierende_abmachung_einloesen_map_zahlenwps by simp



text\<open>Es ist nur möglich eine \<^const>\<open>existierende_abmachung_einloesen\<close>,
wenn alle Betroffenen auch zustimmen.
Es is beispielsweise nicht möglich, dass \<^const>\<open>Alice\<close> eine Handlung
ausführt, die \<^const>\<open>Carol\<close> betrifft, ohne deren Zustimmung.\<close>
beispiel \<open>\<not> ausfuehrbar Alice
  \<lparr>
    besitz = \<^url>[Alice := 5, Bob := 10, Carol := -3],
    konsens = (\<lambda>_. [])(
      Alice := [to_abmachung [Verliert Carol 3]]
      ),
    staatsbesitz = 9000,
    umwelt = 600
  \<rparr>
  (Handlungsabsicht existierende_abmachung_einloesen)\<close>
  by eval
text\<open>Nur wenn \<^const>\<open>Carol\<close> zustimmt wird die Handlung möglich.\<close>
beispiel \<open>ausfuehrbar Alice
  \<lparr>
    besitz = \<^url>[Alice := 5, Bob := 10, Carol := -3],
    konsens = (\<lambda>_. [])(
      Alice := [to_abmachung [Verliert Carol 3]],
      Carol := [to_abmachung [Verliert Carol 3]]
      ),
    staatsbesitz = 9000,
    umwelt = 600
  \<rparr>
  (Handlungsabsicht existierende_abmachung_einloesen)\<close>
  by eval

(*bissal doof:*)
text\<open>Da \<^const>\<open>Alice\<close> nicht betroffen is, bleibt \<^term>\<open>[Verliert Carol 3]\<close> bei \<^const>\<open>Alice\<close> übrig.\<close>
beispiel \<open>nachher_handeln Alice
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
  \<rparr>\<close>
  by eval


text\<open>Für\<^const>\<open>existierende_abmachung_einloesen\<close> gilt immer \<^const>\<open>hat_konsens\<close>.
Das \<^const>\<open>reverse_engineer_abmachung\<close> macht also das Richtige.\<close>
lemma hat_konsens_existierende_abmachung_einloesen:
  \<open>hat_konsens (handeln p welt (Handlungsabsicht existierende_abmachung_einloesen))\<close>
  apply(simp add: hat_konsens_def handeln_def nachher_handeln.simps)
  apply(cases \<open>existierende_abmachung_einloesen p welt\<close>)
  apply(simp)
  using hat_konsens_def hat_konsens_noop apply fastforce
  apply(simp)
  apply(rename_tac welt')
  apply(simp add: existierende_abmachung_einloesen_def split:list.split_asm)
  apply(frule abmachung_einloesen_some_entahelt_konsens)
  apply(simp add: abmachung_einloesen_reverse_engineer)
  done





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
beispiel \<open>erzeuge_beispiel
  zahlenwps initialwelt
  [Handlungsabsicht (abbauen 5),
   Handlungsabsicht existierende_abmachung_einloesen,
   Handlungsabsicht reset,
   Handlungsabsicht alles_kaputt_machen,
   Handlungsabsicht unmoeglich]
  maxime_altruistischer_fortschritt
= Some
  \<lparr>
   bsp_erfuellte_maxime = False,
   bsp_erlaubte_handlungen = [Handlungsabsicht (abbauen 5), Handlungsabsicht unmoeglich],
   bsp_verbotene_handlungen = [Handlungsabsicht reset, Handlungsabsicht alles_kaputt_machen],
   bsp_uneindeutige_handlungen = [Handlungsabsicht existierende_abmachung_einloesen]
  \<rparr>\<close> by beispiel_tac


(*TODO:
  1) das reverse-engineered delta muss genau dem delta in der welt entsprechen
     (das sollte der neue function map typ providen).
     hat_konsens_existierende_abmachung_einloesen zeigt, dass dies zumindest fuer diese eine HA gilt.
  2) es muss getestet werden, dass die Abmachung auch eingeloest wurde, also aus dem konsens entfernt wurde
*)
definition maxime_hatte_konsens :: \<open>(person, zahlenwelt) maxime\<close> where
  \<open>maxime_hatte_konsens \<equiv> Maxime (\<lambda>ich h. hat_konsens h)\<close>


beispiel \<open>\<forall>h \<in> set (alle_moeglichen_handlungen initialwelt (Handlungsabsicht existierende_abmachung_einloesen)).
 wohlgeformte_maxime_auf
    h zahlenwps 
    maxime_hatte_konsens\<close> by eval

lemma \<open>wohlgeformte_maxime zahlenwps maxime_hatte_konsens\<close>
  by(simp add: wohlgeformte_maxime_def wohlgeformte_maxime_auf_def
               maxime_hatte_konsens_def hat_konsens_swap)

beispiel \<open>erzeuge_beispiel
  zahlenwps initialwelt
  [Handlungsabsicht existierende_abmachung_einloesen]
  maxime_hatte_konsens
= Some
  \<lparr>
   bsp_erfuellte_maxime = True,
   bsp_erlaubte_handlungen = [Handlungsabsicht existierende_abmachung_einloesen],
   bsp_verbotene_handlungen = [],
   bsp_uneindeutige_handlungen = []\<rparr>\<close>
  by beispiel_tac

beispiel \<open>erzeuge_beispiel
  zahlenwps initialwelt
  [Handlungsabsicht (abbauen 5),
   Handlungsabsicht reset,
   Handlungsabsicht alles_kaputt_machen,
   Handlungsabsicht unmoeglich]
  maxime_altruistischer_fortschritt
= Some
  \<lparr>
   bsp_erfuellte_maxime = True,
   bsp_erlaubte_handlungen = [Handlungsabsicht (abbauen 5), Handlungsabsicht unmoeglich],
   bsp_verbotene_handlungen = [Handlungsabsicht reset, Handlungsabsicht alles_kaputt_machen],
   bsp_uneindeutige_handlungen = []\<rparr>\<close>
  by beispiel_tac

(*TODO: MaximeDisj beweisen.

Irgendwie will ich, dass die ausgewaehlte maxime dann fuer eine Handlung gefixed ist.

Ich frage mich ja, ob MaximeDisj hier wirklich funktioniert
oder nur in dieser einen Welt.
*)
beispiel \<open>erzeuge_beispiel
  zahlenwps initialwelt
  [Handlungsabsicht (abbauen 5),
   Handlungsabsicht existierende_abmachung_einloesen,
   Handlungsabsicht reset,
   Handlungsabsicht alles_kaputt_machen,
   Handlungsabsicht unmoeglich]
  (MaximeDisj maxime_altruistischer_fortschritt maxime_hatte_konsens)
= Some
  \<lparr>
   bsp_erfuellte_maxime = True,
   bsp_erlaubte_handlungen = [Handlungsabsicht (abbauen 5), Handlungsabsicht existierende_abmachung_einloesen, Handlungsabsicht unmoeglich],
   bsp_verbotene_handlungen = [Handlungsabsicht reset, Handlungsabsicht alles_kaputt_machen],
   bsp_uneindeutige_handlungen = []\<rparr>\<close>
  by beispiel_tac

  




lemma \<open>maxime_und_handlungsabsicht_generalisieren zahlenwps welt
     maxime_hatte_konsens (Handlungsabsicht existierende_abmachung_einloesen) p\<close>
  apply(simp add: maxime_und_handlungsabsicht_generalisieren_def maxime_hatte_konsens_def)
  apply(clarsimp)
  apply(simp add: hat_konsens_existierende_abmachung_einloesen)
  done
  
lemma mhg_katimp_maxime_hatte_konsens:
  \<open>\<forall>p. maxime_und_handlungsabsicht_generalisieren zahlenwps welt maxime_hatte_konsens ha p \<Longrightarrow>
    wohlgeformte_handlungsabsicht zahlenwps welt ha \<Longrightarrow>
    kategorischer_imperativ_auf ha welt maxime_hatte_konsens\<close>
  apply(simp add: maxime_hatte_konsens_def)
  apply(erule globale_maxime_katimp)
      apply (simp add: handeln_def hat_konsens_noop ist_noop_def; fail)
    subgoal by(simp add: wpsm_kommutiert_handlung_raw hat_konsens_swap_nachher_handeln)  using zahlenwps_sym apply fastforce
   apply (simp add: zahlenwps_id)
  by simp


lemma wpsm_kommutiert_altruistischer_fortschritt:
  \<open>wpsm_kommutiert maxime_altruistischer_fortschritt zahlenwps welt\<close>
  apply(simp add: maxime_altruistischer_fortschritt_def wpsm_kommutiert_def handeln_def nachher_handeln.simps)
  apply(safe)
   apply(case_tac \<open>pX = p1\<close>)
    apply(erule_tac x=\<open>p2\<close> in allE)
    apply (metis besitz_zahlenwps zahlenwps_sym)
   apply(case_tac \<open>pX = p2\<close>)
    apply(erule_tac x=\<open>p1\<close> in allE)
    apply (metis besitz_zahlenwps zahlenwps_sym)
   apply(erule_tac x=\<open>pX\<close> in allE)
   apply(simp add: besitz_zahlenwps_nothing zahlenwps_sym)
  by (metis besitz_zahlenwps besitz_zahlenwps_nothing zahlenwps_sym)

lemma mhg_katimp_maxime_altruistischer_fortschritt:
  \<open>\<forall>p. maxime_und_handlungsabsicht_generalisieren zahlenwps welt maxime_altruistischer_fortschritt ha p \<Longrightarrow>
    wohlgeformte_handlungsabsicht zahlenwps welt ha \<Longrightarrow>
    kategorischer_imperativ_auf ha welt maxime_altruistischer_fortschritt\<close>
  apply(simp add: maxime_altruistischer_fortschritt_def)
  apply(erule globale_maxime_katimp)
      apply (simp add: handeln_def hat_konsens_noop ist_noop_def; fail)
     using wpsm_kommutiert_altruistischer_fortschritt
     apply (simp add: maxime_altruistischer_fortschritt_def) 
    using zahlenwps_sym apply fastforce
   apply (simp add: zahlenwps_id)
    by simp


theorem
  \<open>ex_erfuellbare_instanz maxime_altruistischer_fortschritt welt ha \<and>
    (\<forall>p. maxime_und_handlungsabsicht_generalisieren
          zahlenwps welt maxime_altruistischer_fortschritt ha p)
   \<or>
   ex_erfuellbare_instanz maxime_hatte_konsens welt ha \<and>
    (\<forall>p. maxime_und_handlungsabsicht_generalisieren
          zahlenwps welt maxime_hatte_konsens ha p) \<Longrightarrow>
    wohlgeformte_handlungsabsicht zahlenwps welt ha \<Longrightarrow>
    kategorischer_imperativ_auf ha welt
      (MaximeDisj maxime_altruistischer_fortschritt maxime_hatte_konsens)\<close>
  apply(rule kategorischer_imperativ_auf_MaximeDisjI2)
  apply(elim disjE)
  using mhg_katimp_maxime_altruistischer_fortschritt apply simp
  using mhg_katimp_maxime_hatte_konsens apply simp
  done
end
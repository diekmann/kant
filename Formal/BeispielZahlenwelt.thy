theory BeispielZahlenwelt
  imports Zahlenwelt BeispielPerson KategorischerImperativ
begin

section\<open>Beispiel: Zahlenwelt\label{sec:bspzahlenwelt}\<close>
text\<open>In diesem Abschnitt werden wir ein Beispiel sehen.\<close>

text\<open>Wir nehmen an, die Welt lässt sich durch eine Zahl darstellen,
die den Besitz einer Person modelliert.

Der Besitz ist als ganze Zahl \<^typ>\<open>int\<close> modelliert und kann auch beliebig negativ werden.\<close>
datatype zahlenwelt = Zahlenwelt
  \<open>person \<Rightarrow> int \<comment> \<open>besitz: Besitz jeder Person.\<close>\<close>

(*<*)
definition \<open>show_zahlenwelt w \<equiv> case w of Zahlenwelt besitz \<Rightarrow> show_num_fun besitz\<close>
(*>*)

fun gesamtbesitz :: \<open>zahlenwelt \<Rightarrow> int\<close> where
  \<open>gesamtbesitz (Zahlenwelt besitz) = aufsummieren besitz\<close>

text\<open>Beispiel:\<close>
beispiel \<open>gesamtbesitz (Zahlenwelt (\<euro>(Alice := 4, Carol := 8))) = 12\<close> by eval
beispiel \<open>gesamtbesitz (Zahlenwelt (\<euro>(Alice := 4, Carol := 4))) = 8\<close> by eval

text\<open>Mein persönlicher Besitz:\<close>
fun meins :: \<open>person \<Rightarrow> zahlenwelt \<Rightarrow> int\<close> where
  \<open>meins p (Zahlenwelt besitz) = besitz p\<close>

text\<open>Beispiel:\<close>
beispiel \<open>meins Carol (Zahlenwelt (\<euro>(Alice := 8, Carol := 4))) = 4\<close> by eval


text\<open>Um den \<^file>\<open>SchleierNichtwissen.thy\<close> zu implementieren:\<close>
fun zahlenwps :: \<open>person \<Rightarrow> person \<Rightarrow> zahlenwelt \<Rightarrow> zahlenwelt\<close> where
  \<open>zahlenwps p1 p2 (Zahlenwelt besitz) = Zahlenwelt (swap p1 p2 besitz)\<close>

text\<open>Beispiel:\<close>
beispiel \<open>zahlenwps Alice Carol (Zahlenwelt (\<euro>(Alice := 4, Bob := 6, Carol := 8)))
    = (Zahlenwelt (\<euro>(Alice := 8, Bob := 6, Carol := 4)))\<close>
  by eval

(*<*)
lemma zahlenwps_sym:
  \<open>zahlenwps p1 p2 welt = zahlenwps p2 p1 welt\<close>
  by(cases \<open>welt\<close>, simp add: swap_symmetric)

lemma zahlenwps_id: \<open>zahlenwps p p w = w\<close>
  by(cases \<open>w\<close>, simp)

lemma zahlenwps_twice:
  \<open>zahlenwps p1 p2 (zahlenwps p1 p2 welt) = welt\<close>
  \<open>zahlenwps p1 p2 (zahlenwps p2 p1 welt) = welt\<close>
  by(cases \<open>welt\<close>, simp)+

lemma gesamtbesitz_swap:
  \<open>gesamtbesitz (zahlenwps p1 p2 welt) = gesamtbesitz welt\<close>
  by(cases \<open>welt\<close>, simp add: aufsummieren_swap)


lemma hlp1: \<open>meins p1 (zahlenwps p1 p2 welt) = meins p2 welt\<close>
  by(cases \<open>welt\<close>, simp add: swap_def)
lemma hlp2: \<open>meins p2 (zahlenwps p1 p2 welt) = meins p1 welt\<close>
  by(cases \<open>welt\<close>, simp add: swap_def)

lemma hlp3: \<open>p1 \<noteq> p2 \<Longrightarrow> p \<noteq> p1 \<Longrightarrow> p \<noteq> p2 \<Longrightarrow>
         meins p (zahlenwps p1 p2 welt) = meins p welt\<close>
  by(cases \<open>welt\<close>, simp add: swap_def)
(*>*)


text\<open>\<^const>\<open>Alice\<close> hat Besitz, \<^const>\<open>Bob\<close> ist reicher, \<^const>\<open>Carol\<close> hat Schulden.\<close>
definition \<open>initialwelt \<equiv> Zahlenwelt (\<euro>(Alice := 5, Bob := 10, Carol := -3))\<close>



subsection\<open>Ungültige Handlung\<close>
text\<open>Sobald ich eine konkrete Person in einer Handlungsabsicht hardcode,
  ist diese nicht mehr wohlgeformt.\<close>

beispiel \<open>\<not>wohlgeformte_handlungsabsicht
    zahlenwps (Zahlenwelt (\<euro>(Alice := 5, Bob := 10, Carol := -3)))
    (Handlungsabsicht (\<lambda>ich w. if ich = Alice then Some w else Some (Zahlenwelt (\<lambda>_. 0))))\<close>
  apply(simp add: wohlgeformte_handlungsabsicht.simps swap_def)
  apply(eval)
  done

subsection\<open>Nicht-Wohlgeformte Handlungen\<close>
fun stehlen_nichtwf :: \<open>int \<Rightarrow> person \<Rightarrow> person \<Rightarrow> zahlenwelt \<Rightarrow> zahlenwelt option\<close> where
  \<open>stehlen_nichtwf beute opfer dieb (Zahlenwelt besitz) =
        Some (Zahlenwelt \<lbrakk>\<lbrakk>besitz(opfer -= beute)\<rbrakk>(dieb += beute)\<rbrakk>)\<close>
text\<open>Die Handlung \<^const>\<open>stehlen\<close> diskriminiert und ist damit nicht wohlgeformt:\<close>
lemma \<open>wohlgeformte_handlungsabsicht_gegenbeispiel zahlenwps
      (Zahlenwelt (\<lambda>x. 0)) (Handlungsabsicht (stehlen_nichtwf 5 Bob))
      Alice Bob\<close>
  by(eval)

text\<open>Wir versuchen, das Opfer nach Besitz auszuwählen, nicht nach Namen.
  Nach unserer Definition ist der Besitz ein Merkmal, nach dem man diskriminieren darf.
  Man darf nur nicht nach Eigenschaften der \<^typ>\<open>person\<close> diskriminieren, sondern nur
  nach Eigenschaften der \<^typ>\<open>zahlenwelt\<close>.\<close>
fun opfer_nach_besitz_auswaehlen :: \<open>int \<Rightarrow> ('person \<Rightarrow> int) \<Rightarrow> 'person list \<Rightarrow> 'person option\<close> where
  \<open>opfer_nach_besitz_auswaehlen _ _ [] = None\<close>
| \<open>opfer_nach_besitz_auswaehlen b besitz (p#ps) = 
      (if besitz p = b then Some p else opfer_nach_besitz_auswaehlen b besitz ps)\<close>

fun stehlen_nichtwf2 :: \<open>int \<Rightarrow> int \<Rightarrow> person \<Rightarrow> zahlenwelt \<Rightarrow> zahlenwelt option\<close> where
  \<open>stehlen_nichtwf2 beute opfer_nach_besitz dieb (Zahlenwelt besitz) =
        (case opfer_nach_besitz_auswaehlen opfer_nach_besitz besitz Enum.enum
           of None \<Rightarrow> None
            | Some opfer \<Rightarrow> Some (Zahlenwelt \<lbrakk>\<lbrakk>besitz(opfer -= beute)\<rbrakk>(dieb += beute)\<rbrakk>)
        )\<close>
text\<open>Leider ist diese Funktion auch diskriminierend:
  Wenn es mehrere potenzielle Opfer mit dem gleichen Besitz gibt,
  dann bestimmt die Reihenfolge in \<^term>\<open>Enum.enum\<close> wer bestohlen wird.
  Diese Reihenfolge ist wieder eine Eigenschaft von \<^typ>\<open>person\<close> und nicht \<^typ>\<open>zahlenwelt\<close>.\<close>
beispiel\<open>handeln Alice (Zahlenwelt (\<euro>(Alice := 10, Bob := 10, Carol := -3)))
                (Handlungsabsicht (stehlen_nichtwf2 5 10))
  = Handlung (Zahlenwelt (\<euro>(Alice := 10, Bob := 10, Carol := - 3)))
               (Zahlenwelt (\<euro>(Alice := 10, Bob := 10, Carol := - 3)))\<close> by eval
beispiel\<open>handeln Bob (Zahlenwelt (\<euro>(Alice := 10, Bob := 10, Carol := -3)))
              (Handlungsabsicht (stehlen_nichtwf2 5 10))
  = Handlung (Zahlenwelt (\<euro>(Alice := 10, Bob := 10, Carol := - 3)))
             (Zahlenwelt (\<euro>(Alice := 5, Bob := 15, Carol := - 3)))\<close> by eval
beispiel \<open>wohlgeformte_handlungsabsicht_gegenbeispiel
      zahlenwps
      (Zahlenwelt (\<euro>(Alice := 10, Bob := 10, Carol := -3))) (Handlungsabsicht (stehlen_nichtwf2 5 10))
      Alice Bob\<close>
  by eval

fun schenken :: \<open>int \<Rightarrow> person \<Rightarrow> person \<Rightarrow> zahlenwelt \<Rightarrow> zahlenwelt option\<close> where
  \<open>schenken betrag empfaenger schenker (Zahlenwelt besitz) =
        Some (Zahlenwelt \<lbrakk>\<lbrakk>besitz(schenker -= betrag)\<rbrakk>(empfaenger += betrag)\<rbrakk>)\<close>

text\<open>Da wir ganze Zahlen verwenden und der Besitz auch beliebig negativ werden kann,
  ist Stehlen äquivalent dazu einen negativen Betrag zu verschenken:\<close>
lemma stehlen_ist_schenken: \<open>stehlen_nichtwf i = schenken (-i)\<close>
  apply(simp add: fun_eq_iff)
  apply(intro allI, rename_tac p1 p2 welt, case_tac \<open>welt\<close>)
  by auto

text\<open>Das Modell ist nicht ganz perfekt, .... Aber passt schon um damit zu spielen.\<close>


subsection\<open>Wohlgeformte Handlungen\<close>
text\<open>Die folgende Handlung erschafft neuen Besitz aus dem Nichts:\<close>
fun erschaffen :: \<open>nat \<Rightarrow> person \<Rightarrow> zahlenwelt \<Rightarrow> zahlenwelt option\<close> where
  \<open>erschaffen i p (Zahlenwelt besitz) = Some (Zahlenwelt \<lbrakk>besitz(p += int i)\<rbrakk>)\<close>

lemma wohlgeformte_handlungsabsicht_erschaffen:
  \<open>wohlgeformte_handlungsabsicht zahlenwps welt (Handlungsabsicht (erschaffen n))\<close>
  apply(case_tac \<open>welt\<close>, simp add: wohlgeformte_handlungsabsicht.simps)
  apply(simp add: swap_def Fun.swap_def)
  done

text\<open>Wenn wir das Opfer eindeutig auswählen, ist die Handlungsabsicht "Stehlen" wohlgeformt.
  Allerdings wird niemand bestohlen, wenn das Opfer nicht eindeutig ist.\<close>
fun stehlen :: \<open>int \<Rightarrow> int \<Rightarrow> person \<Rightarrow> zahlenwelt \<Rightarrow> zahlenwelt option\<close> where
  \<open>stehlen beute opfer_nach_besitz dieb (Zahlenwelt besitz) =
        map_option Zahlenwelt (Zahlenwelt.stehlen beute opfer_nach_besitz dieb besitz)\<close>

(*<*)
lemma wohlgeformte_handlungsabsicht_stehlen:
  \<open>wohlgeformte_handlungsabsicht zahlenwps welt (Handlungsabsicht (stehlen n p))\<close>
  apply(cases \<open>welt\<close>)
  apply(rule wfh_generalize_worldI[OF wohlgeformte_handlungsabsicht_stehlen, where C=\<open>Zahlenwelt\<close>])
  by(auto)
(*>*)

text\<open>Reset versetzt die Welt wieder in den Ausgangszustand. Eine sehr destruktive Handlung.\<close>
fun reset :: \<open>person \<Rightarrow> zahlenwelt \<Rightarrow> zahlenwelt option\<close> where
  \<open>reset ich (Zahlenwelt besitz) = Some (Zahlenwelt (\<lambda> _. 0))\<close>

text\<open>Der \<^const>\<open>reset\<close> ist im moralischen Sinne vermutlich keine gute Handlung,
  dennoch ist es eine wohlgeformte Handlung, welche wir betrachten können:\<close>
lemma wohlgeformte_handlungsabsicht_reset:
  \<open>wohlgeformte_handlungsabsicht zahlenwps welt (Handlungsabsicht reset)\<close>
  apply(simp add: wohlgeformte_handlungsabsicht.simps handeln_def nachher_handeln.simps)
  by(case_tac \<open>welt\<close>, simp add: swap_def fun_eq_iff)

fun alles_kaputt_machen :: \<open>person \<Rightarrow> zahlenwelt \<Rightarrow> zahlenwelt option\<close> where
  \<open>alles_kaputt_machen ich (Zahlenwelt besitz) = Some (Zahlenwelt (\<lambda> _. Min (besitz ` UNIV) - 1))\<close>

(*<*)
lemma alles_kaputt_machen_code[code]:
  \<open>alles_kaputt_machen ich welt =
     (case welt of Zahlenwelt besitz \<Rightarrow> Some (Zahlenwelt (\<lambda>_. min_list (map besitz enum_class.enum) -1)))\<close>
  apply(cases \<open>welt\<close>, simp add: alles_kaputt_machen_code_help)
  done

lemma wohlgeformte_handlungsabsicht_alles_kaputt_machen:
  \<open>wohlgeformte_handlungsabsicht zahlenwps welt (Handlungsabsicht alles_kaputt_machen)\<close>
  apply(simp add: wohlgeformte_handlungsabsicht.simps)
  apply(simp add: alles_kaputt_machen_code)
  apply(case_tac \<open>welt\<close>, simp add: fun_eq_iff)
  apply(simp add: min_list_swap_int_enum)
  by (simp add: swap_def)
(*>*)

beispiel \<open>alles_kaputt_machen Alice (Zahlenwelt (\<euro>(Alice := 5, Bob := 10, Carol := -3)))
  = Some (Zahlenwelt (\<euro>(Alice := -4, Bob := -4, Carol := -4, Eve := -4)))\<close>
  by(code_simp)

(*TODO: Handlung alles_besser_machen.*)


text\<open>Auch die unmögliche (niemals ausführbare) Handlung lässt sich modellieren.\<close>
fun unmoeglich :: \<open>person \<Rightarrow> zahlenwelt \<Rightarrow> zahlenwelt option\<close> where
  \<open>unmoeglich _ _ = None\<close>




text\<open>Die Beispielhandlungsabsichten, die wir betrachten wollen.\<close>
definition \<open>handlungsabsichten \<equiv> [
  Handlungsabsicht (erschaffen 5),
  Handlungsabsicht (stehlen 5 10),
  Handlungsabsicht reset,
  Handlungsabsicht alles_kaputt_machen,
  Handlungsabsicht unmoeglich
]\<close>

lemma wfh_handlungsabsichten:
  \<open>ha \<in> set handlungsabsichten \<Longrightarrow> wohlgeformte_handlungsabsicht zahlenwps welt ha\<close>
  apply(simp add: handlungsabsichten_def)
  apply(safe)
      apply(simp_all add: wohlgeformte_handlungsabsicht_stehlen
      wohlgeformte_handlungsabsicht_alles_kaputt_machen
      wohlgeformte_handlungsabsicht_erschaffen
      wohlgeformte_handlungsabsicht_reset)
  apply(simp add: wohlgeformte_handlungsabsicht.simps)
  done


subsection\<open>Maxime für individuellen Fortschritt\<close>
text\<open>Wir definieren eine Maxime die besagt,
  dass sich der Besitz einer Person nicht verringern darf:\<close>
fun individueller_fortschritt :: \<open>person \<Rightarrow> zahlenwelt handlung \<Rightarrow> bool\<close> where
  \<open>individueller_fortschritt p (Handlung vor nach) \<longleftrightarrow> (meins p vor) \<le> (meins p nach)\<close>


definition maxime_zahlenfortschritt :: \<open>(person, zahlenwelt) maxime\<close> where
  \<open>maxime_zahlenfortschritt \<equiv> Maxime (\<lambda>ich. individueller_fortschritt ich)\<close>

(*<*)
lemma mhg_maxime_zahlenfortschritt_stehlen:
  \<open>maxime_und_handlungsabsicht_generalisieren zahlenwps welt maxime_zahlenfortschritt (Handlungsabsicht (stehlen 5 10)) p\<close>
  apply(simp add: maxime_und_handlungsabsicht_generalisieren_def
                  maxime_zahlenfortschritt_def, intro allI impI)
  apply(case_tac \<open>welt\<close>, simp)
  apply(simp add: Zahlenwelt.stehlen.simps handeln_def nachher_handeln.simps
                  opfer_eindeutig_nach_besitz_auswaehlen_the_single_elem_enumall)
  apply(auto intro: the_single_elem_exhaust)
  done
(*>*)

text\<open>Die Eigenschaft \<^const>\<open>maxime_und_handlungsabsicht_generalisieren\<close> wird von den meisten
Handlungsabsichten erfüllt.
Jedoch nicht von \<^const>\<open>reset\<close>.
Das nicht-wohlgeformte \<^const>\<open>stehlen_nichtwf\<close> erfüllt sie allerdings schon.\<close>
lemma \<open>ha \<in> {
    Handlungsabsicht (erschaffen 5),
    Handlungsabsicht (stehlen_nichtwf 5 Bob),
    Handlungsabsicht (stehlen 5 10),
    Handlungsabsicht alles_kaputt_machen,
    Handlungsabsicht unmoeglich
  } \<Longrightarrow> maxime_und_handlungsabsicht_generalisieren zahlenwps welt maxime_zahlenfortschritt ha p\<close>
  apply(simp)
  apply(safe)
      apply(case_tac \<open>welt\<close>, simp add: handeln_def nachher_handeln.simps maxime_und_handlungsabsicht_generalisieren_def maxime_zahlenfortschritt_def; fail)
     apply(case_tac \<open>welt\<close>, simp add: handeln_def nachher_handeln.simps maxime_und_handlungsabsicht_generalisieren_def maxime_zahlenfortschritt_def; fail)
  subgoal using mhg_maxime_zahlenfortschritt_stehlen by simp
  subgoal
    by(case_tac \<open>welt\<close>, simp add: handeln_def nachher_handeln.simps maxime_und_handlungsabsicht_generalisieren_def maxime_zahlenfortschritt_def, auto)
  apply(case_tac \<open>welt\<close>, simp add: handeln_def nachher_handeln.simps maxime_und_handlungsabsicht_generalisieren_def maxime_zahlenfortschritt_def; fail)
  done

text\<open>Nicht alle Handlungen generalisieren, z.B. \<^const>\<open>reset\<close> nicht:\<close>
beispiel
  \<open>\<not> maxime_und_handlungsabsicht_generalisieren
         zahlenwps (Zahlenwelt (\<euro>(Alice := 5, Bob := 10, Carol := -3)))
         maxime_zahlenfortschritt (Handlungsabsicht reset) Alice\<close>
  by eval


text\<open>Die \<^const>\<open>maxime_zahlenfortschritt\<close> erfüllt allgemein \<^bold>\<open>nicht\<close>
den \<^const>\<open>kategorischer_imperativ\<close>,
da \<^const>\<open>Alice\<close> nach der Maxime z.B. \<^const>\<open>Bob\<close> bestehlen dürfte.\<close>
beispiel \<open>kategorischer_imperativ_gegenbeispiel
  zahlenwps initialwelt maxime_zahlenfortschritt
  (Handlungsabsicht (stehlen 1 10))
  Alice
  Bob
  Alice\<close>
  apply(simp add: kategorischer_imperativ_gegenbeispiel_def
      wohlgeformte_handlungsabsicht_stehlen mhg_maxime_zahlenfortschritt_stehlen)
  by(eval)

(*<*)
lemma \<open>wpsm_kommutiert (maxime_zahlenfortschritt) zahlenwps welt\<close>
  by(simp add: maxime_zahlenfortschritt_def handeln_def
               nachher_handeln.simps wpsm_kommutiert_def hlp1 hlp2 zahlenwps_sym)
(*>*)


text\<open>Folgendes Beispiel zeigt, dass die \<^const>\<open>maxime_zahlenfortschritt\<close> den
kategorischen Imperativ auf unseren \<^const>\<open>handlungsabsichten\<close> nicht erfüllt
(zu sehen an dem \<^const>\<open>False\<close> im \<^const>\<open>bsp_erfuellte_maxime\<close>.).
Die Handlungsabsichten \<^const>\<open>stehlen\<close> als auch \<^const>\<open>reset\<close> sind nicht mit der Maxime vereinbar.
Für die übrigen Handlungsabsichten ist das Ergebnis aber intuitiv:
  \<^item> \<^const>\<open>erschaffen\<close> ist erlaubt.
  \<^item> da \<^const>\<open>unmoeglich\<close> im Nichtstuen endet, ist dies auch erlaubt.
  \<^item> \<^const>\<open>alles_kaputt_machen\<close> ist verboten.
\<close>
beispiel \<open>erzeuge_beispiel
    zahlenwps (Zahlenwelt (\<euro>(Alice := 5, Bob := 10, Carol := -3)))
    handlungsabsichten
    maxime_zahlenfortschritt =
  Some
    \<lparr>
     bsp_erfuellte_maxime = False,
     bsp_erlaubte_handlungen = [
        Handlungsabsicht (erschaffen 5),
        Handlungsabsicht unmoeglich],
     bsp_verbotene_handlungen = [Handlungsabsicht alles_kaputt_machen],
     bsp_uneindeutige_handlungen = [
        Handlungsabsicht (stehlen 5 10),
        Handlungsabsicht reset]\<rparr>\<close>
  by beispiel_tac


subsubsection\<open>Einzelbeispiele\<close>
text\<open>In jeder Welt ist die \<^term>\<open>Handlungsabsicht (erschaffen n)\<close> \<^const>\<open>moralisch\<close>:\<close>
lemma \<open>moralisch welt maxime_zahlenfortschritt (Handlungsabsicht (erschaffen n))\<close>
  apply(cases \<open>welt\<close>)
  by(simp add: maxime_zahlenfortschritt_def moralisch_simp handeln_def nachher_handeln.simps)

text\<open>In kein Welt ist Stehlen \<^const>\<open>moralisch\<close>:\<close>
lemma \<open>\<not> moralisch welt maxime_zahlenfortschritt (Handlungsabsicht (stehlen_nichtwf 5 Bob))\<close>
  by(cases \<open>welt\<close>, auto simp add: maxime_zahlenfortschritt_def moralisch_simp handeln_def nachher_handeln.simps)

text\<open>In unserer \<^const>\<open>initialwelt\<close> in der \<^const>\<open>Bob\<close> als Opfer anhand seines Besitzes
    als Opfer eines Diebstahls ausgewählt würde, ist stehlen dennoch nicht \<^const>\<open>moralisch\<close>,
    obwohl die Handlungsabsicht wohlgeformt ist:\<close>
lemma \<open>\<not> moralisch initialwelt maxime_zahlenfortschritt (Handlungsabsicht (stehlen 5 10))\<close>
  by(eval)

text\<open>Da Schenken und Stehlen in dieser Welt equivalent ist, ist Schenken auch unmoralisch:\<close>  
lemma \<open>\<not> moralisch welt maxime_zahlenfortschritt (Handlungsabsicht (schenken 5 Bob))\<close>
  by(cases \<open>welt\<close>, auto simp add: maxime_zahlenfortschritt_def moralisch_simp handeln_def nachher_handeln.simps)




subsection\<open>Maxime für allgemeinen Fortschritt\<close>
text\<open>Wir können die vorherige Maxime generalisieren, indem wir \<^const>\<open>individueller_fortschritt\<close>
für jeden fordern.
Effektiv wird dabei das \<^term>\<open>ich::person\<close> ignoriert.\<close>

definition maxime_altruistischer_fortschritt :: \<open>(person, zahlenwelt) maxime\<close> where
  \<open>maxime_altruistischer_fortschritt \<equiv> Maxime (\<lambda>ich h. \<forall>pX. individueller_fortschritt pX h)\<close>

text\<open>Folgendes Beispiel zeigt, dass die \<^const>\<open>maxime_altruistischer_fortschritt\<close>
den kategorischen Imperativ (für diese \<^const>\<open>initialwelt\<close> und \<^const>\<open>handlungsabsichten\<close>)
erfüllt; zu sehen an dem \<^const>\<open>True\<close> im \<^const>\<open>bsp_erfuellte_maxime\<close>.

Die Handlungsabsichten werden eingeordnet wie erwartet:
  \<^item> \<^const>\<open>erschaffen\<close> ist gut, \<^const>\<open>unmoeglich\<close> (bedeutet: Nichtstun) ist auch okay.
  \<^item> \<^const>\<open>stehlen\<close>, \<^const>\<open>reset\<close>, \<^const>\<open>alles_kaputt_machen\<close> ist schlecht.
  \<close>
beispiel \<open>erzeuge_beispiel
    zahlenwps (Zahlenwelt (\<euro>(Alice := 5, Bob := 10, Carol := -3)))
    handlungsabsichten
    maxime_altruistischer_fortschritt =
  Some
    \<lparr>
     bsp_erfuellte_maxime = True,
     bsp_erlaubte_handlungen = [
        Handlungsabsicht (erschaffen 5),
        Handlungsabsicht unmoeglich],
     bsp_verbotene_handlungen = [
        Handlungsabsicht (stehlen 5 10),
        Handlungsabsicht reset,
        Handlungsabsicht alles_kaputt_machen],
     bsp_uneindeutige_handlungen = []\<rparr>\<close>
  by beispiel_tac
text\<open>Das ist ein sehr schönes Beispiel.\<close>

(*<*)
lemma wpsm_kommutiert_altruistischer_fortschritt:
  \<open>wpsm_kommutiert maxime_altruistischer_fortschritt zahlenwps welt\<close>
  apply(simp add: maxime_altruistischer_fortschritt_def wpsm_kommutiert_def handeln_def nachher_handeln.simps)
  apply(safe)
   apply(case_tac \<open>p1 = p2\<close>)
    apply(simp add: zahlenwps_id; fail)
   apply(case_tac \<open>pX = p1\<close>)
    apply(simp)
    apply (metis hlp1 zahlenwps_sym)
   apply (metis hlp2 hlp3 zahlenwps_sym)
  by (metis hlp2 hlp3 zahlenwps_id zahlenwps_sym)

lemma mhg_maxime_altruistischer_fortschritt_stehlen:
  \<open>maxime_und_handlungsabsicht_generalisieren zahlenwps welt 
      maxime_altruistischer_fortschritt (Handlungsabsicht (stehlen 5 10)) p\<close>
  apply(simp add: maxime_altruistischer_fortschritt_def maxime_und_handlungsabsicht_generalisieren_def maxime_zahlenfortschritt_def handeln_def nachher_handeln.simps, intro allI impI)
  apply(simp add: ausfuehrbar.simps)
  apply(case_tac \<open>welt\<close>, simp)
  apply(simp add: Zahlenwelt.stehlen.simps opfer_eindeutig_nach_besitz_auswaehlen_the_single_elem_enumall)
  apply(simp add: ist_noop_def split: option.split option.split_asm)
  by fastforce

lemma maxime_altruistischer_fortschritt_reset:
  \<open>maxime_und_handlungsabsicht_generalisieren zahlenwps welt 
      maxime_altruistischer_fortschritt (Handlungsabsicht (reset)) p\<close>
  apply(simp add: maxime_altruistischer_fortschritt_def maxime_und_handlungsabsicht_generalisieren_def maxime_zahlenfortschritt_def handeln_def nachher_handeln.simps, intro allI impI)
  apply(case_tac \<open>welt\<close>, simp)
  apply(auto simp add: swap_def Fun.swap_def split: option.split option.split_asm)
  done

lemma maxime_altruistischer_fortschritt_alles_kaputt_machen:
  \<open>maxime_und_handlungsabsicht_generalisieren zahlenwps welt 
      maxime_altruistischer_fortschritt (Handlungsabsicht (alles_kaputt_machen)) p\<close>
  apply(simp add: maxime_altruistischer_fortschritt_def maxime_und_handlungsabsicht_generalisieren_def maxime_zahlenfortschritt_def handeln_def nachher_handeln.simps, intro allI impI)
  apply(case_tac \<open>welt\<close>, simp)
  apply(auto simp add: swap_def Fun.swap_def split: option.split option.split_asm)
  done

lemma wfm_maxime_altruistischer_fortschritt:
  \<open>wohlgeformte_maxime zahlenwps maxime_altruistischer_fortschritt\<close>
  apply(simp add: maxime_altruistischer_fortschritt_def wohlgeformte_maxime_def wohlgeformte_maxime_auf_def handeln_def nachher_handeln.simps, intro allI, rename_tac h p1 p2)
  apply(case_tac \<open>h\<close>, rename_tac vor nach, simp)
  apply(case_tac \<open>vor\<close>, case_tac \<open>nach\<close>, simp)
  apply(simp add: swap_forall)
  done

lemma individueller_fortschritt_map_handlung_zahlenwps:
  \<open>individueller_fortschritt pX (map_handlung (zahlenwps p1 p2) ha)
      = individueller_fortschritt (swap p1 p2 id pX) ha\<close>
  apply(cases \<open>ha\<close>, simp)
  apply(cases \<open>pX = p1\<close>)
   apply(simp add: hlp1  swap_a; fail)
  apply(cases \<open>pX = p2\<close>)
   apply(simp add: hlp2 swap_b; fail)
  by (metis hlp3 id_apply swap_nothing zahlenwps_id)

lemma maxime_altruistischer_fortschritt_mhg_handlungsabsichten:
  \<open>ha \<in> set handlungsabsichten \<Longrightarrow>
    maxime_und_handlungsabsicht_generalisieren zahlenwps welt maxime_altruistischer_fortschritt ha p\<close>
  apply(simp add: handlungsabsichten_def)
  apply(safe)
      apply(case_tac \<open>welt\<close>, simp add: handeln_def nachher_handeln.simps maxime_und_handlungsabsicht_generalisieren_def maxime_altruistischer_fortschritt_def; fail)
     apply (simp add: mhg_maxime_altruistischer_fortschritt_stehlen; fail)
    apply(simp add: maxime_altruistischer_fortschritt_reset; fail)
   apply(simp add: maxime_altruistischer_fortschritt_alles_kaputt_machen; fail)
  apply(case_tac \<open>welt\<close>, simp add: handeln_def nachher_handeln.simps maxime_und_handlungsabsicht_generalisieren_def maxime_altruistischer_fortschritt_def)
  done
(*>*)


text\<open>Die Aussage, dass die \<^const>\<open>maxime_altruistischer_fortschritt\<close> den kategorischen Imperativ
  für bestimmte Handlungsabsichten und Welten erfüllt generalisiert noch weiter.
  Für alle Welten und alle wohlgeformten Handlungsabsichten welche mit der Maxime generalisieren
  erfüllt die Maxime den kategorischen Imperativ.\<close>
theorem kapimp_maxime_altruistischer_fortschritt: \<open>
    \<forall>p. maxime_und_handlungsabsicht_generalisieren zahlenwps welt maxime_altruistischer_fortschritt ha p \<Longrightarrow>
    wohlgeformte_handlungsabsicht zahlenwps welt ha \<Longrightarrow>
    kategorischer_imperativ_auf ha welt maxime_altruistischer_fortschritt\<close>
  unfolding maxime_altruistischer_fortschritt_def
  apply(erule globale_maxime_katimp)
      apply(cases \<open>ha\<close>, simp add: ist_noop_def handeln_def nachher_handeln.simps; fail)
     apply(simp add: wpsm_kommutiert_altruistischer_fortschritt[simplified maxime_altruistischer_fortschritt_def]; fail)
    apply (simp add: zahlenwps_sym; fail)
   apply (simp add: zahlenwps_twice; fail)
  by(simp; fail)

text\<open>Allgemein scheint dies eine sehr gute Maxime zu sein
  (für dieses sehr beschränkte Weltenmodell).\<close>

corollary \<open>ha \<in> set handlungsabsichten \<Longrightarrow>
    kategorischer_imperativ_auf ha welt maxime_altruistischer_fortschritt\<close>
  apply(rule kapimp_maxime_altruistischer_fortschritt)
  using maxime_altruistischer_fortschritt_mhg_handlungsabsichten apply simp
  using wfh_handlungsabsichten apply simp
  done



(*<*)
(*Interessante Sachen. Die sollten in die jeweiligen thys upgestremed werden.*)
lemma
  \<open>okay maxime_altruistischer_fortschritt p1 (handeln p2 welt ha) \<longleftrightarrow> 
    okay maxime_altruistischer_fortschritt p2 (map_handlung (zahlenwps p1 p2) (handeln p2 welt ha))\<close>
  using wfm_maxime_altruistischer_fortschritt
  by (simp add: wohlgeformte_maxime_auf_def wohlgeformte_maxime_def)

beispiel \<open>p \<noteq> p1 \<Longrightarrow> p \<noteq> p2 \<Longrightarrow>
  zahlenwps p2 p (zahlenwps p1 p2 (zahlenwps p1 p welt)) = zahlenwps p1 p2 welt\<close>
  apply(cases \<open>welt\<close>, simp add: swap_def)
  by (metis swap_nilpotent swap_triple)

lemma zahlenwps_unrelated_im_kreis:
  \<open>p \<noteq> p1 \<Longrightarrow> p \<noteq> p2 \<Longrightarrow>
    zahlenwps p2 p (zahlenwps p1 p2 (zahlenwps p p1 (zahlenwps p1 p2 welt))) = welt\<close>
  by(cases \<open>welt\<close>, simp add: swap_unrelated_im_kreis)

lemma zahlenwps_unrelated_im_kreis_map_handlung_helper:
  \<open>p \<noteq> p1 \<Longrightarrow> p \<noteq> p2 \<Longrightarrow>
  map_handlung (zahlenwps p1 p) (map_handlung (zahlenwps p2 p1) (map_handlung (zahlenwps p p2) h))
  = map_handlung (zahlenwps p2 p1) h\<close>
  apply(cases \<open>h\<close>, rename_tac vor nach, simp)
  apply(case_tac \<open>vor\<close>, case_tac \<open>nach\<close>, simp)
  by (metis swap1 swap_unrelated_im_kreis)

(*WOW: ich bekomme ein (zahlenwps p1 p2 welt) innerhalb einer Handlung weg!*)
lemma wfh_unrelated_pullout_wps:
  \<open>p \<noteq> p1 \<Longrightarrow> p \<noteq> p2 \<Longrightarrow>
  \<forall>welt. wohlgeformte_handlungsabsicht zahlenwps welt ha \<Longrightarrow>
    handeln p (zahlenwps p1 p2 welt) ha
      = map_handlung (zahlenwps p2 p1) (handeln p welt ha)\<close>
  thm wohlgeformte_handlungsabsicht_wpsid_wpssym_komm
  thm wohlgeformte_handlungsabsicht_wpsid_simp[of \<open>zahlenwps\<close> \<open>zahlenwps p1 p2 welt\<close> \<open>ha\<close>]
  apply(subgoal_tac \<open>handeln p (zahlenwps p1 p2 welt) ha =
     map_handlung (zahlenwps p1 p) (handeln p1 (zahlenwps p p1 (zahlenwps p1 p2 welt)) ha)\<close>)
   prefer 2
  using wohlgeformte_handlungsabsicht_wpsid_simp[of \<open>zahlenwps\<close> \<open>zahlenwps p1 p2 welt\<close> \<open>ha\<close>]
   apply (simp add: wps_id_def zahlenwps_twice(2); fail)
  apply(simp)
  apply(thin_tac \<open>handeln p (zahlenwps p1 p2 welt) ha = _\<close>)
  thm wohlgeformte_handlungsabsicht_wpsid_simp[of \<open>zahlenwps\<close> \<open>zahlenwps p p1 (zahlenwps p1 p2 welt)\<close> \<open>ha\<close>]
  apply(subgoal_tac \<open>handeln p1 (zahlenwps p p1 (zahlenwps p1 p2 welt)) ha =
     map_handlung (zahlenwps p2 p1) (handeln p2 (zahlenwps p1 p2 (zahlenwps p p1 (zahlenwps p1 p2 welt))) ha)\<close>)
   prefer 2
  using wohlgeformte_handlungsabsicht_wpsid_simp[of \<open>zahlenwps\<close> \<open>(zahlenwps p p1 (zahlenwps p1 p2 welt))\<close> \<open>ha\<close>]
   apply (simp add: wps_id_def zahlenwps_twice(2); fail)
  apply(simp)
  apply(thin_tac \<open>handeln p1 _ ha = _\<close>)
  thm wohlgeformte_handlungsabsicht_wpsid_simp[of \<open>zahlenwps\<close> \<open>(zahlenwps p1 p2 (zahlenwps p p1 (zahlenwps p1 p2 welt)))\<close> \<open>ha\<close>]
  apply(subgoal_tac \<open>handeln p2 (zahlenwps p1 p2 (zahlenwps p p1 (zahlenwps p1 p2 welt))) ha =
     map_handlung (zahlenwps p p2)
      (handeln p (zahlenwps p2 p (zahlenwps p1 p2 (zahlenwps p p1 (zahlenwps p1 p2 welt)))) ha)\<close>)
   prefer 2
  using wohlgeformte_handlungsabsicht_wpsid_simp[of \<open>zahlenwps\<close> \<open>(zahlenwps p1 p2 (zahlenwps p p1 (zahlenwps p1 p2 welt)))\<close> \<open>ha\<close>]
   apply (simp add: wps_id_def zahlenwps_twice(2); fail)
  apply(simp)
  apply(thin_tac \<open>handeln p2 _ ha = _\<close>)
  apply(simp add: zahlenwps_unrelated_im_kreis zahlenwps_unrelated_im_kreis_map_handlung_helper; fail)
  done


(*ziemlich powerful, weil das das wps aus der welt rauszieht! Allerdings aendert sich die handelnde Person.
TODO: kann ich das generalisieren?*)
lemma wohlgeformte_handlungsabsicht_zahlenwps_komm:
  \<open>\<forall>welt. wohlgeformte_handlungsabsicht zahlenwps welt ha \<Longrightarrow>
    handeln p (zahlenwps p1 p2 welt) ha =
            map_handlung (zahlenwps p1 p2) (handeln (swap p1 p2 id p) welt ha)\<close>
  apply(subgoal_tac \<open>wohlgeformte_handlungsabsicht zahlenwps (zahlenwps p1 p2 welt) ha\<close>)
   prefer 2 apply blast
  apply(drule wohlgeformte_handlungsabsicht_mit_wpsid)
  subgoal by (simp add: wps_id_def zahlenwps_twice(2)) 
  apply(case_tac \<open>p=p1\<close>)
   apply(simp add: swap_a)
   apply (metis handlung.collapse handlung.map_sel(1) handlung.map_sel(2) zahlenwps_sym zahlenwps_twice(1))
  apply(case_tac \<open>p=p2\<close>)
   apply(simp add: swap_b)
   apply (metis zahlenwps_twice(2))
  apply(simp add: swap_nothing)
  apply(thin_tac \<open> \<forall>p1a p2a. _ p1a p2a\<close>)
  using wfh_unrelated_pullout_wps
  by (metis zahlenwps_sym)

lemma \<open>pX \<noteq> p1 \<Longrightarrow> pX \<noteq> p2 \<Longrightarrow> p1 \<noteq> p2 \<Longrightarrow>
  zahlenwps pX p1 (zahlenwps pX p2 (zahlenwps p1 pX (zahlenwps p1 p2 welt))) = welt\<close>
  by(cases \<open>welt\<close>, simp add: swap_def Fun.swap_def)

lemma \<open>pX \<noteq> p1 \<Longrightarrow> pX \<noteq> p2 \<Longrightarrow> p1 \<noteq> p2 \<Longrightarrow>
  zahlenwps pX p2 (zahlenwps pX p1 (zahlenwps p2 pX (zahlenwps p1 p2 welt))) = welt\<close>
  by(cases \<open>welt\<close>, simp add: swap_def Fun.swap_def)

lemma zahlenwps_funny_permutation: \<open>p \<noteq> p1 \<Longrightarrow> p \<noteq> p2 \<Longrightarrow>
  zahlenwps p2 p1 (zahlenwps p p2 (zahlenwps p1 p (zahlenwps p1 p2 welt)))
    = zahlenwps p p1 (zahlenwps p2 p welt)\<close>
  apply(cases \<open>welt\<close>, simp add: swap_def Fun.swap_def)
  by auto

lemma zahlenwps_funny_permutation_map_handlung_helper:
  \<open>p \<noteq> p1 \<Longrightarrow> p \<noteq> p2 \<Longrightarrow> p1 \<noteq> p2 \<Longrightarrow>
  map_handlung (zahlenwps p p1) (map_handlung (zahlenwps p2 p) (map_handlung (zahlenwps p1 p2) h))
    = map_handlung (zahlenwps p2 p) ( ( h))\<close>
  apply(cases \<open>h\<close>, rename_tac vor nach, simp)
  apply(case_tac \<open>vor\<close>, case_tac \<open>nach\<close>, simp)
  apply(simp add: swap_def Fun.swap_def)
  by auto

lemma wfh_pullout_wps_helper_same:
  \<open>p1 = p2 \<Longrightarrow>
    handeln p1 (zahlenwps p1 p2 welt) ha = handeln p1 welt ha\<close>
  apply(simp add: zahlenwps_id)
  done

text\<open>Umschreiben mit einem unrelated p. Bin mir noch nicht sicher, ob das was bringt.\<close>
lemma wfh_pullout_wps_move_to_unrelated:
  \<open>\<forall>welt. wohlgeformte_handlungsabsicht zahlenwps welt ha \<Longrightarrow>
    p \<noteq> p1 \<Longrightarrow> p \<noteq> p2 \<Longrightarrow> p1 \<noteq> p2 \<Longrightarrow>
    handeln p1 (zahlenwps p1 p2 welt) ha
      = map_handlung (zahlenwps p2 p) (handeln p1 (zahlenwps p p1 (zahlenwps p2 p welt)) ha)\<close>
  apply(subgoal_tac \<open>handeln p1 (zahlenwps p1 p2 welt) ha =
     map_handlung (zahlenwps p p1) (handeln p (zahlenwps p1 p (zahlenwps p1 p2 welt)) ha)\<close>)
   prefer 2
  using wohlgeformte_handlungsabsicht_wpsid_simp[of \<open>zahlenwps\<close> \<open>zahlenwps p1 p2 welt\<close> \<open>ha\<close>]
   apply (simp add: wps_id_def zahlenwps_twice(2); fail)
  apply(simp)
  apply(thin_tac \<open>handeln p1 _ ha = _\<close>)
  thm wohlgeformte_handlungsabsicht_wpsid_simp[of \<open>zahlenwps\<close> \<open>zahlenwps p1 p (zahlenwps p1 p2 welt)\<close> \<open>ha\<close>]
  apply(subgoal_tac \<open>handeln p (zahlenwps p1 p (zahlenwps p1 p2 welt)) ha =
     map_handlung (zahlenwps p2 p) (handeln p2 (zahlenwps p p2 (zahlenwps p1 p (zahlenwps p1 p2 welt))) ha)\<close>)
   prefer 2
  using wohlgeformte_handlungsabsicht_wpsid_simp[of \<open>zahlenwps\<close> \<open>(zahlenwps p1 p (zahlenwps p1 p2 welt))\<close> \<open>ha\<close>]
   apply (simp add: wps_id_def zahlenwps_twice(2); fail)
  apply(simp)
  apply(thin_tac \<open>handeln p _ ha = _\<close>)
  thm wohlgeformte_handlungsabsicht_wpsid_simp[of \<open>zahlenwps\<close> \<open>zahlenwps p p2 (zahlenwps p1 p (zahlenwps p1 p2 welt))\<close> \<open>ha\<close>]
  apply(subgoal_tac \<open>handeln p2 (zahlenwps p p2 (zahlenwps p1 p (zahlenwps p1 p2 welt))) ha =
     map_handlung (zahlenwps p1 p2)
      (handeln p1 (zahlenwps p2 p1 (zahlenwps p p2 (zahlenwps p1 p (zahlenwps p1 p2 welt)))) ha)\<close>)
   prefer 2
  using wohlgeformte_handlungsabsicht_wpsid_simp[of \<open>zahlenwps\<close> \<open>zahlenwps p p2 (zahlenwps p1 p (zahlenwps p1 p2 welt))\<close> \<open>ha\<close>]
   apply (simp add: wps_id_def zahlenwps_twice(2); fail)
  apply(simp)
  apply(thin_tac \<open>handeln p2 _ ha = _\<close>)
  apply(simp add: zahlenwps_funny_permutation zahlenwps_funny_permutation_map_handlung_helper)
  done

(*
  text\<open>todo. wenn das klappt haetten wir einen kat imp bewiesen. Wird aber nicht klappen.\<close>
lemma "wohlgeformte_handlungsabsicht zahlenwps welt ha \<Longrightarrow>
    kategorischer_imperativ_auf ha welt maxime_altruistischer_fortschritt"

brauchen etwas in die Richtung:
handeln p2 (zahlenwps ich p2 welt) ha) = zahlenwps ich p2 (handeln p2 welt ha)
Warum das nicht gelte wird:
Handlungsabsicht: erschaffen 5 Alice
Welt: Alice=0, Bob=3
wps Alice Bob
links: Alice=8, Bob=0
rechts: Alice=5, Bob=3
da laesst sich auch dann nachtraeglich nichts mehr swappen.



könnte ich eventuell:
kategorischer Imperativ \<Longrightarrow> maxime_und_handlungsabsicht_generalisieren*)

(*>*)


subsection\<open>Maxime für strikten individuellen Fortschritt\<close>
text\<open>In der Maxime \<^const>\<open>individueller_fortschritt\<close> hatten wir
   \<^term>\<open>(meins p nach) \<ge> (meins p vor)\<close>.
  Was wenn wir nun echten Fortschritt fordern:
   \<^term>\<open>(meins p nach) > (meins p vor)\<close>?\<close>

fun individueller_strikter_fortschritt :: \<open>person \<Rightarrow> zahlenwelt handlung \<Rightarrow> bool\<close> where
  \<open>individueller_strikter_fortschritt p (Handlung vor nach) \<longleftrightarrow> (meins p vor) < (meins p nach)\<close>

text\<open>Folgendes ernüchterndes Beispiel zeigt,
die Maxime \<^const>\<open>individueller_strikter_fortschritt\<close> erfüllt nicht den kategorischen Imperativ.
Entweder erlaubt die Maxime keine Assuage über eine Handlungsabsicht,
oder die Handlungsabsicht ist verboten.\<close>
beispiel \<open>erzeuge_beispiel
    zahlenwps (Zahlenwelt (\<euro>(Alice := 5, Bob := 10, Carol := -3)))
    handlungsabsichten
    (Maxime individueller_strikter_fortschritt) =
  Some
    \<lparr>
     bsp_erfuellte_maxime = False,
     bsp_erlaubte_handlungen = [],
     bsp_verbotene_handlungen = [
        Handlungsabsicht alles_kaputt_machen,
        Handlungsabsicht unmoeglich],
     bsp_uneindeutige_handlungen = [
        Handlungsabsicht (erschaffen 5),
        Handlungsabsicht (stehlen 5 10),
        Handlungsabsicht reset]
    \<rparr>\<close>
  by beispiel_tac

text\<open>In keiner Welt ist die Handlung \<^const>\<open>erschaffen\<close> nun \<^const>\<open>moralisch\<close>:\<close>
lemma \<open>\<not> moralisch welt
            (Maxime (\<lambda>ich. individueller_strikter_fortschritt ich)) (Handlungsabsicht (erschaffen 5))\<close>
  apply(cases \<open>welt\<close>)
  by(auto simp add: maxime_zahlenfortschritt_def moralisch_simp handeln_def nachher_handeln.simps)

text\<open> Der Grund ist, dass der Rest der Bevölkerung keine \<^emph>\<open>strikte\<close> Erhöhung des
eigenen Wohlstands erlebt.
Effektiv führt diese Maxime zu einem Gesetz, welches es einem Individuum nicht erlaubt
mehr Besitz zu erschaffen, obwohl niemand dadurch einen Nachteil hat.
Diese Maxime kann meiner Meinung nach nicht gewollt sein.

Beispielsweise ist \<^const>\<open>Bob\<close> das Opfer wenn \<^const>\<open>Alice\<close> sich 5 Wohlstand erschafft,
aber \<^const>\<open>Bob\<close>'s Wohlstand sich dabei nicht erhöht:\<close>
beispiel
  \<open>\<lparr>
      dbg_opfer = Bob, dbg_taeter = Alice,
      dbg_handlung = handeln Alice initialwelt (Handlungsabsicht (erschaffen 5))
     \<rparr>
          \<in> debug_maxime id initialwelt
            (Maxime (\<lambda>ich. individueller_strikter_fortschritt ich)) (Handlungsabsicht (erschaffen 5)) \<close>
  by eval


subsection\<open>Maxime für globales striktes Optimum\<close>
text\<open>Wir bauen nun eine Maxime, die das Individuum vernachlässigt und nur nach dem
globalen Optimum strebt:\<close>
fun globaler_strikter_fortschritt :: \<open>zahlenwelt handlung \<Rightarrow> bool\<close> where
  \<open>globaler_strikter_fortschritt (Handlung vor nach) \<longleftrightarrow> (gesamtbesitz vor) < (gesamtbesitz nach)\<close>

text\<open>Die Maxime ignoriert das \<^term>\<open>ich :: person\<close> komplett.
  
Nun ist es \<^const>\<open>Alice\<close> wieder erlaubt, Wohlstand für sich selbst zu erzeugen,
da sich dadurch auch der Gesamtwohlstand erhöht:\<close>
beispiel \<open>moralisch initialwelt
          (Maxime (\<lambda>ich. globaler_strikter_fortschritt)) (Handlungsabsicht (erschaffen 5))\<close>
  by(eval)    

text\<open>Allerdings ist auch diese Maxime auch sehr grausam, da sie Untätigkeit verbietet:\<close>
beispiel \<open>\<not> moralisch initialwelt
          (Maxime (\<lambda>ich. globaler_strikter_fortschritt)) (Handlungsabsicht (erschaffen 0))\<close>
  by(eval)


text\<open>Unsere initiale einfache \<^const>\<open>maxime_zahlenfortschritt\<close> würde Untätigkeit hier erlauben:\<close>
beispiel \<open>moralisch initialwelt
          maxime_zahlenfortschritt (Handlungsabsicht (erschaffen 0))\<close>
  by(eval)


text\<open>Folgendes Beispiel zeigt, dass die Maxime \<^const>\<open>globaler_strikter_fortschritt\<close>
den kategorischen Imperativ erfüllen kann.
Die Handlungsabsichten sind fast intuitiv in erlaubt und verboten eingeordnet.
  \<^item> \<^term>\<open>erschaffen 5\<close> ist erlaubt.
  \<^item> \<^const>\<open>stehlen\<close>, \<^const>\<open>reset\<close>, \<^const>\<open>alles_kaputt_machen\<close> sind verboten.
    Allerdings ist auch \<^const>\<open>unmoeglich\<close> verboten, da die Maxime Untätigkeit verbietet.
    Dieser letzte Fall ist unschön.
\<close>
beispiel \<open>erzeuge_beispiel
    zahlenwps (Zahlenwelt (\<euro>(Alice := 5, Bob := 10, Carol := -3)))
    handlungsabsichten
    (Maxime (\<lambda>ich. globaler_strikter_fortschritt)) =
  Some
    \<lparr>
     bsp_erfuellte_maxime = True,
     bsp_erlaubte_handlungen = [Handlungsabsicht (erschaffen 5)],
     bsp_verbotene_handlungen = [
      Handlungsabsicht (stehlen 5 10),
      Handlungsabsicht reset,
      Handlungsabsicht alles_kaputt_machen,
      Handlungsabsicht unmoeglich],
     bsp_uneindeutige_handlungen = []\<rparr>\<close>
  by beispiel_tac



subsection\<open>Maxime für globales Optimum\<close>
text\<open>Wir können die Maxime für globalen Fortschritt etwas lockern.\<close>
fun globaler_fortschritt :: \<open>zahlenwelt handlung \<Rightarrow> bool\<close> where
  \<open>globaler_fortschritt (Handlung vor nach) \<longleftrightarrow> (gesamtbesitz vor) \<le> (gesamtbesitz nach)\<close>

text\<open>Untätigkeit ist nun auch hier erlaubt:\<close>
beispiel \<open>moralisch initialwelt
          (Maxime (\<lambda>ich. globaler_fortschritt)) (Handlungsabsicht (erschaffen 0))\<close>
  by(eval)

(*<*)
lemma globaler_fortschritt_kommutiert:
  \<open>wpsm_kommutiert (Maxime (\<lambda>ich::person. globaler_fortschritt)) zahlenwps welt\<close>
  by(simp add: wpsm_kommutiert_def gesamtbesitz_swap zahlenwps_sym handeln_def nachher_handeln.simps)
(*>*)

text\<open>Allerdings ist auch Stehlen erlaubt, da global gesehen, kein Besitz vernichtet wird:\<close>
beispiel \<open>moralisch initialwelt
          (Maxime (\<lambda>ich. globaler_fortschritt)) (Handlungsabsicht (stehlen_nichtwf 5 Bob))\<close>
  by(eval)
beispiel \<open>moralisch initialwelt
          (Maxime (\<lambda>ich. globaler_fortschritt)) (Handlungsabsicht (stehlen 5 10))\<close>
  by(eval)

text\<open>Folgendes Beispiel zeigt, dass die Maxime \<^const>\<open>globaler_fortschritt\<close>
den kategorischen Imperativ erfüllen kann.
Die Handlungsabsichten sind meiner Meinung nach intuitiv
(basierend auf der globalen Betrachtung der Maxime) in erlaubt und verboten eingeordnet.
  \<^item> \<^term>\<open>erschaffen\<close> ist erlaubt.
    Auch \<^const>\<open>stehlen\<close> ist erlaubt, da dabei "doem Kollektiv" kein Besitz verloren geht.
    Untätigkeit wird wieder über \<^const>\<open>unmoeglich\<close> erlaubt.
  \<^item> \<^const>\<open>reset\<close> und \<^const>\<open>alles_kaputt_machen\<close> sind verboten.
\<close>
beispiel \<open>erzeuge_beispiel
    zahlenwps (Zahlenwelt (\<euro>(Alice := 5, Bob := 10, Carol := -3)))
    handlungsabsichten
    (Maxime (\<lambda>ich. globaler_fortschritt)) =
  Some
    \<lparr>
     bsp_erfuellte_maxime = True,
     bsp_erlaubte_handlungen = [
      Handlungsabsicht (erschaffen 5),
      Handlungsabsicht (stehlen 5 10),
      Handlungsabsicht unmoeglich],
     bsp_verbotene_handlungen = [
      Handlungsabsicht reset,
      Handlungsabsicht alles_kaputt_machen],
     bsp_uneindeutige_handlungen = []\<rparr>\<close>
  by beispiel_tac

text\<open>Auch allgemein lässt ich beweisen,
dass diese Maxime für sehr viele Handlungsabsichten den kategorischen Imperativ erfüllt.\<close>
theorem 
  \<open>\<forall>p. maxime_und_handlungsabsicht_generalisieren zahlenwps welt
     (Maxime (\<lambda>ich. globaler_fortschritt)) ha p \<Longrightarrow>
 wohlgeformte_handlungsabsicht zahlenwps welt ha \<Longrightarrow>
  kategorischer_imperativ_auf ha welt (Maxime (\<lambda>ich::person. globaler_fortschritt))\<close>
  apply(erule globale_maxime_katimp)
      apply(cases \<open>welt\<close>, cases \<open>ha\<close>, simp add: ist_noop_def handeln_def nachher_handeln.simps; fail)
     apply(simp add: globaler_fortschritt_kommutiert; fail)
    apply(simp add: zahlenwps_sym)
   apply (simp add: zahlenwps_twice; fail)
  by(simp; fail)

text\<open>Sollte man das Kollektiv höher stellen als das Individuum
und damit effektiv das Recht auf Privateigentum ablehnen (was ich persönlich nicht unterstütze),
so ist \<^const>\<open>globaler_fortschritt\<close> eine Maxime mit schönen Eigenschaften.\<close>



subsection\<open>Ungültige Maxime\<close>
text\<open>Es ist verboten, in einer Maxime eine spezielle Person hardzucoden.
Technisch könnte so eine Maxime den \<^const>\<open>kategorischer_imperativ_auf\<close> erfüllen.
Dies wollen wir aber nicht, da dies gegen die Gleichbehandlung aller Menschen verstoßen würde.
Das Ergebnis wären verdrehte Moralbewertungen,
welche moralische Entscheidungen ausschließlich basierend auf egoistischen Bedürfnissen
der hardgecodeten Personen basieren.
  
Beispielsweise könnten wir \<^const>\<open>individueller_fortschritt\<close> nicht mehr parametrisiert verwenden,
sondern einfach \<^const>\<open>Alice\<close> reinschreiben:\<close>
beispiel \<open>individueller_fortschritt Alice
    = (\<lambda>h. case h of Handlung vor nach \<Rightarrow> (meins Alice vor) \<le> (meins Alice nach))\<close>
  apply(simp add: fun_eq_iff)
  apply(intro allI, rename_tac h, case_tac \<open>h\<close>)
  apply(simp)
  done

text\<open>Solch eine Maxime ist allerdings nicht wohlgeformt.\<close>
beispiel \<open>\<not> wohlgeformte_maxime_auf
    (handeln Alice initialwelt (Handlungsabsicht (stehlen 5 10))) zahlenwps
    (Maxime (\<lambda>ich. individueller_fortschritt Alice))\<close>
  apply(simp add: wohlgeformte_maxime_auf_def)
  apply(rule_tac x=\<open>Alice\<close> in exI)
  apply(rule_tac x=\<open>Bob\<close> in exI)
  apply(code_simp)
  done

text\<open>Sobald wir aufhören \<^const>\<open>Alice\<close> hardzucoden, wird die Maxime wohlgeformt.\<close>
beispiel \<open>wohlgeformte_maxime_auf
    (handeln Alice initialwelt (Handlungsabsicht (stehlen 5 10))) zahlenwps
    (Maxime (\<lambda>ich. individueller_fortschritt ich))\<close>
  apply(simp add: wohlgeformte_maxime_auf_def)
  apply(code_simp)
  done

text\<open>Unser \<^const>\<open>erzeuge_beispiel\<close> verweigert die Arbeit auf nicht-wohlgeformten Maximen.\<close>


subsection\<open>Uneindeutige Handlungen\<close>
text\<open>Bis jetzt haben wir den Schuldigen immer bei der Maxime gesucht,
wenn der kategorische Imperativ nicht erfüllt war und wir somit über bestimmte Handlungsabsichten
keine Aussage treffen konnten.
Gibt es jedoch auch Handlungsabsichten welche vermutlich unabhängig von jeder durchdachten Maxime
keine Bewertung im Sinne des kategorischen Imperativs erlauben?\<close>

text\<open>Folgende Funktion ist inspiriert durch das \<^url>\<open>https://de.wikipedia.org/wiki/Collatz-Problem\<close>.\<close>
fun collatz:: \<open>int \<Rightarrow> int\<close> where
  \<open>collatz n = (if n mod 2 = 0 then n div 2 else 3*n + 1)\<close>
beispiel \<open>collatz 19 = 58\<close> by eval

text\<open>Es folgt eine Handlungsabsicht, basierend auf dem Collatz-Problem.
Das eigentliche Collatz-Problem ist an dieser Stelle nicht relevant,
da wir nur eine Iteration machen.
Allerdings ist das eine spannende Handlungsabsicht,
da diese sowohl den Besitz erhöhen kann, aber auch verringern kann.\<close>
fun collatzh:: \<open>person \<Rightarrow> zahlenwelt \<Rightarrow> zahlenwelt option\<close> where
  \<open>collatzh ich (Zahlenwelt besitz) = Some (Zahlenwelt (besitz( ich := collatz (besitz ich))))\<close>

text\<open>Die Handlungsabsicht \<^const>\<open>collatzh\<close> ist tatsächlich immer wohlgeformt.\<close>
lemma \<open>wohlgeformte_handlungsabsicht zahlenwps welt (Handlungsabsicht collatzh)\<close>
  apply(simp add: wohlgeformte_handlungsabsicht.simps)
  apply(case_tac \<open>welt\<close>, simp add: swap_def fun_eq_iff Fun.swap_def)+
  done


text\<open>Die Handlungsabsicht \<^const>\<open>collatzh\<close> generalisiert nicht mit der
\<^const>\<open>maxime_zahlenfortschritt\<close>.
Dies ist keine große Überraschung, da \<^const>\<open>reset\<close> auch nicht mit dieser Maxime generalisiert
hat und wir die Maxime auch für ungeeignet befunden haben.\<close>
beispiel
  \<open>\<not> maxime_und_handlungsabsicht_generalisieren
       zahlenwps (Zahlenwelt (\<euro>(Alice := 2, Bob := 3)))
       maxime_zahlenfortschritt (Handlungsabsicht collatzh) Alice\<close>
  by eval


text \<open>Für unsere hochgelobte \<^const>\<open>maxime_altruistischer_fortschritt\<close> hingegen
haben wir noch kein Beispiel einer Handlungsabsicht gesehen,
welche nicht mit ihr generalisiert hat.
Dies wirft die Frage auf:
"gibt es überhaupt wohlgeformte Handlungsabsichten, welche nicht mit
\<^const>\<open>maxime_altruistischer_fortschritt\<close> generalisieren?"
Die Antwort liefert \<^const>\<open>collatzh\<close>.\<close>
beispiel
  \<open>\<not> maxime_und_handlungsabsicht_generalisieren
       zahlenwps (Zahlenwelt (\<euro>(Alice := 2, Bob := 3)))
       maxime_altruistischer_fortschritt (Handlungsabsicht collatzh) Alice\<close>
  by eval

text\<open>Wir haben \<^const>\<open>collatzh\<close> bis jetzt immer bei der Bewertung von Maximen ausgeschlossen.
Das Ergebnis vorweg:
Ein kategorischer Imperativ, egal welche vielversprechende Maxime,
gilt nicht für die Handlungsabsicht \<^const>\<open>collatzh\<close>.\<close>

beispiel
  \<open>\<not> kategorischer_imperativ_auf (Handlungsabsicht collatzh)
        initialwelt maxime_zahlenfortschritt\<close>
  \<open>\<not> kategorischer_imperativ_auf (Handlungsabsicht collatzh)
        initialwelt maxime_altruistischer_fortschritt\<close>
  \<open>\<not> kategorischer_imperativ_auf (Handlungsabsicht collatzh)
        initialwelt (Maxime (\<lambda>ich. globaler_fortschritt))\<close>
  by(eval)+


text \<open>
Der Grund ist, oberflächlich gesprochen, dass diese Handlungsabsicht
keinen eindeutigen Charakter hat.
Die Handlungsabsicht kann sowohl Besitz verringern als auch vermehren.
In vielen Welten wird es Leute geben, für die \<^const>\<open>collatzh\<close> eine positive
Wirkung hat.
Jedoch ist \<^const>\<open>collatzh\<close> wohl allgemein nicht \<^const>\<open>moralisch\<close>,
da es normalerweise auch Leute gibt, für die \<^const>\<open>collatzh\<close> eine
negative Auswirkung hat.
Daher kann eine Maxime \<^const>\<open>collatzh\<close> nicht allgemein beurteilen.
Jedoch ist auch diese Meta-Aussage eine spannende Aussage:
Der kategorische Imperativ sagt (dadurch, dass er nicht erfüllt ist),
dass die Handlungsabsicht \<^const>\<open>collatz\<close> nicht durch eine unserer Maximen
beurteilt werden sollte, bzw. sollten wir ein allgemeines Gesetz bauen wollen,
so können wir weder \<^const>\<open>collatzh\<close> uneingeschränkt in die Liste erlaubter Handlungsabsichten
aufnehmen,
noch können wir uneingeschränkt \<^const>\<open>collatzh\<close> uneingeschränkt in die Liste verbotener
Handlungsabsichten aufnehmen.
Oder anders ausgedrückt: können wir ein allgemeines Gesetz wollen,
welches eine Aussage über die Handlungsabsicht \<^const>\<open>collatzh\<close> macht?
Ich argumentiere, dass wir solch ein Gesetz nicht wollen, da

  \<^item> Würden wir nur die Auswirkung von \<^const>\<open>collatzh\<close> betrachten,
    (also die resultierende \<^typ>\<open>'welt handlung\<close>,
     nicht die \<^term_type>\<open>Handlungsabsicht collatzh\<close>)
    so kann diese Auswirkung durchweg positiv sein,
    und wir möchten etwas positives nicht verbieten.
  \<^item> Jedoch hat die Handlungsabsicht auch negative Charakterzüge,
    da wir billigend in Kauf nehmen, dass Besitz vernichtet werden könnte.
    Daher möchten wir diese Absicht auch nicht uneingeschränkt erlauben.
    Besonders deutlich wird dies bei folgender zugespitzten Handlungsabsicht,
    welche billigend die komplette Vernichtung allen Besitzes in Kauf nehmen würde. 
\<close>

definition uneindeutiger_charakter:: \<open>person \<Rightarrow> zahlenwelt \<Rightarrow> zahlenwelt option\<close> where
  \<open>uneindeutiger_charakter \<equiv>
      (\<lambda>ich welt. if meins ich welt mod 2 = 0
                   then alles_kaputt_machen ich welt
                   else erschaffen 5 ich welt)\<close>

lemma \<open>wohlgeformte_handlungsabsicht zahlenwps welt (Handlungsabsicht uneindeutiger_charakter)\<close>
  unfolding uneindeutiger_charakter_def
  apply(rule wohlgeformte_handlungsabsicht_ifI)
    apply(simp add: wohlgeformte_handlungsabsicht_alles_kaputt_machen)
   apply(simp add: wohlgeformte_handlungsabsicht_erschaffen)
  apply(simp add: hlp1 hlp2)
  done

beispiel
  \<open>\<not> kategorischer_imperativ_auf (Handlungsabsicht uneindeutiger_charakter)
        initialwelt maxime_zahlenfortschritt\<close>
  \<open>\<not> kategorischer_imperativ_auf (Handlungsabsicht uneindeutiger_charakter)
        initialwelt maxime_altruistischer_fortschritt\<close>
  \<open>\<not> kategorischer_imperativ_auf (Handlungsabsicht uneindeutiger_charakter)
        initialwelt (Maxime (\<lambda>ich. globaler_fortschritt))\<close>
  by(eval)+

text\<open>Mir gefällt, dass der (extensionale) kategorische Imperativ prinzipiell sagt,
dass wir die Handlungsabsicht \<^const>\<open>uneindeutiger_charakter\<close> nicht in einem allgemeinen
Gesetz behandeln können,
da die potenziellen positiven Auswirkungen im starken Gegensatz
zu der potenziell destruktiven zugrundeliegenden Absicht stehen.\<close>


text\<open>Wenn wir allerdings ausnutzen, dass Handlungsabsichten partiell sein können,
und so den guten und den schlechten Charakter in eigenständige Handlungsabsichten separieren,
so können wir wieder allgemeines Aussage über die beiden Handlungsabsichten machen.\<close>

definition partiell_guter_charakter:: \<open>person \<Rightarrow> zahlenwelt \<Rightarrow> zahlenwelt option\<close> where
  \<open>partiell_guter_charakter \<equiv>
      (\<lambda>ich welt. if meins ich welt mod 2 = 0
                   then None
                   else erschaffen 5 ich welt)\<close>

definition partiell_schlechter_charakter:: \<open>person \<Rightarrow> zahlenwelt \<Rightarrow> zahlenwelt option\<close> where
  \<open>partiell_schlechter_charakter \<equiv>
      (\<lambda>ich welt. if meins ich welt mod 2 = 0
                   then alles_kaputt_machen ich welt
                   else None)\<close>

beispiel \<open>erzeuge_beispiel
    zahlenwps (Zahlenwelt (\<euro>(Alice := 5, Bob := 10, Carol := -3)))
    [Handlungsabsicht partiell_guter_charakter, Handlungsabsicht partiell_schlechter_charakter]
    maxime_altruistischer_fortschritt
= Some
  \<lparr>
   bsp_erfuellte_maxime = True,
   bsp_erlaubte_handlungen = [Handlungsabsicht partiell_guter_charakter],
   bsp_verbotene_handlungen = [Handlungsabsicht partiell_schlechter_charakter],
   bsp_uneindeutige_handlungen = []
  \<rparr>\<close>
  by beispiel_tac

end
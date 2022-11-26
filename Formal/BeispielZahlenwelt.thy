theory BeispielZahlenwelt
imports Zahlenwelt BeispielPerson KategorischerImperativ
begin

section\<open>Beispiel: Zahlenwelt\<close>

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
  lemma \<open>gesamtbesitz (Zahlenwelt \<^url>[Alice := 4, Carol := 8]) = 12\<close> by eval
  lemma \<open>gesamtbesitz (Zahlenwelt \<^url>[Alice := 4, Carol := 4]) = 8\<close> by eval

  text\<open>Mein persönlicher Besitz:\<close>
  fun meins :: \<open>person \<Rightarrow> zahlenwelt \<Rightarrow> int\<close> where
    \<open>meins p (Zahlenwelt besitz) = besitz p\<close>
  
  text\<open>Beispiel:\<close>
  lemma \<open>meins Carol (Zahlenwelt \<^url>[Alice := 8, Carol := 4]) = 4\<close> by eval

  
  text\<open>Um den \<^file>\<open>SchleierNichtwissen.thy\<close> zu implementieren:\<close>
  fun zahlenwps :: \<open>person \<Rightarrow> person \<Rightarrow> zahlenwelt \<Rightarrow> zahlenwelt\<close> where
    \<open>zahlenwps p1 p2 (Zahlenwelt besitz) = Zahlenwelt (swap p1 p2 besitz)\<close>
  
  text\<open>Beispiel:\<close>
  lemma \<open>zahlenwps Alice Carol (Zahlenwelt \<^url>[Alice := 4, Bob := 6, Carol := 8])
    = (Zahlenwelt \<^url>[Alice := 8, Bob := 6, Carol := 4])\<close>
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
  definition \<open>initialwelt \<equiv> Zahlenwelt \<^url>[Alice := 5, Bob := 10, Carol := -3]\<close>



subsection\<open>Ungültige Handlung\<close>
  text\<open>Sobald ich eine konkrete Person in einer Handlungsabsicht hardcode,
  ist diese nicht mehr wohlgeformt.\<close>

  lemma \<open>\<not>wohlgeformte_handlungsabsicht
    zahlenwps (Zahlenwelt \<^url>[Alice := 5, Bob := 10, Carol := -3])
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
  lemma\<open>handeln Alice (Zahlenwelt \<^url>[Alice := 10, Bob := 10, Carol := -3])
                (Handlungsabsicht (stehlen_nichtwf2 5 10))
  = Handlung (Zahlenwelt \<^url>[Alice := 10, Bob := 10, Carol := - 3])
               (Zahlenwelt \<^url>[Alice := 10, Bob := 10, Carol := - 3])\<close> by eval
  lemma\<open>handeln Bob (Zahlenwelt \<^url>[Alice := 10, Bob := 10, Carol := -3])
              (Handlungsabsicht (stehlen_nichtwf2 5 10))
  = Handlung (Zahlenwelt \<^url>[Alice := 10, Bob := 10, Carol := - 3])
             (Zahlenwelt \<^url>[Alice := 5, Bob := 15, Carol := - 3])\<close> by eval
  lemma \<open>wohlgeformte_handlungsabsicht_gegenbeispiel
      zahlenwps
      (Zahlenwelt \<^url>[Alice := 10, Bob := 10, Carol := -3]) (Handlungsabsicht (stehlen_nichtwf2 5 10))
      Alice Bob\<close>
    by(eval)

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
  lemma \<open>wohlgeformte_handlungsabsicht zahlenwps welt (Handlungsabsicht (erschaffen n))\<close>
    apply(case_tac \<open>welt\<close>, simp add: wohlgeformte_handlungsabsicht.simps)
    (*parse tree is
      \<forall>p1 p2. (x (p1 += n)) = swap p2 p1 ((swap p1 p2 x) (p2 += n))
     and I don't like this ambiguity*)
    apply(simp add: swap_def)
    done


  text\<open>Wenn wir das Opfer eindeutig auswählen, ist die Handlung wohlgeformt.
  Allerdings wird niemand bestohlen, wenn das Opfer nicht eindeutig ist.\<close>
  fun stehlen4 :: \<open>int \<Rightarrow> int \<Rightarrow> person \<Rightarrow> zahlenwelt \<Rightarrow> zahlenwelt option\<close> where
      \<open>stehlen4 beute opfer_nach_besitz dieb (Zahlenwelt besitz) =
        map_option Zahlenwelt (stehlen beute opfer_nach_besitz dieb besitz)\<close>



(*<*)
  lemma wohlgeformte_handlungsabsicht_stehlen4:
    \<open>wohlgeformte_handlungsabsicht zahlenwps welt (Handlungsabsicht (stehlen4 n p))\<close>
    apply(cases welt)
    apply(rule wfh_generalize_worldI[OF wohlgeformte_handlungsabsicht_stehlen, where C=Zahlenwelt])
    by(auto)
(*>*)

  text\<open>Reset versetzt die Welt wieder in den Ausgangszustand. Eine sehr destruktive Handlung.\<close>
  fun reset :: \<open>person \<Rightarrow> zahlenwelt \<Rightarrow> zahlenwelt option\<close> where
    \<open>reset ich (Zahlenwelt besitz) = Some (Zahlenwelt (\<lambda> _. 0))\<close>

  text\<open>Der \<^const>\<open>reset\<close> ist im moralischen Sinne vermutlich keine gute Handlung,
  dennoch ist es eine wohlgeformte Handlung, welche wir betrachten können:\<close>
  lemma \<open>wohlgeformte_handlungsabsicht zahlenwps welt (Handlungsabsicht reset)\<close>
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


lemma \<open>alles_kaputt_machen Alice (Zahlenwelt \<^url>[Alice := 5, Bob := 10, Carol := -3])
  = Some (Zahlenwelt \<^url>[Alice := -4, Bob := -4, Carol := -4, Eve := -4])\<close>
  by(code_simp)

  (*TODO: Handlung alles_besser_machen.*)



  fun unmoeglich :: \<open>person \<Rightarrow> zahlenwelt \<Rightarrow> zahlenwelt option\<close> where
    \<open>unmoeglich _ _ = None\<close>

text\<open>Die Beispielhandlungsabsichten, die wir betrachten wollen.\<close>
definition "handlungsabsichten \<equiv> [
  Handlungsabsicht (erschaffen 5),
  Handlungsabsicht (stehlen4 5 10),
  Handlungsabsicht reset,
  Handlungsabsicht alles_kaputt_machen,
  Handlungsabsicht unmoeglich
]"

lemma \<open>ha \<in> set handlungsabsichten \<Longrightarrow> wohlgeformte_handlungsabsicht zahlenwps welt ha\<close>
  apply(simp add: handlungsabsichten_def)
  apply(safe)
  apply(simp_all add: wohlgeformte_handlungsabsicht_stehlen4 wohlgeformte_handlungsabsicht_alles_kaputt_machen)
  apply(simp_all add: wohlgeformte_handlungsabsicht.simps)
    apply(case_tac \<open>welt\<close>, simp add: swap_def fun_eq_iff)+
  done


subsection\<open>Maxime für individuellen Fortschritt\<close>
  text\<open>Wir definieren eine Maxime die besagt,
  dass sich der Besitz einer Person nicht verringern darf:\<close>
  fun individueller_fortschritt :: \<open>person \<Rightarrow> zahlenwelt handlung \<Rightarrow> bool\<close> where
    \<open>individueller_fortschritt p (Handlung vor nach) \<longleftrightarrow> (meins p vor) \<le> (meins p nach)\<close>

  (*loeschen?*)
  definition maxime_zahlenfortschritt :: \<open>(person, zahlenwelt) maxime\<close> where
    \<open>maxime_zahlenfortschritt \<equiv> Maxime (\<lambda>ich. individueller_fortschritt ich)\<close>

  text\<open>\<^const>\<open>reset\<close> erfüllt das nicht, aber das normale \<^const>\<open>stehlen\<close>.\<close>
  (*<*)
    lemma mhg_maxime_zahlenfortschritt_stehlen4:
      \<open>maxime_und_handlungsabsicht_generalisieren zahlenwps welt maxime_zahlenfortschritt (Handlungsabsicht (stehlen4 5 10)) p\<close>
      apply(simp add: maxime_und_handlungsabsicht_generalisieren_def maxime_zahlenfortschritt_def, intro allI impI)
      apply(case_tac \<open>welt\<close>, simp)
      apply(simp add: handeln_def nachher_handeln.simps opfer_eindeutig_nach_besitz_auswaehlen_the_single_elem_enumall)
      apply(auto intro: the_single_elem_exhaust)
      done
  (*>*)

  lemma "ha \<in> {
    Handlungsabsicht (erschaffen 5),
    Handlungsabsicht (stehlen_nichtwf 5 Bob),
    Handlungsabsicht (stehlen4 5 10),
    Handlungsabsicht alles_kaputt_machen,
    Handlungsabsicht unmoeglich
  } \<Longrightarrow> maxime_und_handlungsabsicht_generalisieren zahlenwps welt maxime_zahlenfortschritt ha p"
    apply(simp)
    apply(safe)
       apply(case_tac \<open>welt\<close>, simp add: handeln_def nachher_handeln.simps maxime_und_handlungsabsicht_generalisieren_def maxime_zahlenfortschritt_def; fail)
      apply(case_tac \<open>welt\<close>, simp add: handeln_def nachher_handeln.simps maxime_und_handlungsabsicht_generalisieren_def maxime_zahlenfortschritt_def; fail)
    subgoal using mhg_maxime_zahlenfortschritt_stehlen4 by simp
    subgoal
      by(case_tac \<open>welt\<close>, simp add: handeln_def nachher_handeln.simps maxime_und_handlungsabsicht_generalisieren_def maxime_zahlenfortschritt_def, auto)
      apply(case_tac \<open>welt\<close>, simp add: handeln_def nachher_handeln.simps maxime_und_handlungsabsicht_generalisieren_def maxime_zahlenfortschritt_def; fail)
    done

  text\<open>Nicht alle Handlungen generalisieren, z.B. \<^const>\<open>reset\<close> nicht:\<close>
  lemma
      \<open>\<not> maxime_und_handlungsabsicht_generalisieren
         zahlenwps (Zahlenwelt \<^url>[Alice := 5, Bob := 10, Carol := -3])
         maxime_zahlenfortschritt (Handlungsabsicht (reset)) Alice\<close>
    by eval


  text\<open>Die \<^const>\<open>maxime_zahlenfortschritt\<close> erfüllt \<^bold>\<open>nicht\<close> den \<^const>\<open>kategorischer_imperativ\<close>
  da \<^const>\<open>Alice\<close> nach der Maxime z.B. \<^const>\<open>Bob\<close> bestehlen dürfte.\<close>
  lemma \<open>kategorischer_imperativ_gegenbeispiel
  zahlenwps initialwelt maxime_zahlenfortschritt
  (Handlungsabsicht (stehlen4 1 10))
  Alice
  Bob
  Alice\<close>
    apply(simp add: kategorischer_imperativ_gegenbeispiel_def
        wohlgeformte_handlungsabsicht_stehlen4 mhg_maxime_zahlenfortschritt_stehlen4)
    by(eval)

  (*<*)
  lemma \<open>wpsm_kommutiert (Maxime individueller_fortschritt) zahlenwps welt\<close>
    by(simp add: handeln_def nachher_handeln.simps wpsm_kommutiert_def hlp1 hlp2 zahlenwps_sym)
  (*>*)


  subsubsection\<open>Einzellbeispiele\<close>
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
    lemma \<open>\<not> moralisch initialwelt maxime_zahlenfortschritt (Handlungsabsicht (stehlen4 5 10))\<close>
      by(eval)

    text\<open>Da Schenken und Stehlen in dieser Welt equivalent ist, ist Schenken auch unmoralisch:\<close>  
    lemma \<open>\<not> moralisch welt maxime_zahlenfortschritt (Handlungsabsicht (schenken 5 Bob))\<close>
      by(cases \<open>welt\<close>, auto simp add: maxime_zahlenfortschritt_def moralisch_simp handeln_def nachher_handeln.simps)





  text\<open>TODO: erklaeren\<close>
(*bsp_erfuellte_maxime = None. Aber gleiche handlungen erlaubt und verboten*)
  lemma \<open>erzeuge_beispiel
    zahlenwps initialwelt
    handlungsabsichten
    (Maxime individueller_fortschritt) =
  Some
    \<lparr>bsp_welt = Zahlenwelt \<^url>[Alice := 5, Bob := 10, Carol := -3],
     bsp_erfuellte_maxime = None,
     bsp_erlaubte_handlungen = [Handlungsabsicht (erschaffen 5), Handlungsabsicht unmoeglich],
     bsp_verbotene_handlungen = [Handlungsabsicht (stehlen4 5 10), Handlungsabsicht reset, Handlungsabsicht alles_kaputt_machen]\<rparr>\<close>
    by beispiel




subsection\<open>Maxime für allgemeinen Fortschritt\<close>
  text\<open>Allerdings können wir die Maxime generalisieren, indem wir \<^const>\<open>individueller_fortschritt\<close>
  für jeden fordern. Effektiv wird dabei das \<^term>\<open>ich::person\<close> ignoriert.\<close>
  
  definition maxime_altruistischer_fortschritt :: \<open>(person, zahlenwelt) maxime\<close> where
    \<open>maxime_altruistischer_fortschritt \<equiv> Maxime (\<lambda>ich h. \<forall>pX. individueller_fortschritt pX h)\<close>

  text\<open>Folgendes Beispiel zeigt, dass die \<^const>\<open>maxime_altruistischer_fortschritt\<close>
  den kategorischen Imperativ (für diese \<^const>\<open>initialwelt\<close> und \<^const>\<open>handlungsabsichten\<close>)
  erfüllt; zu sehen an dem \<^const>\<open>Some\<close> Term im \<^const>\<open>bsp_erfuellte_maxime\<close>.

  Die Handlungsabsichten werden eingeordnet wie erwartet:
   \<^const>\<open>erschaffen\<close> ist gut,
   \<^const>\<open>stehlen4\<close>, \<^const>\<open>reset\<close>, \<^const>\<open>alles_kaputt_machen\<close> ist  schlecht.
  \<close>
  lemma \<open>erzeuge_beispiel
    zahlenwps initialwelt
    handlungsabsichten
    maxime_altruistischer_fortschritt =
  Some
    \<lparr>bsp_welt = Zahlenwelt \<^url>[Alice := 5, Bob := 10, Carol := -3],
     bsp_erfuellte_maxime = Some maxime_altruistischer_fortschritt,
     bsp_erlaubte_handlungen = [Handlungsabsicht (erschaffen 5), Handlungsabsicht unmoeglich],
     bsp_verbotene_handlungen = [Handlungsabsicht (stehlen4 5 10), Handlungsabsicht reset, Handlungsabsicht alles_kaputt_machen]\<rparr>\<close>
    by beispiel
  text\<open>Das ist ein sehr schönes Beispiel.\<close>

(*<*)
  lemma wpsm_kommutiert_altruistischer_fortschritt:
    \<open>wpsm_kommutiert
           maxime_altruistischer_fortschritt
           zahlenwps welt\<close>
    apply(simp add: maxime_altruistischer_fortschritt_def wpsm_kommutiert_def handeln_def nachher_handeln.simps)
    apply(safe)
     apply(case_tac \<open>p1 = p2\<close>)
      apply(simp add: zahlenwps_id; fail)
     apply(case_tac \<open>pX = p1\<close>)
      apply(simp)
      apply (metis hlp1 zahlenwps_sym)
     apply (metis hlp2 hlp3 zahlenwps_sym)
    by (metis hlp2 hlp3 zahlenwps_id zahlenwps_sym)
  
  lemma mhg_maxime_altruistischer_fortschritt_stehlen4:
      \<open>maxime_und_handlungsabsicht_generalisieren zahlenwps welt 
      maxime_altruistischer_fortschritt (Handlungsabsicht (stehlen4 1 10)) p\<close>
    apply(simp add: maxime_altruistischer_fortschritt_def maxime_und_handlungsabsicht_generalisieren_def maxime_zahlenfortschritt_def handeln_def nachher_handeln.simps, intro allI impI)
    apply(simp add: ausfuehrbar.simps)
    apply(case_tac \<open>welt\<close>, simp)
    apply(simp add: opfer_eindeutig_nach_besitz_auswaehlen_the_single_elem_enumall)
    apply(simp add: ist_noop_def split: option.split option.split_asm)
    by fastforce
  
  lemma maxime_altruistischer_fortschritt_reset:
      \<open>maxime_und_handlungsabsicht_generalisieren zahlenwps welt 
      maxime_altruistischer_fortschritt (Handlungsabsicht (reset)) p\<close>
      apply(simp add: maxime_altruistischer_fortschritt_def maxime_und_handlungsabsicht_generalisieren_def maxime_zahlenfortschritt_def handeln_def nachher_handeln.simps, intro allI impI)
    apply(case_tac \<open>welt\<close>, simp)
      apply(auto simp add: swap_def split: option.split option.split_asm)
    done
  
  
  lemma wfm_maxime_altruistischer_fortschritt:
    \<open>wohlgeformte_maxime zahlenwps maxime_altruistischer_fortschritt\<close>
    apply(simp add: maxime_altruistischer_fortschritt_def wohlgeformte_maxime_def wohlgeformte_maxime_auf_def handeln_def nachher_handeln.simps, intro allI, rename_tac h p1 p2)
    apply(case_tac \<open>h\<close>, rename_tac vor nach, simp)
    apply(case_tac \<open>vor\<close>, case_tac \<open>nach\<close>, simp)
    apply(simp add: swap_forall)
    done
(*>*)

  
  text\<open>Die Aussage, dass die \<^const>\<open>maxime_altruistischer_fortschritt\<close> den kategorischen Imperativ
  für bestimmte Handlungsabsichten und Welten erfüllt generalisiert noch weiter.
  Für alle Welten und alle wohlgeformten Handlungsabsichten welche mit der Maxime generalisieren
  erfüllt die Maxime den kategorischen Imperativ.\<close>
  theorem \<open>
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

subsection\<open>Maxime für strikten individuellen Fortschritt\<close>
  text\<open>In der Maxime \<^const>\<open>individueller_fortschritt\<close> hatten wir
   \<^term>\<open>(meins p nach) \<ge> (meins p vor)\<close>.
  Was wenn wir nun echten Fortschritt fordern:
   \<^term>\<open>(meins p nach) > (meins p vor)\<close>.\<close>
  
  fun individueller_strikter_fortschritt :: \<open>person \<Rightarrow> zahlenwelt handlung \<Rightarrow> bool\<close> where
    \<open>individueller_strikter_fortschritt p (Handlung vor nach) \<longleftrightarrow> (meins p vor) < (meins p nach)\<close>

  text\<open>TODO: erklaeren. Erfuellt nicht kategorischen imperativ und alles ist verboten\<close>
  lemma \<open>erzeuge_beispiel
    zahlenwps initialwelt
    handlungsabsichten
    (Maxime individueller_strikter_fortschritt) =
  Some
    \<lparr>bsp_welt = Zahlenwelt \<^url>[Alice := 5, Bob := 10, Carol := -3],
     bsp_erfuellte_maxime = None,
     bsp_erlaubte_handlungen = [],
     bsp_verbotene_handlungen = handlungsabsichten\<rparr>\<close>
    by beispiel

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
  
  
  Beispielsweise ist \<^const>\<open>Bob\<close> das Opfer wenn \<^const>\<open>Alice\<close> sich
  5 Wohlstand erschafft, aber \<^const>\<open>Bob\<close>'s Wohlstand sich nicht erhöht:\<close>
  lemma\<open>VerletzteMaxime (Opfer Bob) (Taeter Alice)
          (Handlung [(Alice, 5), (Bob, 10), (Carol, -3)] [(Alice, 10), (Bob, 10), (Carol, -3)])
          \<in> debug_maxime show_zahlenwelt initialwelt
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
  lemma \<open>moralisch initialwelt
          (Maxime (\<lambda>ich. globaler_strikter_fortschritt)) (Handlungsabsicht (erschaffen 5))\<close>
  by(eval)    
  
  text\<open>Allerdings ist auch diese Maxime auch sehr grausam, da sie Untätigkeit verbietet:\<close>
  lemma \<open>\<not>moralisch initialwelt
          (Maxime (\<lambda>ich. globaler_strikter_fortschritt)) (Handlungsabsicht (erschaffen 0))\<close>
    by(eval)


  text\<open>Unsere initiale einfache \<^const>\<open>maxime_zahlenfortschritt\<close> würde Untätigkeit hier erlauben:\<close>
  lemma \<open>moralisch initialwelt
          maxime_zahlenfortschritt (Handlungsabsicht (erschaffen 0))\<close>
    by(eval)


  text\<open>TODO: erklaeren.\<close>
  lemma \<open>erzeuge_beispiel
    zahlenwps initialwelt
    handlungsabsichten
    (Maxime (\<lambda>ich. globaler_strikter_fortschritt)) =
  Some
    \<lparr>bsp_welt = Zahlenwelt \<^url>[Alice := 5, Bob := 10, Carol := -3],
     bsp_erfuellte_maxime = Some (Maxime (\<lambda>ich. globaler_strikter_fortschritt)),
     bsp_erlaubte_handlungen = [Handlungsabsicht (erschaffen 5)],
     bsp_verbotene_handlungen = [
      Handlungsabsicht (stehlen4 5 10),
      Handlungsabsicht reset,
      Handlungsabsicht alles_kaputt_machen,
      Handlungsabsicht unmoeglich]\<rparr>\<close>
    by beispiel



subsection\<open>Maxime für globales Optimum\<close>
  text\<open>Wir können die Maxime für globalen Fortschritt etwas lockern:\<close>
  fun globaler_fortschritt :: \<open>zahlenwelt handlung \<Rightarrow> bool\<close> where
   \<open>globaler_fortschritt (Handlung vor nach) \<longleftrightarrow> (gesamtbesitz vor) \<le> (gesamtbesitz nach)\<close>

  text\<open>Untätigkeit ist nun auch hier erlaubt:\<close>
  lemma \<open>moralisch initialwelt
          (Maxime (\<lambda>ich. globaler_fortschritt)) (Handlungsabsicht (erschaffen 0))\<close>
    by(eval)


(*<*)
  lemma globaler_fortschritt_kommutiert:
    \<open>wpsm_kommutiert (Maxime (\<lambda>ich::person. globaler_fortschritt)) zahlenwps welt\<close>
    by(simp add: wpsm_kommutiert_def gesamtbesitz_swap zahlenwps_sym handeln_def nachher_handeln.simps)
(*>*)
  
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


  text\<open>Allerdings ist auch Stehlen erlaubt, da global gesehen, kein Besitz vernichtet wird:\<close>
  lemma \<open>moralisch initialwelt
          (Maxime (\<lambda>ich. globaler_fortschritt)) (Handlungsabsicht (stehlen_nichtwf 5 Bob))\<close>
    by(eval)
  lemma \<open>moralisch initialwelt
          (Maxime (\<lambda>ich. globaler_fortschritt)) (Handlungsabsicht (stehlen4 5 10))\<close>
    by(eval)

  text\<open>TODO: erklaeren.\<close>
  lemma \<open>erzeuge_beispiel
    zahlenwps initialwelt
    handlungsabsichten
    (Maxime (\<lambda>ich. globaler_fortschritt)) =
  Some
    \<lparr>bsp_welt = Zahlenwelt \<^url>[Alice := 5, Bob := 10, Carol := -3],
     bsp_erfuellte_maxime = Some (Maxime (\<lambda>ich. globaler_fortschritt)),
     bsp_erlaubte_handlungen = [
      Handlungsabsicht (erschaffen 5),
      Handlungsabsicht (stehlen4 5 10),
      Handlungsabsicht unmoeglich],
     bsp_verbotene_handlungen = [
      Handlungsabsicht reset,
      Handlungsabsicht alles_kaputt_machen]\<rparr>\<close>
    by beispiel

subsection\<open>Ungültige Maxime\<close>
  text\<open>Es ist verboten, in einer Maxime eine spezielle Person hardzucoden.
  Da dies gegen die Gleichbehandlung aller Menschen verstoßen würde.
  
  Beispielsweise könnten wir \<^const>\<open>individueller_fortschritt\<close> nicht mehr parametrisiert verwenden,
  sondern einfach \<^const>\<open>Alice\<close> reinschreiben:
  \<close>
  lemma \<open>individueller_fortschritt Alice
    = (\<lambda>h. case h of Handlung vor nach \<Rightarrow> (meins Alice vor) \<le> (meins Alice nach))\<close>
    apply(simp add: fun_eq_iff)
    apply(intro allI, rename_tac h, case_tac \<open>h\<close>)
    apply(simp)
    done
  lemma "\<not>wohlgeformte_maxime_auf
    (handeln Alice initialwelt (Handlungsabsicht (stehlen4 5 10))) zahlenwps
    (Maxime (\<lambda>ich. individueller_fortschritt Alice))"
    apply(simp add: wohlgeformte_maxime_auf_def)
    apply(rule_tac x=Alice in exI)
    apply(rule_tac x=Bob in exI)
    apply(code_simp)
    done
  lemma "wohlgeformte_maxime_auf
    (handeln Alice initialwelt (Handlungsabsicht (stehlen4 5 10))) zahlenwps
    (Maxime (\<lambda>ich. individueller_fortschritt ich))"
    apply(simp add: wohlgeformte_maxime_auf_def)
    apply(code_simp)
    done

end
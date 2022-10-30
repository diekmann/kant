theory BeispielZahlenwelt
imports Zahlenwelt Simulation Gesetze BeispielPerson Swap
begin

section\<open>Beispiel: Zahlenwelt\<close>

  text\<open>Wir nehmen an, die Welt lässt sich durch eine Zahl darstellen,
  die den Besitz einer Person modelliert.
  
  Der Besitz ist als ganze Zahl \<^typ>\<open>int\<close> modelliert und kann auch beliebig negativ werden.\<close>
  datatype zahlenwelt = Zahlenwelt
    \<open>person \<Rightarrow> int \<comment> \<open>besitz: Besitz jeder Person.\<close>\<close>
  
  fun gesamtbesitz :: \<open>zahlenwelt \<Rightarrow> int\<close> where
    \<open>gesamtbesitz (Zahlenwelt besitz) = sum_list (map besitz Enum.enum)\<close>

  lemma \<open>gesamtbesitz (Zahlenwelt besitz) = (\<Sum>p\<leftarrow>[Alice,Bob,Carol,Eve]. besitz p)\<close>
    by(simp add: enum_person_def)
  
  
  lemma \<open>gesamtbesitz (Zahlenwelt \<^url>[Alice := 4, Carol := 8]) = 12\<close> by eval
  lemma \<open>gesamtbesitz (Zahlenwelt \<^url>[Alice := 4, Carol := 4]) = 8\<close> by eval

  
  fun meins :: \<open>person \<Rightarrow> zahlenwelt \<Rightarrow> int\<close> where
    \<open>meins p (Zahlenwelt besitz) = besitz p\<close>
  
  lemma \<open>meins Carol (Zahlenwelt \<^url>[Alice := 8, Carol := 4]) = 4\<close> by eval
  
  (*<*)
  definition \<open>show_zahlenwelt w \<equiv> case w of Zahlenwelt besitz \<Rightarrow> show_num_fun besitz\<close>
  fun delta_zahlenwelt :: \<open>(zahlenwelt, person, int) delta\<close> where
    \<open>delta_zahlenwelt (Handlung (Zahlenwelt vor_besitz) (Zahlenwelt nach_besitz)) =
        Aenderung.delta_num_fun (Handlung vor_besitz nach_besitz)\<close>
  (*>*)


  fun zahlenwelt_personen_swap :: \<open>person \<Rightarrow> person \<Rightarrow> zahlenwelt \<Rightarrow> zahlenwelt\<close> where
    \<open>zahlenwelt_personen_swap p1 p2 (Zahlenwelt besitz) = Zahlenwelt (swap p1 p2 besitz)\<close>
  
  lemma \<open>zahlenwelt_personen_swap Alice Carol (Zahlenwelt \<^url>[Alice := 4, Bob := 6, Carol := 8])
    = (Zahlenwelt \<^url>[Alice := 8, Bob := 6, Carol := 4])\<close>
    by eval

  (*<*)
  lemma zahlenwelt_personen_swap_sym:
    \<open>zahlenwelt_personen_swap p1 p2 welt = zahlenwelt_personen_swap p2 p1 welt\<close>
    by(cases \<open>welt\<close>, simp add: swap_symmetric)

  lemma zahlenwelt_personen_swap_id: \<open>zahlenwelt_personen_swap p p w = w\<close>
    by(cases \<open>w\<close>, simp)


  lemma gesamtbesitz_swap:
    \<open>gesamtbesitz (zahlenwelt_personen_swap p1 p2 welt) = gesamtbesitz welt\<close>
    apply(cases \<open>welt\<close>, simp)
    apply(rule sum_list_swap)
    using enum_class.in_enum enum_class.enum_distinct by auto
  (*>*)

subsection\<open>Handlungen\<close>

  text\<open>Die folgende Handlung erschafft neuen Besitz aus dem Nichts:\<close>
  fun erschaffen :: \<open>nat \<Rightarrow> person \<Rightarrow> zahlenwelt \<Rightarrow> zahlenwelt\<close> where
    \<open>erschaffen i p (Zahlenwelt besitz) = Zahlenwelt (besitz(p += int i))\<close>
  lemma \<open>wohlgeformte_handlungsabsicht zahlenwelt_personen_swap welt (Handlungsabsicht (erschaffen n))\<close>
    apply(simp add: wohlgeformte_handlungsabsicht_def)
    apply(intro allI, case_tac \<open>welt\<close>, simp)
    apply(simp add: swap_def)
    done
  
  fun stehlen :: \<open>int \<Rightarrow> person \<Rightarrow> person \<Rightarrow> zahlenwelt \<Rightarrow> zahlenwelt\<close> where
    \<open>stehlen beute opfer dieb (Zahlenwelt besitz) =
        Zahlenwelt (besitz(opfer -= beute)(dieb += beute))\<close>
  text\<open>Die Handlung \<^const>\<open>stehlen\<close> diskriminiert und ist damit nicht wohlgeformt:\<close>
  lemma "wohlgeformte_handlungsabsicht_gegenbeispiel zahlenwelt_personen_swap
      (Zahlenwelt (\<lambda>x. 0)) (Handlungsabsicht (stehlen 5 Bob))
      Alice Bob"
    by(eval)

  text\<open>Wir versuchen, das Opfer nach Besitz auszuwählen, nicht nach Namen.
  Nach unserer Definition ist der Besitz ein Merkmal, nach dem man diskriminieren darf.
  Man darf nur nicht nach Eigenschaften der \<^typ>\<open>person\<close> diskriminieren, sondern nur
  nach Eigenschaften der \<^typ>\<open>zahlenwelt\<close>.\<close>
  fun opfer_nach_besitz_auswaehlen :: \<open>int \<Rightarrow> ('person \<Rightarrow> int) \<Rightarrow> 'person list \<Rightarrow> 'person option\<close> where
    \<open>opfer_nach_besitz_auswaehlen _ _ [] = None\<close>
  | \<open>opfer_nach_besitz_auswaehlen b besitz (p#ps) = 
      (if besitz p = b then Some p else opfer_nach_besitz_auswaehlen b besitz ps)\<close>
  
  fun stehlen2 :: \<open>int \<Rightarrow> int \<Rightarrow> person \<Rightarrow> zahlenwelt \<Rightarrow> zahlenwelt\<close> where
      \<open>stehlen2 beute opfer_nach_besitz dieb (Zahlenwelt besitz) =
        (case opfer_nach_besitz_auswaehlen opfer_nach_besitz besitz Enum.enum
           of None \<Rightarrow> (Zahlenwelt besitz)
            | Some opfer \<Rightarrow> Zahlenwelt (besitz(opfer -= beute)(dieb += beute))
        )\<close>
  text\<open>Leider ist diese Funktion auch diskriminierend:
  Wenn es mehrere potenzielle Opfer mit dem gleichen Besitz gibt,
  dann bestimmt die Reihenfolge in \<^term>\<open>Enum.enum\<close> wer bestohlen wird.
  Diese Reihenfolge ist wieder eine Eigenschaft von \<^typ>\<open>person\<close> und nicht \<^typ>\<open>zahlenwelt\<close>.\<close>
  lemma\<open>handeln Alice (Zahlenwelt \<^url>[Alice := 10, Bob := 10, Carol := -3])
                (Handlungsabsicht (stehlen2 5 10))
  = Handlung (Zahlenwelt \<^url>[Alice := 10, Bob := 10, Carol := - 3])
               (Zahlenwelt \<^url>[Alice := 10, Bob := 10, Carol := - 3])\<close> by eval
  lemma\<open>handeln Bob (Zahlenwelt \<^url>[Alice := 10, Bob := 10, Carol := -3])
              (Handlungsabsicht (stehlen2 5 10))
  = Handlung (Zahlenwelt \<^url>[Alice := 10, Bob := 10, Carol := - 3])
             (Zahlenwelt \<^url>[Alice := 5, Bob := 15, Carol := - 3])\<close> by eval
  lemma \<open>wohlgeformte_handlungsabsicht_gegenbeispiel
      zahlenwelt_personen_swap
      (Zahlenwelt \<^url>[Alice := 10, Bob := 10, Carol := -3]) (Handlungsabsicht (stehlen2 5 10))
      Alice Bob\<close>
    by(eval)



  text\<open>Wenn wir das Opfer allerdings eindeutig auswählen, ist die Handlung wohlgeformt.
  Allerdings wird niemand bestohlen, wenn das Opfer nicht eindeutig ist.\<close>
  fun stehlen4 :: \<open>int \<Rightarrow> int \<Rightarrow> person \<Rightarrow> zahlenwelt \<Rightarrow> zahlenwelt\<close> where
      \<open>stehlen4 beute opfer_nach_besitz dieb (Zahlenwelt besitz) =
        (case opfer_eindeutig_nach_besitz_auswaehlen opfer_nach_besitz besitz Enum.enum
           of None \<Rightarrow> (Zahlenwelt besitz)
            | Some opfer \<Rightarrow> Zahlenwelt (besitz(opfer -= beute)(dieb += beute))
        )\<close>


  lemma wohlgeformte_handlungsabsicht_stehlen4:
    \<open>wohlgeformte_handlungsabsicht zahlenwelt_personen_swap welt (Handlungsabsicht (stehlen4 n p))\<close>
      apply(simp add: wohlgeformte_handlungsabsicht_def)
      apply(intro allI, case_tac \<open>welt\<close>, simp)
      apply(simp add: opfer_eindeutig_nach_besitz_auswaehlen_swap_enumall)
      apply(simp add: opfer_eindeutig_nach_besitz_auswaehlen_the_single_elem_enumall)
      apply(simp add: the_single_elem)
      apply(safe)
       apply (simp add: swap_def; fail)
      by (simp add: fun_upd_twist swap_def)


  fun schenken :: \<open>int \<Rightarrow> person \<Rightarrow> person \<Rightarrow> zahlenwelt \<Rightarrow> zahlenwelt\<close> where
    \<open>schenken betrag empfaenger schenker (Zahlenwelt besitz) =
        Zahlenwelt (besitz(schenker -= betrag)(empfaenger += betrag))\<close>
  
  text\<open>Da wir ganze Zahlen verwenden und der Besitz auch beliebig negativ werden kann,
  ist Stehlen äquivalent dazu einen negativen Betrag zu verschenken:\<close>
  lemma stehlen_ist_schenken: \<open>stehlen i = schenken (-i)\<close>
    apply(simp add: fun_eq_iff)
    apply(intro allI, rename_tac p1 p2 welt, case_tac \<open>welt\<close>)
    by auto
  
  text\<open>Das Modell ist nicht ganz perfekt, .... Aber passt schon um damit zu spielen.\<close>


  text\<open>Reset versetzt die Welt wieder in den Ausgangszustand. Eine sehr destruktive Handlung.\<close>
  fun reset :: \<open>person \<Rightarrow> zahlenwelt \<Rightarrow> zahlenwelt\<close> where
    \<open>reset ich (Zahlenwelt besitz) = Zahlenwelt (\<lambda> _. 0)\<close>

  text\<open>Der \<^const>\<open>reset\<close> ist im moralischen Sinne vermutlich keine gute Handlung,
  dennoch ist es eine wohlgeformte Handlung, welche wir betrachten können:\<close>
  lemma \<open>wohlgeformte_handlungsabsicht zahlenwelt_personen_swap welt (Handlungsabsicht reset)\<close>
      apply(simp add: wohlgeformte_handlungsabsicht_def)
     by(intro allI, case_tac \<open>welt\<close>, simp add: swap_def fun_eq_iff)


subsection\<open>Setup\<close>
  text\<open>\<^const>\<open>Alice\<close> hat Besitz, \<^const>\<open>Bob\<close> ist reicher, \<^const>\<open>Carol\<close> hat Schulden.\<close>
  definition \<open>initialwelt \<equiv> Zahlenwelt \<^url>[Alice := 5, Bob := 10, Carol := -3]\<close>
  
  text\<open>Wir nehmen an unsere handelnde Person ist \<^const>\<open>Alice\<close>.\<close>
  
  definition \<open>beispiel_case_law_absolut maxime handlungsabsicht \<equiv>
    simulateOne
      (SimConsts
        Alice
        maxime
        (printable_case_law_ableiten_absolut show_zahlenwelt))
      5 handlungsabsicht initialwelt (Gesetz {})\<close>
  definition \<open>beispiel_case_law_relativ maxime handlungsabsicht \<equiv>
    simulateOne
      (SimConsts
        Alice
        maxime
        (case_law_ableiten_relativ delta_zahlenwelt))
      10 handlungsabsicht initialwelt (Gesetz {})\<close>

subsection\<open>Alice erzeugt 5 Wohlstand für sich.\<close>

  text\<open>Wir definieren eine Maxime die besagt,
  dass sich der Besitz einer Person nicht verringern darf:\<close>
  fun individueller_fortschritt :: \<open>person \<Rightarrow> zahlenwelt handlung \<Rightarrow> bool\<close> where
    \<open>individueller_fortschritt p (Handlung vor nach) \<longleftrightarrow> (meins p vor) \<le> (meins p nach)\<close>
  definition maxime_zahlenfortschritt :: \<open>(person, zahlenwelt) maxime\<close> where
    \<open>maxime_zahlenfortschritt \<equiv> Maxime (\<lambda>ich. individueller_fortschritt ich)\<close>


  lemma \<open>maxime_und_handlungsabsicht_generalisieren maxime_zahlenfortschritt (Handlungsabsicht (erschaffen 5)) p\<close>
    apply(simp add: maxime_und_handlungsabsicht_generalisieren_def maxime_zahlenfortschritt_def, intro allI)
    apply(case_tac \<open>w1\<close>, case_tac \<open>w2\<close>, simp)
    done
  
  lemma \<open>maxime_und_handlungsabsicht_generalisieren maxime_zahlenfortschritt (Handlungsabsicht (stehlen 5 Bob)) p\<close>
    apply(simp add: maxime_und_handlungsabsicht_generalisieren_def maxime_zahlenfortschritt_def, intro allI)
    apply(case_tac \<open>w1\<close>, case_tac \<open>w2\<close>, simp)
    done

  lemma mhg_maxime_zahlenfortschritt_stehlen4:
    \<open>maxime_und_handlungsabsicht_generalisieren maxime_zahlenfortschritt (Handlungsabsicht (stehlen4 1 10)) p\<close>
    apply(simp add: maxime_und_handlungsabsicht_generalisieren_def maxime_zahlenfortschritt_def, intro allI)
    apply(case_tac \<open>w1\<close>, case_tac \<open>w2\<close>, simp)
    apply(simp add: opfer_eindeutig_nach_besitz_auswaehlen_the_single_elem_enumall)
    apply(auto intro: the_single_elem_exhaust)
    done

  text\<open>In jeder Welt ist die Handlung \<^const>\<open>moralisch\<close>:\<close>
  lemma \<open>moralisch welt maxime_zahlenfortschritt (Handlungsabsicht (erschaffen 5))\<close>
    apply(cases \<open>welt\<close>)
    by(simp add: maxime_zahlenfortschritt_def moralisch_simp)


  (*AWESOME!*)
  text\<open>Die \<^const>\<open>maxime_zahlenfortschritt\<close> erfüllt nicht den \<^const>\<open>kategorischer_imperativ\<close>
  da \<^const>\<open>Alice\<close> nach der Maxime z.B. \<^const>\<open>Bob\<close> bestehlen würde.\<close>
  lemma \<open>\<not> kategorischer_imperativ zahlenwelt_personen_swap initialwelt maxime_zahlenfortschritt\<close>
    apply(simp add: kategorischer_imperativ_def maxime_zahlenfortschritt_def moralisch_simp)
    apply(rule_tac x=\<open>Handlungsabsicht (stehlen4 1 10)\<close> in exI)
    apply(simp add: wohlgeformte_handlungsabsicht_stehlen4)
    apply(intro conjI)
     apply(rule_tac x=\<open>Alice\<close> in exI)
     apply(intro conjI allI)
    using mhg_maxime_zahlenfortschritt_stehlen4[simplified maxime_zahlenfortschritt_def] apply blast
     apply(simp add: initialwelt_def, eval)
    apply(rule_tac x=\<open>Bob\<close> in exI)
    apply(rule_tac x=\<open>Alice\<close> in exI)
    apply(simp add: initialwelt_def, eval)
    done

lemma hlp1: \<open>meins p1 (zahlenwelt_personen_swap p1 p2 welt) = meins p2 welt\<close>
  by(cases \<open>welt\<close>, simp add: swap_def)
lemma hlp2: \<open>meins p2 (zahlenwelt_personen_swap p1 p2 welt) = meins p1 welt\<close>
  by(cases \<open>welt\<close>, simp add: swap_def)

lemma hlp3: \<open>p1 \<noteq> p2 \<Longrightarrow> p \<noteq> p1 \<Longrightarrow> p \<noteq> p2 \<Longrightarrow>
       meins p (zahlenwelt_personen_swap p1 p2 welt) = meins p welt\<close>
  by(cases \<open>welt\<close>, simp add: swap_def)

lemma \<open>wpsm_kommutiert (Maxime individueller_fortschritt) zahlenwelt_personen_swap welt\<close>
  by(simp add: wpsm_kommutiert_def hlp1 hlp2 zahlenwelt_personen_swap_sym)


(*TODO: Diese Maxime braucht einen Namen!*)
lemma \<open>wpsm_kommutiert
         (Maxime (\<lambda>(ich::person) h. (\<forall>pX. individueller_fortschritt pX h)))
         zahlenwelt_personen_swap welt\<close>
  apply(simp add: wpsm_kommutiert_def)
  apply(safe)
   apply(case_tac \<open>p1 = p2\<close>)
    apply(simp add: zahlenwelt_personen_swap_id; fail)
   apply(case_tac \<open>pX = p1\<close>)
    apply(simp)
    apply (metis hlp1 zahlenwelt_personen_swap_sym)
   apply (metis hlp2 hlp3 zahlenwelt_personen_swap_sym)
  by (metis hlp2 hlp3 zahlenwelt_personen_swap_id zahlenwelt_personen_swap_sym)
  

(*AWESOME!*)
  lemma \<open>kategorischer_imperativ zahlenwelt_personen_swap welt
    (Maxime (\<lambda>(ich::person) h. (\<forall>pX. individueller_fortschritt pX h)))\<close>
    apply(rule altruistische_maxime_katimp)
       apply (simp add: wpsm_kommutiert_def hlp1 hlp2 zahlenwelt_personen_swap_sym; fail)
      apply (simp add: wpsm_unbeteiligt1_def hlp3; fail)
     apply (simp add: wpsm_unbeteiligt2_def hlp3; fail)
    by (simp add: zahlenwelt_personen_swap_sym)


  text\<open>Alice kann beliebig oft 5 Wohlstand für sich selbst erschaffen.
  Das entstehende Gesetz ist nicht sehr gut, da es einfach jedes Mal einen
  Snapshot der Welt aufschreibt und nicht sehr generisch ist.\<close>
  lemma \<open>beispiel_case_law_absolut maxime_zahlenfortschritt (Handlungsabsicht (erschaffen 5))
  =
  Gesetz
  {(\<section> 5,
    Rechtsnorm
     (Tatbestand ([(Alice, 25), (Bob, 10), (Carol, - 3)], [(Alice, 30), (Bob, 10), (Carol, - 3)]))
     (Rechtsfolge Erlaubnis)),
   (\<section> 4,
    Rechtsnorm
     (Tatbestand ([(Alice, 20), (Bob, 10), (Carol, - 3)], [(Alice, 25), (Bob, 10), (Carol, - 3)]))
     (Rechtsfolge Erlaubnis)),
   (\<section> 3,
    Rechtsnorm
     (Tatbestand ([(Alice, 15), (Bob, 10), (Carol, - 3)], [(Alice, 20), (Bob, 10), (Carol, - 3)]))
     (Rechtsfolge Erlaubnis)),
   (\<section> 2,
    Rechtsnorm
     (Tatbestand ([(Alice, 10), (Bob, 10), (Carol, - 3)], [(Alice, 15), (Bob, 10), (Carol, - 3)]))
     (Rechtsfolge Erlaubnis)),
   (\<section> 1,
    Rechtsnorm
     (Tatbestand ([(Alice, 5), (Bob, 10), (Carol, - 3)], [(Alice, 10), (Bob, 10), (Carol, - 3)]))
     (Rechtsfolge Erlaubnis))}
  \<close> by eval
  
  
  text\<open>Die gleiche Handlung, wir schreiben aber nur die Änderung der Welt ins Gesetz:\<close>
  lemma \<open>beispiel_case_law_relativ maxime_zahlenfortschritt (Handlungsabsicht (erschaffen 5)) =
    Gesetz
    {(\<section> 1, Rechtsnorm (Tatbestand [Gewinnt Alice 5]) (Rechtsfolge Erlaubnis))}\<close>
    by eval

  (*TODO: Beispiele mit der guten maxime!*)
  lemma \<open>beispiel_case_law_relativ
    (Maxime (\<lambda>(ich::person) h. (\<forall>pX. individueller_fortschritt pX h))) (Handlungsabsicht (erschaffen 5)) =
  Gesetz {(\<section> 1, Rechtsnorm (Tatbestand [Gewinnt Alice 5]) (Rechtsfolge Erlaubnis))}\<close>
  by eval

subsection\<open>Kleine Änderung in der Maxime\<close>
  text\<open>In der Maxime \<^const>\<open>individueller_fortschritt\<close> hatten wir
   \<^term>\<open>(meins p nach) \<ge> (meins p vor)\<close>.
  Was wenn wir nun echten Fortschritt fordern:
   \<^term>\<open>(meins p nach) > (meins p vor)\<close>.\<close>
  
  fun individueller_strikter_fortschritt :: \<open>person \<Rightarrow> zahlenwelt handlung \<Rightarrow> bool\<close> where
    \<open>individueller_strikter_fortschritt p (Handlung vor nach) \<longleftrightarrow> (meins p vor) < (meins p nach)\<close>

  text\<open>Nun ist es \<^const>\<open>Alice\<close> verboten Wohlstand für sich selbst zu erzeugen.\<close>
  lemma \<open>beispiel_case_law_relativ
          (Maxime (\<lambda>ich. individueller_strikter_fortschritt ich))
          (Handlungsabsicht (erschaffen 5)) =
    Gesetz {(\<section> 1, Rechtsnorm (Tatbestand [Gewinnt Alice 5]) (Rechtsfolge Verbot))}\<close>
    by eval
    
  text\<open>In keiner Welt ist die Handlung nun \<^const>\<open>moralisch\<close>:\<close>
lemma \<open>\<not> moralisch welt
          (Maxime (\<lambda>ich. individueller_strikter_fortschritt ich)) (Handlungsabsicht (erschaffen 5))\<close>
    apply(cases \<open>welt\<close>)
    by(auto simp add: maxime_zahlenfortschritt_def moralisch_simp)

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


subsection\<open>Maxime für Globales Optimum\<close>
  text\<open>Wir bauen nun eine Maxime, die das Individuum vernachlässigt und nur nach dem
  globalen Optimum strebt:\<close>
  fun globaler_strikter_fortschritt :: \<open>zahlenwelt handlung \<Rightarrow> bool\<close> where
    \<open>globaler_strikter_fortschritt (Handlung vor nach) \<longleftrightarrow> (gesamtbesitz vor) < (gesamtbesitz nach)\<close>
  
  text\<open>Die Maxime ignoriert das \<^term>\<open>ich :: person\<close> komplett.
  
  Nun ist es \<^const>\<open>Alice\<close> wieder erlaubt, Wohlstand für sich selbst zu erzeugen,
  da sich dadurch auch der Gesamtwohlstand erhöht:\<close>
  lemma \<open>beispiel_case_law_relativ
          (Maxime (\<lambda>ich. globaler_strikter_fortschritt))
          (Handlungsabsicht (erschaffen 5)) =
    Gesetz {(\<section> 1, Rechtsnorm (Tatbestand [Gewinnt Alice 5]) (Rechtsfolge Erlaubnis))}\<close>
    by eval


  lemma \<open>moralisch initialwelt
          (Maxime (\<lambda>ich. globaler_strikter_fortschritt)) (Handlungsabsicht (erschaffen 5))\<close>
  by(eval)
    
    
  
  text\<open>Allerdings ist auch diese Maxime auch sehr grausam, da sie Untätigkeit verbietet:\<close>
  lemma \<open>beispiel_case_law_relativ
          (Maxime (\<lambda>ich. globaler_strikter_fortschritt))
          (Handlungsabsicht (erschaffen 0)) =
    Gesetz {(\<section> 1, Rechtsnorm (Tatbestand []) (Rechtsfolge Verbot))}\<close>
    by eval


  text\<open>Unsere initiale einfache \<^const>\<open>maxime_zahlenfortschritt\<close> würde Untätigkeit hier erlauben:\<close>
  lemma \<open>beispiel_case_law_relativ
          maxime_zahlenfortschritt
          (Handlungsabsicht (erschaffen 0)) =
    Gesetz {(\<section> 1, Rechtsnorm (Tatbestand []) (Rechtsfolge Erlaubnis))}\<close>
    by eval

  text\<open>Wir können die Maxime für globalen Fortschritt etwas lockern:\<close>
  fun globaler_fortschritt :: \<open>zahlenwelt handlung \<Rightarrow> bool\<close> where
   \<open>globaler_fortschritt (Handlung vor nach) \<longleftrightarrow> (gesamtbesitz vor) \<le> (gesamtbesitz nach)\<close>

  text\<open>Untätigkeit ist nun auch hier erlaubt:\<close>
  lemma\<open>beispiel_case_law_relativ
            (Maxime (\<lambda>ich. globaler_fortschritt))
            (Handlungsabsicht (erschaffen 0))
    =
    Gesetz {(\<section> 1, Rechtsnorm (Tatbestand []) (Rechtsfolge Erlaubnis))}\<close>
    by eval

(*TODO: eine Person als handelnde Person in eine Handlungsabsicht
 hardzucoden ist illegal!

eine Person also Opfer hardzucoden muss aber gehen.
Handlungsabsicht (stehlen 5 Bob)
sollte eine wohlgeformte Handlungsabsicht sein.
*)
lemma \<open>\<not>wohlgeformte_handlungsabsicht
  zahlenwelt_personen_swap initialwelt
  (Handlungsabsicht (\<lambda>ich w. if ich = Alice then w else Zahlenwelt (\<lambda>_. 0)))\<close>
  apply(simp add: initialwelt_def wohlgeformte_handlungsabsicht_def swap_def)
  apply(eval)
  done


lemma \<open>\<not> maxime_und_handlungsabsicht_generalisieren maxime_zahlenfortschritt
        (Handlungsabsicht (\<lambda>ich w. if ich = Alice then w else Zahlenwelt (\<lambda>_. 0))) Carol\<close>
  apply(simp add: maxime_zahlenfortschritt_def maxime_und_handlungsabsicht_generalisieren_def)
  apply(rule_tac x=\<open>Zahlenwelt (\<lambda>_. -1)\<close> in exI, simp)
  apply(rule_tac x=\<open>Zahlenwelt (\<lambda>_. 1)\<close> in exI, simp)
  done

  

(*<*)
  lemma globaler_fortschritt_kommutiert:
    \<open>wpsm_kommutiert (Maxime (\<lambda>ich::person. globaler_fortschritt)) zahlenwelt_personen_swap welt\<close>
    by(simp add: wpsm_kommutiert_def gesamtbesitz_swap zahlenwelt_personen_swap_sym)
  lemma globaler_fortschritt_unbeteiligt1:
    \<open>wpsm_unbeteiligt1 (Maxime (\<lambda>ich::person. globaler_fortschritt)) zahlenwelt_personen_swap welt\<close>
    by(simp add: wpsm_unbeteiligt1_def gesamtbesitz_swap)
  lemma globaler_fortschritt_unbeteiligt2:
    \<open>wpsm_unbeteiligt2 (Maxime (\<lambda>ich::person. globaler_fortschritt)) zahlenwelt_personen_swap welt\<close>
    by(simp add: wpsm_unbeteiligt2_def gesamtbesitz_swap)
(*>*)
  
  theorem \<open>kategorischer_imperativ zahlenwelt_personen_swap (Zahlenwelt besitz)
          (Maxime (\<lambda>ich::person. globaler_fortschritt))\<close>
    apply(rule globale_maxime_katimp)
       apply(simp add: globaler_fortschritt_kommutiert; fail)
      apply(simp add: globaler_fortschritt_unbeteiligt1; fail)
     apply(simp add: globaler_fortschritt_unbeteiligt2; fail)
    apply(simp add: zahlenwelt_personen_swap_sym)
    done


  text\<open>Allerdings ist auch Stehlen erlaubt, da global gesehen, kein Besitz vernichtet wird:\<close>
  lemma\<open>beispiel_case_law_relativ
          (Maxime (\<lambda>ich. globaler_fortschritt))
          (Handlungsabsicht (stehlen 5 Bob))
    =
    Gesetz
    {(\<section> 1, Rechtsnorm (Tatbestand [Gewinnt Alice 5, Verliert Bob 5]) (Rechtsfolge Erlaubnis))}\<close>
    by eval

subsection\<open>Alice stiehlt 5\<close>
  text\<open>Zurück zur einfachen \<^const>\<open>maxime_zahlenfortschritt\<close>.\<close>
  
  text\<open>Stehlen ist verboten:\<close>
  lemma \<open>beispiel_case_law_relativ maxime_zahlenfortschritt (Handlungsabsicht (stehlen 5 Bob)) =
    Gesetz
    {(\<section> 1, Rechtsnorm (Tatbestand [Gewinnt Alice 5, Verliert Bob 5]) (Rechtsfolge Verbot))}\<close>
    by eval

  text\<open>In kein Welt ist Stehlen \<^const>\<open>moralisch\<close>:\<close>
  lemma \<open>\<not> moralisch welt maxime_zahlenfortschritt (Handlungsabsicht (stehlen 5 Bob))\<close>
    apply(cases \<open>welt\<close>)
    by(auto simp add: maxime_zahlenfortschritt_def moralisch_simp)
  
  text\<open>Auch wenn \<^const>\<open>Alice\<close> von sich selbst stehlen möchte ist dies verboten,
  obwohl hier keiner etwas verliert:\<close>
  lemma \<open>beispiel_case_law_relativ maxime_zahlenfortschritt (Handlungsabsicht (stehlen 5 Alice)) =
    Gesetz {(\<section> 1, Rechtsnorm (Tatbestand []) (Rechtsfolge Verbot))}\<close>
    by eval
  
  text\<open>Der Grund ist, dass \<^const>\<open>Alice\<close> die abstrakte Handlung "Alice wird bestohlen" gar nicht gut
  fände, wenn sie jemand anderes ausführt:\<close>
  lemma \<open>debug_maxime show_zahlenwelt initialwelt
          maxime_zahlenfortschritt (Handlungsabsicht (stehlen 5 Alice)) =
   {VerletzteMaxime (Opfer Alice) (Taeter Bob)
     (Handlung [(Alice, 5), (Bob, 10), (Carol, - 3)] [(Bob, 15), (Carol, - 3)]),
    VerletzteMaxime (Opfer Alice) (Taeter Carol)
     (Handlung [(Alice, 5), (Bob, 10), (Carol, - 3)] [(Bob, 10), (Carol, 2)]),
    VerletzteMaxime (Opfer Alice) (Taeter Eve)
     (Handlung [(Alice, 5), (Bob, 10), (Carol, - 3)] [(Bob, 10), (Carol, - 3), (Eve, 5)])
   }\<close>
    by eval
  
  text\<open>Leider ist das hier abgeleitete Gesetz sehr fragwürdig:
  \<^term>\<open>Rechtsnorm (Tatbestand []) (Rechtsfolge Verbot)\<close>
  
  Es besagt, dass Nichtstun verboten ist.\<close>

  text\<open>Indem wir die beiden Handlungen Nichtstun und Selbstbestehlen betrachten,
  können wir sogar ein widersprüchliches Gesetz ableiten:\<close>
  lemma \<open>simulateOne
      (SimConsts
        Alice
        maxime_zahlenfortschritt
        (case_law_ableiten_relativ delta_zahlenwelt))
      20 (Handlungsabsicht (stehlen 5 Alice)) initialwelt
      (beispiel_case_law_relativ maxime_zahlenfortschritt (Handlungsabsicht (erschaffen 0)))
    =
    Gesetz
  {(\<section> 2, Rechtsnorm (Tatbestand []) (Rechtsfolge Verbot)),
   (\<section> 1, Rechtsnorm (Tatbestand []) (Rechtsfolge Erlaubnis))}\<close>
    by eval

  text\<open>Meine persönliche Conclusion: Wir müssen irgendwie die Absicht mit ins Gesetz schreiben.\<close>

subsection\<open>Schenken\<close>
  text\<open>Es ist \<^const>\<open>Alice\<close> verboten, etwas zu verschenken:\<close>
  lemma\<open>beispiel_case_law_relativ maxime_zahlenfortschritt (Handlungsabsicht (schenken 5 Bob))
    =
    Gesetz
      {(\<section> 1,
        Rechtsnorm (Tatbestand [Verliert Alice 5, Gewinnt Bob 5]) (Rechtsfolge Verbot))}\<close>
    by eval
  text\<open>Der Grund ist, dass \<^const>\<open>Alice\<close> dabei etwas verliert und
  die \<^const>\<open>maxime_zahlenfortschritt\<close> dies nicht Erlaubt.
  Es fehlt eine Möglichkeit zu modellieren, dass \<^const>\<open>Alice\<close> damit einverstanden ist,
  etwas abzugeben.
  Doch wir haben bereits in @{thm stehlen_ist_schenken} gesehen,
  dass \<^const>\<open>stehlen\<close> und \<^const>\<open>schenken\<close> nicht unterscheidbar sind.\<close>

(*TODO: kategorischen Imperativ aendern, so dass allgemeines gesetz ableiten eine
handlungsabsicht anstatt einer handlung nimmt.
Evtl in neue Datei, damit sich dieses Beipsiel noch gut liesst.*)

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
  text\<open>Dies würde es erlauben, dass \<^const>\<open>Alice\<close> Leute bestehlen darf:\<close>
  lemma\<open>beispiel_case_law_relativ
            (Maxime (\<lambda>ich. individueller_fortschritt Alice))
            (Handlungsabsicht (stehlen 5 Bob))
    =
    Gesetz
    {(\<section> 1, Rechtsnorm (Tatbestand [Gewinnt Alice 5, Verliert Bob 5]) (Rechtsfolge Erlaubnis))}\<close>
    by eval

end
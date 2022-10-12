theory BeispielZahlenwelt
imports Zahlenwelt Simulation Gesetze BeispielPerson
begin

section\<open>Beispiel: Zahlenwelt\<close>

  text\<open>Wir nehmen an, die Welt lässt sich durch eine Zahl darstellen,
  die den Besitz einer Person modelliert.
  
  Der Besitz ist als ganze Zahl \<^typ>\<open>int\<close> modelliert und kann auch beliebig negativ werden.\<close>
  datatype zahlenwelt = Zahlenwelt
    "person \<Rightarrow> int \<comment> \<open>besitz: Besitz jeder Person.\<close>"
  
  fun gesamtbesitz :: "zahlenwelt \<Rightarrow> int" where
    "gesamtbesitz (Zahlenwelt besitz) = sum_list (map besitz Enum.enum)"
  
  lemma "gesamtbesitz (Zahlenwelt \<^url>[Alice := 4, Carol := 8]) = 12" by eval
  lemma "gesamtbesitz (Zahlenwelt \<^url>[Alice := 4, Carol := 4]) = 8" by eval
  
  
  fun meins :: "person \<Rightarrow> zahlenwelt \<Rightarrow> int" where
    "meins p (Zahlenwelt besitz) = besitz p"
  
  lemma "meins Carol (Zahlenwelt \<^url>[Alice := 8, Carol := 4]) = 4" by eval
  
  (*<*)
  definition "show_zahlenwelt w \<equiv> case w of Zahlenwelt besitz \<Rightarrow> show_num_fun besitz"
  fun delta_zahlenwelt :: "(zahlenwelt, person, int) delta" where
    "delta_zahlenwelt (Handlung (Zahlenwelt vor_besitz) (Zahlenwelt nach_besitz)) =
        Aenderung.delta_num_fun (Handlung vor_besitz nach_besitz)"
  (*>*)

subsection\<open>Handlungen\<close>

  text\<open>Die folgende Handlung erschafft neuen Besitz aus dem Nichts:\<close>
  fun erschaffen :: "nat \<Rightarrow> person \<Rightarrow> zahlenwelt \<Rightarrow> zahlenwelt" where
    "erschaffen i p (Zahlenwelt besitz) = Zahlenwelt (besitz(p += int i))"
  
  fun stehlen :: "int \<Rightarrow> person \<Rightarrow> person \<Rightarrow> zahlenwelt \<Rightarrow> zahlenwelt" where
    "stehlen beute opfer dieb (Zahlenwelt besitz) =
        Zahlenwelt (besitz(opfer -= beute)(dieb += beute))"
  
  fun schenken :: "int \<Rightarrow> person \<Rightarrow> person \<Rightarrow> zahlenwelt \<Rightarrow> zahlenwelt" where
    "schenken betrag empfaenger schenker (Zahlenwelt besitz) =
        Zahlenwelt (besitz(schenker -= betrag)(empfaenger += betrag))"
  
  text\<open>Da wir ganze Zahlen verwenden und der Besitz auch beliebig negativ werden kann,
  ist Stehlen äquivalent dazu einen negativen Betrag zu verschenken:\<close>
  lemma stehlen_ist_schenken: "stehlen i = schenken (-i)"
    apply(simp add: fun_eq_iff)
    apply(intro allI, rename_tac p1 p2 welt, case_tac welt)
    by auto
  
  text\<open>Das Modell ist nicht ganz perfekt, .... Aber passt schon um damit zu spielen.\<close>


  text\<open>Reset versetzt die Welt wieder in den Ausgangszustand. Eine sehr destruktive Handlung.\<close>
  fun reset :: "person \<Rightarrow> zahlenwelt \<Rightarrow> zahlenwelt" where
    "reset ich (Zahlenwelt besitz) = Zahlenwelt (\<lambda> _. 0)"

  (*TODO: eigentlich keine gute handlung, aber fuer einen verschuldeten egoisten gut.*)


subsection\<open>Setup\<close>
  text\<open>\<^const>\<open>Alice\<close> hat Besitz, \<^const>\<open>Bob\<close> ist reicher, \<^const>\<open>Carol\<close> hat Schulden.\<close>
  definition "initialwelt \<equiv> Zahlenwelt \<^url>[Alice := 5, Bob := 10, Carol := -3]"
  
  text\<open>Wir nehmen an unsere handelnde Person ist \<^const>\<open>Alice\<close>.\<close>
  
  definition "beispiel_case_law_absolut maxime handlungsabsicht \<equiv>
    simulateOne
      (SimConsts
        Alice
        maxime
        (printable_case_law_ableiten_absolut show_zahlenwelt))
      5 handlungsabsicht initialwelt (Gesetz {})"
  definition "beispiel_case_law_relativ maxime handlungsabsicht \<equiv>
    simulateOne
      (SimConsts
        Alice
        maxime
        (case_law_ableiten_relativ delta_zahlenwelt))
      10 handlungsabsicht initialwelt (Gesetz {})"

subsection\<open>Alice erzeugt 5 Wohlstand für sich.\<close>

  text\<open>Wir definieren eine Maxime die besagt,
  dass sich der Besitz einer Person nicht verringern darf:\<close>
  fun individueller_fortschritt :: "person \<Rightarrow> zahlenwelt handlung \<Rightarrow> bool" where
    "individueller_fortschritt p (Handlung vor nach) \<longleftrightarrow> (meins p vor) \<le> (meins p nach)"
  definition maxime_zahlenfortschritt :: "(person, zahlenwelt) maxime" where
    "maxime_zahlenfortschritt \<equiv> Maxime (\<lambda>ich. individueller_fortschritt ich)"


  text\<open>In jeder Welt ist die Handlung \<^const>\<open>moralisch\<close>:\<close>
  lemma "moralisch welt maxime_zahlenfortschritt (HandlungF (erschaffen 5))"
    apply(cases welt)
    by(simp add: maxime_zahlenfortschritt_def moralisch_simp)

  (*AWESOME!*)
  text\<open>Die \<^const>\<open>maxime_zahlenfortschritt\<close> erfüllt nicht den \<^const>\<open>kategorischer_imperativ\<close>
  da \<^const>\<open>Alice\<close> nach der Maxime z.B. \<^const>\<open>Bob\<close> bestehen würde.\<close>
  lemma "\<not> kategorischer_imperativ welt maxime_zahlenfortschritt"
    apply(simp add: maxime_zahlenfortschritt_def moralisch_simp)
    apply(rule_tac x="HandlungF (stehlen 1 Bob)" in exI)
    apply(simp)
    apply(intro conjI)
     apply(rule_tac x=Alice in exI)
     apply(case_tac welt, simp; fail)
    apply(rule_tac x=Bob in exI)
    apply(rule_tac x=Alice in exI)
    apply(cases welt, rename_tac besitz)
    apply(simp)
    done

  (*TODO: wenn wir aus einer maxime ein allgemeines gesetz ableiten, wollen wir dann
      einfach aus den `ich` ein \<forall>ich. machen?
    so einfach ist es nicht:
  *)
  lemma "\<not>kategorischer_imperativ welt
    (Maxime (\<lambda>(ich::person) h. (\<forall>pX. individueller_fortschritt pX h)))"
    apply(simp add: maxime_zahlenfortschritt_def moralisch_simp)
    apply(rule_tac x="HandlungF (stehlen 1 Bob)" in exI)
    apply(simp)
    apply(intro conjI)
     apply(rule_tac x=Bob in exI)
     apply(case_tac welt, simp; fail)
    apply(rule_tac x=Alice in exI)
    apply(rule_tac x=Bob in exI)
    apply(cases welt, rename_tac besitz)
    apply(simp)
    done

  (*Was muesste denn eine Maxime sein die den katimp erfuellt?*)
  lemma "kategorischer_imperativ welt
    (Maxime (\<lambda>(ich::person) h. (\<forall>pX. individueller_fortschritt pX h)))"
    apply(simp add: maxime_zahlenfortschritt_def moralisch_simp)
    oops

  lemma "kategorischer_imperativ welt
    (Maxime (\<lambda>ich. individueller_fortschritt ich))"
    apply(simp add: maxime_zahlenfortschritt_def moralisch_simp)
    apply(intro allI impI)
    apply(cases welt, rename_tac besitz, simp)
    apply(case_tac h, rename_tac h, simp)
    apply(case_tac "h = erschaffen 5", simp)
    apply(case_tac "h = stehlen 5 Bob", simp)
    apply(case_tac "h = schenken 5 Bob", simp)
      apply(case_tac "h = reset", simp)
    oops
  (*TODO*)

  text\<open>Alice kann beliebig oft 5 Wohlstand für sich selbst erschaffen.
  Das entstehende Gesetz ist nicht sehr gut, da es einfach jedes Mal einen
  Snapshot der Welt aufschreibt und nicht sehr generisch ist.\<close>
  lemma \<open>beispiel_case_law_absolut maxime_zahlenfortschritt (HandlungF (erschaffen 5))
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
  lemma \<open>beispiel_case_law_relativ maxime_zahlenfortschritt (HandlungF (erschaffen 5)) =
    Gesetz
    {(\<section> 1, Rechtsnorm (Tatbestand [Gewinnt Alice 5]) (Rechtsfolge Erlaubnis))}\<close>
    by eval

subsection\<open>Kleine Änderung in der Maxime\<close>
  text\<open>In der Maxime \<^const>\<open>individueller_fortschritt\<close> hatten wir
   \<^term>\<open>(meins p nach) \<ge> (meins p vor)\<close>.
  Was wenn wir nun echten Fortschritt fordern:
   \<^term>\<open>(meins p nach) > (meins p vor)\<close>.\<close>
  
  fun individueller_strikter_fortschritt :: "person \<Rightarrow> zahlenwelt handlung \<Rightarrow> bool" where
    "individueller_strikter_fortschritt p (Handlung vor nach) \<longleftrightarrow> (meins p vor) < (meins p nach)"

  text\<open>Nun ist es \<^const>\<open>Alice\<close> verboten Wohlstand für sich selbst zu erzeugen.\<close>
  lemma \<open>beispiel_case_law_relativ
          (Maxime (\<lambda>ich. individueller_strikter_fortschritt ich))
          (HandlungF (erschaffen 5)) =
    Gesetz {(\<section> 1, Rechtsnorm (Tatbestand [Gewinnt Alice 5]) (Rechtsfolge Verbot))}\<close>
    by eval
    
  text\<open>In keiner Welt ist die Handlung nun \<^const>\<open>moralisch\<close>:\<close>
lemma "\<not> moralisch welt
          (Maxime (\<lambda>ich. individueller_strikter_fortschritt ich)) (HandlungF (erschaffen 5))"
    apply(cases welt)
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
            (Maxime (\<lambda>ich. individueller_strikter_fortschritt ich)) (HandlungF (erschaffen 5)) \<close>
    by eval


subsection\<open>Maxime für Globales Optimum\<close>
  text\<open>Wir bauen nun eine Maxime, die das Individuum vernachlässigt und nur nach dem
  globalen Optimum strebt:\<close>
  fun globaler_strikter_fortschritt :: "zahlenwelt handlung \<Rightarrow> bool" where
    "globaler_strikter_fortschritt (Handlung vor nach) \<longleftrightarrow> (gesamtbesitz vor) < (gesamtbesitz nach)"
  
  text\<open>Die Maxime ignoriert das \<^term>\<open>ich :: person\<close> komplett.
  
  Nun ist es \<^const>\<open>Alice\<close> wieder erlaubt, Wohlstand für sich selbst zu erzeugen,
  da sich dadurch auch der Gesamtwohlstand erhöht:\<close>
  lemma \<open>beispiel_case_law_relativ
          (Maxime (\<lambda>ich. globaler_strikter_fortschritt))
          (HandlungF (erschaffen 5)) =
    Gesetz {(\<section> 1, Rechtsnorm (Tatbestand [Gewinnt Alice 5]) (Rechtsfolge Erlaubnis))}\<close>
    by eval


  lemma "moralisch initialwelt
          (Maxime (\<lambda>ich. globaler_strikter_fortschritt)) (HandlungF (erschaffen 5))"
  by(eval)
    
    
  
  text\<open>Allerdings ist auch diese Maxime auch sehr grausam, da sie Untätigkeit verbietet:\<close>
  lemma \<open>beispiel_case_law_relativ
          (Maxime (\<lambda>ich. globaler_strikter_fortschritt))
          (HandlungF (erschaffen 0)) =
    Gesetz {(\<section> 1, Rechtsnorm (Tatbestand []) (Rechtsfolge Verbot))}\<close>
    by eval


  text\<open>Unsere initiale einfache \<^const>\<open>maxime_zahlenfortschritt\<close> würde Untätigkeit hier erlauben:\<close>
  lemma \<open>beispiel_case_law_relativ
          maxime_zahlenfortschritt
          (HandlungF (erschaffen 0)) =
    Gesetz {(\<section> 1, Rechtsnorm (Tatbestand []) (Rechtsfolge Erlaubnis))}\<close>
    by eval

  text\<open>Wir können die Maxime für globalen Fortschritt etwas lockern:\<close>
  fun globaler_fortschritt :: "zahlenwelt handlung \<Rightarrow> bool" where
   "globaler_fortschritt (Handlung vor nach) \<longleftrightarrow> (gesamtbesitz vor) \<le> (gesamtbesitz nach)"

  text\<open>Untätigkeit ist nun auch hier erlaubt:\<close>
  lemma\<open>beispiel_case_law_relativ
            (Maxime (\<lambda>ich. globaler_fortschritt))
            (HandlungF (erschaffen 0))
    =
    Gesetz {(\<section> 1, Rechtsnorm (Tatbestand []) (Rechtsfolge Erlaubnis))}\<close>
    by eval

(*TODO: eine Person in eine Handlungsabsicht als handelnde hardzucoden ist illegal!*)
lemma "\<not>kategorischer_imperativ initialwelt (Maxime (\<lambda>ich::person. globaler_fortschritt))"
  apply(simp add: moralisch_simp)
  apply(simp add: initialwelt_def)
  apply(rule_tac x="HandlungF (\<lambda>ich w. if ich = Alice then w else Zahlenwelt (\<lambda>_. 0))" in exI)
  apply(simp)
  apply(eval)
  done

  text\<open>Allerdings ist auch Stehlen erlaubt, da global gesehen, kein Besitz vernichtet wird:\<close>
  lemma\<open>beispiel_case_law_relativ
          (Maxime (\<lambda>ich. globaler_fortschritt))
          (HandlungF (stehlen 5 Bob))
    =
    Gesetz
    {(\<section> 1, Rechtsnorm (Tatbestand [Gewinnt Alice 5, Verliert Bob 5]) (Rechtsfolge Erlaubnis))}\<close>
    by eval

subsection\<open>Alice stiehlt 5\<close>
  text\<open>Zurück zur einfachen \<^const>\<open>maxime_zahlenfortschritt\<close>.\<close>
  
  text\<open>Stehlen ist verboten:\<close>
  lemma \<open>beispiel_case_law_relativ maxime_zahlenfortschritt (HandlungF (stehlen 5 Bob)) =
    Gesetz
    {(\<section> 1, Rechtsnorm (Tatbestand [Gewinnt Alice 5, Verliert Bob 5]) (Rechtsfolge Verbot))}\<close>
    by eval

  text\<open>In kein Welt ist Stehlen \<^const>\<open>moralisch\<close>:\<close>
  lemma "\<not> moralisch welt maxime_zahlenfortschritt (HandlungF (stehlen 5 Bob))"
    apply(cases welt)
    by(auto simp add: maxime_zahlenfortschritt_def moralisch_simp)
  
  text\<open>Auch wenn \<^const>\<open>Alice\<close> von sich selbst stehlen möchte ist dies verboten,
  obwohl hier keiner etwas verliert:\<close>
  lemma \<open>beispiel_case_law_relativ maxime_zahlenfortschritt (HandlungF (stehlen 5 Alice)) =
    Gesetz {(\<section> 1, Rechtsnorm (Tatbestand []) (Rechtsfolge Verbot))}\<close>
    by eval
  
  text\<open>Der Grund ist, dass \<^const>\<open>Alice\<close> die abstrakte Handlung "Alice wird bestohlen" gar nicht gut
  fände, wenn sie jemand anderes ausführt:\<close>
  lemma \<open>debug_maxime show_zahlenwelt initialwelt
          maxime_zahlenfortschritt (HandlungF (stehlen 5 Alice)) =
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
      20 (HandlungF (stehlen 5 Alice)) initialwelt
      (beispiel_case_law_relativ maxime_zahlenfortschritt (HandlungF (erschaffen 0)))
    =
    Gesetz
  {(\<section> 2, Rechtsnorm (Tatbestand []) (Rechtsfolge Verbot)),
   (\<section> 1, Rechtsnorm (Tatbestand []) (Rechtsfolge Erlaubnis))}\<close>
    by eval

  text\<open>Meine persönliche Conclusion: Wir müssen irgendwie die Absicht mit ins Gesetz schreiben.\<close>

subsection\<open>Schenken\<close>
  text\<open>Es ist \<^const>\<open>Alice\<close> verboten, etwas zu verschenken:\<close>
  lemma\<open>beispiel_case_law_relativ maxime_zahlenfortschritt (HandlungF (schenken 5 Bob))
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
handlungF anstatt einer handlung nimmt.
Evtl in neue Datei, damit sich dieses Beipsiel noch gut liesst.*)

subsection\<open>Ungültige Maxime\<close>
  text\<open>Es ist verboten, in einer Maxime eine spezielle Person hardzucoden.
  Da dies gegen die Gleichbehandlung aller Menschen verstoßen würde.
  
  Beispielsweise könnten wir \<^const>\<open>individueller_fortschritt\<close> nicht mehr parametrisiert verwenden,
  sondern einfach \<^const>\<open>Alice\<close> reinschreiben:
  \<close>
  lemma "individueller_fortschritt Alice
    = (\<lambda>h. case h of Handlung vor nach \<Rightarrow> (meins Alice vor) \<le> (meins Alice nach))"
    apply(simp add: fun_eq_iff)
    apply(intro allI, rename_tac h, case_tac h)
    apply(simp)
    done
  text\<open>Dies würde es erlauben, dass \<^const>\<open>Alice\<close> Leute bestehlen darf:\<close>
  lemma\<open>beispiel_case_law_relativ
            (Maxime (\<lambda>ich. individueller_fortschritt Alice))
            (HandlungF (stehlen 5 Bob))
    =
    Gesetz
    {(\<section> 1, Rechtsnorm (Tatbestand [Gewinnt Alice 5, Verliert Bob 5]) (Rechtsfolge Erlaubnis))}\<close>
    by eval

end
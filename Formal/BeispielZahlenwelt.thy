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
  lemma "stehlen i = schenken (-i)"
    apply(simp add: fun_eq_iff)
    apply(intro allI, rename_tac p1 p2 welt, case_tac welt)
    by auto
  
  text\<open>Das Modell ist nicht ganz perfekt, .... Aber passt schon um damit zu spielen.\<close>


subsection\<open>Setup\<close>

  definition "initialwelt \<equiv> Zahlenwelt \<^url>[Alice := 5, Bob := 10]"
  
  text\<open>Wir nehmen an unsere handelnde Person ist \<^const>\<open>Alice\<close>.\<close>
  
  definition "beispiel_case_law_absolut maxime handlung \<equiv>
    simulateOne
      (SimConsts
        Alice
        maxime
        (printable_case_law_ableiten_absolut show_zahlenwelt))
      10 handlung initialwelt (Gesetz {})"
  definition "beispiel_case_law_relativ maxime handlung \<equiv>
    simulateOne
      (SimConsts
        Alice
        maxime
        (case_law_ableiten_relativ delta_zahlenwelt))
      20 handlung initialwelt (Gesetz {})"

subsection\<open>Alice erzeugt 5 Wohlstand für sich.\<close>

  text\<open>Wir definieren eine Maxime die besagt,
  dass sich der Besitz einer Person nicht verringern darf:\<close>
  fun individueller_fortschritt :: "person \<Rightarrow> zahlenwelt handlung \<Rightarrow> bool" where
    "individueller_fortschritt p (Handlung vor nach) \<longleftrightarrow> (meins p vor) \<le> (meins p nach)"
  definition maxime_zahlenfortschritt :: "(person, zahlenwelt) maxime" where
    "maxime_zahlenfortschritt \<equiv> Maxime (\<lambda>ich. individueller_fortschritt ich)"
  
  
  
  text\<open>Alice kann beliebig oft 5 Wohlstand für sich selbst erschaffen.
  Das entstehende Gesetz ist nicht sehr gut, da es einfach jedes Mal einen
  Snapshot der Welt aufschreibt und nicht sehr generisch ist.\<close>
  lemma \<open>beispiel_case_law_absolut maxime_zahlenfortschritt (HandlungF (erschaffen 5))
  =
  Gesetz
    {(Paragraph 10,
      Rechtsnorm (Tatbestand ([(Alice, 50), (Bob, 10)], [(Alice, 55), (Bob, 10)]))
       (Rechtsfolge Erlaubnis)),
     (Paragraph 9,
      Rechtsnorm (Tatbestand ([(Alice, 45), (Bob, 10)], [(Alice, 50), (Bob, 10)]))
       (Rechtsfolge Erlaubnis)),
     (Paragraph 8,
      Rechtsnorm (Tatbestand ([(Alice, 40), (Bob, 10)], [(Alice, 45), (Bob, 10)]))
       (Rechtsfolge Erlaubnis)),
     (Paragraph 7,
      Rechtsnorm (Tatbestand ([(Alice, 35), (Bob, 10)], [(Alice, 40), (Bob, 10)]))
       (Rechtsfolge Erlaubnis)),
     (Paragraph 6,
      Rechtsnorm (Tatbestand ([(Alice, 30), (Bob, 10)], [(Alice, 35), (Bob, 10)]))
       (Rechtsfolge Erlaubnis)),
     (Paragraph 5,
      Rechtsnorm (Tatbestand ([(Alice, 25), (Bob, 10)], [(Alice, 30), (Bob, 10)]))
       (Rechtsfolge Erlaubnis)),
     (Paragraph 4,
      Rechtsnorm (Tatbestand ([(Alice, 20), (Bob, 10)], [(Alice, 25), (Bob, 10)]))
       (Rechtsfolge Erlaubnis)),
     (Paragraph 3,
      Rechtsnorm (Tatbestand ([(Alice, 15), (Bob, 10)], [(Alice, 20), (Bob, 10)]))
       (Rechtsfolge Erlaubnis)),
     (Paragraph 2,
      Rechtsnorm (Tatbestand ([(Alice, 10), (Bob, 10)], [(Alice, 15), (Bob, 10)]))
       (Rechtsfolge Erlaubnis)),
     (Paragraph 1,
      Rechtsnorm (Tatbestand ([(Alice, 5), (Bob, 10)], [(Alice, 10), (Bob, 10)]))
       (Rechtsfolge Erlaubnis))}
  \<close> by eval
  
  
  text\<open>Die gleiche Handlung, wir schreiben aber nur die Änderung der Welt ins Gesetz:\<close>
  lemma \<open>beispiel_case_law_relativ maxime_zahlenfortschritt (HandlungF (erschaffen 5)) =
    Gesetz
    {(Paragraph 1, Rechtsnorm (Tatbestand [Gewinnt Alice 5]) (Rechtsfolge Erlaubnis))}\<close>
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
    Gesetz {(Paragraph 1, Rechtsnorm (Tatbestand [Gewinnt Alice 5]) (Rechtsfolge Verbot))}\<close>
    by eval
  
  
  text\<open> Der Grund ist, dass der Rest der Bevölkerung keine \<^emph>\<open>strikte\<close> Erhöhung des eigenen Wohlstands
  erlebt.
  Effektiv führt diese Maxime zu einem Gesetz, welches es einem Individuum nicht erlaubt
  mehr Besitz zu erschaffen, obwohl niemand dadurch einen Nachteil hat.
  Diese Maxime kann meiner Meinung nach nicht gewollt sein.
  
  
  Beispielsweise ist \<^const>\<open>Bob\<close> das Opfer wenn \<^const>\<open>Alice\<close> sich
  5 Wohlstand erschafft, aber \<^const>\<open>Bob\<close>'s Wohlstand sich nicht erhöht:\<close>
  lemma\<open>VerletzteMaxime (Opfer Bob) (Taeter Alice)
          (Handlung [(Alice, 5), (Bob, 10)] [(Alice, 10), (Bob, 10)])
          \<in> debug_maxime show_zahlenwelt initialwelt
            (HandlungF (erschaffen 5)) (Maxime (\<lambda>ich. individueller_strikter_fortschritt ich))\<close>
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
    Gesetz {(Paragraph 1, Rechtsnorm (Tatbestand [Gewinnt Alice 5]) (Rechtsfolge Erlaubnis))}\<close>
    by eval
  
  text\<open>Allerdings ist auch diese Maxime auch sehr grausam, da sie Untätigkeit verbietet:\<close>
  lemma \<open>beispiel_case_law_relativ
          (Maxime (\<lambda>ich. globaler_strikter_fortschritt))
          (HandlungF (erschaffen 0)) =
    Gesetz {(Paragraph 1, Rechtsnorm (Tatbestand []) (Rechtsfolge Verbot))}\<close>
    by eval


  text\<open>Unsere initiale einfache \<^const>\<open>maxime_zahlenfortschritt\<close> würde Untätigkeit hier erlauben:\<close>
  lemma \<open>beispiel_case_law_relativ
          maxime_zahlenfortschritt
          (HandlungF (erschaffen 0)) =
    Gesetz {(Paragraph 1, Rechtsnorm (Tatbestand []) (Rechtsfolge Erlaubnis))}\<close>
    by eval

subsection\<open>Alice stiehlt 5\<close>
  text\<open>Zurück zur einfachen \<^const>\<open>maxime_zahlenfortschritt\<close>.\<close>
  
  text\<open>Stehlen ist verboten:\<close>
  lemma \<open>beispiel_case_law_relativ maxime_zahlenfortschritt (HandlungF (stehlen 5 Bob)) =
    Gesetz
    {(Paragraph 1, Rechtsnorm (Tatbestand [Gewinnt Alice 5, Verliert Bob 5]) (Rechtsfolge Verbot))}\<close>
    by eval
  
  text\<open>Auch wenn \<^const>\<open>Alice\<close> von sich selbst stehlen möchte ist dies verboten,
  obwohl hier keiner etwas verliert:\<close>
  lemma \<open>beispiel_case_law_relativ maxime_zahlenfortschritt (HandlungF (stehlen 5 Alice)) =
    Gesetz {(Paragraph 1, Rechtsnorm (Tatbestand []) (Rechtsfolge Verbot))}\<close>
    by eval
  
  text\<open>Der Grund ist, dass \<^const>\<open>Alice\<close> die abstrakte Handlung "Alice wird bestohlen" gar nicht gut
  fände, wenn sie jemand anderes ausführt:\<close>
  value \<open>debug_maxime show_zahlenwelt initialwelt
          (HandlungF (stehlen 5 Alice)) maxime_zahlenfortschritt =
   {VerletzteMaxime (Opfer Alice) (Taeter Bob)
      (Handlung [(Alice, 5), (Bob, 10)] [(Bob, 15)]),
    VerletzteMaxime (Opfer Alice) (Taeter Carol)
      (Handlung [(Alice, 5), (Bob, 10)] [(Bob, 10), (Carol, 5)]),
    VerletzteMaxime (Opfer Alice) (Taeter Eve)
      (Handlung [(Alice, 5), (Bob, 10)] [(Bob, 10), (Eve, 5)])
   }\<close>
  
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
  {(Paragraph 2, Rechtsnorm (Tatbestand []) (Rechtsfolge Verbot)),
   (Paragraph 1, Rechtsnorm (Tatbestand []) (Rechtsfolge Erlaubnis))}\<close>
  by eval


subsection\<open>TODO\<close>
(*Interessant: hard-coded Alice anstelle von 'ich' in maxime_zahlenfortschritt.*)


(*TODO: den Fall der Untätigkeit verbietet anschauen.*)

text\<open>
Mehr ist mehr gut.
Globaler Fortschritt erlaubt stehlen, solange dabei nichts vernichtet wird.


Größer (>) anstelle (>=) ist hier echt spannend!

\<close>

text\<open>Dieser globale Fortschritt sollte eigentlich allgemeines Gesetz werden und die
Maxime sollte individuelle Bereicherung sein (und die unsichtbare Hand macht den Rest. YOLO).\<close>

end
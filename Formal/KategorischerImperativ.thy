theory KategorischerImperativ
imports Maxime Gesetz SchleierNichtwissen
begin

section\<open>Kategorischer Imperativ\<close>
subsection\<open>Allgemeines Gesetz Ableiten\<close>

text\<open>Wir wollen implementieren:

\<^emph>\<open>„Handle nur nach derjenigen Maxime, durch die du zugleich wollen kannst,
   dass sie ein \<^bold>\<open>allgemeines Gesetz\<close> werde.“\<close>

Für eine gebene Welt haben wir schon eine Handlung nach einer Maxime untersucht:
\<^term>\<open>moralisch::'world \<Rightarrow> ('person, 'world) maxime \<Rightarrow> ('person, 'world) handlungF \<Rightarrow> bool\<close>

Das Ergebnis sagt uns ob diese Handlung gut oder schlecht ist.
Basierend darauf müssen wir nun ein allgemeines Gesetz ableiten.

Ich habe keine Ahnung wie das genau funktionieren soll, deswegen schreibe ich
einfach nur in einer Typsignatur auf, was zu tun ist:

Gegeben:
  \<^item> \<^typ>\<open>'world handlung\<close>: Die Handlung
  \<^item> \<^typ>\<open>sollensanordnung\<close>: Das Ergebnis der moralischen Bewertung, ob die Handlung gut/schlecht.

Gesucht:
  \<^item> \<^typ>\<open>('a, 'b) rechtsnorm\<close>: ein allgemeines Gesetz
\<close>

type_synonym ('world, 'a, 'b) allgemeines_gesetz_ableiten =
  \<open>'world handlung \<Rightarrow> sollensanordnung \<Rightarrow> ('a, 'b) rechtsnorm\<close>

text\<open>
Soviel vorweg:
Nur aus einer von außen betrachteten Handlung
und einer Entscheidung ob diese Handlung ausgeführt werden soll
wird es schwer ein allgemeines Gesetz abzuleiten.
\<close>
(*TODO: waere hier ('person, 'world) handlungF anstatt 'world handlung besser?*)

subsection\<open>Implementierung Moralisch ein Allgemeines Gesetz Ableiten\<close>
(*TODO: unterstütze viele Maximen, wobei manche nicht zutreffen können?*)
text\<open>Und nun werfen wir alles zuammen:

\<^emph>\<open>„Handle nur nach derjenigen Maxime, durch die du zugleich wollen kannst,
   dass sie ein allgemeines Gesetz werde.“\<close>


Eingabe:
 \<^item> \<^typ>\<open>'person\<close>: handelnde Person
 \<^item> \<^typ>\<open>'world\<close>: Die Welt in ihrem aktuellen Zustand
 \<^item> \<^typ>\<open>('person, 'world) handlungF\<close>: Eine mögliche Handlung,
    über die wir entscheiden wollen ob wir sie ausführen sollten.
 \<^item> \<^typ>\<open>('person, 'world) maxime\<close>: Persönliche Ethik.
 \<^item> \<^typ>\<open>('world, 'a, 'b) allgemeines_gesetz_ableiten\<close>:
    wenn man keinen Plan hat wie man sowas implementiert, einfach als Eingabe annehmen.
 \<^item> \<^typ>\<open>(nat, 'a, 'b) gesetz\<close>: Initiales allgemeines Gesetz (normalerweise am Anfang leer).

Ausgabe:
   \<^typ>\<open>sollensanordnung\<close>: Sollen wir die Handlung ausführen?
   \<^typ>\<open>(nat, 'a, 'b) gesetz\<close>: Soll das allgemeine Gesetz entsprechend angepasst werden?
\<close>
  (*TODO: Wenn unsere Maximen perfekt und die Maximen aller Menschen konsisten sind,
        soll das Gesetz nur erweitert werden.*)
(*
  -- Es fehlt: ich muss nach allgemeinem Gesetz handeln.
  --           Wenn das Gesetz meinen Fall nicht abdeckt,
  --           dann muss meine Maxime zum Gesetz erhoben werden.
  -- Es fehlt: "Wollen"
  -- TODO: Wir unterstützen nur Erlaubnis/Verbot.
*)

definition moarlisch_gesetz_ableiten ::
  \<open>'person \<Rightarrow>
   'world \<Rightarrow>
   ('person, 'world) maxime \<Rightarrow>
   ('person, 'world) handlungF \<Rightarrow>
   ('world, 'a, 'b) allgemeines_gesetz_ableiten \<Rightarrow>
   (nat, 'a, 'b) gesetz
  \<Rightarrow> (sollensanordnung \<times> (nat, 'a, 'b) gesetz)\<close>
where
  \<open>moarlisch_gesetz_ableiten ich welt maxime handlungsabsicht gesetz_ableiten gesetz \<equiv>
    let soll_handeln = if moralisch welt maxime handlungsabsicht
                       then
                         Erlaubnis
                       else
                         Verbot in
      (
        soll_handeln,
        hinzufuegen (gesetz_ableiten (handeln ich welt handlungsabsicht) soll_handeln) gesetz
      )\<close>

text\<open>Das ganze \<^const>\<open>moarlisch_gesetz_ableiten\<close> dient mehr dem Debugging, ...\<close>

subsection\<open>Kategorischer Imperativ\<close>

text\<open>
Wir haben mit der goldenen Regel bereits definiert, 
wann für eine gegebene Welt und eine gegebene maxime, eine Handlungsabsicht moralisch ist:

 \<^item> \<^term_type>\<open>moralisch :: 
     'world \<Rightarrow> ('person, 'world) maxime \<Rightarrow> ('person, 'world) handlungF \<Rightarrow> bool\<close>

Effektiv testet die goldene Regel eine Handlungsabsicht.

Nach meinem Verständnis generalisiert Kant mit dem Kategorischen Imperativ diese Regel,
indem die Maxime nicht mehr als gegeben angenommen wird,
sondern die Maxime selbst getestet wird.
Sei die Welt weiterhin gegeben,
dass müsste der kategorische Imperativ folgende Typsignatur haben:

  \<^item> \<^typ>\<open>'world \<Rightarrow> ('person, 'world) maxime \<Rightarrow> bool\<close>

Eine Implementierung muss dann über alle möglichen Handlungsabsichten allquantifizieren.


Ich behaupte, der kategorischer Imperativ lässt sich wie folgt umformulieren:

  \<^item> Handle nur nach derjenigen Maxime, durch die du zugleich wollen kannst, 
    dass sie ein allgemeines Gesetz werde.
  \<^item> Handle nur nach derjenigen Maxime, durch die du zugleich wollen kannst,
    dass sie jeder befolgt, im Sinne der goldenen Regel.
  \<^item> Handle nur nach derjenigen Maxime, durch die du zugleich wollen kannst,
    dass sie (Handlung+Maxime) moralisch ist.
  \<^item> Wenn es jemanden gibt der nach einer Maxime handeln will,
    dann muss diese Handlung nach der Maxime moralsich sein.
  \<^item> Für jede Handlungsabsicht muss gelten:
    Wenn jemand in jeder Welt nach der Handlungsabsicht handeln würde,
    dann muss diese Handlung moralisch sein.

Daraus ergibt sich die finale Formalisierung:

Für alle möglichen (wohlgeformten) Handlungsabsichten muss gelten:
Wenn es eine Person gibt für die diese Handlungsabsicht moralisch ist,
dann muss diese Handlungsabsicht auch für alle moralisch (im Sinne der goldenen Regel) sein.
\<close>
definition kategorischer_imperativ
  :: \<open>('person, 'world) wp_swap \<Rightarrow> 'world \<Rightarrow> ('person, 'world) maxime \<Rightarrow> bool\<close>
where
  \<open>kategorischer_imperativ welt_personen_swap welt m =
    (\<forall>h.
          wohlgeformte_handlungsabsicht welt_personen_swap welt h \<and>
          (\<exists>p. maxime_und_handlungsabsicht_generalisieren m h p \<and> okay m p (handeln p welt h))
              \<longrightarrow> moralisch welt m h)\<close>

text\<open>Dabei sind \<^const>\<open>wohlgeformte_handlungsabsicht\<close>
und \<^const>\<open>maxime_und_handlungsabsicht_generalisieren\<close>
ein technisch notwendiges Implementierungsdetail um nicht-wohlgeformte Handlungen
oder Maximen auszuschließen.\<close>

text\<open>Minimal andere Formulierung:\<close>
lemma
\<open>kategorischer_imperativ welt_personen_swap welt m \<longleftrightarrow>
  (\<forall>h.
    (\<exists>p.
        wohlgeformte_handlungsabsicht welt_personen_swap welt h \<and>
        maxime_und_handlungsabsicht_generalisieren m h p \<and>
        okay m p (handeln p welt h))
    \<longrightarrow> moralisch welt m h)\<close>
  unfolding kategorischer_imperativ_def
  by(simp)

text\<open>Der Existenzquantor lässt sich auch in einen Allquantor umschreiben:\<close>
lemma
\<open>kategorischer_imperativ welt_personen_swap welt m \<longleftrightarrow>
  (\<forall>h ich.
      wohlgeformte_handlungsabsicht welt_personen_swap welt h \<and> 
      maxime_und_handlungsabsicht_generalisieren m h ich \<and>
      okay m ich (handeln ich welt h) \<longrightarrow> moralisch welt m h)\<close>
  by(simp add: kategorischer_imperativ_def)
  

text\<open>Für jede Handlungsabsicht:
  wenn ich so handeln würde muss es auch okay sein, wenn zwei beliebige
  personen so handeln, wobei einer Täter und einer Opfer ist.\<close>
lemma kategorischer_imperativ_simp:
  "kategorischer_imperativ welt_personen_swap welt m \<longleftrightarrow>
    (\<forall>h p1 p2 ich.
      wohlgeformte_handlungsabsicht welt_personen_swap welt h \<and> 
      maxime_und_handlungsabsicht_generalisieren m h ich \<and>
      okay m ich (handeln ich welt h)
      \<longrightarrow> okay m p1 (handeln p2 welt h))"
  by (simp add: kategorischer_imperativ_def moralisch_simp)


lemma kategorischer_imperativI:
  \<open>(\<And>h p1 p2 p. wohlgeformte_handlungsabsicht welt_personen_swap welt h \<Longrightarrow>
   maxime_und_handlungsabsicht_generalisieren m h p \<Longrightarrow>
   okay m p (handeln p welt h) \<Longrightarrow> okay m p1 (handeln p2 welt h)
   )
 \<Longrightarrow> kategorischer_imperativ welt_personen_swap welt m\<close>
  by(auto simp add: kategorischer_imperativ_simp)


subsection\<open>Triviale Maximen die den Kategorischen Imperativ immer Erfüllen\<close>
text\<open>
Die Maxime die keine Handlung erlaubt (weil immer False) erfüllt den kategorischen
Imperativ:\<close>
lemma \<open>kategorischer_imperativ welt_personen_swap welt (Maxime (\<lambda>ich h. False))\<close>
  by(simp add: kategorischer_imperativ_def)

text\<open>Allerdings kann mit so einer Maxime nie etwas moralisch sein.\<close>
lemma \<open>\<not> moralisch welt (Maxime (\<lambda>ich h. False)) h\<close>
  by(simp add: moralisch_simp)

text\<open>Die Maxime die jede Handlung erlaubt (weil immer True) erfüllt den kategorischen
Imperativ:\<close>
lemma \<open>kategorischer_imperativ welt_personen_swap welt (Maxime (\<lambda>ich h. True))\<close>
  by(simp add: kategorischer_imperativ_simp)

text\<open>Allerdings ist mot so einer Maxime alles moralisch.\<close>
lemma \<open>moralisch welt (Maxime (\<lambda>ich h. True)) h\<close>
  by(simp add: moralisch_simp)



subsection\<open>Zusammenhang Goldene Regel\<close>
text\<open>
Mit der goldenen Regel konnten wir wie folgt moralische Entscheidungen treffen:
@{thm goldene_regel}

In Worten:
Wenn eine Handlungsabsicht moralisch ist (nach goldener Regel)
und es okay ist für mich diese Handlung auszuführen,
denn ist es auch für mich okay, wenn jeder andere diese Handlung mit mir als Opfer ausführt. 

Der kategorische Imperativ liftet dies eine Abstraktionsebene:
\<close>

lemma \<open>kategorischer_imperativ welt_personen_swap welt m \<Longrightarrow>
  wohlgeformte_handlungsabsicht welt_personen_swap welt h \<Longrightarrow>
  maxime_und_handlungsabsicht_generalisieren m h ich \<Longrightarrow>
  okay m ich (handeln ich welt h) \<Longrightarrow> moralisch welt m h\<close>
  apply(simp add: kategorischer_imperativ_def)
  by auto

text\<open>
In Worten:
Wenn eine Maxime den kategorischen Imperativ erfüllt
und es für eine beliebige (wohlgeformte) Handlung auszuführen für mich okay ist diese auszuführen,
dann ist diese Handlung moralisch..
\<close>

text\<open>Für Beispiele wird es einfacher zu zeigen, dass eine Maxime nicht den
kategorischen Imperativ erfüllt, wenn wir direkt ein Beispiel angeben.\<close>
(*insbesondere weil ich das proof document als outline baue und man den beweis,
also das Gegenbeispiel, nicht sieht.*)
definition "kategorischer_imperativ_gegenbeispiel welt_personen_swap welt m h ich p1 p2 \<equiv>
wohlgeformte_handlungsabsicht welt_personen_swap welt h \<and> 
      maxime_und_handlungsabsicht_generalisieren m h ich \<and>
      okay m ich (handeln ich welt h) \<and>
      \<not> okay m p1 (handeln p2 welt h)"

lemma "kategorischer_imperativ_gegenbeispiel welt_personen_swap welt m h ich p1 p2 \<Longrightarrow>
  \<not> kategorischer_imperativ welt_personen_swap welt m"
  apply(simp add: kategorischer_imperativ_simp kategorischer_imperativ_gegenbeispiel_def)
  apply(rule_tac x=h in exI, simp)
  by blast

subsection\<open>Maximen die den Kategorischen Imperativ immer Erfüllen\<close>

text\<open>Wenn eine Maxime jede Handlungsabsicht als moralisch bewertet,
erfüllt diese Maxime den kategorischen Imperativ.
Da diese Maxime jede Handlung erlaubt, ist es dennoch eine wohl ungeeignete Maxime.\<close>
lemma \<open>\<forall>h. moralisch welt maxime h \<Longrightarrow> kategorischer_imperativ welt_personen_swap welt maxime\<close>
  apply(cases \<open>maxime\<close>, rename_tac m)
  by(simp add: kategorischer_imperativ_def moralisch_simp)


text\<open>Eine Maxime die das ich und die Handlung ignoriert und etwas für alle fordert erfüllt den
kategorischen Imperativ.\<close>
lemma blinde_maxime_katimp:
  \<open>kategorischer_imperativ welt_personen_swap welt (Maxime (\<lambda>ich h. \<forall>p. m p))\<close>
  apply(rule kategorischer_imperativI)
  by(simp add: maxime_und_handlungsabsicht_generalisieren_def)



text\<open>Eine Maxime die das ich ignoriert und etwas für alle fordert erfüllt den
kategorischen Imperativ.\<close>
theorem altruistische_maxime_katimp:
  fixes P :: \<open>'person \<Rightarrow> 'world handlung \<Rightarrow> bool\<close>
  assumes kom: \<open>wpsm_kommutiert (Maxime P) welt_personen_swap welt\<close>
      and unrel1: \<open>wpsm_unbeteiligt1 (Maxime P) welt_personen_swap welt\<close>
      and unrel2: \<open>wpsm_unbeteiligt2 (Maxime P) welt_personen_swap welt\<close>
      and welt_personen_swap_sym:
        \<open>\<forall>p1 p2 welt. welt_personen_swap p1 p2 welt = welt_personen_swap p2 p1 welt\<close>
  shows \<open>kategorischer_imperativ welt_personen_swap welt (Maxime (\<lambda>ich h. (\<forall>pX. P pX h)))\<close>
proof(rule kategorischer_imperativI, simp, intro allI)
  fix ha :: \<open>('person, 'world) handlungF\<close>
  and p1 p2 p :: \<open>'person\<close>
  assume wfh: \<open>wohlgeformte_handlungsabsicht welt_personen_swap welt ha\<close>
     and mhg: \<open>maxime_und_handlungsabsicht_generalisieren (Maxime (\<lambda>ich h. \<forall>pX. P pX h)) ha p\<close>
     and okayp: \<open>\<forall>pX. P pX (handeln p welt ha)\<close>

  obtain h where h: \<open>ha = HandlungF h\<close>
    by(cases \<open>ha\<close>, blast)

  from wfh[simplified wohlgeformte_handlungsabsicht_def h]
  have 1: \<open>h p2 welt = welt_personen_swap p p2 (h p (welt_personen_swap p2 p welt))\<close>
    by simp
  from mhg[simplified maxime_und_handlungsabsicht_generalisieren_def h] okayp[simplified h]
  have 2:
  \<open>\<forall>pX. P pX (handeln p (welt_personen_swap p2 p welt) ha)\<close>
    by(auto simp add: h)
  from okayp[simplified h] 2
  have 4:
    \<open>P p (handeln p (welt_personen_swap p2 p welt) ha)\<close>
    by(simp)

  show \<open>P p1 (handeln p2 welt ha)\<close>
  proof(cases \<open>p = p2\<close>)
    case True
    then show \<open>?thesis\<close>
      using okayp by auto 
  next
    case False
    assume \<open>p \<noteq> p2\<close>
    then show \<open>?thesis\<close>
    proof(cases \<open>p1 = p\<close>)
      case True
      assume \<open>p1 = p\<close>
      with 4[simplified handeln.simps h] kom[simplified wpsm_kommutiert_def okay.simps] show \<open>?thesis\<close>
        apply(simp add: h 1)
        using 2[simplified handeln.simps h] welt_personen_swap_sym by fastforce
    next
      case False
      assume \<open>p1 \<noteq> p\<close>
      show \<open>?thesis\<close>
      proof(cases \<open>p1 = p2\<close>)
        case True
        with 4 kom[simplified wpsm_kommutiert_def okay.simps] show \<open>?thesis\<close>
          apply(simp)
          apply(simp add: h 1)
          using welt_personen_swap_sym by fastforce
      next
        case False
        assume \<open>p1 \<noteq> p2\<close>
        with \<open>p \<noteq> p2\<close> \<open>p1 \<noteq> p\<close> show \<open>?thesis\<close>
        using unrel1[simplified wpsm_unbeteiligt1_def]
           unrel2[simplified wpsm_unbeteiligt2_def]
        apply(simp)
        apply(simp add: h)
        using 1[simplified handeln.simps h] 2[simplified handeln.simps h] by metis
      qed
    qed
  qed
qed

text\<open>Auch eine Maxime welche das ich ignoriert,
also nur die Handlung global betrachtet, erfüllt den kategorischen Imperativ.\<close>
theorem globale_maxime_katimp:
  fixes P :: \<open>'world handlung \<Rightarrow> bool\<close>
  assumes kom: \<open>wpsm_kommutiert (Maxime (\<lambda>ich::'person. P)) welt_personen_swap welt\<close>
      and unrel1: \<open>wpsm_unbeteiligt1 (Maxime (\<lambda>ich::'person. P)) welt_personen_swap welt\<close>
      and unrel2: \<open>wpsm_unbeteiligt2 (Maxime (\<lambda>ich::'person. P)) welt_personen_swap welt\<close>
      and welt_personen_swap_sym:
        \<open>\<forall>p1 p2 welt. welt_personen_swap p1 p2 welt = welt_personen_swap p2 p1 welt\<close>
  shows \<open>kategorischer_imperativ welt_personen_swap welt (Maxime (\<lambda>ich::'person. P))\<close>
proof(rule kategorischer_imperativI, simp)
  fix ha :: \<open>('person, 'world) handlungF\<close>
  and p2 p :: \<open>'person\<close>
  assume wfh: \<open>wohlgeformte_handlungsabsicht welt_personen_swap welt ha\<close>
     and mhg: \<open>maxime_und_handlungsabsicht_generalisieren (Maxime (\<lambda>ich. P)) ha p\<close>
     and okayp: \<open>P (handeln p welt ha)\<close>

  obtain h where h: \<open>ha = HandlungF h\<close>
    by(cases \<open>ha\<close>, blast)

  from wfh[simplified wohlgeformte_handlungsabsicht_def h]
  have 1: \<open>h p2 welt = welt_personen_swap p p2 (h p (welt_personen_swap p2 p welt))\<close>
    by simp
  from mhg[simplified maxime_und_handlungsabsicht_generalisieren_def h] okayp[simplified h]
  have 2:
  \<open>P (handeln p (welt_personen_swap p2 p welt) ha)\<close>
    by(auto simp add: h)
  from okayp[simplified h] 2
  have 4:
    \<open>P (handeln p (welt_personen_swap p2 p welt) ha)\<close>
    by(simp)

  show \<open>P (handeln p2 welt ha)\<close>
  proof(cases \<open>p = p2\<close>)
    case True
    then show \<open>?thesis\<close>
      using okayp by auto 
  next
    case False
    assume \<open>p \<noteq> p2\<close>
    with 1[simplified handeln.simps h] 4[simplified handeln.simps h] show \<open>?thesis\<close>
      apply(simp add: h)
      using kom[simplified wpsm_kommutiert_def okay.simps] welt_personen_swap_sym by fastforce
  qed
qed

(*TODO: HandlungF (jeder_zahlt erfuellt kategorischen imp?*)

end
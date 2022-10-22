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
einfach nur in einer Typsignatir auf, was yu tun ist:

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


subsection\<open>Kategorischer Imperativ\<close>

text\<open>
Wir haben mit der goldenen Regel bereits definiert, 
wann für eine gegebene Welt und eine gegebene maxime, eine Handlungsabsicht moralisch ist:

 \<^item> @{term_type \<open>moralisch :: 
     'world \<Rightarrow> ('person, 'world) maxime \<Rightarrow> ('person, 'world) handlungF \<Rightarrow> bool\<close>}

Effektiv testet die goldene Regel eine Handlungsabsicht.

Nach meinem Verständnis generalisiert Kant mit dem Kategorischen Imperativ diese Regel,
indem die Maxime nicht mehr als gegeben angenommen wird,
sondern die Maxime selbst getestet wird.
Sei die Welt weiterhin gegeben,
dass müsste der kategorische Imperativ folgende Typsignatur haben:

  \<^item> \<^typ>\<open>'world \<Rightarrow> ('person, 'world) maxime \<Rightarrow> bool\<close>

Eine Implementierung muss dann über alle möglichen Handlungsabsichten allquantifizieren.

TODO: implementieren!!!
\<close>
(*TODO: kategorischer Imperativ*)

(*
Kategorischer Imperativ umformuliert:

Handle nur nach derjenigen Maxime, durch die du zugleich wollen kannst, 
  dass sie ein allgemeines Gesetz werde.

Handle nur nach derjenigen Maxime, durch die du zugleich wollen kannst,
   dass sie jeder befolgt, im Sinne der goldenen Regel.

Handle nur nach derjenigen Maxime, durch die du zugleich wollen kannst,
   dass sie (Handlung+Maxime) moralisch ist.

Wenn es jemanden gibt der nach einer Maxime handeln will,
   dann muss diese Handlung nach der Maxime moralsich sein.

Für jede Handlungsabsicht muss gelten:
  Wenn jemand in jeder welt nach der Handlungsabsicht handeln würde,
  dann muss diese Handlung moralisch sein.
*)



text\<open>
Für alle möglichen Handlungsabsichten:
Wenn es eine Person gibt für die diese Handlungsabsicht moralisch ist,
dann muss diese Handlungsabsicht auch für alle moralisch (im Sinne der goldenen Regel) sein.
\<close>
fun kategorischer_imperativ
  :: \<open>('person, 'world) wp_swap \<Rightarrow> 'world \<Rightarrow> ('person, 'world) maxime \<Rightarrow> bool\<close>
where
  \<open>kategorischer_imperativ welt_personen_swap welt m =
    (\<forall>h.
          wohlgeformte_handlungsabsicht welt_personen_swap welt h \<and>
          (\<exists>p. maxime_und_handlungsabsicht_generalisieren m h p \<and> okay m p (handeln p welt h))
              \<longrightarrow> moralisch welt m h)\<close>


(*TODO: ist das equivalent einfach \<forall>welt im \<exists>Teil zu fordern?
  kann ich das maxime_und_handlungsabsicht_generalisieren aus dem \<exists> rausziehen?*)


text\<open>Der Existenzquantor lässt sich auch in einen Allquantor umschreiben:\<close>

(*
lemma
  "kategorischer_imperativ welt (Maxime m) \<longleftrightarrow>
    (\<forall>h ich. m ich (handeln ich welt h) \<longrightarrow> moralisch welt (Maxime m) h)"
  apply(simp del: kategorischer_imperativ.simps)
  by(simp)

text\<open>Für jede Handlungsabsicht:
  wenn ich so handeln würde muss es auch okay sein, wenn zwei beliebige
  personen so handeln, wobei iner Täter und einer Opfer ist.\<close>
lemma
  "kategorischer_imperativ welt (Maxime m) \<longleftrightarrow>
    (\<forall>h p1 p2 ich. m ich (handeln ich welt h) \<longrightarrow> m p1 (handeln p2 welt h))"
  by (simp add: moralisch_simp)

(*hmmm, interessant, ...*)
lemma "kategorischer_imperativ welt (Maxime m) \<Longrightarrow>
  (\<forall>h ich. (\<forall>w. m ich (handeln ich w h)) \<longrightarrow> (\<forall>p. m p (handeln ich welt h)))"
  apply(simp add: moralisch_simp)
  by auto

lemma "(\<forall>h ich. (\<forall>w. m ich (handeln ich welt h)) \<longrightarrow> (\<forall>p. m p (handeln ich welt h)))
  \<Longrightarrow> kategorischer_imperativ welt (Maxime m)"
  apply(simp add: moralisch_simp)
  apply(intro allI impI)
  apply(elim exE)
  apply(erule_tac x=h in allE)
  (*quickcheck found a counterexample*)
  oops

*)
text\<open>WOW:

Die Maxime die keine Handlung erlaubt (weil immer False) erfüllt den kategorischen
Imperativ\<close>
lemma "kategorischer_imperativ welt_personen_swap welt (Maxime (\<lambda>ich h. False))"
  by(simp)

lemma "\<not> moralisch welt (Maxime (\<lambda>ich h. False)) h"
  by(simp add: moralisch_simp)


lemma "kategorischer_imperativ welt_personen_swap welt (Maxime (\<lambda>ich h. True))"
  by(simp add: moralisch_simp)

lemma "moralisch welt (Maxime (\<lambda>ich h. True)) h"
  by(simp add: moralisch_simp)

(*
lemma "kategorischer_imperativ welt_personen_swap welt (Maxime (\<lambda>ich_ignored h. P h))"
  apply(simp add: moralisch_simp)
  apply(intro allI impI, elim exE)
  oops (*hmmm, bekomme ich das mit dem Steuersystem verbunden?*)
*)

(*Wenn wir wirklich \<forall>handlungsabsichten haben, dann sollte sich das vereinfachen lassen
zu
(\<forall>h :: ('person, 'world) handlungF.
    (\<exists>p::'person. m p (handeln p welt h)) \<longrightarrow> (\<forall>p::'person. m p ()))

value \<open>kat_imperativ (0::nat) (Maxime (\<lambda> ich handlung. True))\<close>
*)

  thm goldene_regel
(*
TODO: Erkläre

Handlung fuer mich okay == m ich (handeln ich welt h) 
*)


lemma "kategorischer_imperativ welt_personen_swap welt m \<Longrightarrow>
  wohlgeformte_handlungsabsicht welt_personen_swap welt h \<Longrightarrow>
  maxime_und_handlungsabsicht_generalisieren m h ich \<Longrightarrow>
  okay m ich (handeln ich welt h) \<Longrightarrow> moralisch welt m h"
  apply(simp)
  by auto

lemma kategorischer_imperativI:
  "(\<And>h p1 p2 p. wohlgeformte_handlungsabsicht welt_personen_swap welt h \<Longrightarrow>
   maxime_und_handlungsabsicht_generalisieren m h p \<Longrightarrow>
   okay m p (handeln p welt h) \<Longrightarrow> okay m p1 (handeln p2 welt h)
   )
 \<Longrightarrow> kategorischer_imperativ welt_personen_swap welt m"
  by(auto simp add: moralisch_simp)

(*Welt in ihrem aktuellen Zustand. TODO: eigentlich sollten wir für jede mögliche Welt testen!*)

text\<open>Wenn eine Maxime jede Handlungsabsicht als morlaisch bewertet
erfüllt diese Maxime den kategorischen Imperativ.
Da diese Maxime jede Handlung erlaubt, ist es dennoch eine wohl ungeeignete Maxime.\<close>
lemma "\<forall>h. moralisch welt maxime h \<Longrightarrow> kategorischer_imperativ welt_personen_swap welt maxime"
  apply(cases maxime, rename_tac m)
  by(simp add: moralisch_simp)


text\<open>Eine Maxime die das ich und die Handlung ignoriert und etwas für alle fordert erfüllt den
kategorischen Imperativ.\<close>
lemma blinde_maxime_katimp:
  "kategorischer_imperativ welt_personen_swap welt (Maxime (\<lambda>ich h. \<forall>p. m p))"
  apply(rule kategorischer_imperativI)
  by(simp add: maxime_und_handlungsabsicht_generalisieren_def)



text\<open>Eine Maxime die das ich ignoriert und etwas für alle fordert erfüllt den
kategorischen Imperativ.\<close>
(*
theorem altruistische_maxime_katimp:
  fixes P :: "'person \<Rightarrow> 'world handlung \<Rightarrow> bool"
  assumes kom: "wpsm_kommutiert (Maxime P) welt_personen_swap welt"
      and unrel1: "wpsm_unbeteiligt1 (Maxime P) welt_personen_swap welt"
      and unrel2: "wpsm_unbeteiligt2 (Maxime P) welt_personen_swap welt"
      and welt_personen_swap_sym: "\<forall>p1 p2 welt. welt_personen_swap p1 p2 welt = welt_personen_swap p2 p1 welt"
  shows "kategorischer_imperativ welt_personen_swap welt (Maxime (\<lambda>ich h. (\<forall>pX. P pX h)))"
  apply(simp add: moralisch_simp)
  apply(intro allI impI, elim conjE exE)
  apply(rename_tac h p2 p1 p)
  apply(case_tac h, rename_tac ha p2 p1 p h, simp)
  apply(simp add: wohlgeformte_handlungsabsicht_def)

  apply(case_tac "p = p2")
   apply(simp; fail)

  apply(subgoal_tac "P p1 (Handlung welt (h p welt))")
   prefer 2 apply(simp; fail)

  apply(erule_tac x=p2 in allE)
  apply(erule_tac x=p in allE) back
  apply(elim conjE)
  apply(thin_tac "welt = _")
  apply(simp)
  apply(thin_tac "h p2 welt = _")
  apply(simp add: maxime_und_handlungsabsicht_generalisieren_def)

  apply(case_tac "p1 = p", simp)
   apply(erule_tac x="welt_personen_swap p p2 welt" in allE)
   apply(erule_tac x="welt" in allE)

   apply(case_tac "(\<forall>pX. P pX
              (Handlung (welt_personen_swap p p2 welt)
                (h p (welt_personen_swap p p2 welt))))")
    prefer 2 apply(simp; fail)
   apply(simp)
   apply(erule_tac x=p2 in allE) back
  using kom[simplified wpsm_kommutiert_def] apply(simp; fail)


  apply(case_tac "p1 = p2")
   apply(simp)
   apply(erule_tac x="welt_personen_swap p2 p welt" in allE)
   apply(erule_tac x="welt" in allE)
   apply(case_tac "(\<forall>pX. P pX
              (Handlung (welt_personen_swap p2 p welt)
                (h p (welt_personen_swap p2 p welt))))")
    prefer 2 apply(simp; fail)
   apply(simp)
   apply(erule_tac x=p in allE) back
  using kom[simplified wpsm_kommutiert_def]
  using welt_personen_swap_sym apply fastforce 

  apply(erule_tac x="welt_personen_swap p2 p welt" in allE)
  apply(erule_tac x="welt" in allE)
  apply(simp)
  apply(erule_tac x=p1 in allE) back
  using unrel1[simplified wpsm_unbeteiligt1_def] 
  apply(simp)
  apply(erule_tac x=p in allE) back
  apply(erule_tac x=p2 in allE) back
  apply(elim impE, (simp; fail))
  apply(erule_tac x=p1 in allE) back
  apply(elim impE, (simp; fail)+)

  using unrel2[simplified wpsm_unbeteiligt2_def] apply(simp)
  done
*)

theorem altruistische_maxime_katimp:
  fixes P :: "'person \<Rightarrow> 'world handlung \<Rightarrow> bool"
  assumes kom: "wpsm_kommutiert (Maxime P) welt_personen_swap welt"
      and unrel1: "wpsm_unbeteiligt1 (Maxime P) welt_personen_swap welt"
      and unrel2: "wpsm_unbeteiligt2 (Maxime P) welt_personen_swap welt"
      and welt_personen_swap_sym:
        "\<forall>p1 p2 welt. welt_personen_swap p1 p2 welt = welt_personen_swap p2 p1 welt"
  shows "kategorischer_imperativ welt_personen_swap welt (Maxime (\<lambda>ich h. (\<forall>pX. P pX h)))"
proof(rule kategorischer_imperativI, simp, intro allI)
  fix ha :: "('person, 'world) handlungF"
  and p1 p2 p :: 'person
  assume wfh: "wohlgeformte_handlungsabsicht welt_personen_swap welt ha"
     and mhg: "maxime_und_handlungsabsicht_generalisieren (Maxime (\<lambda>ich h. \<forall>pX. P pX h)) ha p"
     and okayp: "\<forall>pX. P pX (handeln p welt ha)"

  obtain h where h: "ha = HandlungF h"
    by(cases ha, blast)

  from wfh[simplified wohlgeformte_handlungsabsicht_def h]
  have 1: "h p2 welt = welt_personen_swap p p2 (h p (welt_personen_swap p2 p welt))"
    by simp
  from mhg[simplified maxime_und_handlungsabsicht_generalisieren_def h] okayp[simplified h]
  have 2:
  "\<forall>pX. P pX (handeln p (welt_personen_swap p2 p welt) ha)"
    by(auto simp add: h)
  from okayp[simplified h] 2
  have 4:
    "P p (handeln p (welt_personen_swap p2 p welt) ha)"
    by(simp)

  show "P p1 (handeln p2 welt ha)"
  proof(cases "p = p2")
    case True
    then show ?thesis
      using okayp by auto 
  next
    case False
    assume "p \<noteq> p2"
    then show ?thesis
    proof(cases "p1 = p")
      case True
      assume "p1 = p"
      with 4[simplified handeln.simps h] kom[simplified wpsm_kommutiert_def okay.simps] show ?thesis
        apply(simp add: h 1)
        using 2[simplified handeln.simps h] welt_personen_swap_sym by fastforce
    next
      case False
      assume "p1 \<noteq> p"
      show ?thesis
      proof(cases "p1 = p2")
        case True
        with 4 kom[simplified wpsm_kommutiert_def okay.simps] show ?thesis
          apply(simp)
          apply(simp add: h 1)
          using welt_personen_swap_sym by fastforce
      next
        case False
        assume "p1 \<noteq> p2"
        with \<open>p \<noteq> p2\<close> \<open>p1 \<noteq> p\<close> show ?thesis
        using unrel1[simplified wpsm_unbeteiligt1_def]
           unrel2[simplified wpsm_unbeteiligt2_def]
        apply(simp)
        apply(simp add: h)
        using 1[simplified handeln.simps h] 2[simplified handeln.simps h] by metis
      qed
    qed
  qed
qed

text\<open>Maxime welche das ich ignoriert, also nur die Handlung global betrachtet.\<close>
theorem globale_maxime_katimp:
  fixes P :: "'world handlung \<Rightarrow> bool"
  assumes kom: "wpsm_kommutiert (Maxime (\<lambda>ich::'person. P)) welt_personen_swap welt"
      and unrel1: "wpsm_unbeteiligt1 (Maxime (\<lambda>ich::'person. P)) welt_personen_swap welt"
      and unrel2: "wpsm_unbeteiligt2 (Maxime (\<lambda>ich::'person. P)) welt_personen_swap welt"
      and welt_personen_swap_sym:
        "\<forall>p1 p2 welt. welt_personen_swap p1 p2 welt = welt_personen_swap p2 p1 welt"
  shows "kategorischer_imperativ welt_personen_swap welt (Maxime (\<lambda>ich::'person. P))"
proof(rule kategorischer_imperativI, simp)
  fix ha :: "('person, 'world) handlungF"
  and p2 p :: 'person
  assume wfh: "wohlgeformte_handlungsabsicht welt_personen_swap welt ha"
     and mhg: "maxime_und_handlungsabsicht_generalisieren (Maxime (\<lambda>ich. P)) ha p"
     and okayp: "P (handeln p welt ha)"

  obtain h where h: "ha = HandlungF h"
    by(cases ha, blast)

  from wfh[simplified wohlgeformte_handlungsabsicht_def h]
  have 1: "h p2 welt = welt_personen_swap p p2 (h p (welt_personen_swap p2 p welt))"
    by simp
  from mhg[simplified maxime_und_handlungsabsicht_generalisieren_def h] okayp[simplified h]
  have 2:
  "P (handeln p (welt_personen_swap p2 p welt) ha)"
    by(auto simp add: h)
  from okayp[simplified h] 2
  have 4:
    "P (handeln p (welt_personen_swap p2 p welt) ha)"
    by(simp)

  show "P (handeln p2 welt ha)"
  proof(cases "p = p2")
    case True
    then show ?thesis
      using okayp by auto 
  next
    case False
    assume "p \<noteq> p2"
    with 1[simplified handeln.simps h] 4[simplified handeln.simps h] show ?thesis
      apply(simp add: h)
      using kom[simplified wpsm_kommutiert_def okay.simps] welt_personen_swap_sym by fastforce
  qed
qed

end
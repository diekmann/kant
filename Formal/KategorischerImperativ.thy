theory KategorischerImperativ
imports Maxime Gesetz
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


(*TODO: move to Handlung? Gleiched fuer maxime.*)
(*welt rawls schleier um handlung verallgemeinern. Definition*)
definition wohlgeformte_handlungsabsicht
  :: "('person \<Rightarrow> 'person \<Rightarrow> 'world \<Rightarrow> 'world) \<Rightarrow>
      'world \<Rightarrow> ('person, 'world) handlungF
      \<Rightarrow> bool"
where
  "wohlgeformte_handlungsabsicht welt_personen_swap welt h \<equiv>
    \<forall>p1 p2. (handeln p1 welt h) =
            map_handlung (welt_personen_swap p2 p1) (handeln p2 (welt_personen_swap p1 p2 welt) h)"


fun maxime_und_handlungsabsicht_generalisieren
  :: "('person, 'world) maxime \<Rightarrow> ('person, 'world) handlungF \<Rightarrow> 'person \<Rightarrow> bool"
where
  "maxime_und_handlungsabsicht_generalisieren m h p =
    (\<forall>w1 w2. okay m p (handeln p w1 h) \<longleftrightarrow> okay m p (handeln p w2 h))"
  

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
  :: \<open>('person \<Rightarrow> 'person \<Rightarrow> 'world \<Rightarrow> 'world) \<Rightarrow> 'world \<Rightarrow> ('person, 'world) maxime \<Rightarrow> bool\<close>
where
  \<open>kategorischer_imperativ welt_personen_swap welt m =
    (\<forall>h.
          wohlgeformte_handlungsabsicht welt_personen_swap welt h \<and>
          (\<exists>p. maxime_und_handlungsabsicht_generalisieren m h p \<and> okay m p (handeln p welt h))
              \<longrightarrow> moralisch welt m h)\<close>

(* Hat was von dem Urzustand Schleier von Rawls? *)

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

Die Maxime die keine Handlung erlaubt (weil immer False) erfuellt den kategorischen
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
Handlung fuer mich okay == m ich (handeln ich welt h) 
*)


(*TODO: das \<forall>w1 w2. will ne definition*)
lemma "kategorischer_imperativ welt_personen_swap welt m \<Longrightarrow>
  wohlgeformte_handlungsabsicht welt_personen_swap welt h \<Longrightarrow>
  (\<forall>w1 w2. okay m ich (handeln ich w1 h) = okay m ich (handeln ich w2 h)) \<Longrightarrow>
  okay m ich (handeln ich welt h) \<Longrightarrow> moralisch welt m h"
  apply(simp)
  by auto

  



(*Welt in ihrem aktuellen Zustand. TODO: eigentlich sollten wir für jede mögliche Welt testen!*)

text\<open>Wenn eine Maxime jede Handlungsabsicht als morlaisch bewertet
erfüllt diese Maxime den kategorischen Imperativ.
Da diese Maxime jede Handlung erlaubt, ist es dennoch eine wohl ungeeignete Maxime.\<close>
lemma "\<forall>h. moralisch welt maxime h \<Longrightarrow> kategorischer_imperativ welt_personen_swap welt maxime"
  apply(cases maxime, rename_tac m)
  by(simp add: moralisch_simp)

(*
text\<open>Eine Maxime die das ich und die Handlung ignoriert und etwas für alle fordert erfüllt den
kategorischen Imperativ.\<close>
lemma blinde_maxime_katimp:
  "kategorischer_imperativ welt_personen_swap welt (Maxime (\<lambda>ich h. \<forall>p. m p))"
  apply(simp add: moralisch_simp)


*)




definition "Maxime_kommutiert m welt_personen_swap welt \<equiv> \<forall> p1 p2 h.
  okay m p2 (Handlung (welt_personen_swap p1 p2 welt) (h p1 (welt_personen_swap p1 p2 welt)))
  \<longleftrightarrow>
  okay m p1 (Handlung welt (welt_personen_swap p1 p2 (h p1 (welt_personen_swap p2 p1 welt))))"

definition "Maxime_swap_unrelated m welt_personen_swap (welt::'world) \<equiv> \<forall> p1 p2 pX h (welt'::'world).
  p1 \<noteq> p2 \<longrightarrow> pX \<noteq> p1 \<longrightarrow> pX \<noteq> p2 \<longrightarrow>
  okay m pX (Handlung welt (welt_personen_swap p1 p2 (h p1 welt')))
  \<longleftrightarrow>
  okay m pX (Handlung welt (h p1 welt'))"


(*TODO: die 3 Eiggenschaften sind nur ueber die Maxime und die swap funktion.
evtl muss ich die in den kategorischen imperativ uebernehmen?
Auf jeden fall sollte ich testen, ob das auch fuer den globalen fortschritt gilt!
*)
text\<open>Eine Maxime die das ich ignoriert und etwas für alle fordert erfüllt den
kategorischen Imperativ.\<close>
theorem altruistische_maxime_katimp:
  assumes kom: "Maxime_kommutiert (Maxime P) welt_personen_swap welt"
     and unrel1: "Maxime_swap_unrelated (Maxime P) welt_personen_swap welt"
    (* das ist Maxime_swap_unrelated nur auf 1. param.*)
     and unrel2: "\<forall> p1 p2 pX welt'.
  p1 \<noteq> p2 \<longrightarrow> pX \<noteq> p1 \<longrightarrow> pX \<noteq> p2 \<longrightarrow> 
    P pX (Handlung (welt_personen_swap p2 p1 welt) welt')
    \<longleftrightarrow> P pX (Handlung welt welt')"
     and welt_personen_swap_sym: "\<forall>p1 p2 welt. welt_personen_swap p1 p2 welt = welt_personen_swap p2 p1 welt"
  shows "kategorischer_imperativ welt_personen_swap welt
    (Maxime (\<lambda>ich h. (\<forall>pX::'person. P pX h)))"
  apply(simp add: moralisch_simp)
  apply(intro allI impI, elim conjE exE)
  apply(simp add: wohlgeformte_handlungsabsicht_def)
  apply(case_tac h, rename_tac ha p2 pX p1 h, simp)


  apply(subgoal_tac "P pX (Handlung welt (h p1 welt))")
   prefer 2 apply(simp; fail)

  apply(erule_tac x=p2 in allE)
  apply(erule_tac x=p1 in allE) back
  apply(elim conjE)
  apply(simp)
  apply(thin_tac "welt = _")
  apply(case_tac "p1 = p2")
   apply(simp; fail)
  apply(thin_tac "h p2 welt = _")

  apply(case_tac "pX = p1", simp)
   apply(erule_tac x="welt_personen_swap p1 p2 welt" in allE)
   apply(erule_tac x="welt" in allE)

   apply(case_tac "(\<forall>pX. P pX
              (Handlung (welt_personen_swap p1 p2 welt)
                (h p1 (welt_personen_swap p1 p2 welt))))")
    prefer 2 apply(simp; fail)
   apply(simp)
   apply(erule_tac x=p2 in allE) back
  using kom[simplified Maxime_kommutiert_def] apply(simp; fail)


  apply(case_tac "pX = p2")
   apply(simp)
   apply(erule_tac x="welt_personen_swap p2 p1 welt" in allE)
   apply(erule_tac x="welt" in allE)
   apply(case_tac "(\<forall>pX. P pX
              (Handlung (welt_personen_swap p2 p1 welt)
                (h p1 (welt_personen_swap p2 p1 welt))))")
    prefer 2 apply(simp; fail)
   apply(simp)
   apply(erule_tac x=p1 in allE) back
  using kom[simplified Maxime_kommutiert_def]
  using welt_personen_swap_sym apply fastforce 

  apply(erule_tac x="welt_personen_swap p2 p1 welt" in allE)
  apply(erule_tac x="welt" in allE)
  apply(simp)
  apply(erule_tac x=pX in allE) back
  using unrel1[simplified Maxime_swap_unrelated_def] 
  apply(simp)
  apply(erule_tac x=p1 in allE) back
  apply(erule_tac x=p2 in allE) back
  apply(elim impE, (simp; fail))
  apply(erule_tac x=pX in allE) back
  apply(elim impE, (simp; fail)+)

  apply(simp add: unrel2)
  done

end
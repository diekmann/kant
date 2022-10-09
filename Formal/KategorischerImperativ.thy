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
fun kat_imperativ ::
  \<open>'world \<Rightarrow> ('person, 'world) maxime \<Rightarrow> bool\<close> where
\<open>kat_imperativ welt (Maxime m) =
  (\<forall>h :: ('person, 'world) handlungF.
    (\<exists>p::'person. m p (handeln p welt h)) \<longrightarrow> moralisch welt (Maxime m) h)\<close>

ist der \<exists> wirklich korrekt? Eigentlich will ich doch \<forall>*)

(*Wenn wir wirklich \<forall>handlungsabsichten haben, dann sollte sich das vereinfachen lassen
zu
(\<forall>h :: ('person, 'world) handlungF.
    (\<exists>p::'person. m p (handeln p welt h)) \<longrightarrow> (\<forall>p::'person. m p ()))

value \<open>kat_imperativ (0::nat) (Maxime (\<lambda> ich handlung. True))\<close>
*)

(*Welt in ihrem aktuellen Zustand. TODO: eigentlich sollten wir für jede mögliche Welt testen!*)



end
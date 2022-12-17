theory AllgemeinesGesetz
imports Gesetz Maxime
begin

section\<open>Experimental: Moralisch Gesetzs Ableiten\<close>
subsection\<open>Allgemeines Gesetz Ableiten\<close>

text\<open>Wir wollen implementieren:

\<^emph>\<open>„Handle nur nach derjenigen Maxime, durch die du zugleich wollen kannst,
   dass sie ein \<^bold>\<open>allgemeines Gesetz\<close> werde.“\<close>

Für eine gebene Welt haben wir schon eine Handlung nach einer Maxime untersucht:
\<^term>\<open>moralisch::'welt \<Rightarrow> ('person, 'welt) maxime \<Rightarrow> ('person, 'welt) handlungsabsicht \<Rightarrow> bool\<close>

Das Ergebnis sagt uns ob diese Handlung gut oder schlecht ist.
Basierend darauf müssen wir nun ein allgemeines Gesetz ableiten.

Ich habe keine Ahnung wie das genau funktionieren soll, deswegen schreibe ich
einfach nur in einer Typsignatur auf, was zu tun ist:

Gegeben:
  \<^item> \<^typ>\<open>'welt handlung\<close>: Die Handlung
  \<^item> \<^typ>\<open>sollensanordnung\<close>: Das Ergebnis der moralischen Bewertung, ob die Handlung gut/schlecht.

Gesucht:
  \<^item> \<^typ>\<open>('a, 'b) rechtsnorm\<close>: ein allgemeines Gesetz
\<close>

type_synonym ('welt, 'a, 'b) allgemeines_gesetz_ableiten =
  \<open>'welt handlung \<Rightarrow> sollensanordnung \<Rightarrow> ('a, 'b) rechtsnorm\<close>

text\<open>
Soviel vorweg:
Nur aus einer von außen betrachteten Handlung
und einer Entscheidung ob diese Handlung ausgeführt werden soll
wird es schwer ein allgemeines Gesetz abzuleiten.
\<close>
(*TODO: waere hier ('person, 'welt) handlungsabsicht anstatt 'welt handlung besser?*)

subsection\<open>Implementierung Moralisch ein Allgemeines Gesetz Ableiten\<close>
(*TODO: unterstütze viele Maximen, wobei manche nicht zutreffen können?*)
text\<open>Und nun werfen wir alles zusammen:

\<^emph>\<open>„Handle nur nach derjenigen Maxime, durch die du zugleich wollen kannst,
   dass sie ein allgemeines Gesetz werde.“\<close>


Eingabe:
 \<^item> \<^typ>\<open>'person\<close>: handelnde Person
 \<^item> \<^typ>\<open>'welt\<close>: Die Welt in ihrem aktuellen Zustand
 \<^item> \<^typ>\<open>('person, 'welt) handlungsabsicht\<close>: Eine mögliche Handlung,
    über die wir entscheiden wollen ob wir sie ausführen sollten.
 \<^item> \<^typ>\<open>('person, 'welt) maxime\<close>: Persönliche Ethik.
 \<^item> \<^typ>\<open>('welt, 'a, 'b) allgemeines_gesetz_ableiten\<close>:
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
   'welt \<Rightarrow>
   ('person, 'welt) maxime \<Rightarrow>
   ('person, 'welt) handlungsabsicht \<Rightarrow>
   ('welt, 'a, 'b) allgemeines_gesetz_ableiten \<Rightarrow>
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


end
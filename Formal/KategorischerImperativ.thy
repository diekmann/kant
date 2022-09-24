theory KategorischerImperativ
imports Maxime Gesetz
begin

section\<open>Kategorischer Imperativ\<close>
subsection\<open>Allgemeines Gesetz Ableiten\<close>

text\<open>Wir wollen implementieren:

\<^emph>\<open>„Handle nur nach derjenigen Maxime, durch die du zugleich wollen kannst,
   dass sie ein \<^bold>\<open>allgemeines Gesetz\<close> werde.“\<close>

Für eine gebene Welt haben wir schon eine Handlung nach einer Maxime untersucht:
\<^term>\<open>teste_maxime::'world \<Rightarrow> ('person, 'world) handlungF \<Rightarrow> ('person, 'world) maxime \<Rightarrow> bool\<close>

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

subsection\<open>Implementierung Kategorischer Imperativ.\<close>
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

definition kategorischer_imperativ ::
  \<open>'person \<Rightarrow>
   'world \<Rightarrow>
   ('person, 'world) handlungF \<Rightarrow>
   ('person, 'world) maxime \<Rightarrow>
   ('world, 'a, 'b) allgemeines_gesetz_ableiten \<Rightarrow>
   (nat, 'a, 'b) gesetz
  \<Rightarrow> (sollensanordnung \<times> (nat, 'a, 'b) gesetz)\<close>
where
  \<open>kategorischer_imperativ ich welt handlung maxime gesetz_ableiten gesetz \<equiv>
    let soll_handeln = if teste_maxime welt handlung maxime
                       then
                         Erlaubnis
                       else
                         Verbot in
      (
        soll_handeln,
        hinzufuegen (gesetz_ableiten (handeln ich welt handlung) soll_handeln) gesetz
      )\<close>


end
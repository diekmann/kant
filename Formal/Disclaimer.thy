theory Disclaimer
imports Main
begin

section\<open>Disclaimer\<close>
text\<open>
Ich habe
  \<^item> mir philosophische Grundlagen nur im Selbststudium beigebracht. Meine Primärquellen sind
    \<^item> Die deutsche Übersetzung von Bertrand Russells 1946 erstveröffentlichtem
      "History of Western Philosophy" \cite{russellphi}.
      Von diesem Buch existiert auch eine Onlinefassung
      \<^url>\<open>https://archive.org/details/PHILOSOPHIEDESABENDLANDESVONBERTRANDRUSSEL\<close>.
    \<^item> Eva Böhringers YouTube Kanal "Ethik-Abi by BOE" \<^url>\<open>https://www.youtube.com/@EthikAbibyBOE\<close>.
    \<^item> Wikipedia im Allgemeinen.
      Innerhalb des Dokuments versuche ich Definitionen aus Wikipedia zu verwenden,
      da diese einfach und ohne Paywall zugänglich sind.
    \<^item> Weitere Bücher oder Internetquellen ohne herausragende Bedeutung für mich.
      Zu Beispiel stand mein "Kant für die Hand" Würfel ohne große Einsicht sehr lange herum,
      bis er schließlich dem Kind zum Opfer fiel.
  \<^item> wenig Ahnung von deutschem Steuerrecht. Das Steuer-Beispiel im hinteren Abschnitt dieses
    Dokuments ist zwar an das deutsche Einkommensteuerrecht angelehnt (Quelle: Wikipedia),
    dennoch ist dieses Beispiel nur der Idee nach richtig.
    Faktisch ist es falsch und ich empfehle niemanden seine Steuererklärung basierend auf dieser
    Theorie zu machen.
  \<^item> keine Ahnung von Jura und Strafrecht.
    Die thys enthalten noch ein fehlgeschlagenes Experiment welches versucht aus dem kategorischen
    Imperativ ein Gesetz (im rechtlichen Sinne) abzuleiten.
    Dieses Experiment ist allerdings fehlgeschlagen und ist auch nicht im kompilierten pdf Dokument
    enthalten.

Dieses Dokument ist ein instabiler Development Snapshot,
entwickelt auf \<^url>\<open>https://github.com/diekmann/kant\<close>.
Er enthält sinnvolles und weniger sinnvolle Experimente!

\<^bigskip>
  Cheers!
\<close>

subsection\<open>Über den Titel\<close>
text\<open>
Der Titel lautet \<^emph>\<open>Extensionale Interpretation des Kategorischen Imperativs\<close>.
Dabei sind die Wörter wie folgt zu verstehen

  \<^item> \<^emph>\<open>Extensional\<close> bezieht sich hier auf den Fachbegriff der Logik
    \<^url>\<open>https://en.wikipedia.org/wiki/Extensionality\<close>, welcher besagt,
    dass Objekte gleich sind, wenn sie die gleichen externen Eigenschaften aufweisen.
    Beispielsweise sind zwei Funktionen gleich,
    wenn sie für alle Eingaben die gleiche Ausgabe liefern: @{thm fun_eq_iff}.
    Die interne (intensionale) Implementierung der Funktionen mag unterschiedlich sein,
    dennoch sind sie gleich.
    Dies ist die natürliche Gleichheit in HOL, welche uns erlaubt unser Modell
    bequem zu shallow-embedden.
    Meine extensionale Modellierung prägt diese Theorie stark.
    Beispielsweise sind Handlungen extensional modelliert, 
    d.h nur die äußerlich messbaren Ergebnisse werden betrachtet.
    Dies widerspricht vermutlich stark Kants Vorstellung.
  \<^item> \<^emph>\<open>Interpretation\<close> besagt, dass es sic hier um meine persönliche Interpretation handelt.
    Diese Theorie ist keine strenge Formalisierung der Literatur,
    sondern enthält sehr viele persönliche Meinungen.
  \<^item> \<^emph>\<open>Kategorischer Imperativ\<close> bezieht sich auf Kants Kategorischer Imperativ.
    Ziel dieser Theorie ist es, moralische Entscheidungen basierend auf Kants Idee zu machen.


Der Titel in einfacher Sprache:
Der kategorische Imperativ, aber wohl nicht so wie Kant ihn gedacht hat,
also, dass nur der innere, gute Wille zählt,
sondern die gegenteilige Umsetzung,
bei der wir uns auf die Ergebnisse einer Handlung fokussieren.
\<close>

end
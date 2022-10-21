theory Disclaimer
imports Main
begin

section\<open>Disclaimer\<close>
text\<open>
Ich habe
  \<^item> kein Ahnung von Philosophie.
  \<^item> keine Ahnung von Recht und Jura.
  \<^item> und schon gar keine Ahnung von Strafrecht oder Steuerrecht.

Und in dieser Session werden ich all das zusammenwerfen.

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
    Beispielweise sind Handlungen extensional modelliert, 
    d.h nur die äußerlich messbaren Ergebnisse werden betrachtet.
    Dies widerspricht vermutlich stark Kants Vorstellung.
  \<^item> \<^emph>\<open>Interpretation\<close> besagt, dass es sic hier um meine persönliche Interpretation handelt.
    Diese Theorie ist keine strenge Formalisierung der Literatur,
    sondern enthält sehr viele persönliche Meinungen.
  \<^item> \<^emph>\<open>Kategorischer Imperativ\<close> bezieht sich auf Kants Kategorischer Imperativ.
    Ziel dieser Theorie ist es, moralische Entscheidungen basierend auf Kants Idee zu machen.
\<close>

end
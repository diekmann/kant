theory SchnelleinstiegHOL
  imports Main BeispielTac
begin

section\<open>Schnelleinstieg Isabelle/HOL\<close>

subsection\<open>Typen\<close>
text\<open>Typen werden per \<^verbatim>\<open>::\<close> annotiert.
Beispielsweise sagt \<^theory_text>\<open>3::nat\<close>, dass \<^term>\<open>3::nat\<close> eine natürliche Zahl (\<^typ>\<open>nat\<close>) ist.\<close>

subsection\<open>Beweise\<close>
text\<open>Die besondere Fähigkeit im Beweisassistent Isabelle/HOL liegt darin,
maschinengeprüfte Beweise zu machen.

Beispiel:\<close>

lemma \<open>3 = 2+1\<close> by simp

text\<open>In der PDFversion wird der eigentliche Beweis ausgelassen.
Aber keine Sorge, der Computer hat den Beweis überprüft.
Würde der Beweis nicht gelten, würde das PDF garnicht compilieren.

Ich wurde schon für meine furchtbaren Beweise zitiert.
Ist also ganz gut, dass wir nur Ergebnisse im PDF sehen und der eigentliche Beweis ausgelassen ist.
Am besten kann man Beweise sowieso im Isabelle Editor anschauen und nicht im PDF.

Wir werden die meisten Hilfsfakten als @{command lemma} kennzeichnen.
Wichtige Fakten werden wir @{command theorem} nennen.
Zusätzlich führen wir noch das @{command beispiel} Kommando ein,
um Lemmata von Beispielen zu unterscheiden.

Folgende drei Aussagen sind alle equivalent und maschinengeprüft korrekt:
\<close>


lemma \<open>3 = 2+1\<close> by simp
theorem \<open>3 = 2+1\<close> by simp
beispiel \<open>3 = 2+1\<close> by simp

subsection\<open>Mehr Typen\<close>
text\<open>Jeder Typ der mit einem einfachen Anführungszeichen anfängt ist ein polymorpher Typ.
Beispiel: \<^typ>\<open>'a\<close> oder \<^typ>\<open>'\<alpha>\<close>.
So ein Typ ist praktisch ein generischer Typ,
welcher durch jeden anderen Typen instanziiert werden kann.


Beispielsweise steht \<^typ>\<open>'nat\<close> für einen beliebigen Typen,
während \<^typ>\<open>nat\<close> der konkrete Typ der natürlichen Zahlen ist.

Wenn wir nun \<^theory_text>\<open>3::'a\<close> schreiben handelt es sich nur um das generische Numeral 3.
Das ist so generisch, dass z.B. noch nicht einmal die Plusoperation darauf definiert ist.
Im Gegensatz dazu ist \<^theory_text>\<open>3::nat\<close> die natürliche Zahl 3,
mit allen wohlbekannten Rechenoperationen.
Im Beweis obigen \<^theory_text>\<open>lemma\<open>3 = 2+1\<close>\<close> hat Isabelle die Typen automatisch inferiert.
\<close>

subsection\<open>Funktionen\<close>
text\<open>Beispiel:
Eine Funktionen welche eine natürliche Zahl nimmt und
eine natürliche Zahl zurück gibt (\<^typ>\<open>nat \<Rightarrow> nat\<close>):\<close>

fun beispielfunktion :: \<open>nat \<Rightarrow> nat\<close> where
  \<open>beispielfunktion n = n + 10\<close>


text\<open>Funktionsaufrufe funktionieren ohne Klammern.\<close>

beispiel \<open>beispielfunktion 32 = 42\<close> by eval

text\<open>Funktionen sind gecurried. Hier ist eine Funktion welche 2 natürliche Zahlen nimmt
und eine natürliche Zahl zurück gibt (\<^typ>\<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close>):\<close>
fun addieren :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>addieren a b = a + b\<close>

beispiel \<open>addieren 32 10 = 42\<close> by eval

text\<open>Currying bedeutet auch, wenn wir \<^const>\<open>addieren\<close> nur mit einem Argument aufrufen
(welches eine natürliche Zahl \<^typ>\<open>nat\<close> sein muss),
dass wir eine Funktion zurückbekommen, die noch das zweite Argument erwartet,
bevor sie das Ergebnis zurückgeben kann.

Beispiel: \<^term_type>\<open>(addieren 10) :: (nat \<Rightarrow> nat)\<close>

Zufälligerweise ist \<^term>\<open>addieren 10\<close> equivalent zu \<^term>\<open>beispielfunktion\<close>:
\<close>
beispiel \<open>addieren 10 = beispielfunktion\<close>
  by(simp add: fun_eq_iff)


text\<open>Zusätzlich lassen sich Funktionen im Lambda Calculus darstellen.
Beispiel:\<close>

beispiel \<open>(\<lambda>n::nat. n+10) 3 = 13\<close> by eval

beispiel \<open>beispielfunktion = (\<lambda>n. n+10)\<close>
  by(simp add: fun_eq_iff)

subsection\<open>Mengen\<close>
text\<open>Mengen funktionieren wie normale mathematische Mengen.

Beispiel. Die Menge der geraden Zahlen:
\<close>
beispiel \<open>{0,2,4,6,8,10,12} \<subseteq> {n::nat. n mod 2 = 0}\<close>
  by(simp)

beispiel \<open>{0,2,4,6,8,10} = {n::nat. n mod 2 = 0 \<and> n \<le> 10}\<close>
  by fastforce

text\<open>Bei vorherigen Beispiel können wir das Prinzip der (mathematischen) \<^emph>\<open>Extensionalität\<close> sehen:
Intensional sind die beiden Mengen \<^term>\<open>{0,2,4,6,8,10}::nat set\<close> und \<^term>\<open>{n::nat. n mod 2 = 0 \<and> n \<le> 10}\<close>
verschieden, da sie unterschiedlich definiert sind.
Extensional betrachtet, sind die beiden Mengen jedoch gleich,
da sie genau die gleichen äußeren Eigenschaften haben,
d.h. da sie genau die gleichen Elemente enthalten.\<close>

subsection \<open>Über Isabelle/HOL\<close>
text\<open>Isabelle/HOL ist ein interaktiver Beweisassistent und kann
von \<^url>\<open>https://isabelle.in.tum.de/\<close> bezogen werden.

Isabelle stammt aus der Tradition der LCF (Logic for Computable Functions) Theorembeweiser.
Die Standardlogik ist Higher-Order Logic (HOL), welche auf der klassischen Mathematik basiert.

Isabelle basiert auf einem mathematischen Microkernel.
Zum aktuellen Zeitpunkt mit Isabelle2022 befindet sich das Herzstück dieses mathematischen
Microkernels in der Datei \<^file>\<open>~~/src/Pure/thm.ML\<close>, welche aus nur ca 2500 Zeilen ML Code besteht.
Dies ist relativ wenig Code welchem wir vertrauen müssen.
Die Korrektheit aller Ergebnisse und Beweise dieser Theory hängen nur von der Korrektheit dieses
Microkernels ab.

Isabelle/HOL ist ein interaktiver Beweisassistent, was bedeutet,
Isabelle hilft einem Benutzer dabei Beweise zu schreiben.
Alle Beweise müssen von Isabelles Microkernel akzeptiert werden, welcher die Korrektheit garantiert.
Im Gegensatz zu interaktiven Beweisassistenten gibt es auch automatische Theorembeweiser,
wie z.B. Z3.
Z3 besteht aus mehreren hunderttausend Zeilen C Code (\<^url>\<open>https://github.com/Z3Prover/z3\<close>)
und ist damit im Vergleich zu Isabelles Microkernel riesig.
Dies bedeutet auch, dass einer riesige Menge an Code vertraut werden muss,
um einem Beweis von Z3 zu vertrauen.
Glücklicherweise arbeiten Isabelle und z.B. Z3 sehr gut zusammen:
Z3 kann losgeschickt werden um einen Beweis zu suchen.
Sobald Z3 meldet, dass ein Beweis gefunden wurde,
akzeptiert Isabelle diesen jedoch nicht blind,
sondern Isabelle akzeptiert den gefundenen Beweis nur,
wenn der Beweis sich gegen Isabelles Microkernel wiedergeben lässt.
Somit kombiniert Isabelle das Beste aus vielen Welten:
Die starke Korrektheitsgarantie eines mathematischen Microkernels der LCF Reihe
mit der Automatisierung der neuesten Generationen von automatischen Theorembeweisern.

Der Unterschied zwischen z.B. Z3 und Isabelle/HOL zeigt sich auch in einigen Beispielen:
Während der Z3 Bugtracker sehr viele Soundness Issues zeigt,
d.h. Fälle in denen Z3 etwas falsches beweisen hat,
hat es meines Wissens nach im Isabelle/HOL Kernel in über 30 Jahren keinen logischen Fehler gegeben,
welcher normale Benutzer betroffen hat.
Natürlich gab es auch in Isabelle/HOL Bugs und in künstlich geschaffenen Grenzfällen
konnte Isabelle überzeugt werden einen falschen Fakt zu akzeptieren,
jedoch handelt es sich hier um wenige Einzelfälle welche speziell konstruiert wurden
um Isabelle anzugreifen -- kein einziger Bug hat unter normalen Umständen zu logischer
Inkonsistenz geführt.
Umgekehrt ist Z3 schnell und automatisch.
Während Isabelle vom Benutzer verlangt, dass Beweise manuell gefunden und formalisiert
werden müssen kann Z3 teils extrem komplizierte Probleme schnell und automatisch lösen.

Isabelle integriert nicht nur mit automatischen Beweisern wie Z3,
Isabelle integriert auch mit automatischen Gegenbeispielsfindern,
wie z.B. @{command quickcheck} oder @{command nitpick}.
Dies bedeutet, sobald der Benutzer einen vermeintlichen Fakt in Isabelle eintippt,
schickt Isabelle Prozesse los um ein Gegenbeispiel zu finden.
Diese so gefundenen Gegenbeispiele sind oft unintuitiv.
Allerdings sind es echte Gegenbeispiele und der Computer erweist sich als
grausamer unnachgiebiger Diskussionspartner.
Dies führt dazu, dass wir nicht mit halbgaren oberflächlichen Argumenten durchkommen.
Oft eröffnen diese automatischen Gegenbeispiele auch eine neue Sicht auf die Dinge
und helfen, die eigenen impliziten Annahmen zu erkennen und zu hinterfragen.
Der Computer erweist sich hier als perfekter logischer geduldiger Diskussionspartner,
denn
"der wahre Philosoph ist gewillt, alle vorgefaßten Meinungen einer Prüfung zu unterziehen"
\cite{russellphi}.
Und da alle Fakten welche wir ultimativ als wahr behaupten wollen durch den mathematischen
Microkernel müssen, sind logische Flüchtigkeitsfehler in unserer Argumentation ausgeschlossen.
Allerdgings können wir immer noch falsche Annahmen aufstellen,
auf welche wir unsere Ergebnisse stützen.
Jedoch müssen wir diese Annahmen explizit treffen und aufschreiben,
denn sonst ließe sich nichts beweisen.
\<close>

end
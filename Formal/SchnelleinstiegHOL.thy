theory SchnelleinstiegHOL
  imports Main BeispielTac
begin

section\<open>Schnelleinstieg Isabelle/HOL\<close>

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


subsection\<open>Typen\<close>
text\<open>Typen werden per \<^verbatim>\<open>::\<close> annotiert.
Beispielsweise sagt \<^theory_text>\<open>3::nat\<close>, dass \<^term>\<open>3::nat\<close> eine natürliche Zahl (Typ \<^typ>\<open>nat\<close>) ist.\<close>

text\<open>Einige vordefinierte Typen in Isabelle/HOL:

  \<^item> Natürliche Zahlen. Typ \<^typ>\<open>nat\<close>.
    Beispielsweise  \<^term_type>\<open>0 :: nat\<close>, \<^term_type>\<open>1 :: nat\<close>,
    \<^term_type>\<open>2 :: nat\<close>, \<^term_type>\<open>3 :: nat\<close>.
    Auf natürlichen Zahlen ist die Nachfolgerfunktion \<^const>\<open>Suc\<close> definiert.
    Beispielsweise ist @{lemma \<open>Suc 2 = 3\<close> by simp}.
  \<^item> Ganze Zahlen. Typ \<^typ>\<open>int\<close>.
    Beispielsweise  \<^term_type>\<open>0 :: int\<close>, \<^term_type>\<open>1 :: int\<close>,
    \<^term_type>\<open>-1 :: int\<close>, \<^term_type>\<open>-42 :: int\<close>.
  \<^item> Listen. Typ \<^typ>\<open>'\<alpha> list\<close>.
    Beispielsweise  \<^term_type>\<open>[] :: nat list\<close>, \<^term_type>\<open>[] :: int list\<close>,
    \<^term_type>\<open>[0, 1, 2, 3] :: nat list\<close>, \<^term_type>\<open>[0, 1, -1, -42] :: int list\<close>.
  \<^item> Strings. Typ \<^typ>\<open>string\<close>.
    Beispielsweise  \<^term_type>\<open>''Hello, World'' :: string\<close>.
\<close>


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

subsection\<open>Noch mehr Typen\<close>
text\<open>Eigene Typen können unter Anderem mit dem Keyword @{command datatype} eingeführt werden.
Im folgenden Beispiel führen wir einen @{command datatype} für Farben ein.\<close>

datatype beispiel_farbe = Rot | Gruen | Blau

text\<open>Eine variable \<^term_type>\<open>x :: beispiel_farbe\<close> kann entweder den Wert
\<^const>\<open>Rot\<close>, \<^const>\<open>Gruen\<close>, oder \<^const>\<open>Blau\<close> haben.
Dies lässt sich auch beweisen:\<close>

beispiel\<open>x = Rot \<or> x = Gruen \<or> x = Blau\<close>
  by(cases \<open>x\<close>, auto)

text\<open>Wir können auch einen Schritt weitergehen und eine Liste von \<^typ>\<open>beispiel_farbe\<close>
selbst implementieren.\<close>

datatype beispiel_farbe_liste = FLLeer | FLKopf \<open>beispiel_farbe\<close> \<open>beispiel_farbe_liste\<close>

text\<open>Eine \<^typ>\<open>beispiel_farbe_liste\<close> ist hier rekursiv definiert:

  \<^item> Entweder ist die Liste \<^const>\<open>FLLeer\<close> und enthält keine Elemente.
  \<^item> Oder es gibt bereits eine \<^typ>\<open>beispiel_farbe_liste\<close> und über den \<^const>\<open>FLKopf\<close>
    Konstruktor hängen wir eine weitere \<^typ>\<open>beispiel_farbe\<close> an.
    Die Abkürzung \<^const>\<open>FLKopf\<close> steht hier für Farben-Listen-Kopf.

Beispielsweise können wir immer länger werdende
\<^typ>\<open>beispiel_farbe_liste\<close>n welche nur \<^const>\<open>Rot\<close>e Elemente enthalten wie folgt konstruieren:

  \<^item> \<^term>\<open>(FLLeer) :: beispiel_farbe_liste\<close> enthält 0 Elemente.
  \<^item> \<^term>\<open>(FLKopf Rot FLLeer) :: beispiel_farbe_liste\<close> enthält ein \<^const>\<open>Rot\<close> Element.
  \<^item> \<^term>\<open>(FLKopf Rot (FLKopf Rot FLLeer)) :: beispiel_farbe_liste\<close>
     enthält zwei \<^const>\<open>Rot\<close> Elemente.
  \<^item> \<^term>\<open>(FLKopf Rot (FLKopf Rot (FLKopf Rot FLLeer))) :: beispiel_farbe_liste\<close>
     enthält drei \<^const>\<open>Rot\<close> Elemente.
\<close>

text\<open>Das Konzept Liste kann weiter verallgemeinert werden.
Wir können eine generische Liste bauen, welche nicht nur \<^typ>\<open>beispiel_farbe\<close>n aufnehmen kann,
sondern eine polymorphe Liste,
welche beliebige Typen speichern kann.
\<close>

datatype '\<alpha> beispiel_liste = Leer | Kopf \<open>'\<alpha>\<close> \<open>'\<alpha> beispiel_liste\<close>

text\<open>Der Typ \<^typ>\<open>'\<alpha>\<close> steht hierbei für einen Platzhalter für beliebige Typen.
Beispielsweise können wir mit der generischen \<^typ>\<open>'\<alpha> beispiel_liste\<close> wieder unsere
\<^typ>\<open>beispiel_farbe_liste\<close> simulieren:

  \<^item> \<^term_type>\<open>(Leer) :: beispiel_farbe beispiel_liste\<close> enthält 0 Elemente.
  \<^item> \<^term_type>\<open>(Kopf Rot Leer) :: beispiel_farbe beispiel_liste\<close>
    enthält ein \<^const>\<open>Rot\<close> Element.
  \<^item> \<^term_type>\<open>(Kopf Rot (Kopf Rot Leer)) :: beispiel_farbe beispiel_liste\<close>
     enthält zwei \<^const>\<open>Rot\<close> Elemente.
  \<^item> \<^term_type>\<open>(Kopf Rot (Kopf Rot (Kopf Rot Leer))) :: beispiel_farbe beispiel_liste\<close>
     enthält drei \<^const>\<open>Rot\<close> Elemente.

Die Liste kann jedoch auch andere Typen von Elementen speichern.

  \<^item> \<^term_type>\<open>(Kopf 2 (Kopf 1 (Kopf 0 Leer))) :: nat beispiel_liste\<close>
  \<^item> \<^term_type>\<open>(Kopf ''Erstes Element'' (Kopf ''Letzes Element'' Leer)) :: string beispiel_liste\<close>
\<close>

text\<open>Die Länge einer \<^typ>\<open>'\<alpha> beispiel_liste\<close> lässt sich über folgende rekursive Funktion
wie folgt definieren:\<close>

fun beispiel_liste_laenge :: \<open>'\<alpha> beispiel_liste \<Rightarrow> nat\<close> where
  \<open>beispiel_liste_laenge Leer = 0\<close>
| \<open>beispiel_liste_laenge (Kopf _ ls) = Suc (beispiel_liste_laenge ls)\<close>

text\<open>Funktionen werden oft über Pattern-Matching implementiert,
d.h., dass der gegebene Datentyp zerlegt wird und eine Fallunterscheidung getroffen wird.

  \<^item> Für den Basisfall \<^const>\<open>Leer\<close> wird \<^term>\<open>0::nat\<close> zurückgegeben.
  \<^item> Für den rekursiven Fall \<^term>\<open>Kopf\<close> in dem wir ein Kopfelement haben
    welches wir ignorieren und einer Folgeliste \<^term>\<open>ls::'\<alpha> beispiel_liste\<close>
    rufen wir \<^const>\<open>beispiel_liste_laenge\<close> rekursiv mit der Folgeliste auf und geben den
    Nachfolger der so berechneten Zahl zurück.\<close>

beispiel \<open>beispiel_liste_laenge Leer = 0\<close>
  by eval
beispiel \<open>beispiel_liste_laenge (Kopf Rot (Kopf Rot (Kopf Rot Leer))) = 3\<close>
  by eval

text\<open>Zusätzlich können den einzelnen Feldern in Datentypen spezielle Namen gegeben werden.
Beispielsweise:\<close>

datatype '\<alpha> beispiel_liste_mit_namen =
    LeerMN | KopfMN (kopfelement: \<open>'\<alpha>\<close>) (schwanzliste: \<open>'\<alpha> beispiel_liste_mit_namen\<close>)

text\<open>Der Fall \<^const>\<open>LeerMN\<close> bleibt unverändert.
Um Verwechslung zu vermeiden haben wir den einzelnen Fällen das Suffix MN (Mit-Namen)
gegeben, da die Konstruktoren \<^const>\<open>Leer\<close> und \<^const>\<open>Kopf\<close> bereits durch das vorherige Beispiel
definiert sind.
Im \<^const>\<open>KopfMN\<close>-Fall haben nun die einzelnen Felder Namen.\<close>

beispiel\<open>kopfelement (KopfMN Rot LeerMN) = Rot\<close> by simp
beispiel\<open>schwanzliste (KopfMN Rot LeerMN) = LeerMN\<close> by simp

text\<open>Die von Isabelle mitgelieferte Standardimplementierung einer Liste
sieht unserem Beispiel recht ähnlich,
allerdings liefert Isabelle noch zusätzlichen Syntactic Sugar um Listen komfortabler darzustellen.
Die Implementierung einer Liste in der Standardbibliothek ist: \<^datatype>\<open>list\<close>\<close>


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

text\<open>Im vorhergehenden Beispiel wurden zwei Funktionen
(die \<^const>\<open>beispielfunktion\<close> die wir oben definiert haben und ein lambda-Ausdruck)
als equivalent bewiesen.
Dafür wurde die Extensionalität verwendet.\<close>

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

subsection\<open>First-Order Logic\<close>
text\<open>First-Order Logic, oder auch Prädikatenlogik erster Stufe, besteht aus folgenden Symbolen.

  \<^item> Konjunktion. Der Term \<^term>\<open>A \<and> B\<close> besagt, dass sowohl \<^term>\<open>A\<close> als auch \<^term>\<open>B\<close> wahr sind.
    Dies entspricht dem logischen "Und".
  \<^item> Disjunktion. Der Term \<^term>\<open>A \<or> B\<close> besagt, dass \<^term>\<open>A\<close> oder \<^term>\<open>B\<close> (oder beide) wahr sind.
    Dies entspricht dem logischen "Oder".
  \<^item> Negation. Der Term \<^term>\<open>\<not> A\<close> besagt, dass \<^term>\<open>A\<close> nicht wahr ist.
    Dies entspricht dem logischen "Nicht".
  \<^item> Implikation. Der Term \<^term>\<open>A \<longrightarrow> B\<close> besagt, dass wenn \<^term>\<open>A\<close> gilt dann gilt auch \<^term>\<open>B\<close>.
    Dies entspricht dem logischen "Wenn-Dann".
    Unsere Mathematik ist hardcore klassisch und es gilt
    @{lemma [break=true] \<open>A \<longrightarrow> B \<longleftrightarrow> \<not>A \<or> B\<close> by blast}.
  \<^item> All-Quantifier. Der Term \<^term>\<open>\<forall>x. P x\<close> besagt, dass \<^term>\<open>P x\<close> wahr ist für alle \<^term>\<open>x\<close>.
    Dies entspricht dem logischen "Für-Alle".
  \<^item> Existenz-Quantifier. Der Term \<^term>\<open>\<exists>x. P x\<close> besagt, dass es ein \<^term>\<open>x\<close> gibt,
    für das \<^term>\<open>P x\<close> gilt.
    Dies entspricht dem logischen "Es-Existiert".
  \<^item> Des Weiteren gibt es noch die Abkürzung @{term [source=true] \<open>A \<longleftrightarrow> B\<close>}, welche bedeutet,
    dass \<^term>\<open>A\<close> genau dann gilt wenn \<^term>\<open>B\<close> gilt.
    Dies entspricht dem logischen "Genau-Dann-Wenn".
    Genau genommen ist @{term [source=true] \<open>A \<longleftrightarrow> B\<close>} eine Abkürzung für \<^term>\<open>A = B\<close>.
    Oft ist @{term [source=true] \<open>A \<longleftrightarrow> B\<close>} praktischer zu schreiben, da es schwächer bindet.
    Genau genommen gilt @{lemma [source=true] \<open>(A \<longleftrightarrow> B) = ((A) = (B))\<close> by blast}.
    Die schwache Bindung von @{term [source=true] \<open>A \<longleftrightarrow> B\<close>} wird dann relevant,
    wenn \<^term>\<open>A\<close> und \<^term>\<open>B\<close> komplizierte Ausdrücke sind,
    da wir uns im Gegensatz zu @{term [source=true] \<open>(A) = (B)\<close>} Klammern sparen können.
\<close>

subsection\<open>Higher-Order Logic (HOL)\<close>
text\<open>First-Order Logic ist in Higher-Order Logic eingebettet.
Higher-Order Logic (HOL) ist die native Sprache von Isabelle/HOL.
Im Vergleich zur First-Order Logic besteht HOL nur aus zwei essentiellen Symbolen:

  \<^item> All-Quantifier. Der Term \<^term>\<open>\<And>x. P x\<close> besagt \<^term>\<open>\<forall>x. P x\<close>.
    Eigentlich ist zwischen dem First-Order und dem Higher-Order All-Quantifier kein
    wesentlicher Unterschied.
    Genau genommen lässt sich der First-Order All-Quantifier via HOL einführen wie folgt:
    @{thm allI}.
    
    Da mathematisch der Ausdruck \<^term>\<open>P x\<close> besagt, dass \<^term>\<open>P\<close> für
    beliebiges \<^term>\<open>x\<close>---sprich: alle \<^term>\<open>x\<close>---
    gilt, ist folgendes equivalent:
      \<^item> \<^term>\<open>\<And>x. P x\<close>
      \<^item> \<^term>\<open>\<forall>x. P x\<close>
      \<^item> \<^term>\<open>P x\<close>
  \<^item> Implikation. Der Term \<^term>\<open>A \<Longrightarrow> B\<close> besagt \<^term>\<open>A \<longrightarrow> B\<close>.
    Eigentlich ist zwischen der First-Order und der Higher-Order Implikation kein
    wesentlicher Unterschied.

    Die Implikation assoziiert nach rechts.
    Dies bedeutet @{lemma [source=true] \<open>A \<longrightarrow> B \<longrightarrow> C \<longleftrightarrow> (A \<longrightarrow> (B \<longrightarrow> C))\<close> by blast}.

    Logisch gilt damit auch folgendes:
    @{lemma [source=true] \<open>A \<longrightarrow> B \<longrightarrow> C \<longleftrightarrow> A \<and> B \<longrightarrow> C\<close> by blast}.

    In Isabelle/HOL werden wir viele Lemmata der Form @{term [source=true] \<open>A \<Longrightarrow> B \<Longrightarrow> C\<close>} sehen,
    welche zu lesen sind als: Aus \<^term>\<open>A\<close> und \<^term>\<open>B\<close> folgt \<^term>\<open>C\<close>.
    Dies ist gleichbedeutend mit \<^term>\<open>A \<and> B \<Longrightarrow> C\<close>.
    Da die Higher-Order Implikation einer der Kernbausteine von HOL sind ist die Formulierung
    welche nur die Implikation verwendet sehr praktisch für Isabelle.
\<close>

subsection\<open>Über Isabelle/HOL\<close>
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
@{cite russellphi}.
Und da alle Fakten welche wir ultimativ als wahr behaupten wollen durch den mathematischen
Microkernel müssen, sind logische Flüchtigkeitsfehler in unserer Argumentation ausgeschlossen.
Allerdings können wir immer noch falsche Annahmen aufstellen,
auf welche wir unsere Ergebnisse stützen.
Jedoch müssen wir diese Annahmen explizit treffen und aufschreiben,
denn sonst ließe sich nichts beweisen.
\<close>

subsection\<open>Ist das KI?\<close>
text\<open>TODO: nein!

KI oft synonym machine learning.
Axiome.

Isabelle/HOL

\<close>
(*find ./Downloads/Isabelle2022/src/HOL -name "*.thy"  | xargs grep axiomatiz | wc -l*)

subsection\<open>Shallow Embedding vs. Deep Embedding\<close>
text\<open>TODO\<close>

end
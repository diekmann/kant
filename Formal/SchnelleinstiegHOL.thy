theory SchnelleinstiegHOL
imports Main
begin

section\<open>Schnelleinstieg Isabelle/HOL\<close>

subsection\<open>Typen\<close>
text\<open>Typen werden per \<^verbatim>\<open>::\<close> annotiert.
Beispielsweise sagt \<^theory_text>\<open>3::nat\<close>, dass \<^term>\<open>3::nat\<close> eine natürliche Zahl (\<^typ>\<open>nat\<close>) ist.\<close>

subsection\<open>Beweise\<close>
text\<open>Die besondere Fähigkeit im Beweisassistent Isabelle/HOL liegt darin,
maschinengeprüfte Beweise zu machen.

Beispiel:\<close>

lemma\<open>3 = 2+1\<close> by simp

text\<open>In der PDFversion wird der eigentliche Beweis ausgelassen.
Aber keine Sorge, der Computer hat den Beweis überprüft.
Würde der Beweis nicht gelten, würde das PDF garnicht compilieren.

Ich wurde schon für meine furchtbaren Beweise zitiert.
Ist also ganz gut, dass wir nur Ergebnisse im PDF sehen und der eigentliche Beweis ausgelassen ist.
Am besten kann man Beweise sowieso im Isabelle Editor anschauen und nicht im PDF.
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

subsection\<open>Funktionen\<close>
text\<open>Beispiel:
Eine Funktionen welche eine natürliche Zahl nimmt und
eine natürliche Zahl zurück gibt (\<^typ>\<open>nat \<Rightarrow> nat\<close>):\<close>

fun beispielfunktion :: \<open>nat \<Rightarrow> nat\<close> where
  \<open>beispielfunktion n = n + 10\<close>


text\<open>Funktionsaufrufe funktionieren ohne Klammern.\<close>

lemma \<open>beispielfunktion 32 = 42\<close> by eval

text\<open>Funktionen sind gecurried. Hier ist eine Funktion welche 2 natürliche Zahlen nimmt
und eine natürliche Zahl zurück gibt (\<^typ>\<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close>):\<close>
fun addieren :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>addieren a b = a + b\<close>


lemma \<open>addieren 32 10 = 42\<close> by eval

text\<open>Currying bedeutet auch, wenn wir \<^const>\<open>addieren\<close> nur mit einem Argument aufrufen
(welches eine natürliche Zahl \<^typ>\<open>nat\<close> sein muss),
dass wir eine Funktion zurückbekommen, die noch das zweite Argument erwartet,
bevor sie das Ergebnis zurückgeben kann.

Beispiel: \<^term_type>\<open>(addieren 10) :: (nat \<Rightarrow> nat)\<close>

Zufälligerweise ist \<^term>\<open>addieren 10\<close> equivalent zu \<^term>\<open>beispielfunktion\<close>:
\<close>
lemma \<open>addieren 10 = beispielfunktion\<close>
  by(simp add: fun_eq_iff)


text\<open>Zusätzlich lassen sich Funktionen im Lambda Calculus darstellen.
Beispiel:\<close>

lemma \<open>(\<lambda>n::nat. n+10) 3 = 13\<close> by eval

lemma \<open>beispielfunktion = (\<lambda>n. n+10)\<close>
  by(simp add: fun_eq_iff)

subsection\<open>Mengen\<close>
text\<open>Mengen funktionieren wie normale mathematische Mengen.

Beispiel. Die Menge der geraden Zahlen:
\<close>
lemma \<open>{0,2,4,6,8,10,12} \<subseteq> {n::int. n mod 2 = 0}\<close>
  by(simp)


end
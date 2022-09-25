theory Handlung
imports Main
begin

section\<open>Handlung\<close>

text\<open>
Beschreibt Handlungen als Änderung der Welt. Unabhängig von der handelnden Person.
Wir beschreiben nur vergangene bzw. mögliche Handlungen und deren Auswirkung.

Eine Handlung ist reduziert auf deren Auswirkung.
Intention oder Wollen ist nicht modelliert,
da wir irgendwie die geistige Welt mit der physischen Welt verbinden müssen und wir daher nur
messbare Tatsachen betrachten können.

Handlungen können Leute betreffen.
Handlungen können aus Sicht Anderer wahrgenommen werden.
Ich brauche nur Welt vorher und Welt nachher.
So kann ich handelnde Person und beobachtende Person trennen.
\<close>
datatype 'world handlung = Handlung (vorher: \<open>'world\<close>) (nachher: \<open>'world\<close>)

(*<*)
text\<open>The datatype-generated functions are really cool:\<close>
lemma \<open>map_handlung Suc (Handlung 1 2) = Handlung 2 3\<close> by eval
(*>*)

text \<open>
Handlung als Funktion gewrapped.
Diese abstrakte Art eine Handlung zu modelliert so ein bisschen die Absicht oder Intention.
\<close>
datatype ('person, 'world) handlungF = HandlungF \<open>'person \<Rightarrow> 'world \<Rightarrow> 'world\<close>

text \<open>
Von Außen können wir Funktionen nur extensional betrachten, d.h. Eingabe und Ausgabe anschauen.
Die Absicht die sich in einer Funktion verstecken kann ist schwer zu erkennen.
Dies deckt sich ganz gut damit, dass Isabelle standardmäßig Funktionen nicht printet.
Eine \<^typ>\<open>('person, 'world) handlungF\<close> kann nicht geprinted werden!
\<close>


fun handeln :: \<open>'person \<Rightarrow> 'world \<Rightarrow> ('person, 'world) handlungF \<Rightarrow> 'world handlung\<close> where
\<open>handeln handelnde_person welt (HandlungF h) = Handlung welt (h handelnde_person welt)\<close>

text\<open>
Beispiel, für eine Welt die nur aus einer Zahl bestehtÖ
Wenn die Zahl kleiner als 9000 ist erhöhe ich sie, ansonsten bleibt sie unverändert.
\<close>
definition \<open>beispiel_handlungf \<equiv> HandlungF (\<lambda>p n. if n < 9000 then n+1 else n)\<close>

text\<open>Da Funktionen nicht geprintet werden können, sieht \<^const>\<open>beispiel_handlungf\<close> so aus:
@{value \<open>beispiel_handlungf::(nat, int) handlungF\<close>}\<close>



subsection\<open>Interpretation: Gesinnungsethik vs. Verantwortungethik\<close>
text\<open>
Sei eine Ethik eine Funktion, welche einem beliebigen \<^typ>\<open>'\<alpha>\<close> eine
Bewertung Gut = \<^const>\<open>True\<close>, Schlecht = \<^const>\<open>False\<close> zuordent.

  \<^item> Eine Ethik hat demnach den Typ: \<^typ>\<open>'\<alpha> \<Rightarrow> bool\<close>.

\<^medskip>

Laut \<^url>\<open>https://de.wikipedia.org/wiki/Gesinnungsethik\<close> ist eine Gesinnugsethik
"[..] eine der moralischen Theorien,
 die Handlungen nach der Handlungsabsicht [...]  bewertet,
 und zwar ungeachtet der nach erfolgter Handlung eingetretenen Handlungsfolgen."

  \<^item> Demnach ist eine Gesinnungsethik: \<^typ>\<open>('person, 'world) handlungF \<Rightarrow> bool\<close>.

\<^smallskip>

Nach \<^url>\<open>https://de.wikipedia.org/wiki/Verantwortungsethik\<close> steht die Verantwortungsethik
dazu im strikten Gegensatz, da die Verantwortungsethik
"in der Bewertung des Handelns die Verantwortbarkeit der \<^emph>\<open>tatsächlichen Ergebnisse\<close> betont."

  \<^item> Demnach ist eine Verantwortungsethik: \<^typ>\<open>'world handlung \<Rightarrow> bool\<close>.


\<^medskip>

Da \<^const>\<open>handeln\<close> eine Handlungsabsicht \<^typ>\<open>('person, 'world) handlungF\<close>
in eine konkrete Änderung der Welt \<^typ>\<open>'world handlung\<close> überführt,
können wie die beiden Ethiktypen miteinander in Verbindungs setzen.
Wir sagen, eine Gesinnungsethik und eine Verantwortungsethik sind konsistent,
genau dann wenn für jede Handlungsabsicht, die
Gesinnungsethik die Handlungsabsicht genau so bewertet,
wie die Verantwortungsethik die Handlungsabsicht bewerten würde,
wenn die die Handlungsabsicht in jeder möglichen Welt und
als jede mögliche handelnde Person tatsächlich ausführt wird und die Folgen betrachtet werden:
\<close>

definition gesinnungsethik_verantwortungsethik_konsistent
  :: "(('person, 'world) handlungF \<Rightarrow> bool) \<Rightarrow> ('world handlung \<Rightarrow> bool) \<Rightarrow> bool" where
"gesinnungsethik_verantwortungsethik_konsistent gesinnungsethik verantwortungsethik \<equiv>
  \<forall>handlungsabsicht.
    gesinnungsethik handlungsabsicht \<longleftrightarrow>
      (\<forall>person welt. verantwortungsethik (handeln person welt handlungsabsicht))"


text\<open>Ich habe kein Beispiel für eine Gesinnungsethik
und eine Verantwortungsethik,
die tatsächlich konsistent sind.\<close>

end
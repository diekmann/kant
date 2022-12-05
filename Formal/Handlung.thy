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


text\<open>Folgende Funktion beschreibt ob eine Handlung eine No-Op ist,
also eine Handlung welche die Welt nicht verändert.\<close>
definition ist_noop :: \<open>'world handlung \<Rightarrow> bool\<close> where
  \<open>ist_noop h \<equiv> vorher h = nachher h\<close>

(*<*)

lemma ist_noop_map_handlung:
  shows \<open>ist_noop h \<Longrightarrow> ist_noop (map_handlung f h)\<close>
  by(cases \<open>h\<close>, rename_tac vor nach, simp add: ist_noop_def)


(*>*)


text \<open>
Handlung als Funktion gewrapped.
Diese abstrakte Art eine Handlung zu modelliert so ein bisschen die Absicht oder Intention.
\<close>
datatype ('person, 'world) handlungsabsicht = Handlungsabsicht \<open>'person \<Rightarrow> 'world \<Rightarrow> 'world option\<close>


text\<open>Eine \<^typ>\<open>('person, 'world) handlungsabsicht\<close> gibt eine \<^typ>\<open>'world option\<close> zurück,
anstatt einer \<^typ>\<open>'world\<close>.
Handlungsabsichten sind damit partielle Funktionen, was modelliert,
dass die Ausführung einer Handlungsabsicht scheitern kann.
Beispielsweise könnte ein Dieb versuchen ein Opfer zu bestehlen;
wenn sich allerdings kein passendes Opfer findet, dann darf die Handlung scheitern.
Oder es könnte der pathologische Sonderfall eintreten, dass ein Dieb sich selbst
bestehlen soll.
Auch hier darf die Handlung scheitern.
Von außen betrachtet ist eine solche gescheiterte Handlung nicht zu unterscheiden vom Nichtstun.
Allerdings ist es für die moralische Betrachtung dennoch wichtig zu unterscheiden,
ob die Handlungsabsicht ein gescheiterter Diebstahl war,
oder ob die Handlungsabsicht einfach Nichtstun war.
Dadurch dass Handlungsabsichten partiell sind, können wir unterscheiden ob die Handlung
wie geplant ausgeführt wurde oder gescheitert ist.
Moralisch sind Stehlen und Nichtstun sehr verschieden.\<close>

fun nachher_handeln
  :: \<open>'person \<Rightarrow> 'world \<Rightarrow> ('person, 'world) handlungsabsicht \<Rightarrow> 'world\<close>
where
  \<open>nachher_handeln handelnde_person welt (Handlungsabsicht h) = 
    (case h handelnde_person welt of Some welt' \<Rightarrow> welt'
                                  | None \<Rightarrow> welt)\<close>

text\<open>Die Funktion \<^const>\<open>nachher_handeln\<close> besagt, dass eine gescheiterte Handlung
die Welt nicht verändert.
Ab diesem Punkt sind also die Handlungen "sich selbst bestehlen" und "Nichtstun"
von außen ununterscheidbar, da beide die Welt nicht verändern.\<close>

definition handeln
  :: \<open>'person \<Rightarrow> 'world \<Rightarrow> ('person, 'world) handlungsabsicht \<Rightarrow> 'world handlung\<close>
where
  \<open>handeln handelnde_person welt ha \<equiv> Handlung welt (nachher_handeln handelnde_person welt ha)\<close>


text\<open>Die Funktion \<^const>\<open>nachher_handeln\<close> liefert die Welt nach der Handlung.
Die Funktion \<^const>\<open>handeln\<close> liefert eine \<^typ>\<open>'world handlung\<close>,
welche die Welt vor und nach der Handlung darstellt.\<close>


text\<open>
Beispiel, für eine Welt die nur aus einer Zahl besteht:
Wenn die Zahl kleiner als 9000 ist erhöhe ich sie, ansonsten schlägt die Handlung fehl.
\<close>
definition \<open>beispiel_handlungsabsicht \<equiv> Handlungsabsicht (\<lambda>_ n. if n < 9000 then Some (n+1) else None)\<close>

lemma \<open>nachher_handeln ''Peter'' (42::nat) beispiel_handlungsabsicht = 43\<close> by eval
lemma \<open>handeln ''Peter'' (42::nat) beispiel_handlungsabsicht = Handlung 42 43\<close> by eval
lemma \<open>nachher_handeln ''Peter'' (9000::nat) beispiel_handlungsabsicht = 9000\<close> by eval
lemma \<open>ist_noop (handeln ''Peter'' (9000::nat) beispiel_handlungsabsicht)\<close> by eval

text \<open>
Von Außen können wir Funktionen nur extensional betrachten, d.h. Eingabe und Ausgabe anschauen.
Die Absicht die sich in einer Funktion verstecken kann ist schwer zu erkennen.
Dies deckt sich ganz gut damit, dass Isabelle standardmäßig Funktionen nicht printet.
Eine \<^typ>\<open>('person, 'world) handlungsabsicht\<close> kann nicht geprinted werden!
\<close>

text\<open>Da Funktionen nicht geprintet werden können, sieht \<^const>\<open>beispiel_handlungsabsicht\<close> so aus:
\<^value>\<open>beispiel_handlungsabsicht::(nat, int) handlungsabsicht\<close>\<close>


(*<*)
lemma vorher_handeln[simp]: \<open>vorher (handeln p welt h) = welt\<close>
  by(cases \<open>h\<close>, simp add: handeln_def)
lemma nachher_handeln_raw: \<open>nachher (handeln p welt (Handlungsabsicht h)) = 
  (case h p welt of None \<Rightarrow> welt
                  | Some w \<Rightarrow> w)\<close>
  by(simp add: handeln_def)

(*I don't want to expand this definition by default, but keep the handeln function around.
Otherwise, case distinctions for the option type pop up in all proof obligations.*)
declare nachher_handeln.simps[simp del]
(*>*)


text\<open>Um eine gescheiterte Handlung von einer Handlung welche die Welt nicht verändert
zu unterscheiden, sagen wir, dass eine Handlungsabsicht ausführbar ist,
wenn die ausgeführte Handlungsabsicht nicht gescheitert ist:\<close>

fun ausfuehrbar :: \<open>'person \<Rightarrow> 'world \<Rightarrow> ('person, 'world) handlungsabsicht \<Rightarrow> bool\<close>
where
  \<open>ausfuehrbar p welt (Handlungsabsicht h) = (h p welt \<noteq> None)\<close>

(*<*)
declare ausfuehrbar.simps[simp del]
(*>*)

text\<open>Nicht ausführbare Handlungen resultieren in unserem Modell im Nichtstun:\<close>
lemma nicht_ausfuehrbar_ist_noop:
  \<open>\<not>ausfuehrbar p welt ha \<Longrightarrow> ist_noop (handeln p welt ha)\<close>
  apply(cases \<open>ha\<close>)
  by(simp add: ausfuehrbar.simps ist_noop_def handeln_def nachher_handeln.simps)

(*<*)
lemma ausfuehrbar_nachher_handeln:
  \<open>ausfuehrbar p welt (Handlungsabsicht h) \<Longrightarrow>
  nachher_handeln p welt (Handlungsabsicht h) = the (h p welt)\<close>
  apply(simp add: ausfuehrbar.simps nachher_handeln.simps split:option.split)
  by fastforce
(*>*)


subsection\<open>Interpretation: Gesinnungsethik vs. Verantwortungethik \label{sec:gesinnungsverantwortungsethik}\<close>
text\<open>
Sei eine Ethik eine Funktion, welche einem beliebigen \<^typ>\<open>'\<alpha>\<close> eine
Bewertung Gut = \<^const>\<open>True\<close>, Schlecht = \<^const>\<open>False\<close> zuordnet.

  \<^item> Eine Ethik hat demnach den Typ: \<^typ>\<open>'\<alpha> \<Rightarrow> bool\<close>.

\<^medskip>

Laut \<^url>\<open>https://de.wikipedia.org/wiki/Gesinnungsethik\<close> ist eine Gesinnungsethik
"[..] eine der moralischen Theorien,
 die Handlungen nach der Handlungsabsicht [...]  bewertet,
 und zwar ungeachtet der nach erfolgter Handlung eingetretenen Handlungsfolgen."

  \<^item> Demnach ist eine Gesinnungsethik: \<^typ>\<open>('person, 'world) handlungsabsicht \<Rightarrow> bool\<close>.

\<^smallskip>

Nach \<^url>\<open>https://de.wikipedia.org/wiki/Verantwortungsethik\<close> steht die Verantwortungsethik
dazu im strikten Gegensatz, da die Verantwortungsethik
"in der Bewertung des Handelns die Verantwortbarkeit der \<^emph>\<open>tatsächlichen Ergebnisse\<close> betont."

  \<^item> Demnach ist eine Verantwortungsethik: \<^typ>\<open>'world handlung \<Rightarrow> bool\<close>.


\<^medskip>

Da \<^const>\<open>handeln\<close> eine Handlungsabsicht \<^typ>\<open>('person, 'world) handlungsabsicht\<close>
in eine konkrete Änderung der Welt \<^typ>\<open>'world handlung\<close> überführt,
können wie die beiden Ethiktypen miteinander in Verbindung setzen.
Wir sagen, eine Gesinnungsethik und eine Verantwortungsethik sind konsistent,
genau dann wenn für jede Handlungsabsicht, die
Gesinnungsethik die Handlungsabsicht genau so bewertet,
wie die Verantwortungsethik die Handlungsabsicht bewerten würde,
wenn die die Handlungsabsicht in jeder möglichen Welt und
als jede mögliche handelnde Person tatsächlich ausführt wird und die Folgen betrachtet werden:
\<close>

definition gesinnungsethik_verantwortungsethik_konsistent
  :: \<open>(('person, 'world) handlungsabsicht \<Rightarrow> bool) \<Rightarrow> ('world handlung \<Rightarrow> bool) \<Rightarrow> bool\<close> where
\<open>gesinnungsethik_verantwortungsethik_konsistent gesinnungsethik verantwortungsethik \<equiv>
  \<forall>handlungsabsicht.
    gesinnungsethik handlungsabsicht \<longleftrightarrow>
      (\<forall>person welt. verantwortungsethik (handeln person welt handlungsabsicht))\<close>


text\<open>Ich habe aktuell kein Beispiel für eine Gesinnungsethik
und eine Verantwortungsethik,
die tatsächlich konsistent sind.
Später (In \S\ref{sec:golregelutilkonsistent}) werden wir sehen, dass es eine Übersetzung gibt,
mit der die goldene Regel und der Utilitarismus konsistent sind.\<close>

end
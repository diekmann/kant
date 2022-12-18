theory Handlung
imports Main
begin

section\<open>Handlung\<close>
text\<open>In diesem Abschnitt werden wir Handlungen und Handlungsabsichten modellieren.\<close>

text\<open>Wir beschreiben Handlungen als ein Änderung der Welt.
Das Modell einer Handlung ist rein auf die extern beobachtbare Änderung der Welt beschränkt.
Die handelnden Person ist dabei Nebensache.
Wir beschreiben nur vergangene bzw. hypothetische Handlungen und deren Auswirkungen.
\<close>
datatype 'welt handlung = Handlung (vorher: \<open>'welt\<close>) (nachher: \<open>'welt\<close>)

text\<open>
Eine Handlung ist reduziert auf die beobachtbaren Auswirkungen der Handlung.
Die dahinterliegende Handlungsabsicht, bzw. Intention oder "Wollen" sind
in einer \<^typ>\<open>'welt handlung\<close> nicht modelliert.
Dies liegt daran,
dass wir irgendwie die geistige Welt mit der physischen Welt verbinden müssen und wir daher
am Anfang nur messbare Tatsachen betrachten können.
Diese initiale Entscheidung,
eine Handlung rein auf ihre beobachtbaren und messbaren Auswirkungen zu reduzieren,
ist essentiell für diese Theorie.

Handlungen können Leute betreffen.
Handlungen können aus Sicht Anderer wahrgenommen werden.
Unser Modell einer Handlung enthält jedoch nur die Welt vorher und Welt nachher.
So können wir handelnde Person und beobachtende Person trennen.\<close>

(*<*)
text\<open>The datatype-generated functions are really cool:\<close>
lemma \<open>map_handlung Suc (Handlung 1 2) = Handlung 2 3\<close> by eval
(*>*)


text\<open>Folgende Funktion beschreibt ob eine Handlung eine No-Op ist,
also eine Handlung welche die Welt nicht verändert.\<close>
definition ist_noop :: \<open>'welt handlung \<Rightarrow> bool\<close> where
  \<open>ist_noop h \<equiv> vorher h = nachher h\<close>

(*<*)

lemma ist_noop_map_handlung:
  shows \<open>ist_noop h \<Longrightarrow> ist_noop (map_handlung f h)\<close>
  by(cases \<open>h\<close>, rename_tac vor nach, simp add: ist_noop_def)


(*>*)


text \<open>
Folgende Definition ist eine Handlung als Funktion gewrapped.
Diese abstrakte Art eine Handlung darzustellen erlaubt es nun,
die Absicht oder Intention hinter einer Handlung zu modellieren.
\<close>
datatype ('person, 'welt) handlungsabsicht = Handlungsabsicht \<open>'person \<Rightarrow> 'welt \<Rightarrow> 'welt option\<close>

text\<open>Im Vergleich zu unserer \<^typ>\<open>'welt handlung\<close> sehen wir bereits am Typen,
dass eine \<^typ>\<open>('person, 'welt) handlungsabsicht\<close> nicht nur eine einfache Aussage über die
\<^typ>\<open>'welt\<close> trifft, sondern auch die Absicht der handelnden \<^typ>\<open>'person\<close> beinhaltet.

Die Idee ist, dass eine \<^typ>\<open>('person, 'welt) handlungsabsicht\<close> eine generische Handlungsabsicht
modelliert. Beispielsweise \<^term>\<open>Handlungsabsicht (\<lambda>ich welt. brezen_kaufen welt ich)\<close>.
\<close>


text\<open>Eine \<^typ>\<open>('person, 'welt) handlungsabsicht\<close> gibt eine \<^typ>\<open>'welt option\<close> zurück,
anstatt einer \<^typ>\<open>'welt\<close>.
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
Denn moralisch sind Stehlen und Nichtstun sehr verschieden.\<close>


text\<open>Folgende Funktion modelliert die Ausführung einer Handlungsabsicht.\<close>
fun nachher_handeln
  :: \<open>'person \<Rightarrow> 'welt \<Rightarrow> ('person, 'welt) handlungsabsicht \<Rightarrow> 'welt\<close>
where
  \<open>nachher_handeln handelnde_person welt (Handlungsabsicht h) = 
    (case h handelnde_person welt of Some welt' \<Rightarrow> welt'
                                  | None \<Rightarrow> welt)\<close>

text\<open>Gegeben die \<^term_type>\<open>handelnde_person :: 'person\<close>,
die \<^term_type>\<open>welt :: 'welt\<close> in ihrem aktuellen Zustand,
und eine \<^term_type>\<open>ha :: ('person, 'welt) handlungsabsicht\<close>, so liefert
\<^term_type>\<open>(nachher_handeln handelnde_person welt ha) :: 'welt\<close> die potenziell veränderte Welt zurück,
nachdem die Handlungsabsicht ausgeführt wurde.

Die Funktion \<^const>\<open>nachher_handeln\<close> besagt, dass eine gescheiterte Handlung
die Welt nicht verändert.
Ab diesem Punkt sind also die Handlungen "sich selbst bestehlen" und "Nichtstun"
von außen ununterscheidbar, da beide die Welt nicht verändern.\<close>

text\<open>Dank der Hilfsdefinition \<^const>\<open>nachher_handeln\<close> können wir nun "Handeln"
allgemein definieren.
Folgende Funktion überführt effektiv eine \<^typ>\<open>('person, 'welt) handlungsabsicht\<close> in
eine \<^typ>\<open>'welt handlung\<close>.\<close>
definition handeln
  :: \<open>'person \<Rightarrow> 'welt \<Rightarrow> ('person, 'welt) handlungsabsicht \<Rightarrow> 'welt handlung\<close>
where
  \<open>handeln handelnde_person welt ha \<equiv> Handlung welt (nachher_handeln handelnde_person welt ha)\<close>


text\<open>Die Funktion \<^const>\<open>nachher_handeln\<close> liefert die Welt nach der Handlung.
Die Funktion \<^const>\<open>handeln\<close> liefert eine \<^typ>\<open>'welt handlung\<close>,
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
Eine \<^typ>\<open>('person, 'welt) handlungsabsicht\<close> kann nicht geprinted werden!
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

fun ausfuehrbar :: \<open>'person \<Rightarrow> 'welt \<Rightarrow> ('person, 'welt) handlungsabsicht \<Rightarrow> bool\<close>
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
lemma nicht_ausfuehrbar_nachher_handeln:
  \<open>\<not>ausfuehrbar p welt ha \<Longrightarrow>
    nachher_handeln p welt ha = welt\<close>
  by(cases \<open>ha\<close>, simp add: ausfuehrbar.simps nachher_handeln.simps split:option.split)
(*>*)


subsection\<open>Interpretation: Gesinnungsethik vs. Verantwortungethik \label{sec:gesinnungsverantwortungsethik}\<close>
text\<open>
Nur basierend auf unserem Modell einer \<^const>\<open>Handlung\<close> und \<^const>\<open>Handlungsabsicht\<close> können
wir bereits erste Aussagen über moralische Bewertungen treffen.



Sei eine Ethik eine Funktion, welche einem beliebigen \<^typ>\<open>'\<alpha>\<close> eine
Bewertung Gut = \<^const>\<open>True\<close>, Schlecht = \<^const>\<open>False\<close> zuordnet.

  \<^item> Eine Ethik hat demnach den Typ: \<^typ>\<open>'\<alpha> \<Rightarrow> bool\<close>.

\<^medskip>

Laut \<^url>\<open>https://de.wikipedia.org/wiki/Gesinnungsethik\<close> ist eine Gesinnungsethik
"[..] eine der moralischen Theorien,
 die Handlungen nach der Handlungsabsicht [...]  bewertet,
 und zwar ungeachtet der nach erfolgter Handlung eingetretenen Handlungsfolgen."

  \<^item> Demnach ist eine Gesinnungsethik: \<^typ>\<open>('person, 'welt) handlungsabsicht \<Rightarrow> bool\<close>.

\<^smallskip>

Nach \<^url>\<open>https://de.wikipedia.org/wiki/Verantwortungsethik\<close> steht die Verantwortungsethik
dazu im strikten Gegensatz, da die Verantwortungsethik
"in der Bewertung des Handelns die Verantwortbarkeit der \<^emph>\<open>tatsächlichen Ergebnisse\<close> betont."

  \<^item> Demnach ist eine Verantwortungsethik: \<^typ>\<open>'welt handlung \<Rightarrow> bool\<close>.


\<^medskip>

Da \<^const>\<open>handeln\<close> eine Handlungsabsicht \<^typ>\<open>('person, 'welt) handlungsabsicht\<close>
in eine konkrete Änderung der Welt \<^typ>\<open>'welt handlung\<close> überführt,
können wie die beiden Ethiktypen miteinander in Verbindung setzen.
Wir sagen, eine Gesinnungsethik und eine Verantwortungsethik sind konsistent,
genau dann wenn für jede Handlungsabsicht, die
Gesinnungsethik die Handlungsabsicht genau so bewertet,
wie die Verantwortungsethik die Handlungsabsicht bewerten würde,
wenn die die Handlungsabsicht in jeder möglichen Welt und
als jede mögliche handelnde Person tatsächlich ausgeführt wird und die Folgen betrachtet werden:
\<close>

definition gesinnungsethik_verantwortungsethik_konsistent
  :: \<open>(('person, 'welt) handlungsabsicht \<Rightarrow> bool) \<Rightarrow> ('welt handlung \<Rightarrow> bool) \<Rightarrow> bool\<close>
where
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
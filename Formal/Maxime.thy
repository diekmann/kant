theory Maxime
imports Handlung BeispielPerson ExecutableHelper Xor
begin

section\<open>Maxime\<close>
text\<open>In diesem Abschnitt werden wir das Konzept einer Maxime modellieren.\<close>

text\<open>
Nach \<^url>\<open>https://de.wikipedia.org/wiki/Maxime\<close> ist eine Maxime ein
persönlicher Grundsatz des Wollens und Handelns.
Nach Kant ist eine Maxime ein "subjektives Prinzip des Wollens".

Modell einer \<^emph>\<open>Maxime\<close>:
Eine Maxime in diesem Modell beschreibt ob eine Handlung in einer gegebenen Welt gut ist.

Faktisch bruachen wir um eine Maxime zu modellieren
  \<^item> \<^typ>\<open>'person\<close>: die handelnde Person, i.e., \<^emph>\<open>ich\<close>.
  \<^item> \<^typ>\<open>'welt handlung\<close>: die zu betrachtende Handlung.
  \<^item> \<^typ>\<open>bool\<close>: Das Ergebnis der Betrachtung. \<^const>\<open>True\<close> = Gut; \<^const>\<open>False\<close> = Schlecht.

Wir brauchen sowohl die \<^typ>\<open>'welt handlung\<close> als auch die \<^typ>\<open>'person\<close> aus deren Sicht die Maxime
definiert ist,
da es einen großen Unterschied machen kann ob ich selber handel,
ob ich Betroffener einer fremden Handlung bin, oder nur Außenstehender.
\<close>
datatype ('person, 'welt) maxime = Maxime \<open>'person \<Rightarrow> 'welt handlung \<Rightarrow> bool\<close>
                                 (*          ich    -> Auswirkung      -> gut/schlecht  *)

text\<open>Auswertung einer Maxime:\<close>
fun okay :: \<open>('person, 'welt) maxime \<Rightarrow> 'person \<Rightarrow> 'welt handlung \<Rightarrow> bool\<close> where
  \<open>okay (Maxime m) p h = m p h\<close>


text\<open>Beispiel\<close>
definition maxime_mir_ist_alles_recht :: \<open>('person, 'welt) maxime\<close> where
  \<open>maxime_mir_ist_alles_recht \<equiv> Maxime (\<lambda>_ _. True)\<close>

subsection\<open>Maxime in Sinne Kants?\<close>
text\<open>Kants kategorischer Imperativ ist eine deontologische Ethik,
d.h.,
"Es wird eben nicht bewertet, was die Handlung bewirkt, sondern wie die Absicht beschaffen ist."
\<^url>\<open>https://de.wikipedia.org/wiki/Kategorischer_Imperativ\<close>.

Wenn wir Kants kategorischen Imperativ bauen wollen, dürfen wir also nicht die Folgen einer
Handlung betrachten, sondern nur die Absicht dahinter.
Doch unsere \<^const>\<open>Maxime\<close> betrachtet eine \<^typ>\<open>'welt handlung\<close>, also eine konkrete Handlung,
die nur durch ihre Folgen gegeben ist.
Die Maxime betrachtet keine Handlungsabsicht \<^typ>\<open>('person, 'welt) handlungsabsicht\<close>.

>>Zweifellos hat Immanuel Kant eine Art von Gesinnungsethik vertreten<<
\<^url>\<open>https://de.wikipedia.org/wiki/Gesinnungsethik#Gesinnungsethik_bei_Kant\<close>.
Wie wir bereits im Abschnitt \ref{sec:gesinnungsverantwortungsethik} gesehen haben,
sollte eine Maxime demnach eine \<^typ>\<open>('person, 'welt) handlungsabsicht\<close> und
keine \<^typ>\<open>'welt handlung\<close> betrachten.
Dennoch haben wir uns für unsere \<^emph>\<open>extensionale\<close> Interpretation für
eine \<^typ>\<open>('person, 'welt) handlungsabsicht\<close> entschieden.
Und auch wenn wir das Zitat der
\<^url>\<open>https://de.wikipedia.org/w/index.php?title=Gesinnungsethik&oldid=218409490#Gesinnungsethik_bei_Kant\<close>
weiterlesen, sehen wir, dass unser Modell zumindest nicht komplett inkonsistent ist:
>>Zweifellos hat Immanuel Kant eine Art von Gesinnungsethik vertreten,
die allerdings nicht im Gegensatz zu einer Verantwortungsethik,
sondern allenfalls zu einer bloßen „Erfolgsethik“ steht.<<

Kant unterscheidet unter Anderem
"zwischen >>apriorischen<< und >>empirischen<< Urteilen" @{cite russellphi}.
Wenn wir uns den Typ \<^typ>\<open>'welt handlung\<close> als Beobachtung der Welt \<^const>\<open>vorher\<close> und \<^const>\<open>nachher\<close> anschauen,
dann könnte man sagen, unser Moralbegriff der \<^const>\<open>Maxime\<close> sei empirisch.
Für Kant gilt jedoch:
"Alle Moralbegriffe [...] haben \<^emph>\<open>a priori\<close> ihren Sitz und Ursprung ausschließlich in der Vernunft" @{cite russellphi}.
Hier widerspricht unser Modell wieder Kant, da unser Modell empirisch ist und nicht apriorisch.


Dies mag nun als Fehler in unserem Modell verstanden werden.
Doch irgendwo müssen wir praktisch werden.
Nur von Handlungsabsichten zu reden, ohne dass die beabsichtigten Folgen betrachtet werden
ist mir einfach zu abstrakt und nicht greifbar.


Alles ist jedoch nicht verloren, denn "Alle rein mathematischen Sätze sind [...] apriorisch" @{cite russellphi}.
Und auch Russel schlussfolgert:
"Um ein ausreichendes Kriterium zu gewinnen, müßten wir Kants rein formalen Standpunkt aufgeben
und die Wirkung der Handlungen in Betracht ziehen" @{cite russellphi}.

Auch Kants kategorischer Imperativ und die Goldene Regel sind grundverschieden:
\<^url>\<open>https://web.archive.org/web/20220123174117/https://www.goethegymnasium-hildesheim.de/index.php/faecher/faecher/gesellschaftswissenschaften/philosophie\<close>
Dennoch, betrachten wir den kategorischen Imperativ als eine Verallgemeinerung
der goldenen Regel.
\<close>


subsection\<open>Die Goldene Regel\<close>
text\<open>Die Goldene Regel nach \<^url>\<open>https://de.wikipedia.org/wiki/Goldene_Regel\<close> sagt:

  „Behandle andere so, wie du von ihnen behandelt werden willst.“

  „Was du nicht willst, dass man dir tu, das füg auch keinem andern zu.“


So wie wir behandelt werden wollen ist modelliert durch eine \<^typ>\<open>('person, 'welt) maxime\<close>.

Die goldene Regel testet ob eine Handlung, bzw. Handlungsabsicht moralisch ist.
Um eine Handlung gegen eine Maxime zu testen fragen wir uns:
  \<^item> Was wenn jeder so handeln würde?
  \<^item> Was wenn jeder nach dieser Maxime handeln würde?

Beispielsweise mag "stehlen" und "bestohlen werden" die gleiche Handlung sein,
jedoch wird sie von Täter und Opfer grundverschieden wahrgenommen.
\<close>
definition bevoelkerung :: \<open>'person set\<close> where \<open>bevoelkerung \<equiv> UNIV\<close>

definition wenn_jeder_so_handelt
    :: \<open>'welt \<Rightarrow> ('person, 'welt) handlungsabsicht \<Rightarrow> ('welt handlung) set\<close>
  where
    \<open>wenn_jeder_so_handelt welt handlungsabsicht \<equiv>
      (\<lambda>handelnde_person. handeln handelnde_person welt handlungsabsicht) ` bevoelkerung\<close>

fun was_wenn_jeder_so_handelt_aus_sicht_von
    :: \<open>'welt \<Rightarrow> ('person, 'welt) maxime \<Rightarrow> ('person, 'welt) handlungsabsicht \<Rightarrow> 'person \<Rightarrow> bool\<close>
  where
    \<open>was_wenn_jeder_so_handelt_aus_sicht_von welt m handlungsabsicht betroffene_person =
        (\<forall> h \<in> wenn_jeder_so_handelt welt handlungsabsicht. okay m betroffene_person h)\<close>


text\<open>Für eine gegebene Welt und eine gegebene Maxime nennen wir eine Handlungsabsicht
genau dann moralisch, wenn die Handlung auch die eigene Maxime erfüllt,
wenn die Handlung von anderen durchgeführt würde.\<close>
definition moralisch ::
  \<open>'welt \<Rightarrow> ('person, 'welt) maxime \<Rightarrow> ('person, 'welt) handlungsabsicht \<Rightarrow> bool\<close> where
\<open>moralisch welt handlungsabsicht maxime \<equiv>
  \<forall>p \<in> bevoelkerung. was_wenn_jeder_so_handelt_aus_sicht_von welt handlungsabsicht maxime p\<close>

text\<open>
Faktisch bedeutet diese Definition, wir bilden das Kreuzprodukt \<^term>\<open>bevoelkerung \<times> bevoelkerung\<close>,
wobei jeder einmal als handelnde Person auftritt und einmal als betroffene Person.
\<close>
lemma moralisch_unfold:
  \<open>moralisch welt (Maxime m) handlungsabsicht \<longleftrightarrow>
        (\<forall>p1\<in>bevoelkerung. \<forall>p2\<in>bevoelkerung. m p1 (handeln p2 welt handlungsabsicht))\<close>
  by(simp add: moralisch_def wenn_jeder_so_handelt_def)
lemma \<open>moralisch welt (Maxime m) handlungsabsicht \<longleftrightarrow>
        (\<forall>(p1,p2)\<in>bevoelkerung\<times>bevoelkerung. m p1 (handeln p2 welt handlungsabsicht))\<close>
  unfolding moralisch_unfold by simp

lemma moralisch_simp:
  \<open>moralisch welt m handlungsabsicht \<longleftrightarrow>
        (\<forall>p1 p2. okay m p1 (handeln p2 welt handlungsabsicht))\<close>
  unfolding moralisch_unfold
  by (cases \<open>m\<close>, simp add: bevoelkerung_def moralisch_unfold)

text\<open>
Wir können die goldene Regel auch umformulieren,
nicht als Imperativ, sondern als Beobachtung eines Wunschzustandes:
Wenn eine Handlung für eine Person okay ist, dann muss sie auch Okay sein,
wenn jemand anderes diese Handlung ausführt.

Formal:
\<^term>\<open>okay m ich (handeln ich welt handlungsabsicht) \<Longrightarrow> \<forall>p2. okay m ich (handeln p2 welt handlungsabsicht)\<close>

Genau dies können wir aus unserer Definition von \<^const>\<open>moralisch\<close> ableiten:\<close>

lemma goldene_regel:
  \<open>moralisch welt m handlungsabsicht \<Longrightarrow>
   okay m ich (handeln ich welt handlungsabsicht) \<Longrightarrow>
   \<forall>p2. okay m ich (handeln p2 welt handlungsabsicht)\<close>
  by (simp add: moralisch_simp)

text\<open>Für das obige lemma brauchen wir die Annahme
\<^term>\<open>m ich (handeln ich welt handlungsabsicht)\<close> gar nicht.

Wenn für eine gegebene \<^term>\<open>Maxime m\<close> eine Handlungsabsicht moralisch ist,
dann ist es auch okay, wenn ich von der Handlungsabsicht betroffen bin,
egal wer sie ausführt.\<close>
corollary
  \<open>moralisch welt m handlungsabsicht \<Longrightarrow>
   \<forall>p2. okay m ich (handeln p2 welt handlungsabsicht)\<close>
  by (simp add: moralisch_simp)

text\<open>Die umgekehrte Richtung gilt nicht, weil diese Formulierung nur die Handlungen betrachtet,
die okay sind.\<close>


text\<open>Entweder ist etwas moralisch,
oder es gibt zwei Personen, für die eine Handlungsabsicht nicht \<^const>\<open>okay\<close> ist.\<close>
lemma moralisch_oder_nicht_okay:
  "moralisch welt m ha \<oplus> (\<exists>p1 p2. \<not> okay m p2 (handeln p1 welt ha))"
  by (auto simp add: xor2 moralisch_simp)

(*<*)
text\<open>Versuch eine executable version zu bauen.
Wir müssen die Bevölkerung enumerieren.\<close>
definition moralisch_exhaust where
  \<open>moralisch_exhaust bevoelk welt maxime handlungsabsicht \<equiv>
    (case maxime of (Maxime m) \<Rightarrow> 
      list_all (\<lambda>(p,x). m p (handeln x welt handlungsabsicht)) (List.product bevoelk bevoelk))\<close>

lemma moralisch_exhaust_univ: \<open>set b = (UNIV::'person set) \<Longrightarrow>
        moralisch welt maxime ha = moralisch_exhaust b welt maxime ha\<close>
  apply(case_tac \<open>maxime\<close>, rename_tac m, simp)
  unfolding moralisch_unfold moralisch_exhaust_def bevoelkerung_def
  apply(simp)
  by(simp add: list_all_iff)

subsection \<open>Making it executable\<close>
  (*TODO: for reasons I do not understand,
    moralisch_exhaust [Alice, Bob, Carol, Eve] (not enum) needs [code_unfold]
    but
    moralisch_exhaust (enum) needs [code]
    ? ? ?*)
  lemma moralisch_exhaust [code]: \<open>moralisch = moralisch_exhaust enum_class.enum\<close>
    apply(simp add: fun_eq_iff)
    apply(rule allI)+
    apply(rule moralisch_exhaust_univ)
    using enum_UNIV by simp
  
  declare moralisch_def[code del] \<comment> \<open>Only use executable \<^const>\<open>moralisch_exhaust\<close>\<close>
(*>*)

text\<open>Hier schlägt das Programmiererherz höher:
Wenn \<^typ>\<open>'person\<close> aufzählbar ist haben wir ausführbaren Code: @{thm moralisch_exhaust}
wobei \<^const>\<open>moralisch_exhaust\<close> implementiert ist als @{thm moralisch_exhaust_def}.
\<close>

subsection\<open>Maximen Debugging\<close>
text\<open>Der folgende Datentyp modelliert ein Beispiel in welcher Konstellation eine gegebene
Maxime verletzt ist:\<close>

record ('person, 'welt) dbg_verletzte_maxime =
  dbg_opfer :: \<open>'person\<close> \<comment>\<open>verletzt für; das Opfer\<close>
  dbg_taeter :: \<open>'person\<close> \<comment>\<open>handelnde Person; der Täter\<close>
  dbg_handlung :: \<open>'welt handlung\<close> \<comment>\<open>Die verletzende Handlung\<close>

text\<open>Alle Feldnamen bekommen das Präfix "dbg" für Debug um den Namensraum nicht zu verunreinigen.\<close>
    

text\<open>Die folgende Funktion liefert alle Gegebenheiten welche eine Maxime verletzen:\<close>
fun debug_maxime
  :: \<open>('welt \<Rightarrow> 'printable_world) \<Rightarrow> 'welt \<Rightarrow>
      ('person, 'welt) maxime \<Rightarrow> ('person, 'welt) handlungsabsicht
      \<Rightarrow> (('person, 'printable_world) dbg_verletzte_maxime) set\<close>
where
  \<open>debug_maxime print_world welt m handlungsabsicht =
    {\<lparr>
      dbg_opfer = p1,
      dbg_taeter = p2,
      dbg_handlung = map_handlung print_world (handeln p2 welt handlungsabsicht)
     \<rparr>
      | p1 p2. \<not>okay m p1 (handeln p2 welt handlungsabsicht)}\<close>


text\<open>Es gibt genau dann keine Beispiele für Verletzungen, wenn die Maxime erfüllt ist:\<close>
lemma \<open>debug_maxime print_world welt maxime handlungsabsicht = {}
        \<longleftrightarrow> moralisch welt maxime handlungsabsicht\<close>
  apply(case_tac \<open>maxime\<close>, rename_tac m, simp)
  by(simp add: moralisch_unfold bevoelkerung_def)

(*<*)
definition debug_maxime_exhaust where
  \<open>debug_maxime_exhaust bevoelk print_world welt maxime ha \<equiv>
    (case maxime of (Maxime m) \<Rightarrow> 
      map (\<lambda>(p1,p2). \<lparr> dbg_opfer=p1, dbg_taeter=p2, dbg_handlung=map_handlung print_world (handeln p2 welt ha)\<rparr>)
        (filter (\<lambda>(p1,p2). \<not>m p1 (handeln p2 welt ha)) (List.product bevoelk bevoelk)))\<close>

lemma debug_maxime_exhaust [code]:
  \<open>debug_maxime print_world welt maxime ha
    = set (debug_maxime_exhaust enum_class.enum print_world welt maxime ha)\<close>
  apply(case_tac \<open>maxime\<close>, rename_tac m, simp)
  apply(simp add: debug_maxime_exhaust_def enum_UNIV)
  by(simp add: image_Collect)
(*>*)

subsection \<open>Beispiel\<close>
(*TODO: bekomme ich das irgendwie in einen eignenen namespace?*)
(*this causes
  fun moralisch _ _ _ = raise Fail "Kant.moralisch";
when we don't use moralisch_exhaust.
So when code fails with "Kant.moralisch", make sure the 'person implements enum.*)

text\<open>Beispiel:
Die Welt sei nur eine Zahl und die zu betrachtende Handlungsabsicht sei,
dass wir diese Zahl erhöhen.
Die Mir-ist-alles-Recht Maxime ist hier erfüllt:\<close>
beispiel \<open>moralisch
            (42::nat)
             maxime_mir_ist_alles_recht
            (Handlungsabsicht (\<lambda>(person::person) welt. Some (welt + 1)))\<close> by eval

text\<open>Beispiel:
Die Welt ist modelliert als eine Abbildung von Person auf Besitz.
Die Maxime sagt, dass Leute immer mehr oder gleich viel wollen, aber nie etwas verlieren wollen.
In einer Welt in der keiner etwas hat, erfüllt die Handlung jemanden 3 zu geben die Maxime.
\<close>
beispiel \<open>moralisch
            [Alice \<mapsto> (0::nat), Bob \<mapsto> 0, Carol \<mapsto> 0, Eve \<mapsto> 0]
            (Maxime (\<lambda>person handlung.
                (the ((vorher handlung) person)) \<le> (the ((nachher handlung) person))))
            (Handlungsabsicht (\<lambda>person welt. Some (welt(person \<mapsto> 3))))\<close>
  by eval
beispiel \<open>debug_maxime show_map
            [Alice \<mapsto> (0::nat), Bob \<mapsto> 0, Carol \<mapsto> 0, Eve \<mapsto> 0]
            (Maxime (\<lambda>person handlung.
                (the ((vorher handlung) person)) \<le> (the ((nachher handlung) person))))
            (Handlungsabsicht (\<lambda>person welt. Some(welt(person \<mapsto> 3))))
  = {}\<close>
  by eval


text\<open>Wenn nun \<^const>\<open>Bob\<close> allerdings bereits 4 hat, würde die obige Handlung ein Verlust
für ihn bedeuten und die Maxime ist nicht erfüllt.\<close>
beispiel \<open>\<not> moralisch
            [Alice \<mapsto> (0::nat), Bob \<mapsto> 4, Carol \<mapsto> 0, Eve \<mapsto> 0]
            (Maxime (\<lambda>person handlung.
                (the ((vorher handlung) person)) \<le> (the ((nachher handlung) person))))
            (Handlungsabsicht (\<lambda>person welt. Some (welt(person \<mapsto> 3))))\<close>
  by eval
beispiel \<open>debug_maxime show_map
            [Alice \<mapsto> (0::nat), Bob \<mapsto> 4, Carol \<mapsto> 0, Eve \<mapsto> 0]
            (Maxime (\<lambda>person handlung.
                (the ((vorher handlung) person)) \<le> (the ((nachher handlung) person))))
            (Handlungsabsicht (\<lambda>person welt. Some (welt(person \<mapsto> 3))))
  = {\<lparr>
      dbg_opfer = Bob,
      dbg_taeter = Bob,
      dbg_handlung = Handlung [(Alice, 0), (Bob, 4), (Carol, 0), (Eve, 0)]
                              [(Alice, 0), (Bob, 3), (Carol, 0), (Eve, 0)]
     \<rparr>}\<close>
  by eval



subsection\<open>Maximen Kombinieren\<close>
text\<open>Konjunktion (Und) zweier Maximen.\<close>
fun MaximeConj
  :: \<open>('person, 'welt) maxime \<Rightarrow> ('person, 'welt) maxime \<Rightarrow> ('person, 'welt) maxime\<close>
  where
\<open>MaximeConj (Maxime m1) (Maxime m2) = Maxime (\<lambda>p h. m1 p h \<and> m2 p h)\<close>

text\<open>Die erwarteten Regeln auf einer Konjunktion gelten.\<close>
lemma okay_MaximeConj: \<open>okay (MaximeConj m1 m2) p h \<longleftrightarrow> okay m1 p h \<and> okay m2 p h\<close>
  by(cases \<open>m1\<close>, cases \<open>m2\<close>, simp)

lemma moralisch_MaximeConj:
  \<open>moralisch welt (MaximeConj m1 m2) ha \<longleftrightarrow> moralisch welt m1 ha \<and> moralisch welt m2 ha\<close>
  apply(simp add: moralisch_simp okay_MaximeConj)
  by blast

lemma moralisch_MaximeConj_False:
  \<open>moralisch welt (MaximeConj m1 (Maxime (\<lambda>_ _. True))) ha \<longleftrightarrow> moralisch welt m1 ha\<close>
  by(simp add: moralisch_simp okay_MaximeConj)

lemma moralisch_MaximeConj_True:
  \<open>\<not> moralisch welt (MaximeConj m1 (Maxime (\<lambda>_ _. False))) ha\<close>
  by(simp add: moralisch_simp okay_MaximeConj)

(*<*)
declare MaximeConj.simps[simp del]
(*>*)

text\<open>Disjunktion (Oder) zweier Maximen.\<close>
fun MaximeDisj
  :: \<open>('person, 'welt) maxime \<Rightarrow> ('person, 'welt) maxime \<Rightarrow> ('person, 'welt) maxime\<close>
  where
\<open>MaximeDisj (Maxime m1) (Maxime m2) = Maxime (\<lambda>p h. m1 p h \<or> m2 p h)\<close>

lemma okay_MaximeDisj: \<open>okay (MaximeDisj m1 m2) p h \<longleftrightarrow> okay m1 p h \<or> okay m2 p h\<close>
  by(cases \<open>m1\<close>, cases \<open>m2\<close>, simp)


text\<open>Leider ist \<^const>\<open>MaximeDisj\<close> weniger schön,
weil es kein genau-dann-wenn mit der Disjunktion (\<^term>\<open>m1 \<or> m2\<close>) gibt.\<close>

lemma moralisch_MaximeDisjI:
  \<open>moralisch welt m1 ha \<or> moralisch welt m2 ha \<Longrightarrow> moralisch welt (MaximeDisj m1 m2) ha\<close>
  apply(simp add: moralisch_simp okay_MaximeDisj)
  by auto
text\<open>Die Rückrichtung gilt leider nicht.
\<^term>\<open>MaximeDisj m1 m2\<close> is effektiv schwächer, da sich jede Person unabhängig entscheiden darf,
ob sie \<^term>\<open>m1\<close> oder \<^term>\<open>m2\<close> folgt.
Im Gegensatz dazu sagt \<^term>\<open>moralisch welt m1 ha \<or> moralisch welt m2 ha\<close>, dass für
\<^emph>\<open>alle\<close> Personen entweder \<^term>\<open>m1\<close> oder \<^term>\<open>m2\<close> gelten muss.\<close>

lemma moralisch_MaximeDisj1:
  \<open>moralisch welt m1 ha \<Longrightarrow> moralisch welt (MaximeDisj m1 m2) ha\<close>
  by(simp add: moralisch_MaximeDisjI)
lemma moralisch_MaximeDisj2:
  \<open>moralisch welt m2 ha \<Longrightarrow> moralisch welt (MaximeDisj m1 m2) ha\<close>
  by(simp add: moralisch_MaximeDisjI)

lemma moralisch_MaximeDisj_False:
  \<open>moralisch welt (MaximeDisj m1 (Maxime (\<lambda>_ _. False))) ha \<longleftrightarrow> moralisch welt m1 ha\<close>
  by(simp add: moralisch_simp okay_MaximeDisj)

lemma moralisch_MaximeDisj_True:
  \<open>moralisch welt (MaximeDisj m1 (Maxime (\<lambda>_ _. True))) ha\<close>
  by(simp add: moralisch_simp okay_MaximeDisj)

(*<*)
declare MaximeDisj.simps[simp del]
(*>*)

text\<open>Negation.\<close>
fun MaximeNot :: \<open>('person, 'welt) maxime \<Rightarrow> ('person, 'welt) maxime\<close>
  where
\<open>MaximeNot (Maxime m) = Maxime (\<lambda>p h. \<not> m p h)\<close>

lemma okay_MaximeNot: \<open>okay (MaximeNot m) p h \<longleftrightarrow> \<not> okay m p h\<close>
  by(cases \<open>m\<close>, simp)

lemma okay_DeMorgan:
\<open>okay (MaximeNot (MaximeConj m1 m2)) p h
  \<longleftrightarrow>  okay (MaximeDisj (MaximeNot m1) (MaximeNot m2)) p h\<close>
  by (simp add: okay_MaximeConj okay_MaximeDisj okay_MaximeNot)

lemma moralisch_DeMorgan:
\<open>moralisch welt (MaximeNot (MaximeConj m1 m2)) ha
  \<longleftrightarrow>  moralisch welt (MaximeDisj (MaximeNot m1) (MaximeNot m2)) ha\<close>
  by (simp add: moralisch_simp okay_DeMorgan)
  
(*<*)
declare MaximeNot.simps[simp del]
(*>*)
end
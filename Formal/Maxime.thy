theory Maxime
imports Handlung BeispielPerson ExecutableHelper
begin

section\<open>Maxime\<close>

text\<open>
Nach \<^url>\<open>https://de.wikipedia.org/wiki/Maxime\<close> ist eine Maxime ein
persönlicher Grundsatz des Wollens und Handelns.
Nach Kant ist eine Maxime ein "subjektives Prinzip des Wollens".

Modell einer \<^emph>\<open>Maxime\<close>:
Eine Maxime in diesem Modell beschreibt ob eine Handlung in einer gegebenen Welt gut ist.

Faktisch ist eine Maxime
  \<^item> \<^typ>\<open>'person\<close>: die handelnde Person, i.e., \<^emph>\<open>ich\<close>.
  \<^item> \<^typ>\<open>'world handlung\<close>: die zu betrachtende Handlung.
  \<^item> \<^typ>\<open>bool\<close>: Das Ergebnis der Betrachtung. \<^const>\<open>True\<close> = Gut; \<^const>\<open>False\<close> = Schlecht.

Wir brauchen sowohl die \<^typ>\<open>'world handlung\<close> als auch die \<^typ>\<open>'person\<close> aus deren Sicht die Maxime
definiert ist,
da es einen großen Unterschied machen kann ob ich selber handel,
ob ich Betroffener einer fremden Handlung bin, oder nur Außenstehender.
\<close>
datatype ('person, 'world) maxime = Maxime \<open>'person \<Rightarrow> 'world handlung \<Rightarrow> bool\<close>
                                 (*          ich    -> Auswirkung      -> gut/schlecht  *)

text\<open>Auswertung einer Maxime:\<close>
fun okay :: \<open>('person, 'world) maxime \<Rightarrow> 'person \<Rightarrow> 'world handlung \<Rightarrow> bool\<close> where
  \<open>okay (Maxime m) p h = m p h\<close>


text\<open>Beispiel\<close>
definition maxime_mir_ist_alles_recht :: \<open>('person, 'world) maxime\<close> where
  \<open>maxime_mir_ist_alles_recht \<equiv> Maxime (\<lambda>_ _. True)\<close>

subsection\<open>Maxime in Sinne Kants?\<close>
text\<open>Kants kategorischer Imperativ ist eine deontologische Ethik,
d.h.,
"Es wird eben nicht bewertet, was die Handlung bewirkt, sondern wie die Absicht beschaffen ist."
\<^url>\<open>https://de.wikipedia.org/wiki/Kategorischer_Imperativ\<close>.

Wenn wir Kants kategorischen Imperativ bauen wollen, dürfen wir also nicht die Folgen einer
Handlung betrachten, sondern nur die Absicht dahinter.
Doch unsere \<^const>\<open>Maxime\<close> betrachtet eine \<^typ>\<open>'world handlung\<close>, also eine konkrete Handlung,
die nur durch ihre Folgen gegeben ist.
Die Maxime betrachtet keine Handlungsabsicht \<^typ>\<open>('person, 'world) handlungF\<close>.

Dies mag nun als Fehler in unserem Modell verstanden werden.
Doch irgendwo müssen wir praktisch werden.
Nur von Handlungsabsichten zu reden, ohne dass die beabsichtigten Folgen betrachtet werden
ist mir einfach zu abstrakt und nicht greifbar.

Kants kategorischer Imperativ und die Goldene Regel grundverschieden:
\<^url>\<open>https://web.archive.org/web/20220123174117/https://www.goethegymnasium-hildesheim.de/index.php/faecher/faecher/gesellschaftswissenschaften/philosophie\<close>
Dennoch, betrachten wir den kategorischen Imperativ als eine Verallgemeinerung
der goldenen Regel.
\<close>

(*
TODO: in einer Maxime darf keine konkrete Person hardcoded sein.
 Verboten: Maxime (\ich _ -> if ich == "konkrete Person" then ...)

das muss formalisiert werden!
Maximen duerfen nicht _diskriminierend_ sein.
*)

subsection\<open>Die Goldene Regel\<close>
text\<open>Die Goldene Regel nach \<^url>\<open>https://de.wikipedia.org/wiki/Goldene_Regel\<close> sagt:

  „Behandle andere so, wie du von ihnen behandelt werden willst.“

  „Was du nicht willst, dass man dir tu, das füg auch keinem andern zu.“


So wie wir behandelt werden wollen ist modelliert durch eine \<^typ>\<open>('person, 'world) maxime\<close>.

Die goldene Regel testet ob eine Handlung, bzw. Handlungsabsicht moralisch ist.
Um eine Handlung gegen eine Maxime zu testen fragen wir uns:
  \<^item> Was wenn jeder so handeln würde?
  \<^item> Was wenn jeder nach dieser Maxime handeln würde?

Beispielsweise mag "stehlen" und "bestohlen werden" die gleiche Handlung sein,
jedoch wird sie von Täter und Opfer grundverschieden wahrgenommen.
\<close>
definition bevoelkerung :: \<open>'person set\<close> where \<open>bevoelkerung \<equiv> UNIV\<close>
definition wenn_jeder_so_handelt
    :: \<open>'world \<Rightarrow> ('person, 'world) handlungF \<Rightarrow> ('world handlung) set\<close>
  where
    \<open>wenn_jeder_so_handelt welt handlungsabsicht \<equiv>
      (\<lambda>handelnde_person. handeln handelnde_person welt handlungsabsicht) ` bevoelkerung\<close>
fun was_wenn_jeder_so_handelt_aus_sicht_von
    :: \<open>'world \<Rightarrow> ('person, 'world) maxime \<Rightarrow> ('person, 'world) handlungF \<Rightarrow> 'person \<Rightarrow> bool\<close>
  where
    \<open>was_wenn_jeder_so_handelt_aus_sicht_von welt m handlungsabsicht betroffene_person =
        (\<forall> h \<in> wenn_jeder_so_handelt welt handlungsabsicht. okay m betroffene_person h)\<close>


text\<open>Für eine gegebene Welt und eine gegebene Maxime nennen wir eine Handlungsabsicht
genau dann moralisch, wenn die Handlung auch die eigene Maxime erfüllt,
wenn die Handlung von anderen durchgeführt würde.\<close>
definition moralisch ::
  \<open>'world \<Rightarrow> ('person, 'world) maxime \<Rightarrow> ('person, 'world) handlungF \<Rightarrow> bool\<close> where
\<open>moralisch welt handlungsabsicht maxime \<equiv>
  \<forall>p \<in> bevoelkerung. was_wenn_jeder_so_handelt_aus_sicht_von welt handlungsabsicht maxime p\<close>

text\<open>
Faktisch bedeutet diese Definition, wir bilden das Kreuzprodukt Bevölkerung x Bevölkerung,
wobei jeder einmal als handelnde Person auftritt und einmal als betroffene Person.
\<close>
lemma moralisch_unfold:
  \<open>moralisch welt (Maxime m) handlungsabsicht \<longleftrightarrow>
        (\<forall>p1\<in>bevoelkerung. \<forall>p2\<in>bevoelkerung. m p1 (handeln p2 welt handlungsabsicht))\<close>
  by(simp add: moralisch_def wenn_jeder_so_handelt_def)
lemma \<open>moralisch welt (Maxime m) handlungsabsicht \<longleftrightarrow>
        (\<forall>(p1,p2)\<in>bevoelkerung\<times>bevoelkerung. m p1 (handeln p2 welt handlungsabsicht))\<close>
  unfolding moralisch_unfold by simp

(*TODO: use okay here?*)
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
\<^term>\<open>m ich (handeln ich welt handlungsabsicht) \<Longrightarrow> \<forall>p2. m ich (handeln p2 welt handlungsabsicht)\<close>

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
datatype 'person opfer = Opfer \<open>'person\<close>
datatype 'person taeter = Taeter \<open>'person\<close>
datatype ('person, 'world) verletzte_maxime = 
  VerletzteMaxime
    \<open>'person opfer\<close> \<comment>\<open>verletzt für; das Opfer\<close>
    \<open>'person taeter\<close> \<comment>\<open>handelnde Person; der Täter\<close>
    \<open>'world handlung\<close> \<comment>\<open>Die verletzende Handlung\<close>

text\<open>Die folgende Funktion liefert alle Gegebenheiten welche eine Maxime verletzen:\<close>
fun debug_maxime
  :: \<open>('world \<Rightarrow> 'printable_world) \<Rightarrow> 'world \<Rightarrow>
      ('person, 'world) maxime \<Rightarrow> ('person, 'world) handlungF
      \<Rightarrow> (('person, 'printable_world) verletzte_maxime) set\<close>
where
  \<open>debug_maxime print_world welt m handlungsabsicht =
    {VerletzteMaxime
      (Opfer p1) (Taeter p2)
      (map_handlung print_world (handeln p2 welt handlungsabsicht)) | p1 p2.
          \<not>okay m p1 (handeln p2 welt handlungsabsicht)}\<close>


text\<open>Es gibt genau dann keine Beispiele für Verletzungen, wenn die Maxime erfüllt ist:\<close>
lemma \<open>debug_maxime print_world welt maxime handlungsabsicht = {}
        \<longleftrightarrow> moralisch welt maxime handlungsabsicht\<close>
  apply(case_tac \<open>maxime\<close>, rename_tac m, simp)
  by(simp add: moralisch_unfold bevoelkerung_def)

(*<*)
definition debug_maxime_exhaust where
  \<open>debug_maxime_exhaust bevoelk print_world welt maxime ha \<equiv>
    (case maxime of (Maxime m) \<Rightarrow> 
      map (\<lambda>(p1,p2). VerletzteMaxime (Opfer p1) (Taeter p2) (map_handlung print_world (handeln p2 welt ha)))
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
lemma \<open>moralisch
            (42::nat)
             maxime_mir_ist_alles_recht
            (HandlungF (\<lambda>(person::person) welt. welt + 1))\<close> by eval

text\<open>Beispiel:
Die Welt ist modelliert als eine Abbildung von Person auf Besitz.
Die Maxime sagt, dass Leute immer mehr oder gleich viel wollen, aber nie etwas verlieren wollen.
In einer Welt in der keiner etwas hat, erfüllt die Handlung jemanden 3 zu geben die Maxime.
\<close>
lemma \<open>moralisch
            [Alice \<mapsto> (0::nat), Bob \<mapsto> 0, Carol \<mapsto> 0, Eve \<mapsto> 0]
            (Maxime (\<lambda>person handlung.
                (the ((vorher handlung) person)) \<le> (the ((nachher handlung) person))))
            (HandlungF (\<lambda>person welt. welt(person \<mapsto> 3)))\<close>
  by eval
lemma \<open>debug_maxime show_map
            [Alice \<mapsto> (0::nat), Bob \<mapsto> 0, Carol \<mapsto> 0, Eve \<mapsto> 0]
            (Maxime (\<lambda>person handlung.
                (the ((vorher handlung) person)) \<le> (the ((nachher handlung) person))))
            (HandlungF (\<lambda>person welt. welt(person \<mapsto> 3)))
  = {}\<close>
  by eval


text\<open>Wenn nun \<^const>\<open>Bob\<close> allerdings bereits 4 hat, würde die obige Handlung ein Verlust
für ihn bedeuten und die Maxime ist nicht erfüllt.\<close>
lemma \<open>\<not> moralisch
            [Alice \<mapsto> (0::nat), Bob \<mapsto> 4, Carol \<mapsto> 0, Eve \<mapsto> 0]
            (Maxime (\<lambda>person handlung.
                (the ((vorher handlung) person)) \<le> (the ((nachher handlung) person))))
            (HandlungF (\<lambda>person welt. welt(person \<mapsto> 3)))\<close>
  by eval
lemma \<open>debug_maxime show_map
            [Alice \<mapsto> (0::nat), Bob \<mapsto> 4, Carol \<mapsto> 0, Eve \<mapsto> 0]
            (Maxime (\<lambda>person handlung.
                (the ((vorher handlung) person)) \<le> (the ((nachher handlung) person))))
            (HandlungF (\<lambda>person welt. welt(person \<mapsto> 3)))
  = {VerletzteMaxime (Opfer Bob) (Taeter Bob)
     (Handlung [(Alice, 0), (Bob, 4), (Carol, 0), (Eve, 0)]
               [(Alice, 0), (Bob, 3), (Carol, 0), (Eve, 0)])}\<close>
  by eval


end
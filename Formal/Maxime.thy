theory Maxime
imports Handlung BeispielPerson ExecutableHelper
begin

section\<open>Maxime\<close>
text\<open>
Alles in diesem Abschnitt ist darauf ausgelegt, später den kategorischen Imperativ zu modellieren.
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

text\<open>Beispiel\<close>
definition maxime_mir_ist_alles_recht :: \<open>('person, 'world) maxime\<close> where
  \<open>maxime_mir_ist_alles_recht \<equiv> Maxime (\<lambda>_ _. True)\<close>

(*
TODO: in einer Maxime darf keine konkrete Person hardcoded sein.
 Verboten: Maxime (\ich _ -> if ich == "konkrete Person" then ...)
*)


text\<open>
Um eine Handlung gegen eine Maxime zu testen fragen wir uns:
  \<^item> Was wenn jeder so handeln würde?
  \<^item> Was wenn jeder diese Maxime hätte? Bsp: stehlen und bestohlen werden.
\<close>
definition bevoelkerung :: \<open>'person set\<close> where \<open>bevoelkerung \<equiv> UNIV\<close>
definition wenn_jeder_so_handelt
    :: \<open>'world \<Rightarrow> ('person, 'world) handlungF \<Rightarrow> ('world handlung) set\<close>
  where
    \<open>wenn_jeder_so_handelt welt handlungsabsicht \<equiv>
      (\<lambda>handelnde_person. handeln handelnde_person welt handlungsabsicht) ` bevoelkerung\<close>
fun was_wenn_jeder_so_handelt_aus_sicht_von
    :: \<open>'world \<Rightarrow> ('person, 'world) handlungF \<Rightarrow> ('person, 'world) maxime \<Rightarrow> 'person \<Rightarrow> bool\<close>
  where
    \<open>was_wenn_jeder_so_handelt_aus_sicht_von welt handlungsabsicht (Maxime m) betroffene_person =
        (\<forall> h \<in> wenn_jeder_so_handelt welt handlungsabsicht. m betroffene_person h)\<close>
(*Welt in ihrem aktuellen Zustand. TODO: eigentlich sollten wir für jede mögliche Welt testen!*)
(*TODO: rename zu moralisch*)
definition teste_maxime ::
  \<open>'world \<Rightarrow> ('person, 'world) handlungF \<Rightarrow> ('person, 'world) maxime \<Rightarrow> bool\<close> where
\<open>teste_maxime welt handlungsabsicht maxime \<equiv>
  \<forall>p \<in> bevoelkerung. was_wenn_jeder_so_handelt_aus_sicht_von welt handlungsabsicht maxime p\<close>

text\<open>
Faktisch bedeutet diese Definition, wir bilden das Kreuzprodukt Bevölkerung x Bevölkerung,
wobei jeder einmal als handelnde Person auftritt und einmal als betroffene Person.
\<close>
lemma teste_maxime_unfold:
  \<open>teste_maxime welt handlungsabsicht (Maxime m) =
        (\<forall>p1\<in>bevoelkerung. \<forall>p2\<in>bevoelkerung. m p1 (handeln p2 welt handlungsabsicht))\<close>
  by(simp add: teste_maxime_def wenn_jeder_so_handelt_def)
lemma \<open>teste_maxime welt handlungsabsicht (Maxime m) =
        (\<forall>(p1,p2)\<in>bevoelkerung\<times>bevoelkerung. m p1 (handeln p2 welt handlungsabsicht))\<close>
  unfolding teste_maxime_unfold by simp

(*<*)
lemma teste_maxime_simp:
  \<open>teste_maxime welt handlungsabsicht (Maxime m) =
        (\<forall>p1. \<forall>p2. m p1 (handeln p2 welt handlungsabsicht))\<close>
  unfolding teste_maxime_unfold
  by (simp add: bevoelkerung_def)

text\<open>Versuch eine executable version zu bauen.
Wir müssen die Bevölkerung enumerieren.\<close>
definition teste_maxime_exhaust where
  \<open>teste_maxime_exhaust bevoelk welt handlungsabsicht maxime \<equiv>
    (case maxime of (Maxime m) \<Rightarrow> 
      list_all (\<lambda>(p,x). m p (handeln x welt handlungsabsicht)) (List.product bevoelk bevoelk))\<close>

lemma teste_maxime_exhaust_univ: \<open>set b = (UNIV::'person set) \<Longrightarrow>
        teste_maxime welt ha maxime = teste_maxime_exhaust b welt ha maxime\<close>
  apply(case_tac \<open>maxime\<close>, rename_tac m, simp)
  unfolding teste_maxime_unfold teste_maxime_exhaust_def bevoelkerung_def
  apply(simp)
  by(simp add: list_all_iff)

subsection \<open>Making it executable\<close>
  (*TODO: for reasons I do not understand,
    teste_maxime_exhaust [Alice, Bob, Carol, Eve] (not enum) needs [code_unfold]
    but
    teste_maxime_exhaust (enum) needs [code]
    ? ? ?*)
  lemma teste_maxime_exhaust [code]: \<open>teste_maxime = teste_maxime_exhaust enum_class.enum\<close>
    apply(simp add: fun_eq_iff)
    apply(rule allI)+
    apply(rule teste_maxime_exhaust_univ)
    using enum_UNIV by simp
  
  declare teste_maxime_def[code del] \<comment> \<open>Only use executable \<^const>\<open>teste_maxime_exhaust\<close>\<close>
(*>*)

text\<open>Hier schlägt das Programmiererherz höher:
Wenn \<^typ>\<open>'person\<close> aufzählbar ist haben wir ausführbaren Code: @{thm teste_maxime_exhaust}
wobei @{const teste_maxime_exhaust} implementiert ist als @{thm teste_maxime_exhaust_def}.
\<close>

subsection\<open>Maximen Debugging\<close>
text\<open>Der folgende Datentyp modelliert ein Beispiel in welcher Konstellation eine gegebene
Maxime verletzt ist:\<close>
datatype 'person opfer = Opfer 'person
datatype 'person taeter = Taeter 'person
datatype ('person, 'world) verletzte_maxime = 
  VerletzteMaxime
    \<open>'person opfer\<close> \<comment>\<open>verletzt für; das Opfer\<close>
    \<open>'person taeter\<close> \<comment>\<open>handelnde Person; der Täter\<close>
    \<open>'world handlung\<close> \<comment>\<open>Die verletzende Handlung\<close>

text\<open>Die folgende Funktion liefert alle Gegebenheiten welche eine Maxime verletzen:\<close>
fun debug_maxime
  :: "('world \<Rightarrow> 'printable_world) \<Rightarrow> 'world \<Rightarrow>
      ('person, 'world) handlungF \<Rightarrow> ('person, 'world) maxime
      \<Rightarrow> (('person, 'printable_world) verletzte_maxime) set"
where
  "debug_maxime print_world welt handlungsabsicht (Maxime m) =
    {VerletzteMaxime
      (Opfer p1) (Taeter p2)
      (map_handlung print_world (handeln p2 welt handlungsabsicht)) | p1 p2.
          \<not>m p1 (handeln p2 welt handlungsabsicht)}"


text\<open>Es gibt genau dann keine Beispiele für Verletzungen, wenn die Maxime erfüllt ist:\<close>
lemma "debug_maxime print_world welt handlungsabsicht maxime = {}
        \<longleftrightarrow> teste_maxime welt handlungsabsicht maxime"
  apply(case_tac maxime, rename_tac m, simp)
  by(simp add: teste_maxime_unfold bevoelkerung_def)

(*<*)
definition debug_maxime_exhaust where
  \<open>debug_maxime_exhaust bevoelk print_world welt ha maxime \<equiv>
    (case maxime of (Maxime m) \<Rightarrow> 
      map (\<lambda>(p1,p2). VerletzteMaxime (Opfer p1) (Taeter p2) (map_handlung print_world (handeln p2 welt ha)))
        (filter (\<lambda>(p1,p2). \<not>m p1 (handeln p2 welt ha)) (List.product bevoelk bevoelk)))\<close>

lemma debug_maxime_exhaust [code]:
  \<open>debug_maxime print_world welt ha maxime
    = set (debug_maxime_exhaust enum_class.enum print_world welt ha maxime)\<close>
  apply(case_tac \<open>maxime\<close>, rename_tac m, simp)
  apply(simp add: debug_maxime_exhaust_def enum_UNIV)
  by(simp add: image_Collect)
(*>*)

subsection \<open>Beispiel\<close>
(*TODO: bekomme ich das irgendwie in einen eignenen namespace?*)

(*this causes
  fun teste_maxime _ _ _ = raise Fail "Kant.teste_maxime";
when we don't use teste_maxime_exhaust.
So when code fails with "Kant.teste_maxime", make sure the 'person implements enum.*)

text\<open>Beispiel:
Die Welt sei nur eine Zahl und die zu betrachtende Handlungsabsicht sei,
dass wir diese Zahl erhöhen.
Die Mir-ist-alles-Recht Maxime ist hier erfüllt:\<close>
lemma \<open>teste_maxime
            (42::nat)
            (HandlungF (\<lambda>(person::person) welt. welt + 1))
            maxime_mir_ist_alles_recht\<close> by eval

text\<open>Beispiel:
Die Welt ist modelliert als eine Abbildung von Person auf Besitz.
Die Maxime sagt, dass Leute immer mehr oder gleich viel wollen, aber nie etwas verlieren wollen.
In einer Welt in der keiner etwas hat, erfuellt die Handlung jemanden 3 zu geben die Maxime.
\<close>
lemma \<open>teste_maxime
            [Alice \<mapsto> (0::nat), Bob \<mapsto> 0, Carol \<mapsto> 0, Eve \<mapsto> 0]
            (HandlungF (\<lambda>person welt. welt(person \<mapsto> 3)))
            (Maxime (\<lambda>person handlung.
                (the ((vorher handlung) person)) \<le> (the ((nachher handlung) person))))\<close>
  by eval
lemma \<open>debug_maxime show_map
            [Alice \<mapsto> (0::nat), Bob \<mapsto> 0, Carol \<mapsto> 0, Eve \<mapsto> 0]
            (HandlungF (\<lambda>person welt. welt(person \<mapsto> 3)))
            (Maxime (\<lambda>person handlung.
                (the ((vorher handlung) person)) \<le> (the ((nachher handlung) person))))
  = {}\<close>
  by eval


text\<open>Wenn nun \<^const>\<open>Bob\<close> allerdings bereits 4 hat, würde die obige Handlung ein Verlust
für ihn bedeuten und die Maxime ist nicht erfüllt.\<close>
lemma \<open>\<not> teste_maxime
            [Alice \<mapsto> (0::nat), Bob \<mapsto> 4, Carol \<mapsto> 0, Eve \<mapsto> 0]
            (HandlungF (\<lambda>person welt. welt(person \<mapsto> 3)))
            (Maxime (\<lambda>person handlung.
                (the ((vorher handlung) person)) \<le> (the ((nachher handlung) person))))\<close>
  by eval
lemma \<open>debug_maxime show_map
            [Alice \<mapsto> (0::nat), Bob \<mapsto> 4, Carol \<mapsto> 0, Eve \<mapsto> 0]
            (HandlungF (\<lambda>person welt. welt(person \<mapsto> 3)))
            (Maxime (\<lambda>person handlung.
                (the ((vorher handlung) person)) \<le> (the ((nachher handlung) person))))
  = {VerletzteMaxime (Opfer Bob) (Taeter Bob)
     (Handlung [(Alice, 0), (Bob, 4), (Carol, 0), (Eve, 0)]
               [(Alice, 0), (Bob, 3), (Carol, 0), (Eve, 0)])}\<close>
  by eval




end
theory KategorischerImperativ
imports Maxime SchleierNichtwissen
begin

section\<open>Kategorischer Imperativ\<close>

text\<open>
Wir haben mit der goldenen Regel bereits definiert, 
wann für eine gegebene Welt und eine gegebene Maxime, eine Handlungsabsicht moralisch ist:

 \<^item> \<^term_type>\<open>moralisch :: 
     'world \<Rightarrow> ('person, 'world) maxime \<Rightarrow> ('person, 'world) handlungsabsicht \<Rightarrow> bool\<close>

Effektiv testet die goldene Regel eine Handlungsabsicht.

Nach meinem Verständnis generalisiert Kant mit dem Kategorischen Imperativ diese Regel,
indem die Maxime nicht mehr als gegeben angenommen wird,
sondern die Maxime selbst getestet wird.
Sei die Welt weiterhin gegeben,
dann müsste der kategorische Imperativ folgende Typsignatur haben:

  \<^item> \<^typ>\<open>'world \<Rightarrow> ('person, 'world) maxime \<Rightarrow> bool\<close>


Eine Implementierung muss dann über alle möglichen Handlungsabsichten allquantifizieren.

Grob gesagt: Die goldene Regel urteilt über eine Handlungsabsicht gegeben eine Maxime,
der kategorische Imperativ urteilt über die Maxime an sich.


Ich behaupte, der kategorischer Imperativ lässt sich wie folgt umformulieren:

  \<^item> Handle nur nach derjenigen Maxime, durch die du zugleich wollen kannst, 
    dass sie ein allgemeines Gesetz werde.
  \<^item> Handle nur nach derjenigen Maxime, durch die du zugleich wollen kannst,
    dass sie jeder befolgt, im Sinne der goldenen Regel.
  \<^item> Handle nur nach derjenigen Maxime, durch die du zugleich wollen kannst,
    dass sie (Handlung und Maxime) moralisch ist.
  \<^item> Wenn es jemanden gibt der nach einer Maxime handeln will,
    dann muss diese Handlung nach der Maxime moralisch sein.
  \<^item> Für jede Handlungsabsicht muss gelten:
    Wenn jemand einer Handlungsabsicht handeln würde (getestet durch die Maxime),
    dann muss diese Handlung moralisch sein (getestet durch die Maxime).

Daraus ergibt sich diese Formalisierung:

Für eine bestimmte Handlungsabsicht:
Wenn es eine Person gibt für die diese Handlungsabsicht moralisch ist,
dann muss diese Handlungsabsicht auch für alle moralisch (im Sinne der goldenen Regel) sein.
\<close>
definition kategorischer_imperativ_auf
  :: \<open>('person, 'world) handlungsabsicht \<Rightarrow> 'world \<Rightarrow> ('person, 'world) maxime \<Rightarrow> bool\<close>
where
  \<open>kategorischer_imperativ_auf ha welt m \<equiv>
     (\<exists>ich. ausfuehrbar ich welt ha \<and> okay m ich (handeln ich welt ha)) \<longrightarrow> moralisch welt m ha\<close>

text\<open>
Wir beschränken uns auf die \<^const>\<open>ausfuehrbar\<close>en Handlungsabsichten um pathologische
Grenzfälle (welche keinen Rückschluss auf moralische Gesinnung lassen) auszuschließen.


Für alle möglichen (wohlgeformten) Handlungsabsichten muss dies nun gelten:
\<close>
definition kategorischer_imperativ
  :: \<open>('person, 'world) wp_swap \<Rightarrow> 'world \<Rightarrow> ('person, 'world) maxime \<Rightarrow> bool\<close>
where
  \<open>kategorischer_imperativ wps welt m \<equiv>
    \<forall>ha. wohlgeformte_handlungsabsicht wps welt ha \<longrightarrow>
          kategorischer_imperativ_auf ha welt m\<close>

text\<open>Wir führen die interne Hilfsdefinition \<^const>\<open>kategorischer_imperativ_auf\<close> ein
um den kategorischen Imperativ nur für eine Teilmenge aller Handlungen besser
diskutieren zu können.

Leider fehlen mir nicht-triviale Beispiele von Maximen welche den kategorischen Imperativ uneingeschränkt
auf allen Handlungsabsichten erfüllen.
\<close>

text\<open>Die Vorbedingung \<^term>\<open>ausfuehrbar ich welt ha\<close> in \<^const>\<open>kategorischer_imperativ_auf\<close>
wirkt etwas holprig.
Wir brauchen sie aber, um pathologische Grenzfälle auszuschließen.
Beispielsweise ist von-sich-selbst stehlen eine (nicht ausführbare) No-Op.
No-ops sind normalerweise nicht böse.
Stehlen ist schon böse.
Dieser Grenzfall in dem Stehlen zur no-op wird versteckt also den Charakter der
Handlungsabsicht und muss daher ausgeschlossen werden.
Da Handlungen partiell sind, ist von-sich-selbst-stehlen auch also nicht ausführbar modelliert,
da Stehlen bedeutet "jemand anderen etwas wegnehmen" und im Grenzfall "von sich selbst stehlen"
nicht definiert ist.
\<close>


text\<open>In der Definition \<^const>\<open>kategorischer_imperativ\<close> ist \<^const>\<open>wohlgeformte_handlungsabsicht\<close>
ein technisch notwendiges Implementierungsdetail um nicht-wohlgeformte Handlungen
auszuschließen.\<close>


text\<open>Minimal andere Formulierung:\<close>
lemma
\<open>kategorischer_imperativ wps welt m \<longleftrightarrow>
  (\<forall>ha.
    (\<exists>p.
        wohlgeformte_handlungsabsicht wps welt ha \<and>
        ausfuehrbar p welt ha \<and>
        okay m p (handeln p welt ha))
    \<longrightarrow> moralisch welt m ha)\<close>
  unfolding kategorischer_imperativ_def kategorischer_imperativ_auf_def
  apply(simp)
  by blast

text\<open>Der Existenzquantor lässt sich auch in einen Allquantor umschreiben:\<close>
lemma
\<open>kategorischer_imperativ wps welt m \<longleftrightarrow>
  (\<forall>ha ich.
      wohlgeformte_handlungsabsicht wps welt ha \<and> ausfuehrbar ich welt ha \<and>
      okay m ich (handeln ich welt ha) \<longrightarrow> moralisch welt m ha)\<close>
  apply(simp add: kategorischer_imperativ_def kategorischer_imperativ_auf_def)
  by blast


text\<open>Vergleich zu \<^const>\<open>moralisch\<close>.
Wenn eine Handlung moralisch ist, dann impliziert diese Handlung die Kernforderung des
\<^const>\<open>kategorischer_imperativ\<close>.
Wenn die Handlungsabsicht für mich okay ist, ist sie auch für alle anderen okay.\<close>
lemma \<open>moralisch welt m ha \<Longrightarrow>
        kategorischer_imperativ_auf ha welt m\<close>
  by(simp add: moralisch_simp kategorischer_imperativ_auf_def)

text\<open>Die andere Richtung gilt nicht,
z.B. ist die Maxime die immer False zurückgibt ein Gegenbeispiel.\<close>
lemma \<open>m = Maxime (\<lambda>_ _. False) \<Longrightarrow>
        kategorischer_imperativ_auf ha welt m \<longrightarrow> moralisch welt m ha
          \<Longrightarrow> False\<close>
  by(simp add: kategorischer_imperativ_auf_def moralisch_simp)


text\<open>Der \<^const>\<open>kategorischer_imperativ\<close> lässt sich auch wie folgt umformulieren.
Für jede Handlungsabsicht:
  wenn ich so handeln würde muss es auch okay sein, wenn zwei beliebige
  Personen so handeln, wobei einer Täter und einer Opfer ist.\<close>
lemma kategorischer_imperativ_simp:
  \<open>kategorischer_imperativ wps welt m \<longleftrightarrow>
    (\<forall>ha p1 p2 ich.
      wohlgeformte_handlungsabsicht wps welt ha \<and> ausfuehrbar ich welt ha \<and>
      okay m ich (handeln ich welt ha)
      \<longrightarrow> okay m p1 (handeln p2 welt ha))\<close>
  apply(simp add: kategorischer_imperativ_def kategorischer_imperativ_auf_def moralisch_simp)
  by blast


(*<*)
text\<open>Introduction rules\<close>
lemma kategorischer_imperativI:
  \<open>(\<And>ha ich p1 p2. wohlgeformte_handlungsabsicht wps welt ha \<Longrightarrow>
                   ausfuehrbar ich welt ha \<Longrightarrow>
                   okay m ich (handeln ich welt ha) \<Longrightarrow> okay m p1 (handeln p2 welt ha)
                )
      \<Longrightarrow> kategorischer_imperativ wps welt m\<close>
  by(auto simp add: kategorischer_imperativ_simp)

lemma kategorischer_imperativ_aufI:
  \<open>(\<And>ich p1 p2. ausfuehrbar ich welt ha
      \<Longrightarrow> okay m ich (handeln ich welt ha) \<Longrightarrow> okay m p1 (handeln p2 welt ha))
      \<Longrightarrow> kategorischer_imperativ_auf ha welt m\<close>
  by(auto simp add: kategorischer_imperativ_auf_def moralisch_simp)
(*>*)


text\<open>Um den \<^const>\<open>kategorischer_imperativ_auf\<close> einer Handlungsabsicht zu zeigen muss
entweder die Handlungsabsicht moralisch sein,
oder es darf keine Person geben, die diese Handlung auch tatsächlich
unter gegebener Maxime ausführen würde:\<close>
lemma kategorischer_imperativ_auf2:
  \<open>moralisch welt m ha \<or> \<not>(\<exists> p. ausfuehrbar p welt ha \<and> okay m p (handeln p welt ha))
      \<longleftrightarrow> kategorischer_imperativ_auf ha welt m\<close>
  by(auto simp add: kategorischer_imperativ_auf_def moralisch_simp)


text\<open>Für Beispiele wird es einfacher zu zeigen, dass eine Maxime nicht den
kategorischen Imperativ erfüllt, wenn wir direkt ein Beispiel angeben.\<close>
(*insbesondere weil ich das proof document als outline baue und man den beweis,
also das Gegenbeispiel, nicht sieht.*)
definition \<open>kategorischer_imperativ_gegenbeispiel wps welt m ha ich p1 p2 \<equiv>
wohlgeformte_handlungsabsicht wps welt ha \<and> 
       ausfuehrbar ich welt ha \<and> okay m ich (handeln ich welt ha) \<and>
      \<not> okay m p1 (handeln p2 welt ha)\<close>

lemma \<open>kategorischer_imperativ_gegenbeispiel wps welt m ha ich p1 p2 \<Longrightarrow>
  \<not> kategorischer_imperativ wps welt m\<close>
  apply(simp add: kategorischer_imperativ_simp kategorischer_imperativ_gegenbeispiel_def)
  apply(rule_tac x=\<open>ha\<close> in exI, simp)
  by blast

subsection\<open>Triviale Maximen die den Kategorischen Imperativ immer Erfüllen\<close>
text\<open>
Die Maxime die keine Handlung erlaubt (weil immer False) erfüllt den kategorischen
Imperativ:\<close>
lemma \<open>kategorischer_imperativ wps welt (Maxime (\<lambda>ich h. False))\<close>
  by(simp add: kategorischer_imperativ_simp)

text\<open>Allerdings kann mit so einer Maxime nie etwas moralisch sein.\<close>
lemma \<open>\<not> moralisch welt (Maxime (\<lambda>ich h. False)) h\<close>
  by(simp add: moralisch_simp)

text\<open>Die Maxime die jede Handlung erlaubt (weil immer True) erfüllt den kategorischen
Imperativ:\<close>
lemma \<open>kategorischer_imperativ wps welt (Maxime (\<lambda>ich h. True))\<close>
  by(simp add: kategorischer_imperativ_simp)

text\<open>Allerdings ist mit so einer Maxime alles moralisch.\<close>
lemma \<open>moralisch welt (Maxime (\<lambda>ich h. True)) h\<close>
  by(simp add: moralisch_simp)



subsection\<open>Zusammenhang Goldene Regel\<close>
text\<open>
Mit der goldenen Regel konnten wir wie folgt moralische Entscheidungen treffen:
@{thm goldene_regel}

In Worten:
Wenn eine Handlungsabsicht moralisch ist (nach goldener Regel)
und es okay ist für mich diese Handlung auszuführen,
dann ist es auch für mich okay, wenn jeder andere diese Handlung mit mir als Opfer ausführt. 

Der kategorische Imperativ hebt diese eine Abstraktionsebene höher.
Wenn eine Maxime den kategorischen Imperativ erfüllt
und es okay ist für mich eine Handlung nach dieser Maxime auszuführen (wie in der goldenen Regel),
dann ist diese Handlungsabsicht allgemein moralisch.
Die goldene Regel konnte nur folgern, dass eine Handlungsabsicht auch okay ist wenn ich das
Opfer wäre, der kategorisch Imperativ schließt, dass eine Handlungsabsicht allgemein moralisch
sein muss, wobei beliebige Personen (nicht nur ich) Täter und Opfer sein können.
\<close>

lemma \<open>kategorischer_imperativ wps welt m \<Longrightarrow>
  wohlgeformte_handlungsabsicht wps welt ha \<Longrightarrow>
   ausfuehrbar ich welt ha \<Longrightarrow>
  okay m ich (handeln ich welt ha) \<Longrightarrow> moralisch welt m ha\<close>
  by(auto simp add: kategorischer_imperativ_simp moralisch_simp)
  

text\<open>
In Worten:
Wenn eine Maxime den kategorischen Imperativ erfüllt
und es für eine beliebige (wohlgeformte) Handlung auszuführen für mich okay ist diese auszuführen,
dann ist diese Handlung moralisch..
\<close>



subsection\<open>Maximen die den Kategorischen Imperativ immer Erfüllen\<close>

text\<open>Wenn eine Maxime jede Handlungsabsicht als moralisch bewertet,
erfüllt diese Maxime den kategorischen Imperativ.
Da diese Maxime jede Handlung erlaubt, ist es dennoch eine wohl ungeeignete Maxime.\<close>
lemma \<open>\<forall>ha. moralisch welt maxime ha \<Longrightarrow> kategorischer_imperativ wps welt maxime\<close>
  apply(cases \<open>maxime\<close>, rename_tac m)
  by(simp add: kategorischer_imperativ_simp moralisch_simp)


text\<open>Eine Maxime die das ich und die Handlung ignoriert erfüllt den kategorischen Imperativ.\<close>
lemma blinde_maxime_katimp:
  \<open>kategorischer_imperativ wps welt (Maxime (\<lambda>ich h. m))\<close>
  apply(rule kategorischer_imperativI)
  by(simp)


text\<open>Eine Maxime welche das \<^term>\<open>ich::'person\<close> ignoriert,
also nur die Handlung global betrachtet, erfüllt den kategorischen Imperativ
(mit einigen weiteren Annahmen).\<close>
theorem globale_maxime_katimp:
  fixes P :: \<open>'world handlung \<Rightarrow> bool\<close>
  assumes mhg: \<open>\<forall>p. maxime_und_handlungsabsicht_generalisieren wps welt (Maxime (\<lambda>ich::'person. P)) ha p\<close>
    and maxime_erlaubt_untaetigkeit: \<open>\<forall>p. ist_noop (handeln p welt ha) \<longrightarrow> okay (Maxime (\<lambda>ich::'person. P)) p (handeln p welt ha)\<close>
    and kom: \<open>wpsm_kommutiert (Maxime (\<lambda>ich::'person. P)) wps welt\<close>
    and wps_sym:
    \<open>\<forall>p1 p2 welt. wps p1 p2 welt = wps p2 p1 welt\<close>
    and wps_id:
    \<open>\<forall>p1 p2 welt. wps p1 p2 (wps p1 p2 welt) = welt\<close>
    and wfh: \<open>wohlgeformte_handlungsabsicht wps welt ha\<close>
  shows \<open>kategorischer_imperativ_auf ha welt (Maxime (\<lambda>ich::'person. P))\<close>
proof(rule kategorischer_imperativ_aufI, simp)
  fix ich p2 :: \<open>'person\<close>
  assume ausfuehrbarich: \<open>ausfuehrbar ich welt ha\<close>
    and okayich: \<open>P (handeln ich welt ha)\<close>

  from wps_id wps_sym have wpsid_swapped: \<open>wps_id wps welt\<close>
    by(simp add: wps_id_def)

  obtain h where h: \<open>ha = Handlungsabsicht h\<close>
    by(cases \<open>ha\<close>, blast)

  show \<open>P (handeln p2 welt ha)\<close>
  proof(cases \<open>\<not> ausfuehrbar p2 welt ha\<close>)
    case True
    assume \<open>\<not> ausfuehrbar p2 welt ha\<close>
    hence \<open>ist_noop (handeln p2 welt ha)\<close> using nicht_ausfuehrbar_ist_noop by fast
    with maxime_erlaubt_untaetigkeit show \<open>P (handeln p2 welt ha)\<close> by simp
  next
    case False
    assume \<open>\<not> \<not> ausfuehrbar p2 welt ha\<close>
    with wohlgeformte_handlungsabsicht_ausfuehrbar[OF wfh]
    have mhg_pre: \<open>ausfuehrbar ich (wps p2 ich welt) (Handlungsabsicht h)\<close> using h by blast

    from ausfuehrbarich mhg_pre[simplified h] mhg[simplified maxime_und_handlungsabsicht_generalisieren_def h] okayich[simplified h]
    have
      \<open>P (handeln ich (wps p2 ich welt) ha)\<close>
      by(auto simp add: h)
    with wps_sym have
      \<open>P (handeln ich (wps ich p2 welt) ha)\<close>
      by(simp)
    with wfh_wpsm_kommutiert_simp[OF wpsid_swapped wfh kom] show \<open>P (handeln p2 welt ha)\<close>
      by(simp add: h)
  qed
qed


subsection\<open>Ausführbarer Beispielgenerator\<close>
text\<open>Gegeben sei eine Welt, sowie eine Maxime, und eine Liste von Handlungsabsichten.
Wir wollen nun wissen ob die Maxime und Handlungsabsichten wohlgeformt sind,
und wenn ja, ob die Maxime auf diesen Handlungsabsichten den kategorischen Imperativ erfüllt,
und wie die Handlungen bewertet werden.\<close>

(*<*)
value\<open>[(x,y). x \<leftarrow> xs, y \<leftarrow> ys, x \<noteq> y]\<close>
(*>*)

definition alle_moeglichen_handlungen
  :: \<open>'world \<Rightarrow> ('person::enum, 'world) handlungsabsicht list \<Rightarrow> 'world handlung list\<close>
where
  \<open>alle_moeglichen_handlungen welt has \<equiv> [handeln p welt ha. ha \<leftarrow> has, p \<leftarrow> (Enum.enum::'person list)]\<close>

lemma set_alle_moeglichen_handlungen:
  \<open>set (alle_moeglichen_handlungen welt has) = {handeln p welt ha | ha p. ha\<in>set has}\<close>
  apply(simp add: alle_moeglichen_handlungen_def)
  apply(simp add: enum_class.enum_UNIV)
  by blast

(*Um den Namespace nicht zu verschmutzen prefixe ich alles mit bsp_*)
record ('person, 'world) beipiel =
  bsp_welt :: \<open>'world\<close>
  bsp_erfuellte_maxime :: \<open>('person, 'world) maxime option\<close>
  bsp_erlaubte_handlungen :: \<open>('person, 'world) handlungsabsicht list\<close>
  bsp_verbotene_handlungen :: \<open>('person, 'world) handlungsabsicht list\<close>


definition erzeuge_beispiel
  :: \<open>('person::enum, 'world) wp_swap \<Rightarrow> 'world \<Rightarrow>
      ('person, 'world) handlungsabsicht list \<Rightarrow> ('person, 'world) maxime
      \<Rightarrow> ('person, 'world) beipiel option\<close>
  where
\<open>erzeuge_beispiel wps welt has m \<equiv>
  if (\<exists>h\<in>set (alle_moeglichen_handlungen welt has). \<not>wohlgeformte_maxime_auf h wps m)
     \<or> (\<exists>ha\<in>set has. \<not> wohlgeformte_handlungsabsicht wps welt ha)
  then None
  else Some
   \<lparr> bsp_welt = welt,
     bsp_erfuellte_maxime = if \<forall>ha\<in>set has. kategorischer_imperativ_auf ha welt m then Some m else None,
     bsp_erlaubte_handlungen = [ha\<leftarrow>has. moralisch welt m ha],
     bsp_verbotene_handlungen = [ha\<leftarrow>has. \<not> moralisch welt m ha]
   \<rparr>\<close>

text\<open>
Das Ergebnis von \<^const>\<open>erzeuge_beispiel\<close> ließt sich wie folgt.
  \<^item> Wenn \<^const>\<open>bsp_erfuellte_maxime\<close> einen \<^const>\<open>Some\<close> term enthält ist der
    \<^const>\<open>kategorischer_imperativ_auf\<close> den Handlungen erfüllt
  \<^item> Die \<^const>\<open>bsp_erlaubte_handlungen\<close> und \<^const>\<open>bsp_verbotene_handlungen\<close> entspricht
    quasi dem allgemeinen Gesetz, welches besagt, welche Handlungen erlaubt oder verboten sind.
\<close>

text\<open>\<^const>\<open>erzeuge_beispiel\<close> erzeugt nur ein Beiespiel wenn alles wohlgeformt ist.\<close>
lemma \<open>erzeuge_beispiel wps welt has m = Some bsp \<Longrightarrow>
  (\<forall> ha \<in> set has. wohlgeformte_handlungsabsicht wps welt ha) \<and>
  (\<forall> h \<in> set (alle_moeglichen_handlungen welt has). wohlgeformte_maxime_auf h wps m)\<close>
  by(simp add: erzeuge_beispiel_def split: if_split_asm)

(*<*)
(*thx lars: https://stackoverflow.com/questions/74337244/turning-a-valuesimp-example-into-a-lemma-with-functions-in-them/74394525#74394525*)
ML\<open>
fun beispiel_conv ctxt =
  Conv.arg_conv (Conv.arg1_conv (Code_Simp.dynamic_conv ctxt) then_conv Conv.arg_conv (Code_Simp.dynamic_conv ctxt))

fun beispiel_tac ctxt =
  HEADGOAL (CONVERSION (beispiel_conv ctxt) THEN_ALL_NEW (resolve_tac ctxt @{thms refl}))
\<close>

method_setup beispiel = \<open>Scan.succeed (SIMPLE_METHOD o beispiel_tac)\<close>
(*>*)

lemma\<open>erzeuge_beispiel swap (\<lambda>p::person. 0::int) [Handlungsabsicht (\<lambda>p w. Some w)] (Maxime (\<lambda>ich w. True))
  =
  Some
  \<lparr>bsp_welt = (\<lambda>p::person. 0::int),
   bsp_erfuellte_maxime = Some (Maxime (\<lambda>ich w. True)),
   bsp_erlaubte_handlungen = [Handlungsabsicht (\<lambda>p w. Some w)],
   bsp_verbotene_handlungen = []
  \<rparr>\<close>
  by beispiel

text\<open>Der Nachteil von \<^const>\<open>erzeuge_beispiel\<close> ist,
dass der resultierende Record viele Funktionen enthält,
welche eigentlich nicht geprintet werden können.
Allerdings ist dies vermutlich die einzige (sinnvolle, einfache) Art eine Handlungsabsicht 
darzustellen.

Es wäre einfacher, nur die Handlung (also die \<^typ>\<open>'world handlung\<close>,
nur die Welt vorher und nachher, ohne Absicht) aufzuschreiben.
Allerdings erzeugt das ohne die Absicht (i.e. \<^typ>\<open> ('person, 'world) handlungsabsicht\<close>)
sehr viel Unfug, da z.B. pathologische Grenzfälle
(wie z.B. sich-selsbt-bestehlen, oder die-welt-die-zufällig-im-ausgangszustand-ist-resetten)
dazu, dass diese no-op Handlungen verboten sind, da die dahinterliegende Absicht schlecht ist.
Wenn wir allerdings nur die Ergebnisse einer solchen Handlung (ohne die Absicht) aufschreiben
kommt heraus: Nichtstun ist verboten.

Glücklicherweise hat Lars uns 4 Zeilen ML geschrieben, welche \<^const>\<open>erzeuge_beispiel\<close> als
ausführbares Beispiel benutzbar macht und dabei es auch erlaubt die Funktionen richtig
zu printen, solange diese einen Namen haben.\<close>





subsection\<open>Kombination vom Maximen\<close>
text\<open>Die folgenden Lemmata über Konjunktion, Disjunktion, und Negation von Maximen werden
leider etwas kompliziert.
Wir führen eine Hilfsdefinition ein, welche besagt, ob es einen Fall gibt
in dem die Handlungsabsicht tatsächlich ausführbar ist und die Maxime erfüllt.
Dabei werden gezielt die pathologischen Grenzfälle ausgeklammert,
in denen die Handlungsabsicht nicht ausführbar ist und in einer No-Op resultieren würde.\<close>
(*TODO: in die kat imp definition folden!*)
definition ex_erfuellbare_instanz
  :: \<open>('person, 'world) maxime \<Rightarrow> 'world \<Rightarrow> ('person, 'world) handlungsabsicht \<Rightarrow> bool\<close>
where
  \<open>ex_erfuellbare_instanz m welt ha \<equiv>
      \<exists>ich. ausfuehrbar ich welt ha \<and> okay m ich (handeln ich welt ha)\<close>


subsubsection\<open>Konjunktion\<close>

lemma MaximeConjI:
  \<open>kategorischer_imperativ_auf ha welt m1 \<and> kategorischer_imperativ_auf ha welt m2 \<Longrightarrow>
  kategorischer_imperativ_auf ha welt (MaximeConj m1 m2)\<close>
  apply(cases \<open>m1\<close>, cases \<open>m2\<close>, simp)
  apply(simp add: kategorischer_imperativ_auf_def moralisch_simp okay_MaximeConj)
  apply blast
  done

text\<open>Die Rückrichtung gilt nur, wenn wir annehmen, dass es auch einen Fall gibt
in dem die \<^const>\<open>MaximeConj\<close> auch erfüllbar ist:\<close>
lemma MaximeConjD:
  \<open>ex_erfuellbare_instanz (MaximeConj m1 m2) welt ha \<Longrightarrow>
    kategorischer_imperativ_auf ha welt (MaximeConj m1 m2) \<Longrightarrow>
    kategorischer_imperativ_auf ha welt m1 \<and> kategorischer_imperativ_auf ha welt m2\<close>
  apply(simp add: ex_erfuellbare_instanz_def kategorischer_imperativ_auf_def)
  apply(simp add: moralisch_MaximeConj)
  done

text\<open>Wenn wir \<^const>\<open>ex_erfuellbare_instanz\<close> annehmen, dann verhält sich \<^const>\<open>MaximeConj\<close>
im \<^const>\<open>kategorischer_imperativ_auf\<close> wie eine normale Konjunktion.\<close>
lemma MaximeConj:
  \<open>ex_erfuellbare_instanz (MaximeConj m1 m2) welt ha \<Longrightarrow>
    kategorischer_imperativ_auf ha welt (MaximeConj m1 m2) \<longleftrightarrow>
    kategorischer_imperativ_auf ha welt m1 \<and> kategorischer_imperativ_auf ha welt m2\<close>
  using MaximeConjI MaximeConjD by metis

lemma kategorischer_imperativ_auf_MaximeConj_comm:
  \<open>kategorischer_imperativ_auf ha welt (MaximeConj m1 m2)
   \<longleftrightarrow> kategorischer_imperativ_auf ha welt (MaximeConj m2 m1)\<close>
  by(auto simp add: kategorischer_imperativ_auf_def moralisch_simp okay_MaximeConj)

lemma kategorischer_imperativ_auf_MaximeConj_True:
  \<open>kategorischer_imperativ_auf ha welt (MaximeConj m1 (Maxime (\<lambda>_ _. True)))
  \<longleftrightarrow> kategorischer_imperativ_auf ha welt m1\<close>
  by(simp add: kategorischer_imperativ_auf_def moralisch_simp okay_MaximeConj)

text\<open>Achtung: Folgendes lemma ist das Gegenteil, was man von einer Konjunktion erwarten würde.
Normalerweise ist \<^term>\<open>a \<and> False = False\<close>.
Bei \<^const>\<open>MaximeConj\<close> ist dies aber \<^const>\<open>True\<close>!
Dies liegt daran, dass \<^term>\<open>Maxime (\<lambda>_ _. False)\<close> keine Handlung erlaubt,
und damit als pathologischen Grenzfall den kategorischen Imperativ erfüllt.\<close>
lemma kategorischer_imperativ_auf_MaximeConj_False:
  \<open>kategorischer_imperativ_auf ha welt (MaximeConj m1 (Maxime (\<lambda>_ _. False)))\<close>
  by(simp add: kategorischer_imperativ_auf_def moralisch_simp okay_MaximeConj)


subsubsection\<open>Disjunktion\<close>

text\<open>Für \<^const>\<open>MaximeDisj\<close> müssen wir generell annehmen,
dass einer der Fälle erfüllbar ist.\<close>
lemma kategorischer_imperativ_auf_MaximeDisjI:
\<open>(ex_erfuellbare_instanz m1 welt ha \<and> kategorischer_imperativ_auf ha welt m1) \<or>
 (ex_erfuellbare_instanz m2 welt ha \<and> kategorischer_imperativ_auf ha welt m2) \<Longrightarrow>
  kategorischer_imperativ_auf ha welt (MaximeDisj m1 m2)\<close>
  apply(simp add: ex_erfuellbare_instanz_def kategorischer_imperativ_auf_def okay_MaximeDisj)
  apply(erule disjE)
  apply (metis moralisch_MaximeDisjI)+
  done
text\<open>Die Rückrichtung gilt leider nicht.\<close>

text\<open>Die Annahmen sind leider sehr stark:\<close>
lemma
  \<open>ex_erfuellbare_instanz m welt ha \<and> kategorischer_imperativ_auf ha welt m
  \<Longrightarrow>
  moralisch welt m ha\<close>
  by (simp add: ex_erfuellbare_instanz_def kategorischer_imperativ_auf_def)


text\<open>Wenn wir die Annahme stärker machen gilt auch folgendes:\<close>
lemma kategorischer_imperativ_auf_MaximeDisjI_from_conj:
  \<open>kategorischer_imperativ_auf ha welt m1 \<and> kategorischer_imperativ_auf ha welt m2 \<Longrightarrow>
  kategorischer_imperativ_auf ha welt (MaximeDisj m1 m2)\<close>
  apply(simp add: kategorischer_imperativ_auf_def moralisch_simp okay_MaximeDisj)
  by blast


text\<open>Als Introduction rule eignet sich vermutlich folgendes besser,
weil es auch erlaubt,
dass eine Handlungsabsicht nicht ausführbar ist oder von keiner Maxime erfüllbar ist.\<close>
lemma kategorischer_imperativ_auf_MaximeDisjI2:
\<open>(ex_erfuellbare_instanz m1 welt ha \<and> kategorischer_imperativ_auf ha welt m1) \<or>
 (ex_erfuellbare_instanz m2 welt ha \<and> kategorischer_imperativ_auf ha welt m2) \<or>
 (\<not> ex_erfuellbare_instanz (MaximeDisj m1 m2) welt ha)
\<Longrightarrow>
  kategorischer_imperativ_auf ha welt (MaximeDisj m1 m2)\<close>
  apply(simp add: ex_erfuellbare_instanz_def kategorischer_imperativ_auf_def okay_MaximeDisj)
  apply(elim disjE)
    apply (metis moralisch_MaximeDisjI)
   apply (metis moralisch_MaximeDisjI)
   apply blast
  done
text\<open>Die vorherige Introduction Rule lässt sich wie folgt erklären.
Mindestens eine der \<^const>\<open>ex_erfuellbare_instanz\<close>Fälle muss immer zutreffen:\<close>
lemma
  \<open>ex_erfuellbare_instanz m1 welt ha \<or>
   ex_erfuellbare_instanz m2 welt ha \<or>
   \<not> ex_erfuellbare_instanz (MaximeDisj m1 m2) welt ha\<close>
  by(auto simp add: ex_erfuellbare_instanz_def okay_MaximeDisj)
text\<open>Wenn wir also mental den \<^const>\<open>ex_erfuellbare_instanz\<close> Teil ausblenden,
dann liest sich obige Introduction Rule wie folgt:
\<^term>\<open>kategorischer_imperativ_auf ha welt m1 \<or> kategorischer_imperativ_auf ha welt m2
\<Longrightarrow> kategorischer_imperativ_auf ha welt (MaximeDisj m1 m2)\<close>.
Dies ist genau die Disjunktions Introduction Rule die ich gerne hätte.
Die gesamte Regel ist leider leicht komplizierter,
da der entsprechende Oder-Fall immer mit dem entsprechenden \<^const>\<open>ex_erfuellbare_instanz\<close>
gepaart auftreten muss.
\<close>

text\<open>Eine gewöhnliche Introduction Rule (ohne die \<^const>\<open>ex_erfuellbare_instanz\<close> Teile)
gilt leider nicht.\<close>
lemma
  \<open>ha = Handlungsabsicht (\<lambda>p w. Some w) \<Longrightarrow>
   m1 = Maxime ((\<lambda>p h. False)(Bob := \<lambda>h. True)) \<Longrightarrow>
   welt = (0::int) \<Longrightarrow>
kategorischer_imperativ_auf ha welt m1 \<Longrightarrow>
  \<not> kategorischer_imperativ_auf ha welt (MaximeDisj m1 m2)\<close>
  apply(simp)
  apply(thin_tac \<open>_ = _\<close>)+
  apply(code_simp)
  done

text\<open>Zumindest gelten folgende Regeln welche einer gewöhnlichen Disjuntions Introduction
ähnlich sehen (mit leicht stärkeren Annahmen):\<close>
lemma
\<open>(ex_erfuellbare_instanz m1 welt ha \<and> kategorischer_imperativ_auf ha welt m1)
  \<Longrightarrow> kategorischer_imperativ_auf ha welt (MaximeDisj m1 m2)\<close>
\<open>moralisch welt m1 ha
  \<Longrightarrow> kategorischer_imperativ_auf ha welt (MaximeDisj m1 m2)\<close>
   apply (meson kategorischer_imperativ_auf_MaximeDisjI2)
  by (simp add: kategorischer_imperativ_auf_def moralisch_MaximeDisj1 kategorischer_imperativ_auf_MaximeDisjI2)


lemma moralisch_kategorischer_imperativ_auf_MaximeDisjI:
  \<open>moralisch welt m1 ha \<Longrightarrow>
  kategorischer_imperativ_auf ha welt (MaximeDisj m1 m2)\<close>
  by(simp add: kategorischer_imperativ_auf_def moralisch_simp okay_MaximeDisj)

lemma kategorischer_imperativ_auf_MaximeDisj_comm:
  \<open>kategorischer_imperativ_auf ha welt (MaximeDisj m1 m2)
   \<longleftrightarrow> kategorischer_imperativ_auf ha welt (MaximeDisj m2 m1)\<close>
  by(auto simp add: kategorischer_imperativ_auf_def moralisch_simp okay_MaximeDisj)





text\<open>Für die Grenzfälle einer Disjunktion mit \<^const>\<open>True\<close> und \<^const>\<open>False\<close>
verhält sich \<^const>\<open>MaximeDisj\<close> wie erwartet.\<close>
lemma kategorischer_imperativ_auf_MaximeDisj_True:
  \<open>kategorischer_imperativ_auf ha welt (MaximeDisj m1 (Maxime (\<lambda>_ _. True)))\<close>
  by(simp add: kategorischer_imperativ_auf_def moralisch_simp okay_MaximeDisj)
lemma kategorischer_imperativ_auf_MaximeDisj_False:
  \<open>kategorischer_imperativ_auf ha welt (MaximeDisj m1 (Maxime (\<lambda>_ _. False)))
  \<longleftrightarrow> kategorischer_imperativ_auf ha welt m1\<close>
  by(simp add: kategorischer_imperativ_auf_def moralisch_simp okay_MaximeDisj)



text\<open>Die Negation verhält sich wie erwartet.\<close>
lemma kategorischer_imperativ_auf_Maxime_DeMorgan:
\<open>kategorischer_imperativ_auf ha welt (MaximeNot (MaximeConj m1 m2))
  \<longleftrightarrow>
  kategorischer_imperativ_auf ha welt (MaximeDisj (MaximeNot m1) (MaximeNot m2))\<close>
  by (simp add: kategorischer_imperativ_auf_def moralisch_DeMorgan okay_DeMorgan)

lemma kategorischer_imperativ_auf_MaximeNot_double:
  \<open>kategorischer_imperativ_auf ha welt (MaximeNot (MaximeNot m))
    \<longleftrightarrow> kategorischer_imperativ_auf ha welt m\<close>
  by(simp add: kategorischer_imperativ_auf_def moralisch_simp okay_MaximeNot)



end
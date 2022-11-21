theory KategorischerImperativ
imports Maxime SchleierNichtwissen
begin

section\<open>Kategorischer Imperativ\<close>

text\<open>
Wir haben mit der goldenen Regel bereits definiert, 
wann für eine gegebene Welt und eine gegebene maxime, eine Handlungsabsicht moralisch ist:

 \<^item> \<^term_type>\<open>moralisch :: 
     'world \<Rightarrow> ('person, 'world) maxime \<Rightarrow> ('person, 'world) handlungsabsicht \<Rightarrow> bool\<close>

Effektiv testet die goldene Regel eine Handlungsabsicht.

Nach meinem Verständnis generalisiert Kant mit dem Kategorischen Imperativ diese Regel,
indem die Maxime nicht mehr als gegeben angenommen wird,
sondern die Maxime selbst getestet wird.
Sei die Welt weiterhin gegeben,
dass müsste der kategorische Imperativ folgende Typsignatur haben:

  \<^item> \<^typ>\<open>'world \<Rightarrow> ('person, 'world) maxime \<Rightarrow> bool\<close>

Eine Implementierung muss dann über alle möglichen Handlungsabsichten allquantifizieren.


Ich behaupte, der kategorischer Imperativ lässt sich wie folgt umformulieren:

  \<^item> Handle nur nach derjenigen Maxime, durch die du zugleich wollen kannst, 
    dass sie ein allgemeines Gesetz werde.
  \<^item> Handle nur nach derjenigen Maxime, durch die du zugleich wollen kannst,
    dass sie jeder befolgt, im Sinne der goldenen Regel.
  \<^item> Handle nur nach derjenigen Maxime, durch die du zugleich wollen kannst,
    dass sie (Handlung+Maxime) moralisch ist.
  \<^item> Wenn es jemanden gibt der nach einer Maxime handeln will,
    dann muss diese Handlung nach der Maxime moralisch sein.
  \<^item> Für jede Handlungsabsicht muss gelten:
    Wenn jemand in jeder Welt nach der Handlungsabsicht handeln würde,
    dann muss diese Handlung moralisch sein.

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

TODO: Leider fehlen mir Beispiele von Maximen welche den kategorischen Imperativ uneingeschränkt
auf allen Handlungsabsichten erfüllen.
\<close>

text\<open>Diese \<^term>\<open>\<not>ist_noop (handeln ich welt h)\<close> gefällt mir gar nicht.
Wir brauchen es aber, damit die Beispiele funktionieren.
Das ist nötig, um pathologische Grenzfälle auszuschließen.
Beispielsweise ist von-sich-selbst stehlen eine no-op.
No-ops sind normalerweise nicht böse.
Stehlen ist schon böse.
Dieser Grenzfall in dem Stehlen zur no-op wird versteckt also den Charakter der
Handlungsabsicht und muss daher ausgeschlossen werden.
Ganz glücklich bin ich mit der Rechtfertigung aber nicht.
Eventuell wäre es schöner, Handlungen partiell zu machen,
also dass Handlungsabsichten auch mal \<^const>\<open>None\<close> zurückgeben dürfen.
Das könnte einiges rechtfertigen.
Beispielsweise ist Stehlen: jemand anderen etwas wegnehmen.
Nicht von sich selbst.
Allerdings machen partielle Handlungen alles komplizierter.
\<close>


text\<open>In der Definition is \<^const>\<open>wohlgeformte_handlungsabsicht\<close>
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
Wenn die Handlungsabsicht für mich okaz ist, ist sie auch für alle anderen okay.\<close>
lemma \<open>moralisch welt m ha \<Longrightarrow>
        kategorischer_imperativ_auf ha welt m\<close>
  by(simp add: moralisch_simp kategorischer_imperativ_auf_def)

text\<open>Die andere Richtung gilt nicht,
z.B. ist die Maxime die immer False zurückgibt ein Gegenbeispiel.\<close>
lemma \<open>m = Maxime (\<lambda>_ _. False) \<Longrightarrow>
        kategorischer_imperativ_auf ha welt m \<longrightarrow> moralisch welt m ha
          \<Longrightarrow> False\<close>
  by(simp add: kategorischer_imperativ_auf_def moralisch_simp)


text\<open>Für jede Handlungsabsicht:
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


text\<open>Introduction rules\<close>
lemma kategorischer_imperativI:
  \<open>(\<And>ha ich p1 p2. wohlgeformte_handlungsabsicht wps welt ha \<Longrightarrow>
                   ausfuehrbar ich welt ha \<Longrightarrow>
                   okay m ich (handeln ich welt ha) \<Longrightarrow> okay m p1 (handeln p2 welt ha)
                )
      \<Longrightarrow> kategorischer_imperativ wps welt m\<close>
  by(auto simp add: kategorischer_imperativ_simp)

(**TODO: handlungsabsicht ha und h konsitent verwenden**)

lemma kategorischer_imperativ_aufI:
  \<open>(\<And>ich p1 p2. ausfuehrbar ich welt ha
      \<Longrightarrow> okay m ich (handeln ich welt ha) \<Longrightarrow> okay m p1 (handeln p2 welt ha))
      \<Longrightarrow> kategorischer_imperativ_auf ha welt m\<close>
  by(auto simp add: kategorischer_imperativ_auf_def moralisch_simp)


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

text\<open>Allerdings ist mot so einer Maxime alles moralisch.\<close>
lemma \<open>moralisch welt (Maxime (\<lambda>ich h. True)) h\<close>
  by(simp add: moralisch_simp)



subsection\<open>Zusammenhang Goldene Regel\<close>
text\<open>
Mit der goldenen Regel konnten wir wie folgt moralische Entscheidungen treffen:
@{thm goldene_regel}

In Worten:
Wenn eine Handlungsabsicht moralisch ist (nach goldener Regel)
und es okay ist für mich diese Handlung auszuführen,
denn ist es auch für mich okay, wenn jeder andere diese Handlung mit mir als Opfer ausführt. 

Der kategorische Imperativ liftet dies eine Abstraktionsebene:
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
also nur die Handlung global betrachtet, erfüllt den kategorischen Imperativ.\<close>
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

  from wps_id wps_sym have wpsid_swapped: "wps_id wps welt"
    by(simp add: wps_id_def)

  obtain h where h: \<open>ha = Handlungsabsicht h\<close>
    by(cases \<open>ha\<close>, blast)

  show \<open>P (handeln p2 welt ha)\<close>
  proof(cases \<open>\<not> ausfuehrbar p2 welt ha\<close>)
    case True
    assume \<open>\<not> ausfuehrbar p2 welt ha\<close>
    hence "ist_noop (handeln p2 welt ha)" using nicht_ausfuehrbar_ist_noop by fast
    with maxime_erlaubt_untaetigkeit show \<open>P (handeln p2 welt ha)\<close> by simp
  next
    case False
    assume \<open>\<not> \<not> ausfuehrbar p2 welt ha\<close>
    with wohlgeformte_handlungsabsicht_ausfuehrbar[OF wfh]
    have mhg_pre: "ausfuehrbar ich (wps p2 ich welt) (Handlungsabsicht h)" using h by blast

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

(*
text\<open>Eine Maxime die das ich ignoriert und etwas für alle fordert erfüllt den
kategorischen Imperativ.\<close>
theorem altruistische_maxime_katimp:
  fixes P :: \<open>'person \<Rightarrow> 'world handlung \<Rightarrow> bool\<close>
  assumes kom: \<open>wpsm_kommutiert (Maxime P) wps welt\<close>
      and unrel1: \<open>wpsm_unbeteiligt1 (Maxime P) wps welt\<close>
      and unrel2: \<open>wpsm_unbeteiligt2 (Maxime P) wps welt\<close>
      and wps_sym:
        \<open>\<forall>p1 p2 welt. wps p1 p2 welt = wps p2 p1 welt\<close>
  shows \<open>kategorischer_imperativ wps welt (Maxime (\<lambda>ich h. (\<forall>pX. P pX h)))\<close>
proof(rule kategorischer_imperativI, simp, intro allI)
  fix ha :: \<open>('person, 'world) handlungsabsicht\<close>
  and p1 p2 p :: \<open>'person\<close>
  assume wfh: \<open>wohlgeformte_handlungsabsicht wps welt ha\<close>
     and mhg: \<open>maxime_und_handlungsabsicht_generalisieren2 wps (Maxime (\<lambda>ich h. \<forall>pX. P pX h)) ha\<close>
     and okayp: \<open>\<forall>pX. P pX (handeln p welt ha)\<close>

  obtain h where h: \<open>ha = Handlungsabsicht h\<close>
    by(cases \<open>ha\<close>, blast)

  from wfh[simplified wohlgeformte_handlungsabsicht_def h]
  have 1: \<open>h p2 welt = wps p p2 (h p (wps p2 p welt))\<close>
    by simp

  from wfh[simplified wohlgeformte_handlungsabsicht_def h] okayp
  have WTF: "\<forall>pX. P pX (Handlung welt (wps p p2 (h p2 (wps p p2 welt))))"
      (*WTF? ?*)
      by (metis h handeln.simps handlung.map_sel(2) nachher_handeln  wps_sym)


  from mhg[simplified maxime_und_handlungsabsicht_generalisieren2_def h, simplified] okayp[simplified h, simplified]
    have XXX: "\<forall>pX. P pX (Handlung (wps p p2 welt) (h p2 (wps p p2 welt)))"
      by simp (*uffff, das hat mir metis oben schon auch ohne mhg gebaut*)
  hence "(\<forall>pX. P pX (handeln p2 (wps p p2 welt) ha))"
    by(simp add: h)
  thm XXX kom[simplified wpsm_kommutiert_def okay.simps]
  
  
  from mhg[simplified maxime_und_handlungsabsicht_generalisieren2_def] okayp[simplified h]
  have 2:
  \<open>\<forall>pX. P pX (handeln p (wps p2 p welt) ha)\<close>
    apply(simp)
    apply(simp add: h)
    sorry (*keine ahnung ob das was wird :( *)
  from 2
  have 4:
    \<open>P p (handeln p (wps p2 p welt) ha)\<close>
    by(simp)

  show \<open>P p1 (handeln p2 welt ha)\<close>
  proof(cases \<open>p = p2\<close>)
    case True
    then show \<open>?thesis\<close>
      using okayp by auto 
  next
    case False
    assume \<open>p \<noteq> p2\<close>
    then show \<open>?thesis\<close>
    proof(cases \<open>p1 = p\<close>)
      case True
      assume \<open>p1 = p\<close>
      with 4[simplified handeln.simps h] kom[simplified wpsm_kommutiert_def okay.simps] show \<open>?thesis\<close>
        apply(simp add: h 1)
        using 2[simplified handeln.simps h] wps_sym by fastforce
    next
      case False
      assume \<open>p1 \<noteq> p\<close>
      show \<open>?thesis\<close>
      proof(cases \<open>p1 = p2\<close>)
        case True
        with 4 kom[simplified wpsm_kommutiert_def okay.simps] show \<open>?thesis\<close>
          apply(simp)
          apply(simp add: h 1)
          using wps_sym by fastforce
      next
        case False
        assume \<open>p1 \<noteq> p2\<close>
        with \<open>p \<noteq> p2\<close> \<open>p1 \<noteq> p\<close> show \<open>?thesis\<close>
        using unrel1[simplified wpsm_unbeteiligt1_def]
           unrel2[simplified wpsm_unbeteiligt2_def]
        apply(simp)
        apply(simp add: h)
        using 1[simplified handeln.simps h] 2[simplified handeln.simps h] by metis
      qed
    qed
  qed
qed

*)

section\<open>Experimental: Beispiel\<close>
(*das wird technisch um da executable code zu bekommen, ...*)

value\<open>[(x,y). x \<leftarrow> xs, y \<leftarrow> ys, x \<noteq> y]\<close>


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

text\<open>\<^const>\<open>erzeuge_beispiel\<close> erzeugt nur ein Beiespiel wenn alles wohlgeformt ist.\<close>
lemma "erzeuge_beispiel wps welt has m = Some bsp \<Longrightarrow>
  (\<forall> ha \<in> set has. wohlgeformte_handlungsabsicht wps welt ha) \<and>
  (\<forall> h \<in> set (alle_moeglichen_handlungen welt has). wohlgeformte_maxime_auf h wps m)"
  by(simp add: erzeuge_beispiel_def split: if_split_asm)
  

(*thx lars: https://stackoverflow.com/questions/74337244/turning-a-valuesimp-example-into-a-lemma-with-functions-in-them/74394525#74394525*)
ML\<open>
fun beispiel_conv ctxt =
  Conv.arg_conv (Conv.arg1_conv (Code_Simp.dynamic_conv ctxt) then_conv Conv.arg_conv (Code_Simp.dynamic_conv ctxt))

fun beispiel_tac ctxt =
  HEADGOAL (CONVERSION (beispiel_conv ctxt) THEN_ALL_NEW (resolve_tac ctxt @{thms refl}))
\<close>

method_setup beispiel = \<open>Scan.succeed (SIMPLE_METHOD o beispiel_tac)\<close>


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
kommt heraus: Nichtstun ist verboten.\<close>





subsection\<open>Kombination vom Maximen\<close>

lemma MaximeConjI:
  "kategorischer_imperativ_auf ha welt m1 \<and> kategorischer_imperativ_auf ha welt m2 \<Longrightarrow>
  kategorischer_imperativ_auf ha welt (MaximeConj m1 m2)"
  apply(cases m1, cases m2, simp)
  apply(simp add: kategorischer_imperativ_auf_def moralisch_simp okay_MaximeConj)
  apply blast
  done

text\<open>Die Rückrichtung gilt nur, wenn wir annehmen, dass es auch einen Fall gibt
in dem die \<^const>\<open>MaximeConj\<close> auch erfüllbar ist:\<close>
lemma MaximeConjD:
  "\<exists>ich. ausfuehrbar ich welt ha \<and> okay (MaximeConj m1 m2) ich (handeln ich welt ha) \<Longrightarrow>
    kategorischer_imperativ_auf ha welt (MaximeConj m1 m2) \<Longrightarrow>
    kategorischer_imperativ_auf ha welt m1 \<and> kategorischer_imperativ_auf ha welt m2"
  apply(simp add: kategorischer_imperativ_auf_def)
  apply(simp add: moralisch_MaximeConj)
  done

lemma MaximeConj:
  "\<exists>ich. ausfuehrbar ich welt ha \<and> okay (MaximeConj m1 m2) ich (handeln ich welt ha) \<Longrightarrow>
    kategorischer_imperativ_auf ha welt (MaximeConj m1 m2) \<longleftrightarrow>
    kategorischer_imperativ_auf ha welt m1 \<and> kategorischer_imperativ_auf ha welt m2"
  using MaximeConjI MaximeConjD by metis

lemma kategorischer_imperativ_auf_MaximeConj_comm:
  "kategorischer_imperativ_auf ha welt (MaximeConj m1 m2)
   \<longleftrightarrow> kategorischer_imperativ_auf ha welt (MaximeConj m2 m1)"
  by(auto simp add: kategorischer_imperativ_auf_def moralisch_simp okay_MaximeConj)




text\<open>Für \<^const>\<open>MaximeDisj\<close> müssen wir generell annehmen,
dass einer der Fälle erfüllbar ist.\<close>
lemma MaximeDisjI:
"((\<exists>ich. ausfuehrbar ich welt ha \<and> okay m1 ich (handeln ich welt ha))
   \<and> kategorischer_imperativ_auf ha welt m1) \<or>
 ((\<exists>ich. ausfuehrbar ich welt ha \<and> okay m2 ich (handeln ich welt ha))
   \<and> kategorischer_imperativ_auf ha welt m2) \<Longrightarrow>
  kategorischer_imperativ_auf ha welt (MaximeDisj m1 m2)"
  apply(simp add: kategorischer_imperativ_auf_def okay_MaximeDisj)
  apply(erule disjE)
  apply (metis moralisch_MaximeDisjI)+
  done
text\<open>Die Rückrichtung gilt leider nicht.\<close>

text\<open>Die Annahmen sind leider sehr stark:\<close>
lemma
  "((\<exists>ich. ausfuehrbar ich welt ha \<and> okay m ich (handeln ich welt ha))
    \<and> kategorischer_imperativ_auf ha welt m)
  \<Longrightarrow>
  moralisch welt m ha"
  by (simp add: kategorischer_imperativ_auf_def)


text\<open>Wenn wir die Annahme stärker machen gilt auch folgendes:\<close>
lemma MaximeDisjI_from_conj:
  "kategorischer_imperativ_auf ha welt m1 \<and> kategorischer_imperativ_auf ha welt m2 \<Longrightarrow>
  kategorischer_imperativ_auf ha welt (MaximeDisj m1 m2)"
  apply(simp add: kategorischer_imperativ_auf_def moralisch_simp okay_MaximeDisj)
  by blast


lemma moralisch_kapImp_MaximeDisjI:
  "moralisch welt m1 ha \<Longrightarrow>
  kategorischer_imperativ_auf ha welt (MaximeDisj m1 m2)"
  by(simp add: kategorischer_imperativ_auf_def moralisch_simp okay_MaximeDisj)

lemma kategorischer_imperativ_auf_MaximeDisj_comm:
  "kategorischer_imperativ_auf ha welt (MaximeDisj m1 m2)
   \<longleftrightarrow> kategorischer_imperativ_auf ha welt (MaximeDisj m2 m1)"
  by(auto simp add: kategorischer_imperativ_auf_def moralisch_simp okay_MaximeDisj)




lemma
  "kategorischer_imperativ_auf ha1 welt m1 \<Longrightarrow> kategorischer_imperativ_auf ha2 welt m2 \<Longrightarrow>
  kategorischer_imperativ_auf ha1 welt (MaximeDisj m1 m2)"
(*und ha2. Bessere disjI regel bauen?*)
  apply(cases m1, cases m2, simp)
(*Nitpick found a counterexample for card 'a = 2 and card 'b = 1:
*)
  oops
(*hmmmmm, nicht gut*)
lemma
  "
    ha1 = Handlungsabsicht (\<lambda>p w. Some w) \<Longrightarrow>
    ha2 = Handlungsabsicht (\<lambda>p w. None) \<Longrightarrow>
    m1 = Maxime (\<lambda>p h. False) \<Longrightarrow>
    m2 = Maxime ((\<lambda>p h. False)(Bob := \<lambda>h. True)) \<Longrightarrow>
    welt = (0::int) \<Longrightarrow>
kategorischer_imperativ_auf ha1 welt m1 \<Longrightarrow> kategorischer_imperativ_auf ha2 welt m2 \<Longrightarrow>
  \<not> kategorischer_imperativ_auf ha1 welt (MaximeDisj m1 m2)"
  apply(simp)
  apply(thin_tac "_ = _")+
  apply(code_simp)
  done


(*das waere die korrekte DisjI:*)
lemma
  "kategorischer_imperativ_auf ha welt m1 \<Longrightarrow>
  kategorischer_imperativ_auf ha welt (MaximeDisj m1 m2)"
  oops (*nitpick found a counter example*)










end
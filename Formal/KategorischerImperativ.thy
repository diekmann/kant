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

Daraus ergibt sich die finale Formalisierung:

Für alle möglichen (wohlgeformten) Handlungsabsichten muss gelten:
Wenn es eine Person gibt für die diese Handlungsabsicht moralisch ist,
dann muss diese Handlungsabsicht auch für alle moralisch (im Sinne der goldenen Regel) sein.
\<close>
definition kategorischer_imperativ
  :: \<open>('person, 'world) wp_swap \<Rightarrow> 'world \<Rightarrow> ('person, 'world) maxime \<Rightarrow> bool\<close>
where
  \<open>kategorischer_imperativ welt_personen_swap welt m =
    (\<forall>h.
          wohlgeformte_handlungsabsicht welt_personen_swap welt h \<and>
          (\<exists>p. maxime_und_handlungsabsicht_generalisieren2 welt_personen_swap m h \<and> okay m p (handeln p welt h))
              \<longrightarrow> moralisch welt m h)\<close>

text\<open>Dabei sind \<^const>\<open>wohlgeformte_handlungsabsicht\<close>
und \<^const>\<open>maxime_und_handlungsabsicht_generalisieren\<close>
ein technisch notwendiges Implementierungsdetail um nicht-wohlgeformte Handlungen
oder Maximen auszuschließen.\<close>

text\<open>Minimal andere Formulierung:\<close>
lemma
\<open>kategorischer_imperativ welt_personen_swap welt m \<longleftrightarrow>
  (\<forall>h.
    (\<exists>p.
        wohlgeformte_handlungsabsicht welt_personen_swap welt h \<and>
        maxime_und_handlungsabsicht_generalisieren2 welt_personen_swap m h \<and>
        okay m p (handeln p welt h))
    \<longrightarrow> moralisch welt m h)\<close>
  unfolding kategorischer_imperativ_def
  by(simp)

text\<open>Der Existenzquantor lässt sich auch in einen Allquantor umschreiben:\<close>
lemma
\<open>kategorischer_imperativ welt_personen_swap welt m \<longleftrightarrow>
  (\<forall>h ich.
      wohlgeformte_handlungsabsicht welt_personen_swap welt h \<and> 
      maxime_und_handlungsabsicht_generalisieren2 welt_personen_swap m h \<and>
      okay m ich (handeln ich welt h) \<longrightarrow> moralisch welt m h)\<close>
  by(simp add: kategorischer_imperativ_def)
  

text\<open>Für jede Handlungsabsicht:
  wenn ich so handeln würde muss es auch okay sein, wenn zwei beliebige
  personen so handeln, wobei einer Täter und einer Opfer ist.\<close>
lemma kategorischer_imperativ_simp:
  "kategorischer_imperativ welt_personen_swap welt m \<longleftrightarrow>
    (\<forall>h p1 p2 ich.
      wohlgeformte_handlungsabsicht welt_personen_swap welt h \<and> 
      maxime_und_handlungsabsicht_generalisieren2 welt_personen_swap m h \<and>
      okay m ich (handeln ich welt h)
      \<longrightarrow> okay m p1 (handeln p2 welt h))"
  by (simp add: kategorischer_imperativ_def moralisch_simp)


lemma kategorischer_imperativI:
  \<open>(\<And>h p1 p2 p. wohlgeformte_handlungsabsicht welt_personen_swap welt h \<Longrightarrow>
   maxime_und_handlungsabsicht_generalisieren2 welt_personen_swap m h \<Longrightarrow>
   okay m p (handeln p welt h) \<Longrightarrow> okay m p1 (handeln p2 welt h)
   )
 \<Longrightarrow> kategorischer_imperativ welt_personen_swap welt m\<close>
  by(auto simp add: kategorischer_imperativ_simp)


subsection\<open>Triviale Maximen die den Kategorischen Imperativ immer Erfüllen\<close>
text\<open>
Die Maxime die keine Handlung erlaubt (weil immer False) erfüllt den kategorischen
Imperativ:\<close>
lemma \<open>kategorischer_imperativ welt_personen_swap welt (Maxime (\<lambda>ich h. False))\<close>
  by(simp add: kategorischer_imperativ_def)

text\<open>Allerdings kann mit so einer Maxime nie etwas moralisch sein.\<close>
lemma \<open>\<not> moralisch welt (Maxime (\<lambda>ich h. False)) h\<close>
  by(simp add: moralisch_simp)

text\<open>Die Maxime die jede Handlung erlaubt (weil immer True) erfüllt den kategorischen
Imperativ:\<close>
lemma \<open>kategorischer_imperativ welt_personen_swap welt (Maxime (\<lambda>ich h. True))\<close>
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

lemma \<open>kategorischer_imperativ welt_personen_swap welt m \<Longrightarrow>
  wohlgeformte_handlungsabsicht welt_personen_swap welt h \<Longrightarrow>
  maxime_und_handlungsabsicht_generalisieren2 welt_personen_swap m h \<Longrightarrow>
  okay m ich (handeln ich welt h) \<Longrightarrow> moralisch welt m h\<close>
  apply(simp add: kategorischer_imperativ_def)
  by auto

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
definition "kategorischer_imperativ_gegenbeispiel welt_personen_swap welt m h ich p1 p2 \<equiv>
wohlgeformte_handlungsabsicht welt_personen_swap welt h \<and> 
      maxime_und_handlungsabsicht_generalisieren2 welt_personen_swap m h \<and>
      okay m ich (handeln ich welt h) \<and>
      \<not> okay m p1 (handeln p2 welt h)"

lemma "kategorischer_imperativ_gegenbeispiel welt_personen_swap welt m h ich p1 p2 \<Longrightarrow>
  \<not> kategorischer_imperativ welt_personen_swap welt m"
  apply(simp add: kategorischer_imperativ_simp kategorischer_imperativ_gegenbeispiel_def)
  apply(rule_tac x=h in exI, simp)
  by blast

subsection\<open>Maximen die den Kategorischen Imperativ immer Erfüllen\<close>

text\<open>Wenn eine Maxime jede Handlungsabsicht als moralisch bewertet,
erfüllt diese Maxime den kategorischen Imperativ.
Da diese Maxime jede Handlung erlaubt, ist es dennoch eine wohl ungeeignete Maxime.\<close>
lemma \<open>\<forall>h. moralisch welt maxime h \<Longrightarrow> kategorischer_imperativ welt_personen_swap welt maxime\<close>
  apply(cases \<open>maxime\<close>, rename_tac m)
  by(simp add: kategorischer_imperativ_def moralisch_simp)


text\<open>Eine Maxime die das ich und die Handlung ignoriert und etwas für alle fordert erfüllt den
kategorischen Imperativ.\<close>
lemma blinde_maxime_katimp:
  \<open>kategorischer_imperativ welt_personen_swap welt (Maxime (\<lambda>ich h. \<forall>p. m p))\<close>
  apply(rule kategorischer_imperativI)
  by(simp add: maxime_und_handlungsabsicht_generalisieren_def)


theorem altruistische_maxime_katimp:
  assumes kom: \<open>wpsm_kommutiert M welt_personen_swap welt\<close>
      and unrel1: \<open>wpsm_unbeteiligt1 M welt_personen_swap welt\<close>
      and unrel2: \<open>wpsm_unbeteiligt2 M welt_personen_swap welt\<close>
      and welt_personen_swap_sym:
        \<open>\<forall>p1 p2 welt. welt_personen_swap p1 p2 welt = welt_personen_swap p2 p1 welt\<close>
      and welt_personen_swap_id:
        \<open>\<forall>p1 p2 welt. welt_personen_swap p1 p2 (welt_personen_swap p1 p2 welt) = welt\<close>
      and maxime_ignoriert_ich: "M = Maxime m \<and> (\<forall>ich. m ich = M')"
  shows \<open>kategorischer_imperativ welt_personen_swap welt M\<close>
proof(rule kategorischer_imperativI)
  fix ha ich p1 p2
  assume wfh: "wohlgeformte_handlungsabsicht welt_personen_swap welt ha"
    and  "maxime_und_handlungsabsicht_generalisieren2 welt_personen_swap M ha"
    and  okich: "okay M ich (handeln ich welt ha)"

  from maxime_ignoriert_ich have M': "M = Maxime (\<lambda>ich h. M' h)"
    by(simp add: fun_eq_iff)
  hence okay_ignoriert_person: "okay M p1 h \<longleftrightarrow> okay M p2 h" for p1 p2 h
    by(simp)

  from kom have komHOL:
    "\<And> p1 p2 h.
   okay M p2 (Handlung (welt_personen_swap p1 p2 welt) (h p1 (welt_personen_swap p1 p2 welt))) =
   okay M p1 (Handlung welt (welt_personen_swap p1 p2 (h p1 (welt_personen_swap p2 p1 welt))))"
    by(simp add: wpsm_kommutiert_def)

  obtain h where h: \<open>ha = Handlungsabsicht h\<close>
    by(cases \<open>ha\<close>, blast)

  from wfh[simplified wohlgeformte_handlungsabsicht_def h]
  have 1: \<open>h p2 welt = welt_personen_swap ich p2 (h ich (welt_personen_swap p2 ich welt))\<close>
    by simp

  from wfh wohlgeformte_handlungsabsicht_imp_swpaid
  have swapid: "welt_personen_swap p2 ich (welt_personen_swap ich p2 welt) = welt"
    by fastforce


  from welt_personen_swap_id have map_handlung_id:
    "\<And>h p1 p2. (map_handlung (welt_personen_swap p1 p2) (map_handlung (welt_personen_swap p1 p2) h)) = h"
    by(case_tac h, simp)


  have mhg3: "\<forall>p2. okay M ich (handeln ich welt ha)
      \<longleftrightarrow> okay M p2 ((map_handlung (welt_personen_swap p2 ich) (handeln ich welt ha)))"
    sorry (*will ich das als assm?*)
  thm maxime_und_handlungsabsicht_generalisieren3_def
  from okich mhg3
  have "okay M p2 (map_handlung (welt_personen_swap p2 ich) (handeln ich welt ha))"
    by simp
  with wfh[simplified wohlgeformte_handlungsabsicht_def]
  have "okay M p2
    (map_handlung (welt_personen_swap p2 ich)
      (map_handlung (welt_personen_swap p2 ich) (handeln p2 (welt_personen_swap ich p2 welt) ha)))"
    by simp
  with map_handlung_id have "okay M p2 (handeln p2 (welt_personen_swap ich p2 welt) ha)"
    by(simp)
    

  from wfh[simplified wohlgeformte_handlungsabsicht_def] okich
  have "okay M ich
    (map_handlung (welt_personen_swap p2 ich) (handeln p2 (welt_personen_swap ich p2 welt) ha))"
    by simp
  hence "okay M ich
    (Handlung (welt_personen_swap p2 ich (welt_personen_swap ich p2 welt))
                (welt_personen_swap p2 ich (nachher (handeln p2 (welt_personen_swap ich p2 welt) ha))))"
    by(cases ha, simp)
  hence "okay M ich
    (Handlung welt
                (welt_personen_swap p2 ich (nachher (handeln p2 (welt_personen_swap ich p2 welt) ha))))"
    by(simp add: swapid)
  hence "okay M ich
    (Handlung welt (welt_personen_swap p2 ich (h p2 (welt_personen_swap ich p2 welt))))"
    by(simp add: h)
  with komHOL[of ich p2 h] okay_ignoriert_person
  have "okay M ich (Handlung (welt_personen_swap p2 ich welt) (h p2 (welt_personen_swap p2 ich welt)))"
    by blast
  hence "okay M ich (handeln p2 (welt_personen_swap p2 ich welt) ha)"
    by(simp add: h)


  have 4:
    \<open>okay M ich (handeln ich (welt_personen_swap p2 ich welt) ha)\<close>
    sorry


  show "okay M p1 (handeln p2 welt ha)"
  proof(cases \<open>ich = p2\<close>)
    case True
    then show \<open>?thesis\<close>
      using okich okay_ignoriert_person by auto
  next
    case False
    assume \<open>ich \<noteq> p2\<close>
    with 1[simplified handeln.simps h] 4[simplified handeln.simps h] show \<open>?thesis\<close>
      apply(simp add: h)
      using kom[simplified wpsm_kommutiert_def okay.simps] welt_personen_swap_sym
      using okay_ignoriert_person by fastforce 
  qed

oops

text\<open>Eine Maxime die das ich ignoriert und etwas für alle fordert erfüllt den
kategorischen Imperativ.\<close>
theorem altruistische_maxime_katimp:
  fixes P :: \<open>'person \<Rightarrow> 'world handlung \<Rightarrow> bool\<close>
  assumes kom: \<open>wpsm_kommutiert (Maxime P) welt_personen_swap welt\<close>
      and unrel1: \<open>wpsm_unbeteiligt1 (Maxime P) welt_personen_swap welt\<close>
      and unrel2: \<open>wpsm_unbeteiligt2 (Maxime P) welt_personen_swap welt\<close>
      and welt_personen_swap_sym:
        \<open>\<forall>p1 p2 welt. welt_personen_swap p1 p2 welt = welt_personen_swap p2 p1 welt\<close>
  shows \<open>kategorischer_imperativ welt_personen_swap welt (Maxime (\<lambda>ich h. (\<forall>pX. P pX h)))\<close>
proof(rule kategorischer_imperativI, simp, intro allI)
  fix ha :: \<open>('person, 'world) handlungsabsicht\<close>
  and p1 p2 p :: \<open>'person\<close>
  assume wfh: \<open>wohlgeformte_handlungsabsicht welt_personen_swap welt ha\<close>
     and mhg: \<open>maxime_und_handlungsabsicht_generalisieren2 welt_personen_swap (Maxime (\<lambda>ich h. \<forall>pX. P pX h)) ha\<close>
     and okayp: \<open>\<forall>pX. P pX (handeln p welt ha)\<close>

  obtain h where h: \<open>ha = Handlungsabsicht h\<close>
    by(cases \<open>ha\<close>, blast)

  from wfh[simplified wohlgeformte_handlungsabsicht_def h]
  have 1: \<open>h p2 welt = welt_personen_swap p p2 (h p (welt_personen_swap p2 p welt))\<close>
    by simp

  from wfh[simplified wohlgeformte_handlungsabsicht_def h] okayp
  have WTF: "\<forall>pX. P pX (Handlung welt (welt_personen_swap p p2 (h p2 (welt_personen_swap p p2 welt))))"
      (*WTF? ?*)
      by (metis h handeln.simps handlung.map_sel(2) nachher_handeln  welt_personen_swap_sym)


  from mhg[simplified maxime_und_handlungsabsicht_generalisieren2_def h, simplified] okayp[simplified h, simplified]
    have XXX: "\<forall>pX. P pX (Handlung (welt_personen_swap p p2 welt) (h p2 (welt_personen_swap p p2 welt)))"
      by simp (*uffff, das hat mir metis oben schon auch ohne mhg gebaut*)
  hence "(\<forall>pX. P pX (handeln p2 (welt_personen_swap p p2 welt) ha))"
    by(simp add: h)
  thm XXX kom[simplified wpsm_kommutiert_def okay.simps]
  
  
  from mhg[simplified maxime_und_handlungsabsicht_generalisieren2_def] okayp[simplified h]
  have 2:
  \<open>\<forall>pX. P pX (handeln p (welt_personen_swap p2 p welt) ha)\<close>
    apply(simp)
    apply(simp add: h)
    sorry (*keine ahnung ob das was wird :( *)
  from 2
  have 4:
    \<open>P p (handeln p (welt_personen_swap p2 p welt) ha)\<close>
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
        using 2[simplified handeln.simps h] welt_personen_swap_sym by fastforce
    next
      case False
      assume \<open>p1 \<noteq> p\<close>
      show \<open>?thesis\<close>
      proof(cases \<open>p1 = p2\<close>)
        case True
        with 4 kom[simplified wpsm_kommutiert_def okay.simps] show \<open>?thesis\<close>
          apply(simp)
          apply(simp add: h 1)
          using welt_personen_swap_sym by fastforce
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

text\<open>Auch eine Maxime welche das ich ignoriert,
also nur die Handlung global betrachtet, erfüllt den kategorischen Imperativ.\<close>
theorem globale_maxime_katimp:
  fixes P :: \<open>'world handlung \<Rightarrow> bool\<close>
  assumes kom: \<open>wpsm_kommutiert (Maxime (\<lambda>ich::'person. P)) welt_personen_swap welt\<close>
      and unrel1: \<open>wpsm_unbeteiligt1 (Maxime (\<lambda>ich::'person. P)) welt_personen_swap welt\<close>
      and unrel2: \<open>wpsm_unbeteiligt2 (Maxime (\<lambda>ich::'person. P)) welt_personen_swap welt\<close>
      and welt_personen_swap_sym:
        \<open>\<forall>p1 p2 welt. welt_personen_swap p1 p2 welt = welt_personen_swap p2 p1 welt\<close>
  shows \<open>kategorischer_imperativ welt_personen_swap welt (Maxime (\<lambda>ich::'person. P))\<close>
proof(rule kategorischer_imperativI, simp)
  fix ha :: \<open>('person, 'world) handlungsabsicht\<close>
  and p2 p :: \<open>'person\<close>
  assume wfh: \<open>wohlgeformte_handlungsabsicht welt_personen_swap welt ha\<close>
     and mhg: \<open>maxime_und_handlungsabsicht_generalisieren (Maxime (\<lambda>ich. P)) ha p\<close>
     and okayp: \<open>P (handeln p welt ha)\<close>

  obtain h where h: \<open>ha = Handlungsabsicht h\<close>
    by(cases \<open>ha\<close>, blast)

  from wfh[simplified wohlgeformte_handlungsabsicht_def h]
  have 1: \<open>h p2 welt = welt_personen_swap p p2 (h p (welt_personen_swap p2 p welt))\<close>
    by simp
  from mhg[simplified maxime_und_handlungsabsicht_generalisieren_def h] okayp[simplified h]
  have 2:
  \<open>P (handeln p (welt_personen_swap p2 p welt) ha)\<close>
    by(auto simp add: h)
  from 2
  have 4:
    \<open>P (handeln p (welt_personen_swap p2 p welt) ha)\<close>
    by(simp)

  show \<open>P (handeln p2 welt ha)\<close>
  proof(cases \<open>p = p2\<close>)
    case True
    then show \<open>?thesis\<close>
      using okayp by auto 
  next
    case False
    assume \<open>p \<noteq> p2\<close>
    with 1[simplified handeln.simps h] 4[simplified handeln.simps h] show \<open>?thesis\<close>
      apply(simp add: h)
      using kom[simplified wpsm_kommutiert_def okay.simps] welt_personen_swap_sym by fastforce
  qed
qed

(*TODO: Handlungsabsicht (jeder_zahlt erfuellt kategorischen imp?*)

end
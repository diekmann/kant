theory SchleierNichtwissen
imports BeispielPerson Handlung Maxime Swap
begin

section\<open>Schleier des Nichtwissens\<close>
text\<open>
Rawls' Schleier des Nichtwissens \<^url>\<open>https://de.wikipedia.org/wiki/Schleier_des_Nichtwissens\<close>
ist ein fiktives Modell,
>> über die zukünftige Gesellschaftsordnung entscheiden können,
aber selbst nicht wissen,
an welcher Stelle dieser Ordnung sie sich später befinden werden,
also unter einem „Schleier des Nichtwissens“ stehen.<< Quote wikipedia


Wir bedienen uns bei der Idee dieses Modells um gültige Handlungsabsichten und Maximen
zu definieren.
Handlungsabsichten und Maximen sind nur gültig, wenn darin keine Personen hardgecoded werden.

Beispielsweise ist folgende Handlungsabsicht ungültig:
\<^term>\<open>\<lambda>ich welt. if ich = Alice then Do_A welt else Do_B welt\<close>

Handlungsabsichten und Maximen müssen immer generisch geschrieben werden,
so dass die handelnden und betroffenen Personen niemals anhand ihres Namens ausgewählt werden.

unser Modell von Handlungsabsichten und Maximen stellt beispielsweise die
handelnde Person als Parameter bereit.
Folgendes ist also eine gültige Handlung:
\<^term>\<open>\<lambda>ich welt. ModifiziereWelt welt ich\<close>

Auch ist es erlaubt, Personen in einer Handlungsabsicht oder Maxime nur anhand ihrer
Eigenschaften in der Welt auszuwählen.
Folgendes wäre eine wohlgeformte Handlung, wenn auch eine moralisch fragwürdige:
\<^term>\<open>\<lambda>ich welt. enteignen ` {opfer. besitz opfer > besitz ich}\<close>

Um diese Idee von wohlgeformten Handlungsabsichten und Maximen zu formalisieren bedienen
wir uns der Idee des Schleiers des Nichtwissens.
Wir sagen, dass Handlungsabsichten wohlgeformt sind, wenn die Handlungsabsicht gleich bleibt,
wenn man sowohl die handelnde Person austauscht,
als auch alle weltlichen Eigenschaften dieser Person.
Anders ausgedrückt: Wohlgeformte Handlungsabsichten und Maximen sind solche,
bei denen bei der Definition noch nicht feststeht, auf we sie später zutreffen.
\<close>

text\<open>Für jede Welt muss eine Welt-Personen Swap (wps) Funktion bereit gestellt werden,
die alle Weltlichen Eigenschaften von 2 Personen vertauscht:\<close>
type_synonym ('person, 'world) wp_swap = \<open>'person \<Rightarrow> 'person \<Rightarrow> 'world \<Rightarrow> 'world\<close>

text_raw\<open>
\begin{equation*}
\begin{tikzcd}[column sep=14em, row sep=huge]
\textit{welt}
  \arrow[red, d, "\textit{welt-personen-swap}\ \textit{p1}\ \textit{p2}" near start]
  \arrow[blue]{r}[blue]{\textit{handeln}\ \textit{p1}}
& \textit{welt'} \\
\textit{alternativ-welt}
  \arrow[red]{r}{\textit{handeln}\ \textit{p2}}
& \textit{alternativ-welt'}
  \arrow[red, u, "\textit{welt-personen-swap}\ \textit{p1}\ \textit{p2}" near start]
\end{tikzcd}
\end{equation*}
\<close>

subsection\<open>Wohlgeformte Handlungsabsicht\<close>


definition wohlgeformte_handlungsabsicht
  :: \<open>('person, 'world) wp_swap \<Rightarrow> 'world \<Rightarrow> ('person, 'world) handlungsabsicht \<Rightarrow> bool\<close>
where
  \<open>wohlgeformte_handlungsabsicht wps welt h \<equiv>
    \<forall>p1 p2. handeln p1 welt h =
            map_handlung (wps p2 p1) (handeln p2 (wps p1 p2 welt) h)\<close>

(*TODO: jeden beweis der wohlgeformte_handlungsabsicht_def verwendet durch wohlgeformte_handlungsabsicht_simp ersetzen*)
text\<open>Folgende Equivalenz erklärt die Definition vermutlich besser:\<close>
lemma wohlgeformte_handlungsabsicht_simp:
  \<open>wohlgeformte_handlungsabsicht wps welt ha \<longleftrightarrow>
    (\<forall>p1 p2. wps p2 p1 (wps p1 p2 welt) = welt) \<and>
    (\<forall>p1 p2. handeln p1 welt ha =
                Handlung welt
                        (wps p2 p1 (nachher_handeln p2 (wps p1 p2 welt) ha)))\<close>
  apply(cases \<open>ha\<close>, simp add: wohlgeformte_handlungsabsicht_def handeln_def)
  by fastforce

definition wohlgeformte_handlungsabsicht_gegenbeispiel
  :: \<open>('person, 'world) wp_swap \<Rightarrow> 'world \<Rightarrow> ('person, 'world) handlungsabsicht \<Rightarrow> 'person \<Rightarrow> 'person \<Rightarrow> bool\<close>
where
  \<open>wohlgeformte_handlungsabsicht_gegenbeispiel wps welt h taeter opfer \<equiv>
    handeln taeter welt h \<noteq>
        map_handlung (wps opfer taeter) (handeln opfer (wps taeter opfer welt) h)\<close>

lemma \<open>wohlgeformte_handlungsabsicht_gegenbeispiel wps welt h p1 p2 \<Longrightarrow>
        \<not>wohlgeformte_handlungsabsicht wps welt h\<close>
  by(auto simp add: wohlgeformte_handlungsabsicht_gegenbeispiel_def wohlgeformte_handlungsabsicht_def)

(*TODO: das sollte ein Homomorphismus sein.*)

lemma wohlgeformte_handlungsabsicht_imp_swpaid:
  \<open>wohlgeformte_handlungsabsicht wps welt h \<Longrightarrow>
    wps p1 p2 (wps p2 p1 welt) = welt\<close>
  by(simp add: wohlgeformte_handlungsabsicht_simp)








text\<open>Nach der gleichen Argumentation müssen Maxime und Handlungsabsicht so generisch sein,
dass sie in allen Welten zum gleichen Ergebnis kommen.\<close>
(*
Warum die Vorbedingung: Sonderfall noops: (bsp von sich selbst stehlen). Ohne das geht z.B. stehlen nicht.
*)
definition maxime_und_handlungsabsicht_generalisieren
  :: \<open>('person, 'world) wp_swap \<Rightarrow> 'world \<Rightarrow> 
      ('person, 'world) maxime \<Rightarrow> ('person, 'world) handlungsabsicht \<Rightarrow> 'person \<Rightarrow> bool\<close>
where
  \<open>maxime_und_handlungsabsicht_generalisieren wps welt m h p =
    (\<forall>p1 p2. (\<not>ist_noop (handeln p welt h) \<and> \<not>ist_noop (handeln p (wps p1 p2 welt) h))
              \<longrightarrow> okay m p (handeln p welt h) \<longleftrightarrow> okay m p (handeln p (wps p1 p2 welt) h))\<close>


text\<open>Für eine gegebene Maxime schließt die Forderung
\<^const>\<open>maxime_und_handlungsabsicht_generalisieren\<close> leider einige Handlungen aus.
Beispiel:
In einer Welt besitzt \<^const>\<open>Alice\<close> 2 und \<^const>\<open>Eve\<close> hat 1 Schulden.
Die Maxime ist, dass Individuen gerne keinen Besitz verlieren.
Die Handlung sei ein globaler reset, bei dem jeden ein Besitz von 0 zugeordnet wird.
Leider generalisiert diese Handlung nicht, da \<^const>\<open>Eve\<close> die Handlung gut findet,
\<^const>\<open>Alice\<close> allerdings nicht.
\<close>
lemma
   \<open>\<not> maxime_und_handlungsabsicht_generalisieren
      swap
      ((\<lambda>x. 0)(Alice := (2::int), Eve := - 1))
      (Maxime (\<lambda>ich h. (vorher h) ich \<le> (nachher h) ich))
      (Handlungsabsicht (\<lambda>ich w. Some (\<lambda>_. 0)))
      Eve\<close>
  apply(simp add: maxime_und_handlungsabsicht_generalisieren_def )
  apply(simp add: ist_noop_def fun_eq_iff handeln_def nachher_handeln.simps)
  by (metis (full_types) fun_upd_other fun_upd_same not_numeral_le_zero person.simps(6) swap_a swap_b zero_neq_neg_one)
  
  


text\<open>Die Maxime und \<^typ>\<open>('person, 'world) wp_swap\<close> müssen einige Eigenschaften erfüllen.
Wir kürzen das ab mit \<^term>\<open>wpsm :: ('person, 'world) wp_swap\<close>: Welt Person Swap Maxime.\<close>

text\<open>Die Person für die Maxime ausgewertet wird und swappen der Personen in der Welt
muss equivalent sein:\<close>
definition wpsm_kommutiert
  :: \<open>('person, 'world) maxime \<Rightarrow> ('person, 'world) wp_swap \<Rightarrow> 'world \<Rightarrow> bool\<close>
where
  \<open>wpsm_kommutiert m wps welt \<equiv>
  \<forall> p1 p2 ha.
    okay m p2 (handeln p1 (wps p1 p2 welt) ha)
    \<longleftrightarrow>
    okay m p1 (Handlung welt (wps p1 p2 (nachher_handeln p1 (wps p2 p1 welt) ha)))\<close>

lemma wpsm_kommutiert_handlung_raw:
  \<open>wpsm_kommutiert m wps welt =
  (\<forall> p1 p2 ha.
    okay m p2 (Handlung (wps p1 p2 welt) (nachher_handeln p1 (wps p1 p2 welt) ha))
    \<longleftrightarrow>
    okay m p1 (Handlung welt (wps p1 p2 (nachher_handeln p1 (wps p2 p1 welt) ha))))\<close>
  apply(simp add: wpsm_kommutiert_def)
  apply(rule iffI)
   apply(intro allI)
   apply(erule_tac x=p1 in allE)
   apply(erule_tac x=p2 in allE)
   apply(erule_tac x="ha" in allE)
   apply(simp add: nachher_handeln.simps handeln_def; fail)
  apply(intro allI)
  apply(case_tac ha)
  apply(simp add: handeln_def)
  done


lemma wpsm_kommutiert_unfold_handlungsabsicht:
  \<open>wpsm_kommutiert m wps welt =
  (\<forall> p1 p2 ha.
    okay m p2 (handeln p1 (wps p1 p2 welt) ha)
    \<longleftrightarrow>
    okay m p1 (handeln p1 welt (Handlungsabsicht (\<lambda>p w. Some (wps p1 p2 (nachher_handeln p (wps p2 p1 w) ha)))))
  )\<close>
  apply(simp add: wpsm_kommutiert_handlung_raw)
  by (simp add: handeln_def nachher_handeln.simps)

text\<open>Wenn sowohl \<^const>\<open>wohlgeformte_handlungsabsicht\<close> als auch \<^const>\<open>wpsm_kommutiert\<close>,
dann erhalten wir ein sehr intuitives Ergebnis,
welches besagt, dass ich handelnde Person und Person für die die Maxime gelten soll
vertauschen kann.\<close>
lemma wfh_wpsm_kommutiert_simp:
  \<open>wohlgeformte_handlungsabsicht wps welt ha \<Longrightarrow>
  wpsm_kommutiert m wps welt \<Longrightarrow>
    okay m p2 (handeln p1 (wps p1 p2 welt) ha)
    \<longleftrightarrow>
    okay m p1 (handeln p2 welt ha)\<close>
  apply(cases \<open>ha\<close>, simp)
  by(simp add: wpsm_kommutiert_def wohlgeformte_handlungsabsicht_simp)

text\<open>Die Rückrichtung gilt auch,
aber da wir das für alle Handlungsabsichten in der Annahme brauchen,
ist das eher weniger hilfreich.\<close>
lemma wfh_kommutiert_wpsm:
  \<open>\<forall>ha. wohlgeformte_handlungsabsicht wps welt ha \<and>
       (\<forall>p1 p2. okay m p2 (handeln p1 (wps p1 p2 welt) ha)
           \<longleftrightarrow>
           okay m p1 (handeln p2 welt ha)) \<Longrightarrow>
wpsm_kommutiert m wps welt\<close>
  by(simp add: wpsm_kommutiert_def wohlgeformte_handlungsabsicht_simp)
  


subsection\<open>Wohlgeformte Maxime\<close>

(*Eigentlich sollte das fuer alle Handlungen gelten, aber wenn ich ausfuehrbaren code will
habe ich ein Problem, dass Handlungen nicht enumerable sind.*)
definition wohlgeformte_maxime_auf
  :: \<open>'world handlung \<Rightarrow> ('person, 'world) wp_swap \<Rightarrow> ('person, 'world) maxime \<Rightarrow> bool\<close>
where
  \<open>wohlgeformte_maxime_auf h wps m \<equiv>
    \<forall>p1 p2. okay m p1 h \<longleftrightarrow> okay m p2 (map_handlung (wps p1 p2) h)\<close>

definition wohlgeformte_maxime
  :: \<open>('person, 'world) wp_swap \<Rightarrow> ('person, 'world) maxime \<Rightarrow> bool\<close>
where
  \<open>wohlgeformte_maxime wps m \<equiv>
    \<forall>h. wohlgeformte_maxime_auf h wps m\<close>


text\<open>Beispiel:\<close>
lemma \<open>wohlgeformte_maxime swap (Maxime (\<lambda>ich h. (vorher h) ich \<le> (nachher h) ich))\<close>
  apply(simp add: wohlgeformte_maxime_def wohlgeformte_maxime_auf_def)
  apply(intro allI, case_tac \<open>h\<close>, simp)
  by (metis swap_a swap_symmetric)
  

(*<*)
subsection\<open>Generische Lemmata\<close>


lemma ist_noop_map_handlung:
  assumes wps_id:
        \<open>\<forall>p1 p2 welt. wps p1 p2 (wps p1 p2 welt) = welt\<close>
  shows \<open>ist_noop (map_handlung (wps p1 p2) h) = ist_noop h\<close>
  apply(cases \<open>h\<close>, rename_tac vor nach, simp add: ist_noop_def)
  using wps_id by metis

lemma ist_noop_wps_weak:
  assumes wfh: \<open>wohlgeformte_handlungsabsicht wps welt ha\<close>
    and swap_noop: \<open>\<forall>p1 p2 h. ist_noop (map_handlung (wps p1 p2) h) = ist_noop h\<close>
  shows \<open>ist_noop (handeln ich (wps p2 ich welt) ha) \<longleftrightarrow> ist_noop (handeln p2 welt ha)\<close>
  apply(subst wfh[simplified wohlgeformte_handlungsabsicht_def])
  apply(simp add: swap_noop)
  done

lemma ist_noop_wps:
  assumes wfh: \<open>wohlgeformte_handlungsabsicht wps welt ha\<close>
  and wps_id:
       \<open>\<forall>p1 p2 welt. wps p1 p2 (wps p1 p2 welt) = welt\<close>
  shows \<open>ist_noop (handeln p2 (wps ich p2 welt) ha) \<longleftrightarrow> ist_noop (handeln ich welt ha)\<close>
  apply(rule ist_noop_wps_weak[OF wfh])
  using ist_noop_map_handlung[OF wps_id] by simp




lemma ausfuehrbar_wps:
  assumes wfh: \<open>wohlgeformte_handlungsabsicht wps welt ha\<close>
  and wps_id:
       \<open>\<forall>p1 p2 welt. wps p1 p2 (wps p1 p2 welt) = welt\<close>
     shows \<open>ausfuehrbar p2 (wps ich p2 welt) ha \<longleftrightarrow> ausfuehrbar ich welt ha\<close>
  apply -
  apply(insert wfh[simplified wohlgeformte_handlungsabsicht_simp handeln_def nachher_handeln.simps])
  apply(cases ha, simp add: ausfuehrbar.simps)
  apply(simp add: nachher_handeln.simps)
(*TODO: bei der wohlgeformten Handlungsabsicht muss dass ausfuehrbar propagieren!*)
  
  
(*>*)

end
theory SchleierNichtwissen
imports BeispielPerson Handlung Maxime Swap
begin

section\<open>Schleier des Nichtwissens\<close>
text\<open>
Rawls' Schleier des Nichtwissens \<^url>\<open>https://de.wikipedia.org/wiki/Schleier_des_Nichtwissens\<close>
ist ein fiktives Modell, in der Personen
>>über die zukünftige Gesellschaftsordnung entscheiden können,
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

text\<open>Ein jeder \<^typ>\<open>('person, 'world) wp_swap\<close> sollte mindestens folgendes erfüllen:\<close>
definition wps_id :: \<open>('person, 'world) wp_swap \<Rightarrow> 'world \<Rightarrow> bool\<close>
where
  \<open>wps_id wps welt \<equiv> \<forall>p1 p2. wps p2 p1 (wps p1 p2 welt) = welt\<close>


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

fun wohlgeformte_handlungsabsicht
  :: \<open>('person, 'world) wp_swap \<Rightarrow> 'world \<Rightarrow> ('person, 'world) handlungsabsicht \<Rightarrow> bool\<close>
where
  \<open>wohlgeformte_handlungsabsicht wps welt (Handlungsabsicht h) =
   (\<forall>p1 p2. h p1 welt = map_option (wps p2 p1) (h p2 (wps p1 p2 welt)))\<close>

declare wohlgeformte_handlungsabsicht.simps[simp del]

lemma wohlgeformte_handlungsabsicht_ausfuehrbar:
  \<open>wohlgeformte_handlungsabsicht wps welt ha \<Longrightarrow>
        \<forall>p1 p2. ausfuehrbar p1 welt ha \<longleftrightarrow> ausfuehrbar p2 (wps p1 p2 welt) ha\<close>
  apply(cases \<open>ha\<close>, simp add: wohlgeformte_handlungsabsicht.simps)
  by (metis ausfuehrbar.simps option.map_disc_iff)


lemma wohlgeformte_handlungsabsicht_mit_wpsid:
  \<open>wohlgeformte_handlungsabsicht wps welt ha \<Longrightarrow>
   wps_id wps welt \<Longrightarrow>
    \<forall>p1 p2. handeln p1 welt ha =
            map_handlung (wps p2 p1) (handeln p2 (wps p1 p2 welt) ha)\<close>
  apply(cases \<open>ha\<close>, simp add: wohlgeformte_handlungsabsicht.simps)
  apply(simp add: handeln_def nachher_handeln.simps)
  apply(safe)
   apply(simp add: wps_id_def; fail)
  apply(erule_tac x=\<open>p1\<close> in allE)
  apply(erule_tac x=\<open>p2\<close> in allE)
  apply(simp)
  apply(simp split: option.split)
  apply(simp add: wps_id_def)
  done


text\<open>Folgende Folgerung erklärt die Definition vermutlich besser:\<close>
lemma wohlgeformte_handlungsabsicht_wpsid_imp_handeln:
  \<open>wohlgeformte_handlungsabsicht wps welt ha \<Longrightarrow> wps_id wps welt \<Longrightarrow>
    (\<forall>p1 p2. handeln p1 welt ha =
                Handlung welt
                        (wps p2 p1 (nachher_handeln p2 (wps p1 p2 welt) ha)))\<close>
  apply(drule(1) wohlgeformte_handlungsabsicht_mit_wpsid)
  apply(cases \<open>ha\<close>, simp add: wohlgeformte_handlungsabsicht.simps handeln_def)
  done

lemma wfh_handeln_imp_wpsid:
  \<open>(\<forall>p1 p2. handeln p1 welt ha =
            map_handlung (wps p2 p1) (handeln p2 (wps p1 p2 welt) ha)) \<Longrightarrow>
  wps_id wps welt\<close>
  by(cases \<open>ha\<close>, simp add: wps_id_def handeln_def)

lemma wohlgeformte_handlungsabsicht_wpsid_simp:
  \<open>wohlgeformte_handlungsabsicht wps welt ha \<and> wps_id wps welt
  \<longleftrightarrow>
      (\<forall>p1 p2. ausfuehrbar p1 welt ha \<longleftrightarrow> ausfuehrbar p2 (wps p1 p2 welt) ha)
      \<and> (\<forall>p1 p2. handeln p1 welt ha =
                 map_handlung (wps p2 p1) (handeln p2 (wps p1 p2 welt) ha))\<close>
  apply(rule iffI)
  using wohlgeformte_handlungsabsicht_ausfuehrbar wohlgeformte_handlungsabsicht_mit_wpsid apply fast
  apply(rule conjI)
   prefer 2 using wfh_handeln_imp_wpsid apply fast
  apply(cases \<open>ha\<close>, simp add: wohlgeformte_handlungsabsicht.simps handeln_def nachher_handeln.simps)
  apply(intro allI, rename_tac h p1 p2)
  apply(case_tac \<open>h p2 (wps p1 p2 welt)\<close>)
   apply(simp)
   apply (metis ausfuehrbar.simps)
  apply(simp add: ausfuehrbar.simps)
  by (metis option.simps(5))
  


fun wohlgeformte_handlungsabsicht_gegenbeispiel
  :: \<open>('person, 'world) wp_swap \<Rightarrow> 'world \<Rightarrow> ('person, 'world) handlungsabsicht \<Rightarrow> 'person \<Rightarrow> 'person \<Rightarrow> bool\<close>
where
  \<open>wohlgeformte_handlungsabsicht_gegenbeispiel wps welt (Handlungsabsicht h) taeter opfer \<longleftrightarrow>
  h taeter welt \<noteq> map_option (wps opfer taeter) (h opfer (wps taeter opfer welt))\<close>

lemma \<open>wohlgeformte_handlungsabsicht_gegenbeispiel wps welt ha p1 p2 \<Longrightarrow>
        \<not>wohlgeformte_handlungsabsicht wps welt ha\<close>
  by(cases \<open>ha\<close>, auto simp add: wohlgeformte_handlungsabsicht.simps)

(*TODO: das sollte ein Homomorphismus sein.*)

(* das gilt nicht mehr! wpsid muss ich annehmen
lemma wohlgeformte_handlungsabsicht_imp_swpaid:
  \<open>wohlgeformte_handlungsabsicht wps welt h \<Longrightarrow>
    wps p1 p2 (wps p2 p1 welt) = welt\<close>
  by(simp add: wohlgeformte_handlungsabsicht_simp)
*)



(*<*)
text\<open>Wenn sich eine einfache Welt \<^typ>\<open>'w\<close> in eine komplexere Welt \<^typ>\<open>'zw\<close> übersetzen lässt,
(wobei die Übersetzung hier \<^term>\<open>C::'w \<Rightarrow> 'zw\<close> ist),
dann kann auch \<^const>\<open>wohlgeformte_handlungsabsicht\<close> mit übersetzt werden.\<close>
lemma wfh_generalize_worldI:
  fixes wps :: \<open>('person, 'w) wp_swap\<close>
    and welt :: \<open>'w\<close>
    and ha :: \<open>'person \<Rightarrow> 'w \<Rightarrow> 'w option\<close>
    and C :: \<open>'w \<Rightarrow> 'zw\<close>
  shows
\<open>wohlgeformte_handlungsabsicht wps welt (Handlungsabsicht (ha)) \<Longrightarrow>
  zwelt = C welt \<Longrightarrow>
  (\<And>p1 p2 w. zwps p1 p2 (C w) = C (wps p1 p2 w)) \<Longrightarrow>
  (\<And>p w. zha p (C w) =  map_option C (ha p w)) \<Longrightarrow>
wohlgeformte_handlungsabsicht zwps zwelt (Handlungsabsicht (zha))\<close>
  apply(simp)
  apply(simp add: wohlgeformte_handlungsabsicht.simps)
  apply(simp add: option.map_comp)
  apply(simp add: comp_def)
  by (smt (verit, best) map_option_is_None option.exhaust_sel option.map_sel)
(*>*)


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
    (\<forall>p1 p2. (ausfuehrbar p welt h \<and> ausfuehrbar p (wps p1 p2 welt) h)
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
  by (smt (verit) ausfuehrbar.simps fun_upd_same fun_upd_twist not_numeral_le_zero option.simps(3) person.distinct(5) swap_def)

  
  


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
   apply(erule_tac x=\<open>p1\<close> in allE)
   apply(erule_tac x=\<open>p2\<close> in allE)
   apply(erule_tac x=\<open>ha\<close> in allE)
   apply(simp add: nachher_handeln.simps handeln_def; fail)
  apply(intro allI)
  apply(case_tac \<open>ha\<close>)
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
  assumes wpsid: \<open>wps_id wps welt\<close>
  shows \<open>wohlgeformte_handlungsabsicht wps welt ha \<Longrightarrow>
  wpsm_kommutiert m wps welt \<Longrightarrow>
    okay m p2 (handeln p1 (wps p1 p2 welt) ha)
    \<longleftrightarrow>
    okay m p1 (handeln p2 welt ha)\<close>
  apply(cases \<open>ha\<close>, simp)
  apply(simp add: wpsm_kommutiert_def)
  apply(drule wohlgeformte_handlungsabsicht_wpsid_imp_handeln[OF _ wpsid])
  by simp

text\<open>Die Rückrichtung gilt auch,
aber da wir das für alle Handlungsabsichten in der Annahme brauchen,
ist das eher weniger hilfreich.\<close>
lemma wfh_kommutiert_wpsm:
  assumes wpsid: \<open>wps_id wps welt\<close>
  shows 
  \<open>\<forall>ha. wohlgeformte_handlungsabsicht wps welt ha \<and>
       (\<forall>p1 p2. okay m p2 (handeln p1 (wps p1 p2 welt) ha)
           \<longleftrightarrow>
           okay m p1 (handeln p2 welt ha)) \<Longrightarrow>
wpsm_kommutiert m wps welt\<close>
  apply(simp add: wpsm_kommutiert_def)
  apply(intro allI, rename_tac p1 p2 ha)
  apply(erule_tac x=\<open>ha\<close> in allE)
  apply(case_tac \<open>ha\<close>, simp)
  apply(erule conjE)
  apply(drule wohlgeformte_handlungsabsicht_wpsid_imp_handeln[OF _ wpsid])
  by simp


lemma wpsm_kommutiert_map_handlung:
  assumes wpsid: \<open>wps_id wps welt\<close>
    and wps_sym: \<open>wps p1 p2 welt = wps p2 p1 welt\<close>
  shows \<open>wpsm_kommutiert m wps (wps p1 p2 welt) \<Longrightarrow>
    okay m p1 (map_handlung (wps p1 p2) (handeln p1 welt ha))
    \<longleftrightarrow>
    okay m p2 (handeln p1 welt ha)\<close>
  apply(cases \<open>ha\<close>, simp)
  apply(simp add: wpsm_kommutiert_def)
  apply(erule_tac x=\<open>p1\<close> in allE)
  apply(erule_tac x=\<open>p2\<close> in allE)
  apply(simp add: handeln_def wpsid[simplified wps_id_def])
  by (metis wps_id_def wps_sym wpsid)

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

lemma ist_noop_map_handlung_wpsid:
  assumes strong_wps_id:
        \<open>\<forall>p1 p2 welt. wps p1 p2 (wps p1 p2 welt) = welt\<close>
  shows \<open>ist_noop (map_handlung (wps p1 p2) h) \<longleftrightarrow> ist_noop h\<close>
  apply(cases \<open>h\<close>, rename_tac vor nach, simp add: ist_noop_def)
  using strong_wps_id by metis

lemma ist_noop_wps:
  assumes wfh: \<open>wohlgeformte_handlungsabsicht wps welt ha\<close>
  and wps_id: \<open>wps_id wps welt\<close>
  and strong_wps_id: \<open>\<forall>p1 p2 welt. wps p1 p2 (wps p1 p2 welt) = welt\<close>
  shows \<open>ist_noop (handeln p2 (wps ich p2 welt) ha) \<longleftrightarrow> ist_noop (handeln ich welt ha)\<close>
proof -
  from wps_id have weak_wps_sym: \<open>\<forall>p1 p2. wps p1 p2 welt = wps p2 p1 welt\<close> by (metis strong_wps_id wps_id_def)
  from wohlgeformte_handlungsabsicht_wpsid_imp_handeln[OF wfh wps_id]
  have \<open>ist_noop (handeln ich welt ha)
        = ist_noop (Handlung welt (wps p2 ich (nachher_handeln p2 (wps ich p2 welt) ha)))\<close>
    by simp
  also have \<open>\<dots> = ist_noop (Handlung (wps ich p2 welt) (nachher_handeln p2 (wps ich p2 welt) ha))\<close>
    apply(simp add: ist_noop_def)
    using strong_wps_id weak_wps_sym by metis
  finally have \<open>ist_noop (handeln ich welt ha)
    = ist_noop (Handlung (wps ich p2 welt) (nachher_handeln p2 (wps ich p2 welt) ha))\<close> .
  thus \<open>?thesis\<close>
    by(simp add: handeln_def wps_id[simplified wps_id_def])
qed


(*>*)

end
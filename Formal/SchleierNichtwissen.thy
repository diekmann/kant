theory SchleierNichtwissen
imports BeispielPerson Handlung Maxime Swap
begin

section\<open>Schleier des Nichtwissens\<close>
text\<open>In diesem Abschnitt werden wir,
basierend auf der Idee von Rawls Schleier des Nitchwissens,
definieren, was eine wohlgeformte Handlungsabsicht und eine wohlgeformte Maxime sind.\<close>


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
type_synonym ('person, 'welt) wp_swap = \<open>'person \<Rightarrow> 'person \<Rightarrow> 'welt \<Rightarrow> 'welt\<close>

text\<open>Ein jeder \<^typ>\<open>('person, 'welt) wp_swap\<close> sollte mindestens folgendes erfüllen:\<close>
definition wps_id :: \<open>('person, 'welt) wp_swap \<Rightarrow> 'welt \<Rightarrow> bool\<close>
where
  \<open>wps_id wps welt \<equiv> \<forall>p1 p2. wps p2 p1 (wps p1 p2 welt) = welt\<close>


text_raw\<open>
\begin{equation*}
\begin{tikzcd}[column sep=14em, row sep=huge]
\textit{welt}
  \arrow[red, d, "\textit{wps}\ \textit{p1}\ \textit{p2}" near start]
  \arrow[blue, r, "\textit{handeln}\ \textit{p1}"]
& \textit{welt'} \\
\textit{alternativ-welt}
  \arrow[red, r, "\textit{handeln}\ \textit{p2}"]
& \textit{alternativ-welt'}
  \arrow[red, u, "\textit{wps}\ \textit{p1}\ \textit{p2}" near start]
\end{tikzcd}
\end{equation*}
\<close>

subsection\<open>Wohlgeformte Handlungsabsicht\<close>
text\<open>Wir sagen, eine Handlungsabsicht ist wohlgeformt,
genau dann wenn sie obiges kommutatives Diagramm erfüllt,
d.h. wenn folgendes equivalent ist
  \<^item> handeln in einer Welt.
  \<^item> zwei Personen in einer Welt zu vertauschen, in der veränderten Welt zu handeln,
    und die beiden Personen wieder zurück tauschen.\<close>

fun wohlgeformte_handlungsabsicht
  :: \<open>('person, 'welt) wp_swap \<Rightarrow> 'welt \<Rightarrow> ('person, 'welt) handlungsabsicht \<Rightarrow> bool\<close>
where
  \<open>wohlgeformte_handlungsabsicht wps welt (Handlungsabsicht h) =
   (\<forall>p1 p2. h p1 welt = map_option (wps p2 p1) (h p2 (wps p1 p2 welt)))\<close>

(*<*)
declare wohlgeformte_handlungsabsicht.simps[simp del]

lemma wohlgeformte_handlungsabsicht_ausfuehrbar:
  \<open>wohlgeformte_handlungsabsicht wps welt ha \<Longrightarrow>
        \<forall>p1 p2. ausfuehrbar p1 welt ha \<longleftrightarrow> ausfuehrbar p2 (wps p1 p2 welt) ha\<close>
  apply(cases \<open>ha\<close>, simp add: wohlgeformte_handlungsabsicht.simps)
  by (metis ausfuehrbar.simps option.map_disc_iff)


(*rueckrichtung gilt nicht*)
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
(*>*)


(*TODO: gilt die rueckrichting?*)
text\<open>Folgende Folgerung erklärt die Definition vermutlich besser:\<close>
lemma wohlgeformte_handlungsabsicht_wpsid_imp_handeln:
  \<open>wohlgeformte_handlungsabsicht wps welt ha \<Longrightarrow> wps_id wps welt \<Longrightarrow>
    (\<forall>p1 p2. handeln p1 welt ha =
                Handlung welt
                        (wps p2 p1 (nachher_handeln p2 (wps p1 p2 welt) ha)))\<close>
  apply(drule(1) wohlgeformte_handlungsabsicht_mit_wpsid)
  apply(cases \<open>ha\<close>, simp add: wohlgeformte_handlungsabsicht.simps handeln_def)
  done
(*TODO: das sollte ein Homomorphismus sein.*)

text\<open>Folgendes Lemma erlaubt es uns das kommutative Diagramm auch leicht anders zu zeichnen.\<close>
lemma wohlgeformte_handlungsabsicht_wpsid_wpssym_komm:
  assumes wpsid: \<open>\<forall>welt. wps_id wps welt\<close>
    and wps_sym: \<open>\<forall>welt. wps p1 p2 welt = wps p2 p1 welt\<close>
  shows \<open>wohlgeformte_handlungsabsicht wps (wps p1 p2 welt) ha \<Longrightarrow>
    handeln p1 (wps p1 p2 welt) ha =
            map_handlung (wps p1 p2) (handeln p2 welt ha)\<close>
  apply(drule wohlgeformte_handlungsabsicht_mit_wpsid)
  subgoal using wpsid by simp
  apply(erule_tac x=\<open>p1\<close> in allE)
  apply(erule_tac x=\<open>p2\<close> in allE)
  apply(subgoal_tac \<open>wps p1 p2 (wps p1 p2 welt) = welt\<close>)
   prefer 2
   apply (metis wps_id_def wps_sym wpsid)
  apply(simp add: )
  apply(subgoal_tac \<open>wps p2 p1 = wps p1 p2\<close>)
   prefer 2 using wps_sym apply presburger
  by simp

  text_raw\<open>
\begin{equation*}
\begin{tikzcd}[column sep=14em, row sep=huge]
\textit{welt}
  \arrow[blue, d, "\textit{wps}\ \textit{p1}\ \textit{p2}" near start]
  \arrow[red, r, "\textit{handeln}\ \textit{p2}"]
& \textit{welt'} 
  \arrow[red, d, "\textit{wps}\ \textit{p1}\ \textit{p2}" near start]\\
\textit{alternativ-welt}
  \arrow[blue, r, "\textit{handeln}\ \textit{p1}"]
& \textit{alternativ-welt'}
\end{tikzcd}
\end{equation*}
\<close>

(*<*)
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
  apply(clarsimp)
  apply(erule_tac x=\<open>p1\<close> in allE)
  apply(erule_tac x=\<open>p1\<close> in allE)
  apply(erule_tac x=\<open>p2\<close> in allE)
  apply(erule_tac x=\<open>p2\<close> in allE)
  apply(simp split: option.split_asm)
  done

lemma wohlgeformte_handlungsabsicht_ifI:
  \<open>wohlgeformte_handlungsabsicht wps welt (Handlungsabsicht h1) \<Longrightarrow>
   wohlgeformte_handlungsabsicht wps welt (Handlungsabsicht h2) \<Longrightarrow>
   (\<And>p1 p2. P p1 welt \<longleftrightarrow> P p2 (wps p1 p2 welt)) \<Longrightarrow>
   wohlgeformte_handlungsabsicht wps welt
      (Handlungsabsicht (\<lambda>ich welt. if P ich welt then h1 ich welt else h2 ich welt))\<close>
  by(simp add: wohlgeformte_handlungsabsicht.simps)
(*>*)


text\<open>In einigen späteren Beispielen möchten wir zeigen, dass bestimmte Handlungsabsichten
nicht wohlgeformt sind.\<close>
fun wohlgeformte_handlungsabsicht_gegenbeispiel
  :: \<open>('person, 'welt) wp_swap \<Rightarrow> 'welt \<Rightarrow> ('person, 'welt) handlungsabsicht \<Rightarrow> 'person \<Rightarrow> 'person \<Rightarrow> bool\<close>
where
  \<open>wohlgeformte_handlungsabsicht_gegenbeispiel wps welt (Handlungsabsicht h) taeter opfer \<longleftrightarrow>
  h taeter welt \<noteq> map_option (wps opfer taeter) (h opfer (wps taeter opfer welt))\<close>

lemma
  \<open>\<exists>p1 p2. wohlgeformte_handlungsabsicht_gegenbeispiel wps welt ha p1 p2 \<longleftrightarrow>
        \<not>wohlgeformte_handlungsabsicht wps welt ha\<close>
  apply(cases \<open>ha\<close>, simp add: wohlgeformte_handlungsabsicht.simps)
  by blast




(*<*)
text\<open>Assume we have a compound datatype, consisting of the parts selected by \<^term>\<open>sel\<close>
and the parts selected by \<^term>\<open>sel_other\<close>.
Together, they build the complete datatype.
But we can reason about \<^const>\<open>map_option\<close> equivalence in isolation.\<close>
lemma datatype_split_map_option_equal:
  \<open>map_option sel w1 = map_option sel w2 \<Longrightarrow>
   (\<And> w. makeZ (sel w) (sel_other w) = w) \<Longrightarrow>
   map_option sel_other w1 = map_option sel_other w2 \<Longrightarrow>
  w1 = w2\<close>
  by (metis (no_types, lifting) None_eq_map_option_iff option.exhaust_sel option.map_sel)

text\<open>Assume we have a compound complex world \<^typ>\<open>'zw\<close>.
Assume we have a simpler sub-world \<^typ>\<open>'w\<close>.
Assume we have a Handlungsabsicht in this simpler sub-world \<^term_type>\<open>ha :: 'person \<Rightarrow> 'w \<Rightarrow> 'w option\<close>
which only modifies the sub-world.
Then we can lift \<^const>\<open>wohlgeformte_handlungsabsicht\<close> from the sub-world to the compound world.

\<^term>\<open>makeZ\<close> is basically the constructor which combines the simpler sub-world with other stuff
to the complicated compound world.

The \<^term_type>\<open>sel :: 'zw \<Rightarrow> 'w\<close> selects the parts of the compound world which are modified.
The \<^term_type>\<open>sel_other :: 'zw \<Rightarrow> 'a\<close> selects the parts of the compound world which are not modified.\<close>
  lemma wfh_generalize_worldI:
  fixes wps :: \<open>('person, 'w) wp_swap\<close> \<comment>\<open>swap in the simple world\<close>
    and zwps :: \<open>('person, 'zw) wp_swap\<close> \<comment>\<open>swap in the compound world\<close>
    and welt :: \<open>'w\<close> \<comment>\<open>the simple world\<close>
    and zwelt :: \<open>'zw\<close> \<comment>\<open>the compound world\<close>
    and ha :: \<open>'person \<Rightarrow> 'w \<Rightarrow> 'w option\<close>
    and sel :: \<open>'zw \<Rightarrow> 'w\<close> \<comment>\<open>selects the parts from the compound wold which are modified.\<close>
    and makeZ :: \<open>'w \<Rightarrow> 'other \<Rightarrow> 'zw\<close> \<comment>\<open>builds the compound world from the simple world and other stuff\<close>
  assumes wf_ha: \<open>wohlgeformte_handlungsabsicht wps welt (Handlungsabsicht ha)\<close>
  and     sel_welt: \<open>sel zwelt = welt\<close>
  and     sel_wps: \<open>\<And>p1 p2 zw. wps p1 p2 (sel zw) = sel (zwps p1 p2 zw)\<close>
  and     sel_ha: \<open>\<And>p zw. ha p (sel zw) = map_option sel (zha p zw)\<close>
  and     make_whole: \<open>\<And> w. makeZ (sel w) (sel_other w) = w\<close>

  and not_touches_other:
      \<open>\<And>p welt welt'. zha p welt = Some welt' \<Longrightarrow> sel_other welt' = sel_other welt\<close>
  and iff_None: \<open>\<And>p1 p2 welt. zha p1 welt = None \<longleftrightarrow> zha p2 (zwps p1 p2 welt) = None\<close>
  and makeZ_pullout:
    \<open>\<And>p1 p2 a b. makeZ (sel (zwps p2 p1 a)) (sel_other (zwps p2 p1 b)) = zwps p2 p1 (makeZ (sel a) (sel_other b))\<close>
  and wpsid: \<open>\<And> welt p1 p2. zwps p2 p1 (zwps p1 p2 welt) = welt\<close>
  and wps_sym: \<open>\<And>welt p1 p2. zwps p1 p2 welt = zwps p2 p1 welt\<close>

  shows
    \<open>wohlgeformte_handlungsabsicht zwps zwelt (Handlungsabsicht zha)\<close>
proof -         
  from wf_ha sel_welt sel_wps sel_ha have wohlgeformt_sel:
    \<open>map_option sel (zha p1 zwelt) = map_option sel (map_option (zwps p2 p1) (zha p2 (zwps p1 p2 zwelt)))\<close>
    for p1 p2
    apply(simp add: wohlgeformte_handlungsabsicht.simps)
    apply(clarsimp)
    apply(erule_tac x=\<open>p1\<close> in allE)
    apply(erule_tac x=\<open>p2\<close> in allE)
    apply(simp add: option.map_comp)
    apply(subgoal_tac \<open>wps p2 p1 \<circ> sel = sel \<circ> zwps p2 p1\<close>)
     prefer 2
     apply fastforce
    apply(simp)
    done

  have wohlgeformt_sel_on_wps_zwelt:
    \<open>map_option sel (zha p2 (zwps p1 p2 zwelt)) =
      map_option sel (map_option (zwps p1 p2) (zha p1 (zwps p2 p1 (zwps p1 p2 zwelt))))\<close>
    for p2 p1
    using wohlgeformt_sel[of \<open>p1\<close> \<open>p2\<close>]
    apply(simp add: wpsid)
    apply(cases \<open>zha p1 zwelt\<close>)
     apply(simp; fail)
    apply(cases \<open>zha p2 (zwps p1 p2 zwelt)\<close>)
     apply(simp; fail)
    apply(simp)
    by (metis wpsid sel_wps)

  from wps_sym have not_touches_other_wps:
    \<open>zha p2 (zwps p1 p2 welt) = Some welt'
                          \<Longrightarrow> sel_other welt' = sel_other (zwps p2 p1 welt)\<close>
    for p1 p2 welt welt'
    using not_touches_other[of \<open>p2\<close> \<open>(zwps p1 p2 welt)\<close>] by simp

  have wpsid': \<open>zwps p2 p1 (zwps p2 p1 w) = w\<close> for w p1 p2
    using wps_sym wpsid by simp

  have sel_wps_propagate:
    \<open>zha p2 (zwps p1 p2 zwelt) = Some welt'
      \<Longrightarrow> sel welt' = sel (the (map_option (zwps p2 p1) (zha p1 zwelt)))\<close>
    for welt' p1  p2
    using wohlgeformt_sel_on_wps_zwelt[of \<open>p2\<close> \<open>p1\<close>]
    apply(simp add: wpsid)
    apply(case_tac \<open>zha p1 zwelt\<close>)
     apply(simp; fail)
    apply(simp)
    using wps_sym by presburger

  have sel_other_makeZ:
    \<open>zha p1 zwelt = Some welt' \<Longrightarrow>
       sel_other zwelt = sel_other (makeZ (sel welt') (sel_other zwelt))\<close>
    for welt' p1
    apply -
    apply(drule not_touches_other[symmetric])
    using make_whole[of \<open>welt'\<close>] by simp

  have wohlgeformt_sel_other:
    \<open>map_option sel_other (zha p1 zwelt) =
                 map_option sel_other (map_option (zwps p2 p1) (zha p2 (zwps p1 p2 zwelt)))\<close>
    for p1 p2
  proof -
    let \<open>?w\<close>=\<open>zha p2 (zwps p1 p2 zwelt)\<close>
    let \<open>?ignoreMe\<close>=\<open>case ?w of Some w \<Rightarrow> sel w\<close>
  
    have ignoreMe: \<open>?w \<noteq> None \<Longrightarrow> makeZ ?ignoreMe (sel_other (the ?w)) = the ?w\<close>
      apply (cases \<open>?w\<close>)
       apply(simp; fail)
      apply(simp)
      using make_whole by simp
  
    have shuffle_sel:
      \<open>map_option (sel_other \<circ> zwps p2 p1) ?w =
        map_option (sel_other \<circ> zwps p2 p1 \<circ> (\<lambda>other. makeZ ?ignoreMe other) \<circ> sel_other) ?w\<close>
      for p1 p2
      apply(cases \<open>?w\<close>)
       apply(simp; fail)
      apply(simp)
      using ignoreMe by simp

    show \<open>?thesis\<close>
    apply(cases \<open>zha p1 zwelt\<close>)
     apply(simp)
     using iff_None apply blast
    apply(simp add: not_touches_other[of \<open>p1\<close>])
     apply(simp add: option.map_comp)
    apply(subst shuffle_sel)
    apply(case_tac \<open>zha p2 (zwps p1 p2 zwelt)\<close>)
     apply(simp)
     using iff_None apply force
    apply(simp)
    apply(frule not_touches_other_wps, simp)
    apply(simp add: sel_wps_propagate)
    apply(simp add: makeZ_pullout)
    apply(simp add: wpsid')
     using sel_other_makeZ by simp
 qed

  from datatype_split_map_option_equal[OF wohlgeformt_sel make_whole wohlgeformt_sel_other] make_whole have
    \<open>(zha p1 zwelt) = (map_option (zwps p2 p1) (zha p2 (zwps p1 p2 zwelt)))\<close>
    for p1 p2
    by simp
  then show \<open>?thesis\<close>
  by(simp add: wohlgeformte_handlungsabsicht.simps )
qed

(*TODO: can we derive wfh_generalize_world_ConstrI from wfh_generalize_worldI?*)
thm wfh_generalize_worldI[where makeZ=\<open>\<lambda>w other. C w\<close> and sel=\<open>\<lambda>zw. (inv C) zw\<close>
                                and zha=\<open>zha\<close> and zwelt=\<open>C welt\<close> and zwps=\<open>zwps\<close>]
lemma \<open>inj C \<Longrightarrow> inv C (C welt) = welt\<close> by(simp)

text\<open>Wenn sich eine einfache Welt \<^typ>\<open>'w\<close> in eine komplexere Welt \<^typ>\<open>'zw\<close> übersetzen lässt,
(wobei die Übersetzung hier \<^term>\<open>C::'w \<Rightarrow> 'zw\<close> ist),
dann kann auch \<^const>\<open>wohlgeformte_handlungsabsicht\<close> mit übersetzt werden.

This is basically @{thm wfh_generalize_worldI}, but instead of \<^term>\<open>sel\<close>,
we have the opposite: Constructor \<^term>\<open>C\<close>.\<close>
lemma wfh_generalize_world_ConstrI:
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
  apply(clarsimp)
  apply(erule_tac x=\<open>p1\<close> in allE)
  apply(erule_tac x=\<open>p2\<close> in allE)
  apply(simp)
  apply(simp add: option.map_comp)
  apply(simp add: comp_def)
  done
(*>*)


subsection\<open>Spezialfall: Maxime und Handlungsabsichten haben nette Eigenschaften\<close>
text\<open>Dieses Kapitel darf gerne übersprungen werden,
da der Spezialfall nur in bestimmten Beweisen interessant wird.\<close>

text\<open>Nach der gleichen Argumentation müssten Maxime und Handlungsabsicht so generisch sein,
dass sie in allen Welten zum gleichen Ergebnis kommen.
Dies gilt jedoch nicht immer.
Wenn dieser Sonderfall eintritt sagen wir, Maxime und Handlungsabsicht generalisieren.\<close>
definition maxime_und_handlungsabsicht_generalisieren
  :: \<open>('person, 'welt) wp_swap \<Rightarrow> 'welt \<Rightarrow> 
      ('person, 'welt) maxime \<Rightarrow> ('person, 'welt) handlungsabsicht \<Rightarrow> 'person \<Rightarrow> bool\<close>
where
  \<open>maxime_und_handlungsabsicht_generalisieren wps welt m ha p =
    (\<forall>p1 p2. (ausfuehrbar p welt ha \<and> ausfuehrbar p (wps p1 p2 welt) ha)
              \<longrightarrow> okay m p (handeln p welt ha) \<longleftrightarrow> okay m p (handeln p (wps p1 p2 welt) ha))\<close>
text\<open>Die Vorbedingungen in obiger Definition,
nämlich dass die Handlungsabsicht \<^const>\<open>ausfuehrbar\<close> ist,
ist nötig, um z.B. Handlungsabsichten wie das Stehlen zu ermöglichen;
jedoch gibt es beim Stehlen genau den pathologischen Grenzfall von-sich-selbst Stehlen,
welcher in einer No-Op endet und das Ergebnis damit nicht moralisch falsch ist.
Durch die Einschränkung auf \<^const>\<open>ausfuehrbar\<close> Fälle lassen sich solche pathologischen Grenzfälle
ausklammern.\<close>

text\<open>Für eine gegebene Maxime schließt die Forderung
\<^const>\<open>maxime_und_handlungsabsicht_generalisieren\<close> leider einige Handlungen aus.
Beispiel:
In einer Welt besitzt \<^const>\<open>Alice\<close> 2 und \<^const>\<open>Eve\<close> hat 1 Schulden.
Die Maxime ist, dass Individuen gerne keinen Besitz verlieren.
Die Handlung sei ein globaler reset, bei dem jeden ein Besitz von 0 zugeordnet wird.
Leider generalisiert diese Handlung nicht, da \<^const>\<open>Eve\<close> die Handlung gut findet,
\<^const>\<open>Alice\<close> allerdings nicht.
\<close>
beispiel
   \<open>\<not> maxime_und_handlungsabsicht_generalisieren
      swap
      ((\<lambda>x. 0)(Alice := (2::int), Eve := - 1))
      (Maxime (\<lambda>ich h. (vorher h) ich \<le> (nachher h) ich))
      (Handlungsabsicht (\<lambda>ich w. Some (\<lambda>_. 0)))
      Eve\<close>
  apply(simp add: maxime_und_handlungsabsicht_generalisieren_def )
  apply(simp add: ist_noop_def fun_eq_iff handeln_def nachher_handeln.simps)
  by(code_simp)

(*<*)
lemma maxime_und_handlungsabsicht_generalisieren_MaximeConj:
  \<open>maxime_und_handlungsabsicht_generalisieren wps welt m1 ha p
    \<and> maxime_und_handlungsabsicht_generalisieren wps welt m2 ha p
  \<Longrightarrow>maxime_und_handlungsabsicht_generalisieren wps welt (MaximeConj m1 m2) ha p\<close>
  apply(simp add: maxime_und_handlungsabsicht_generalisieren_def okay_MaximeConj)
  apply(clarsimp)
  done

(*there is an \<and> in there, not an \<or>*)
lemma maxime_und_handlungsabsicht_generalisieren_MaximeDisj_Conj:
  \<open>maxime_und_handlungsabsicht_generalisieren wps welt m1 ha p
    \<and> maxime_und_handlungsabsicht_generalisieren wps welt m2 ha p
    \<Longrightarrow> maxime_und_handlungsabsicht_generalisieren wps welt (MaximeDisj m1 m2) ha p\<close>
  apply(simp add: maxime_und_handlungsabsicht_generalisieren_def okay_MaximeDisj)
  apply(clarsimp)
  done
(*>*)
  
  


text\<open>Die Maxime und \<^typ>\<open>('person, 'welt) wp_swap\<close> können einige Eigenschaften erfüllen.

Wir kürzen das ab mit \<^term>\<open>wpsm :: ('person, 'welt) wp_swap\<close>: Welt Person Swap Maxime.\<close>

text\<open>Die Person für die Maxime ausgewertet wird und swappen der Personen in der Welt
kann equivalent sein:\<close>
definition wpsm_kommutiert
  :: \<open>('person, 'welt) maxime \<Rightarrow> ('person, 'welt) wp_swap \<Rightarrow> 'welt \<Rightarrow> bool\<close>
where
  \<open>wpsm_kommutiert m wps welt \<equiv>
  \<forall> p1 p2 ha.
    okay m p2 (handeln p1 (wps p1 p2 welt) ha)
    \<longleftrightarrow>
    okay m p1 (Handlung welt (wps p1 p2 (nachher_handeln p1 (wps p2 p1 welt) ha)))\<close>

(*<*)
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
(*>*)

text\<open>Wenn sowohl eine \<^const>\<open>wohlgeformte_handlungsabsicht\<close> vorliegt,
als auch \<^const>\<open>wpsm_kommutiert\<close>,
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

(*<*)
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
(*>*)


subsection\<open>Wohlgeformte Maxime\<close>
text\<open>Nach dem gleichen Konzept nach dem wir die \<^const>\<open>wohlgeformte_handlungsabsicht\<close>
definiert haben,
definieren wir, was es bedeutet für eine Maxime wohlgeformt zu sein.\<close>

(*Eigentlich sollte das fuer alle Handlungen gelten, aber wenn ich ausfuehrbaren code will
habe ich ein Problem, dass Handlungen nicht enumerable sind.*)
definition wohlgeformte_maxime_auf
  :: \<open>'welt handlung \<Rightarrow> ('person, 'welt) wp_swap \<Rightarrow> ('person, 'welt) maxime \<Rightarrow> bool\<close>
where
  \<open>wohlgeformte_maxime_auf h wps m \<equiv>
    \<forall>p1 p2. okay m p1 h \<longleftrightarrow> okay m p2 (map_handlung (wps p1 p2) h)\<close>

text\<open>Eigentlich sollte eine Maxime wohlgeformte sein für alle Handlungen.
Jedoch definieren wir hier eine restriktive Version \<^const>\<open>wohlgeformte_maxime_auf\<close> welche
nur auf einer Handlung wohlgeformt ist.
Der Grund ist leider ein Implementierungsdetail.
Da wir ausführbaren Code wollen und Handlungen normalerweise nicht vollständig
aufzählbar sind, werden wir auch den kategorischen Imperativ auf eine endliche Menge
von Handlungsabsichten beschränken.
Die eigentlich schönere (jedoch schwer zu beweisende) Forderung lautet:\<close>

definition wohlgeformte_maxime
  :: \<open>('person, 'welt) wp_swap \<Rightarrow> ('person, 'welt) maxime \<Rightarrow> bool\<close>
where
  \<open>wohlgeformte_maxime wps m \<equiv>
    \<forall>h. wohlgeformte_maxime_auf h wps m\<close>


text\<open>Beispiel:\<close>
beispiel \<open>wohlgeformte_maxime swap (Maxime (\<lambda>ich h. (vorher h) ich \<le> (nachher h) ich))\<close>
  apply(simp add: wohlgeformte_maxime_def wohlgeformte_maxime_auf_def)
  apply(intro allI, case_tac \<open>h\<close>, simp)
  by (metis swap_a swap_symmetric)
  

(*
aus wpsm_kommutiert koennen wir FAST wohlgeformte_maxime_auf ableiten.
Leider muss pX=p2.
lemma
  assumes wpsid: \<open>wps_id wps welt\<close>
    and wps_sym: \<open>\<forall>p1 p2. wps p1 p2 = wps p2 p1\<close>
  shows \<open>(\<forall>p1 p2::'person. wpsm_kommutiert m wps (wps p1 p2 welt)) \<Longrightarrow>
    wohlgeformte_maxime_auf (handeln (pX::'person) welt ha) wps m\<close>
  apply(simp add: wohlgeformte_maxime_auf_def)
  apply(clarsimp)
  apply(erule_tac x=p2 in allE)
  apply(erule_tac x=p1 in allE)
  apply(subgoal_tac "wps p2 p1 welt = wps p1 p2 welt")
  prefer 2 subgoal using wps_sym by simp
  apply(drule(1) wpsm_kommutiert_map_handlung[OF wpsid, where ha=ha])
  apply(case_tac "pX=p2")
   apply(simp add: wps_sym; fail)
  apply(simp)
  oops
*)

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
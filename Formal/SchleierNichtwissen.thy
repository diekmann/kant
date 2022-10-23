theory SchleierNichtwissen
imports Main BeispielPerson Handlung Maxime
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

Beispielweise ist folgende Handlungsabsicht ungültig:
\<^term>\<open>\<lambda>ich welt. if ich = Alice then Do_A welt else Do_B welt\<close>

Handlungsabsichten und Maximen müssen immer generisch geschrieben werden,
so dass die handelnden und betroffenen Personen niemals anhand ihres Namens ausgewählt werden.

unser Modell von Handlungsabsichten und Maximen stellt beispielweise die
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

text\<open>Für jede Welt muss eine Welt-Personen Swap Funktion bereit gestellt werden,
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



definition wohlgeformte_handlungsabsicht
  :: \<open>('person, 'world) wp_swap \<Rightarrow> 'world \<Rightarrow> ('person, 'world) handlungF \<Rightarrow> bool\<close>
where
  \<open>wohlgeformte_handlungsabsicht welt_personen_swap welt h \<equiv>
    \<forall>p1 p2. (handeln p1 welt h) =
            map_handlung (welt_personen_swap p2 p1) (handeln p2 (welt_personen_swap p1 p2 welt) h)\<close>

(*TODO: das sollte ein Homomorphismus sein. Biled hier.*)

text\<open>Nach der gleichen Argumentation müssen Maxime und Handlungsabsicht so generisch sein,
dass sie in allen Welten zum gleichen Ergebnis kommen.\<close>
definition maxime_und_handlungsabsicht_generalisieren
  :: \<open>('person, 'world) maxime \<Rightarrow> ('person, 'world) handlungF \<Rightarrow> 'person \<Rightarrow> bool\<close>
where
  \<open>maxime_und_handlungsabsicht_generalisieren m h p =
    (\<forall>w1 w2. okay m p (handeln p w1 h) \<longleftrightarrow> okay m p (handeln p w2 h))\<close>


text\<open>Die Maxime und \<^typ>\<open>('person, 'world) wp_swap\<close> müssen einige Eigenschaften erfülem.
Wir kürzen das ab mit wpsm: Welt Person Swap Maxime.\<close>

text\<open>Die Person für die Maxime ausgewertet wurd und swappen der Personen in der Welt
muss equivalent sein:\<close>
definition wpsm_kommutiert
  :: \<open>('person, 'world) maxime \<Rightarrow> ('person, 'world) wp_swap \<Rightarrow> 'world \<Rightarrow> bool\<close>
where
  \<open>wpsm_kommutiert m welt_personen_swap welt \<equiv>
\<forall> p1 p2 h.
  okay m p2 (Handlung (welt_personen_swap p1 p2 welt) (h p1 (welt_personen_swap p1 p2 welt)))
  \<longleftrightarrow>
  okay m p1 (Handlung welt (welt_personen_swap p1 p2 (h p1 (welt_personen_swap p2 p1 welt))))\<close>

lemma \<open>wpsm_kommutiert m welt_personen_swap welt =
(\<forall> p1 p2 h.
  okay m p2 (handeln p1 (welt_personen_swap p1 p2 welt) (HandlungF h))
  \<longleftrightarrow>
  okay m p1 (handeln p1 welt (HandlungF (\<lambda>p w. welt_personen_swap p1 p2 (h p (welt_personen_swap p2 p1 w)))))
)\<close>
  by(simp add: wpsm_kommutiert_def)

text\<open>Die Auswertung der Maxime für eine bestimme Person muss unabhänging
vom swappen von zwei unbeteiligten Personen sein.\<close>
definition wpsm_unbeteiligt1
  :: \<open>('person, 'world) maxime \<Rightarrow> ('person, 'world) wp_swap \<Rightarrow> 'world \<Rightarrow> bool\<close>
where
  \<open>wpsm_unbeteiligt1 m welt_personen_swap welt \<equiv>
\<forall> p1 p2 pX welt'.
  p1 \<noteq> p2 \<longrightarrow> pX \<noteq> p1 \<longrightarrow> pX \<noteq> p2 \<longrightarrow> 
    okay m pX (Handlung (welt_personen_swap p2 p1 welt) welt')
    \<longleftrightarrow>
    okay m pX (Handlung welt welt')\<close>

definition wpsm_unbeteiligt2
  :: \<open>('person, 'world) maxime \<Rightarrow> ('person, 'world) wp_swap \<Rightarrow> 'world \<Rightarrow> bool\<close>
where
  \<open>wpsm_unbeteiligt2 m welt_personen_swap welt \<equiv>
\<forall> p1 p2 pX h (welt'::'world).
  p1 \<noteq> p2 \<longrightarrow> pX \<noteq> p1 \<longrightarrow> pX \<noteq> p2 \<longrightarrow>
    okay m pX (Handlung welt (welt_personen_swap p1 p2 (h p1 welt')))
    \<longleftrightarrow>
    okay m pX (Handlung welt (h p1 welt'))\<close>
  


end
theory Simulation
imports Gesetz Handlung KategorischerImperativ
begin

section\<open>Simulation\<close>
text\<open>Gegeben eine handelnde Person und eine Maxime,
wir wollen simulieren was für ein allgemeines Gesetz abgeleitet werden könnte.\<close>


datatype ('person, 'world, 'a, 'b) simulation_constants = SimConsts
    \<open>'person\<close> \<comment> \<open>handelnde Person\<close>
    \<open>('person, 'world) maxime\<close>
    \<open>('world, 'a, 'b) allgemeines_gesetz_ableiten\<close>

    (*moeglich :: H.Handlung world -> Bool, -- brauch ich das oder geht das mit typen?*)


text\<open>...\<close>
(*<*)

text\<open>Simulate one \<^typ>\<open>('person, 'world) handlungsabsicht\<close> once:\<close>
fun simulate_handlungsabsicht
    :: \<open>('person, 'world, 'a, 'b) simulation_constants \<Rightarrow>
        ('person, 'world) handlungsabsicht \<Rightarrow> 'world \<Rightarrow> (nat, 'a, 'b) gesetz
        \<Rightarrow> ('world \<times> (nat, 'a, 'b) gesetz)\<close>
  where
    \<open>simulate_handlungsabsicht (SimConsts person maxime aga) ha welt g =
    (let (sollensanordnung, g') = moarlisch_gesetz_ableiten person welt maxime ha aga g in
      let w' = (if sollensanordnung = Erlaubnis
                then
                  nachher (handeln person welt ha)
                else
                  welt
               ) in
      (w', g')
    )\<close>

lemma \<open>simulate_handlungsabsicht
       (SimConsts
          ()
          (Maxime (\<lambda>_ _. True))
          (\<lambda>h s. Rechtsnorm (Tatbestand h) (Rechtsfolge ''count'')))
       (Handlungsabsicht (\<lambda>p w. w+1))
       (32::int)
       (Gesetz {})= 
  (33,
   Gesetz
    {(\<section> (Suc 0), Rechtsnorm (Tatbestand (Handlung 32 33)) (Rechtsfolge ''count''))})\<close>
  by eval

text\<open>Funktion begrenzt oft anwenden bis sich die Welt nicht mehr ändert.
Parameter
 \<^item> Funktion
 \<^item> Maximale Anzahl Iterationen (Simulationen)
 \<^item> Initialwelt
 \<^item> Initialgesetz
\<close>
fun converge
    :: \<open>('world \<Rightarrow> 'gesetz \<Rightarrow> ('world \<times> 'gesetz)) \<Rightarrow> nat \<Rightarrow> 'world \<Rightarrow> 'gesetz \<Rightarrow> ('world \<times> 'gesetz)\<close>
  where
      \<open>converge _ 0         w g = (w, g)\<close>
    | \<open>converge f (Suc its) w g =
        (let (w', g') = f w g in
          if w = w' then
            (w, g')
          else
            converge f its w' g')\<close>

text\<open>Example: Count 32..42,
      where \<^term>\<open>32::int\<close> is the initial world and we do \<^term>\<open>10::nat\<close> iterations.\<close>
lemma \<open>converge (\<lambda>w g. (w+1, w#g)) 10 (32::int) ([]) =
        (42, [41, 40, 39, 38, 37, 36, 35, 34, 33, 32])\<close> by eval

text\<open>simulate one \<^typ>\<open>('person, 'world) handlungsabsicht\<close> a few times\<close>
definition simulateOne
    :: \<open>('person, 'world, 'a, 'b) simulation_constants \<Rightarrow>
        nat \<Rightarrow> ('person, 'world) handlungsabsicht \<Rightarrow> 'world \<Rightarrow> (nat, 'a, 'b) gesetz
        \<Rightarrow> (nat, 'a, 'b) gesetz\<close>
    where
    \<open>simulateOne simconsts i ha w g \<equiv>
      let (welt, gesetz) = converge (simulate_handlungsabsicht simconsts ha) i w g in
            gesetz\<close>
(*>*)
text\<open>...
Die Funktion \<^const>\<open>simulateOne\<close> nimmt
eine Konfiguration \<^typ>\<open>('person, 'world, 'a, 'b) simulation_constants\<close>,
eine Anzahl an Iterationen die durchgeführt werden sollen,
eine Handlung,
eine Initialwelt,
ein Initialgesetz,
und gibt das daraus resultierende Gesetz nach so vielen Iterationen zurück.


Beispiel:
Wir nehmen die mir-ist-alles-egal Maxime.
Wir leiten ein allgemeines Gesetz ab indem wir einfach nur die Handlung wörtlich ins Gesetz
übernehmen.
Wir machen \<^term>\<open>10\<close> Iterationen.
Die Welt ist nur eine Zahl und die initiale Welt sei \<^term>\<open>32\<close>.
Die Handlung ist es diese Zahl um Eins zu erhöhen,
Das Ergebnis der Simulation ist dann, dass wir einfach von \<^term>\<open>32\<close> bis \<^term>\<open>42\<close> zählen.\<close>
lemma \<open>simulateOne
        (SimConsts () (Maxime (\<lambda>_ _. True)) (\<lambda>h s. Rechtsnorm (Tatbestand h) (Rechtsfolge ''count'')))
        10 (Handlungsabsicht (\<lambda>p n. Suc n))
        32
        (Gesetz {}) =
  Gesetz
  {(\<section> 10, Rechtsnorm (Tatbestand (Handlung 41 42)) (Rechtsfolge ''count'')),
   (\<section> 9, Rechtsnorm (Tatbestand (Handlung 40 41)) (Rechtsfolge ''count'')),
   (\<section> 8, Rechtsnorm (Tatbestand (Handlung 39 40)) (Rechtsfolge ''count'')),
   (\<section> 7, Rechtsnorm (Tatbestand (Handlung 38 39)) (Rechtsfolge ''count'')),
   (\<section> 6, Rechtsnorm (Tatbestand (Handlung 37 38)) (Rechtsfolge ''count'')),
   (\<section> 5, Rechtsnorm (Tatbestand (Handlung 36 37)) (Rechtsfolge ''count'')),
   (\<section> 4, Rechtsnorm (Tatbestand (Handlung 35 36)) (Rechtsfolge ''count'')),
   (\<section> 3, Rechtsnorm (Tatbestand (Handlung 34 35)) (Rechtsfolge ''count'')),
   (\<section> 2, Rechtsnorm (Tatbestand (Handlung 33 34)) (Rechtsfolge ''count'')),
   (\<section> 1, Rechtsnorm (Tatbestand (Handlung 32 33)) (Rechtsfolge ''count''))}\<close>
  by eval


text\<open>Eine Iteration der Simulation liefert genau einen Paragraphen im Gesetz:\<close>
lemma \<open>\<exists>tb rf. 
  simulateOne
    (SimConsts person maxime gesetz_ableiten)
    1 handlungsabsicht
    initialwelt
    (Gesetz {})
  = Gesetz {(\<section> 1, Rechtsnorm (Tatbestand tb) (Rechtsfolge rf))}\<close>
  apply(simp add: simulateOne_def moarlisch_gesetz_ableiten_def)
  apply(case_tac \<open>maxime\<close>, simp)
  apply(simp add: moralisch_unfold max_paragraph_def)
  apply(intro conjI impI)
  by(metis rechtsfolge.exhaust rechtsnorm.exhaust tatbestand.exhaust)+
end
theory Simulation
imports Gesetz Handlung Kant
begin

section\<open>Simulation\<close>
text\<open>Gegeben eine handelnde Person und eine Maxime,
wir wollen simulieren was für ein allgemeines Gesetz abgeleitet werden könnte.\<close>


datatype ('person, 'world, 'a, 'b) simulation_constants = SimConsts
    'person \<comment> \<open>handelnde Person\<close>
    "('person, 'world) maxime"
    "('world, 'a, 'b) allgemeines_gesetz_ableiten"

    (*moeglich :: H.Handlung world -> Bool, -- brauch ich das oder geht das mit typen?*)


text\<open>...\<close>
(*<*)

text\<open>Simulate one \<^typ>\<open>('person, 'world) handlungF\<close> once:\<close>
fun simulate_handlungF
    :: "('person, 'world, 'a, 'b) simulation_constants \<Rightarrow>
        ('person, 'world) handlungF \<Rightarrow> 'world \<Rightarrow> (nat, 'a, 'b) gesetz
        \<Rightarrow> ('world \<times> (nat, 'a, 'b) gesetz)"
  where
    "simulate_handlungF (SimConsts person maxime aga) h welt g =
    (let (sollensanordnung, g') = kategorischer_imperativ person welt h maxime aga g in
      let w' = (if sollensanordnung = Erlaubnis
                then
                  nachher (handeln person welt h)
                else
                  welt
               ) in
      (w', g')
    )"

lemma \<open>simulate_handlungF
       (SimConsts
          ()
          (Maxime (\<lambda>_ _. True))
          (\<lambda>h s. Rechtsnorm (Tatbestand h) (Rechtsfolge ''count'')))
       (HandlungF (\<lambda>p w. w+1))
       (32::int)
       (Gesetz {})= 
  (33,
   Gesetz
    {(Paragraph (Suc 0), Rechtsnorm (Tatbestand (Handlung 32 33)) (Rechtsfolge ''count''))})\<close>
  by eval

text\<open>Funktion begrenzt oft anwenden bis sich die Welt nicht mehr ändert.
Parameter
 \<^item> Funktion
 \<^item> Maximale Anzahl Iterationen (Simulationen)
 \<^item> Initialwelt
 \<^item> Initialgesetz
\<close>
fun converge
    :: "('world \<Rightarrow> 'gesetz \<Rightarrow> ('world \<times> 'gesetz)) \<Rightarrow> nat \<Rightarrow> 'world \<Rightarrow> 'gesetz \<Rightarrow> ('world \<times> 'gesetz)"
  where
      "converge _ 0         w g = (w, g)"
    | "converge f (Suc its) w g =
        (let (w', g') = f w g in
          if w = w' then
            (w, g')
          else
            converge f its w' g')"

text\<open>Example: Count 32..42,
      where \<^term>\<open>32::int\<close> is the initial world and we do \<^term>\<open>10::nat\<close> iterations.\<close>
lemma \<open>converge (\<lambda>w g. (w+1, w#g)) 10 (32::int) ([]) =
        (42, [41, 40, 39, 38, 37, 36, 35, 34, 33, 32])\<close> by eval

text\<open>simulate one \<^typ>\<open>('person, 'world) handlungF\<close> a few times\<close>
definition simulateOne
    :: "('person, 'world, 'a, 'b) simulation_constants \<Rightarrow>
        nat \<Rightarrow> ('person, 'world) handlungF \<Rightarrow> 'world \<Rightarrow> (nat, 'a, 'b) gesetz
        \<Rightarrow> (nat, 'a, 'b) gesetz"
    where
    "simulateOne simconsts i h w g \<equiv>
      let (welt, gesetz) = converge (simulate_handlungF simconsts h) i w g in
            gesetz"
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
        10 (HandlungF (\<lambda>p n. Suc n))
        32
        (Gesetz {}) =
  Gesetz
  {(Paragraph 10, Rechtsnorm (Tatbestand (Handlung 41 42)) (Rechtsfolge ''count'')),
   (Paragraph 9, Rechtsnorm (Tatbestand (Handlung 40 41)) (Rechtsfolge ''count'')),
   (Paragraph 8, Rechtsnorm (Tatbestand (Handlung 39 40)) (Rechtsfolge ''count'')),
   (Paragraph 7, Rechtsnorm (Tatbestand (Handlung 38 39)) (Rechtsfolge ''count'')),
   (Paragraph 6, Rechtsnorm (Tatbestand (Handlung 37 38)) (Rechtsfolge ''count'')),
   (Paragraph 5, Rechtsnorm (Tatbestand (Handlung 36 37)) (Rechtsfolge ''count'')),
   (Paragraph 4, Rechtsnorm (Tatbestand (Handlung 35 36)) (Rechtsfolge ''count'')),
   (Paragraph 3, Rechtsnorm (Tatbestand (Handlung 34 35)) (Rechtsfolge ''count'')),
   (Paragraph 2, Rechtsnorm (Tatbestand (Handlung 33 34)) (Rechtsfolge ''count'')),
   (Paragraph 1, Rechtsnorm (Tatbestand (Handlung 32 33)) (Rechtsfolge ''count''))}\<close>
  by eval


text\<open>Eine Iteration der Simulation liefert genau einen Paragraphen im Gesetz:\<close>
lemma \<open>\<exists>tb rf. 
  simulateOne
    (SimConsts person maxime gesetz_ableiten)
    1 handlungF
    initialwelt
    (Gesetz {})
  = Gesetz {(Paragraph 1, Rechtsnorm (Tatbestand tb) (Rechtsfolge rf))}\<close>
  apply(simp add: simulateOne_def kategorischer_imperativ_def)
  apply(case_tac maxime, simp)
  apply(simp add: teste_maxime_unfold max_paragraph_def)
  apply(intro conjI impI)
  by(metis rechtsfolge.exhaust rechtsnorm.exhaust tatbestand.exhaust)+
  
end
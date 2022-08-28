theory Simulation
imports Gesetz Handlung Kant
begin

datatype ('person, 'world, 'a, 'b) simulation_constants  = SimConsts
    'person \<comment>\<open>handelnde Person\<close>
    (*moeglich :: H.Handlung world -> Bool, -- brauch ich das oder geht das mit typen?*)
    "('person, 'world) maxime"
    "('world, 'a, 'b) allgemeines_gesetz_ableiten"


text\<open>simulate one \<^typ>\<open>('person, 'world) handlungF\<close> once\<close>
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

text\<open>simulate one \<^typ>\<open>('person, 'world) handlungF\<close> a few times\<close>
definition simulateOne
    :: "('person, 'world, 'a, 'b) simulation_constants \<Rightarrow>
        nat \<Rightarrow> ('person, 'world) handlungF \<Rightarrow> 'world \<Rightarrow> (nat, 'a, 'b) gesetz
        \<Rightarrow> (nat, 'a, 'b) gesetz"
    where
    "simulateOne simconsts i h w g \<equiv>
      let (welt, gesetz) = converge (simulate_handlungF simconsts h) i w g in
            gesetz"
end
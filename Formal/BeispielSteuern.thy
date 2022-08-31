theory BeispielSteuern
imports Kant Gesetze Simulation
begin

text\<open>Wenn die Welt sich durch eine Zahl darstellen lässt, ...\<close>
datatype steuerwelt = Steuerwelt
        (get_einkommen: "person \<Rightarrow> int option") \<comment>\<open>einkommen: einkommen jeder Person.\<close>

fun steuerlast :: "person \<Rightarrow> steuerwelt handlung \<Rightarrow> int" where
  "steuerlast p (Handlung vor nach) =
    (the_default ((get_einkommen vor) p) 0) - (the_default ((get_einkommen nach) p) 0)"

lemma \<open>steuerlast Alice (Handlung (Steuerwelt [Alice \<mapsto> 8]) (Steuerwelt [Alice \<mapsto> 5])) = 3\<close> by eval
lemma \<open>steuerlast Alice (Handlung (Steuerwelt [Alice \<mapsto> 8]) (Steuerwelt [Alice \<mapsto> 0])) = 8\<close> by eval
lemma \<open>steuerlast Bob   (Handlung (Steuerwelt [Alice \<mapsto> 8]) (Steuerwelt [Alice \<mapsto> 5])) = 0\<close> by eval

fun mehrverdiener :: "person \<Rightarrow> steuerwelt handlung \<Rightarrow> person set" where
  "mehrverdiener ich (Handlung vor nach) =
    {p. the_default ((get_einkommen vor) p) 0 \<ge> the_default ((get_einkommen vor) ich) 0}"

lemma \<open>mehrverdiener Alice
        (Handlung (Steuerwelt [Alice \<mapsto> 8, Bob \<mapsto> 12, Eve \<mapsto> 7]) (Steuerwelt [Alice \<mapsto> 5]))
       = {Alice, Bob}\<close> by eval

definition maxime_steuern :: "(person, steuerwelt) maxime" where
  "maxime_steuern \<equiv> Maxime 
      (\<lambda>ich handlung.
           \<forall>p\<in>mehrverdiener ich handlung. steuerlast ich handlung \<le> steuerlast p handlung)"


definition "sc \<equiv> SimConsts Alice maxime_steuern case_law_ableiten"
definition "initialwelt \<equiv> Steuerwelt [Alice \<mapsto> 10, Bob \<mapsto> 5, Carol \<mapsto> 5, Eve \<mapsto> 5]"

definition "beispiel_case_law h \<equiv> simulateOne sc 20 h initialwelt (Gesetz {})"

text\<open>Keiner zahlt steuern: funktioniert\<close>
value \<open>beispiel_case_law (HandlungF (\<lambda>ich welt. welt))\<close>

text\<open>Jeder zahlt 1 Steuer: funnktioniert nicht, .... komisch, sollte aber?\<close>
value \<open>beispiel_case_law (HandlungF (\<lambda>ich welt. Steuerwelt ((get_einkommen welt)(ich \<mapsto> (the_default ((get_einkommen welt) ich) 0) - 1))))\<close>
end
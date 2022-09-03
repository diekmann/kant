theory BeispielSteuern
imports Kant Gesetze Simulation
begin

text\<open>Wenn die Welt sich durch eine Zahl darstellen lässt, ...\<close>
datatype steuerwelt = Steuerwelt
        (*TODO: was ist der unterschied zwischen 
            Alice \<rightarrow> None
            Alice \<rightarrow> 0
          Warum nicht `person \<Rightarrow> int` und einfach immer 0 annehmen wenn nicht anders definiert?*)
        (get_einkommen: "person \<rightharpoonup> int") \<comment>\<open>einkommen: einkommen jeder Person.\<close>

fun steuerlast :: "person \<Rightarrow> steuerwelt handlung \<Rightarrow> int" where
  "steuerlast p (Handlung vor nach) =
    (the_default ((get_einkommen vor) p) 0) - (the_default ((get_einkommen nach) p) 0)"

lemma \<open>steuerlast Alice (Handlung (Steuerwelt [Alice \<mapsto> 8]) (Steuerwelt [Alice \<mapsto> 5])) = 3\<close> by eval
lemma \<open>steuerlast Alice (Handlung (Steuerwelt [Alice \<mapsto> 8]) (Steuerwelt [Alice \<mapsto> 0])) = 8\<close> by eval
lemma \<open>steuerlast Bob   (Handlung (Steuerwelt [Alice \<mapsto> 8]) (Steuerwelt [Alice \<mapsto> 5])) = 0\<close> by eval
lemma \<open>steuerlast Alice (Handlung (Steuerwelt [Alice \<mapsto> -3]) (Steuerwelt [Alice \<mapsto> -4])) = 1\<close> by eval
lemma \<open>steuerlast Alice (Handlung (Steuerwelt [Alice \<mapsto> 1]) (Steuerwelt [Alice \<mapsto> -1])) = 2\<close> by eval

fun mehrverdiener :: "person \<Rightarrow> steuerwelt handlung \<Rightarrow> person set" where
  "mehrverdiener ich (Handlung vor nach) =
    {p. the_default ((get_einkommen vor) p) 0 \<ge> the_default ((get_einkommen vor) ich) 0}"

lemma \<open>mehrverdiener Alice
        (Handlung (Steuerwelt [Alice \<mapsto> 8, Bob \<mapsto> 12, Eve \<mapsto> 7]) (Steuerwelt [Alice \<mapsto> 5]))
       = {Alice, Bob}\<close> by eval

(*TODO: maxime sollte sein, dass ich mehr steuern zu zahlen hab als geringerverdiener.*)
definition maxime_steuern :: "(person, steuerwelt) maxime" where
  "maxime_steuern \<equiv> Maxime 
      (\<lambda>ich handlung.
           \<forall>p\<in>mehrverdiener ich handlung. steuerlast ich handlung \<le> steuerlast p handlung)"


term map_option
term map_comp


text\<open>Isabelle does not allow printing functions, but it allows printing lists\<close>
definition show_map :: "('a::enum \<rightharpoonup> 'b) \<Rightarrow> ('a \<times> 'b) list" where
  "show_map m \<equiv> List.map_filter (\<lambda>p. map_option (\<lambda>i. (p, i)) (m p)) (enum_class.enum)"

lemma \<open>show_map [Alice \<mapsto> (8::int), Bob \<mapsto> 12, Eve \<mapsto> 7] = [(Alice, 8), (Bob, 12), (Eve, 7)]\<close> by eval

lemma "map_of (show_map m) = m"
  apply(simp add: show_map_def map_of_def)
  apply(induction enum_class.enum)
   apply(simp)
  oops (*TODO*)

(*TODO: why isnt this a library function?*)
definition map_map :: "('a \<Rightarrow> 'b) \<Rightarrow> ('k \<rightharpoonup> 'a) \<Rightarrow> ('k \<rightharpoonup> 'b)" where
  "map_map f m k \<equiv> case m k of None \<Rightarrow> None | Some a \<Rightarrow> Some (f a)"

lemma map_map: "map_map f m = map_comp (\<lambda>a. Some (f a)) m"
  by(simp add: fun_eq_iff map_map_def map_comp_def)

(*does this help printing?*)
lemma map_map_map_if_propagate[simp add]:
  "map_map f (\<lambda>k. if P k then Some y else X k) = (\<lambda>k. if P k then Some (f y) else map_map f X k)"
  apply(simp add: fun_eq_iff, intro allI conjI)
   apply(simp add: map_map_def)+
  done



definition "sc \<equiv> SimConsts
                    Alice
                    maxime_steuern
                    (\<lambda>h. case_law_ableiten (map_handlung (\<lambda>w. show_map (get_einkommen w)) h))" (*printable handlung*)
definition "initialwelt \<equiv> Steuerwelt [Alice \<mapsto> 8, Bob \<mapsto> 3, Eve \<mapsto> 5]"

definition "beispiel_case_law h \<equiv> simulateOne sc 20 h initialwelt (Gesetz {})"

text\<open>Keiner zahlt steuern: funktioniert\<close>
value \<open>beispiel_case_law (HandlungF (\<lambda>ich welt. welt))\<close>

text\<open>Ich zahle 1 Steuer: funnktioniert nicht, .... komisch, sollte aber? Achjaaaaaa, jeder muss ja steuer zahlen, ....\<close>
value \<open>beispiel_case_law
  (HandlungF (\<lambda>ich welt. Steuerwelt (
                (get_einkommen welt)(ich \<mapsto> (the_default ((get_einkommen welt) ich) 0) - 1)
    )))\<close>
value \<open>beispiel_case_law
  (HandlungF (\<lambda>ich welt. Steuerwelt (
                (get_einkommen welt)(ich := map_option (\<lambda>e. e - 1) ((get_einkommen welt) ich))
    )))\<close>

  
text\<open>Jeder muss steuern zahlen: funktioniert\<close> (*TODO: ich muss die maps printen!*)
(*TODO: wieso hoert das eigentlich mit einem Verbot auf?*)
value \<open>beispiel_case_law
  (HandlungF (\<lambda>ich welt. Steuerwelt (
        (map_map (\<lambda>e. e - 1) (get_einkommen welt))
    )))\<close>
end
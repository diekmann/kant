theory BeispielSteuern
imports Kant Gesetze Simulation
begin


section\<open>Beispiel: Steuern\<close>

text\<open>Wenn die Welt sich durch eine Zahl darstellen lässt, ...\<close>
datatype steuerwelt = Steuerwelt
        (get_einkommen: "person \<Rightarrow> int") \<comment>\<open>einkommen: einkommen jeder Person (im Zweifel 0).\<close>

fun steuerlast :: "person \<Rightarrow> steuerwelt handlung \<Rightarrow> int" where
  "steuerlast p (Handlung vor nach) = ((get_einkommen vor) p) - ((get_einkommen nach) p)"

text\<open>Default: kein Einkommen. Um Beispiele einfacher zu schreiben.\<close>
definition KE :: "person \<Rightarrow> int" where
  "KE \<equiv> \<lambda>p. 0"

lemma \<open>steuerlast Alice (Handlung (Steuerwelt (KE(Alice:=8))) (Steuerwelt (KE(Alice:=5)))) = 3\<close> by eval
lemma \<open>steuerlast Alice (Handlung (Steuerwelt (KE(Alice:=8))) (Steuerwelt (KE(Alice:=0)))) = 8\<close> by eval
lemma \<open>steuerlast Bob   (Handlung (Steuerwelt (KE(Alice:=8))) (Steuerwelt (KE(Alice:=5)))) = 0\<close> by eval
lemma \<open>steuerlast Alice (Handlung (Steuerwelt (KE(Alice:=-3))) (Steuerwelt (KE(Alice:=-4)))) = 1\<close> by eval
lemma \<open>steuerlast Alice (Handlung (Steuerwelt (KE(Alice:=1))) (Steuerwelt (KE(Alice:=-1)))) = 2\<close> by eval

fun mehrverdiener :: "person \<Rightarrow> steuerwelt handlung \<Rightarrow> person set" where
  "mehrverdiener ich (Handlung vor nach) = {p. (get_einkommen vor) p \<ge> (get_einkommen vor) ich}"

lemma \<open>mehrverdiener Alice
        (Handlung (Steuerwelt (KE(Alice:=8, Bob:=12, Eve:=7))) (Steuerwelt (KE(Alice:=5))))
       = {Alice, Bob}\<close> by eval

(*TODO: maxime sollte sein, dass ich mehr steuern zu zahlen hab als geringerverdiener.*)
definition maxime_steuern :: "(person, steuerwelt) maxime" where
  "maxime_steuern \<equiv> Maxime 
      (\<lambda>ich handlung.
           \<forall>p\<in>mehrverdiener ich handlung. steuerlast ich handlung \<le> steuerlast p handlung)"




definition "sc \<equiv> SimConsts
    Alice
    maxime_steuern
    (\<lambda>h. case_law_ableiten_absolut (map_handlung (\<lambda>w. show_fun (get_einkommen w)) h))" (*printable handlung*)
definition "initialwelt \<equiv> Steuerwelt (KE(Alice:=8, Bob:=3, Eve:= 5))"

definition "beispiel_case_law h \<equiv> simulateOne sc 20 h initialwelt (Gesetz {})"

text\<open>Keiner zahlt steuern: funktioniert\<close>
value \<open>beispiel_case_law (HandlungF (\<lambda>ich welt. welt))\<close>

text\<open>Ich zahle 1 Steuer: funnktioniert nicht, .... komisch, sollte aber?
Achjaaaaaa, jeder muss ja steuer zahlen, ....\<close>
value \<open>beispiel_case_law
  (HandlungF (\<lambda>ich welt. Steuerwelt (
                (get_einkommen welt)(ich := ((get_einkommen welt) ich) - 1)
    )))\<close>

  
text\<open>Jeder muss steuern zahlen: funktioniert, ist aber doof\<close>
value \<open>beispiel_case_law
  (HandlungF (\<lambda>ich welt. Steuerwelt (
        ((\<lambda>e. e - 1) \<circ> (get_einkommen welt))
    )))\<close>
end
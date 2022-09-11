theory BeispielSteuern
imports Kant Gesetze Simulation Steuern
begin


section\<open>Beispiel: Steuern\<close>

text\<open>Wenn die Welt sich durch eine Zahl darstellen lässt, ...\<close>
datatype steuerwelt = Steuerwelt
        (get_einkommen: "person \<Rightarrow> int") \<comment> \<open>einkommen: einkommen jeder Person (im Zweifel 0).\<close>

fun steuerlast :: "person \<Rightarrow> steuerwelt handlung \<Rightarrow> int" where
  "steuerlast p (Handlung vor nach) = ((get_einkommen vor) p) - ((get_einkommen nach) p)"

text\<open>Default: kein Einkommen. Um Beispiele einfacher zu schreiben.\<close>
definition KE :: "person \<Rightarrow> int" where
  "KE \<equiv> \<lambda>p. 0"

lemma \<open>steuerlast Alice (Handlung (Steuerwelt (KE(Alice:=8))) (Steuerwelt (KE(Alice:=5)))) = 3\<close>
  by eval
lemma \<open>steuerlast Alice (Handlung (Steuerwelt (KE(Alice:=8))) (Steuerwelt (KE(Alice:=0)))) = 8\<close>
  by eval
lemma \<open>steuerlast Bob   (Handlung (Steuerwelt (KE(Alice:=8))) (Steuerwelt (KE(Alice:=5)))) = 0\<close>
  by eval
lemma \<open>steuerlast Alice (Handlung (Steuerwelt (KE(Alice:=-3))) (Steuerwelt (KE(Alice:=-4)))) = 1\<close>
  by eval
lemma \<open>steuerlast Alice (Handlung (Steuerwelt (KE(Alice:=1))) (Steuerwelt (KE(Alice:=-1)))) = 2\<close>
  by eval

fun mehrverdiener :: "person \<Rightarrow> steuerwelt handlung \<Rightarrow> person set" where
  "mehrverdiener ich (Handlung vor nach) = {p. (get_einkommen vor) p \<ge> (get_einkommen vor) ich}"

lemma \<open>mehrverdiener Alice
        (Handlung (Steuerwelt (KE(Alice:=8, Bob:=12, Eve:=7))) (Steuerwelt (KE(Alice:=5))))
       = {Alice, Bob}\<close> by eval

(*TODO: maxime sollte sein, dass ich mehr steuern zu zahlen hab als geringerverdiener.*)
definition maxime_steuern :: "(person, steuerwelt) maxime" where
  "maxime_steuern \<equiv> Maxime 
      (\<lambda>ich handlung.
           \<forall>p\<in>mehrverdiener ich handlung.
                steuerlast ich handlung \<le> steuerlast p handlung)"



fun delta_steuerwelt :: "(steuerwelt, person, int) delta" where
  "delta_steuerwelt vor nach = Aenderung.delta_num_fun (get_einkommen vor) (get_einkommen nach)"

definition "sc \<equiv> SimConsts
    Alice
    maxime_steuern
    (printable_case_law_ableiten_absolut (\<lambda>w. show_fun (get_einkommen w)))"
definition "sc' \<equiv> SimConsts
    Alice
    maxime_steuern
    (case_law_ableiten_relativ delta_steuerwelt)"

definition "initialwelt \<equiv> Steuerwelt (KE(Alice:=8, Bob:=3, Eve:= 5))"

definition "beispiel_case_law h \<equiv> simulateOne sc 3 h initialwelt (Gesetz {})"
definition "beispiel_case_law' h \<equiv> simulateOne sc' 20 h initialwelt (Gesetz {})"

text\<open>Keiner zahlt steuern: funktioniert\<close>
value \<open>beispiel_case_law (HandlungF (\<lambda>ich welt. welt))\<close>
lemma \<open>beispiel_case_law' (HandlungF (\<lambda>ich welt. welt)) =
  Gesetz {(Paragraph 1, Rechtsnorm (Tatbestand []) (Rechtsfolge Erlaubnis))}\<close> by eval

text\<open>Ich zahle 1 Steuer: funnktioniert nicht, .... komisch, sollte aber?
Achjaaaaaa, jeder muss ja Steuer zahlen, ....\<close>
definition "ich_zahle_1_steuer ich welt \<equiv>
  Steuerwelt ((get_einkommen welt)(ich := ((get_einkommen welt) ich) - 1))"
lemma \<open>beispiel_case_law (HandlungF ich_zahle_1_steuer) =
  Gesetz
  {(Paragraph 1,
    Rechtsnorm
     (Tatbestand
       ([(Alice, 8), (Bob, 3), (Carol, 0), (Eve, 5)],
        [(Alice, 7), (Bob, 3), (Carol, 0), (Eve, 5)]))
     (Rechtsfolge Verbot))}\<close> by eval
lemma \<open>beispiel_case_law' (HandlungF ich_zahle_1_steuer) =
  Gesetz
  {(Paragraph 1, Rechtsnorm (Tatbestand [Verliert Alice 1])
                            (Rechtsfolge Verbot))}\<close> by eval
  
text\<open>Jeder muss steuern zahlen:
  funktioniert, ist aber doof, denn am Ende sind alle im Minus.

Das \<^term>\<open>ich\<close> wird garnicht verwendet, da jeder Steuern zahlt.\<close>
definition "jeder_zahle_1_steuer ich welt \<equiv>
  Steuerwelt ((\<lambda>e. e - 1) \<circ> (get_einkommen welt))"
lemma \<open>beispiel_case_law (HandlungF jeder_zahle_1_steuer) =
Gesetz
  {(Paragraph 3,
    Rechtsnorm
     (Tatbestand
       ([(Alice, 6), (Bob, 1), (Carol, - 2), (Eve, 3)],
        [(Alice, 5), (Bob, 0), (Carol, - 3), (Eve, 2)]))
     (Rechtsfolge Erlaubnis)),
   (Paragraph 2,
    Rechtsnorm
     (Tatbestand
       ([(Alice, 7), (Bob, 2), (Carol, - 1), (Eve, 4)],
        [(Alice, 6), (Bob, 1), (Carol, - 2), (Eve, 3)]))
     (Rechtsfolge Erlaubnis)),
   (Paragraph 1,
    Rechtsnorm
     (Tatbestand
       ([(Alice, 8), (Bob, 3), (Carol, 0), (Eve, 5)],
        [(Alice, 7), (Bob, 2), (Carol, - 1), (Eve, 4)]))
     (Rechtsfolge Erlaubnis))}\<close> by eval
lemma \<open>beispiel_case_law' (HandlungF jeder_zahle_1_steuer) =
  Gesetz
  {(Paragraph 1,
    Rechtsnorm
     (Tatbestand [Verliert Alice 1, Verliert Bob 1, Verliert Carol 1, Verliert Eve 1])
     (Rechtsfolge Erlaubnis))}\<close> by eval

text\<open>Jetzt kommt die Steuern.thy ins Spiel.\<close>
(*wow ist das langsam!*)

text\<open>Bei dem geringen Einkommen zahlt keiner Steuern.\<close>
definition "jeder_zahlt_einkommenssteuer ich welt \<equiv>
  Steuerwelt ((\<lambda>e. e - einkommenssteuer e) \<circ> nat \<circ> (get_einkommen welt))"
lemma \<open>beispiel_case_law (HandlungF jeder_zahlt_einkommenssteuer ) = 
  Gesetz
  {(Paragraph 1,
    Rechtsnorm
     (Tatbestand
       ([(Alice, 8), (Bob, 3), (Carol, 0), (Eve, 5)],
        [(Alice, 8), (Bob, 3), (Carol, 0), (Eve, 5)]))
     (Rechtsfolge Erlaubnis))}\<close> by eval

lemma \<open>simulateOne
  sc' 1
  (HandlungF jeder_zahlt_einkommenssteuer)
  (Steuerwelt (KE(Alice:=10000, Bob:=14000, Eve:= 20000)))
  (Gesetz {})
  =
  Gesetz
  {(Paragraph 1,
    Rechtsnorm (Tatbestand [Verliert Bob 511, Verliert Eve 1857])
     (Rechtsfolge Erlaubnis))}\<close> by eval
end
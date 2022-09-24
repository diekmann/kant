theory BeispielSteuern
imports Zahlenwelt Maxime Gesetze Simulation Steuern
begin


section\<open>Beispiel: Steuern\<close>

text\<open>Wenn die Welt sich durch eine Zahl darstellen lässt, ...

Achtung: Im Unterschied zum BeispielZahlenwelt.thy modellieren wir hier nicht den Gesamtbesitz,
sondern das Jahreseinkommen. Besitz wird ignoriert.
\<close>
datatype steuerwelt = Steuerwelt
        (get_einkommen: "person \<Rightarrow> int") \<comment> \<open>einkommen: einkommen jeder Person (im Zweifel 0).\<close>

fun steuerlast :: "person \<Rightarrow> steuerwelt handlung \<Rightarrow> int" where
  "steuerlast p (Handlung vor nach) = ((get_einkommen vor) p) - ((get_einkommen nach) p)"

fun brutto :: "person \<Rightarrow> steuerwelt handlung \<Rightarrow> int" where
  "brutto p (Handlung vor nach) = (get_einkommen vor) p"
fun netto :: "person \<Rightarrow> steuerwelt handlung \<Rightarrow> int" where
  "netto p (Handlung vor nach) = (get_einkommen nach) p"


text\<open>Default: \<^const>\<open>DEFAULT\<close> entspricht keinem Einkommen. Um Beispiele einfacher zu schreiben.\<close>

lemma \<open>steuerlast Alice (Handlung (Steuerwelt \<^url>[Alice:=8]) (Steuerwelt \<^url>[Alice:=5])) = 3\<close>
  by eval
lemma \<open>steuerlast Alice (Handlung (Steuerwelt \<^url>[Alice:=8]) (Steuerwelt \<^url>[Alice:=0])) = 8\<close>
  by eval
lemma \<open>steuerlast Bob   (Handlung (Steuerwelt \<^url>[Alice:=8]) (Steuerwelt \<^url>[Alice:=5])) = 0\<close>
  by eval
lemma \<open>steuerlast Alice (Handlung (Steuerwelt \<^url>[Alice:=-3]) (Steuerwelt \<^url>[Alice:=-4])) = 1\<close>
  by eval
lemma \<open>steuerlast Alice (Handlung (Steuerwelt \<^url>[Alice:=1]) (Steuerwelt \<^url>[Alice:=-1])) = 2\<close>
  by eval

fun mehrverdiener :: "person \<Rightarrow> steuerwelt handlung \<Rightarrow> person set" where
  "mehrverdiener ich (Handlung vor nach) = {p. (get_einkommen vor) p \<ge> (get_einkommen vor) ich}"

lemma \<open>mehrverdiener Alice
        (Handlung (Steuerwelt \<^url>[Alice:=8, Bob:=12, Eve:=7]) (Steuerwelt \<^url>[Alice:=5]))
       = {Alice, Bob}\<close> by eval

(*TODO: eine andere test maxime sollte sein, dass ich mehr steuern zu zahlen hab als geringerverdiener.*)
definition maxime_steuern :: "(person, steuerwelt) maxime" where
  "maxime_steuern \<equiv> Maxime 
      (\<lambda>ich handlung.
           (\<forall>p\<in>mehrverdiener ich handlung.
                steuerlast ich handlung \<le> steuerlast p handlung)
          \<and> (\<forall>p\<in>mehrverdiener ich handlung.
                netto ich handlung \<le> netto p handlung)
          )"
  (*do we also need: \<and> steuerlast ich handlung \<le> brutto ich handlung*)


fun delta_steuerwelt :: "(steuerwelt, person, int) delta" where
  "delta_steuerwelt (Handlung vor nach) =
      Aenderung.delta_num_fun (Handlung (get_einkommen vor) (get_einkommen nach))"

definition "sc \<equiv> SimConsts
    Alice
    maxime_steuern
    (printable_case_law_ableiten_absolut (\<lambda>w. show_fun (get_einkommen w)))"
definition "sc' \<equiv> SimConsts
    Alice
    maxime_steuern
    (case_law_ableiten_relativ delta_steuerwelt)"

definition "initialwelt \<equiv> Steuerwelt \<^url>[Alice:=8, Bob:=3, Eve:= 5]"

definition "beispiel_case_law h \<equiv> simulateOne sc 3 h initialwelt (Gesetz {})"
definition "beispiel_case_law' h \<equiv> simulateOne sc' 20 h initialwelt (Gesetz {})"

text\<open>Keiner zahlt steuern: funktioniert\<close>
value \<open>beispiel_case_law (HandlungF (\<lambda>ich welt. welt))\<close>
lemma \<open>beispiel_case_law' (HandlungF (\<lambda>ich welt. welt)) =
  Gesetz {(\<section> 1, Rechtsnorm (Tatbestand []) (Rechtsfolge Erlaubnis))}\<close> by eval

text\<open>Ich zahle 1 Steuer: funnktioniert nicht, .... komisch, sollte aber?
Achjaaaaaa, jeder muss ja Steuer zahlen, ....\<close>
definition "ich_zahle_1_steuer ich welt \<equiv>
  Steuerwelt ((get_einkommen welt)(ich := ((get_einkommen welt) ich) - 1))"
lemma \<open>beispiel_case_law (HandlungF ich_zahle_1_steuer) =
  Gesetz
  {(\<section> 1,
    Rechtsnorm
     (Tatbestand
       ([(Alice, 8), (Bob, 3), (Carol, 0), (Eve, 5)],
        [(Alice, 7), (Bob, 3), (Carol, 0), (Eve, 5)]))
     (Rechtsfolge Verbot))}\<close> by eval
lemma \<open>beispiel_case_law' (HandlungF ich_zahle_1_steuer) =
  Gesetz
  {(\<section> 1, Rechtsnorm (Tatbestand [Verliert Alice 1])
                            (Rechtsfolge Verbot))}\<close> by eval
  
text\<open>Jeder muss steuern zahlen:
  funktioniert, ist aber doof, denn am Ende sind alle im Minus.

Das \<^term>\<open>ich\<close> wird garnicht verwendet, da jeder Steuern zahlt.\<close>
definition "jeder_zahle_1_steuer ich welt \<equiv>
  Steuerwelt ((\<lambda>e. e - 1) \<circ> (get_einkommen welt))"
lemma \<open>beispiel_case_law (HandlungF jeder_zahle_1_steuer) =
Gesetz
  {(\<section> 3,
    Rechtsnorm
     (Tatbestand
       ([(Alice, 6), (Bob, 1), (Carol, - 2), (Eve, 3)],
        [(Alice, 5), (Bob, 0), (Carol, - 3), (Eve, 2)]))
     (Rechtsfolge Erlaubnis)),
   (\<section> 2,
    Rechtsnorm
     (Tatbestand
       ([(Alice, 7), (Bob, 2), (Carol, - 1), (Eve, 4)],
        [(Alice, 6), (Bob, 1), (Carol, - 2), (Eve, 3)]))
     (Rechtsfolge Erlaubnis)),
   (\<section> 1,
    Rechtsnorm
     (Tatbestand
       ([(Alice, 8), (Bob, 3), (Carol, 0), (Eve, 5)],
        [(Alice, 7), (Bob, 2), (Carol, - 1), (Eve, 4)]))
     (Rechtsfolge Erlaubnis))}\<close> by eval
lemma \<open>beispiel_case_law' (HandlungF jeder_zahle_1_steuer) =
  Gesetz
  {(\<section> 1,
    Rechtsnorm
     (Tatbestand [Verliert Alice 1, Verliert Bob 1, Verliert Carol 1, Verliert Eve 1])
     (Rechtsfolge Erlaubnis))}\<close> by eval

text\<open>Jetzt kommt die Steuern.thy ins Spiel.\<close>
(*wow ist das langsam!*)

text\<open>Bei dem geringen Einkommen zahlt keiner Steuern.\<close>
definition "jeder_zahlt steuerberechnung ich welt \<equiv>
  Steuerwelt ((\<lambda>e. e - steuerberechnung e) \<circ> nat \<circ> (get_einkommen welt))"

definition "jeder_zahlt_einkommenssteuer \<equiv> jeder_zahlt einkommenssteuer"
lemma \<open>beispiel_case_law (HandlungF jeder_zahlt_einkommenssteuer ) = 
  Gesetz
  {(\<section> 1,
    Rechtsnorm
     (Tatbestand
       ([(Alice, 8), (Bob, 3), (Carol, 0), (Eve, 5)],
        [(Alice, 8), (Bob, 3), (Carol, 0), (Eve, 5)]))
     (Rechtsfolge Erlaubnis))}\<close> by eval

lemma \<open>simulateOne
  sc' 1
  (HandlungF jeder_zahlt_einkommenssteuer)
  (Steuerwelt \<^url>[Alice:=10000, Bob:=14000, Eve:= 20000])
  (Gesetz {})
  =
  Gesetz
  {(\<section> 1,
    Rechtsnorm (Tatbestand [Verliert Bob 511, Verliert Eve 1857])
     (Rechtsfolge Erlaubnis))}\<close> by eval

(*TODO: eigentlich sollte das folgende gelten in beide richtungen:*)
text\<open>Die Anforderungen fuer ein \<^locale>\<open>steuersystem\<close> und die \<^const>\<open>maxime_steuern\<close> sind vereinbar.\<close>
lemma "steuersystem steuersystem_impl \<Longrightarrow>
        (\<forall>welt. teste_maxime welt (HandlungF (jeder_zahlt steuersystem_impl)) maxime_steuern)"
   apply(simp add: maxime_steuern_def teste_maxime_unfold)
   apply(simp add: jeder_zahlt_def bevoelkerung_def)
   apply(intro allI impI conjI)
   apply(rename_tac welt p1 p2)
   thm steuersystem.wer_hat_der_gibt
   apply(drule_tac
        einkommen_b="nat (get_einkommen welt p1)" and
        einkommen_a="nat (get_einkommen welt p2)" in steuersystem.wer_hat_der_gibt)
    apply(simp; fail)
   apply(simp; fail)
  apply(rename_tac welt p1 p2)
  apply(drule_tac
        einkommen_b="nat (get_einkommen welt p1)" and
        einkommen_a="nat (get_einkommen welt p2)" in steuersystem.leistung_lohnt_sich)
   apply(simp; fail)
  by (simp add: steuer_defs.netto_def)

lemma "a \<le> x \<Longrightarrow> int x - int (x - a) = a" by simp

(*TODO*)
text\<open>Danke ihr nats. Macht also keinen Sinn das als Annahme in die Maxime zu packen....\<close>
lemma steuern_kleiner_einkommen_nat:
      "steuerlast ich (Handlung welt (jeder_zahlt steuersystem_impl ich welt))
         \<le> brutto ich (Handlung welt (jeder_zahlt steuersystem_impl ich welt))"
  apply(simp del: steuerlast.simps)
  apply(subst steuerlast.simps)
  apply(simp add: jeder_zahlt_def)
  done

(*Braucht ein paar Annahmen.*)
lemma "(\<forall>einkommen. steuersystem_impl einkommen \<le> einkommen) \<Longrightarrow>
       (\<forall>einkommen. einkommen \<le> 9888 \<longrightarrow> steuersystem_impl einkommen = 0) \<Longrightarrow>
        \<forall>welt. teste_maxime welt (HandlungF (jeder_zahlt steuersystem_impl)) maxime_steuern
        \<Longrightarrow> steuersystem steuersystem_impl"
proof
  fix einkommen_b einkommen_a :: nat
  assume m: "\<forall>welt. teste_maxime welt (HandlungF (jeder_zahlt steuersystem_impl)) maxime_steuern"
     and a: "einkommen_b \<le> einkommen_a"
     and bezahlbar: "\<forall>einkommen. steuersystem_impl einkommen \<le> einkommen"
  from m have m':
    "get_einkommen welt pA \<le> get_einkommen welt pB \<Longrightarrow>
       get_einkommen welt pA -
             int (nat (get_einkommen welt pA) - steuersystem_impl (nat (get_einkommen welt pA)))
             \<le> get_einkommen welt pB -
                int (nat (get_einkommen welt pB) - steuersystem_impl (nat (get_einkommen welt pB)))"
    for welt :: steuerwelt and pA pB :: person
    by(simp add: maxime_steuern_def teste_maxime_unfold jeder_zahlt_def bevoelkerung_def)
  from m'[where welt="Steuerwelt (\<lambda>p. if p = Bob then einkommen_b else einkommen_a)"
                and pA=Bob and pB=Alice] a
  have almost:
    "int einkommen_b - int (einkommen_b - steuersystem_impl einkommen_b)
      \<le> int einkommen_a - int (einkommen_a - steuersystem_impl einkommen_a)"
    by simp
  from bezahlbar have "steuersystem_impl einkommen_b \<le> einkommen_b" by simp
  from this almost show "steuersystem_impl einkommen_b \<le> steuersystem_impl einkommen_a"
    by simp
next
  fix einkommen_b einkommen_a :: nat
  assume m: "\<forall>welt. teste_maxime welt (HandlungF (jeder_zahlt steuersystem_impl)) maxime_steuern"
     and a: "einkommen_b \<le> einkommen_a"
  from m have m':
    "get_einkommen welt pA \<le> get_einkommen welt pB \<Longrightarrow>
       nat (get_einkommen welt pA) - steuersystem_impl (nat (get_einkommen welt pA))
       \<le> nat (get_einkommen welt pB) - steuersystem_impl (nat (get_einkommen welt pB))"
    for welt :: steuerwelt and pA pB :: person
    by(simp add: maxime_steuern_def teste_maxime_unfold jeder_zahlt_def bevoelkerung_def)
  from m'[where welt="Steuerwelt (\<lambda>p. if p = Bob then einkommen_b else einkommen_a)"
                and pA=Bob and pB=Alice] a
  have "einkommen_b - steuersystem_impl einkommen_b \<le> einkommen_a - steuersystem_impl einkommen_a"
    by simp
  from this show
    "steuer_defs.netto steuersystem_impl einkommen_b
      \<le> steuer_defs.netto steuersystem_impl einkommen_a"
    by(simp add: steuer_defs.netto_def)
next
  fix einkommen
  show "\<forall>einkommen\<le>9888. steuersystem_impl einkommen = 0
        \<Longrightarrow> einkommen \<le> 9888 \<Longrightarrow> steuersystem_impl einkommen = 0"
    by simp
qed
    

end
theory BeispielSteuern
imports Zahlenwelt Maxime Gesetze Simulation Steuern
begin


section\<open>Beispiel: Steuern\<close>

text\<open>Wir nehmen eine einfach Welt an, in der jeder Person ihr Einkommen zugeordnet wird.

Achtung: Im Unterschied zum BeispielZahlenwelt.thy modellieren wir hier nicht den Gesamtbesitz,
sondern das Jahreseinkommen. Besitz wird ignoriert.
\<close>
datatype steuerwelt = Steuerwelt
        (get_einkommen: \<open>person \<Rightarrow> int\<close>) \<comment> \<open>einkommen jeder Person (im Zweifel 0).\<close>

fun steuerlast :: \<open>person \<Rightarrow> steuerwelt handlung \<Rightarrow> int\<close> where
  \<open>steuerlast p (Handlung vor nach) = ((get_einkommen vor) p) - ((get_einkommen nach) p)\<close>

fun brutto :: \<open>person \<Rightarrow> steuerwelt handlung \<Rightarrow> int\<close> where
  \<open>brutto p (Handlung vor nach) = (get_einkommen vor) p\<close>
fun netto :: \<open>person \<Rightarrow> steuerwelt handlung \<Rightarrow> int\<close> where
  \<open>netto p (Handlung vor nach) = (get_einkommen nach) p\<close>


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

fun mehrverdiener :: \<open>person \<Rightarrow> steuerwelt handlung \<Rightarrow> person set\<close> where
  \<open>mehrverdiener ich (Handlung vor nach) = {p. (get_einkommen vor) p \<ge> (get_einkommen vor) ich}\<close>

lemma \<open>mehrverdiener Alice
        (Handlung (Steuerwelt \<^url>[Alice:=8, Bob:=12, Eve:=7]) (Steuerwelt \<^url>[Alice:=5]))
       = {Alice, Bob}\<close> by eval

text\<open>Folgende Maxime versucht Steuergerechtigkeit festzuschreiben:\<close>
(*TODO: eine andere test maxime sollte sein,
dass ich mehr steuern zu zahlen hab als geringerverdiener.*)
definition maxime_steuern :: \<open>(person, steuerwelt) maxime\<close> where
  \<open>maxime_steuern \<equiv> Maxime 
      (\<lambda>ich handlung.
           (\<forall>p\<in>mehrverdiener ich handlung.
                steuerlast ich handlung \<le> steuerlast p handlung)
          \<and> (\<forall>p\<in>mehrverdiener ich handlung.
                netto ich handlung \<le> netto p handlung)
          )\<close>
  (*do we also need: \<and> steuerlast ich handlung \<le> brutto ich handlung*)


(*<*)
fun delta_steuerwelt :: \<open>(steuerwelt, person, int) delta\<close> where
  \<open>delta_steuerwelt (Handlung vor nach) =
      Aenderung.delta_num_fun (Handlung (get_einkommen vor) (get_einkommen nach))\<close>
(*>*)


subsection\<open>Setup für Beispiele\<close>

definition \<open>initialwelt \<equiv> Steuerwelt \<^url>[Alice:=8, Bob:=3, Eve:= 5]\<close>

definition \<open>beispiel_case_law_absolut welt steuerfun \<equiv>
  simulateOne
    (SimConsts
      Alice
      maxime_steuern
      (printable_case_law_ableiten_absolut (\<lambda>w. show_fun (get_einkommen w))))
    3 steuerfun welt (Gesetz {})\<close>
definition \<open>beispiel_case_law_relativ welt steuerfun \<equiv>
  simulateOne
    (SimConsts
      Alice
      maxime_steuern
      (case_law_ableiten_relativ delta_steuerwelt))
    1 steuerfun welt (Gesetz {})\<close>


subsection\<open>Beispiel: Keiner Zahlt Steuern\<close>

text\<open>Die Maxime ist erfüllt, da wir immer nur kleiner-gleich fordern!\<close>
lemma \<open>beispiel_case_law_relativ initialwelt (HandlungF (\<lambda>ich welt. welt)) =
  Gesetz {(\<section> 1, Rechtsnorm (Tatbestand []) (Rechtsfolge Erlaubnis))}\<close> by eval


subsection\<open>Beiepiel: Ich zahle 1 Steuer\<close>
text\<open>Das funktioniert nicht:\<close>
definition \<open>ich_zahle_1_steuer ich welt \<equiv>
  Steuerwelt ((get_einkommen welt)(ich -= 1))\<close>
lemma \<open>beispiel_case_law_absolut initialwelt (HandlungF ich_zahle_1_steuer) =
  Gesetz
  {(\<section> 1,
    Rechtsnorm
     (Tatbestand
       ([(Alice, 8), (Bob, 3), (Carol, 0), (Eve, 5)],
        [(Alice, 7), (Bob, 3), (Carol, 0), (Eve, 5)]))
     (Rechtsfolge Verbot))}\<close> by eval
lemma \<open>beispiel_case_law_relativ initialwelt (HandlungF ich_zahle_1_steuer) =
  Gesetz
  {(\<section> 1, Rechtsnorm (Tatbestand [Verliert Alice 1])
                            (Rechtsfolge Verbot))}\<close> by eval

text\<open>Denn jeder muss Steuer zahlen!
Ich finde es super spannend, dass hier faktisch ein Gleichbehandlungsgrundsatz rausfällt,
ohne dass wir soewtas jemals explizit gefordert haben.
\<close>


subsection\<open>Beiepiel: Jeder zahle 1 Steuer\<close>
text\<open>Jeder muss steuern zahlen:
  funktioniert, ist aber doof, denn am Ende sind alle im Minus.

Das \<^term>\<open>ich\<close> wird garnicht verwendet, da jeder Steuern zahlt.\<close>
definition \<open>jeder_zahle_1_steuer ich welt \<equiv>
  Steuerwelt ((\<lambda>e. e - 1) \<circ> (get_einkommen welt))\<close>
lemma \<open>beispiel_case_law_absolut initialwelt (HandlungF jeder_zahle_1_steuer) =
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
lemma \<open>beispiel_case_law_relativ initialwelt (HandlungF jeder_zahle_1_steuer) =
  Gesetz
  {(\<section> 1,
    Rechtsnorm
     (Tatbestand [Verliert Alice 1, Verliert Bob 1, Verliert Carol 1, Verliert Eve 1])
     (Rechtsfolge Erlaubnis))}\<close> by eval


subsection\<open>Beiepiel: Vereinfachtes Deutsches Steuersystem\<close>
text\<open>Jetzt kommt die Steuern.thy ins Spiel.\<close>

definition jeder_zahlt :: \<open>(nat \<Rightarrow> nat) \<Rightarrow> 'a \<Rightarrow> steuerwelt \<Rightarrow> steuerwelt\<close> where
  \<open>jeder_zahlt steuerberechnung ich welt \<equiv>
    Steuerwelt ((\<lambda>e. e - steuerberechnung e) \<circ> nat \<circ> (get_einkommen welt))\<close>

definition \<open>jeder_zahlt_einkommenssteuer \<equiv> jeder_zahlt einkommenssteuer\<close>


text\<open>Bei dem geringen Einkommen der \<^const>\<open>initialwelt\<close> zahlt keiner Steuern.\<close>
lemma \<open>beispiel_case_law_absolut initialwelt (HandlungF jeder_zahlt_einkommenssteuer ) = 
  Gesetz
  {(\<section> 1,
    Rechtsnorm
     (Tatbestand
       ([(Alice, 8), (Bob, 3), (Carol, 0), (Eve, 5)],
        [(Alice, 8), (Bob, 3), (Carol, 0), (Eve, 5)]))
     (Rechtsfolge Erlaubnis))}\<close> by eval


text\<open>Für höhere Einkommen erhalten wir plausible Werte und niemand rutscht ins negative:\<close>
lemma \<open>beispiel_case_law_relativ
  (Steuerwelt \<^url>[Alice:=10000, Bob:=14000, Eve:= 20000])
  (HandlungF jeder_zahlt_einkommenssteuer)
  =
  Gesetz
  {(\<section> 1,
    Rechtsnorm (Tatbestand [Verliert Bob 511, Verliert Eve 1857])
     (Rechtsfolge Erlaubnis))}\<close> by eval


section\<open>Vereinfachtes Deutsches Steuersystem vs. die Steuermaxime\<close>
text\<open>Die Anforderungen fuer ein \<^locale>\<open>steuersystem\<close> und die \<^const>\<open>maxime_steuern\<close> sind vereinbar.\<close>
lemma steuersystem_imp_maxime:
  \<open>steuersystem steuersystem_impl \<Longrightarrow>
        (\<forall>welt. moralisch welt maxime_steuern (HandlungF (jeder_zahlt steuersystem_impl)))\<close>
   apply(simp add: maxime_steuern_def moralisch_unfold)
   apply(simp add: jeder_zahlt_def bevoelkerung_def)
   apply(intro allI impI conjI)
   apply(rename_tac welt p1 p2)
   thm steuersystem.wer_hat_der_gibt
   apply(drule_tac
        einkommen_b=\<open>nat (get_einkommen welt p1)\<close> and
        einkommen_a=\<open>nat (get_einkommen welt p2)\<close> in steuersystem.wer_hat_der_gibt)
    apply(simp; fail)
   apply(simp; fail)
  apply(rename_tac welt p1 p2)
  apply(drule_tac
        einkommen_b=\<open>nat (get_einkommen welt p1)\<close> and
        einkommen_a=\<open>nat (get_einkommen welt p2)\<close> in steuersystem.leistung_lohnt_sich)
   apply(simp; fail)
  by (simp add: steuer_defs.netto_def)


text\<open>Danke ihr nats. Macht also keinen Sinn das als Annahme in die Maxime zu packen....\<close>
lemma steuern_kleiner_einkommen_nat:
      \<open>steuerlast ich (Handlung welt (jeder_zahlt steuersystem_impl ich welt))
         \<le> brutto ich (Handlung welt (jeder_zahlt steuersystem_impl ich welt))\<close>
  apply(simp del: steuerlast.simps)
  apply(subst steuerlast.simps)
  apply(simp add: jeder_zahlt_def)
  done

(*Braucht ein paar Annahmen.*)
lemma maxime_imp_steuersystem:
    \<open>(\<forall>einkommen. steuersystem_impl einkommen \<le> einkommen) \<Longrightarrow>
       (\<forall>einkommen. einkommen \<le> 9888 \<longrightarrow> steuersystem_impl einkommen = 0) \<Longrightarrow>
        \<forall>welt. moralisch welt maxime_steuern (HandlungF (jeder_zahlt steuersystem_impl))
        \<Longrightarrow> steuersystem steuersystem_impl\<close>
proof
  fix einkommen_b einkommen_a :: \<open>nat\<close>
  assume m: \<open>\<forall>welt. moralisch welt maxime_steuern (HandlungF (jeder_zahlt steuersystem_impl))\<close>
     and a: \<open>einkommen_b \<le> einkommen_a\<close>
     and bezahlbar: \<open>\<forall>einkommen. steuersystem_impl einkommen \<le> einkommen\<close>
  from m have m':
    \<open>get_einkommen welt pA \<le> get_einkommen welt pB \<Longrightarrow>
       get_einkommen welt pA -
             int (nat (get_einkommen welt pA) - steuersystem_impl (nat (get_einkommen welt pA)))
             \<le> get_einkommen welt pB -
                int (nat (get_einkommen welt pB) - steuersystem_impl (nat (get_einkommen welt pB)))\<close>
    for welt :: \<open>steuerwelt\<close> and pA pB :: \<open>person\<close>
    by(simp add: maxime_steuern_def moralisch_unfold jeder_zahlt_def bevoelkerung_def)
  from m'[where welt=\<open>Steuerwelt (\<lambda>p. if p = Bob then einkommen_b else einkommen_a)\<close>
                and pA=\<open>Bob\<close> and pB=\<open>Alice\<close>] a
  have almost:
    \<open>int einkommen_b - int (einkommen_b - steuersystem_impl einkommen_b)
      \<le> int einkommen_a - int (einkommen_a - steuersystem_impl einkommen_a)\<close>
    by simp
  from bezahlbar have \<open>steuersystem_impl einkommen_b \<le> einkommen_b\<close> by simp
  from this almost show \<open>steuersystem_impl einkommen_b \<le> steuersystem_impl einkommen_a\<close>
    by simp
next
  fix einkommen_b einkommen_a :: \<open>nat\<close>
  assume m: \<open>\<forall>welt. moralisch welt maxime_steuern (HandlungF (jeder_zahlt steuersystem_impl))\<close>
     and a: \<open>einkommen_b \<le> einkommen_a\<close>
  from m have m':
    \<open>get_einkommen welt pA \<le> get_einkommen welt pB \<Longrightarrow>
       nat (get_einkommen welt pA) - steuersystem_impl (nat (get_einkommen welt pA))
       \<le> nat (get_einkommen welt pB) - steuersystem_impl (nat (get_einkommen welt pB))\<close>
    for welt :: \<open>steuerwelt\<close> and pA pB :: \<open>person\<close>
    by(simp add: maxime_steuern_def moralisch_unfold jeder_zahlt_def bevoelkerung_def)
  from m'[where welt=\<open>Steuerwelt (\<lambda>p. if p = Bob then einkommen_b else einkommen_a)\<close>
                and pA=\<open>Bob\<close> and pB=\<open>Alice\<close>] a
  have \<open>einkommen_b - steuersystem_impl einkommen_b \<le> einkommen_a - steuersystem_impl einkommen_a\<close>
    by simp
  from this show
    \<open>steuer_defs.netto steuersystem_impl einkommen_b
      \<le> steuer_defs.netto steuersystem_impl einkommen_a\<close>
    by(simp add: steuer_defs.netto_def)
next
  fix einkommen
  show \<open>\<forall>einkommen\<le>9888. steuersystem_impl einkommen = 0
        \<Longrightarrow> einkommen \<le> 9888 \<Longrightarrow> steuersystem_impl einkommen = 0\<close>
    by simp
qed


text\<open>
Für jedes \<^term_type>\<open>steuersystem_impl :: nat \<Rightarrow> nat\<close>,
mit zwei weiteren Annahmen,
gilt das \<^locale>\<open>steuersystem\<close> und \<^const>\<open>maxime_steuern\<close> in der \<^const>\<open>jeder_zahlt\<close> Implementierung
äquivalent sind.
\<close>
theorem
  fixes steuersystem_impl :: \<open>nat \<Rightarrow> nat\<close>
  assumes steuer_kleiner_einkommen: \<open>\<forall>einkommen. steuersystem_impl einkommen \<le> einkommen\<close>
      and existenzminimum: \<open>\<forall>einkommen. einkommen \<le> 9888 \<longrightarrow> steuersystem_impl einkommen = 0\<close>
    shows
   \<open>(\<forall>welt. moralisch welt maxime_steuern (HandlungF (jeder_zahlt steuersystem_impl)))
        \<longleftrightarrow> steuersystem steuersystem_impl\<close>
  using steuersystem_imp_maxime maxime_imp_steuersystem
  using assms by blast 

end
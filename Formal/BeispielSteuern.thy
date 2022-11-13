theory BeispielSteuern
imports Zahlenwelt Maxime Gesetze Simulation Steuern KategorischerImperativ
begin


section\<open>Beispiel: Steuern\<close>

text\<open>Wir nehmen eine einfach Welt an, in der jeder Person ihr Einkommen zugeordnet wird.

Achtung: Im Unterschied zum BeispielZahlenwelt.thy modellieren wir hier nicht den Gesamtbesitz,
sondern das Jahreseinkommen. Besitz wird ignoriert.
\<close>
datatype steuerwelt = Steuerwelt
        (get_einkommen: \<open>person \<Rightarrow> int\<close>) \<comment> \<open>einkommen jeder Person (im Zweifel 0).\<close>


(*TODO: copy from zahlenwelt*)
fun steuerwps :: \<open>person \<Rightarrow> person \<Rightarrow> steuerwelt \<Rightarrow> steuerwelt\<close> where
  \<open>steuerwps p1 p2 (Steuerwelt besitz) = Steuerwelt (swap p1 p2 besitz)\<close>


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

lemma mehrverdiener_betrachtet_nur_ausgangszustand:
  \<open>mehrverdiener p (handeln p' welt h) = mehrverdiener p (Handlung welt welt)\<close>
  by (metis handlung.collapse mehrverdiener.simps vorher_handeln)

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

(*Ist das uberhaupt eine gute Maxime?
Angenommen ich bin der Spitzenverdiener.
Dann ist die Handlungsabsicht "ich zahle 10 Steuer" gueltig nach der maxime, da "mehrverdiener ich handlung={}".
Diese Handlung kann ich aber nicht auf andere projezieren, da 
  * einerseits waere es unmoralisch so viel steuer von geringverdienern zu fordern
  * andererseits erfuelt die handlung die maxime nicht fuer jeden der nicht spitzenverdiener ist.
    Die Handlung die die maxime erfuellen wuerde waere "JEDER zahle 10 Steuer".
*)


(*<*)
fun delta_steuerwelt :: \<open>(steuerwelt, person, int) delta\<close> where
  \<open>delta_steuerwelt (Handlung vor nach) =
      Aenderung.delta_num_fun (Handlung (get_einkommen vor) (get_einkommen nach))\<close>
(*>*)

(*TODO: kategorischer Imperativ fuer diese maxime beweisen!*)
thm globale_maxime_katimp (*generalisiert das?*)

(*(Maxime 
      (\<lambda>ich handlung.
           (\<forall>p\<in>mehrverdiener ich handlung.
                steuerlast ich handlung \<le> steuerlast p handlung)))*)


lemma \<open>wpsm_kommutiert (Maxime 
      (\<lambda>ich handlung.
           (\<forall>p\<in>mehrverdiener ich handlung.
                steuerlast ich handlung \<le> steuerlast p handlung))) steuerwps welt\<close>
(*
Nitpick found a counterexample:
  Free variable:
    welt = Steuerwelt ((\<lambda>x. _)(p\<^sub>1 := 1, p\<^sub>2 := 1, p\<^sub>3 := 2, p\<^sub>4 := 2))
  Skolem constants:
    ??.wpsm_kommutiert.h =
      (\<lambda>x. _)
      (p\<^sub>1 := (\<lambda>x. _)
         (Steuerwelt ((\<lambda>x. _)(p\<^sub>1 := - 1, p\<^sub>2 := 2, p\<^sub>3 := 1, p\<^sub>4 := - 1)) :=
            Steuerwelt ((\<lambda>x. _)(p\<^sub>1 := 1, p\<^sub>2 := 1, p\<^sub>3 := 2, p\<^sub>4 := 2)),
          Steuerwelt ((\<lambda>x. _)(p\<^sub>1 := 0, p\<^sub>2 := 2, p\<^sub>3 := 0, p\<^sub>4 := - 1)) :=
            Steuerwelt ((\<lambda>x. _)(p\<^sub>1 := 1, p\<^sub>2 := 1, p\<^sub>3 := 2, p\<^sub>4 := 2)),
          Steuerwelt ((\<lambda>x. _)(p\<^sub>1 := 1, p\<^sub>2 := 1, p\<^sub>3 := 2, p\<^sub>4 := 2)) :=
            Steuerwelt ((\<lambda>x. _)(p\<^sub>1 := 1, p\<^sub>2 := 1, p\<^sub>3 := 2, p\<^sub>4 := 2)),
          Steuerwelt ((\<lambda>x. _)(p\<^sub>1 := 2, p\<^sub>2 := 2, p\<^sub>3 := 1, p\<^sub>4 := 0)) :=
            Steuerwelt ((\<lambda>x. _)(p\<^sub>1 := 1, p\<^sub>2 := 1, p\<^sub>3 := 2, p\<^sub>4 := 2))),
       p\<^sub>2 := (\<lambda>x. _)
         (Steuerwelt ((\<lambda>x. _)(p\<^sub>1 := - 1, p\<^sub>2 := 2, p\<^sub>3 := 1, p\<^sub>4 := - 1)) :=
            Steuerwelt ((\<lambda>x. _)(p\<^sub>1 := 2, p\<^sub>2 := 2, p\<^sub>3 := 1, p\<^sub>4 := 0)),
          Steuerwelt ((\<lambda>x. _)(p\<^sub>1 := 0, p\<^sub>2 := 2, p\<^sub>3 := 0, p\<^sub>4 := - 1)) :=
            Steuerwelt ((\<lambda>x. _)(p\<^sub>1 := - 1, p\<^sub>2 := 2, p\<^sub>3 := 1, p\<^sub>4 := - 1)),
          Steuerwelt ((\<lambda>x. _)(p\<^sub>1 := 1, p\<^sub>2 := 1, p\<^sub>3 := 2, p\<^sub>4 := 2)) :=
            Steuerwelt ((\<lambda>x. _)(p\<^sub>1 := - 1, p\<^sub>2 := 2, p\<^sub>3 := 1, p\<^sub>4 := - 1)),
          Steuerwelt ((\<lambda>x. _)(p\<^sub>1 := 2, p\<^sub>2 := 2, p\<^sub>3 := 1, p\<^sub>4 := 0)) :=
            Steuerwelt ((\<lambda>x. _)(p\<^sub>1 := 0, p\<^sub>2 := 2, p\<^sub>3 := 0, p\<^sub>4 := - 1))),
       p\<^sub>3 := (\<lambda>x. _)
         (Steuerwelt ((\<lambda>x. _)(p\<^sub>1 := - 1, p\<^sub>2 := 2, p\<^sub>3 := 1, p\<^sub>4 := - 1)) :=
            Steuerwelt ((\<lambda>x. _)(p\<^sub>1 := 2, p\<^sub>2 := 2, p\<^sub>3 := 1, p\<^sub>4 := 0)),
          Steuerwelt ((\<lambda>x. _)(p\<^sub>1 := 0, p\<^sub>2 := 2, p\<^sub>3 := 0, p\<^sub>4 := - 1)) :=
            Steuerwelt ((\<lambda>x. _)(p\<^sub>1 := 2, p\<^sub>2 := 2, p\<^sub>3 := 1, p\<^sub>4 := 0)),
          Steuerwelt ((\<lambda>x. _)(p\<^sub>1 := 1, p\<^sub>2 := 1, p\<^sub>3 := 2, p\<^sub>4 := 2)) :=
            Steuerwelt ((\<lambda>x. _)(p\<^sub>1 := 0, p\<^sub>2 := 2, p\<^sub>3 := 0, p\<^sub>4 := - 1)),
          Steuerwelt ((\<lambda>x. _)(p\<^sub>1 := 2, p\<^sub>2 := 2, p\<^sub>3 := 1, p\<^sub>4 := 0)) :=
            Steuerwelt ((\<lambda>x. _)(p\<^sub>1 := 1, p\<^sub>2 := 1, p\<^sub>3 := 2, p\<^sub>4 := 2))),
       p\<^sub>4 := (\<lambda>x. _)
         (Steuerwelt ((\<lambda>x. _)(p\<^sub>1 := - 1, p\<^sub>2 := 2, p\<^sub>3 := 1, p\<^sub>4 := - 1)) :=
            Steuerwelt ((\<lambda>x. _)(p\<^sub>1 := 2, p\<^sub>2 := 2, p\<^sub>3 := 1, p\<^sub>4 := 0)),
          Steuerwelt ((\<lambda>x. _)(p\<^sub>1 := 0, p\<^sub>2 := 2, p\<^sub>3 := 0, p\<^sub>4 := - 1)) :=
            Steuerwelt ((\<lambda>x. _)(p\<^sub>1 := - 1, p\<^sub>2 := 2, p\<^sub>3 := 1, p\<^sub>4 := - 1)),
          Steuerwelt ((\<lambda>x. _)(p\<^sub>1 := 1, p\<^sub>2 := 1, p\<^sub>3 := 2, p\<^sub>4 := 2)) :=
            Steuerwelt ((\<lambda>x. _)(p\<^sub>1 := 1, p\<^sub>2 := 1, p\<^sub>3 := 2, p\<^sub>4 := 2)),
          Steuerwelt ((\<lambda>x. _)(p\<^sub>1 := 2, p\<^sub>2 := 2, p\<^sub>3 := 1, p\<^sub>4 := 0)) :=
            Steuerwelt ((\<lambda>x. _)(p\<^sub>1 := 0, p\<^sub>2 := 2, p\<^sub>3 := 0, p\<^sub>4 := - 1))))
    ??.wpsm_kommutiert.p1 = p\<^sub>4
    ??.wpsm_kommutiert.p2 = p\<^sub>3
*)
  oops

lemma wfh_steuerberechnung_jeder_zahlt_int:
  \<open>ha = Handlungsabsicht (\<lambda>ich w. Some (Steuerwelt ((\<lambda>e. e - steuerberechnung e) \<circ> (get_einkommen w))))
    \<Longrightarrow> wohlgeformte_handlungsabsicht steuerwps welt ha\<close>
  apply(cases \<open>welt\<close>, rename_tac eink, simp)
  apply(simp add: wohlgeformte_handlungsabsicht.simps comp_def fun_eq_iff)
  apply(safe)
  by (smt (verit, best) swap_a swap_b swap_nothing)
  
  
  

thm mehrverdiener_betrachtet_nur_ausgangszustand
(*TODO: was kann ihc ueber die handlung ableiten, wenn maxime_und_handlungsabsicht_generalisieren_def gilt?*)
(*steuerwps*)
lemma \<open>ha = Handlungsabsicht (\<lambda>ich w. Some (Steuerwelt ((\<lambda>e. e - steuerberechnung e) \<circ> (get_einkommen w)))) \<Longrightarrow>
  kategorischer_imperativ_auf ha welt
    (Maxime 
      (\<lambda>ich handlung.
           (\<forall>p\<in>mehrverdiener ich handlung.
                steuerlast ich handlung \<le> steuerlast p handlung)))\<close>
  apply(cases \<open>welt\<close>, rename_tac eink, simp)
  apply(rule kategorischer_imperativ_aufI, rename_tac eink ich p1 p2)
  apply(case_tac \<open>ha\<close>, rename_tac h, simp)
  apply(thin_tac \<open>ha = _\<close>)
  apply(safe)
(*
Nitpick found a counterexample:
  Free variables:
    steuerberechnung = (\<lambda>x. _)(- 1 := 0, 0 := - 1, 1 := - 1, 2 := - 1)
    welt = Steuerwelt ((\<lambda>x. _)(p\<^sub>1 := - 1, p\<^sub>2 := - 1, p\<^sub>3 := 0, p\<^sub>4 := 0))
  Skolem constants:
    eink = (\<lambda>x. _)(p\<^sub>1 := - 1, p\<^sub>2 := - 1, p\<^sub>3 := 0, p\<^sub>4 := 0)
    ich = p\<^sub>4
    p = p\<^sub>3
    p1 = p\<^sub>2
*)
  (*apply(simp add: mehrverdiener_betrachtet_nur_ausgangszustand)*)
  oops text\<open>TODO: finish, gilt aber nicht\<close> (*TODO*)

  text\<open>Wenn die Steuerfunktion monoton ist, dann kann ich auch einen sehr
eingeschraenken kat imp zeigen.\<close>
lemma \<open>
  (\<And>e1 e2. e1 \<le> e2 \<Longrightarrow> steuerberechnung e1 \<le> steuerberechnung e2) \<Longrightarrow>
  ha = Handlungsabsicht (\<lambda>ich w. Some (Steuerwelt ((\<lambda>e. e - steuerberechnung e) \<circ> (get_einkommen w)))) \<Longrightarrow>
  kategorischer_imperativ_auf ha welt
    (Maxime 
      (\<lambda>ich handlung.
           (\<forall>p\<in>mehrverdiener ich handlung.
                steuerlast ich handlung \<le> steuerlast p handlung)))\<close>
  apply(cases \<open>welt\<close>, rename_tac eink, simp add:)
  apply(rule kategorischer_imperativ_aufI, rename_tac eink ich p1 p2)
  apply(case_tac \<open>ha\<close>, rename_tac h, simp)
  apply(simp add: handeln_def nachher_handeln.simps)
  done




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
lemma \<open>beispiel_case_law_relativ initialwelt (Handlungsabsicht (\<lambda>ich welt. Some welt)) =
  Gesetz {(\<section> 1, Rechtsnorm (Tatbestand []) (Rechtsfolge Erlaubnis))}\<close> by eval


subsection\<open>Beispiel: Ich zahle 1 Steuer\<close>
text\<open>Das funktioniert nicht:\<close>
definition \<open>ich_zahle_1_steuer ich welt \<equiv>
  Some (Steuerwelt ((get_einkommen welt)(ich -= 1)))\<close>
lemma \<open>beispiel_case_law_absolut initialwelt (Handlungsabsicht ich_zahle_1_steuer) =
  Gesetz
  {(\<section> 1,
    Rechtsnorm
     (Tatbestand
       ([(Alice, 8), (Bob, 3), (Carol, 0), (Eve, 5)],
        [(Alice, 7), (Bob, 3), (Carol, 0), (Eve, 5)]))
     (Rechtsfolge Verbot))}\<close> by eval
lemma \<open>beispiel_case_law_relativ initialwelt (Handlungsabsicht ich_zahle_1_steuer) =
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
  Some (Steuerwelt ((\<lambda>e. e - 1) \<circ> (get_einkommen welt)))\<close>
lemma \<open>beispiel_case_law_absolut initialwelt (Handlungsabsicht jeder_zahle_1_steuer) =
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
lemma \<open>beispiel_case_law_relativ initialwelt (Handlungsabsicht jeder_zahle_1_steuer) =
  Gesetz
  {(\<section> 1,
    Rechtsnorm
     (Tatbestand [Verliert Alice 1, Verliert Bob 1, Verliert Carol 1, Verliert Eve 1])
     (Rechtsfolge Erlaubnis))}\<close> by eval


subsection\<open>Beispiel: Vereinfachtes Deutsches Steuersystem\<close>
text\<open>Jetzt kommt die Steuern.thy ins Spiel.\<close>

definition jeder_zahlt :: \<open>(nat \<Rightarrow> nat) \<Rightarrow> 'a \<Rightarrow> steuerwelt \<Rightarrow> steuerwelt\<close> where
  \<open>jeder_zahlt steuerberechnung ich welt \<equiv>
    Steuerwelt ((\<lambda>e. e - steuerberechnung e) \<circ> nat \<circ> (get_einkommen welt))\<close>

definition \<open>jeder_zahlt_einkommenssteuer p w \<equiv> Some (jeder_zahlt einkommenssteuer p w)\<close>


text\<open>Bei dem geringen Einkommen der \<^const>\<open>initialwelt\<close> zahlt keiner Steuern.\<close>
lemma \<open>beispiel_case_law_absolut initialwelt (Handlungsabsicht jeder_zahlt_einkommenssteuer) = 
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
  (Handlungsabsicht jeder_zahlt_einkommenssteuer)
  =
  Gesetz
  {(\<section> 1,
    Rechtsnorm (Tatbestand [Verliert Bob 511, Verliert Eve 1857])
     (Rechtsfolge Erlaubnis))}\<close> by eval


section\<open>Vereinfachtes Deutsches Steuersystem vs. die Steuermaxime\<close>
text\<open>Die Anforderungen für ein \<^locale>\<open>steuersystem\<close> und die \<^const>\<open>maxime_steuern\<close> sind vereinbar.\<close>
lemma steuersystem_imp_maxime:
  \<open>steuersystem steuersystem_impl \<Longrightarrow>
        (\<forall>welt. moralisch welt
                maxime_steuern
                (Handlungsabsicht (\<lambda>p w. Some (jeder_zahlt steuersystem_impl p w))))\<close>
   apply(simp add: maxime_steuern_def moralisch_unfold handeln_def nachher_handeln.simps)
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
        \<forall>welt. moralisch welt maxime_steuern (Handlungsabsicht (\<lambda>p w. Some (jeder_zahlt steuersystem_impl p w)))
        \<Longrightarrow> steuersystem steuersystem_impl\<close>
proof
  fix einkommen_b einkommen_a :: \<open>nat\<close>
  assume m: \<open>\<forall>welt. moralisch welt maxime_steuern (Handlungsabsicht (\<lambda>p w. Some (jeder_zahlt steuersystem_impl p w)))\<close>
     and a: \<open>einkommen_b \<le> einkommen_a\<close>
     and bezahlbar: \<open>\<forall>einkommen. steuersystem_impl einkommen \<le> einkommen\<close>
  from m have m':
    \<open>get_einkommen welt pA \<le> get_einkommen welt pB \<Longrightarrow>
       get_einkommen welt pA -
             int (nat (get_einkommen welt pA) - steuersystem_impl (nat (get_einkommen welt pA)))
             \<le> get_einkommen welt pB -
                int (nat (get_einkommen welt pB) - steuersystem_impl (nat (get_einkommen welt pB)))\<close>
    for welt :: \<open>steuerwelt\<close> and pA pB :: \<open>person\<close>
    by(simp add: handeln_def nachher_handeln.simps maxime_steuern_def moralisch_unfold jeder_zahlt_def bevoelkerung_def)
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
  assume m: \<open>\<forall>welt. moralisch welt maxime_steuern (Handlungsabsicht (\<lambda>p w. Some (jeder_zahlt steuersystem_impl p w)))\<close>
     and a: \<open>einkommen_b \<le> einkommen_a\<close>
  from m have m':
    \<open>get_einkommen welt pA \<le> get_einkommen welt pB \<Longrightarrow>
       nat (get_einkommen welt pA) - steuersystem_impl (nat (get_einkommen welt pA))
       \<le> nat (get_einkommen welt pB) - steuersystem_impl (nat (get_einkommen welt pB))\<close>
    for welt :: \<open>steuerwelt\<close> and pA pB :: \<open>person\<close>
    by(simp add: handeln_def nachher_handeln.simps maxime_steuern_def moralisch_unfold jeder_zahlt_def bevoelkerung_def)
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
   \<open>(\<forall>welt. moralisch welt maxime_steuern (Handlungsabsicht (\<lambda>p w. Some (jeder_zahlt steuersystem_impl p w))))
        \<longleftrightarrow> steuersystem steuersystem_impl\<close>
  using steuersystem_imp_maxime maxime_imp_steuersystem
  using assms by blast 

end
theory BeispielSteuern
imports Zahlenwelt Maxime Steuern Aenderung KategorischerImperativ
begin


section\<open>Beispiel: Steuern\<close>
text\<open>In diesem Abschnitt kombinieren wir das vorhergehende Modell der Einkommensteuergesetzgebung
mit dem kategorischen Imperativ um ein Beispiel über moralische Aussagen über Steuern zu schaffen.\<close>

text\<open>Wir nehmen eine einfach Welt an, in der jeder Person ihr Einkommen zugeordnet wird.

Achtung: Im Unterschied zum BeispielZahlenwelt.thy modellieren wir hier nicht den Gesamtbesitz,
sondern das Jahreseinkommen. Besitz wird ignoriert.
\<close>
datatype steuerwelt = Steuerwelt
        (get_einkommen: \<open>person \<Rightarrow> int\<close>) \<comment> \<open>Einkommen jeder Person (im Zweifel 0).\<close>

(*<*)
fun steuerwps :: \<open>person \<Rightarrow> person \<Rightarrow> steuerwelt \<Rightarrow> steuerwelt\<close> where
  \<open>steuerwps p1 p2 (Steuerwelt besitz) = Steuerwelt (swap p1 p2 besitz)\<close>
(*>*)

text\<open>Die Steuerlast sagt, wie viel Steuern gezahlt werden.\<close>
fun steuerlast :: \<open>person \<Rightarrow> steuerwelt handlung \<Rightarrow> int\<close> where
  \<open>steuerlast p (Handlung vor nach) = ((get_einkommen vor) p) - ((get_einkommen nach) p)\<close>

text\<open>Das Einkommen vor Steuer wird brutto genannt.\<close>
fun brutto :: \<open>person \<Rightarrow> steuerwelt handlung \<Rightarrow> int\<close> where
  \<open>brutto p (Handlung vor nach) = (get_einkommen vor) p\<close>
text\<open>Das Einkommen nach Steuer wird netto genannt.\<close>
fun netto :: \<open>person \<Rightarrow> steuerwelt handlung \<Rightarrow> int\<close> where
  \<open>netto p (Handlung vor nach) = (get_einkommen nach) p\<close>


text\<open>Beispiele\<close>
beispiel \<open>steuerlast Alice (Handlung (Steuerwelt (\<euro>(Alice:=8))) (Steuerwelt (\<euro>(Alice:=5)))) = 3\<close>
  by eval
beispiel \<open>steuerlast Alice (Handlung (Steuerwelt (\<euro>(Alice:=8))) (Steuerwelt (\<euro>(Alice:=0)))) = 8\<close>
  by eval
beispiel \<open>steuerlast Bob   (Handlung (Steuerwelt (\<euro>(Alice:=8))) (Steuerwelt (\<euro>(Alice:=5)))) = 0\<close>
  by eval
beispiel \<open>steuerlast Alice (Handlung (Steuerwelt (\<euro>(Alice:=-3))) (Steuerwelt (\<euro>(Alice:=-4)))) = 1\<close>
  by eval
beispiel \<open>steuerlast Alice (Handlung (Steuerwelt (\<euro>(Alice:=1))) (Steuerwelt (\<euro>(Alice:=-1)))) = 2\<close>
  by eval


text\<open>Folgende Menge beinhaltet alle Personen die mehr verdienen als ich.\<close>
fun mehrverdiener :: \<open>person \<Rightarrow> steuerwelt handlung \<Rightarrow> person set\<close> where
  \<open>mehrverdiener ich (Handlung vor nach) = {p. (get_einkommen vor) p \<ge> (get_einkommen vor) ich}\<close>

beispiel \<open>mehrverdiener Alice
        (Handlung (Steuerwelt (\<euro>(Alice:=8, Bob:=12, Eve:=7))) (Steuerwelt (\<euro>(Alice:=5))))
       = {Alice, Bob}\<close> by eval

(*<*)
lemma mehrverdiener_betrachtet_nur_ausgangszustand:
  \<open>mehrverdiener p (handeln p' welt h) = mehrverdiener p (Handlung welt welt)\<close>
  by (metis handlung.collapse mehrverdiener.simps vorher_handeln)
(*>*)

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

(*okay_MaximeConj sagt ich koennte auch MaximeConj nehmen.
TODO: jeder submaxime eine eigene Definition geben und per MaximeConj kombinieren!*)

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
  apply(rename_tac eink p1 p2 p)
  by(rule swap_cases, simp_all add: swap_a swap_b swap_nothing)
(*>*)


text\<open>Wenn die Steuerfunktion monoton ist,
dann können wir auch einen sehr eingeschränkten kategorischen Imperativ zeigen.\<close>
lemma katimp_auf_handlungsabsicht_monoton:
  \<open>(\<And>e1 e2. e1 \<le> e2 \<Longrightarrow> steuerberechnung e1 \<le> steuerberechnung e2) \<Longrightarrow>
  ha = Handlungsabsicht
          (\<lambda>ich w. Some (Steuerwelt ((\<lambda>e. e - steuerberechnung e) \<circ> (get_einkommen w)))) \<Longrightarrow>
  kategorischer_imperativ_auf ha welt
    (Maxime 
      (\<lambda>ich handlung.
           (\<forall>p\<in>mehrverdiener ich handlung.
                steuerlast ich handlung \<le> steuerlast p handlung)))\<close>
  apply(cases \<open>welt\<close>, rename_tac eink, simp)
  apply(rule kategorischer_imperativ_aufI, rename_tac eink ich p1 p2)
  apply(simp add: handeln_def nachher_handeln.simps)
  done


subsection\<open>Beispiel: Keiner Zahlt Steuern\<close>

text\<open>Die Maxime ist im Beispiel erfüllt, da wir immer nur kleiner-gleich fordern!\<close>
beispiel \<open>moralisch (Steuerwelt (\<euro>(Alice:=8, Bob:=3, Eve:= 5)))
                  maxime_steuern (Handlungsabsicht (\<lambda>ich welt. Some welt))\<close> by eval


subsection\<open>Beispiel: Ich zahle 1 Steuer\<close>
text\<open>Das funktioniert nicht:\<close>
definition \<open>ich_zahle_1_steuer ich welt \<equiv>
  Some (Steuerwelt \<lbrakk>(get_einkommen welt)(ich -= 1)\<rbrakk>)\<close>
beispiel \<open>\<not> moralisch (Steuerwelt (\<euro>(Alice:=8, Bob:=3, Eve:= 5)))
                    maxime_steuern (Handlungsabsicht ich_zahle_1_steuer)\<close> by eval

text\<open>Denn jeder muss Steuer zahlen!
Ich finde es super spannend, dass hier faktisch ein Gleichbehandlungsgrundsatz rausfällt,
ohne dass wir so Etwas jemals explizit gefordert haben.
\<close>

subsection\<open>Beiepiel: Jeder zahle 1 Steuer\<close>
text\<open>Jeder muss steuern zahlen: funktioniert.

Das \<^term>\<open>ich\<close> wird gar nicht verwendet, da jeder Steuern zahlt.\<close>
definition \<open>jeder_zahle_1_steuer ich welt \<equiv>
  Some (Steuerwelt ((\<lambda>e. e - 1) \<circ> (get_einkommen welt)))\<close>
beispiel \<open>moralisch (Steuerwelt (\<euro>(Alice:=8, Bob:=3, Eve:= 5)))
                 maxime_steuern (Handlungsabsicht jeder_zahle_1_steuer)\<close> by eval


subsection\<open>Beispiel: Vereinfachtes Deutsches Steuersystem\<close>
text\<open>Jetzt kommt die Steuern.thy ins Spiel.\<close>

definition jeder_zahlt :: \<open>(nat \<Rightarrow> nat) \<Rightarrow> 'a \<Rightarrow> steuerwelt \<Rightarrow> steuerwelt\<close> where
  \<open>jeder_zahlt steuerberechnung ich welt \<equiv>
    Steuerwelt ((\<lambda>e. e - steuerberechnung e) \<circ> nat \<circ> (get_einkommen welt))\<close>

(*<*)
lemma jeder_zahlt_ignoriert_person:
  \<open>jeder_zahlt steuersystem_impl p w = jeder_zahlt steuersystem_impl p' w\<close>
  by(simp add: jeder_zahlt_def)
(*>*)

definition \<open>jeder_zahlt_einkommenssteuer p w \<equiv> Some (jeder_zahlt einkommenssteuer p w)\<close>


text\<open>Bei dem geringen Einkommen der \<^term>\<open>Steuerwelt (\<euro>(Alice:=8, Bob:=3, Eve:= 5))\<close> zahlt keiner Steuern.\<close>

beispiel \<open>ist_noop 
  (handeln Alice(Steuerwelt (\<euro>(Alice:=8, Bob:=3, Eve:= 5)))
             (Handlungsabsicht jeder_zahlt_einkommenssteuer))\<close> by eval

beispiel \<open>moralisch (Steuerwelt (\<euro>(Alice:=8, Bob:=3, Eve:= 5)))
                  maxime_steuern (Handlungsabsicht jeder_zahlt_einkommenssteuer)\<close> by eval


text\<open>Für höhere Einkommen erhalten wir plausible Werte und niemand rutscht ins negative:\<close>
beispiel \<open>delta_steuerwelt
      (handeln
      Alice (Steuerwelt (\<euro>(Alice:=10000, Bob:=14000, Eve:= 20000)))
      (Handlungsabsicht jeder_zahlt_einkommenssteuer))
  = [Verliert Bob 511, Verliert Eve 1857]\<close> by eval
beispiel \<open>moralisch
  (Steuerwelt (\<euro>(Alice:=10000, Bob:=14000, Eve:= 20000)))
  maxime_steuern
  (Handlungsabsicht jeder_zahlt_einkommenssteuer)\<close> by eval

text\<open>Unser Beispiel erfüllt auch den kategorischen Imperativ.\<close>
beispiel \<open>erzeuge_beispiel
    steuerwps (Steuerwelt (\<euro>(Alice:=10000, Bob:=14000, Eve:= 20000)))
    [Handlungsabsicht jeder_zahlt_einkommenssteuer]
    maxime_steuern
  =
  Some
    \<lparr>
     bsp_erfuellte_maxime = True,
     bsp_erlaubte_handlungen = [Handlungsabsicht jeder_zahlt_einkommenssteuer],
     bsp_verbotene_handlungen = [],
     bsp_uneindeutige_handlungen = []
    \<rparr>\<close>
  by beispiel_tac

subsection\<open>Vereinfachtes Deutsches Steuersystem vs. die Steuermaxime\<close>
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

(*<*)
text\<open>Danke ihr nats. Macht also keinen Sinn das als Annahme in die Maxime zu packen....\<close>
lemma steuern_kleiner_einkommen_nat:
      \<open>steuerlast ich (Handlung welt (jeder_zahlt steuersystem_impl ich welt))
         \<le> brutto ich (Handlung welt (jeder_zahlt steuersystem_impl ich welt))\<close>
  apply(simp del: steuerlast.simps)
  apply(subst steuerlast.simps)
  apply(simp add: jeder_zahlt_def)
  done
(*>*)


text\<open>Mit genug zusätzlichen Annahmen gilt auch die Rückrichtung:\<close>
lemma maxime_imp_steuersystem:
  \<open>\<forall>einkommen. steuersystem_impl einkommen \<le> einkommen \<Longrightarrow>
   \<forall>einkommen. einkommen \<le> 9888 \<longrightarrow> steuersystem_impl einkommen = 0 \<Longrightarrow>
   \<forall>welt. moralisch welt maxime_steuern
             (Handlungsabsicht (\<lambda>p w. Some (jeder_zahlt steuersystem_impl p w)))
    \<Longrightarrow> steuersystem steuersystem_impl\<close>
proof
  fix einkommen_b einkommen_a :: \<open>nat\<close>
  assume m: \<open>\<forall>welt. moralisch welt maxime_steuern
                      (Handlungsabsicht (\<lambda>p w. Some (jeder_zahlt steuersystem_impl p w)))\<close>
     and a: \<open>einkommen_b \<le> einkommen_a\<close>
     and bezahlbar: \<open>\<forall>einkommen. steuersystem_impl einkommen \<le> einkommen\<close>
  from m have m':
    \<open>get_einkommen welt pA \<le> get_einkommen welt pB \<Longrightarrow>
       get_einkommen welt pA -
             int (nat (get_einkommen welt pA) - steuersystem_impl (nat (get_einkommen welt pA)))
             \<le> get_einkommen welt pB -
                int (nat (get_einkommen welt pB) - steuersystem_impl (nat (get_einkommen welt pB)))\<close>
    for welt :: \<open>steuerwelt\<close> and pA pB :: \<open>person\<close>
    by(simp add: handeln_def nachher_handeln.simps
                 maxime_steuern_def moralisch_unfold jeder_zahlt_def bevoelkerung_def)
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
  assume m: \<open>\<forall>welt. moralisch welt maxime_steuern
                        (Handlungsabsicht (\<lambda>p w. Some (jeder_zahlt steuersystem_impl p w)))\<close>
     and a: \<open>einkommen_b \<le> einkommen_a\<close>
  from m have m':
    \<open>get_einkommen welt pA \<le> get_einkommen welt pB \<Longrightarrow>
       nat (get_einkommen welt pA) - steuersystem_impl (nat (get_einkommen welt pA))
       \<le> nat (get_einkommen welt pB) - steuersystem_impl (nat (get_einkommen welt pB))\<close>
    for welt :: \<open>steuerwelt\<close> and pA pB :: \<open>person\<close>
    by(simp add: handeln_def nachher_handeln.simps maxime_steuern_def moralisch_unfold
                 jeder_zahlt_def bevoelkerung_def)
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
Dass die eine Richtung gilt (Maxime impliziert \<^const>\<open>steuersystem\<close>),
die andere Richtung (\<^const>\<open>steuersystem\<close> impliziert Maxime) jedoch nicht ohne weiter Annahmen,
stimmt auch mit Russels Beobachtung überein:
"Kants Maxime [das allgemeine Konzept, nicht meine Implementierung]
scheint tatsächlich ein notwendiges, jedoch nicht \<^emph>\<open>ausreichendes\<close> Kriterium der Tugend zu geben"
@{cite russellphi}.
Insbesondere Russels Folgesatz freut mich, da er mir bestätigt, dass unsere extensionale
Betrachtung von Handlungen vielversprechend ist:
"Um ein ausreichendes Kriterium zu gewinnen, müßten wir Kants rein formalen Standpunkt aufgeben
und die Wirkung der Handlungen in Betracht ziehen" @{cite russellphi}.
\<close>


text\<open>
Für jedes \<^term_type>\<open>steuersystem_impl :: nat \<Rightarrow> nat\<close>,
mit zwei weiteren Annahmen
gilt, dass \<^locale>\<open>steuersystem\<close> und \<^const>\<open>maxime_steuern\<close> in der \<^const>\<open>jeder_zahlt\<close> Implementierung
äquivalent sind.\<close>

theorem
  fixes steuersystem_impl :: \<open>nat \<Rightarrow> nat\<close>
  assumes steuer_kleiner_einkommen: \<open>\<forall>einkommen. steuersystem_impl einkommen \<le> einkommen\<close>
      and existenzminimum: \<open>\<forall>einkommen. einkommen \<le> 9888 \<longrightarrow> steuersystem_impl einkommen = 0\<close>
    shows
     \<open>(\<forall>welt. moralisch welt maxime_steuern
                (Handlungsabsicht (\<lambda>p w. Some (jeder_zahlt steuersystem_impl p w))))
      \<longleftrightarrow>
      steuersystem steuersystem_impl\<close>
  using steuersystem_imp_maxime maxime_imp_steuersystem
  using assms by blast 

text\<open>Da jede Steuersystemimplementierung welche \<^locale>\<open>steuersystem\<close> erfüllt auch
moralisch ist (lemma @{thm [source] steuersystem_imp_maxime}),
erfüllt damit auch jedes solche System den kategorischen Imperativ.\<close>
corollary steuersystem_imp_kaptimp:
 \<open>steuersystem steuersystem_impl \<Longrightarrow>
     kategorischer_imperativ_auf
        (Handlungsabsicht (\<lambda>p w. Some (jeder_zahlt steuersystem_impl p w)))
        welt
        maxime_steuern\<close>
  apply(drule steuersystem_imp_maxime)
  by (simp add: kategorischer_imperativ_auf_def)

text\<open>Und daraus folgt, dass auch \<^const>\<open>jeder_zahlt_einkommenssteuer\<close>
den kategorischen Imperativ erfüllt.\<close>
corollary
 \<open>steuersystem steuersystem_impl \<Longrightarrow>
     kategorischer_imperativ_auf
        (Handlungsabsicht jeder_zahlt_einkommenssteuer)
        welt
        maxime_steuern\<close>
  unfolding jeder_zahlt_einkommenssteuer_def
  apply(rule steuersystem_imp_kaptimp)
  by (simp add: steuersystem_axioms)


end
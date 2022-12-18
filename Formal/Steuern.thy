theory Steuern
imports Main HOL.Real Percentage ExecutableHelper
begin

section\<open>Einkommensteuergesetzgebung\<close>


text\<open>In diesem Abschnitt werden wir eine versuchen die Grundlagen der
Einkommenssteuergesetzgebung zu modellieren.\<close>

(*<*)
text\<open>Helper\<close>
definition floor :: \<open>real \<Rightarrow> nat\<close> where
  \<open>floor x \<equiv> nat \<lfloor>x\<rfloor>\<close>

lemma floorD: \<open>a \<le> b \<Longrightarrow> floor a \<le> floor b\<close>
  apply(simp add: floor_def)
  by linarith

lemma floor_minusD:
  fixes a :: \<open>nat\<close> and a' :: \<open>real\<close>
  shows  \<open>a \<le> b \<Longrightarrow> a - a' \<le> b - b' \<Longrightarrow> a - floor a' \<le> b - floor b'\<close>
  apply(simp add: floor_def)
  by linarith
(*>*)


text\<open>Folgendes Modell basiert auf einer stark vereinfachten Version des deutschen Steuerrechts.
Wenn ich Wikipedia richtig verstanden habe, habe ich sogar aus Versehen einen Teil des 
österreichischen Steuersystem gebaut mit deutschen Konstanten.
\<close>


text\<open>Folgende @{command locale} nimmt an, dass wir eine Funktion
\<^term_type>\<open>steuer :: nat \<Rightarrow> nat\<close> haben, welche basierend auf dem Einkommen
die zu zahlende Steuer berechnet.

Die \<^term>\<open>steuer\<close> Funktion arbeitet auf natürlichen Zahlen.
Wir nehmen an, dass einfach immer auf ganze Geldbeträge gerundet wird.
Wie im deutschen System.

Die @{command locale} einhält einige Definition, gegeben die \<^term>\<open>steuer\<close> Funktion.

Eine konkrete \<^term>\<open>steuer\<close> Funktion wird noch nicht gegeben.
\<close>

locale steuer_defs =
  fixes steuer :: \<open>nat \<Rightarrow> nat\<close> \<comment> \<open>Funktion: Einkommen -> Steuer\<close>
begin
  definition brutto :: \<open>nat \<Rightarrow> nat\<close> where
    \<open>brutto einkommen \<equiv> einkommen\<close>
  definition netto :: \<open>nat \<Rightarrow> nat\<close> where
    \<open>netto einkommen \<equiv> einkommen - (steuer einkommen)\<close>
  definition steuersatz :: \<open>nat \<Rightarrow> percentage\<close> where
    \<open>steuersatz einkommen \<equiv> percentage ((steuer einkommen) / einkommen)\<close>
end


text\<open>Beispiel. Die \<^term>\<open>steuer\<close> Funktion sagt, man muss 25 Prozent Steuern zahlen:\<close>
definition beispiel_25prozent_steuer :: \<open>nat \<Rightarrow> nat\<close> where
  \<open>beispiel_25prozent_steuer e \<equiv> nat \<lfloor>real e * (percentage 0.25)\<rfloor>\<close>

lemma
  \<open>beispiel_25prozent_steuer 100 = 25\<close>
  \<open>steuer_defs.brutto 100 = 100\<close>
  \<open>steuer_defs.netto beispiel_25prozent_steuer 100 = 75\<close>
  \<open>steuer_defs.steuersatz beispiel_25prozent_steuer 100 = percentage 0.25\<close>
  by(simp add: steuer_defs.brutto_def beispiel_25prozent_steuer_def
            steuer_defs.netto_def percentage_code steuer_defs.steuersatz_def)+


text\<open>
Folgende @{command locale} erweitert die \<^locale>\<open>steuer_defs\<close> @{command locale} und stellt
einige Anforderungen die eine gültige \<^term>\<open>steuer\<close> Funktion erfüllen muss.

  \<^item> Wer mehr Einkommen hat, muss auch mehr Steuern zahlen.
  \<^item> Leistung muss sich lohnen:
    Wer mehr Einkommen hat muss auch nach Abzug der Steuer mehr übrig haben.
  \<^item> Existenzminimum: Es gibt ein Existenzminimum, welches nicht besteuert werden darf.
\<close>
locale steuersystem = steuer_defs +
  assumes wer_hat_der_gibt:
    \<open>einkommen_a \<ge> einkommen_b \<Longrightarrow> steuer einkommen_a \<ge> steuer einkommen_b\<close>

  and leistung_lohnt_sich:
    \<open>einkommen_a \<ge> einkommen_b \<Longrightarrow> netto einkommen_a \<ge> netto einkommen_b\<close>

  \<comment> \<open>Ein Existenzminimum wird nicht versteuert.
      Zahl Deutschland 2022, vermutlich sogar die falsche Zahl.\<close>
  and existenzminimum:
    \<open>einkommen \<le> 9888 \<Longrightarrow> steuer einkommen = 0\<close>

(*
  \<comment> \<open>"Steuerprogression bedeutet das Ansteigen des Steuersatzes in Abhängigkeit vom zu
       versteuernden Einkommen oder Vermögen." \<^url>\<open>https://de.wikipedia.org/wiki/Steuerprogression\<close>\<close>
  and progression: "einkommen_a \<ge> einkommen_b \<Longrightarrow> steuersatz einkommen_a \<ge> steuersatz einkommen_b"
*)
begin

end

text\<open>Eigentlich hätte ich gerne noch eine weitere Anforderung.
\<^url>\<open>https://de.wikipedia.org/wiki/Steuerprogression\<close> sagt
"Steuerprogression bedeutet das Ansteigen des Steuersatzes in Abhängigkeit vom zu
 versteuernden Einkommen oder Vermögen."

Formal betrachtet würde das bedeuten
\<^term>\<open>einkommen_a \<ge> einkommen_b
  \<Longrightarrow> steuer_defs.steuersatz einkommen_a \<ge> steuer_defs.steuersatz einkommen_b\<close>

Leider haben wir bereits jetzt in dem Modell eine Annahme getroffen,
die es uns quasi unmöglich macht, ein Steuersystem zu implementieren, welches die
Steuerprogression erfüllt.
Der Grund ist, dass wir die Steuerfunktion auf ganzen Zahlen definiert haben.
Aufgrund von Rundung können wir also immer Fälle haben, indem ein höheres
Einkommen einen leicht geringeren Steuersatz hat als ein geringeres Einkommen.
Beispielsweise bedeutet das für \<^const>\<open>beispiel_25prozent_steuer\<close>, dass
jemand mit 100 EUR Einkommen genau 25 Prozent Steuer zahlt,
jemand mit 103 EUR Einkommen aber nur ca 24,3 Prozent Steuer zahlt. 
\<close>

lemma
  \<open>steuer_defs.steuersatz beispiel_25prozent_steuer 100 = percentage 0.25\<close>
  \<open>steuer_defs.steuersatz beispiel_25prozent_steuer 103 = percentage (25 / 103)\<close>
  \<open>percentage (25 / 103) < percentage 0.25\<close>
  \<open>(103::nat) > 100\<close>
  by(simp add: steuer_defs.brutto_def beispiel_25prozent_steuer_def
            steuer_defs.netto_def percentage_code steuer_defs.steuersatz_def)+

text\<open>In der Praxis sollten diese kleinen Rundungsfehler kein Problem darstellen,
in diesem theoretischen Modell sorgen sie aber dafür,
dass unser Steuersystem (und wir modellieren eine vereinfachte Version des
deutschen Steuerystems) keine Steuerprogression erfüllt.\<close>

(*<*)
fun zonensteuer :: \<open>(nat \<times> percentage) list \<Rightarrow> percentage \<Rightarrow> nat \<Rightarrow> real\<close> where
   \<open>zonensteuer ((zone, prozent)#zonen) spitzensteuer e =
        ((min zone e) * prozent) + (zonensteuer zonen spitzensteuer (e - zone))\<close>
|  \<open>zonensteuer [] spitzensteuer e = e*spitzensteuer\<close>

lemma zonensteuermono: \<open>e1 \<le> e2
  \<Longrightarrow> zonensteuer zs spitzensteuer e1 \<le> zonensteuer zs spitzensteuer e2\<close>
  apply(induction \<open>zs\<close> arbitrary: \<open>e1\<close> \<open>e2\<close>)
   apply(simp add: mult_right_mono percentage_range; fail)
  apply(rename_tac z zs e1 e2, case_tac \<open>z\<close>, rename_tac zone prozent)
  apply(simp)
  apply(rule Groups.add_mono_thms_linordered_semiring(1), rule conjI)
   defer
   apply(simp; fail)
  by(simp add: mult_right_mono percentage_range)

text\<open>Kein Einkommen -> keine Steuer\<close>
lemma zonensteuer_zero: \<open>zonensteuer ls p 0 = 0\<close>
  by(induction \<open>ls\<close>) auto

text\<open>Steuer ist immer positiv.\<close>
  (*Da das Einkommen ein nat ist, ist das Einkommen hier auch immer positiv.
    Eventuell will ich aber mal das Einkommen auf int aendern,
    dann muss das folgende Lemma aber immernoch gelten!*)
lemma zonensteuer_pos: \<open>zonensteuer ls p e \<ge> 0\<close>
  apply(induction \<open>ls\<close>)
   apply(simp add: percentage_range)
  by (metis zero_le zonensteuer_zero zonensteuermono)
  
text\<open>Steuer kann nicht höher sein als das Einkommen.\<close>
lemma zonensteuer_limit: \<open>zonensteuer ls spitzensteuer einkommen \<le> einkommen\<close>
  apply(induction \<open>ls\<close> arbitrary: \<open>einkommen\<close>)
   apply(simp)
   apply (simp add: real_of_percentage_mult; fail)
  apply(rename_tac z zs einkommen, case_tac \<open>z\<close>, rename_tac zone prozent)
  apply(simp)
  apply(case_tac \<open>zone \<le>  einkommen\<close>)
  apply(simp)
  apply(subst percentage_add_limit_helper, simp_all)
  apply (metis of_nat_diff)
  by (simp add: real_of_percentage_mult zonensteuer_zero)

lemma zonensteuer_leistung_lohnt_sich: \<open>e1 \<le> e2
  \<Longrightarrow> e1 - zonensteuer zs spitzensteuer e1 \<le> e2 - zonensteuer zs spitzensteuer e2\<close>
proof(induction \<open>zs\<close> arbitrary: \<open>e1\<close> \<open>e2\<close>)
  case Nil
  then show \<open>?case\<close>
   apply(simp)
   using real_of_percentage_range by(metis
      diff_ge_0_iff_ge mult.right_neutral mult_right_mono
      of_nat_le_iff right_diff_distrib') 
next
  case (Cons z zs)
  obtain zone prozent where z: \<open>z = (zone, prozent)\<close> by(cases \<open>z\<close>)
  have \<open>e1 - zone \<le> e2 - zone\<close> using Cons.prems diff_le_mono by blast
  from Cons.IH[OF this] have IH:
    \<open> (e1 - zone) - zonensteuer zs spitzensteuer (e1 - zone)
      \<le> (e2 - zone) - zonensteuer zs spitzensteuer (e2 - zone)\<close> .
  then have IH':
    \<open>e1 - zonensteuer zs spitzensteuer (e1 - zone)
      \<le> e2 - zonensteuer zs spitzensteuer (e2 - zone)\<close>
    using Cons.prems by linarith
  from Cons.prems percentage_nat_diff_mult_right_mono have e1e2diff:
    \<open>e1 - e1 * prozent \<le> e2 - e2 * prozent\<close> by simp
  have
    \<open>e1 - (min zone e1 * prozent + zonensteuer zs spitzensteuer (e1 - zone))
      \<le> e2 - (min zone e2 * prozent + zonensteuer zs spitzensteuer (e2 - zone))\<close>
    proof(cases \<open>e1 \<le> zone\<close>)
      case True
      assume \<open>e1 \<le> zone\<close>
      have e1: \<open>min (real zone) e1 = e1\<close> using \<open>e1 \<le> zone\<close> by simp
      from percentage_nat_diff_mult_right_mono have e1zonediff:
       \<open>e1 - e1 * prozent \<le> zone - zone * prozent\<close> using True by auto
      show \<open>?thesis\<close>
      proof(cases \<open>e2 \<le> zone\<close>)
        case True
        then show \<open>?thesis\<close>
          apply(simp add: e1 \<open>e1 \<le> zone\<close>)
          using e1e2diff by (simp)
      next
        case False
        from False have \<open>zone < e2\<close> by simp
        from this obtain mehr where mehr: \<open>e2 = zone + mehr\<close>
          using less_imp_add_positive by blast
        have zonensteuer_limit: \<open>zonensteuer zs spitzensteuer mehr \<le> mehr\<close>
          using zonensteuer_limit by simp
        from False show \<open>?thesis\<close>
          apply(simp add: e1)
          apply(simp add: \<open>e1 \<le> zone\<close>)
          apply(simp add: mehr)
          apply(simp add: zonensteuer_zero)
          using e1zonediff zonensteuer_limit by linarith
        qed
    next
      case False
      have e1: \<open>min zone e1 = zone\<close> using False by auto
      have e2: \<open>min zone e2 = zone\<close> using False Cons.prems by auto
      from IH' e1 e2 show \<open>?thesis\<close> by (simp)
    qed
  then show \<open>?case\<close>
    by(simp add: z)
qed

definition steuerzonen2022 :: \<open>(nat \<times> percentage) list\<close> where
  \<open>steuerzonen2022 \<equiv> [
                       (10347, percentage 0),
                       (4579, percentage 0.14),
                       (43670, percentage 0.2397),
                       (219229, percentage 0.42)
                      ]\<close>


fun steuerzonenAbs :: \<open>(nat \<times> percentage) list \<Rightarrow> (nat \<times> percentage) list\<close> where
   \<open>steuerzonenAbs [] = []\<close>
 |  \<open>steuerzonenAbs ((zone, prozent)#zonen) = 
      (zone,prozent)#(map (\<lambda>(z,p). (zone+z, p)) (steuerzonenAbs zonen))\<close>
(*>*)

text\<open>Die folgende Liste,
basierend auf \<^url>\<open>https://de.wikipedia.org/wiki/Einkommensteuer_(Deutschland)#Tarif_2022\<close>,
sagt in welchem Bereich welcher Prozentsatz an Steuern zu zahlen ist.
Beispielsweise sind die ersten \<^term>\<open>10347::nat\<close> steuerfrei.
\<close>
definition steuerbuckets2022 :: \<open>(nat \<times> percentage) list\<close> where
  \<open>steuerbuckets2022 \<equiv> [
                       (10347, percentage 0),
                       (14926, percentage 0.14),
                       (58596, percentage 0.2397),
                       (277825, percentage 0.42)
                      ]\<close>
                       (*(\<infinity>, 0.45)*)

text\<open>Für jedes Einkommen über 277825 gilt der Spitzensteuersatz von 45 Prozent.
Wir ignorieren die Progressionsfaktoren in Zone 2 und 3.\<close>

(*<*)
lemma steuerbuckets2022: \<open>steuerbuckets2022 = steuerzonenAbs steuerzonen2022\<close>
  by(simp add: steuerbuckets2022_def steuerzonen2022_def)

fun wfSteuerbuckets :: \<open>(nat \<times> percentage) list \<Rightarrow> bool\<close> where
  \<open>wfSteuerbuckets [] = True\<close>
| \<open>wfSteuerbuckets [bs] = True\<close>
| \<open>wfSteuerbuckets ((b1, p1)#(b2, p2)#bs) \<longleftrightarrow> b1 \<le> b2 \<and> wfSteuerbuckets ((b2,p2)#bs)\<close>
(*>*)

text\<open>Folgende Funktion berechnet die zu zahlende Steuer, basierend auf einer Steuerbucketliste.\<close>

fun bucketsteuerAbs :: \<open>(nat \<times> percentage) list \<Rightarrow> percentage \<Rightarrow> nat \<Rightarrow> real\<close> where
   \<open>bucketsteuerAbs ((bis, prozent)#mehr) spitzensteuer e =
        ((min bis e) * prozent)
        + (bucketsteuerAbs (map (\<lambda>(s,p). (s-bis,p)) mehr) spitzensteuer (e - bis))\<close>
|  \<open>bucketsteuerAbs [] spitzensteuer e = e*spitzensteuer\<close>

(*<*)
lemma wfSteuerbucketsConsD: \<open>wfSteuerbuckets (z#zs) \<Longrightarrow> wfSteuerbuckets zs\<close>
  apply(case_tac \<open>z\<close>, simp)
  using wfSteuerbuckets.elims(3) by fastforce

lemma wfSteuerbucketsMapD: 
  \<open>wfSteuerbuckets (map (\<lambda>(z, y). (zone + z, y)) zs) \<Longrightarrow>  wfSteuerbuckets zs\<close>
  apply(induction \<open>zs\<close>)
   apply(simp)
  apply(rename_tac z zs, case_tac \<open>z\<close>)
  apply(simp)
  apply(case_tac \<open>zs\<close>)
   apply(simp)
  apply(simp)
  by auto
  

lemma mapHelp1: \<open>wfSteuerbuckets zs \<Longrightarrow>
       (map ((\<lambda>(s, y). (s - x, y)) \<circ> (\<lambda>(z, y). (x + z, y)))) zs = zs\<close>
  apply(induction \<open>zs\<close>)
   apply(simp; fail)
  apply(rename_tac z zs, case_tac \<open>z\<close>, rename_tac zone prozent)
  apply(simp)
  apply(simp add: wfSteuerbucketsConsD)
  done

lemma bucketsteuerAbs_zonensteuer:
  \<open>wfSteuerbuckets (steuerzonenAbs zs) \<Longrightarrow>
       bucketsteuerAbs (steuerzonenAbs zs) spitzensteuer e
       = zonensteuer zs spitzensteuer e\<close>
  apply(induction \<open>zs\<close> arbitrary:\<open>e\<close>)
   apply(simp; fail)
  apply(rename_tac z zs e, case_tac \<open>z\<close>, rename_tac zone prozent)
  apply(simp)
  apply(subgoal_tac \<open>wfSteuerbuckets (steuerzonenAbs zs)\<close>)
   apply(subst mapHelp1)
    apply(simp; fail)
   apply(simp; fail)
  apply(simp)
  apply(drule wfSteuerbucketsConsD)
  using wfSteuerbucketsMapD by simp
(*>*)

text\<open>Die Einkommenssteuerberechnung, mit Spitzensteuersatz 45 Prozent und finalem Abrunden.\<close>
definition einkommenssteuer :: \<open>nat \<Rightarrow> nat\<close> where
  \<open>einkommenssteuer einkommen \<equiv>
    floor (bucketsteuerAbs steuerbuckets2022 (percentage  0.45) einkommen)\<close>

text\<open>Beispiel. Alles unter dem Existenzminimum ist steuerfrei:\<close>
lemma \<open>einkommenssteuer 10 = 0\<close> by eval
lemma \<open>einkommenssteuer 10000 = 0\<close> by eval

text\<open>Für ein Einkommen nur knapp über dem Existenzminimum fällt sehr wenig Steuer an:\<close>
lemma \<open>einkommenssteuer 14000 = floor ((14000-10347)*0.14)\<close> by eval
lemma \<open>einkommenssteuer 14000 = 511\<close> by eval


text\<open>Bei einem Einkommen von 20000 EUR wird ein Teil bereits mit den höheren Steuersatz der
3. Zone besteuert:\<close>
lemma \<open>einkommenssteuer 20000 = 1857\<close> by eval
lemma \<open>einkommenssteuer 20000 =
        floor ((14926-10347)*0.14 + (20000-14926)*0.2397)\<close> by eval


text\<open>Höhere Einkommen führen zu einer höheren Steuer:\<close>
lemma \<open>einkommenssteuer 40000 = 6651\<close> by eval
lemma \<open>einkommenssteuer 60000 = 11698\<close> by eval

(*<*)
lemma einkommenssteuer:
  \<open>einkommenssteuer einkommen =
    floor (zonensteuer steuerzonen2022 (percentage 0.45) einkommen)\<close>
  apply(simp add: einkommenssteuer_def)
  apply(simp add: steuerbuckets2022)
  apply(subst bucketsteuerAbs_zonensteuer)
   apply(simp add: steuerzonen2022_def; fail)
  apply(simp)
  done
(*>*)

(*TODO: geht das ohne immer steuer_defs zu schreiben?*)

text\<open>Die \<^const>\<open>einkommenssteuer\<close> Funktion erfüllt die Anforderungen an \<^locale>\<open>steuersystem\<close>.\<close>

interpretation steuersystem
  where steuer = \<open>einkommenssteuer\<close>
proof
  fix einkommen_a and einkommen_b
  show \<open>einkommen_a \<le> einkommen_b
        \<Longrightarrow> einkommenssteuer einkommen_a \<le> einkommenssteuer einkommen_b\<close>
    apply(simp add: einkommenssteuer)
    apply(rule floorD)
    apply(rule zonensteuermono)
    by(simp)
next
  fix einkommen_a and einkommen_b
  show \<open>einkommen_b \<le> einkommen_a \<Longrightarrow>
       steuer_defs.netto einkommenssteuer einkommen_b
       \<le> steuer_defs.netto einkommenssteuer einkommen_a\<close>
    apply(simp add: einkommenssteuer steuer_defs.netto_def)
    thm floor_minusD
    apply(rule floor_minusD, simp)
    using zonensteuer_leistung_lohnt_sich by simp
next
  fix einkommen
  show \<open>einkommen \<le> 9888 \<Longrightarrow> einkommenssteuer einkommen = 0\<close>
    by(simp add: einkommenssteuer floor_def steuerzonen2022_def percentage_code)
(*next
  fix einkommen_a and einkommen_b
  show "einkommen_a \<ge> einkommen_b \<Longrightarrow>
    steuer_defs.steuersatz einkommenssteuer einkommen_a \<ge> steuer_defs.steuersatz einkommenssteuer einkommen_b"
    apply(simp add: steuer_defs.steuersatz_def einkommenssteuer)
    (*TODO*)
*)
qed

end
theory Steuern
imports Main HOL.Real Percentage
begin

section\<open>Experiment: Steuergesetzgebung\<close>

text\<open>Basierend auf einer stark vereinfachten Version des deutschen Steuerrechts.
Wenn ich Wikipedia richtig verstanden habe, habe ich sogar aus Versehen einen Teil des 
österreichischen Steuersystem gebaut mit deutschen Konstanten.\<close>


locale steuer_defs =
  fixes steuer :: "nat \<Rightarrow> nat" \<comment>\<open>Einkommen -> Steuer\<close>
begin
  definition brutto :: "nat \<Rightarrow> nat" where
    "brutto einkommen \<equiv> einkommen"
  definition netto :: "nat \<Rightarrow> nat" where
    "netto einkommen \<equiv> einkommen - (steuer einkommen)"

  (*definition steuersatz*)
end

locale steuersystem = steuer_defs +
  assumes wer_hat_der_gibt:
    "einkommen_a \<ge> einkommen_b \<Longrightarrow> steuer einkommen_a \<ge> steuer einkommen_b"
  and leistung_lohnt_sich:
    "einkommen_a \<ge> einkommen_b \<Longrightarrow> netto einkommen_a \<ge> netto einkommen_b"
begin

  (*TODO: mehr einkommen \<Rightarrow> hoeherer Steuersatz*)
end

fun zonensteuer :: "(nat \<times> percentage) list \<Rightarrow> percentage \<Rightarrow> nat \<Rightarrow> real" where
   "zonensteuer ((zone, prozent)#zonen) spitzensteuer e =
        ((min zone e) * prozent) + (zonensteuer zonen spitzensteuer (e - zone))"
|  "zonensteuer [] spitzensteuer e = e*spitzensteuer"

lemma zonensteuermono: "e1 \<le> e2
  \<Longrightarrow> zonensteuer zs spitzensteuer e1 \<le> zonensteuer zs spitzensteuer e2"
  apply(induction zs arbitrary: e1 e2)
   apply(simp add: mult_right_mono percentage_range; fail)
  apply(rename_tac z zs e1 e2, case_tac z, rename_tac zone prozent)
  apply(simp)
  apply(rule Groups.add_mono_thms_linordered_semiring(1), rule conjI)
   defer
   apply(simp; fail)
  by(simp add: mult_right_mono percentage_range)

text\<open>Kein Einkommen -> keine Steuer\<close>
lemma zonensteuer_zero: "zonensteuer ls p 0 = 0"
  by(induction ls) auto

text\<open>Steuer ist immer positiv.\<close>
  (*Da das Einkommen ein nat ist, ist das Einkommen hier auch immer positiv.
    Eventuell will ich aber mal das Einkommen auf int aendern,
    dann muss das folgende Lemma aber immernoch gelten!*)
lemma zonensteuer_pos: "zonensteuer ls p e \<ge> 0"
  apply(induction ls)
   apply(simp add: percentage_range)
  by (metis zero_le zonensteuer_zero zonensteuermono)


lemma zonensteuer_leistung_lohnt_sich: "e1 \<le> e2
  \<Longrightarrow> e1 - zonensteuer zs spitzensteuer e1 \<le> e2 - zonensteuer zs spitzensteuer e2"
proof(induction zs arbitrary: e1 e2)
  case Nil
  then show ?case
   apply(simp)
   using real_of_percentage_range by(metis
      diff_ge_0_iff_ge mult.right_neutral mult_right_mono
      of_nat_le_iff right_diff_distrib') 
next
  case (Cons z zs)
  obtain zone prozent where z: "z = (zone, prozent)" by(cases z)
  have "e1 - zone \<le> e2 - zone" using Cons.prems diff_le_mono by blast
  from Cons.IH[OF this] have IH:
    "real (e1 - zone) - zonensteuer zs spitzensteuer (e1 - zone)
      \<le> real (e2 - zone) - zonensteuer zs spitzensteuer (e2 - zone)" . (*THIS?*)
  hence IH':
    "real e1 - zonensteuer zs spitzensteuer (e1 - zone)
      \<le> real e2 - zonensteuer zs spitzensteuer (e2 - zone)"
    using Cons.prems by linarith
  from Cons.prems have
    "min (real zone) (real e1) * real_of_percentage prozent
      \<le> min (real zone) (real e2) * real_of_percentage prozent"
    using real_of_percentage_range[of prozent] by(simp add: mult_mono')
  from Cons.prems have e1e2diff:
    "real e1 - real e1 * real_of_percentage prozent
      \<le> real e2 - real e2 * real_of_percentage prozent"
    by (metis diff_ge_0_iff_ge mult.right_neutral mult_right_mono
              of_nat_le_iff percentage_range right_diff_distrib')
  have
    "real e1 -
    (min (real zone) (real e1) * real_of_percentage prozent +
     zonensteuer zs spitzensteuer (e1 - zone))
    \<le> real e2 -
       (min (real zone) (real e2) * real_of_percentage prozent +
        zonensteuer zs spitzensteuer (e2 - zone))"
    proof(cases "e1 \<le> zone")
      case True
      assume \<open>e1 \<le> zone\<close>
      have e1: "min (real zone) (real e1) = real e1" using True by simp
      show ?thesis
      proof(cases "e2 \<le> zone")
        case True
        then show ?thesis
          apply(simp add: e1)
          apply(simp add: \<open>e1 \<le> zone\<close>)
          using e1e2diff by (simp; fail)
      next
        case False
        from False have "zone < e2" by simp
        from this obtain mehr where mehr: "e2 = zone + mehr"
          using less_imp_add_positive by blast
        thm Cons.prems False \<open>e1 \<le> zone\<close> 
        
        have e1zonediff:
         "real e1 - real e1 * real_of_percentage prozent
           \<le> real zone - real zone * real_of_percentage prozent"
          by (metis (no_types, opaque_lifting) diff_ge_0_iff_ge e1 min.bounded_iff
              mult.right_neutral mult_right_mono nle_le percentage_range
              right_diff_distrib')

        (*TODO: this should be a general lemma!*)
        have zonensteuer_limit:
          "zonensteuer zs spitzensteuer mehr \<le> mehr"
          using IH True mehr zonensteuer_zero by force
  
        from False show ?thesis
          apply(simp add: e1)
          apply(simp add: \<open>e1 \<le> zone\<close>)
          apply(simp add: mehr)
          apply(simp add: zonensteuer_zero)
          using e1zonediff zonensteuer_limit by linarith
        qed
    next
      case False
      have e1: "min (real zone) (real e1) = real zone" using False by auto
      have e2: "min (real zone) (real e2) = real zone" using False Cons.prems by auto
      from IH' e1 e2 show ?thesis by (simp)
    qed
  thus ?case
    by(simp add: z)
qed


definition steuerzonen2022 :: "(nat \<times> percentage) list" where
  "steuerzonen2022 \<equiv> [
                       (10347, percentage 0),
                       (4579, percentage 0.14),
                       (43670, percentage 0.2397),
                       (219229, percentage 0.42)
                      ]"

fun steuerzonenAbs :: "(nat \<times> percentage) list \<Rightarrow> (nat \<times> percentage) list" where
   "steuerzonenAbs [] = []"
 |  "steuerzonenAbs ((zone, prozent)#zonen) = 
      (zone,prozent)#(map (\<lambda>(z,p). (zone+z, p)) (steuerzonenAbs zonen))"

definition steuerbuckets2022 :: "(nat \<times> percentage) list" where
  "steuerbuckets2022 \<equiv> [
                       (10347, percentage 0),
                       (14926, percentage 0.14),
                       (58596, percentage 0.2397),
                       (277825, percentage 0.42)
                      ]"
                       (*(\<infinity>, 0.45)*)

lemma steuerbuckets2022: "steuerbuckets2022 = steuerzonenAbs steuerzonen2022"
  by(simp add: steuerbuckets2022_def steuerzonen2022_def)

fun wfSteuerbuckets :: "(nat \<times> percentage) list \<Rightarrow> bool" where
  "wfSteuerbuckets [] = True"
| "wfSteuerbuckets [bs] = True"
| "wfSteuerbuckets ((b1, p1)#(b2, p2)#bs) \<longleftrightarrow> b1 \<le> b2 \<and> wfSteuerbuckets ((b2,p2)#bs)"

(*TODO; get rid of the map, just have spans! and derive those separators as a view ..*)
fun bucketsteuerAbs :: "(nat \<times> percentage) list \<Rightarrow> percentage \<Rightarrow> nat \<Rightarrow> real" where
   "bucketsteuerAbs ((bis, prozent)#mehr) spitzensteuer e =
        ((min bis e) * prozent)
        + (bucketsteuerAbs (map (\<lambda>(s,p). (s-bis,p)) mehr) spitzensteuer (e - bis))"
|  "bucketsteuerAbs [] spitzensteuer e = e*spitzensteuer"

lemma wfSteuerbucketsConsD: "wfSteuerbuckets (z#zs) \<Longrightarrow> wfSteuerbuckets zs"
  apply(case_tac z, simp)
  using wfSteuerbuckets.elims(3) by fastforce

lemma wfSteuerbucketsMapD: 
  "wfSteuerbuckets (map (\<lambda>(z, y). (zone + z, y)) zs) \<Longrightarrow>  wfSteuerbuckets zs"
  apply(induction zs)
   apply(simp)
  apply(rename_tac z zs, case_tac z)
  apply(simp)
  apply(case_tac zs)
   apply(simp)
  apply(simp)
  by auto
  

lemma mapHelp1: "wfSteuerbuckets zs \<Longrightarrow>
       (map ((\<lambda>(s, y). (s - x, y)) \<circ> (\<lambda>(z, y). (x + z, y)))) zs = zs"
  apply(induction zs)
   apply(simp; fail)
  apply(rename_tac z zs, case_tac z, rename_tac zone prozent)
  apply(simp)
  apply(simp add: wfSteuerbucketsConsD)
  done

lemma bucketsteuerAbs_zonensteuer:
  "wfSteuerbuckets (steuerzonenAbs zs) \<Longrightarrow>
       bucketsteuerAbs (steuerzonenAbs zs) spitzensteuer e
       = zonensteuer zs spitzensteuer e"
  apply(induction zs arbitrary:e)
   apply(simp; fail)
  apply(rename_tac z zs e, case_tac z, rename_tac zone prozent)
  apply(simp)
  apply(subgoal_tac "wfSteuerbuckets (steuerzonenAbs zs)")
   apply(subst mapHelp1)
    apply(simp; fail)
   apply(simp; fail)
  apply(simp)
  apply(drule wfSteuerbucketsConsD)
  using wfSteuerbucketsMapD by simp
  


definition floor :: "real \<Rightarrow> nat" where
  "floor x \<equiv> nat \<lfloor>x\<rfloor>"

lemma floorD: "a \<le> b \<Longrightarrow> floor a \<le> floor b"
  apply(simp add: floor_def)
  by linarith

lemma floor_minusD:
  fixes a :: nat and a' :: real
  shows  "a \<le> b \<Longrightarrow> a - a' \<le> b - b' \<Longrightarrow> a - floor a' \<le> b - floor b'"
  apply(simp add: floor_def)
  by (smt (verit, ccfv_SIG) diff_is_0_eq le_floor_iff nat_0_iff
        nat_le_real_less of_int_1 of_nat_diff of_nat_nat real_of_int_floor_gt_diff_one)

definition einkommenssteuer :: "nat \<Rightarrow> nat" where
  "einkommenssteuer einkommen \<equiv>
    floor (bucketsteuerAbs steuerbuckets2022 (percentage  0.45) einkommen)"

value \<open>einkommenssteuer 10\<close>
lemma \<open>einkommenssteuer 10 = 0\<close> by eval
lemma \<open>einkommenssteuer 10000 = 0\<close> by eval
lemma \<open>einkommenssteuer 14000 = floor ((14000-10347)*0.14)\<close> by eval
lemma \<open>einkommenssteuer 20000 =
        floor ((14926-10347)*0.14 + (20000-14926)*0.2397)\<close> by eval
value \<open>einkommenssteuer 40000\<close>
value \<open>einkommenssteuer 60000\<close>

lemma einkommenssteuer:
  "einkommenssteuer einkommen =
    floor (zonensteuer steuerzonen2022 (percentage 0.45) einkommen)"
  apply(simp add: einkommenssteuer_def)
  apply(simp add: steuerbuckets2022)
  apply(subst bucketsteuerAbs_zonensteuer)
   apply(simp add: steuerzonen2022_def; fail)
  apply(simp)
  done

interpretation steuersystem
  where steuer = einkommenssteuer
proof
  fix einkommen_a and einkommen_b
  show "einkommen_a \<le> einkommen_b
        \<Longrightarrow> einkommenssteuer einkommen_a \<le> einkommenssteuer einkommen_b"
    apply(simp add: einkommenssteuer)
    apply(rule floorD)
    apply(rule zonensteuermono)
    by(simp)
next
  fix einkommen_a and einkommen_b
  show "einkommen_b \<le> einkommen_a \<Longrightarrow>
       steuer_defs.netto einkommenssteuer einkommen_b
       \<le> steuer_defs.netto einkommenssteuer einkommen_a"
    apply(simp add: einkommenssteuer steuer_defs.netto_def)
    thm floor_minusD
    apply(rule floor_minusD, simp)
    using zonensteuer_leistung_lohnt_sich by simp
qed


end
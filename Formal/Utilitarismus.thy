theory Utilitarismus
imports Handlung "HOL-Library.Extended_Real" Maxime
begin

section\<open>Utilitarismus\<close>
text\<open>
Wir betrachten hier primär einen einfachen Handlungsutilitarismus.
Frei nach Jeremy Bentham. Sehr frei. Also sehr viel persönliche Auslegung.

Eine Handlung ist genau dann moralisch richtig,
wenn sie den aggregierten Gesamtnutzen,
d.h. die Summe des Wohlergehens aller Betroffenen, maximiert wird.\<close>

type_synonym 'world glueck_messen = \<open>'world handlung \<Rightarrow> ereal\<close>

text\<open>Wir messen Glück im Typen \<^typ>\<open>ereal\<close>, also reelle Zahlen mit \<^term>\<open>\<infinity>::ereal\<close>
und \<^term>\<open>-\<infinity>::ereal\<close>, so dass auch "den höchsten Preis zahlen" modelliert werden kann.\<close>

lemma \<open>(\<lambda>h::ereal handlung. case h of Handlung vor nach \<Rightarrow> nach - vor) (Handlung 3 5) = 2\<close>
  by simp
lemma \<open>(\<lambda>h::ereal handlung. case h of Handlung vor nach \<Rightarrow> nach - vor) (Handlung 3 \<infinity>) = \<infinity>\<close>
  by simp
lemma \<open>(\<lambda>h::ereal handlung. case h of Handlung vor nach \<Rightarrow> nach - vor) (Handlung 3 (-\<infinity>)) = -\<infinity>\<close>
  by simp

definition moralisch_richtig :: "'world glueck_messen \<Rightarrow> 'world handlung \<Rightarrow> bool" where
  "moralisch_richtig glueck_messen handlung \<equiv> (glueck_messen handlung) \<ge> 0"

subsection\<open>Kant und Utilitarismus im Einklang\<close>
text\<open>
In diese kleinen Intermezzo werden wir zeigen, wie sich die Gesinnungsethik Kants
in die Verantwortungsethik des Utilitarismus übersetzen lässt.
\<close>

definition kant_als_gesinnungsethik
  :: "('person, 'world) maxime \<Rightarrow> ('person, 'world) handlungF \<Rightarrow> bool"
where
  "kant_als_gesinnungsethik maxime handlungsabsicht \<equiv>
    \<forall>welt. teste_maxime welt handlungsabsicht maxime"

definition utilitarismus_als_verantwortungsethik
  :: "'world glueck_messen \<Rightarrow> 'world handlung \<Rightarrow> bool"
where
  "utilitarismus_als_verantwortungsethik glueck_messen handlung \<equiv>
    moralisch_richtig glueck_messen handlung"



text\<open>
Eine Maxime ist immer aus Sicht einer bestimmten Person definiert.
Wir "neutralisieren" eine Maxime indem wir diese bestimmte Person entfernen
und die Maxime so allgemeingültiger machen.
Alle Personen müssen gleich behandelt werden
Um die maxime unabhängig von einer bestimmten Person zu machen,
fordern wir einfach, dass die Maxime für aller Personen erfüllt sein muss.\<close>
(*TODO: gegen teste_maxime beweisen?
und erklaeren! Warum \<forall>
Macht eine maxime unabhängig von der person*)
fun maximeNeutralisieren :: "('person, 'world) maxime \<Rightarrow> ('world handlung \<Rightarrow> bool)" where
  "maximeNeutralisieren (Maxime m) = (\<lambda>welt. \<forall>p::'person. m p welt)"


text\<open>
Nun übersetzen wir eine maxime in die \<^typ>\<open>'world glueck_messen\<close> Funktion des Utilitarismus.
Der Trick: eine verletzte Maxime wird als unendliches Leid übersetzt.\<close>
definition maxime_als_nutzenkalkuel
  :: "('person, 'world) maxime \<Rightarrow> 'world glueck_messen"
where
  "maxime_als_nutzenkalkuel maxime \<equiv>
    (\<lambda>welt. case (maximeNeutralisieren maxime) welt
              of True \<Rightarrow> 1     
               | False \<Rightarrow> - \<infinity>)"

(*<*)
lemma ereal_zero_geq_case:
  \<open>((0::ereal) \<le> (case (\<forall>p. f p) of True \<Rightarrow> 1 | False \<Rightarrow> - \<infinity>))
      \<longleftrightarrow> (\<forall>p. f p)\<close>
  by (simp add: bool.split_sel)
(*>*)

text\<open>Für diese Übersetzung können wir beweisen,
dass die kantische Gesinnungsethik und die utilitaristische Verantwortungsethik
konsistent sind:\<close>
theorem "gesinnungsethik_verantwortungsethik_konsistent
        (kant_als_gesinnungsethik maxime)
        (utilitarismus_als_verantwortungsethik (maxime_als_nutzenkalkuel maxime))"
  apply(cases maxime, rename_tac m, simp)
  apply(simp add: gesinnungsethik_verantwortungsethik_konsistent_def
                  kant_als_gesinnungsethik_def utilitarismus_als_verantwortungsethik_def
                  moralisch_richtig_def maxime_als_nutzenkalkuel_def)
  apply(intro allI)
  apply(case_tac handlungsabsicht, rename_tac h, simp)
  apply(simp add: teste_maxime_simp)
  apply(simp add: ereal_zero_geq_case)
  by blast

text\<open>Diese Konsistenz gilt nicht im allgemeinen,
sondern nur wenn Glück gemessen wird mit Hilfe der \<^const>\<open>maxime_als_nutzenkalkuel\<close> Funktion.
Der Trick dabei ist nicht, dass wir einer verletzten Maxime \<^term>\<open>-\<infinity>::ereal\<close> Nutzen zuordnen,
sondern der Trick besteht in \<^const>\<open>maximeNeutralisieren\<close>, welche nicht erlaubt Glück
aufzuaddieren und mit Leid zu verrechnen, sondern dank des Allquantors dafür sorgt,
dass auch nur das kleinste Leid dazu führt, dass sofort \<^const>\<open>False\<close> zurückgegebn wird.

Aber wenn wir ordentlich aufsummieren, jedoch einer verletzten Maxime \<^term>\<open>-\<infinity>::ereal\<close>
Nutzen zuordnen und zusätzlich annehmen, dass die Bevölkerung endlich ist,
dann funktioniert das auch:
\<close>


fun maxime_als_summe_wohlergehen
  :: "('person, 'world) maxime \<Rightarrow> 'world glueck_messen"
where
  "maxime_als_summe_wohlergehen (Maxime m) =
    (\<lambda>welt. \<Sum>p\<in>bevoelkerung. (case m p welt
                                 of True \<Rightarrow> 1     
                                  | False \<Rightarrow> - \<infinity>))"

(*<*)

lemma "(\<Sum>p\<in>B. case f p of True \<Rightarrow> 1 | False \<Rightarrow> - \<infinity>) < (\<infinity>::ereal)"
  by (simp add: case_bool_if sum_Pinfty)


lemma helper_finite_wohlergehen_sum_cases:
  "finite B \<Longrightarrow>
(\<Sum>p\<in>B. case f p of True \<Rightarrow> 1 | False \<Rightarrow> - \<infinity>) = (- \<infinity>::ereal)
\<or>
((0::ereal) \<le> (\<Sum>p\<in>B. case f p of True \<Rightarrow> 1 | False \<Rightarrow> - \<infinity>))"
  apply(induction rule: finite.induct)
   apply(simp; fail)
  apply (simp add: case_bool_if)
  apply(simp add: sum.insert_if)
  apply(intro allI impI conjI)
  apply(elim disjE)
   apply(simp)
  apply(simp)
  done
    
thm ereal_MInfty_eq_plus ereal_less_eq(1) ereal_times(1) not_MInfty_nonneg sum_Pinfty

lemma helper_wohlergehen_sum_cases_iff:
  \<open>finite B \<Longrightarrow>
    (0::ereal) \<le> (\<Sum>p\<in>B. case f p of True \<Rightarrow> 1 | False \<Rightarrow> - \<infinity>)
        \<longleftrightarrow> (\<forall>p\<in>B. f p)\<close>

  apply(frule_tac helper_finite_wohlergehen_sum_cases[of _ f])
  apply(elim disjE)
   apply(simp)
   apply (smt (verit) not_MInfty_nonneg sum_nonneg zero_less_one_ereal)
  apply(simp)

  apply(induction rule: finite.induct)
   apply(simp; fail)
  apply (simp add: case_bool_if)
  apply(simp add: sum.insert_if)
  apply(intro allI impI conjI)
   apply (smt (verit) ereal_MInfty_eq_plus ereal_less_eq(1) ereal_times(1) not_MInfty_nonneg sum_Pinfty)
  apply(case_tac "a \<in> A")
   apply(simp)
  apply(simp)
  apply(case_tac "f a")
  apply(simp)
  apply(frule_tac helper_finite_wohlergehen_sum_cases[of _ f, simplified case_bool_if])
  apply(elim disjE)
    apply(simp)
   apply(simp)
  apply(simp)
  using not_MInfty_nonneg by fastforce
  
  

lemma \<open>finite (bevoelkerung::'person set) \<Longrightarrow>
          (0::ereal) \<le> (\<Sum>p\<in>(bevoelkerung::'person set). case f p of True \<Rightarrow> 1 | False \<Rightarrow> - \<infinity>)
        \<longleftrightarrow> (\<forall>p\<in>bevoelkerung. f p)\<close>
  apply(rule helper_wohlergehen_sum_cases_iff)
  by simp
 

(*>*)

theorem
  fixes maxime :: \<open>('person, 'world) maxime\<close>
  assumes "finite (bevoelkerung:: 'person set)"
  shows 
    "gesinnungsethik_verantwortungsethik_konsistent
      (kant_als_gesinnungsethik maxime)
      (utilitarismus_als_verantwortungsethik (maxime_als_summe_wohlergehen maxime))"
  apply(cases maxime, rename_tac m, simp)
  apply(simp add: gesinnungsethik_verantwortungsethik_konsistent_def
                  kant_als_gesinnungsethik_def utilitarismus_als_verantwortungsethik_def
                  moralisch_richtig_def)
  apply(intro allI)
  apply(case_tac handlungsabsicht, rename_tac h, simp)
  apply(simp add: teste_maxime_simp)
  apply(subst helper_wohlergehen_sum_cases_iff[OF \<open>finite bevoelkerung\<close>])
  apply(auto simp add: bevoelkerung_def)
  done


end
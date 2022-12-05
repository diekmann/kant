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


text\<open>Eine Handlung ist genau dann moralisch richtig,
wenn die Gesamtbilanz einen positiven Nutzen aufweist.\<close>
definition moralisch_richtig :: \<open>'world glueck_messen \<Rightarrow> 'world handlung \<Rightarrow> bool\<close> where
  \<open>moralisch_richtig glueck_messen handlung \<equiv> (glueck_messen handlung) \<ge> 0\<close>

subsection\<open>Goldene Regel und Utilitarismus im Einklang \label{sec:golregelutilkonsistent}\<close>
text\<open>
In \S\ref{sec:gesinnungsverantwortungsethik} haben wir
Gesinnungsethik und Verantwortungsethik definiert.

In diesem kleinen Intermezzo werden wir zeigen, wie sich die Gesinnungsethik der goldenen Regel
in die Verantwortungsethik des Utilitarismus übersetzen lässt.
\<close>


text\<open>Wir modellieren die goldene Regel als Gesinnungsethik.\<close>
definition goldene_regel_als_gesinnungsethik
  :: \<open>('person, 'world) maxime \<Rightarrow> ('person, 'world) handlungsabsicht \<Rightarrow> bool\<close>
where
  \<open>goldene_regel_als_gesinnungsethik maxime handlungsabsicht \<equiv>
    \<forall>welt. moralisch welt maxime handlungsabsicht\<close>

definition utilitarismus_als_verantwortungsethik
  :: \<open>'world glueck_messen \<Rightarrow> 'world handlung \<Rightarrow> bool\<close>
where
  \<open>utilitarismus_als_verantwortungsethik glueck_messen handlung \<equiv>
    moralisch_richtig glueck_messen handlung\<close>



text\<open>
Eine Maxime ist immer aus Sicht einer bestimmten Person definiert.
Wir "neutralisieren" eine Maxime indem wir diese bestimmte Person entfernen
und die Maxime so allgemeingültiger machen.
Alle Personen müssen gleich behandelt werden.
Um die Maxime unabhängig von einer bestimmten Person zu machen,
fordern wir einfach, dass die Maxime für aller Personen erfüllt sein muss.\<close>
(*TODO: gegen moralisch beweisen?
und erklaeren! Warum \<forall>
Macht eine maxime unabhängig von der person*)
(*TODO: upstream nach Maxime und katImp beweis!*)
fun maximeNeutralisieren :: \<open>('person, 'world) maxime \<Rightarrow> ('world handlung \<Rightarrow> bool)\<close> where
  \<open>maximeNeutralisieren (Maxime m) = (\<lambda>welt. \<forall>p::'person. m p welt)\<close>


text\<open>
Nun übersetzen wir eine Maxime in die \<^typ>\<open>'world glueck_messen\<close> Funktion des Utilitarismus.
Der Trick: eine verletzte Maxime wird als unendliches Leid übersetzt.\<close>
definition maxime_als_nutzenkalkuel
  :: \<open>('person, 'world) maxime \<Rightarrow> 'world glueck_messen\<close>
where
  \<open>maxime_als_nutzenkalkuel maxime \<equiv>
    (\<lambda>welt. case (maximeNeutralisieren maxime) welt
              of True \<Rightarrow> 1     
               | False \<Rightarrow> - \<infinity>)\<close>

(*<*)
lemma ereal_zero_geq_case:
  \<open>((0::ereal) \<le> (case (\<forall>p. f p) of True \<Rightarrow> 1 | False \<Rightarrow> - \<infinity>)) \<longleftrightarrow> (\<forall>p. f p)\<close>
  by (simp add: bool.split_sel)
(*>*)

text\<open>Für diese Übersetzung können wir beweisen,
dass die Gesinnungsethik der goldenen Regel und die utilitaristische Verantwortungsethik
konsistent sind:\<close>
theorem \<open>gesinnungsethik_verantwortungsethik_konsistent
        (goldene_regel_als_gesinnungsethik maxime)
        (utilitarismus_als_verantwortungsethik (maxime_als_nutzenkalkuel maxime))\<close>
  apply(cases \<open>maxime\<close>, rename_tac m, simp)
  apply(simp add: gesinnungsethik_verantwortungsethik_konsistent_def
                  goldene_regel_als_gesinnungsethik_def utilitarismus_als_verantwortungsethik_def
                  moralisch_richtig_def maxime_als_nutzenkalkuel_def)
  apply(intro allI)
  apply(case_tac \<open>handlungsabsicht\<close>, rename_tac h, simp)
  apply(simp add: moralisch_simp)
  apply(simp add: ereal_zero_geq_case)
  by blast

text\<open>Diese Konsistenz gilt nicht im allgemeinen,
sondern nur wenn Glück gemessen wird mit Hilfe der \<^const>\<open>maxime_als_nutzenkalkuel\<close> Funktion.
Der Trick dabei ist nicht, dass wir einer verletzten Maxime \<^term>\<open>-\<infinity>::ereal\<close> Nutzen zuordnen,
sondern der Trick besteht in \<^const>\<open>maximeNeutralisieren\<close>, welche nicht erlaubt Glück
aufzuaddieren und mit Leid zu verrechnen, sondern dank des Allquantors dafür sorgt,
dass auch nur das kleinste Leid dazu führt, dass sofort \<^const>\<open>False\<close> zurückgegebn wird.

Aber auch wenn wir ordentlich aufsummieren, jedoch einer verletzten Maxime \<^term>\<open>-\<infinity>::ereal\<close>
Nutzen zuordnen und zusätzlich annehmen, dass die Bevölkerung endlich ist,
dann funktioniert das auch:
\<close>


fun maxime_als_summe_wohlergehen
  :: \<open>('person, 'world) maxime \<Rightarrow> 'world glueck_messen\<close>
where
  \<open>maxime_als_summe_wohlergehen (Maxime m) =
    (\<lambda>welt. \<Sum>p\<in>bevoelkerung. (case m p welt
                                 of True \<Rightarrow> 1     
                                  | False \<Rightarrow> - \<infinity>))\<close>

(*<*)

lemma sum_wohlergehen_simp:
  \<open>(\<Sum>p\<in>B. case f p of True \<Rightarrow> 1 | False \<Rightarrow> - \<infinity>) = (\<Sum>p\<in>B. if f p then 1 else - \<infinity>)\<close>
  by (simp add: case_bool_if)
lemma \<open>(\<Sum>p\<in>B. if f p then 1 else - \<infinity>) < (\<infinity>::ereal)\<close>
  by (simp add: sum_Pinfty)


lemma helper_finite_wohlergehen_sum_cases:
  \<open>finite B \<Longrightarrow>
    (\<Sum>p\<in>B. if f p then 1 else - \<infinity>) = (- \<infinity>::ereal)
    \<or>
    ((0::ereal) \<le> (\<Sum>p\<in>B. if f p then 1 else - \<infinity>))\<close>
  apply(induction rule: finite.induct)
   apply(simp; fail)
  apply(simp add: sum.insert_if)
  apply(intro allI impI conjI)
  apply(elim disjE)
   apply(simp)
  apply(simp)
  done
    
lemma helper_wohlergehen_sum_IH:
  \<open>finite B \<Longrightarrow> (0::ereal) \<le> (\<Sum>p\<in>insert b B. if f p then 1 else - \<infinity>)
    \<Longrightarrow>  (0::ereal) \<le> (\<Sum>p\<in>B. if f p then 1 else - \<infinity>)\<close>
  apply(frule helper_finite_wohlergehen_sum_cases[of _ \<open>f\<close>])
  apply(elim disjE)
   apply(simp add: sum.insert_if)
   apply(case_tac \<open>b \<in> B\<close>)
    apply(simp; fail)
   apply(simp)
   apply (metis (full_types) ereal_plus_1(3) not_MInfty_nonneg plus_ereal.simps(6))
  apply (simp)
  done

lemma helper_wohlergehen_sum_minfty:
  \<open>(\<Sum>p\<in>B. if f p then 1 else - \<infinity>) = (-\<infinity>::ereal) \<Longrightarrow> \<exists>x\<in>B. \<not> f x\<close>
  by (metis (mono_tags, lifting) not_MInfty_nonneg sum_nonneg zero_less_one_ereal)

lemma helper_wohlergehen_sum_pos:
  \<open>finite B \<Longrightarrow> (0::ereal) \<le> (\<Sum>p\<in>B. if f p then 1 else - \<infinity>) \<Longrightarrow> \<forall>p\<in>B. f p\<close>
  apply(induction \<open>B\<close> rule: finite.induct)
   apply(simp; fail)
  apply(frule(1) helper_wohlergehen_sum_IH)
  apply(simp)
  apply(simp add: sum.insert_if)
  apply(case_tac \<open>a \<in> A\<close>)
   apply(simp; fail)
  apply(simp)
  apply(case_tac \<open>f a\<close>)
   apply(simp; fail)
  apply(simp)
  by (metis MInfty_neq_PInfty(2) ereal_plus_eq_MInfty ereal_times(1) not_MInfty_nonneg sum_Pinfty)

lemma helper_wohlergehen_sum_iff:
  \<open>finite B \<Longrightarrow> (0::ereal) \<le> (\<Sum>p\<in>B. if f p then 1 else - \<infinity>) \<longleftrightarrow> (\<forall>p\<in>B. f p)\<close>
  apply(frule helper_finite_wohlergehen_sum_cases[of _ \<open>f\<close>])
  apply(elim disjE)
   apply(simp add: helper_wohlergehen_sum_minfty; fail)
  apply(simp)
  using helper_wohlergehen_sum_pos by blast
  
  

lemma helper_wohlergehen_sum_cases_iff:
  \<open>finite (bevoelkerung::'person set) \<Longrightarrow>
          (0::ereal) \<le> (\<Sum>p\<in>(bevoelkerung::'person set). case f p of True \<Rightarrow> 1 | False \<Rightarrow> - \<infinity>)
        \<longleftrightarrow> (\<forall>p\<in>bevoelkerung. f p)\<close>
  using helper_wohlergehen_sum_iff sum_wohlergehen_simp by metis
 

(*>*)

theorem
  fixes maxime :: \<open>('person, 'world) maxime\<close>
  assumes \<open>finite (bevoelkerung:: 'person set)\<close>
  shows 
    \<open>gesinnungsethik_verantwortungsethik_konsistent
      (goldene_regel_als_gesinnungsethik maxime)
      (utilitarismus_als_verantwortungsethik (maxime_als_summe_wohlergehen maxime))\<close>
  apply(cases \<open>maxime\<close>, rename_tac m, simp)
  apply(simp add: gesinnungsethik_verantwortungsethik_konsistent_def
                  goldene_regel_als_gesinnungsethik_def utilitarismus_als_verantwortungsethik_def
                  moralisch_richtig_def)
  apply(intro allI)
  apply(case_tac \<open>handlungsabsicht\<close>, rename_tac h, simp)
  apply(simp add: moralisch_simp)
  apply(subst helper_wohlergehen_sum_cases_iff[OF \<open>finite bevoelkerung\<close>])
  apply(auto simp add: bevoelkerung_def)
  done


text\<open>
"Wie zu erwarten, will Kant nichts vom Utilitarismus oder sonstigen Lehren wissen,
die der Moral einen außerhalb ihrer selbst liegenden Zweck zuschreiben" \cite{russellphi}.
Die eben bewiesene Konsitenz von Gesinnungsethik und Verantwortungsethik zeigt,
das unsere Grunddefinitionen bereits eine Formalisierung des Kategorischen Imperativs
komplett im strengen Sinne Kants ausschließen.
Dennoch finde ich unsere Interpretation bis jetzt nicht abwegig.
Der große Trick besteht darin, dass wir eine \<^typ>\<open>('person, 'world) handlungsabsicht\<close>
sehr einfach in eine \<^typ>\<open>'world handlung\<close> in unserem theoretischen Modell überführen können.
Die widerspricht Kants Grundannahme, dass die Folgen einer Handlungsabsicht unvorhersehbar sind.
\<close>

end
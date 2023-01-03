theory Zahlenwelt
imports BeispielPerson ExecutableHelper Swap SchleierNichtwissen
begin

section\<open>Zahlenwelt Helper\<close>
text\<open>In diesem Abschnitt definieren wir Hilfsfunktionen für kommende "Zahlenwelt" Beispiele.\<close>

text\<open>Wir werden Beispiele betrachten, in denen wir Welten modellieren, in denen jeder Person eine
Zahl zugewiesen wird, Typ \<^typ>\<open>person \<Rightarrow> int\<close>.
Diese Zahl kann zum Beispiel der Besitz oder Wohlstand einer Person sein, oder das Einkommen.
Dabei ist zu beachten,
dass Gesamtbesitz und Einkommen (über einen kurzen Zeitraum) recht unterschiedliche Sachen
modellieren, jedoch den gleichen Typen in unserem Modell haben werden.

Hier sind einige Hilfsfunktionen um mit dem Typ \<^typ>\<open>person \<Rightarrow> int\<close> allgemein zu arbeiten.\<close>

text\<open>Default: Standardmäßig hat jede Person \<^term>\<open>0::int\<close>:\<close>
definition DEFAULT :: \<open>person \<Rightarrow> int\<close> where
  \<open>DEFAULT \<equiv> \<lambda>p. 0\<close>

(*<*)
syntax
  "_ZahlenWelt" :: \<open>updbinds \<Rightarrow> 'a\<close> ("(1\<^url>[_])")

translations
  "_ZahlenWelt ms" \<rightleftharpoons> "_Update (CONST DEFAULT) ms"
(*>*)

beispiel \<open>(DEFAULT(Alice:=8, Bob:=3, Eve:= 5)) Bob = 3\<close> by eval

text\<open>Beispiel mit fancy Syntax:\<close>
beispiel \<open>\<^url>[Alice:=8, Bob:=3, Eve:= 5] Bob = 3\<close> by eval

text\<open>Das Beispiel liest sich wie folgt.
Die Welt \<^term_type>\<open>\<^url>[Alice:=8, Bob:=3, Eve:= 5] :: person \<Rightarrow> int\<close> ist eine Funktion von
\<^typ>\<open>person\<close> nach \<^typ>\<open>int\<close>.
Wir rufen diese Funktion mit den Parameter \<^const>\<open>Bob\<close> auf.
Das Ergebnis ist \<^term>\<open>3::int\<close>.\<close>

text\<open>Die Funktion \<^term>\<open>\<^url>[Alice := 4, Carol := 4]\<close> lässt sich auch mit Hilfe folgender
Hilfsfunktionen als eine Menge von Tupeln darstellen.\<close>
beispiel \<open>show_fun \<^url>[Alice := 4, Carol := 4] = [(Alice, 4), (Bob, 0), (Carol, 4), (Eve, 0)]\<close> by eval
beispiel \<open>show_num_fun \<^url>[Alice := 4, Carol := 4] = [(Alice, 4), (Carol, 4)]\<close> by eval

text\<open>Folgende Syntaxabkürzungen erlauben es uns eine einfachere Notation einzuführen,
um den Besitz einer Person zu erhöhen oder zu verringern.\<close>
(* this can produce ambiguous parse trees. So I added those \<lbrakk>\<rbrakk> *)
abbreviation num_fun_add_syntax ("\<lbrakk>_ '(_ += _')\<rbrakk>") where
  \<open>\<lbrakk>f(p += n)\<rbrakk> \<equiv> (f(p := (f p) + n))\<close>

abbreviation num_fun_minus_syntax ("\<lbrakk>_ '(_ -= _')\<rbrakk>") where
  \<open>\<lbrakk>f(p -= n)\<rbrakk> \<equiv> (f(p := (f p) - n))\<close>

beispiel \<open>\<lbrakk>\<^url>[Alice:=8, Bob:=3, Eve:= 5](Bob += 4)\<rbrakk> Bob = 7\<close> by eval
beispiel \<open>\<lbrakk>\<^url>[Alice:=8, Bob:=3, Eve:= 5](Bob -= 4)\<rbrakk> Bob = -1\<close> by eval

text\<open>Erhöhen und verringern heben sich auf.\<close>
beispiel fixes n:: \<open>int\<close> shows \<open>\<lbrakk>\<lbrakk>f(p += n)\<rbrakk>(p -= n)\<rbrakk> = f\<close> by(simp)


text\<open>Folgende Funktion wählt diskriminierungsfrei
eine \<^typ>\<open>'person\<close> eindeutig anhand Ihres Besitzes aus.\<close>
definition opfer_eindeutig_nach_besitz_auswaehlen
  :: \<open>int \<Rightarrow> ('person \<Rightarrow> int) \<Rightarrow> 'person list \<Rightarrow> 'person option\<close> where
  \<open>opfer_eindeutig_nach_besitz_auswaehlen b besitz ps = 
     (case filter (\<lambda>p. besitz p = b) ps
        of [opfer] \<Rightarrow> Some opfer
         | _ \<Rightarrow> None)\<close>

(*<*)
lemma case_filter_empty_some_helper:
  \<open>(case filter P ps of [] \<Rightarrow> Some a | aa # x \<Rightarrow> Map.empty x) = Some x
  \<longleftrightarrow> (\<forall>x\<in>set ps. \<not> P x) \<and> a = x\<close>
  apply(simp add: list.case_eq_if)
  using empty_filter_conv by metis

lemma case_filter_empty_some_helper2:
  \<open>(case if P a then a # filter P ps else filter P ps of
        [] \<Rightarrow> None | [opfer] \<Rightarrow> Some opfer | opfer # aa # x \<Rightarrow> Map.empty x) =
       Some x \<longleftrightarrow>
  (P a \<and> x = a \<and> filter P ps = []) \<or> (\<not>P a \<and> filter P ps = [x])\<close>
  apply(cases \<open>P a\<close>)
   apply(simp add: case_filter_empty_some_helper)
   apply(metis empty_filter_conv)
  apply(simp)
  apply(cases \<open>filter P ps\<close>)
   apply(simp)
  by(simp split: list.split)

lemma case_filter_empty_some_helper3:
  \<open>(case filter P ps of [] \<Rightarrow> None | [opfer] \<Rightarrow> Some opfer
            | opfer # aa # x \<Rightarrow> Map.empty x) =
           Some opfer
    \<longleftrightarrow>
    filter P ps = [opfer]\<close>
  by(simp split: list.split)

lemma opfer_eindeutig_nach_besitz_auswaehlen_injective:
  \<open>opfer_eindeutig_nach_besitz_auswaehlen opfer_nach_besitz besitz ps = Some opfer
  \<Longrightarrow> inj_on besitz {p \<in> set ps. besitz p = opfer_nach_besitz}\<close>
  apply(simp add: inj_on_def)
  apply(safe)
  apply(induction \<open>ps\<close>)
   apply(simp)
  apply(simp)
  apply(simp add: opfer_eindeutig_nach_besitz_auswaehlen_def)
  apply(safe)
    apply(simp_all)
    apply(simp add: case_filter_empty_some_helper; fail)
   apply(simp add: case_filter_empty_some_helper)
   apply fastforce
  apply(simp add: case_filter_empty_some_helper3)
  apply(simp add: case_filter_empty_some_helper2[of \<open>(\<lambda>p. besitz p = besitz _)\<close>])
  by (metis (mono_tags) empty_filter_conv)
(*>*)

text\<open>Folgende Hilfsdefinition definiert eindeutig das Element in einer Einelementigen Menge,
wenn dieses existiert.\<close>
definition the_single_elem :: \<open>'a set \<Rightarrow> 'a option\<close> where
  \<open>the_single_elem s \<equiv> if card s = 1 then Some (Set.the_elem s) else None\<close>

beispiel \<open>the_single_elem {a} = Some a\<close> by(simp add: the_single_elem_def)
beispiel \<open>the_single_elem {1::nat,2} = None\<close> by(simp add: the_single_elem_def)
beispiel \<open>the_single_elem {} = None\<close> by(simp add: the_single_elem_def)

text\<open>Hier sehen wir unser Shallow Embedding:
Unsere Definition \<^const>\<open>the_single_elem\<close> lässt sich komplett auf bereits existierende Konzepte
in HOL reduzieren.\<close>
lemma the_single_elem:
  \<open>the_single_elem s = (if is_singleton s then Some (Set.the_elem s) else None)\<close>
  apply(simp add: is_singleton_the_elem the_single_elem_def card_1_singleton_iff)
  by auto

(*<*)
lemma \<open>the_single_elem {a} = Some a\<close>
  by(simp add: the_single_elem_def)
lemma \<open>a \<noteq> b \<Longrightarrow> the_single_elem {a,b} = None\<close>
  by(simp add: the_single_elem_def)


lemma the_single_elem_exhaust:
  \<open>(the_single_elem S = None \<Longrightarrow> P None) \<Longrightarrow>
        (\<And>x. the_single_elem S = Some x \<Longrightarrow> P (Some x)) \<Longrightarrow> P (the_single_elem S)\<close>
apply(cases \<open>the_single_elem S\<close>)
by(auto)
(*>*)


lemma opfer_nach_besitz_induct_step_set_simp: \<open>besitz a \<noteq> opfer_nach_besitz \<Longrightarrow>
  {p. (p = a \<or> p \<in> set ps) \<and> besitz p = opfer_nach_besitz} =
    {p \<in> set ps. besitz p = opfer_nach_besitz}\<close>
  by auto

lemma opfer_eindeutig_nach_besitz_auswaehlen_the_single_elem:
  \<open>distinct ps \<Longrightarrow> 
  opfer_eindeutig_nach_besitz_auswaehlen opfer_nach_besitz besitz ps =
          the_single_elem {p \<in> set ps. besitz p = opfer_nach_besitz}\<close>
proof(simp add: the_single_elem, intro conjI impI)
  show \<open>distinct ps \<Longrightarrow>
    is_singleton {p \<in> set ps. besitz p = opfer_nach_besitz} \<Longrightarrow>
    opfer_eindeutig_nach_besitz_auswaehlen opfer_nach_besitz besitz ps =
    Some (the_elem {p \<in> set ps. besitz p = opfer_nach_besitz})\<close>
    apply(induction \<open>ps\<close>)
     apply (simp add: is_singleton_altdef; fail)
    apply(simp)
    apply(simp add: opfer_eindeutig_nach_besitz_auswaehlen_def)
    apply(simp add: is_singleton_the_elem)
    apply(simp add: case_filter_empty_some_helper case_filter_empty_some_helper3)
    apply(safe)
      apply (metis (mono_tags, lifting) mem_Collect_eq singleton_iff)
     apply (metis (mono_tags, lifting) mem_Collect_eq singleton_iff)
    apply(simp add: opfer_nach_besitz_induct_step_set_simp; fail)
    done
next
  show \<open>distinct ps \<Longrightarrow>
    \<not> is_singleton {p \<in> set ps. besitz p = opfer_nach_besitz} \<Longrightarrow>
    opfer_eindeutig_nach_besitz_auswaehlen opfer_nach_besitz besitz ps = None\<close>
    apply(induction \<open>ps\<close>)
     apply(simp add: opfer_eindeutig_nach_besitz_auswaehlen_def; fail)
    apply(simp add: opfer_eindeutig_nach_besitz_auswaehlen_def)
    apply(safe)
     apply(simp split: list.split)
     apply(simp add: filter_empty_conv is_singleton_def)
     apply blast
    by(simp add: opfer_nach_besitz_induct_step_set_simp)
qed

lemma opfer_eindeutig_nach_besitz_auswaehlen_the_single_elem_enumall:
  \<open>opfer_eindeutig_nach_besitz_auswaehlen opfer_nach_besitz besitz enum_class.enum =
          the_single_elem {p. besitz p = opfer_nach_besitz}\<close>
  apply(subst opfer_eindeutig_nach_besitz_auswaehlen_the_single_elem)
  using enum_class.enum_distinct apply(simp)
  apply(simp add: enum_class.enum_UNIV)
  done


(*<*)
lemma \<open>p1 \<in> Ps \<Longrightarrow> p2 \<in> Ps \<Longrightarrow>
  {pa \<in> Ps. swap p1 p2 besitz pa = b} = {p2} \<longleftrightarrow> {pa \<in> Ps. besitz pa = b} = {p1}\<close>
  apply(simp add: singleton_set_to_all)
  by (metis swap_b swap_nothing swap_symmetric)

lemma the_elem_singleton_swap:
  \<open>p1 \<in> Ps \<Longrightarrow>
    p2 \<in> Ps \<Longrightarrow>
    the_elem {pa \<in> Ps. swap p1 p2 besitz pa = b} = p2 \<Longrightarrow>
    is_singleton {pa \<in> Ps. swap p1 p2 besitz pa = b} \<Longrightarrow>
    is_singleton {pa \<in> Ps. besitz pa = b} \<Longrightarrow> the_elem {pa \<in> Ps. besitz pa = b} = p1\<close>
  apply(simp add: is_singleton_the_elem_as_set)
  apply(elim is_singletonE)
  apply(simp add: singleton_set_to_all)
  by (metis swap_b)

lemma the_elem_singleton_swap_none:
    \<open>p1 \<in> set ps \<Longrightarrow>
    p2 \<in> set ps \<Longrightarrow>
    the_elem {pa \<in> set ps. swap p1 p2 besitz pa = p} \<noteq> p2 \<Longrightarrow>
    the_elem {pa \<in> set ps. swap p1 p2 besitz pa = p} \<noteq> p1 \<Longrightarrow>
    is_singleton {pa \<in> set ps. besitz pa = p} \<Longrightarrow>
    is_singleton {pa \<in> set ps. swap p1 p2 besitz pa = p} \<Longrightarrow>
    the_elem {pa \<in> set ps. swap p1 p2 besitz pa = p} = the_elem {pa \<in> set ps. besitz pa = p}\<close>
  apply(rule arg_cong[of _ _ \<open>the_elem\<close>])
  apply(rule Collect_cong)
  apply(elim is_singletonE)
  apply(simp add: is_singleton_the_elem_as_set)
  apply(simp add: singleton_set_to_all)
  by (metis swap_nothing)
  

lemma set_swap_image_pullout:
  \<open>p1 \<in> A \<Longrightarrow>
   p2 \<in> A \<Longrightarrow>
    {a \<in> A. swap p1 p2 besitz a = b} = swap p1 p2 id ` {a \<in> A. besitz a = b}\<close>
  apply(simp add: image_def)
  apply(rule Collect_cong)
  apply(safe)
    apply(rule swap_cases)
      apply(rule_tac x=\<open>p2\<close> in exI, simp add: swap_a swap_b; fail)
     apply(rule_tac x=\<open>p1\<close> in exI, simp add: swap_a swap_b; fail)
    apply(rule_tac x=\<open>a\<close> in exI, simp add: swap_a swap_b swap_nothing; fail)
   apply(rule swap_cases, simp_all add: swap_a swap_b swap_nothing)
  by (simp add: swap_fun_swap_id)

lemma is_singleton_swap:
  \<open>p1 \<in> set ps \<Longrightarrow>
   p2 \<in> set ps \<Longrightarrow>
    is_singleton {pa \<in> set ps. swap p1 p2 besitz pa = p}
    \<longleftrightarrow> is_singleton {pa \<in> set ps. besitz pa = p}\<close>
  apply(simp add: set_swap_image_pullout)
  apply(rule is_singleton_bij_image)
  by (simp add: involuntory_imp_bij swap_fun_swap_id)
 

lemma if_swap_person_help_same: \<open>p1 = a \<Longrightarrow>
       p2 = a \<Longrightarrow>
       (\<lambda>p. if p = a then p2 else if p = p2 then p1 else p) = id\<close>
  by auto


(*TODO: das if will in ne definition*)
lemma opfer_eindeutig_nach_besitz_auswaehlen_swap:
    \<open>p1 \<in> set ps \<Longrightarrow>
     p2 \<in> set ps \<Longrightarrow>
     distinct ps \<Longrightarrow>
  map_option
        (\<lambda>p. if p = p1 then p2 else if p = p2 then p1 else p)
        (opfer_eindeutig_nach_besitz_auswaehlen p (swap p1 p2 besitz) ps)
  = opfer_eindeutig_nach_besitz_auswaehlen p besitz ps\<close>
  apply(simp add: opfer_eindeutig_nach_besitz_auswaehlen_the_single_elem)
  apply(simp add: the_single_elem)
  apply(safe, simp_all add: swap_a swap_b swap_nothing is_singleton_swap)
    apply(rule sym)
    apply(rule the_elem_singleton_swap, simp_all)
    apply(simp add: is_singleton_swap; fail)
   apply(rule sym)
   apply(rule the_elem_singleton_swap, simp_all)
    apply(simp add: swap_symmetric; fail)
   apply(simp add: is_singleton_swap; fail)
  apply(rule the_elem_singleton_swap_none, simp_all)
  using is_singleton_swap by fast

lemma opfer_eindeutig_nach_besitz_auswaehlen_swap_alt:
  \<open>p1 \<in> set ps \<Longrightarrow>
   p2 \<in> set ps \<Longrightarrow>
   distinct ps \<Longrightarrow>
   opfer_eindeutig_nach_besitz_auswaehlen p (swap p1 p2 besitz) ps =
     map_option (\<lambda>p. if p = p1 then p2 else if p = p2 then p1 else p)
       (opfer_eindeutig_nach_besitz_auswaehlen p besitz ps)\<close>
  using opfer_eindeutig_nach_besitz_auswaehlen_swap[of \<open>p1\<close> \<open>ps\<close> \<open>p2\<close> \<open>p\<close> \<open>(swap p1 p2 besitz)\<close>, simplified swap1]
  by simp

lemma opfer_eindeutig_nach_besitz_auswaehlen_swap_enumall:
\<open>opfer_eindeutig_nach_besitz_auswaehlen p (swap p1 p2 besitz) enum_class.enum =
  map_option (\<lambda>p. if p = p1 then p2 else if p = p2 then p1 else p)
    (opfer_eindeutig_nach_besitz_auswaehlen p besitz enum_class.enum)\<close>
  apply(rule opfer_eindeutig_nach_besitz_auswaehlen_swap_alt)
  using enum_class.in_enum enum_class.enum_distinct by auto

lemma opfer_eindeutig_nach_besitz_auswaehlen_swap_None:
  "opfer_eindeutig_nach_besitz_auswaehlen p (swap p1 p2 welt) enum_class.enum = None
    \<longleftrightarrow>
   opfer_eindeutig_nach_besitz_auswaehlen p welt enum_class.enum = None"
  by(simp add: opfer_eindeutig_nach_besitz_auswaehlen_swap_enumall)

lemma the_single_elem_None_swap:
  \<open>the_single_elem {p. x p = a} = None \<Longrightarrow>
       the_single_elem {p. swap p1 p2 x p = a} = None\<close>
  apply(simp add: the_single_elem split: if_split_asm)
  apply(simp add: is_singleton_def)
  apply(safe)
  apply(simp add: singleton_set_to_all2)
  by (metis swap_a swap_b swap_nothing)

lemma the_single_elem_Some_Some_swap:
  \<open>the_single_elem {p. x p = a} = Some s1 \<Longrightarrow>
      the_single_elem {p. swap s1 p2 x p = a} = Some s2 \<Longrightarrow> p2 = s2\<close>
  apply(simp add: the_single_elem is_singleton_the_elem split: if_split_asm)
  by (metis empty_iff insert_iff mem_Collect_eq swap_a swap_nothing)
lemma the_single_elem_Some_ex_swap:
  \<open>the_single_elem {p. x p = a} = Some x2 \<Longrightarrow> \<exists>y. the_single_elem {p. swap p1 p2 x p = a} = Some y\<close>
  apply(case_tac \<open>the_single_elem {p. swap p1 p2 x p = a}\<close>)
   apply(simp)
  using the_single_elem_None_swap apply (metis option.distinct(1) swap2)
  by simp

lemma the_single_elem_Some_swap:
  \<open>the_single_elem {p. x p = a} = Some s \<Longrightarrow>
      the_single_elem {p. swap s p2 x p = a} = Some p2\<close>
  using the_single_elem_Some_ex_swap the_single_elem_Some_Some_swap by fastforce
(*>*)

fun stehlen :: \<open>int \<Rightarrow> int \<Rightarrow> 'person::enum \<Rightarrow> ('person \<Rightarrow> int) \<Rightarrow> ('person \<Rightarrow> int) option\<close> where
  \<open>stehlen beute opfer_nach_besitz dieb besitz =
    (case opfer_eindeutig_nach_besitz_auswaehlen opfer_nach_besitz besitz Enum.enum
       of None \<Rightarrow> None
        | Some opfer \<Rightarrow> if opfer = dieb then None else Some \<lbrakk>\<lbrakk>besitz(opfer -= beute)\<rbrakk>(dieb += beute)\<rbrakk>
    )\<close>

lemma wohlgeformte_handlungsabsicht_stehlen:
  \<open>wohlgeformte_handlungsabsicht swap welt (Handlungsabsicht (stehlen n p))\<close>
    apply(simp add: wohlgeformte_handlungsabsicht.simps)
    apply(simp add: opfer_eindeutig_nach_besitz_auswaehlen_swap_enumall)
    apply(simp add: opfer_eindeutig_nach_besitz_auswaehlen_the_single_elem_enumall)
    apply(simp add: the_single_elem)
    apply(safe)
     apply (simp add: swap_def Fun.swap_def; fail)
  by (simp add: fun_upd_twist swap_def Fun.swap_def)




definition aufsummieren :: \<open>('person::enum \<Rightarrow> int) \<Rightarrow> int\<close> where
  \<open>aufsummieren besitz = sum_list (map besitz Enum.enum)\<close>

lemma \<open>aufsummieren (besitz :: person\<Rightarrow>int) = (\<Sum>p\<leftarrow>[Alice,Bob,Carol,Eve]. besitz p)\<close>
  by(simp add: aufsummieren_def enum_person_def)

lemma \<open>aufsummieren \<^url>[Alice := 4, Carol := 8] = 12\<close> by eval
lemma \<open>aufsummieren \<^url>[Alice := 4, Carol := 4] = 8\<close> by eval

lemma aufsummieren_swap:
  \<open>aufsummieren (swap p1 p2 welt) = aufsummieren welt\<close>
  apply(simp add: aufsummieren_def)
  apply(rule sum_list_swap)
  using enum_class.in_enum enum_class.enum_distinct by auto







lemma list_not_empty_iff_has_element: \<open>as \<noteq> [] \<longleftrightarrow> (\<exists>a. a \<in> set as)\<close>
  by (simp add: ex_in_conv)

lemma enum_class_not_empty_list: \<open>enum_class.enum \<noteq> []\<close>
  using enum_class.in_enum list_not_empty_iff_has_element by blast

lemma alles_kaputt_machen_code_help:
  \<open>(\<lambda>_. Min (range x) - 1) = (\<lambda>_. min_list (map x enum_class.enum) - 1)\<close>
  apply(subst min_list_Min)
   apply(simp add: enum_class_not_empty_list; fail)
  apply(simp)
  apply(simp add: enum_UNIV)
  done




text\<open>\<^const>\<open>swap\<close> funktioniert auch auf Mengen.\<close>
lemma \<open>(swap Alice Carol id) ` {Alice, Bob} = {Carol, Bob}\<close> by eval


end
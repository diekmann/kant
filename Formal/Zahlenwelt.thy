theory Zahlenwelt
imports BeispielPerson ExecutableHelper Swap SchleierNichtwissen
begin

section\<open>Zahlenwelt Helper\<close>
text\<open>Wir werden Beispiele betrachten, in denen wir Welten modellieren, in denen jeder Person eine
Zahl zugewiesen wird: \<^typ>\<open>person \<Rightarrow> int\<close>.
Diese Zahl kann zum Beispiel der Besitz oder Wohlstand einer Person sein, oder das Einkommen.
Wobei Gesamtbesitz und Einkommen über einen kurzen Zeitraum recht unterschiedliche Sachen
modellieren.

Hier sind einige Hilfsfunktionen um mit \<^typ>\<open>person \<Rightarrow> int\<close> allgemein zu arbeiten.\<close>

text\<open>Default: Standardmäßig hat jede Person \<^term>\<open>0::int\<close>:\<close>
definition DEFAULT :: \<open>person \<Rightarrow> int\<close> where
  \<open>DEFAULT \<equiv> \<lambda>p. 0\<close>

(*<*)
syntax
  "_ZahlenWelt"  :: \<open>updbinds \<Rightarrow> 'a\<close> ("(1\<^url>[_])")

translations
  "_ZahlenWelt ms"                     \<rightleftharpoons> "_Update (CONST DEFAULT) ms"

(*>*)


text\<open>Beispiel:\<close>
lemma \<open>(DEFAULT(Alice:=8, Bob:=3, Eve:= 5)) Bob = 3\<close> by eval

text\<open>Beispiel mit fancy Syntax:\<close>
lemma \<open>\<^url>[Alice:=8, Bob:=3, Eve:= 5] Bob = 3\<close> by eval

lemma \<open>show_fun \<^url>[Alice := 4, Carol := 4] = [(Alice, 4), (Bob, 0), (Carol, 4), (Eve, 0)]\<close> by eval
lemma \<open>show_num_fun \<^url>[Alice := 4, Carol := 4] = [(Alice, 4), (Carol, 4)]\<close> by eval


(*from joint_probability
abbreviation joint_probability ("\<P>'(_ ; _') _") where
"\<P>(X ; Y) x \<equiv> \<P>(\<lambda>x. (X x, Y x)) x
*)

(*TODO: this can produce ambiguous parse trees.
So I added those \<lbrakk>\<rbrakk>
*)
abbreviation num_fun_add_syntax ("\<lbrakk>_ '(_ += _')\<rbrakk>") where
  \<open>\<lbrakk>f(p += n)\<rbrakk> \<equiv> (f(p := (f p) + n))\<close>

abbreviation num_fun_minus_syntax ("\<lbrakk>_ '(_ -= _')\<rbrakk>") where
  \<open>\<lbrakk>f(p -= n)\<rbrakk> \<equiv> (f(p := (f p) - n))\<close>

lemma \<open>\<lbrakk>\<^url>[Alice:=8, Bob:=3, Eve:= 5](Bob += 4)\<rbrakk> Bob = 7\<close> by eval
lemma \<open>\<lbrakk>\<^url>[Alice:=8, Bob:=3, Eve:= 5](Bob -= 4)\<rbrakk> Bob = -1\<close> by eval


lemma fixes n:: \<open>int\<close> shows \<open>\<lbrakk>\<lbrakk>f(p += n)\<rbrakk>(p -= n)\<rbrakk> = f\<close> by(simp)


text\<open>Diskriminierungsfrei eine \<^typ>\<open>'person\<close> eindeutig anhand Ihres Besitzes auswählen:\<close>
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
  apply(simp)
  by (metis list.case_eq_if option.distinct(1) option.inject)

lemma case_filter_empty_some_helper3:
  \<open>(case filter P ps of [] \<Rightarrow> None | [opfer] \<Rightarrow> Some opfer
            | opfer # aa # x \<Rightarrow> Map.empty x) =
           Some opfer
    \<longleftrightarrow>
    filter P ps = [opfer]\<close>
  apply(simp add: list.case_eq_if)
  by (metis list.exhaust_sel list.sel(1) list.sel(3))

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

definition the_single_elem :: \<open>'a set \<Rightarrow> 'a option\<close> where
  \<open>the_single_elem s \<equiv> if card s = 1 then Some (Set.the_elem s) else None\<close>

(*<*)
lemma the_single_elem:
  \<open>the_single_elem s = (if is_singleton s then Some (Set.the_elem s) else None)\<close>
  apply(simp add: is_singleton_the_elem the_single_elem_def card_1_singleton_iff)
  by auto

lemma \<open>the_single_elem {a} = Some a\<close>
  by(simp add: the_single_elem_def)
lemma \<open>a \<noteq> b \<Longrightarrow> the_single_elem {a,b} = None\<close>
  by(simp add: the_single_elem_def)


thm  option.exhaust_sel
lemma the_single_elem_exhaust:
  \<open>(the_single_elem S = None \<Longrightarrow> P None) \<Longrightarrow>
        (\<And>x. the_single_elem S = Some x \<Longrightarrow> P (Some x)) \<Longrightarrow> P (the_single_elem S)\<close>
apply(cases \<open>the_single_elem S\<close>)
by(auto)
(*>*)

(*TODO: delete in favor of*)
thm is_singleton_the_elem[symmetric]
lemma \<open>A = {the_elem A} \<longleftrightarrow> is_singleton A\<close>
  by (simp add: is_singleton_the_elem)

lemma opfer_nach_besitz_induct_step_set_simp: \<open>besitz a \<noteq> opfer_nach_besitz \<Longrightarrow>
  {p. (p = a \<or> p \<in> set ps) \<and> besitz p = opfer_nach_besitz} =
    {p \<in> set ps. besitz p = opfer_nach_besitz}\<close>
  by auto

lemma opfer_eindeutig_nach_besitz_auswaehlen_the_single_elem:
  \<open>distinct ps \<Longrightarrow> 
  opfer_eindeutig_nach_besitz_auswaehlen opfer_nach_besitz besitz ps =
          the_single_elem {p \<in> set ps. besitz p = opfer_nach_besitz}\<close>
  apply(simp add: the_single_elem)
  apply(safe)
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

  apply(induction \<open>ps\<close>)
   apply(simp add: opfer_eindeutig_nach_besitz_auswaehlen_def; fail)
  apply(simp add: opfer_eindeutig_nach_besitz_auswaehlen_def)
  apply(safe)
   apply(case_tac \<open>\<not> is_singleton {p \<in> set ps. besitz p = besitz a}\<close>)
    apply (smt (z3) empty_iff empty_set is_singletonI' list.case_eq_if mem_Collect_eq set_filter)
   apply(simp)
   apply (metis One_nat_def card.empty empty_set is_singleton_altdef list.case_eq_if nat.simps(3) set_filter)
  by(simp add: opfer_nach_besitz_induct_step_set_simp)


lemma opfer_eindeutig_nach_besitz_auswaehlen_the_single_elem_enumall:
  \<open>opfer_eindeutig_nach_besitz_auswaehlen opfer_nach_besitz besitz enum_class.enum =
          the_single_elem {p. besitz p = opfer_nach_besitz}\<close>
  apply(subst opfer_eindeutig_nach_besitz_auswaehlen_the_single_elem)
  using enum_class.enum_distinct apply(simp)
  apply(simp add: enum_class.enum_UNIV)
  done


(*<*)
lemma the_elem_singleton_swap:
  \<open>p1 \<in> set ps \<Longrightarrow>
    p2 \<in> set ps \<Longrightarrow>
    the_elem {pa \<in> set ps. swap p1 p2 besitz pa = p} = p2 \<Longrightarrow>
    is_singleton {pa \<in> set ps. swap p1 p2 besitz pa = p} \<Longrightarrow>
    is_singleton {pa \<in> set ps. besitz pa = p} \<Longrightarrow> the_elem {pa \<in> set ps. besitz pa = p} = p1\<close>
  by (smt (verit, del_insts) is_singleton_the_elem mem_Collect_eq singleton_iff swap_b)

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
  apply(simp add: is_singleton_the_elem)
  by (smt (verit) mem_Collect_eq singleton_iff swap_nothing)

lemma is_singleton_swap:
  \<open>p1 \<in> set ps \<Longrightarrow>
   p2 \<in> set ps \<Longrightarrow>
    is_singleton {pa \<in> set ps. swap p1 p2 besitz pa = p}
    \<longleftrightarrow> is_singleton {pa \<in> set ps. besitz pa = p}\<close>
  apply(cases \<open>p2 \<noteq> p1\<close>) (*smt lol*)
  subgoal by (smt (verit) CollectD CollectI insertCI is_singletonI' is_singleton_the_elem singleton_iff swap_a swap_b swap_nothing)
  apply(simp)
  done


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




lemma the_single_elem_None_swap:
  \<open>the_single_elem {p. x p = a} = None \<Longrightarrow>
       the_single_elem {p. swap p1 p2 x p = a} = None\<close>
  apply(simp add: the_single_elem)
  by (smt (verit) empty_iff is_singletonI' is_singleton_the_elem mem_Collect_eq option.simps(3) singleton_iff swap_a swap_b swap_nothing)

  lemma the_single_elem_Some_Some_swap:
    \<open>the_single_elem {p. x p = a} = Some s1 \<Longrightarrow>
        the_single_elem {p. swap s1 p2 x p = a} = Some s2 \<Longrightarrow> p2 = s2\<close>
    by (metis (no_types, lifting) is_singleton_the_elem mem_Collect_eq option.inject option.simps(3) singleton_iff swap_b the_single_elem)
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
     apply (simp add: swap_def; fail)
  by (simp add: fun_upd_twist swap_def)




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







lemma list_not_empty_iff_has_element: "as \<noteq> [] \<longleftrightarrow> (\<exists>a. a \<in> set as)"
  by (simp add: ex_in_conv)

lemma enum_class_not_empty_list: "enum_class.enum \<noteq> []"
  using enum_class.in_enum list_not_empty_iff_has_element by blast

lemma alles_kaputt_machen_code_help:
  "(\<lambda>_. Min (range x) - 1) = (\<lambda>_. min_list (map x enum_class.enum) - 1)"
  apply(subst min_list_Min)
   apply(simp add: enum_class_not_empty_list; fail)
  apply(simp)
  apply(simp add: enum_UNIV)
  done




text\<open>\<^const>\<open>swap\<close> funktioniert auch auf Mengen.\<close>
lemma "(swap Alice Carol id) ` {Alice, Bob} = {Carol, Bob}" by eval


end
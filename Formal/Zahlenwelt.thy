theory Zahlenwelt
imports BeispielPerson ExecutableHelper Swap
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

abbreviation num_fun_add_syntax ("_ '(_ += _')") where
  \<open>f(p += n) \<equiv> (f(p := (f p) + n))\<close>

abbreviation num_fun_minus_syntax ("_ '(_ -= _')") where
  \<open>f(p -= n) \<equiv> (f(p := (f p) - n))\<close>

lemma \<open>(\<^url>[Alice:=8, Bob:=3, Eve:= 5])(Bob += 4) Bob = 7\<close> by eval
lemma \<open>(\<^url>[Alice:=8, Bob:=3, Eve:= 5])(Bob -= 4) Bob = -1\<close> by eval


lemma fixes n:: \<open>int\<close> shows \<open>f(p += n)(p -= n) = f\<close> by(simp)


text\<open>Diskriminierungsfrei eine \<^typ>\<open>'person\<close> eindeutig anhand Ihres Besitzes auswählen:\<close>
definition opfer_eindeutig_nach_besitz_auswaehlen
  :: \<open>int \<Rightarrow> ('person \<Rightarrow> int) \<Rightarrow> 'person list \<Rightarrow> 'person option\<close> where
  \<open>opfer_eindeutig_nach_besitz_auswaehlen b besitz ps = 
     (case filter (\<lambda>p. besitz p = b) ps
        of [opfer] \<Rightarrow> Some opfer
         | _ \<Rightarrow> None)\<close>

(*<*)
lemma case_filter_empty_some_helper:
  "(case filter P ps of [] \<Rightarrow> Some a | aa # x \<Rightarrow> Map.empty x) = Some x
  \<longleftrightarrow> (\<forall>x\<in>set ps. \<not> P x) \<and> a = x"
  apply(simp add: list.case_eq_if)
  using empty_filter_conv by metis

lemma case_filter_empty_some_helper2:
  "(case if P a then a # filter P ps else filter P ps of
        [] \<Rightarrow> None | [opfer] \<Rightarrow> Some opfer | opfer # aa # x \<Rightarrow> Map.empty x) =
       Some x \<longleftrightarrow>
  (P a \<and> x = a \<and> filter P ps = []) \<or> (\<not>P a \<and> filter P ps = [x])"
  apply(cases "P a")
   apply(simp add: case_filter_empty_some_helper)
   apply(metis empty_filter_conv)
  apply(simp)
  apply(cases "filter P ps")
   apply(simp)
  apply(simp)
  by (metis list.case_eq_if option.distinct(1) option.inject)

lemma case_filter_empty_some_helper3:
  "(case filter P ps of [] \<Rightarrow> None | [opfer] \<Rightarrow> Some opfer
            | opfer # aa # x \<Rightarrow> Map.empty x) =
           Some opfer
    \<longleftrightarrow>
    filter P ps = [opfer]"
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
  apply(simp add: case_filter_empty_some_helper2[of "(\<lambda>p. besitz p = besitz _)"])
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
  "(the_single_elem S = None \<Longrightarrow> P None) \<Longrightarrow>
        (\<And>x. the_single_elem S = Some x \<Longrightarrow> P (Some x)) \<Longrightarrow> P (the_single_elem S)"
apply(cases "the_single_elem S")
by(auto)
(*>*)

(*TODO: delete in favor of*)
thm is_singleton_the_elem[symmetric]
lemma "A = {the_elem A} \<longleftrightarrow> is_singleton A"
  by (simp add: is_singleton_the_elem)

lemma opfer_nach_besitz_induct_step_set_simp: "besitz a \<noteq> opfer_nach_besitz \<Longrightarrow>
  {p. (p = a \<or> p \<in> set ps) \<and> besitz p = opfer_nach_besitz} =
    {p \<in> set ps. besitz p = opfer_nach_besitz}"
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
   apply(case_tac "\<not> is_singleton {p \<in> set ps. besitz p = besitz a}")
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

lemma "( B) = ( C) \<Longrightarrow> (A \<and> B) = (A \<and> C)" oops
lemma the_elem_singleton_swap_none:
    \<open>p1 \<in> set ps \<Longrightarrow>
    p2 \<in> set ps \<Longrightarrow>
    the_elem {pa \<in> set ps. swap p1 p2 besitz pa = p} \<noteq> p2 \<Longrightarrow>
    the_elem {pa \<in> set ps. swap p1 p2 besitz pa = p} \<noteq> p1 \<Longrightarrow>
    is_singleton {pa \<in> set ps. besitz pa = p} \<Longrightarrow>
    is_singleton {pa \<in> set ps. swap p1 p2 besitz pa = p} \<Longrightarrow>
    the_elem {pa \<in> set ps. swap p1 p2 besitz pa = p} = the_elem {pa \<in> set ps. besitz pa = p}\<close>
  apply(rule arg_cong[of _ _ the_elem])
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
(*>*)

end
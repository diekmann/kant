theory Zahlenwelt
imports BeispielPerson ExecutableHelper Swap
begin

section\<open>Zahlenwelt Helper\<close>
text\<open>Wir werden Beispiele betrachten, in denen wir Welten modellieren, in denen jeder Person eine
Zahl zugewiesen wird: \<^typ>\<open>person \<Rightarrow> int\<close>.
Diese Zahl kann zum Beispiel der Besitz oder Wohlstand einer Person sein, oder das Einkommen.
Wobei Gesamtbesitz und Einkommen über einen kurzen Zeitraum recht unterschiedliche Sachen
modellieren.

Hier sind einige Hilfsfunktionen um mit \<^typ>\<open>person \<Rightarrow> int\<close> allgmein zu arbeiten.\<close>

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
  \<longleftrightarrow> filter P ps = [] \<and> a = x"
  by (simp add: list.case_eq_if)

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
    apply(simp_all add: case_filter_empty_some_helper)
    apply (metis (mono_tags, lifting) filter_empty_conv list.case_eq_if option.distinct(1))
   apply (metis (mono_tags, lifting) empty_filter_conv list.case_eq_if option.distinct(1))
  by (smt (verit, del_insts) filter_empty_conv list.simps(5) neq_Nil_conv option.discI)
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
(*>*)

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
   apply(safe) thm is_singleton_the_elem
    apply (smt (verit) CollectI empty_filter_conv list.simps(4) singletonD)
    apply (smt (z3) Collect_cong)

  apply(induction \<open>ps\<close>)
   apply(simp add: opfer_eindeutig_nach_besitz_auswaehlen_def; fail)
  apply(simp add: opfer_eindeutig_nach_besitz_auswaehlen_def)
   apply(safe)
  apply (smt (z3) empty_filter_conv empty_set filter_set is_singletonI' list.case_eq_if mem_Collect_eq member_filter)
  thm card_1_singleton_iff Collect_cong empty_filter_conv list.case_eq_if singleton_conv
  thm Set.filter_def empty_Collect_eq empty_set filter_set is_singletonI' is_singleton_the_elem list.exhaust list.simps(5) mem_Collect_eq
  by (smt (z3) Collect_cong)


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
  by (smt (verit, del_insts) CollectI empty_Collect_eq empty_iff insertI1 is_singleton_the_elem singletonD swap_nothing)


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
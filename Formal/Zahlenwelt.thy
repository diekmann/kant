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
definition DEFAULT :: "person \<Rightarrow> int" where
  "DEFAULT \<equiv> \<lambda>p. 0"

(*<*)
syntax
  "_ZahlenWelt"  :: "updbinds \<Rightarrow> 'a" ("(1\<^url>[_])")

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
  "f(p += n) \<equiv> (f(p := (f p) + n))"

abbreviation num_fun_minus_syntax ("_ '(_ -= _')") where
  "f(p -= n) \<equiv> (f(p := (f p) - n))"

lemma \<open>(\<^url>[Alice:=8, Bob:=3, Eve:= 5])(Bob += 4) Bob = 7\<close> by eval
lemma \<open>(\<^url>[Alice:=8, Bob:=3, Eve:= 5])(Bob -= 4) Bob = -1\<close> by eval


lemma fixes n:: int shows "f(p += n)(p -= n) = f" by(simp)


text\<open>Diskriminierungsfrei eine \<^typ>\<open>'person\<close> eindeutig anhand Ihres Besitzes auswählen:\<close>
definition opfer_eindeutig_nach_besitz_auswaehlen
  :: "int \<Rightarrow> ('person \<Rightarrow> int) \<Rightarrow> 'person list \<Rightarrow> 'person option" where
  "opfer_eindeutig_nach_besitz_auswaehlen b besitz ps = 
     (case filter (\<lambda>p. besitz p = b) ps
        of [opfer] \<Rightarrow> Some opfer
         | _ \<Rightarrow> None)"

(*<*)
lemma opfer_eindeutig_nach_besitz_auswaehlen_injective:
  "opfer_eindeutig_nach_besitz_auswaehlen opfer_nach_besitz besitz ps = Some opfer
  \<Longrightarrow> inj_on besitz {p \<in> set ps. besitz p = opfer_nach_besitz}"
  apply(simp add: inj_on_def)
  apply(safe)
  apply(induction ps)
   apply(simp)
  apply(simp)
  apply(simp add: opfer_eindeutig_nach_besitz_auswaehlen_def)
  apply(safe)
    apply(simp_all)
    apply (metis (mono_tags, lifting) filter_empty_conv list.case_eq_if option.distinct(1))
   apply (metis (mono_tags, lifting) empty_filter_conv list.case_eq_if option.distinct(1))
  by (smt (verit, del_insts) filter_empty_conv list.simps(5) neq_Nil_conv option.discI)
(*>*)

definition the_single_elem :: "'a set \<Rightarrow> 'a option" where
  "the_single_elem s \<equiv> if card s = 1 then Some (Set.the_elem s) else None"

(*<*)
lemma the_single_elem:
  "the_single_elem s = (if is_singleton s then Some (Set.the_elem s) else None)"
  apply(simp add: is_singleton_the_elem the_single_elem_def card_1_singleton_iff)
  by auto

lemma "the_single_elem {a} = Some a"
  by(simp add: the_single_elem_def)
lemma "a \<noteq> b \<Longrightarrow> the_single_elem {a,b} = None"
  by(simp add: the_single_elem_def)
(*>*)

lemma opfer_eindeutig_nach_besitz_auswaehlen_the_single_elem:
  "distinct ps \<Longrightarrow> 
  opfer_eindeutig_nach_besitz_auswaehlen opfer_nach_besitz besitz ps =
          the_single_elem {p \<in> set ps. besitz p = opfer_nach_besitz}"
  apply(simp add: the_single_elem)
  apply(safe)
   apply(induction ps)
    apply (simp add: is_singleton_altdef; fail)
   apply(simp)
   apply(simp add: opfer_eindeutig_nach_besitz_auswaehlen_def)
   apply(simp add: is_singleton_the_elem)
   apply(safe) thm is_singleton_the_elem
    apply (smt (verit) CollectI empty_filter_conv list.simps(4) singletonD)
    apply (smt (z3) Collect_cong)

  apply(induction ps)
   apply(simp add: opfer_eindeutig_nach_besitz_auswaehlen_def; fail)
  apply(simp add: opfer_eindeutig_nach_besitz_auswaehlen_def)
   apply(safe)
  apply (smt (z3) empty_filter_conv empty_set filter_set is_singletonI' list.case_eq_if mem_Collect_eq member_filter)
  thm card_1_singleton_iff Collect_cong empty_filter_conv list.case_eq_if singleton_conv
  thm Set.filter_def empty_Collect_eq empty_set filter_set is_singletonI' is_singleton_the_elem list.exhaust list.simps(5) mem_Collect_eq
  by (smt (z3) Collect_cong)


lemma opfer_eindeutig_nach_besitz_auswaehlen_the_single_elem_enumall:
  "opfer_eindeutig_nach_besitz_auswaehlen opfer_nach_besitz besitz enum_class.enum =
          the_single_elem {p. besitz p = opfer_nach_besitz}"
  apply(subst opfer_eindeutig_nach_besitz_auswaehlen_the_single_elem)
  using enum_class.enum_distinct apply(simp)
  apply(simp add: enum_class.enum_UNIV)
  done


(*<*)
lemma the_elem_singleton_swap:
  "p1 \<in> set ps \<Longrightarrow>
    p2 \<in> set ps \<Longrightarrow>
    the_elem {pa \<in> set ps. swap p1 p2 besitz pa = p} = p2 \<Longrightarrow>
    is_singleton {pa \<in> set ps. swap p1 p2 besitz pa = p} \<Longrightarrow>
    is_singleton {pa \<in> set ps. besitz pa = p} \<Longrightarrow> the_elem {pa \<in> set ps. besitz pa = p} = p1"
  by (smt (verit, del_insts) is_singleton_the_elem mem_Collect_eq singleton_iff swap_b)

lemma the_elem_singleton_swap_none:
    "p1 \<in> set ps \<Longrightarrow>
    p2 \<in> set ps \<Longrightarrow>
    the_elem {pa \<in> set ps. swap p1 p2 besitz pa = p} \<noteq> p2 \<Longrightarrow>
    the_elem {pa \<in> set ps. swap p1 p2 besitz pa = p} \<noteq> p1 \<Longrightarrow>
    is_singleton {pa \<in> set ps. besitz pa = p} \<Longrightarrow>
    is_singleton {pa \<in> set ps. swap p1 p2 besitz pa = p} \<Longrightarrow>
    the_elem {pa \<in> set ps. swap p1 p2 besitz pa = p} = the_elem {pa \<in> set ps. besitz pa = p}"
  by (smt (verit, del_insts) CollectI empty_Collect_eq empty_iff insertI1 is_singleton_the_elem singletonD swap_nothing)


lemma is_singleton_swap:
  "p1 \<in> set ps \<Longrightarrow>
   p2 \<in> set ps \<Longrightarrow>
    is_singleton {pa \<in> set ps. swap p1 p2 besitz pa = p}
    \<longleftrightarrow> is_singleton {pa \<in> set ps. besitz pa = p}"
  apply(cases "p2 \<noteq> p1") (*smt lol*)
  subgoal by (smt (verit) CollectD CollectI insertCI is_singletonI' is_singleton_the_elem singleton_iff swap_a swap_b swap_nothing)
  apply(simp)
  done


lemma if_swap_person_help_same: "p1 = a \<Longrightarrow>
       p2 = a \<Longrightarrow>
       (\<lambda>p. if p = a then p2 else if p = p2 then p1 else p) = id"
  by auto


(*TODO: das if will in ne definition*)
lemma opfer_eindeutig_nach_besitz_auswaehlen_swap:
    "p1 \<in> set ps \<Longrightarrow>
     p2 \<in> set ps \<Longrightarrow>
     distinct ps \<Longrightarrow>
  map_option
        (\<lambda>p. if p = p1 then p2 else if p = p2 then p1 else p)
        (opfer_eindeutig_nach_besitz_auswaehlen p (swap p1 p2 besitz) ps)
  = opfer_eindeutig_nach_besitz_auswaehlen p besitz ps"
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
  "p1 \<in> set ps \<Longrightarrow>
   p2 \<in> set ps \<Longrightarrow>
   distinct ps \<Longrightarrow>
opfer_eindeutig_nach_besitz_auswaehlen p (swap p1 p2 besitz) ps =
  map_option (\<lambda>p. if p = p1 then p2 else if p = p2 then p1 else p)
    (opfer_eindeutig_nach_besitz_auswaehlen p besitz ps)"
  using opfer_eindeutig_nach_besitz_auswaehlen_swap[of p1 ps p2 p "(swap p1 p2 besitz)", simplified swap1]
  by simp



lemma opfer_eindeutig_nach_besitz_auswaehlen_swap_enumall:
"opfer_eindeutig_nach_besitz_auswaehlen p (swap p1 p2 besitz) enum_class.enum =
  map_option (\<lambda>p. if p = p1 then p2 else if p = p2 then p1 else p)
    (opfer_eindeutig_nach_besitz_auswaehlen p besitz enum_class.enum)"
  apply(rule opfer_eindeutig_nach_besitz_auswaehlen_swap_alt)
  using enum_class.in_enum enum_class.enum_distinct by auto
(*>*)

end
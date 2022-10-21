theory BeispielZahlenwelt
imports Zahlenwelt Simulation Gesetze BeispielPerson
begin

section\<open>Beispiel: Zahlenwelt\<close>

  text\<open>Wir nehmen an, die Welt lässt sich durch eine Zahl darstellen,
  die den Besitz einer Person modelliert.
  
  Der Besitz ist als ganze Zahl \<^typ>\<open>int\<close> modelliert und kann auch beliebig negativ werden.\<close>
  datatype zahlenwelt = Zahlenwelt
    "person \<Rightarrow> int \<comment> \<open>besitz: Besitz jeder Person.\<close>"
  
  fun gesamtbesitz :: "zahlenwelt \<Rightarrow> int" where
    "gesamtbesitz (Zahlenwelt besitz) = sum_list (map besitz Enum.enum)"
  
  lemma "gesamtbesitz (Zahlenwelt \<^url>[Alice := 4, Carol := 8]) = 12" by eval
  lemma "gesamtbesitz (Zahlenwelt \<^url>[Alice := 4, Carol := 4]) = 8" by eval
  
  
  fun meins :: "person \<Rightarrow> zahlenwelt \<Rightarrow> int" where
    "meins p (Zahlenwelt besitz) = besitz p"
  
  lemma "meins Carol (Zahlenwelt \<^url>[Alice := 8, Carol := 4]) = 4" by eval
  
  (*<*)
  definition "show_zahlenwelt w \<equiv> case w of Zahlenwelt besitz \<Rightarrow> show_num_fun besitz"
  fun delta_zahlenwelt :: "(zahlenwelt, person, int) delta" where
    "delta_zahlenwelt (Handlung (Zahlenwelt vor_besitz) (Zahlenwelt nach_besitz)) =
        Aenderung.delta_num_fun (Handlung vor_besitz nach_besitz)"
  (*>*)

(*TODO: move up*)
definition swap :: "'a \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" where
  "swap a b f \<equiv> f(a:=f b, b:= f a)"

lemma swap1[simp]: "swap a b (swap a b f) = f"
  by(simp add: swap_def)
lemma swap2[simp]: "swap b a (swap a b f) = f"
  by(simp add: swap_def)
lemma swap_id[simp]: "swap a a f = f"
  by(simp add: swap_def)
lemma "f_swapped = (swap a b f) \<Longrightarrow> f_swapped a = f b \<and> f_swapped b = f a"
  by(simp add: swap_def)
lemma swap_symmetric: "swap a b = swap b a"
  by(simp add: fun_eq_iff swap_def)
lemma map_swap_none: "a \<notin> set P \<Longrightarrow> b \<notin> set P \<Longrightarrow> map (swap a b f) P = map f P"
  by(simp add: swap_def)
lemma map_swap_one: "a \<notin> set P \<Longrightarrow>  map (swap a b f) P = map (f(b:=f a)) P"
  by(simp add: swap_def)
lemma swap_a: "swap a b f a = f b"
  by(simp add: swap_def)
lemma swap_b: "swap a b f b = f a"
  by(simp add: swap_def)
lemma sum_swap_none: "a \<notin> P \<Longrightarrow> b \<notin> P \<Longrightarrow> sum (swap a b f) P = sum f P"
  apply(simp add: swap_def)
  by (smt (verit, best) fun_upd_other sum.cong)
lemma swap_nothing: "a \<noteq> p1 \<Longrightarrow> a \<noteq> p2 \<Longrightarrow> swap p1 p2 f a = f a"
  by(simp add: swap_def)

fun zahlenwelt_personen_swap :: "person \<Rightarrow> person \<Rightarrow> zahlenwelt \<Rightarrow> zahlenwelt" where
  "zahlenwelt_personen_swap p1 p2 (Zahlenwelt besitz) = Zahlenwelt (swap p1 p2 besitz)"

lemma \<open>zahlenwelt_personen_swap Alice Carol (Zahlenwelt \<^url>[Alice := 4, Bob := 6, Carol := 8])
  = (Zahlenwelt \<^url>[Alice := 8, Bob := 6, Carol := 4])\<close>
  by eval

lemma zahlenwelt_personen_swap_sym:
  "zahlenwelt_personen_swap p1 p2 welt = zahlenwelt_personen_swap p2 p1 welt"
  by(cases welt, simp add: swap_symmetric)

subsection\<open>Handlungen\<close>

  text\<open>Die folgende Handlung erschafft neuen Besitz aus dem Nichts:\<close>
  fun erschaffen :: "nat \<Rightarrow> person \<Rightarrow> zahlenwelt \<Rightarrow> zahlenwelt" where
    "erschaffen i p (Zahlenwelt besitz) = Zahlenwelt (besitz(p += int i))"
  lemma "wohlgeformte_handlungsabsicht zahlenwelt_personen_swap welt (HandlungF (erschaffen n))"
    apply(simp add: wohlgeformte_handlungsabsicht_def)
    apply(intro allI, case_tac welt, simp)
    apply(simp add: swap_def)
    done
  
  fun stehlen :: "int \<Rightarrow> person \<Rightarrow> person \<Rightarrow> zahlenwelt \<Rightarrow> zahlenwelt" where
    "stehlen beute opfer dieb (Zahlenwelt besitz) =
        Zahlenwelt (besitz(opfer -= beute)(dieb += beute))"
  lemma "wohlgeformte_handlungsabsicht zahlenwelt_personen_swap welt (HandlungF (stehlen n p))"
    apply(simp add: wohlgeformte_handlungsabsicht_def)
    oops (*MIST. Aber okay, die Handlung diskriminiert!*)

(*TODO: Handlung stehlen, aber opfer wird nach Besitz ausgesucht, nicht nach namen.*)
  fun stehlen2 :: "int \<Rightarrow> int \<Rightarrow> person \<Rightarrow> zahlenwelt \<Rightarrow> zahlenwelt" where
    "stehlen2 beute opfer_nach_besitz dieb (Zahlenwelt besitz) =
        Zahlenwelt (besitz((THE opfer. besitz opfer = opfer_nach_besitz) -= beute)(dieb += beute))"
  lemma "wohlgeformte_handlungsabsicht zahlenwelt_personen_swap welt (HandlungF (stehlen2 n p))"
    apply(simp add: wohlgeformte_handlungsabsicht_def)
    apply(intro allI, case_tac welt, simp)
    oops (*TODO. THE. ist etwas hart, evtl sollte ich das als Liste implementieren.
  wird eh nix wegen nichtdeterminismus*)

fun opfer_nach_besitz_auswaehlen :: "int \<Rightarrow> ('person \<Rightarrow> int) \<Rightarrow> 'person list \<Rightarrow> 'person option" where
  "opfer_nach_besitz_auswaehlen _ _ [] = None"
| "opfer_nach_besitz_auswaehlen b besitz (p#ps) = 
    (if besitz p = b then Some p else opfer_nach_besitz_auswaehlen b besitz ps)"

fun stehlen3 :: "int \<Rightarrow> int \<Rightarrow> person \<Rightarrow> zahlenwelt \<Rightarrow> zahlenwelt" where
    "stehlen3 beute opfer_nach_besitz dieb (Zahlenwelt besitz) =
      (case opfer_nach_besitz_auswaehlen opfer_nach_besitz besitz Enum.enum
         of None \<Rightarrow> (Zahlenwelt besitz)
          | Some opfer \<Rightarrow> Zahlenwelt (besitz(opfer -= beute)(dieb += beute))
      )"
value\<open>map_handlung show_zahlenwelt
      (handeln Alice (Zahlenwelt \<^url>[Alice := 5, Bob := 10, Carol := -3])
              (HandlungF (stehlen3 3 10)))\<close>
(*wenn es mehrere potenzielle opfer gibt ist die auswahl irgendwie random. Das diskriminiert.*)
value\<open>map_handlung show_zahlenwelt
      (handeln Alice (Zahlenwelt \<^url>[Alice := 10, Bob := 10, Carol := -3])
              (HandlungF (stehlen3 3 10)))\<close>
value\<open>map_handlung show_zahlenwelt
      (handeln Bob (Zahlenwelt \<^url>[Alice := 10, Bob := 10, Carol := -3])
              (HandlungF (stehlen3 3 10)))\<close>
value\<open>map_handlung show_zahlenwelt
      (handeln Carol (Zahlenwelt \<^url>[Alice := 10, Bob := 10, Carol := -3])
              (HandlungF (stehlen3 3 10)))\<close>
value\<open>map_handlung show_zahlenwelt
      (handeln Carol (Zahlenwelt \<^url>[Alice := -3, Bob := 10, Carol := 10])
              (HandlungF (stehlen3 3 10)))\<close>
lemma "\<not>wohlgeformte_handlungsabsicht
    zahlenwelt_personen_swap (Zahlenwelt (\<lambda>x. 0)) (HandlungF (stehlen3 (1) 0))"
  by(eval)


(*So wird das was*)
definition opfer_eindeutig_nach_besitz_auswaehlen
  :: "int \<Rightarrow> ('person \<Rightarrow> int) \<Rightarrow> 'person list \<Rightarrow> 'person option" where
  "opfer_eindeutig_nach_besitz_auswaehlen b besitz ps = 
     (case filter (\<lambda>p. besitz p = b) ps
        of [opfer] \<Rightarrow> Some opfer
         | _ \<Rightarrow> None)"

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

definition the_single_elem :: "'a set \<Rightarrow> 'a option" where
  "the_single_elem s \<equiv> if card s = 1 then Some (Set.the_elem s) else None"

lemma the_single_elem:
  "the_single_elem s = (if is_singleton s then Some (Set.the_elem s) else None)"
  apply(simp add: is_singleton_the_elem the_single_elem_def card_1_singleton_iff)
  by auto

lemma "the_single_elem {a} = Some a"
  by(simp add: the_single_elem_def)
lemma "a \<noteq> b \<Longrightarrow> the_single_elem {a,b} = None"
  by(simp add: the_single_elem_def)

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

fun stehlen4 :: "int \<Rightarrow> int \<Rightarrow> person \<Rightarrow> zahlenwelt \<Rightarrow> zahlenwelt" where
    "stehlen4 beute opfer_nach_besitz dieb (Zahlenwelt besitz) =
      (case opfer_eindeutig_nach_besitz_auswaehlen opfer_nach_besitz besitz Enum.enum
         of None \<Rightarrow> (Zahlenwelt besitz)
          | Some opfer \<Rightarrow> Zahlenwelt (besitz(opfer -= beute)(dieb += beute))
      )"
value\<open>map_handlung show_zahlenwelt
      (handeln Alice (Zahlenwelt \<^url>[Alice := 8, Bob := 10, Carol := -3])
              (HandlungF (stehlen4 3 10)))\<close>
value\<open>map_handlung show_zahlenwelt
      (handeln Bob (Zahlenwelt \<^url>[Alice := 8, Bob := 10, Carol := -3])
              (HandlungF (stehlen4 3 10)))\<close>
value\<open>map_handlung show_zahlenwelt
      (handeln Carol (Zahlenwelt \<^url>[Alice := 8, Bob := 10, Carol := -3])
              (HandlungF (stehlen4 3 10)))\<close>
value\<open>map_handlung show_zahlenwelt
      (handeln Bob (Zahlenwelt \<^url>[Alice := 10, Bob := 8, Carol := -3])
              (HandlungF (stehlen4 3 10)))\<close>


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

lemma "p1 \<in> set ps \<Longrightarrow>
       p2 \<in> set ps \<Longrightarrow>
       distinct ps \<Longrightarrow>
  filter (\<lambda>pa. swap p1 p2 besitz pa = p) ps =
  map (\<lambda>p. if p = p1 then p2 else if p = p2 then p1 else p) (filter (\<lambda>pa. besitz pa = p) ps)"
  (*nitpick found a counterexample*)
  oops
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


  (*WUHUUUUU*)
lemma wohlgeformte_handlungsabsicht_stehlen4:
  "wohlgeformte_handlungsabsicht zahlenwelt_personen_swap welt (HandlungF (stehlen4 n p))"
    apply(simp add: wohlgeformte_handlungsabsicht_def)
    apply(intro allI, case_tac welt, simp)
    apply(simp add: opfer_eindeutig_nach_besitz_auswaehlen_swap_enumall)
    apply(simp add: opfer_eindeutig_nach_besitz_auswaehlen_the_single_elem_enumall)
    apply(simp add: the_single_elem)
    apply(safe)
     apply (simp add: swap_def; fail)
    by (simp add: fun_upd_twist swap_def)


  fun schenken :: "int \<Rightarrow> person \<Rightarrow> person \<Rightarrow> zahlenwelt \<Rightarrow> zahlenwelt" where
    "schenken betrag empfaenger schenker (Zahlenwelt besitz) =
        Zahlenwelt (besitz(schenker -= betrag)(empfaenger += betrag))"
  
  text\<open>Da wir ganze Zahlen verwenden und der Besitz auch beliebig negativ werden kann,
  ist Stehlen äquivalent dazu einen negativen Betrag zu verschenken:\<close>
  lemma stehlen_ist_schenken: "stehlen i = schenken (-i)"
    apply(simp add: fun_eq_iff)
    apply(intro allI, rename_tac p1 p2 welt, case_tac welt)
    by auto
  
  text\<open>Das Modell ist nicht ganz perfekt, .... Aber passt schon um damit zu spielen.\<close>


  text\<open>Reset versetzt die Welt wieder in den Ausgangszustand. Eine sehr destruktive Handlung.\<close>
  fun reset :: "person \<Rightarrow> zahlenwelt \<Rightarrow> zahlenwelt" where
    "reset ich (Zahlenwelt besitz) = Zahlenwelt (\<lambda> _. 0)"

  (*TODO: eigentlich keine gute handlung, aber fuer einen verschuldeten egoisten gut.*)


subsection\<open>Setup\<close>
  text\<open>\<^const>\<open>Alice\<close> hat Besitz, \<^const>\<open>Bob\<close> ist reicher, \<^const>\<open>Carol\<close> hat Schulden.\<close>
  definition "initialwelt \<equiv> Zahlenwelt \<^url>[Alice := 5, Bob := 10, Carol := -3]"
  
  text\<open>Wir nehmen an unsere handelnde Person ist \<^const>\<open>Alice\<close>.\<close>
  
  definition "beispiel_case_law_absolut maxime handlungsabsicht \<equiv>
    simulateOne
      (SimConsts
        Alice
        maxime
        (printable_case_law_ableiten_absolut show_zahlenwelt))
      5 handlungsabsicht initialwelt (Gesetz {})"
  definition "beispiel_case_law_relativ maxime handlungsabsicht \<equiv>
    simulateOne
      (SimConsts
        Alice
        maxime
        (case_law_ableiten_relativ delta_zahlenwelt))
      10 handlungsabsicht initialwelt (Gesetz {})"

subsection\<open>Alice erzeugt 5 Wohlstand für sich.\<close>

  text\<open>Wir definieren eine Maxime die besagt,
  dass sich der Besitz einer Person nicht verringern darf:\<close>
  fun individueller_fortschritt :: "person \<Rightarrow> zahlenwelt handlung \<Rightarrow> bool" where
    "individueller_fortschritt p (Handlung vor nach) \<longleftrightarrow> (meins p vor) \<le> (meins p nach)"
  definition maxime_zahlenfortschritt :: "(person, zahlenwelt) maxime" where
    "maxime_zahlenfortschritt \<equiv> Maxime (\<lambda>ich. individueller_fortschritt ich)"


lemma "maxime_und_handlungsabsicht_generalisieren maxime_zahlenfortschritt (HandlungF (erschaffen 5)) p"
  apply(simp add: maxime_zahlenfortschritt_def, intro allI)
  apply(case_tac w1, case_tac w2, simp)
  done

lemma "maxime_und_handlungsabsicht_generalisieren maxime_zahlenfortschritt (HandlungF (stehlen 5 Bob)) p"
  apply(simp add: maxime_zahlenfortschritt_def, intro allI)
  apply(case_tac w1, case_tac w2, simp)
  done

  text\<open>In jeder Welt ist die Handlung \<^const>\<open>moralisch\<close>:\<close>
  lemma "moralisch welt maxime_zahlenfortschritt (HandlungF (erschaffen 5))"
    apply(cases welt)
    by(simp add: maxime_zahlenfortschritt_def moralisch_simp)


  (*AWESOME!*)
  text\<open>Die \<^const>\<open>maxime_zahlenfortschritt\<close> erfüllt nicht den \<^const>\<open>kategorischer_imperativ\<close>
  da \<^const>\<open>Alice\<close> nach der Maxime z.B. \<^const>\<open>Bob\<close> bestehlen würde.\<close>
  lemma "\<not> kategorischer_imperativ zahlenwelt_personen_swap initialwelt maxime_zahlenfortschritt"
    apply(simp add: maxime_zahlenfortschritt_def moralisch_simp)
    apply(rule_tac x="HandlungF (stehlen4 1 10)" in exI)
    apply(simp add: wohlgeformte_handlungsabsicht_stehlen4)
    apply(intro conjI)
     apply(rule_tac x=Alice in exI)
     apply(intro conjI allI)
      apply(case_tac w1, case_tac w2, simp)
      apply(simp add: opfer_eindeutig_nach_besitz_auswaehlen_the_single_elem_enumall)
    apply(case_tac "the_single_elem {p. x p = 10}", simp)
       apply(case_tac "the_single_elem {p. xa p = 10}")
    apply(simp; fail)
       apply(case_tac "the_single_elem {p. xa p = 10}")
        apply(simp; fail)
       apply(simp; fail)
      apply(simp)
       apply(case_tac "the_single_elem {p. xa p = 10}")
        apply(simp; fail)
      apply(simp; fail)
    apply(simp add: initialwelt_def, eval)

    apply(rule_tac x=Bob in exI)
    apply(rule_tac x=Alice in exI)
    apply(simp add: initialwelt_def, eval)
    done

lemma hlp1: "meins p1 (zahlenwelt_personen_swap p1 p2 welt) = meins p2 welt"
  by(cases welt, simp add: swap_def)
lemma hlp2: "meins p2 (zahlenwelt_personen_swap p1 p2 welt) = meins p1 welt"
  by(cases welt, simp add: swap_def)

lemma hlp3: "p1 \<noteq> p2 \<Longrightarrow> p \<noteq> p1 \<Longrightarrow> p \<noteq> p2 \<Longrightarrow>
       meins p (zahlenwelt_personen_swap p1 p2 welt) = meins p welt"
  by(cases welt, simp add: swap_def)

(*hieran arbeite ich gerade*)
(*ich hoffe, das kann man generalisieren?*)
(*AWESOME!*)
  lemma "kategorischer_imperativ zahlenwelt_personen_swap welt
    (Maxime (\<lambda>(ich::person) h. (\<forall>pX. individueller_fortschritt pX h)))"
    apply(simp add: maxime_zahlenfortschritt_def moralisch_simp)
    apply(intro allI impI, elim conjE exE)
    apply(simp add: wohlgeformte_handlungsabsicht_def)
    apply(case_tac h, rename_tac ha p2 pX p1 h, simp)


    apply(subgoal_tac "meins pX welt \<le> meins pX (h p1 welt)")
    prefer 2 apply(simp; fail)

    apply(erule_tac x=p2 in allE)
    apply(erule_tac x=p1 in allE) back
    apply(elim conjE)
    apply(simp)
    apply(thin_tac "welt = _")
    apply(case_tac "p1 = p2")
     apply(simp; fail)
    apply(thin_tac "h p2 welt = _")

    apply(case_tac "pX = p1")
     apply(simp add: hlp1)
     apply(erule_tac x="zahlenwelt_personen_swap p1 p2 welt" in allE)
     apply(erule_tac x="welt" in allE)

     apply(case_tac "(\<forall>pX. meins pX (zahlenwelt_personen_swap p1 p2 welt)
               \<le> meins pX (h p1 (zahlenwelt_personen_swap p1 p2 welt)))")
      prefer 2 apply(simp; fail)
     apply(simp)
     apply(erule_tac x=p2 in allE) back
     apply(simp add: hlp2)
     apply (simp add: zahlenwelt_personen_swap_sym; fail)
    

    apply(case_tac "pX = p2")
     apply(simp)
     apply(simp add: hlp2)
     apply(erule_tac x="zahlenwelt_personen_swap p2 p1 welt" in allE)
     apply(erule_tac x="welt" in allE)
     apply(case_tac "(\<forall>pX. meins pX (zahlenwelt_personen_swap p2 p1 welt)
               \<le> meins pX (h p1 (zahlenwelt_personen_swap p2 p1 welt)))")
      prefer 2 apply(simp; fail)
     apply(simp)
     apply(erule_tac x=p1 in allE) back
     apply(simp add: hlp2; fail)

    apply(simp add: hlp3)
    apply(erule_tac x="zahlenwelt_personen_swap p2 p1 welt" in allE)
    apply(erule_tac x="welt" in allE)
    apply(simp)
    apply(erule_tac x=pX in allE) back
    apply(simp add: hlp3; fail)
    done

lemma "P = individueller_fortschritt \<Longrightarrow>
  P p2 (Handlung (zahlenwelt_personen_swap p1 p2 welt) (h p1 (zahlenwelt_personen_swap p1 p2 welt)))
  \<longleftrightarrow>
  P p1 (Handlung welt (zahlenwelt_personen_swap p1 p2 (h p1 (zahlenwelt_personen_swap p2 p1 welt))))"
  apply(simp)
  by (simp add: hlp1 hlp2 zahlenwelt_personen_swap_sym)

definition "Maxime_kommutiert P welt \<equiv> \<forall> p1 p2 h.
  P p2 (Handlung (zahlenwelt_personen_swap p1 p2 welt) (h p1 (zahlenwelt_personen_swap p1 p2 welt)))
  \<longleftrightarrow>
  P p1 (Handlung welt (zahlenwelt_personen_swap p1 p2 (h p1 (zahlenwelt_personen_swap p2 p1 welt))))"

lemma "P = individueller_fortschritt \<Longrightarrow>
p1 \<noteq> p2 \<Longrightarrow> pX \<noteq> p1 \<Longrightarrow> pX \<noteq> p2 \<Longrightarrow>
P pX (Handlung welt (zahlenwelt_personen_swap p1 p2 (h p1 welt')))
\<longleftrightarrow>
P pX (Handlung welt (h p1 welt'))"
  apply(simp)
  apply (simp add: hlp3)
  done

definition "Maxime_swap_unrelated P welt \<equiv> \<forall> p1 p2 pX h (welt'::zahlenwelt).
  p1 \<noteq> p2 \<longrightarrow> pX \<noteq> p1 \<longrightarrow> pX \<noteq> p2 \<longrightarrow>
  P pX (Handlung welt (zahlenwelt_personen_swap p1 p2 (h p1 welt')))
  \<longleftrightarrow>
  P pX (Handlung welt (h p1 welt'))"

lemma "P = individueller_fortschritt \<Longrightarrow>
\<forall> p1 p2 pX welt'.
  p1 \<noteq> p2 \<longrightarrow> pX \<noteq> p1 \<longrightarrow> pX \<noteq> p2 \<longrightarrow> 
    P pX (Handlung (zahlenwelt_personen_swap p2 p1 welt) welt')
    = P pX (Handlung welt welt')"
  by(simp add:hlp3)

(*TODO: die 3 Eiggenschaften sind nur ueber die Maxime und die swap funktion.
evtl muss ich die in den kategorischen imperativ uebernehmen?
Auf jeden fall sollte ich testen, ob das auch fuer den globalen fortschritt gilt!
*)
lemma
  assumes kom: "Maxime_kommutiert P welt"
     and unrel1: "Maxime_swap_unrelated P welt"
    (* das ist Maxime_swap_unrelated nur auf 1. param.*)
     and unrel2: "\<forall> p1 p2 pX welt'.
  p1 \<noteq> p2 \<longrightarrow> pX \<noteq> p1 \<longrightarrow> pX \<noteq> p2 \<longrightarrow> 
    P pX (Handlung (zahlenwelt_personen_swap p2 p1 welt) welt')
    \<longleftrightarrow> P pX (Handlung welt welt')"
  shows "kategorischer_imperativ zahlenwelt_personen_swap welt
    (Maxime (\<lambda>ich h. (\<forall>pX::person. P pX h)))"
  apply(simp add: maxime_zahlenfortschritt_def moralisch_simp)
  apply(intro allI impI, elim conjE exE)
  apply(simp add: wohlgeformte_handlungsabsicht_def)
  apply(case_tac h, rename_tac ha p2 pX p1 h, simp)


  apply(subgoal_tac "P pX (Handlung welt (h p1 welt))")
   prefer 2 apply(simp; fail)

  apply(erule_tac x=p2 in allE)
  apply(erule_tac x=p1 in allE) back
  apply(elim conjE)
  apply(simp)
  apply(thin_tac "welt = _")
  apply(case_tac "p1 = p2")
   apply(simp; fail)
  apply(thin_tac "h p2 welt = _")

  apply(case_tac "pX = p1", simp)
   apply(erule_tac x="zahlenwelt_personen_swap p1 p2 welt" in allE)
   apply(erule_tac x="welt" in allE)

   apply(case_tac "(\<forall>pX. P pX
              (Handlung (zahlenwelt_personen_swap p1 p2 welt)
                (h p1 (zahlenwelt_personen_swap p1 p2 welt))))")
    prefer 2 apply(simp; fail)
   apply(simp)
   apply(erule_tac x=p2 in allE) back
  using kom[simplified Maxime_kommutiert_def] apply(simp; fail)


  apply(case_tac "pX = p2")
   apply(simp)
   apply(erule_tac x="zahlenwelt_personen_swap p2 p1 welt" in allE)
   apply(erule_tac x="welt" in allE)
   apply(case_tac "(\<forall>pX. P pX
              (Handlung (zahlenwelt_personen_swap p2 p1 welt)
                (h p1 (zahlenwelt_personen_swap p2 p1 welt))))")
    prefer 2 apply(simp; fail)
   apply(simp)
   apply(erule_tac x=p1 in allE) back
  using kom[simplified Maxime_kommutiert_def]
  using zahlenwelt_personen_swap_sym apply fastforce 

  apply(erule_tac x="zahlenwelt_personen_swap p2 p1 welt" in allE)
  apply(erule_tac x="welt" in allE)
  apply(simp)
  apply(erule_tac x=pX in allE) back
  using unrel1[simplified Maxime_swap_unrelated_def] 
  apply(simp)
  apply(erule_tac x=p1 in allE) back
  apply(erule_tac x=p2 in allE) back
  apply(elim impE, (simp; fail))
  apply(erule_tac x=pX in allE) back
  apply(elim impE, (simp; fail)+)
  apply(erule_tac x=h in allE)
  apply(erule_tac x="(zahlenwelt_personen_swap p2 p1 welt)" in allE)

  apply(simp add: unrel2)
  done


  text\<open>Alice kann beliebig oft 5 Wohlstand für sich selbst erschaffen.
  Das entstehende Gesetz ist nicht sehr gut, da es einfach jedes Mal einen
  Snapshot der Welt aufschreibt und nicht sehr generisch ist.\<close>
  lemma \<open>beispiel_case_law_absolut maxime_zahlenfortschritt (HandlungF (erschaffen 5))
  =
  Gesetz
  {(\<section> 5,
    Rechtsnorm
     (Tatbestand ([(Alice, 25), (Bob, 10), (Carol, - 3)], [(Alice, 30), (Bob, 10), (Carol, - 3)]))
     (Rechtsfolge Erlaubnis)),
   (\<section> 4,
    Rechtsnorm
     (Tatbestand ([(Alice, 20), (Bob, 10), (Carol, - 3)], [(Alice, 25), (Bob, 10), (Carol, - 3)]))
     (Rechtsfolge Erlaubnis)),
   (\<section> 3,
    Rechtsnorm
     (Tatbestand ([(Alice, 15), (Bob, 10), (Carol, - 3)], [(Alice, 20), (Bob, 10), (Carol, - 3)]))
     (Rechtsfolge Erlaubnis)),
   (\<section> 2,
    Rechtsnorm
     (Tatbestand ([(Alice, 10), (Bob, 10), (Carol, - 3)], [(Alice, 15), (Bob, 10), (Carol, - 3)]))
     (Rechtsfolge Erlaubnis)),
   (\<section> 1,
    Rechtsnorm
     (Tatbestand ([(Alice, 5), (Bob, 10), (Carol, - 3)], [(Alice, 10), (Bob, 10), (Carol, - 3)]))
     (Rechtsfolge Erlaubnis))}
  \<close> by eval
  
  
  text\<open>Die gleiche Handlung, wir schreiben aber nur die Änderung der Welt ins Gesetz:\<close>
  lemma \<open>beispiel_case_law_relativ maxime_zahlenfortschritt (HandlungF (erschaffen 5)) =
    Gesetz
    {(\<section> 1, Rechtsnorm (Tatbestand [Gewinnt Alice 5]) (Rechtsfolge Erlaubnis))}\<close>
    by eval

subsection\<open>Kleine Änderung in der Maxime\<close>
  text\<open>In der Maxime \<^const>\<open>individueller_fortschritt\<close> hatten wir
   \<^term>\<open>(meins p nach) \<ge> (meins p vor)\<close>.
  Was wenn wir nun echten Fortschritt fordern:
   \<^term>\<open>(meins p nach) > (meins p vor)\<close>.\<close>
  
  fun individueller_strikter_fortschritt :: "person \<Rightarrow> zahlenwelt handlung \<Rightarrow> bool" where
    "individueller_strikter_fortschritt p (Handlung vor nach) \<longleftrightarrow> (meins p vor) < (meins p nach)"

  text\<open>Nun ist es \<^const>\<open>Alice\<close> verboten Wohlstand für sich selbst zu erzeugen.\<close>
  lemma \<open>beispiel_case_law_relativ
          (Maxime (\<lambda>ich. individueller_strikter_fortschritt ich))
          (HandlungF (erschaffen 5)) =
    Gesetz {(\<section> 1, Rechtsnorm (Tatbestand [Gewinnt Alice 5]) (Rechtsfolge Verbot))}\<close>
    by eval
    
  text\<open>In keiner Welt ist die Handlung nun \<^const>\<open>moralisch\<close>:\<close>
lemma "\<not> moralisch welt
          (Maxime (\<lambda>ich. individueller_strikter_fortschritt ich)) (HandlungF (erschaffen 5))"
    apply(cases welt)
    by(auto simp add: maxime_zahlenfortschritt_def moralisch_simp)

  text\<open> Der Grund ist, dass der Rest der Bevölkerung keine \<^emph>\<open>strikte\<close> Erhöhung des
  eigenen Wohlstands erlebt.
  Effektiv führt diese Maxime zu einem Gesetz, welches es einem Individuum nicht erlaubt
  mehr Besitz zu erschaffen, obwohl niemand dadurch einen Nachteil hat.
  Diese Maxime kann meiner Meinung nach nicht gewollt sein.
  
  
  Beispielsweise ist \<^const>\<open>Bob\<close> das Opfer wenn \<^const>\<open>Alice\<close> sich
  5 Wohlstand erschafft, aber \<^const>\<open>Bob\<close>'s Wohlstand sich nicht erhöht:\<close>
  lemma\<open>VerletzteMaxime (Opfer Bob) (Taeter Alice)
          (Handlung [(Alice, 5), (Bob, 10), (Carol, -3)] [(Alice, 10), (Bob, 10), (Carol, -3)])
          \<in> debug_maxime show_zahlenwelt initialwelt
            (Maxime (\<lambda>ich. individueller_strikter_fortschritt ich)) (HandlungF (erschaffen 5)) \<close>
    by eval


subsection\<open>Maxime für Globales Optimum\<close>
  text\<open>Wir bauen nun eine Maxime, die das Individuum vernachlässigt und nur nach dem
  globalen Optimum strebt:\<close>
  fun globaler_strikter_fortschritt :: "zahlenwelt handlung \<Rightarrow> bool" where
    "globaler_strikter_fortschritt (Handlung vor nach) \<longleftrightarrow> (gesamtbesitz vor) < (gesamtbesitz nach)"
  
  text\<open>Die Maxime ignoriert das \<^term>\<open>ich :: person\<close> komplett.
  
  Nun ist es \<^const>\<open>Alice\<close> wieder erlaubt, Wohlstand für sich selbst zu erzeugen,
  da sich dadurch auch der Gesamtwohlstand erhöht:\<close>
  lemma \<open>beispiel_case_law_relativ
          (Maxime (\<lambda>ich. globaler_strikter_fortschritt))
          (HandlungF (erschaffen 5)) =
    Gesetz {(\<section> 1, Rechtsnorm (Tatbestand [Gewinnt Alice 5]) (Rechtsfolge Erlaubnis))}\<close>
    by eval


  lemma "moralisch initialwelt
          (Maxime (\<lambda>ich. globaler_strikter_fortschritt)) (HandlungF (erschaffen 5))"
  by(eval)
    
    
  
  text\<open>Allerdings ist auch diese Maxime auch sehr grausam, da sie Untätigkeit verbietet:\<close>
  lemma \<open>beispiel_case_law_relativ
          (Maxime (\<lambda>ich. globaler_strikter_fortschritt))
          (HandlungF (erschaffen 0)) =
    Gesetz {(\<section> 1, Rechtsnorm (Tatbestand []) (Rechtsfolge Verbot))}\<close>
    by eval


  text\<open>Unsere initiale einfache \<^const>\<open>maxime_zahlenfortschritt\<close> würde Untätigkeit hier erlauben:\<close>
  lemma \<open>beispiel_case_law_relativ
          maxime_zahlenfortschritt
          (HandlungF (erschaffen 0)) =
    Gesetz {(\<section> 1, Rechtsnorm (Tatbestand []) (Rechtsfolge Erlaubnis))}\<close>
    by eval

  text\<open>Wir können die Maxime für globalen Fortschritt etwas lockern:\<close>
  fun globaler_fortschritt :: "zahlenwelt handlung \<Rightarrow> bool" where
   "globaler_fortschritt (Handlung vor nach) \<longleftrightarrow> (gesamtbesitz vor) \<le> (gesamtbesitz nach)"

  text\<open>Untätigkeit ist nun auch hier erlaubt:\<close>
  lemma\<open>beispiel_case_law_relativ
            (Maxime (\<lambda>ich. globaler_fortschritt))
            (HandlungF (erschaffen 0))
    =
    Gesetz {(\<section> 1, Rechtsnorm (Tatbestand []) (Rechtsfolge Erlaubnis))}\<close>
    by eval

(*TODO: eine Person als handelnde Person in eine Handlungsabsicht
 hardzucoden ist illegal!

eine Person also Opfer hardzucoden muss aber gehen.
HandlungF (stehlen 5 Bob)
sollte eine wohlgeformte Handlungsabsicht sein.
*)
lemma "\<not>wohlgeformte_handlungsabsicht
  zahlenwelt_personen_swap initialwelt
  (HandlungF (\<lambda>ich w. if ich = Alice then w else Zahlenwelt (\<lambda>_. 0)))"
  apply(simp add: initialwelt_def wohlgeformte_handlungsabsicht_def swap_def)
  apply(eval)
  done


lemma "\<not> maxime_und_handlungsabsicht_generalisieren maxime_zahlenfortschritt
        (HandlungF (\<lambda>ich w. if ich = Alice then w else Zahlenwelt (\<lambda>_. 0))) Carol"
  apply(simp add: maxime_zahlenfortschritt_def)
  apply(rule_tac x="Zahlenwelt (\<lambda>_. -1)" in exI, simp)
  apply(rule_tac x="Zahlenwelt (\<lambda>_. 1)" in exI, simp)
  done

thm sum_list_map_eq_sum_count
lemma helper_sum_int_if: "a \<notin> set P \<Longrightarrow>
(\<Sum>x\<in>set P. int (if a = x then A1 x else A2 x) * B x) =
  (\<Sum>x\<in>set P. int (A2 x) * B x)"
  by (smt (verit, del_insts) sum.cong)
lemma sum_list_map_eq_sum_count_int:
  fixes f :: "'a \<Rightarrow> int"
  shows "sum_list (map f xs) = sum (\<lambda>x. (int (count_list xs x)) * f x) (set xs)"
proof(induction xs)
  case (Cons x xs)
  show ?case (is "?l = ?r")
  proof cases
    assume "x \<in> set xs"
    have XXX: "(\<Sum>xa\<in>set xs - {x}. int (if x = xa then count_list xs xa + 1 else count_list xs xa) * f xa)
  = (\<Sum>xa\<in>set xs - {x}. int (count_list xs xa) * f xa)"
      thm helper_sum_int_if
      by (smt (verit, ccfv_SIG) Diff_insert_absorb \<open>x \<in> set xs\<close> mk_disjoint_insert sum.cong) 
    have "?l = f x + (\<Sum>x\<in>set xs. (int (count_list xs x)) * f x)" by (simp add: Cons.IH)
    also have "set xs = insert x (set xs - {x})" using \<open>x \<in> set xs\<close>by blast
    also have "f x + (\<Sum>x\<in>insert x (set xs - {x}). (int (count_list xs x)) * f x) = ?r"
      apply(simp add: sum.insert_remove XXX)
      by (simp add: mult.commute ring_class.ring_distribs(1))
    finally show ?thesis .
  next
    assume "x \<notin> set xs"
    hence "\<And>xa. xa \<in> set xs \<Longrightarrow> x \<noteq> xa" by blast
    thus ?thesis by (simp add: Cons.IH \<open>x \<notin> set xs\<close>)
  qed
qed simp



  thm sum.remove
lemma sum_swap_a: "finite P \<Longrightarrow> a \<notin> P \<Longrightarrow> b \<in> P \<Longrightarrow> sum (swap a b f) P = f a + sum f (P - {b})"
  apply(subst sum.remove[of P b])
  by(simp_all add: swap_b sum_swap_none)
  
  
lemma count_list_distinct: "distinct P \<Longrightarrow> x \<in> set P \<Longrightarrow> count_list P x = 1"
  apply(induction P)
   apply(simp; fail)
  by(auto)
lemma sum_list_swap: "p1 \<in> set P \<Longrightarrow> p2 \<in> set P \<Longrightarrow> distinct P \<Longrightarrow>
        sum_list (map (swap p1 p2 f) P) = sum_list (map (f::'a\<Rightarrow>int) P)"
  apply(simp add: sum_list_map_eq_sum_count_int)
  apply(simp add: count_list_distinct)
  thm sum.cong
  apply(induction P arbitrary: p1 p2)
   apply(simp)
  apply(simp)
  apply(elim disjE)
     apply(simp_all)
    apply(simp add: swap_a sum_swap_a sum.remove[symmetric]; fail)
   apply(simp add: swap_symmetric swap_a sum_swap_a sum.remove[symmetric]; fail)
  apply(rule swap_nothing)
  by auto
  
lemma gesamtbesitz_swap:
  "gesamtbesitz (zahlenwelt_personen_swap p1 p2 welt) = gesamtbesitz welt"
  apply(cases welt, simp)
  apply(rule sum_list_swap)
  using enum_class.in_enum enum_class.enum_distinct by auto


lemma "kategorischer_imperativ zahlenwelt_personen_swap (Zahlenwelt besitz)
        (Maxime (\<lambda>ich::person. globaler_fortschritt))"
  apply(simp add: moralisch_simp)
  apply(simp add: wohlgeformte_handlungsabsicht_def)
  apply(intro allI impI, elim conjE exE)
  apply(case_tac h, rename_tac h p1 p2 ha, simp)

  apply(erule_tac x=p1 in allE)
  apply(erule_tac x=p2 in allE)
  apply(simp)
  apply(simp add: gesamtbesitz_swap)
  apply(erule_tac x="Zahlenwelt besitz" in allE)
  apply(erule_tac x="Zahlenwelt (swap p1 p2 besitz)" in allE)
  thm gesamtbesitz_swap[where welt="Zahlenwelt besitz", simplified]
  apply(simp)
  apply(simp add: gesamtbesitz_swap[where welt="Zahlenwelt besitz", simplified])
  done

lemma vorher_handeln[simp]: "vorher (handeln p welt h) = welt"
  by(cases h, simp)
lemma nachher_handeln: "nachher (handeln p welt (HandlungF h)) = h p welt"
  by(simp)

(*hmm, this does not pull polymorphism into HOL*)
lemma\<open>{h::'p\<Rightarrow>int\<Rightarrow>int. \<exists>h'::'p'\<Rightarrow>int\<Rightarrow>int. \<exists>translate::'p'\<Rightarrow>'p. \<forall>p. h' p = h (translate p)}
        = {h::'p\<Rightarrow>int\<Rightarrow>int. True}\<close>
  apply(rule Collect_eqI)
  apply(simp)
  apply(rule_tac x="(\<lambda>p' i. x (t p') i)" in exI)
  by fastforce
  
  

lemma "set P = UNIV \<Longrightarrow>
       sum_list (map welt P) \<le> sum_list (map (x p welt) P) \<Longrightarrow>
       sum_list (map welt P) \<le> sum_list (map (x p2 welt) P)"
  (*darf nicht gelten, weil es instanziierungen gaebe, fuer die das definitif falsch ware.*)
  oops


  text\<open>Allerdings ist auch Stehlen erlaubt, da global gesehen, kein Besitz vernichtet wird:\<close>
  lemma\<open>beispiel_case_law_relativ
          (Maxime (\<lambda>ich. globaler_fortschritt))
          (HandlungF (stehlen 5 Bob))
    =
    Gesetz
    {(\<section> 1, Rechtsnorm (Tatbestand [Gewinnt Alice 5, Verliert Bob 5]) (Rechtsfolge Erlaubnis))}\<close>
    by eval

subsection\<open>Alice stiehlt 5\<close>
  text\<open>Zurück zur einfachen \<^const>\<open>maxime_zahlenfortschritt\<close>.\<close>
  
  text\<open>Stehlen ist verboten:\<close>
  lemma \<open>beispiel_case_law_relativ maxime_zahlenfortschritt (HandlungF (stehlen 5 Bob)) =
    Gesetz
    {(\<section> 1, Rechtsnorm (Tatbestand [Gewinnt Alice 5, Verliert Bob 5]) (Rechtsfolge Verbot))}\<close>
    by eval

  text\<open>In kein Welt ist Stehlen \<^const>\<open>moralisch\<close>:\<close>
  lemma "\<not> moralisch welt maxime_zahlenfortschritt (HandlungF (stehlen 5 Bob))"
    apply(cases welt)
    by(auto simp add: maxime_zahlenfortschritt_def moralisch_simp)
  
  text\<open>Auch wenn \<^const>\<open>Alice\<close> von sich selbst stehlen möchte ist dies verboten,
  obwohl hier keiner etwas verliert:\<close>
  lemma \<open>beispiel_case_law_relativ maxime_zahlenfortschritt (HandlungF (stehlen 5 Alice)) =
    Gesetz {(\<section> 1, Rechtsnorm (Tatbestand []) (Rechtsfolge Verbot))}\<close>
    by eval
  
  text\<open>Der Grund ist, dass \<^const>\<open>Alice\<close> die abstrakte Handlung "Alice wird bestohlen" gar nicht gut
  fände, wenn sie jemand anderes ausführt:\<close>
  lemma \<open>debug_maxime show_zahlenwelt initialwelt
          maxime_zahlenfortschritt (HandlungF (stehlen 5 Alice)) =
   {VerletzteMaxime (Opfer Alice) (Taeter Bob)
     (Handlung [(Alice, 5), (Bob, 10), (Carol, - 3)] [(Bob, 15), (Carol, - 3)]),
    VerletzteMaxime (Opfer Alice) (Taeter Carol)
     (Handlung [(Alice, 5), (Bob, 10), (Carol, - 3)] [(Bob, 10), (Carol, 2)]),
    VerletzteMaxime (Opfer Alice) (Taeter Eve)
     (Handlung [(Alice, 5), (Bob, 10), (Carol, - 3)] [(Bob, 10), (Carol, - 3), (Eve, 5)])
   }\<close>
    by eval
  
  text\<open>Leider ist das hier abgeleitete Gesetz sehr fragwürdig:
  \<^term>\<open>Rechtsnorm (Tatbestand []) (Rechtsfolge Verbot)\<close>
  
  Es besagt, dass Nichtstun verboten ist.\<close>

  text\<open>Indem wir die beiden Handlungen Nichtstun und Selbstbestehlen betrachten,
  können wir sogar ein widersprüchliches Gesetz ableiten:\<close>
  lemma \<open>simulateOne
      (SimConsts
        Alice
        maxime_zahlenfortschritt
        (case_law_ableiten_relativ delta_zahlenwelt))
      20 (HandlungF (stehlen 5 Alice)) initialwelt
      (beispiel_case_law_relativ maxime_zahlenfortschritt (HandlungF (erschaffen 0)))
    =
    Gesetz
  {(\<section> 2, Rechtsnorm (Tatbestand []) (Rechtsfolge Verbot)),
   (\<section> 1, Rechtsnorm (Tatbestand []) (Rechtsfolge Erlaubnis))}\<close>
    by eval

  text\<open>Meine persönliche Conclusion: Wir müssen irgendwie die Absicht mit ins Gesetz schreiben.\<close>

subsection\<open>Schenken\<close>
  text\<open>Es ist \<^const>\<open>Alice\<close> verboten, etwas zu verschenken:\<close>
  lemma\<open>beispiel_case_law_relativ maxime_zahlenfortschritt (HandlungF (schenken 5 Bob))
    =
    Gesetz
      {(\<section> 1,
        Rechtsnorm (Tatbestand [Verliert Alice 5, Gewinnt Bob 5]) (Rechtsfolge Verbot))}\<close>
    by eval
  text\<open>Der Grund ist, dass \<^const>\<open>Alice\<close> dabei etwas verliert und
  die \<^const>\<open>maxime_zahlenfortschritt\<close> dies nicht Erlaubt.
  Es fehlt eine Möglichkeit zu modellieren, dass \<^const>\<open>Alice\<close> damit einverstanden ist,
  etwas abzugeben.
  Doch wir haben bereits in @{thm stehlen_ist_schenken} gesehen,
  dass \<^const>\<open>stehlen\<close> und \<^const>\<open>schenken\<close> nicht unterscheidbar sind.\<close>

(*TODO: kategorischen Imperativ aendern, so dass allgemeines gesetz ableiten eine
handlungF anstatt einer handlung nimmt.
Evtl in neue Datei, damit sich dieses Beipsiel noch gut liesst.*)

subsection\<open>Ungültige Maxime\<close>
  text\<open>Es ist verboten, in einer Maxime eine spezielle Person hardzucoden.
  Da dies gegen die Gleichbehandlung aller Menschen verstoßen würde.
  
  Beispielsweise könnten wir \<^const>\<open>individueller_fortschritt\<close> nicht mehr parametrisiert verwenden,
  sondern einfach \<^const>\<open>Alice\<close> reinschreiben:
  \<close>
  lemma "individueller_fortschritt Alice
    = (\<lambda>h. case h of Handlung vor nach \<Rightarrow> (meins Alice vor) \<le> (meins Alice nach))"
    apply(simp add: fun_eq_iff)
    apply(intro allI, rename_tac h, case_tac h)
    apply(simp)
    done
  text\<open>Dies würde es erlauben, dass \<^const>\<open>Alice\<close> Leute bestehlen darf:\<close>
  lemma\<open>beispiel_case_law_relativ
            (Maxime (\<lambda>ich. individueller_fortschritt Alice))
            (HandlungF (stehlen 5 Bob))
    =
    Gesetz
    {(\<section> 1, Rechtsnorm (Tatbestand [Gewinnt Alice 5, Verliert Bob 5]) (Rechtsfolge Erlaubnis))}\<close>
    by eval

end
(*<*)
theory Aenderung
imports Main ExecutableHelper BeispielPerson Handlung Zahlenwelt
begin

section\<open>Änderungen in Welten\<close>

datatype ('person, 'etwas) aenderung = Verliert \<open>'person\<close> \<open>'etwas\<close> | Gewinnt \<open>'person\<close> \<open>'etwas\<close>

text\<open>The delta to get from \<^term>\<open>i2\<close> to \<^term>\<open>i2\<close>\<close>
definition delta_num
  :: \<open>'person \<Rightarrow> 'etwas::{ord,minus} \<Rightarrow> 'etwas \<Rightarrow> (('person, 'etwas) aenderung) option\<close>
  where
    \<open>delta_num p i1 i2 = (
           if i1 > i2 then Some (Verliert p (i1 - i2))
      else if i1 < i2 then Some (Gewinnt p (i2 - i1))
      else None
  )\<close>

lemma \<open>delta_num p i1 i2 = Some (Gewinnt p (i::int)) \<Longrightarrow> i > 0\<close>
  by(auto simp add: delta_num_def split_ifs)
lemma \<open>delta_num p i1 i2 = Some (Verliert p (i::int)) \<Longrightarrow> i > 0\<close>
  by(auto simp add: delta_num_def split_ifs)
lemma \<open>delta_num p1 i1 i2 = Some (Gewinnt p2 (i::int)) \<Longrightarrow> p1 = p2\<close>
  by(auto simp add: delta_num_def split_ifs)
lemma \<open>delta_num p1 i1 i2 = Some (Verliert p2 (i::int)) \<Longrightarrow> p1 = p2\<close>
  by(auto simp add: delta_num_def split_ifs)


lemma \<open>delta_num Alice (2::int) 6 = Some (Gewinnt Alice 4)\<close> by eval
lemma \<open>delta_num Alice (-2::int) 6 = Some (Gewinnt Alice 8)\<close> by eval


lemma delta_num_same: "delta_num p (a::'a::ordered_ab_group_add) a = None"
  by(simp add: delta_num_def)

text\<open>The absolute delta between \<^term>\<open>i1\<close> and \<^term>\<open>i2\<close>.
This basically merges the two terms.\<close>
definition sum_delta_num
  :: \<open>'person \<Rightarrow> 'etwas::{ord,zero,plus,uminus,minus} \<Rightarrow> 'etwas \<Rightarrow> (('person, 'etwas) aenderung) option\<close>
  where
    \<open>sum_delta_num p i1 i2 = (
      let s = i1 + i2 in
           if s < 0 then Some (Verliert p (-s))
      else if s > 0 then Some (Gewinnt p s)
      else None
  )\<close>

lemma \<open>sum_delta_num Alice (2::int) 6 = Some (Gewinnt Alice 8)\<close> by eval
lemma \<open>sum_delta_num Alice (-2::int) 6 = Some (Gewinnt Alice 4)\<close> by eval

lemma sum_delta_num_delta_num:
  fixes i1::"'a::ordered_ab_group_add"
  shows "sum_delta_num p i1 i2 = delta_num p 0 (i1+i2)"
  by(simp add: sum_delta_num_def delta_num_def Let_def)

lemma  delta_num_sum_delta_num:
  fixes i1::"'a::ordered_ab_group_add"
  shows "delta_num p i1 i2 = sum_delta_num p (-i1) i2"
  by(simp add: sum_delta_num_def delta_num_def Let_def)


text\<open>Deltas, d.h. Unterschiede Zwischen Welten.

Man könnte eine class Delta world einführen, mit einer delta-Funtion
  :: welt -> welt -> [Aenderung person etwas]
Diese Klasse würde dann Welten mit Personen und Etwas in Relation setzen.
Dafür bräuchte es MultiParamTypeClasses. Eine simple Funktion ist da einfacher.\<close>
type_synonym ('world, 'person, 'etwas) delta =
    \<open>'world handlung \<Rightarrow> (('person, 'etwas) aenderung) list\<close>

definition betroffen :: "('person, 'etwas) aenderung \<Rightarrow> 'person"
  where
"betroffen a \<equiv> case a of Verliert p _ \<Rightarrow> p | Gewinnt p _ \<Rightarrow> p"

definition betroffene :: "('person, 'etwas) aenderung list \<Rightarrow> 'person list"
  where
"betroffene as \<equiv> map betroffen as"


lemma betroffene_case_aenderung:
  "betroffene = map (case_aenderung (\<lambda>p _. p) (\<lambda>p _. p))"
  by(simp add: fun_eq_iff betroffene_def betroffen_def)

lemma "betroffene [Verliert Alice (2::int), Gewinnt Bob 3, Gewinnt Carol 2, Verliert Eve 1]
  = [Alice, Bob, Carol, Eve]" by eval
lemma "betroffene [Verliert Alice (5::nat), Gewinnt Bob 3, Verliert Eve 7]
  = [Alice, Bob, Eve]" by eval
lemma "betroffene [Verliert Alice (5::nat), Gewinnt Alice 3]
  = [Alice, Alice]" by eval


definition aenderung_val :: "('person, ('etwas::uminus)) aenderung \<Rightarrow> 'etwas"
  where
"aenderung_val a \<equiv> case a of Verliert _ n \<Rightarrow> -n | Gewinnt _ n \<Rightarrow> n"

lemma "aenderung_val (Verliert Alice (2::int)) = -2" by eval
lemma "aenderung_val (Gewinnt Alice (2::int)) = 2" by eval

lemma betroffen_simps[simp]:
  "betroffen (Gewinnt a ab) = a"
  "betroffen (Verliert a ab) = a"
  by(simp add: betroffen_def)+
lemma aenderung_val_simps[simp]:
  "aenderung_val (Gewinnt a ab) = ab"
  "aenderung_val (Verliert a ab) = -ab"
  by(simp add: aenderung_val_def)+

fun delta_num_map
  :: \<open>(('person::enum \<rightharpoonup> ('etwas::{zero,minus,ord})), 'person, 'etwas) delta\<close>
  where
  \<open>delta_num_map (Handlung vor nach) =
      List.map_filter
        (\<lambda>p. case (the_default (vor p) 0, the_default (nach p) 0)
               of (a,b) \<Rightarrow> delta_num p a b)
        (Enum.enum::'person list)\<close>

lemma\<open>delta_num_map
  (Handlung [Alice \<mapsto> 5::int, Bob \<mapsto> 10, Eve \<mapsto> 1]
            [Alice \<mapsto> 3, Bob \<mapsto> 13, Carol \<mapsto> 2])
  = [Verliert Alice 2, Gewinnt Bob 3, Gewinnt Carol 2, Verliert Eve 1]\<close> by eval

fun delta_num_fun
  :: \<open>(('person::enum \<Rightarrow> ('etwas::{minus,ord})), 'person, 'etwas) delta\<close>
  where
  \<open>delta_num_fun (Handlung vor nach) =
      List.map_filter (\<lambda>p. delta_num p (vor p) (nach p)) Enum.enum\<close>

lemma \<open>delta_num_fun
    (Handlung
        ((\<lambda>p. 0::int)(Alice:=8, Bob:=12, Eve:=7))
        ((\<lambda>p. 0::int)(Alice:=3, Bob:=15, Eve:=0)))
  = [Verliert Alice 5, Gewinnt Bob 3, Verliert Eve 7]\<close> by eval

lemma delta_num_map: \<open>delta_num_map (Handlung m1 m2) =
        delta_num_fun (Handlung (\<lambda>p. the_default (m1 p) 0) (\<lambda>p. the_default (m2 p) 0))\<close>
  by(simp)


(*TODO: das if will in die swap.thy?*)
term map_aenderung
definition aenderung_swap
  :: "'person \<Rightarrow> 'person \<Rightarrow> ('person, 'etwas) aenderung \<Rightarrow> ('person, 'etwas) aenderung"
where
  "aenderung_swap p1 p2 a \<equiv> map_aenderung (\<lambda>p. if p = p1 then p2 else if p = p2 then p1 else p) id a"

lemma\<open>aenderung_swap Alice Bob (Gewinnt Alice (3::nat)) = Gewinnt Bob 3\<close> by eval
lemma\<open>aenderung_swap Alice Bob (Gewinnt Bob (3::nat)) = Gewinnt Alice 3\<close> by eval
lemma\<open>aenderung_swap Alice Bob (Gewinnt Carol (3::nat)) = Gewinnt Carol 3\<close> by eval


lemma aenderung_swap_id: "aenderung_swap p1 p2 (aenderung_swap p1 p2 a) = a"
  apply(simp add: aenderung_swap_def)
  apply(cases a)
  by simp_all

lemma aenderung_swap_sym: "aenderung_swap p1 p2 = aenderung_swap p2 p1"
  apply(simp add: fun_eq_iff aenderung_swap_def, intro allI, rename_tac a)
  apply(case_tac a)
  by simp_all

lemma map_map_aenderung_swap:
  "map (map (aenderung_swap p1 p2)) \<circ> (map (map (aenderung_swap p1 p2)) \<circ> kons) = kons"
  by(simp add: fun_eq_iff aenderung_swap_id comp_def)

lemma swap_map_map_aenderung_swap:
  "swap p2 p1 (map (map (aenderung_swap p2 p1)) \<circ> swap p1 p2 (map (map (aenderung_swap p1 p2)) \<circ> kons))
  = kons"
  apply(subst aenderung_swap_sym)
  apply(subst swap_symmetric)
  apply(subst swap_fun_comp_id)
  apply(simp add: map_map_aenderung_swap)
  done




fun aenderung_ausfuehren
  :: "('person, 'etwas::{plus,minus}) aenderung list \<Rightarrow> ('person \<Rightarrow> 'etwas) \<Rightarrow> ('person \<Rightarrow> 'etwas)"
where
  "aenderung_ausfuehren [] bes = bes"
| "aenderung_ausfuehren (Verliert p n # deltas) bes = aenderung_ausfuehren deltas \<lbrakk>bes(p -= n)\<rbrakk>"
| "aenderung_ausfuehren (Gewinnt p n # deltas) bes = aenderung_ausfuehren deltas \<lbrakk>bes(p += n)\<rbrakk>"

lemma
\<open>aenderung_ausfuehren
  [Verliert Alice (2::int), Gewinnt Bob 3, Gewinnt Carol 2, Verliert Eve 1]
  (\<^url>[Alice:=8, Bob:=3, Eve:= 5])
  =
  (\<^url>[Alice:=6, Bob:=6, Carol:=2, Eve:= 4])\<close>
  by eval

lemma
\<open>aenderung_ausfuehren
  [Verliert Alice (2::int), Verliert Alice 6]
  (\<^url>[Alice:=8, Bob:=3, Eve:= 5])
  =
  (\<^url>[Bob:=3, Eve:= 5])\<close>
  by eval


(*TODO: upstream und vereinfachen!*)
lemma swap_aenderung_ausfuehren:
  "swap p1 p2 (Aenderung.aenderung_ausfuehren a bes)
      = Aenderung.aenderung_ausfuehren (map (aenderung_swap p1 p2) a) (swap p1 p2 bes)"
  apply(induction a arbitrary: bes)
   apply(simp)
  apply(simp)
  apply(case_tac a1)
  subgoal
    apply(simp)
    apply(simp add: aenderung_swap_def, safe)
      apply (simp_all add: fun_upd_twist swap_def)
    done
  apply(simp)
    apply(simp add: aenderung_swap_def, safe)
    apply (simp_all add: fun_upd_twist swap_def)
  done


(*TODO: Achtung, das macht unfug wenn p1 und p2 unterschiedlich*)
definition aenderung_merge_same_person
  :: "('person, 'etwas::{ord,zero,plus,minus,uminus}) aenderung \<Rightarrow> ('person, 'etwas) aenderung
      \<Rightarrow> ('person, 'etwas) aenderung option"
where
  "aenderung_merge_same_person a1 a2 =
   (if betroffen a1 \<noteq> betroffen a2
    then undefined
    else sum_delta_num (betroffen a1) (aenderung_val a1) (aenderung_val a2))"
(*TODO: test!*)


lemma \<open>aenderung_merge_same_person (Verliert Alice (2::int)) (Gewinnt Alice 6) = Some (Gewinnt Alice 4)\<close>
  by eval

lemma aenderung_merge_same_person_commute:
  fixes a::"('person, 'a::ordered_ab_group_add) aenderung"
  shows "betroffen a = betroffen b \<Longrightarrow> aenderung_merge_same_person a b = aenderung_merge_same_person b a"
  apply(cases a, case_tac [!] b)
  by(simp_all add: aenderung_merge_same_person_def sum_delta_num_def Let_def add.commute)


fun aenderung_aenderung_map
  :: "('person, 'etwas::{ord,zero,plus,minus,uminus}) aenderung list \<Rightarrow> ('person \<rightharpoonup> ('person, 'etwas) aenderung)"
where
  "aenderung_aenderung_map [] = Map.empty"
| "aenderung_aenderung_map (delta # deltas) = 
   (case (aenderung_aenderung_map deltas) (betroffen delta)
      of None \<Rightarrow> (aenderung_aenderung_map deltas)((betroffen delta) \<mapsto> delta)
       | Some delta2 \<Rightarrow> (aenderung_aenderung_map deltas)((betroffen delta) := aenderung_merge_same_person delta2 delta)
   )"

lemma \<open>aenderung_aenderung_map [Verliert Alice (2::int), Verliert Alice 6]
  = [Alice \<mapsto> Verliert Alice 8]\<close>
  by eval

lemma \<open>aenderung_aenderung_map [Verliert Alice (2::int), Gewinnt Bob 3, Gewinnt Carol 2, Verliert Eve 1]
  = [Alice \<mapsto> Verliert Alice 2, Bob \<mapsto> Gewinnt Bob 3, Carol \<mapsto> Gewinnt Carol 2, Eve \<mapsto> Verliert Eve 1]\<close>
  by eval


lemma \<open>aenderung_aenderung_map [Verliert Alice (2::int), Gewinnt Alice 6]
  = [Alice \<mapsto> Gewinnt Alice 4]\<close>
  by eval


text\<open>Eine \<^typ>\<open>('person, 'etwas) aenderung list\<close> in eine \<^typ>\<open>('person, 'etwas) aenderung set\<close>
zu übersetzen ist nicht trivial, da Die Liste mehrere Änderungen der gleichen Person
enthalten kann, welche gemerged werden müssen.\<close>
definition aenderung_list_to_set
  :: "('person::enum, 'etwas::{ord,zero,plus,minus,uminus}) aenderung list \<Rightarrow> ('person, 'etwas) aenderung set"
  where
"aenderung_list_to_set as \<equiv> set (List.map_filter (aenderung_aenderung_map as) Enum.enum)"

lemma "aenderung_list_to_set as = ran (aenderung_aenderung_map as)"
  apply(simp add: aenderung_list_to_set_def)
  (*TODO!*)
  oops
lemma "aenderung_list_to_set 
  [Verliert Alice (2::int), Gewinnt Bob 3, Gewinnt Eve 3, Gewinnt Alice 2, Gewinnt Carol 2, Verliert Eve 1]
= {Gewinnt Bob 3, Gewinnt Carol 2, Gewinnt Eve 2}"
  by eval



(*
eigentlich hatte ich
type_synonym  ('person, 'etwas) abmachung = "('person, 'etwas) aenderung list
was viel schoner aussieht.
Aber Leider dann Abmachungen nicht Eindeutig sind, was sehr doof ist.

TODO: erklaeren
TODO: upstream
*)

(*TODO:
eventuell laesst sich
  ('person, 'etwas) aenderung list
deutlich besser als
  ('person \<rightharpoonup> 'etwas::uminus
darstellen, weil das viel eindeutiger ist.*)

(*

TODO
TODO
TODO
TODO


Maps sind leider auch nicht eindeutig, weil None und 0 die gleiche Semantik haben.
Ich muss auf 'person \<Rightarrow> 'etwas::ordered_ab_group_add wechseln!


TODO
TODO
TODO
*)

type_synonym  ('person, 'etwas) abmachung = "'person \<rightharpoonup> 'etwas"

(*TODO: dedup mit aenderung_aenderung_map*)
fun aenderung_map
  :: "('person, 'etwas::{ord,zero,plus,minus,uminus}) aenderung list \<Rightarrow> ('person, 'etwas) abmachung"
where
  "aenderung_map [] = Map.empty"
| "aenderung_map (delta # deltas) = 
   (case (aenderung_map deltas) (betroffen delta)
      of None \<Rightarrow> (aenderung_map deltas)((betroffen delta) \<mapsto> aenderung_val delta)
       | Some delta2 \<Rightarrow> (aenderung_map deltas)((betroffen delta) \<mapsto> (aenderung_val delta) + delta2)
   )"
(*TODO: 0 noch durch None ersetzen.*)

lemma aenderung_map_simp_cons:
"aenderung_map (delta # deltas)
  = (aenderung_map deltas)(
      (betroffen delta) \<mapsto>
        (case (aenderung_map deltas) (betroffen delta) of None \<Rightarrow> aenderung_val delta
                                                        | Some delta2 \<Rightarrow> (aenderung_val delta) + delta2)
    )"
  by (simp add: option.case_eq_if)

declare aenderung_map.simps(2)[simp del]

lemma aenderung_map_simp_call:
  "aenderung_map (delta # deltas) p =
    (if p = betroffen delta
     then (case (aenderung_map deltas p) of None \<Rightarrow> Some (aenderung_val delta)
                                          | Some delta2 \<Rightarrow> Some ((aenderung_val delta) + delta2))
     else (aenderung_map deltas p))"
  apply(simp add: aenderung_map_simp_cons)
  by(simp split: option.split)


lemma\<open>[aenderung_map [Gewinnt Alice (3::int)], aenderung_map [Gewinnt Alice 3, Verliert Bob 3]]
= [[Alice \<mapsto> 3], [Alice \<mapsto> 3, Bob \<mapsto> -3]]\<close> by eval


fun abmachung_to_aenderung_list
  :: "'person list \<Rightarrow> ('person, 'etwas::{ord,zero,plus,minus,uminus}) abmachung \<Rightarrow> ('person, 'etwas) aenderung list"
where
  "abmachung_to_aenderung_list [] _ = []"
| "abmachung_to_aenderung_list (p#ps) a =
    (case a p of None \<Rightarrow> abmachung_to_aenderung_list ps a
               | Some i \<Rightarrow> (if i > 0 then Gewinnt p i else Verliert p (- i)) # abmachung_to_aenderung_list ps a
    )"

definition abmachung_to_aenderung
  :: "('person::enum, 'etwas::{ord,zero,plus,minus,uminus}) abmachung \<Rightarrow> ('person, 'etwas) aenderung list"
where
  "abmachung_to_aenderung \<equiv> abmachung_to_aenderung_list Enum.enum"

lemma \<open>abmachung_to_aenderung [Alice \<mapsto> (3::int), Bob \<mapsto> -3] = [Gewinnt Alice 3, Verliert Bob 3]\<close> by eval



definition aenderung_to_abmachung
  :: "('person, 'etwas) aenderung list \<Rightarrow> ('person::enum, 'etwas::{ord,zero,plus,minus,uminus}) abmachung"
where
  "aenderung_to_abmachung \<equiv> aenderung_map"


lemma fixes as :: "('person::enum, int) aenderung list"
  shows "abmachung_to_aenderung (aenderung_to_abmachung as) = as"
  (* nitpick as = [Verliert person\<^sub>1 (- 1)] *)
  oops (*gilt nicht, weil aenderungen nicht eindeutig*)


lemma abmachung_to_aenderung_list_aenderung_map_not_in_ps:
  "p \<notin> set ps \<Longrightarrow>  aenderung_map (abmachung_to_aenderung_list ps a) p = None"
  apply(induction ps)
   apply(simp)
  apply(simp)
  by (simp add: aenderung_map_simp_call option.case_eq_if)

lemma abmachung_to_aenderung_list_not_in_ps:
  "p \<notin> set ps \<Longrightarrow>
       abmachung_to_aenderung_list ps (a(p := v)) = abmachung_to_aenderung_list ps a"
  apply(induction ps)
   apply(simp)
  apply(simp)
  apply (safe)
  apply(simp split: option.split)
  done

lemma aenderung_map_abmachung_to_aenderung_list_induct_helper:
  fixes a :: "('person::enum, 'etwas::ordered_ab_group_add) abmachung"
  shows "dom a \<subseteq> set ps \<Longrightarrow> distinct ps \<Longrightarrow> aenderung_map (abmachung_to_aenderung_list ps a) = a"
  apply(induction ps arbitrary: a)
   apply(simp)
  apply(rename_tac p ps a)
  apply(simp)
  apply(case_tac "a p")
   apply(simp)
   apply (simp add: domIff subset_insert; fail)
  apply(simp)
  apply(simp add: aenderung_map_simp_cons)
  apply(case_tac "p \<notin> dom a")
   apply(subgoal_tac "dom a \<subseteq> set ps")
    apply blast
   apply blast
  apply(simp)
  apply(simp add: abmachung_to_aenderung_list_aenderung_map_not_in_ps)
  apply(subgoal_tac "dom (a(p := None)) \<subseteq> set ps")
   prefer 2
   subgoal by auto[1]
  apply(subgoal_tac "aenderung_map (abmachung_to_aenderung_list ps (a)) = (a(p := None))")
   prefer 2
   using abmachung_to_aenderung_list_not_in_ps apply metis
   apply(simp)
   by fastforce
  

lemma aenderung_to_abmachung_abmachung_to_aenderung:
  fixes a :: "('person::enum, 'etwas::ordered_ab_group_add) abmachung"
  shows "aenderung_to_abmachung (abmachung_to_aenderung a) = a"
  apply(simp add: abmachung_to_aenderung_def aenderung_to_abmachung_def)
  apply(rule aenderung_map_abmachung_to_aenderung_list_induct_helper)
   apply(simp add: enum_class.enum_UNIV)
  apply(simp add: enum_class.enum_distinct)
  done


definition abmachung_ausfuehren
  :: "('person, 'etwas::{plus,minus}) abmachung \<Rightarrow> ('person \<Rightarrow> 'etwas) \<Rightarrow> ('person \<Rightarrow> 'etwas)"
where
  "abmachung_ausfuehren a besitz \<equiv>
      \<lambda>p. case a p of None \<Rightarrow> besitz p
                    | Some b' \<Rightarrow> (besitz p) + b'"


lemma aenderung_ausfuehren_abmachung_to_aenderung_induction_helper:
  fixes welt :: "'person::enum \<Rightarrow> 'etwas::ordered_ab_group_add"
  shows "dom abmachung \<subseteq> set ps \<Longrightarrow> distinct ps \<Longrightarrow> 
          aenderung_ausfuehren (abmachung_to_aenderung_list ps abmachung) welt p =
    welt p + (case abmachung p of None \<Rightarrow> 0 | Some d \<Rightarrow> d)"
  apply(induction ps arbitrary: abmachung welt)
   apply(simp; fail)
  apply(simp)
  apply(rename_tac pa ps abmachung welt)
  apply(case_tac "abmachung pa")
   apply(simp)
   apply (simp add: domIff subset_insert; fail)
  apply(simp)
  apply(subgoal_tac "dom (abmachung(pa := None)) \<subseteq> set ps")
   prefer 2
  subgoal by auto[1]
  apply(subgoal_tac "aenderung_ausfuehren (abmachung_to_aenderung_list ps (abmachung(pa := None))) welt p =
           welt p + (case (abmachung(pa := None)) p of None \<Rightarrow> 0 | Some d \<Rightarrow> d)")
   prefer 2   apply blast
  by (smt (verit) abmachung_to_aenderung_list_not_in_ps add.right_neutral fun_upd_other fun_upd_same option.simps(4) option.simps(5))



lemma aenderung_ausfuehren_abmachung_to_aenderung:
  fixes welt :: "'person::enum \<Rightarrow> 'etwas::ordered_ab_group_add"
  shows "aenderung_ausfuehren (abmachung_to_aenderung abmachung) welt p = 
    welt p + (case abmachung p of None \<Rightarrow> 0 | Some d \<Rightarrow> d)"
  apply(simp add: abmachung_to_aenderung_def)
  apply(rule aenderung_ausfuehren_abmachung_to_aenderung_induction_helper)
   apply(simp add: enum_class.enum_UNIV)
  apply(simp add: enum_class.enum_distinct)
  done

lemma fixes welt :: "'person::enum \<Rightarrow> int" (*TODO: ordered_ab_group_add*)
  shows "abmachung_ausfuehren abmachung welt = aenderung_ausfuehren (abmachung_to_aenderung abmachung) welt"
  apply(simp add: abmachung_ausfuehren_def fun_eq_iff)
  apply(intro allI, rename_tac p)
  apply(case_tac "abmachung p")
   apply(simp)
  
  oops
(*TODO!*)

end
(*>*)
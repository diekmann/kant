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






fun aenderung_ausfuehren
  :: "('person, 'etwas::{plus,minus}) aenderung list \<Rightarrow> ('person \<Rightarrow> 'etwas) \<Rightarrow> ('person \<Rightarrow> 'etwas)"
where
  "aenderung_ausfuehren [] bes = bes"
| "aenderung_ausfuehren (Verliert p n # deltas) bes = aenderung_ausfuehren deltas (bes(p -= n))"
| "aenderung_ausfuehren (Gewinnt p n # deltas) bes = aenderung_ausfuehren deltas (bes(p += n))"

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


fun aenderung_map
  :: "('person, 'etwas::{ord,zero,plus,minus,uminus}) aenderung list \<Rightarrow> ('person \<rightharpoonup> ('person, 'etwas) aenderung)"
where
  "aenderung_map [] = Map.empty"
| "aenderung_map (delta # deltas) = 
   (case (aenderung_map deltas) (betroffen delta)
      of None \<Rightarrow> (aenderung_map deltas)((betroffen delta) \<mapsto> delta)
       | Some delta2 \<Rightarrow> (aenderung_map deltas)((betroffen delta) := aenderung_merge_same_person delta2 delta)
   )"

lemma \<open>aenderung_map [Verliert Alice (2::int), Verliert Alice 6]
  = [Alice \<mapsto> Verliert Alice 8]\<close>
  by eval

lemma \<open>aenderung_map [Verliert Alice (2::int), Gewinnt Bob 3, Gewinnt Carol 2, Verliert Eve 1]
  = [Alice \<mapsto> Verliert Alice 2, Bob \<mapsto> Gewinnt Bob 3, Carol \<mapsto> Gewinnt Carol 2, Eve \<mapsto> Verliert Eve 1]\<close>
  by eval


lemma \<open>aenderung_map [Verliert Alice (2::int), Gewinnt Alice 6]
  = [Alice \<mapsto> Gewinnt Alice 4]\<close>
  by eval

(*TODO:
eventuell laesst sich
  ('person, 'etwas) aenderung list
deutlich besser als
  ('person \<rightharpoonup> 'etwas::uminus
darstellen, weil das viel eindeutiger ist.*)

text\<open>Eine \<^typ>\<open>('person, 'etwas) aenderung list\<close> in eine \<^typ>\<open>('person, 'etwas) aenderung set\<close>
zu übersetzen ist nicht trivial, da Die Liste mehrere Änderungen der gleichen Person
enthalten kann, welche gemerged werden müssen.\<close>
definition aenderung_list_to_set
  :: "('person::enum, 'etwas::{ord,zero,plus,minus,uminus}) aenderung list \<Rightarrow> ('person, 'etwas) aenderung set"
  where
"aenderung_list_to_set as \<equiv> set (List.map_filter (aenderung_map as) Enum.enum)"

lemma "aenderung_list_to_set as = ran (aenderung_map as)"
  apply(simp add: aenderung_list_to_set_def)
  (*TODO!*)
  oops


lemma "aenderung_list_to_set 
  [Verliert Alice (2::int), Gewinnt Bob 3, Gewinnt Eve 3, Gewinnt Alice 2, Gewinnt Carol 2, Verliert Eve 1]
= {Gewinnt Bob 3, Gewinnt Carol 2, Gewinnt Eve 2}"
  by eval




(*TODO: das if will in die swap.thy?*)
term map_aenderung
definition aenderung_swap
  :: "'person \<Rightarrow> 'person \<Rightarrow> ('person, 'etwas) aenderung \<Rightarrow> ('person, 'etwas) aenderung"
where
  "aenderung_swap p1 p2 a \<equiv> map_aenderung (\<lambda>p. if p = p1 then p2 else if p = p2 then p1 else p) id a"

lemma\<open>aenderung_swap Alice Bob (Gewinnt Alice (3::nat)) = Gewinnt Bob 3\<close> by eval
lemma\<open>aenderung_swap Alice Bob (Gewinnt Bob (3::nat)) = Gewinnt Alice 3\<close> by eval
lemma\<open>aenderung_swap Alice Bob (Gewinnt Carol (3::nat)) = Gewinnt Carol 3\<close> by eval



(*TODO: move*)
lemma aenderung_swap_id: "aenderung_swap p1 p2 (aenderung_swap p1 p2 a) = a"
  apply(simp add: aenderung_swap_def)
  apply(cases a)
  by simp_all

lemma aenderung_swap_sym: "aenderung_swap p1 p2 = aenderung_swap p2 p1"
  apply(simp add: fun_eq_iff aenderung_swap_def, intro allI, rename_tac a)
  apply(case_tac a)
  by simp_all

end
(*>*)
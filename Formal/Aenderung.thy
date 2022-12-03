theory Aenderung
imports Main ExecutableHelper BeispielPerson Handlung Zahlenwelt
begin

section\<open>Änderungen in Welten\<close>

datatype ('person, 'etwas) aenderung = Verliert \<open>'person\<close> \<open>'etwas\<close> | Gewinnt \<open>'person\<close> \<open>'etwas\<close>

text\<open>Beispiel: \<^term>\<open>[Gewinnt Alice 3, Verliert Bob 3]::(person, int) aenderung list\<close>.\<close>

(*<*)
text\<open>Das Delta um von \<^term>\<open>i2\<close> nach \<^term>\<open>i2\<close> zu kommen.\<close>
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

(*>*)

subsection\<open>Deltas\<close>
text\<open>Deltas, d.h. Unterschiede zwischen Welten.\<close>
(*Man könnte eine class Delta world einführen, mit einer delta-Funtion
  :: welt -> welt -> [Aenderung person etwas]
Diese Klasse würde dann Welten mit Personen und Etwas in Relation setzen.
Dafür bräuchte es MultiParamTypeClasses. Eine simple Funktion ist da einfacher.*)
type_synonym ('world, 'person, 'etwas) delta =
    \<open>'world handlung \<Rightarrow> (('person, 'etwas) aenderung) list\<close>

text\<open>Von einer \<^typ>\<open>('person, 'etwas) aenderung\<close> betroffene.\<close>
definition betroffen :: "('person, 'etwas) aenderung \<Rightarrow> 'person"
  where
"betroffen a \<equiv> case a of Verliert p _ \<Rightarrow> p | Gewinnt p _ \<Rightarrow> p"

definition betroffene :: "('person, 'etwas) aenderung list \<Rightarrow> 'person list"
  where
"betroffene as \<equiv> map betroffen as"

(*<*)
lemma betroffene_case_aenderung:
  "betroffene = map (case_aenderung (\<lambda>p _. p) (\<lambda>p _. p))"
  by(simp add: fun_eq_iff betroffene_def betroffen_def)
(*>*)


lemma "betroffene [Verliert Alice (2::int), Gewinnt Bob 3, Gewinnt Carol 2, Verliert Eve 1]
  = [Alice, Bob, Carol, Eve]" by eval
lemma "betroffene [Verliert Alice (5::nat), Gewinnt Bob 3, Verliert Eve 7]
  = [Alice, Bob, Eve]" by eval
lemma "betroffene [Verliert Alice (5::nat), Gewinnt Alice 3]
  = [Alice, Alice]" by eval

(*<*)
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
(*>*)



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

(*<*)
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


fun aenderung_list_to_to_abmachung
  :: "('person, 'etwas::{ord,zero,plus,minus,uminus}) aenderung list \<Rightarrow> ('person \<rightharpoonup> ('person, 'etwas) aenderung)"
where
  "aenderung_list_to_to_abmachung [] = Map.empty"
| "aenderung_list_to_to_abmachung (delta # deltas) = 
   (case (aenderung_list_to_to_abmachung deltas) (betroffen delta)
      of None \<Rightarrow> (aenderung_list_to_to_abmachung deltas)((betroffen delta) \<mapsto> delta)
       | Some delta2 \<Rightarrow> (aenderung_list_to_to_abmachung deltas)((betroffen delta) := aenderung_merge_same_person delta2 delta)
   )"

lemma \<open>aenderung_list_to_to_abmachung [Verliert Alice (2::int), Verliert Alice 6]
  = [Alice \<mapsto> Verliert Alice 8]\<close>
  by eval

lemma \<open>aenderung_list_to_to_abmachung [Verliert Alice (2::int), Gewinnt Bob 3, Gewinnt Carol 2, Verliert Eve 1]
  = [Alice \<mapsto> Verliert Alice 2, Bob \<mapsto> Gewinnt Bob 3, Carol \<mapsto> Gewinnt Carol 2, Eve \<mapsto> Verliert Eve 1]\<close>
  by eval


lemma \<open>aenderung_list_to_to_abmachung [Verliert Alice (2::int), Gewinnt Alice 6]
  = [Alice \<mapsto> Gewinnt Alice 4]\<close>
  by eval


text\<open>Eine \<^typ>\<open>('person, 'etwas) aenderung list\<close> in eine \<^typ>\<open>('person, 'etwas) aenderung set\<close>
zu übersetzen ist nicht trivial, da Die Liste mehrere Änderungen der gleichen Person
enthalten kann, welche gemerged werden müssen.\<close>
definition aenderung_list_to_set
  :: "('person::enum, 'etwas::{ord,zero,plus,minus,uminus}) aenderung list \<Rightarrow> ('person, 'etwas) aenderung set"
  where
"aenderung_list_to_set as \<equiv> set (List.map_filter (aenderung_list_to_to_abmachung as) Enum.enum)"

lemma "aenderung_list_to_set as = ran (aenderung_list_to_to_abmachung as)"
  apply(simp add: aenderung_list_to_set_def)
  (*TODO!*)
  oops
lemma "aenderung_list_to_set 
  [Verliert Alice (2::int), Gewinnt Bob 3, Gewinnt Eve 3, Gewinnt Alice 2, Gewinnt Carol 2, Verliert Eve 1]
= {Gewinnt Bob 3, Gewinnt Carol 2, Gewinnt Eve 2}"
  by eval
(*>*)

subsection\<open>Abmachungen\<close>
text\<open>Eine \<^typ>\<open>('person, 'etwas) aenderung list\<close> wie
z.B. \<^term>\<open>[Gewinnt Alice (3::int), Verliert Bob 3]\<close> ließe sich gut verwenden,
um eine Abmachung zwischen \<^const>\<open>Alice\<close> und \<^const>\<open>Bob\<close> zu modellieren.
Allerdings ist diese Darstellung unpraktisch zu benutzen.
Beispielsweise sind 
\<^term>\<open>[Gewinnt Alice (3::int), Verliert Bob 3]\<close>, \<^term>\<open>[Verliert Bob 3, Gewinnt Alice (3::int)]\<close>,
\<^term>\<open>[Gewinnt Alice (1::int), Gewinnt Alice 1, Gewinnt Alice 1, Verliert Bob 3, Verliert Carol 0]\<close>,
extensional betrachtet alle equivalent.
Es ist praktischer, eine Darstellung zu wählen, in der syntaktische und semantische Äquivalenz
zusammenfallen.
Das bedeutet, eine Abmachung muss eindeutig dargestellt werden.
Ein Kandidat dafür wäre eine Map \<^typ>\<open>'person \<rightharpoonup> 'etwas\<close>, da diese eindeutig einer
\<^typ>\<open>'person\<close> ein \<^typ>\<open>'etwas\<close> zuordnet.
Dies funktioniert allerdings nur, wenn \<^typ>\<open>'etwas::{uminus,plus}\<close> mit Plus und Minus
dargestellt werden kann, um \<^const>\<open>Gewinnt\<close> und \<^const>\<open>Verliert\<close> darzustellen.
Allerdings ist auch diese Darstellung nicht eindeutig,
da z.B. \<^term>\<open>[Alice \<mapsto> 0] = Map.empty\<close> semantisch gilt,
solange \<^term>\<open>0\<close> ein neutrales Element ist.
Deshalb stellen wir eine Abmachung als eine
totale Funktion \<^typ>\<open>'person \<Rightarrow> ('etwas::{uminus, plus, zero})\<close> dar.
\<^term>\<open>(\<lambda>_. 0)(Alice := 3, Bob := -3)\<close> bedeutet \<^const>\<open>Alice\<close> bekommt 3, \<^const>\<open>Bob\<close> verliert 3.
\<close>
type_synonym  ('person, 'etwas) abmachung = "'person \<Rightarrow> 'etwas"

(*TODO: dedup mit aenderung_list_to_to_abmachung*)
fun to_abmachung
  :: "('person, 'etwas::{ord,zero,plus,minus,uminus}) aenderung list \<Rightarrow> ('person, 'etwas) abmachung"
where
  "to_abmachung [] = (\<lambda>p. 0)"
| "to_abmachung (delta # deltas) = 
   \<lbrakk>(to_abmachung deltas)(betroffen delta += aenderung_val delta)\<rbrakk>"

(*<*)
lemma to_abmachung_simp_call:
  "to_abmachung (delta # deltas) p =
    (if p = betroffen delta
     then (to_abmachung deltas p) + (aenderung_val delta)
     else (to_abmachung deltas p))"
  by(simp)
(*>*)



lemma \<open>[to_abmachung [Gewinnt Alice (3::int)], to_abmachung [Gewinnt Alice 3, Verliert Bob 3]]
        = [(\<lambda>p.0)(Alice := 3), (\<lambda>p.0)(Alice := 3, Bob := -3)]\<close> by eval

(*<*)
fun abmachung_to_aenderung_list
  :: "'person list \<Rightarrow> ('person, 'etwas::{ord,zero,plus,minus,uminus}) abmachung \<Rightarrow> ('person, 'etwas) aenderung list"
where
  "abmachung_to_aenderung_list [] _ = []"
| "abmachung_to_aenderung_list (p#ps) a =
    (if a p = 0
     then abmachung_to_aenderung_list ps a
     else (if a p > 0 then Gewinnt p (a p) else Verliert p (- (a p))) # abmachung_to_aenderung_list ps a
    )"

definition abmachung_to_aenderung
  :: "('person::enum, 'etwas::{ord,zero,plus,minus,uminus}) abmachung \<Rightarrow> ('person, 'etwas) aenderung list"
where
  "abmachung_to_aenderung \<equiv> abmachung_to_aenderung_list Enum.enum"

lemma \<open>abmachung_to_aenderung ((\<lambda>p.0)(Alice := (3::int), Bob := -3)) = [Gewinnt Alice 3, Verliert Bob 3]\<close> by eval



definition aenderung_to_abmachung
  :: "('person, 'etwas) aenderung list \<Rightarrow> ('person::enum, 'etwas::{ord,zero,plus,minus,uminus}) abmachung"
where
  "aenderung_to_abmachung \<equiv> to_abmachung"


lemma fixes as :: "('person::enum, int) aenderung list"
  shows "abmachung_to_aenderung (aenderung_to_abmachung as) = as"
  (* nitpick as = [Verliert person\<^sub>1 (- 1)] *)
  oops (*gilt nicht, weil aenderungen nicht eindeutig*)


lemma abmachung_to_aenderung_list_to_abmachung_not_in_ps:
  "p \<notin> set ps \<Longrightarrow>  to_abmachung (abmachung_to_aenderung_list ps a) p = 0"
  by(induction ps) simp+

lemma abmachung_to_aenderung_list_not_in_ps:
  "p \<notin> set ps \<Longrightarrow>
       abmachung_to_aenderung_list ps (a(p := v)) = abmachung_to_aenderung_list ps a"
  apply(induction ps)
   apply(simp)
  apply(simp)
  by fastforce


definition abmachung_dom :: "('person, 'etwas::zero) abmachung \<Rightarrow> 'person set" where
  "abmachung_dom m = {a. m a \<noteq> 0}"

lemma abmachung_dom_swap:
  "abmachung_dom (swap p1 p2 a) = (swap p1 p2 id) ` (abmachung_dom a)"
  apply(simp add: abmachung_dom_def)
  apply(simp add: image_def)
  apply(rule Collect_cong)
  apply(simp add: swap_def)
  by fast

lemma to_abmachung_abmachung_to_aenderung_list_induct_helper:
  fixes a :: "('person::enum, 'etwas::ordered_ab_group_add) abmachung"
  shows "abmachung_dom a \<subseteq> set ps \<Longrightarrow> distinct ps \<Longrightarrow> to_abmachung (abmachung_to_aenderung_list ps a) = a"
  apply(induction ps arbitrary: a)
   apply(simp add: abmachung_dom_def)
   apply fastforce
  apply(rename_tac p ps a)
  apply(simp)
  apply(simp add: abmachung_to_aenderung_list_to_abmachung_not_in_ps)
  apply(case_tac "p \<notin> abmachung_dom a")
   apply(subgoal_tac "abmachung_dom a \<subseteq> set ps")
    apply(simp add: abmachung_dom_def; fail)
   apply(simp add: abmachung_dom_def)
   apply blast
  apply(subgoal_tac "abmachung_dom (a(p := 0)) \<subseteq> set ps")
   prefer 2
   apply(simp add: abmachung_dom_def)
   apply blast
  apply(subgoal_tac "to_abmachung (abmachung_to_aenderung_list ps a) = (a(p := 0))") (*instantiate IH*)
   prefer 2
   apply(simp)
   apply (metis abmachung_to_aenderung_list_not_in_ps)
  apply(simp)
  by fastforce

lemma aenderung_to_abmachung_abmachung_to_aenderung:
  fixes a :: "('person::enum, 'etwas::ordered_ab_group_add) abmachung"
  shows "aenderung_to_abmachung (abmachung_to_aenderung a) = a"
  apply(simp add: abmachung_to_aenderung_def aenderung_to_abmachung_def)
  apply(rule to_abmachung_abmachung_to_aenderung_list_induct_helper)
   apply(simp add: enum_class.enum_UNIV)
  apply(simp add: enum_class.enum_distinct)
  done
(*>*)



definition abmachung_ausfuehren
  :: "('person, 'etwas::{plus,minus}) abmachung \<Rightarrow> ('person \<Rightarrow> 'etwas) \<Rightarrow> ('person \<Rightarrow> 'etwas)"
where
  "abmachung_ausfuehren a besitz \<equiv> \<lambda>p. a p + (besitz p)"

text\<open>Beispiel:\<close>
lemma
  "abmachung_ausfuehren
    (to_abmachung [Gewinnt Alice 3, Verliert Bob 3])
    (\<^url>[Alice:=8, Bob:=3, Eve:= 5])
  = (\<^url>[Alice:=11, Bob:=0, Eve:= 5])"
  by(code_simp)


(*<*)
lemma abmachung_ausfuehren_swap:
  "abmachung_ausfuehren (swap p1 p2 a) (swap p1 p2 welt)
    = swap p2 p1 (abmachung_ausfuehren a welt)"
  by(auto simp add: abmachung_ausfuehren_def swap_def)

lemma aenderung_ausfuehren_abmachung_to_aenderung_induction_helper:
  fixes welt :: "'person::enum \<Rightarrow> 'etwas::ordered_ab_group_add"
  shows "abmachung_dom abmachung \<subseteq> set ps \<Longrightarrow> distinct ps \<Longrightarrow> 
          aenderung_ausfuehren (abmachung_to_aenderung_list ps abmachung) welt p =
            welt p + (abmachung p)"
  apply(induction ps arbitrary: abmachung welt)
   apply(simp add: abmachung_dom_def; fail)
  apply(simp)
  apply(rename_tac pa ps abmachung welt)
  apply(subgoal_tac "abmachung_dom (abmachung(pa := 0)) \<subseteq> set ps")
   prefer 2
  subgoal
    apply(simp add: abmachung_dom_def)
    by blast
  apply(subgoal_tac "aenderung_ausfuehren (abmachung_to_aenderung_list ps (abmachung(pa := 0))) welt p =
           welt p + (abmachung(pa := 0)) p")
   prefer 2
   apply blast
  by (metis (no_types, lifting) abmachung_to_aenderung_list_not_in_ps add.right_neutral fun_upd_other fun_upd_same)
  


lemma aenderung_ausfuehren_abmachung_to_aenderung:
  fixes welt :: "'person::enum \<Rightarrow> 'etwas::ordered_ab_group_add"
  shows "aenderung_ausfuehren (abmachung_to_aenderung abmachung) welt p = welt p + (abmachung p)"
  apply(simp add: abmachung_to_aenderung_def)
  apply(rule aenderung_ausfuehren_abmachung_to_aenderung_induction_helper)
   apply(simp add: enum_class.enum_UNIV)
  apply(simp add: enum_class.enum_distinct)
  done

(*TODO: does this make a good [code] rule? I cannot measure performance changes.*)
lemma abmachung_ausfuehren_aenderung:
  fixes abmachung :: "('person::enum, 'etwas::ordered_ab_group_add) abmachung"
  shows "abmachung_ausfuehren abmachung = aenderung_ausfuehren (abmachung_to_aenderung abmachung)"
  by(simp add: abmachung_ausfuehren_def fun_eq_iff aenderung_ausfuehren_abmachung_to_aenderung)

(*>*)


text\<open>Laut \<^url>\<open>https://de.wikipedia.org/wiki/Konsens#Konsens_im_Rechtssystem\<close> lässt sich Konsens
wie folg definieren:
"die Übereinstimmung der Willenserklärungen beider Vertragspartner über die Punkte des Vertrages".
Wir können also \<^term>\<open>to_abmachung [Gewinnt Alice 3, Verliert Bob 3]\<close> verwenden,
um Konsens zu modellieren.
Dabei müssen alle Betroffenen die gleiche Vorstellung der Abmachung haben.
Beispielsweise lässt sich der gesamte Konsens in einer Welt darstellen als
\<^typ>\<open>'person \<Rightarrow> ('person, 'etwas) abmachung list\<close>, wobei jeder person genau die Abmachungen
zugeordnet werden, deren sie zustimmt.
Die Abmachungen sind in einer Liste und keiner Menge, da eine Person eventuell bereit ist,
Abmachungen mehrfach auszuführen.
\<close>


type_synonym ('person, 'etwas) globaler_konsens = "'person \<Rightarrow> ('person, 'etwas) abmachung list"

(*<*)
definition konsensswap
:: "'person \<Rightarrow> 'person \<Rightarrow> ('person, 'etwas) globaler_konsens
    \<Rightarrow> ('person, 'etwas) globaler_konsens"
  where
"konsensswap p1 p2 kons \<equiv> swap p1 p2 ((map (swap p1 p2)) \<circ> kons)"

lemma konsensswap_id[simp]: "konsensswap p1 p2 (konsensswap p1 p2 kons) = kons"
  apply(simp add: konsensswap_def)
  apply(subst swap_fun_map_comp_id)
  by simp

lemma konsensswap_sym: "konsensswap p1 p2 = konsensswap p2 p1"
  by(simp add: fun_eq_iff konsensswap_def swap_symmetric)

lemma konsensswap_apply:
  "konsensswap p1 p2 kons p =  map (swap p1 p2) (swap p1 p2 kons p)"
  apply(simp add: konsensswap_def comp_def)
  by (metis swap_a swap_b swap_nothing)
(*>*)



definition abmachungs_betroffene :: "('person::enum, 'etwas::zero) abmachung \<Rightarrow> 'person list"
where
  "abmachungs_betroffene a \<equiv> [p. p \<leftarrow> Enum.enum, a p \<noteq> 0]"

lemma \<open>abmachungs_betroffene (to_abmachung [Gewinnt Bob (3::int), Verliert Alice 3])
  = [Alice, Bob]\<close> by eval


(*<*)
lemma abmachungs_betroffene_simp: "abmachungs_betroffene a = filter (\<lambda>p. a p \<noteq> 0) Enum.enum"
proof -
  have "concat (map (\<lambda>p. if a p \<noteq> 0 then [p] else []) as) = filter (\<lambda>p. a p \<noteq> 0) as" for as
    by(induction as) auto
  thus ?thesis
    by(simp add: abmachungs_betroffene_def)
qed

lemma abmachungs_betroffene_distinct: "distinct (abmachungs_betroffene a)"
  apply(simp add: abmachungs_betroffene_simp)
  using enum_class.enum_distinct distinct_filter by blast

lemma abmachungs_betroffene_is_dom: "set (abmachungs_betroffene a) = abmachung_dom a"
  by(simp add: abmachung_dom_def abmachungs_betroffene_simp enum_class.enum_UNIV)

lemma set_abmachungs_betroffene_swap:
  "set (abmachungs_betroffene (swap p1 p2 a)) = (swap p1 p2 id) ` set (abmachungs_betroffene a)"
  apply(simp add: abmachungs_betroffene_simp enum_class.enum_UNIV)
  apply(simp add: image_def)
  apply(rule Collect_cong)
  apply(simp add: swap_def)
  by fast
(*>*)



definition enthaelt_konsens
  :: "('person::enum, 'etwas::zero) abmachung \<Rightarrow> ('person, 'etwas) globaler_konsens \<Rightarrow> bool"
where
  "enthaelt_konsens abmachung konsens \<equiv> \<forall>betroffene_person \<in> set (abmachungs_betroffene abmachung).
      abmachung \<in> set (konsens betroffene_person)"

lemma enthaelt_konsens_swap:
  "enthaelt_konsens (swap p1 p2 a) (konsensswap p1 p2 konsens) = enthaelt_konsens a konsens" 
  apply(simp add: enthaelt_konsens_def abmachungs_betroffene_is_dom)
  apply(simp add: abmachung_dom_swap)
  apply(simp add: konsensswap_def comp_def)
  by (smt (z3) id_apply image_def list.set_map mem_Collect_eq swap2 swap_a swap_b swap_nothing)



text\<open>Eine (ausgeführte) Abmachung einlösen, bzw. entfernen.\<close>
definition konsens_entfernen
 :: "('person::enum, 'etwas::zero) abmachung \<Rightarrow> ('person \<Rightarrow> ('person, 'etwas) abmachung list)
   \<Rightarrow> ('person \<Rightarrow> ('person, 'etwas) abmachung list)"
 where
"konsens_entfernen abmachung kons =
      fold (\<lambda>p k. k(p := remove1 abmachung (k p))) (abmachungs_betroffene abmachung) kons"


lemma
  \<open>konsens_entfernen
    (to_abmachung [Gewinnt Alice (3::int), Verliert Bob 3])
    ((\<lambda>_. [])(
      Alice := [to_abmachung [Gewinnt Alice 3], to_abmachung [Gewinnt Alice 3, Verliert Bob 3]],
      Bob := [to_abmachung [Gewinnt Alice 3, Verliert Bob 3]])
    )
  = (\<lambda>_. [])(
    Alice := [to_abmachung [Gewinnt Alice 3]],
    Bob := [])\<close>
  by eval


(*<*)
lemma konsens_entfernen_fold_induct_helper_helper:
  "a \<notin> set as \<Longrightarrow> fold (\<lambda>a k. k(a := f (k a))) as kons a = kons a"
  by(induction as arbitrary: kons) simp+
lemma konsens_entfernen_fold_induct_helper:
  "x \<in> set as \<Longrightarrow> distinct as \<Longrightarrow>
         fold (\<lambda>a k. k(a := f (k a))) as kons x = f (kons x)"
  apply(induction as arbitrary: kons)
   apply(simp; fail)
  apply(simp)
  apply(erule disjE)
   apply(simp)
  apply(simp add: konsens_entfernen_fold_induct_helper_helper; fail)
   apply(simp)
  apply blast
  done
(*>*)



text\<open>Alternative Definition:\<close>
lemma konsens_entfernen_simp:
  "konsens_entfernen a kons
    = (\<lambda>p. if p \<in> set (abmachungs_betroffene a) then remove1 a (kons p) else (kons p))"
  apply(simp add: konsens_entfernen_def fun_eq_iff)
  apply(intro allI conjI impI)
   apply(subst konsens_entfernen_fold_induct_helper, simp_all)
   apply(simp add: abmachungs_betroffene_distinct)
  apply(simp add: konsens_entfernen_fold_induct_helper_helper)
  done


(*<*)  
lemma remove1_konsensswap:
  "remove1 (swap p1 p2 a) (konsensswap p1 p2 kons p)
    = map (swap p1 p2) (remove1 a (swap p1 p2 kons p))"
  by(simp add: konsensswap_apply remove1_swap)

lemma konsens_entfernen_konsensswap:
  "konsensswap p2 p1 (konsens_entfernen (swap p1 p2 a) (konsensswap p1 p2 kons))
    = konsens_entfernen a kons"
  apply(simp add: konsens_entfernen_simp fun_eq_iff)
  apply(safe)
   apply(simp add: set_abmachungs_betroffene_swap)
   apply(simp add: konsensswap_apply)
   apply(simp add: swap_if_move_inner)
   apply(simp add: swap_id_in_set)
   apply(subst(2) remove1_swap2[of p1 p2, symmetric])
   apply(auto simp add: konsensswap_apply swap_def)[1] (*wants helper*)

  apply(simp add: set_abmachungs_betroffene_swap)
  apply(simp add: konsensswap_apply)
  apply(simp add: swap_if_move_inner)
  apply(simp add: swap_id_in_set)
  apply(simp add: konsensswap_apply swap_def comp_def)
  by (simp add: list.map_ident_strong)
(*>*)





end
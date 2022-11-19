(*<*)
theory Aenderung
imports Main ExecutableHelper BeispielPerson Handlung Zahlenwelt
begin

section\<open>Änderungen in Welten\<close>

datatype ('person, 'etwas) aenderung = Verliert \<open>'person\<close> \<open>'etwas\<close> | Gewinnt \<open>'person\<close> \<open>'etwas\<close>

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



lemma delta_num_same: "delta_num p (a::'a::ordered_ab_group_add) a = None"
  by(simp add: delta_num_def)


text\<open>Deltas, d.h. Unterschiede Zwischen Welten.

Man könnte eine class Delta world einführen, mit einer delta-Funtion
  :: welt -> welt -> [Aenderung person etwas]
Diese Klasse würde dann Welten mit Personen und Etwas in Relation setzen.
Dafür bräuchte es MultiParamTypeClasses. Eine simple Funktion ist da einfacher.\<close>
type_synonym ('world, 'person, 'etwas) delta =
    \<open>'world handlung \<Rightarrow> (('person, 'etwas) aenderung) list\<close>


definition betroffen :: "('person, 'etwas) aenderung list \<Rightarrow> 'person list"
  where
"betroffen as \<equiv> map (\<lambda>a. case a of Verliert p _ \<Rightarrow> p | Gewinnt p _ \<Rightarrow> p) as"

lemma betroffen_case_aenderung:
  "betroffen = map (case_aenderung (\<lambda>p _. p) (\<lambda>p _. p))"
  by(simp add: fun_eq_iff betroffen_def)

lemma "betroffen [Verliert Alice (2::int), Gewinnt Bob 3, Gewinnt Carol 2, Verliert Eve 1]
  = [Alice, Bob, Carol, Eve]" by eval
lemma "betroffen [Verliert Alice (5::nat), Gewinnt Bob 3, Verliert Eve 7]
  = [Alice, Bob, Eve]" by eval
lemma "betroffen [Verliert Alice (5::nat), Gewinnt Alice 3]
  = [Alice, Alice]" by eval

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







(*TODO: move*)
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

end
(*>*)
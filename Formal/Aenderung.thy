(*<*)
theory Aenderung
imports Main ExecutableHelper BeispielPerson Handlung
begin

section\<open>Änderungen in Welten\<close>

datatype ('person, 'etwas) aenderung = Verliert 'person 'etwas | Gewinnt 'person 'etwas

definition delta_num
  :: "'person \<Rightarrow> 'etwas::{ord,minus} \<Rightarrow> 'etwas \<Rightarrow> (('person, 'etwas) aenderung) option"
  where
    "delta_num p i1 i2 = (
           if i1 > i2 then Some (Verliert p (i1 - i2))
      else if i1 < i2 then Some (Gewinnt p (i2 - i1))
      else None
  )"

lemma "delta_num p i1 i2 = Some (Gewinnt p (i::int)) \<Longrightarrow> i > 0"
  by(auto simp add: delta_num_def split_ifs)
lemma "delta_num p i1 i2 = Some (Verliert p (i::int)) \<Longrightarrow> i > 0"
  by(auto simp add: delta_num_def split_ifs)
lemma "delta_num p1 i1 i2 = Some (Gewinnt p2 (i::int)) \<Longrightarrow> p1 = p2"
  by(auto simp add: delta_num_def split_ifs)
lemma "delta_num p1 i1 i2 = Some (Verliert p2 (i::int)) \<Longrightarrow> p1 = p2"
  by(auto simp add: delta_num_def split_ifs)


text\<open>Deltas, d.h. Unterschiede Zwischen Welten.

Man könnte eine class Delta world einführen, mit einer delta-Funtion
  :: welt -> welt -> [Aenderung person etwas]
Diese Klasse würde dann Welten mit Personen und Etwas in Relation setzen.
Dafür bräuchte es MultiParamTypeClasses. Eine simple Funktion ist da einfacher.\<close>
type_synonym ('world, 'person, 'etwas) delta =
    "'world handlung \<Rightarrow> (('person, 'etwas) aenderung) list"

fun delta_num_map
  :: "(('person::enum \<rightharpoonup> ('etwas::{zero,minus,ord})), 'person, 'etwas) delta"
  where
  "delta_num_map (Handlung vor nach) =
      List.map_filter
        (\<lambda>p. case (the_default (vor p) 0, the_default (nach p) 0)
               of (a,b) \<Rightarrow> delta_num p a b)
        (Enum.enum::'person list)"

lemma\<open>delta_num_map
  (Handlung [Alice \<mapsto> 5::int, Bob \<mapsto> 10, Eve \<mapsto> 1]
            [Alice \<mapsto> 3, Bob \<mapsto> 13, Carol \<mapsto> 2])
  = [Verliert Alice 2, Gewinnt Bob 3, Gewinnt Carol 2, Verliert Eve 1]\<close> by eval


fun delta_num_fun
  :: "(('person::enum \<Rightarrow> ('etwas::{minus,ord})), 'person, 'etwas) delta"
  where
  "delta_num_fun (Handlung vor nach) =
      List.map_filter (\<lambda>p. delta_num p (vor p) (nach p)) Enum.enum"

lemma \<open>delta_num_fun
    (Handlung
        ((\<lambda>p. 0::int)(Alice:=8, Bob:=12, Eve:=7))
        ((\<lambda>p. 0::int)(Alice:=3, Bob:=15, Eve:=0)))
  = [Verliert Alice 5, Gewinnt Bob 3, Verliert Eve 7]\<close> by eval

lemma delta_num_map: "delta_num_map (Handlung m1 m2) =
        delta_num_fun (Handlung (\<lambda>p. the_default (m1 p) 0) (\<lambda>p. the_default (m2 p) 0))"
  by(simp)


end
(*>*)
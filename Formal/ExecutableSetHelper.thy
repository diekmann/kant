theory ExecutableSetHelper
imports Main
begin

(*TODO: is there a library function for this?*)
fun the_default :: "'a option \<Rightarrow> 'a \<Rightarrow> 'a" where
  "the_default None def = def"
| "the_default (Some a) _ = a"


lemma "{b. \<exists>p. (m p) = Some b} = {b. Some b \<in> range m}"
  by (metis rangeE range_eqI)
lemma map_filter_id: "S = set s \<Longrightarrow> {b. Some b \<in> S} = set (List.map_filter id s)"
  apply(simp add: map_filter_def)
  apply(simp add: image_def)
  apply(rule Collect_cong)
  by auto

lemma set_of_constructor:
  "bij Constr \<Longrightarrow> (\<And>x. deconstruct x = (inv Constr) x) \<Longrightarrow> {p. Constr p \<in> ps} = deconstruct ` ps"
  apply(simp)
  apply(simp add: vimage_def[symmetric])
  apply(simp add: bij_vimage_eq_inv_image)
  done


(*TODO: why isnt this a library function?*)
definition map_map :: "('a \<Rightarrow> 'b) \<Rightarrow> ('k \<rightharpoonup> 'a) \<Rightarrow> ('k \<rightharpoonup> 'b)" where
  "map_map f m k \<equiv> case m k of None \<Rightarrow> None | Some a \<Rightarrow> Some (f a)"

lemma map_map: "map_map f m = map_comp (\<lambda>a. Some (f a)) m"
  by(simp add: fun_eq_iff map_map_def map_comp_def)

(*does this help printing?*)
lemma map_map_map_if_propagate:
  "map_map f (\<lambda>k. if P k then Some y else X k) = (\<lambda>k. if P k then Some (f y) else map_map f X k)"
  apply(simp add: fun_eq_iff, intro allI conjI)
   apply(simp add: map_map_def)+
  done


text\<open>Isabelle does not allow printing functions, but it allows printing lists\<close>
definition show_map :: "('a::enum \<rightharpoonup> 'b) \<Rightarrow> ('a \<times> 'b) list" where
  "show_map m \<equiv> List.map_filter (\<lambda>p. map_option (\<lambda>i. (p, i)) (m p)) (enum_class.enum)"

lemma \<open>show_map [True \<mapsto> (8::int), False \<mapsto> 12] = [(False, 12), (True, 8)]\<close> by eval

lemma "map_of (show_map m) = m"
  apply(simp add: show_map_def map_of_def)
  apply(induction enum_class.enum)
   apply(simp)
  oops (*TODO*)


definition show_fun :: "('a::enum \<Rightarrow> 'b) \<Rightarrow> ('a \<times> 'b) list" where
  "show_fun f \<equiv> map (\<lambda>p. (p, f p)) (enum_class.enum)"


end
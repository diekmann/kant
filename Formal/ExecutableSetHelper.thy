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


end
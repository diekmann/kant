theory ExecutableHelper
imports Main
begin

(*is this helpful?*)
term sorted_list_of_set


section\<open>Executable Helper\<close>
text\<open>This is a helper library (and should be excluded from the theory document).\<close>

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


lemma show_map_induction_helper:
  "distinct xs \<Longrightarrow> dom m \<subseteq> set xs \<Longrightarrow> map_of (List.map_filter (\<lambda>p. map_option (Pair p) (m p)) xs) = m"
proof(induction xs arbitrary: m)
  case Nil
  then show ?case by(simp add: map_filter_def)
next
  case (Cons x xs)
  then show ?case
  proof(cases "\<exists>y. m x = Some y")
    case True
    from True obtain y where "m x = Some y" by blast
    let ?m'="m(x:=None)"
    have m: "m = ?m'(x \<mapsto> y)" using \<open>m x = Some y\<close> by auto
    have "dom ?m' \<subseteq> set xs" using Cons.prems by auto
    with Cons.IH[of ?m'] have IH':
      "map_of (List.map_filter (\<lambda>p. map_option (Pair p) (?m' p)) xs) = ?m'"
      using Cons.prems(1) by fastforce
    show ?thesis
      apply(subst m)
      by (smt (z3) Cons.prems(1)
            \<open>m x = Some y\<close> IH' distinct.simps(2)
            domIff dom_fun_upd filter_cong insertE
            m map_eq_conv map_filter_def map_filter_simps(1)
            map_le_def map_of.simps(2) mem_Collect_eq o_apply
            option.case(2) option.map(2) prod.sel(1) prod.sel(2)
            set_filter upd_None_map_le)
  next
    case False
    with Cons show ?thesis
      apply(simp add: map_filter_def)
      apply (meson domIff subset_insert)
      done
  qed
qed


lemma map_of_show_map:
  fixes m::"'a::enum \<Rightarrow> 'b option"
  shows "map_of (show_map m) = m"
  apply(simp add: show_map_def)
  apply(rule show_map_induction_helper)
  using enum_distinct apply simp
  by(simp add: UNIV_enum[symmetric])


definition show_fun :: "('a::enum \<Rightarrow> 'b) \<Rightarrow> ('a \<times> 'b) list" where
  "show_fun f \<equiv> map (\<lambda>p. (p, f p)) (enum_class.enum)"


end
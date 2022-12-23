theory ExecutableHelper
imports Main BeispielTac "HOL-Library.Code_Target_Numeral"
begin

(*is this helpful?*)
term \<open>sorted_list_of_set\<close>


section\<open>Executable Helper\<close>
text\<open>This is a helper library (and should be excluded from the theory document).\<close>

(*TODO: is there a library function for this?*)
fun the_default :: \<open>'a option \<Rightarrow> 'a \<Rightarrow> 'a\<close> where
  \<open>the_default None def = def\<close>
| \<open>the_default (Some a) _ = a\<close>



lemma set_of_constructor:
  \<open>bij Constr \<Longrightarrow> (\<And>x. deconstruct x = (inv Constr) x) \<Longrightarrow> {p. Constr p \<in> ps} = deconstruct ` ps\<close>
  apply(simp)
  apply(simp add: vimage_def[symmetric])
  apply(simp add: bij_vimage_eq_inv_image)
  done


(*TODO: why isnt this a library function?*)
definition map_map :: \<open>('a \<Rightarrow> 'b) \<Rightarrow> ('k \<rightharpoonup> 'a) \<Rightarrow> ('k \<rightharpoonup> 'b)\<close> where
  \<open>map_map f m k \<equiv> case m k of None \<Rightarrow> None | Some a \<Rightarrow> Some (f a)\<close>

term \<open>map_fun id \<circ> map_option\<close>

lemma map_map: \<open>map_map f m = map_comp (\<lambda>a. Some (f a)) m\<close>
  by(simp add: fun_eq_iff map_map_def map_comp_def)

(*does this help printing?*)
lemma map_map_map_if_propagate:
  \<open>map_map f (\<lambda>k. if P k then Some y else X k) = (\<lambda>k. if P k then Some (f y) else map_map f X k)\<close>
  apply(simp add: fun_eq_iff, intro allI conjI)
   apply(simp add: map_map_def)+
  done


text\<open>Isabelle does not allow printing functions, but it allows printing lists\<close>
definition show_map :: \<open>('a::enum \<rightharpoonup> 'b) \<Rightarrow> ('a \<times> 'b) list\<close> where
  \<open>show_map m \<equiv> List.map_filter (\<lambda>p. map_option (\<lambda>i. (p, i)) (m p)) (enum_class.enum)\<close>

beispiel \<open>show_map [True \<mapsto> (8::int), False \<mapsto> 12] = [(False, 12), (True, 8)]\<close> by eval

lemma List_map_filter_map_some_cons: \<open>m x = Some y \<Longrightarrow>
  (List.map_filter (\<lambda>p. map_option (Pair p) (m p)) (x # xs)) =
       (x,y) # (List.map_filter (\<lambda>p. map_option (Pair p) (m p)) (xs))\<close>
  apply(simp add: List.map_filter_def)
  done


lemma List_map_filter_map_of_eq_helper: \<open>x \<notin> set xs
  \<Longrightarrow>  map_of (List.map_filter (\<lambda>p. map_option (Pair p) ((m(x := None)) p)) xs)
        = (map_of (List.map_filter (\<lambda>p. map_option (Pair p) (m p)) xs))\<close>
  apply(simp add: map_filter_def)
  apply(rule arg_cong)
  apply(simp)
  apply(subgoal_tac \<open>(filter (\<lambda>xa. xa \<noteq> x \<and> (xa \<noteq> x \<longrightarrow> (\<exists>y. m xa = Some y))) xs) =
        (filter (\<lambda>x. \<exists>y. m x = Some y) xs)\<close>)
   prefer 2
   apply (rule filter_cong)
    apply(simp; fail)
   apply blast
  apply(simp)
  done

lemma show_map_induction_helper:
  \<open>distinct xs \<Longrightarrow> dom m \<subseteq> set xs \<Longrightarrow>
    map_of (List.map_filter (\<lambda>p. map_option (Pair p) (m p)) xs) = m\<close>
proof(induction \<open>xs\<close> arbitrary: \<open>m\<close>)
  case Nil
  then show \<open>?case\<close> by(simp add: map_filter_def)
next
  case (Cons x xs)
  then show \<open>?case\<close>
  proof(cases \<open>\<exists>y. m x = Some y\<close>)
    case True
    from True obtain y where \<open>m x = Some y\<close> by blast
    let \<open>?m'\<close>=\<open>m(x:=None)\<close>
    have m: \<open>m = ?m'(x \<mapsto> y)\<close> using \<open>m x = Some y\<close> by auto
    have \<open>x \<notin> set xs\<close> using Cons.prems(1) by auto
    have \<open>dom ?m' \<subseteq> set xs\<close> using Cons.prems by auto
    with Cons.IH[of \<open>?m'\<close>] have IH':
      \<open>map_of (List.map_filter (\<lambda>p. map_option (Pair p) (?m' p)) xs) = ?m'\<close>
      using Cons.prems(1) by fastforce
    with List_map_filter_map_of_eq_helper[OF \<open>x \<notin> set xs\<close>, of \<open>m\<close>] have IH'':
      \<open>map_of (List.map_filter (\<lambda>p. map_option (Pair p) (m p)) xs) = ?m'\<close>
      by simp
    from \<open>m x = Some y\<close> have 1:
      \<open>List.map_filter (\<lambda>p. map_option (Pair p) (m p)) (x # xs) =
        (x, y) # List.map_filter (\<lambda>p. map_option (Pair p) (m p)) xs\<close>
      using List_map_filter_map_some_cons[of \<open>m\<close> \<open>x\<close> \<open>y\<close> \<open>xs\<close>] by simp
    show \<open>?thesis\<close>
      apply(subst 1)
      apply(simp)
      apply(subst IH'')
      using m by auto
  next
    case False
    with Cons show \<open>?thesis\<close>
      apply(simp add: map_filter_def)
      apply (meson domIff subset_insert)
      done
  qed
qed


lemma map_of_show_map:
  fixes m::\<open>'a::enum \<Rightarrow> 'b option\<close>
  shows \<open>map_of (show_map m) = m\<close>
  apply(simp add: show_map_def)
  apply(rule show_map_induction_helper)
  using enum_distinct apply simp
  by(simp add: UNIV_enum[symmetric])


definition show_fun :: \<open>('a::enum \<Rightarrow> 'b) \<Rightarrow> ('a \<times> 'b) list\<close> where
  \<open>show_fun f \<equiv> map (\<lambda>p. (p, f p)) (enum_class.enum)\<close>


definition show_num_fun :: \<open>('a::enum \<Rightarrow> 'b::zero) \<Rightarrow> ('a \<times> 'b) list\<close> where
  \<open>show_num_fun f \<equiv> List.map_filter
    (\<lambda>p. if (f p) = 0 then None else Some (p, f p)) (enum_class.enum)\<close>


end
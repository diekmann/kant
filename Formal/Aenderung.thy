theory Aenderung
imports Main ExecutableHelper BeispielPerson Handlung Zahlenwelt "HOL-Library.Multiset"
begin

section\<open>Änderungen in Welten\<close>
text\<open>In diesem Abschnitt werden wir Änderungen in Welten,
und darauf basierend, Abmachungen modellieren.\<close>

text\<open>Bei einer Änderung keine eine Person entweder etwas verlieren oder gewinnen.
Dieses einfache Modell ist natürlich auf unsere Zahlenwelten angepasst,
in der normalerweise Typ \<^typ>\<open>'etwas\<close> ein \<^typ>\<open>int\<close> ist.\<close>
datatype ('person, 'etwas) aenderung = Verliert \<open>'person\<close> \<open>'etwas\<close> | Gewinnt \<open>'person\<close> \<open>'etwas\<close>

text\<open>Beispiel: \<^term>\<open>[Gewinnt Alice 3, Verliert Bob 3]::(person, int) aenderung list\<close>.\<close>

text\<open>Von einer \<^typ>\<open>('person, 'etwas) aenderung\<close> betroffene Person bzw. Personen.\<close>
definition betroffen :: \<open>('person, 'etwas) aenderung \<Rightarrow> 'person\<close>
  where
\<open>betroffen a \<equiv> case a of Verliert p _ \<Rightarrow> p | Gewinnt p _ \<Rightarrow> p\<close>

definition betroffene :: \<open>('person, 'etwas) aenderung list \<Rightarrow> 'person list\<close>
  where
\<open>betroffene as \<equiv> map betroffen as\<close>

(*<*)
lemma betroffene_case_aenderung:
  \<open>betroffene = map (case_aenderung (\<lambda>p _. p) (\<lambda>p _. p))\<close>
  by(simp add: fun_eq_iff betroffene_def betroffen_def)
(*>*)


beispiel \<open>betroffene [Verliert Alice (2::int), Gewinnt Bob 3, Gewinnt Carol 2, Verliert Eve 1]
  = [Alice, Bob, Carol, Eve]\<close> by eval
beispiel \<open>betroffene [Verliert Alice (5::nat), Gewinnt Bob 3, Verliert Eve 7]
  = [Alice, Bob, Eve]\<close> by eval
beispiel \<open>betroffene [Verliert Alice (5::nat), Gewinnt Alice 3]
  = [Alice, Alice]\<close> by eval

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


beispiel \<open>delta_num Alice (2::int) 6 = Some (Gewinnt Alice 4)\<close> by eval
beispiel \<open>delta_num Alice (-2::int) 6 = Some (Gewinnt Alice 8)\<close> by eval


lemma delta_num_same: \<open>delta_num p (a::'a::ordered_ab_group_add) a = None\<close>
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

beispiel \<open>sum_delta_num Alice (2::int) 6 = Some (Gewinnt Alice 8)\<close> by eval
beispiel \<open>sum_delta_num Alice (-2::int) 6 = Some (Gewinnt Alice 4)\<close> by eval

lemma sum_delta_num_delta_num:
  fixes i1::\<open>'a::ordered_ab_group_add\<close>
  shows \<open>sum_delta_num p i1 i2 = delta_num p 0 (i1+i2)\<close>
  by(simp add: sum_delta_num_def delta_num_def Let_def)

lemma  delta_num_sum_delta_num:
  fixes i1::\<open>'a::ordered_ab_group_add\<close>
  shows \<open>delta_num p i1 i2 = sum_delta_num p (-i1) i2\<close>
  by(simp add: sum_delta_num_def delta_num_def Let_def)

(*>*)

subsection\<open>Deltas\<close>
text\<open>Deltas, d.h. Unterschiede zwischen Welten.
Ein Delta ist eine Liste von Änderungen.
Wir definieren das \<^theory_text>\<open>type_synonym\<close> delta als die Funktion,
welche solch eine Liste berechnet,
gegeben die Handlung welche die Veränderung hervorruft.\<close>
(*Man könnte eine class Delta world einführen, mit einer delta-Funtion
  :: welt -> welt -> [Aenderung person etwas]
Diese Klasse würde dann Welten mit Personen und Etwas in Relation setzen.
Dafür bräuchte es MultiParamTypeClasses. Eine simple Funktion ist da einfacher.*)
type_synonym ('welt, 'person, 'etwas) delta =
    \<open>'welt handlung \<Rightarrow> (('person, 'etwas) aenderung) list\<close>

(*<*)
definition aenderung_val :: \<open>('person, ('etwas::uminus)) aenderung \<Rightarrow> 'etwas\<close>
  where
\<open>aenderung_val a \<equiv> case a of Verliert _ n \<Rightarrow> -n | Gewinnt _ n \<Rightarrow> n\<close>

beispiel \<open>aenderung_val (Verliert Alice (2::int)) = -2\<close> by eval
beispiel \<open>aenderung_val (Gewinnt Alice (2::int)) = 2\<close> by eval

lemma betroffen_simps[simp]:
  \<open>betroffen (Gewinnt a ab) = a\<close>
  \<open>betroffen (Verliert a ab) = a\<close>
  by(simp add: betroffen_def)+
lemma aenderung_val_simps[simp]:
  \<open>aenderung_val (Gewinnt a ab) = ab\<close>
  \<open>aenderung_val (Verliert a ab) = -ab\<close>
  by(simp add: aenderung_val_def)+

fun delta_num_map
  :: \<open>(('person::enum \<rightharpoonup> ('etwas::{zero,minus,ord})), 'person, 'etwas) delta\<close>
  where
  \<open>delta_num_map (Handlung vor nach) =
      List.map_filter
        (\<lambda>p. case (the_default (vor p) 0, the_default (nach p) 0)
               of (a,b) \<Rightarrow> delta_num p a b)
        (Enum.enum::'person list)\<close>

beispiel\<open>delta_num_map
  (Handlung [Alice \<mapsto> 5::int, Bob \<mapsto> 10, Eve \<mapsto> 1]
            [Alice \<mapsto> 3, Bob \<mapsto> 13, Carol \<mapsto> 2])
  = [Verliert Alice 2, Gewinnt Bob 3, Gewinnt Carol 2, Verliert Eve 1]\<close> by eval

fun delta_num_fun
  :: \<open>(('person::enum \<Rightarrow> ('etwas::{minus,ord})), 'person, 'etwas) delta\<close>
  where
  \<open>delta_num_fun (Handlung vor nach) =
      List.map_filter (\<lambda>p. delta_num p (vor p) (nach p)) Enum.enum\<close>

beispiel \<open>delta_num_fun
    (Handlung
        ((\<lambda>p. 0::int)(Alice:=8, Bob:=12, Eve:=7))
        ((\<lambda>p. 0::int)(Alice:=3, Bob:=15, Eve:=0)))
  = [Verliert Alice 5, Gewinnt Bob 3, Verliert Eve 7]\<close> by eval

lemma delta_num_map: \<open>delta_num_map (Handlung m1 m2) =
        delta_num_fun (Handlung (\<lambda>p. the_default (m1 p) 0) (\<lambda>p. the_default (m2 p) 0))\<close>
  by(simp)


(*TODO: das if will in die swap.thy?*)
term \<open>map_aenderung\<close>
definition aenderung_swap
  :: \<open>'person \<Rightarrow> 'person \<Rightarrow> ('person, 'etwas) aenderung \<Rightarrow> ('person, 'etwas) aenderung\<close>
where
  \<open>aenderung_swap p1 p2 a \<equiv> map_aenderung (\<lambda>p. if p = p1 then p2 else if p = p2 then p1 else p) id a\<close>

beispiel\<open>aenderung_swap Alice Bob (Gewinnt Alice (3::nat)) = Gewinnt Bob 3\<close> by eval
beispiel\<open>aenderung_swap Alice Bob (Gewinnt Bob (3::nat)) = Gewinnt Alice 3\<close> by eval
beispiel\<open>aenderung_swap Alice Bob (Gewinnt Carol (3::nat)) = Gewinnt Carol 3\<close> by eval


lemma aenderung_swap_id: \<open>aenderung_swap p1 p2 (aenderung_swap p1 p2 a) = a\<close>
  apply(simp add: aenderung_swap_def)
  apply(cases \<open>a\<close>)
  by simp_all

lemma aenderung_swap_sym: \<open>aenderung_swap p1 p2 = aenderung_swap p2 p1\<close>
  apply(simp add: fun_eq_iff aenderung_swap_def, intro allI, rename_tac a)
  apply(case_tac \<open>a\<close>)
  by simp_all

lemma map_map_aenderung_swap:
  \<open>map (map (aenderung_swap p1 p2)) \<circ> (map (map (aenderung_swap p1 p2)) \<circ> kons) = kons\<close>
  by(simp add: fun_eq_iff aenderung_swap_id comp_def)

lemma swap_map_map_aenderung_swap:
  \<open>swap p2 p1 (map (map (aenderung_swap p2 p1)) \<circ> swap p1 p2 (map (map (aenderung_swap p1 p2)) \<circ> kons))
  = kons\<close>
  apply(subst aenderung_swap_sym)
  apply(subst swap_symmetric)
  apply(subst swap_fun_comp_id)
  apply(simp add: map_map_aenderung_swap)
  done
(*>*)


text\<open>Eine Liste von Änderungen lässt sich ausführen.\<close>
fun aenderung_ausfuehren
  :: \<open>('person, 'etwas::{plus,minus}) aenderung list \<Rightarrow> ('person \<Rightarrow> 'etwas) \<Rightarrow> ('person \<Rightarrow> 'etwas)\<close>
where
  \<open>aenderung_ausfuehren [] bes = bes\<close>
| \<open>aenderung_ausfuehren (Verliert p n # deltas) bes = aenderung_ausfuehren deltas \<lbrakk>bes(p -= n)\<rbrakk>\<close>
| \<open>aenderung_ausfuehren (Gewinnt p n # deltas) bes = aenderung_ausfuehren deltas \<lbrakk>bes(p += n)\<rbrakk>\<close>

text\<open>Die lokale Variable \<^term_type>\<open>bes :: ('person \<Rightarrow> 'etwas)\<close> stellt dabei den
aktuellen Besitz dar.
Die Ausgabe der Funktion ist der modifizierte Besitz, nachdem die Änderung ausgeführt wurde.\<close>

beispiel
\<open>aenderung_ausfuehren
  [Verliert Alice (2::int), Gewinnt Bob 3, Gewinnt Carol 2, Verliert Eve 1]
  (\<euro>(Alice:=8, Bob:=3, Eve:= 5))
  =
  (\<euro>(Alice:=6, Bob:=6, Carol:=2, Eve:= 4))\<close>
  by eval

beispiel
\<open>aenderung_ausfuehren
  [Verliert Alice (2::int), Verliert Alice 6]
  (\<euro>(Alice:=8, Bob:=3, Eve:= 5))
  =
  (\<euro>(Bob:=3, Eve:= 5))\<close>
  by eval
text\<open>Im vorherigen Beispiel verliert \<^const>\<open>Alice\<close> alles.
Da sie nun den \<^const>\<open>DEFAULT\<close>-Wert von \<^term>\<open>0::int\<close> besitzt, wird ihre Besitz nicht angezeigt.\<close>

(*<*)
(*TODO: upstream und vereinfachen!*)
lemma swap_aenderung_ausfuehren:
  \<open>swap p1 p2 (Aenderung.aenderung_ausfuehren a bes)
      = Aenderung.aenderung_ausfuehren (map (aenderung_swap p1 p2) a) (swap p1 p2 bes)\<close>
  apply(induction \<open>a\<close> arbitrary: \<open>bes\<close>)
   apply(simp)
  apply(simp)
  apply(case_tac \<open>a1\<close>)
  subgoal
    apply(simp)
    apply(simp add: aenderung_swap_def, safe)
      apply (simp_all add: fun_upd_twist swap_def Fun.swap_def)
    done
  apply(simp)
    apply(simp add: aenderung_swap_def, safe)
    apply (simp_all add: fun_upd_twist swap_def Fun.swap_def)
  done
(*>*)

subsection\<open>Abmachungen\<close>
text\<open>Eine \<^typ>\<open>('person, 'etwas) aenderung list\<close> wie
z.B. \<^term>\<open>[Gewinnt Alice (3::int), Verliert Bob 3]\<close> ließe sich gut verwenden,
um eine Abmachung zwischen \<^const>\<open>Alice\<close> und \<^const>\<open>Bob\<close> zu modellieren.
Allerdings ist diese Darstellung unpraktisch zu benutzen.
Beispielsweise sind

  \<^item> \<^term>\<open>[Gewinnt Alice (3::int), Verliert Bob 3]\<close>
  \<^item> \<^term>\<open>[Verliert Bob 3, Gewinnt Alice (3::int)]\<close>
  \<^item> \<^term>\<open>[Gewinnt Alice (1::int), Gewinnt Alice 1, Gewinnt Alice 1, Verliert Bob 3, Verliert Carol 0]\<close>

extensional betrachtet alle equivalent.
Es ist praktischer, eine Darstellung zu wählen,
in der syntaktische und semantische Äquivalenz zusammenfallen.
Das bedeutet, eine Abmachung muss eindeutig dargestellt werden.
Ein Kandidat dafür wäre eine Map vom Typ \<^typ>\<open>'person \<rightharpoonup> 'etwas\<close>, da diese eindeutig einer
\<^typ>\<open>'person\<close> ein \<^typ>\<open>'etwas\<close> zuordnet.
Dies funktioniert allerdings nur, wenn @{typ [source=true] \<open>'etwas::{uminus,plus}\<close>} mit Plus und Minus
dargestellt werden kann, um \<^const>\<open>Gewinnt\<close> und \<^const>\<open>Verliert\<close> darzustellen.
Allerdings ist auch diese Darstellung nicht eindeutig,
da z.B. \<^term>\<open>[Alice \<mapsto> 0] = Map.empty\<close> semantisch gilt,
solange \<^term>\<open>0\<close> ein neutrales Element ist.
Deshalb stellen wir eine Abmachung als eine
totale Funktion vom Typ @{typ [source=true] \<open>'person \<Rightarrow> ('etwas::{uminus, plus, zero})\<close>} dar.
Der Term \<^term>\<open>(\<lambda>_. 0)(Alice := 3, Bob := -3)\<close> bedeutet \<^const>\<open>Alice\<close> bekommt 3, \<^const>\<open>Bob\<close> verliert 3.
\<close>
type_synonym  ('person, 'etwas) abmachung = \<open>'person \<Rightarrow> 'etwas\<close>


text\<open>Folgende Funktion konvertiert eine Liste von Änderungen in ein Abmachung.
Persönlich finde ich es schöner eine Liste von Änderungen aufzuschreiben,
mathematisch ist eine Abmachung allerdings überlegen.
Folgende Funktion sorgt dafür, dass wir Abmachungen dennoch als
Liste von Änderungen aufschreiben können, dann allerdings mit der Abmachung weiterrechnen.\<close>
fun to_abmachung
  :: \<open>('person, 'etwas::{ord,zero,plus,minus,uminus}) aenderung list \<Rightarrow> ('person, 'etwas) abmachung\<close>
where
  \<open>to_abmachung [] = (\<lambda>p. 0)\<close>
| \<open>to_abmachung (delta # deltas) = 
   \<lbrakk>(to_abmachung deltas)(betroffen delta += aenderung_val delta)\<rbrakk>\<close>


beispiel \<open>[to_abmachung [Gewinnt Alice (3::int)], to_abmachung [Gewinnt Alice 3, Verliert Bob 3]]
        = [(\<lambda>p.0)(Alice := 3), (\<lambda>p.0)(Alice := 3, Bob := -3)]\<close> by eval


(*<*)
lemma to_abmachung_simp_call:
  \<open>to_abmachung (delta # deltas) p =
    (if p = betroffen delta
     then (to_abmachung deltas p) + (aenderung_val delta)
     else (to_abmachung deltas p))\<close>
  by(simp)

lemma to_abmachung_fold_induct_helper:
  fixes as :: \<open>('person, 'etwas::ordered_ab_group_add) aenderung list\<close>
  shows \<open>fold (\<lambda>a acc. \<lbrakk>acc(betroffen a += aenderung_val a)\<rbrakk>) as abmachung =
    (\<lambda>p. to_abmachung as p + abmachung p)\<close>
  apply(induction \<open>as\<close> arbitrary:\<open>abmachung\<close>)
  by(simp add: fun_eq_iff)+
lemma to_abmachung_fold:
  fixes as :: \<open>('person, 'etwas::ordered_ab_group_add) aenderung list\<close>
  shows \<open>to_abmachung as = fold (\<lambda>a acc. \<lbrakk>acc(betroffen a += aenderung_val a)\<rbrakk>) as (\<lambda>_. 0)\<close>
  apply(subst to_abmachung_fold_induct_helper[where abmachung=\<open>\<lambda>_. 0\<close>])
  by simp

lemma to_abmachung_List_map_filter_simp_call:
  fixes f :: \<open>'person::enum \<Rightarrow> ('person, 'etwas::ordered_ab_group_add) aenderung option\<close>
  assumes valid_f: \<open>\<And>p a. f p = Some a \<Longrightarrow> betroffen a = p\<close>
  shows
  \<open>p \<in> set as \<Longrightarrow> distinct as \<Longrightarrow>
   to_abmachung (List.map_filter f as) p =
    (case f p of Some a \<Rightarrow> to_abmachung [a] p | None \<Rightarrow> 0)\<close>
proof(induction \<open>as\<close>)
  case Nil
  then show \<open>?case\<close> by simp
next
  case (Cons a as)
  have filter_not_in_set:
    \<open>p \<notin> set ps \<Longrightarrow> to_abmachung (List.map_filter f ps) p = 0\<close> for p ps
    apply(induction \<open>ps\<close>)
    apply(simp add: List.map_filter_simps)
    apply(simp add: List.map_filter_simps split:option.split)
    apply(clarsimp, rename_tac a ps a2)
    apply(subgoal_tac \<open>betroffen a2 = a\<close>)
     apply simp
    by(auto dest: valid_f)

  from Cons show \<open>?case\<close>
    apply(simp add: List.map_filter_simps)
    apply(safe)
     apply(case_tac \<open>f p\<close>)
      apply(simp add: filter_not_in_set; fail)
     apply(simp add: filter_not_in_set)
    using filter_not_in_set apply blast
    apply(simp)
     apply(case_tac \<open>f a\<close>)
      apply(simp add: filter_not_in_set; fail)
    apply(simp add: filter_not_in_set)
    by(auto dest: valid_f)
qed

lemma to_abmachung_List_map_filter_enum_simp_call:
fixes f :: \<open>'person::enum \<Rightarrow> ('person, 'etwas::ordered_ab_group_add) aenderung option\<close>
  assumes valid_f: \<open>\<And>p a. f p = Some a \<Longrightarrow> betroffen a = p\<close>
  shows
  \<open>to_abmachung (List.map_filter f Enum.enum) p =
    (case f p of Some a \<Rightarrow> to_abmachung [a] p | None \<Rightarrow> 0)\<close>
  apply(rule to_abmachung_List_map_filter_simp_call)
  using valid_f apply(simp)
   apply(simp add: enum_class.enum_UNIV)
  apply(simp add: enum_class.enum_distinct)
  done

fun abmachung_to_aenderung_list
  :: \<open>'person list \<Rightarrow> ('person, 'etwas::{ord,zero,plus,minus,uminus}) abmachung \<Rightarrow> ('person, 'etwas) aenderung list\<close>
where
  \<open>abmachung_to_aenderung_list [] _ = []\<close>
| \<open>abmachung_to_aenderung_list (p#ps) a =
    (if a p = 0
     then abmachung_to_aenderung_list ps a
     else (if a p > 0 then Gewinnt p (a p) else Verliert p (- (a p))) # abmachung_to_aenderung_list ps a
    )\<close>

definition abmachung_to_aenderung
  :: \<open>('person::enum, 'etwas::{ord,zero,plus,minus,uminus}) abmachung \<Rightarrow> ('person, 'etwas) aenderung list\<close>
where
  \<open>abmachung_to_aenderung \<equiv> abmachung_to_aenderung_list Enum.enum\<close>

beispiel \<open>abmachung_to_aenderung ((\<lambda>p.0)(Alice := (3::int), Bob := -3))
            = [Gewinnt Alice 3, Verliert Bob 3]\<close> by eval


definition aenderung_to_abmachung
  :: \<open>('person, 'etwas) aenderung list \<Rightarrow> ('person::enum, 'etwas::{ord,zero,plus,minus,uminus}) abmachung\<close>
where
  \<open>aenderung_to_abmachung \<equiv> to_abmachung\<close>

lemma fixes as :: \<open>('person::enum, int) aenderung list\<close>
  shows \<open>abmachung_to_aenderung (aenderung_to_abmachung as) = as\<close>
  (* nitpick as = [Verliert person\<^sub>1 (- 1)] *)
  oops (*gilt nicht, weil aenderungen nicht eindeutig*)


lemma abmachung_to_aenderung_list_to_abmachung_not_in_ps:
  \<open>p \<notin> set ps \<Longrightarrow>  to_abmachung (abmachung_to_aenderung_list ps a) p = 0\<close>
  by(induction \<open>ps\<close>) simp+

lemma abmachung_to_aenderung_list_not_in_ps:
  \<open>p \<notin> set ps \<Longrightarrow>
       abmachung_to_aenderung_list ps (a(p := v)) = abmachung_to_aenderung_list ps a\<close>
  apply(induction \<open>ps\<close>)
   apply(simp)
  apply(simp)
  by fastforce


definition abmachung_dom :: \<open>('person, 'etwas::zero) abmachung \<Rightarrow> 'person set\<close> where
  \<open>abmachung_dom m = {a. m a \<noteq> 0}\<close>

lemma abmachung_dom_swap:
  \<open>abmachung_dom (swap p1 p2 a) = (swap p1 p2 id) ` (abmachung_dom a)\<close>
  apply(simp add: abmachung_dom_def)
  apply(simp add: image_def)
  apply(rule Collect_cong)
  apply(simp add: swap_def Fun.swap_def)
  by fast

lemma to_abmachung_abmachung_to_aenderung_list_induct_helper:
  fixes a :: \<open>('person::enum, 'etwas::ordered_ab_group_add) abmachung\<close>
  shows \<open>abmachung_dom a \<subseteq> set ps \<Longrightarrow> distinct ps \<Longrightarrow> to_abmachung (abmachung_to_aenderung_list ps a) = a\<close>
  apply(induction \<open>ps\<close> arbitrary: \<open>a\<close>)
   apply(simp add: abmachung_dom_def)
   apply fastforce
  apply(rename_tac p ps a)
  apply(simp)
  apply(simp add: abmachung_to_aenderung_list_to_abmachung_not_in_ps)
  apply(case_tac \<open>p \<notin> abmachung_dom a\<close>)
   apply(subgoal_tac \<open>abmachung_dom a \<subseteq> set ps\<close>)
    apply(simp add: abmachung_dom_def; fail)
   apply(simp add: abmachung_dom_def)
   apply blast
  apply(subgoal_tac \<open>abmachung_dom (a(p := 0)) \<subseteq> set ps\<close>)
   prefer 2
   apply(simp add: abmachung_dom_def)
   apply blast
  apply(subgoal_tac \<open>to_abmachung (abmachung_to_aenderung_list ps a) = (a(p := 0))\<close>) (*instantiate IH*)
   prefer 2
   apply(simp)
   apply (metis abmachung_to_aenderung_list_not_in_ps)
  apply(simp)
  by fastforce

lemma aenderung_to_abmachung_abmachung_to_aenderung:
  fixes a :: \<open>('person::enum, 'etwas::ordered_ab_group_add) abmachung\<close>
  shows \<open>aenderung_to_abmachung (abmachung_to_aenderung a) = a\<close>
  apply(simp add: abmachung_to_aenderung_def aenderung_to_abmachung_def)
  apply(rule to_abmachung_abmachung_to_aenderung_list_induct_helper)
   apply(simp add: enum_class.enum_UNIV)
  apply(simp add: enum_class.enum_distinct)
  done
(*>*)



text\<open>Personen, welche von einer Abmachung betroffen sind.\<close>
definition abmachungs_betroffene :: \<open>('person::enum, 'etwas::zero) abmachung \<Rightarrow> 'person list\<close>
where
  \<open>abmachungs_betroffene a \<equiv> [p. p \<leftarrow> Enum.enum, a p \<noteq> 0]\<close>

beispiel \<open>abmachungs_betroffene (to_abmachung [Gewinnt Bob (3::int), Verliert Alice 3])
  = [Alice, Bob]\<close> by eval


(*<*)
lemma abmachungs_betroffene_simp: \<open>abmachungs_betroffene a = filter (\<lambda>p. a p \<noteq> 0) Enum.enum\<close>
proof -
  have \<open>concat (map (\<lambda>p. if a p \<noteq> 0 then [p] else []) as) = filter (\<lambda>p. a p \<noteq> 0) as\<close> for as
    by(induction \<open>as\<close>) auto
  thus \<open>?thesis\<close>
    by(simp add: abmachungs_betroffene_def)
qed

lemma abmachungs_betroffene_distinct: \<open>distinct (abmachungs_betroffene a)\<close>
  apply(simp add: abmachungs_betroffene_simp)
  using enum_class.enum_distinct distinct_filter by blast

lemma abmachungs_betroffene_is_dom: \<open>set (abmachungs_betroffene a) = abmachung_dom a\<close>
  by(simp add: abmachung_dom_def abmachungs_betroffene_simp enum_class.enum_UNIV)

lemma set_abmachungs_betroffene_swap:
  \<open>set (abmachungs_betroffene (swap p1 p2 a)) = (swap p1 p2 id) ` set (abmachungs_betroffene a)\<close>
  apply(simp add: abmachungs_betroffene_simp enum_class.enum_UNIV)
  apply(simp add: image_def)
  apply(rule Collect_cong)
  apply(simp add: swap_def Fun.swap_def)
  by fast
(*>*)

text\<open>Eine Abmachung lässt sich ausführen.
Dabei wird effektiv die gegebene \<^term>\<open>besitz::('person \<Rightarrow> 'etwas)\<close> Funktion upgedated.\<close>
definition abmachung_ausfuehren
  :: \<open>('person, 'etwas::{plus,minus}) abmachung \<Rightarrow> ('person \<Rightarrow> 'etwas) \<Rightarrow> ('person \<Rightarrow> 'etwas)\<close>
where
  \<open>abmachung_ausfuehren a besitz \<equiv> \<lambda>p. a p + (besitz p)\<close>

beispiel
  \<open>abmachung_ausfuehren
    (to_abmachung [Gewinnt Alice 3, Verliert Bob 3])
    (\<euro>(Alice:=8, Bob:=3, Eve:= 5))
  = (\<euro>(Alice:=11, Bob:=0, Eve:= 5))\<close>
  by(code_simp)


(*<*)
lemma abmachung_ausfuehren_swap:
  \<open>abmachung_ausfuehren (swap p1 p2 a) (swap p1 p2 welt)
    = swap p2 p1 (abmachung_ausfuehren a welt)\<close>
  by(auto simp add: abmachung_ausfuehren_def swap_def Fun.swap_def)

lemma aenderung_ausfuehren_abmachung_to_aenderung_induction_helper:
  fixes welt :: \<open>'person::enum \<Rightarrow> 'etwas::ordered_ab_group_add\<close>
  shows \<open>abmachung_dom abmachung \<subseteq> set ps \<Longrightarrow> distinct ps \<Longrightarrow> 
          aenderung_ausfuehren (abmachung_to_aenderung_list ps abmachung) welt p =
            welt p + (abmachung p)\<close>
  apply(induction \<open>ps\<close> arbitrary: \<open>abmachung\<close> \<open>welt\<close>)
   apply(simp add: abmachung_dom_def; fail)
  apply(simp)
  apply(rename_tac pa ps abmachung welt)
  apply(subgoal_tac \<open>abmachung_dom (abmachung(pa := 0)) \<subseteq> set ps\<close>)
   prefer 2
  subgoal
    apply(simp add: abmachung_dom_def)
    by blast
(*thank you sledgehammer isar proofs*)
proof -
  fix pa :: \<open>'person\<close> and psa :: \<open>'person list\<close> and abmachunga :: \<open>'person \<Rightarrow> 'etwas\<close> and welta :: \<open>'person \<Rightarrow> 'etwas\<close>
  assume a1: \<open>pa \<notin> set psa \<and> distinct psa\<close>
  assume a2: \<open>abmachung_dom (abmachunga(pa := 0)) \<subseteq> set psa\<close>
  assume \<open>\<And>abmachung welt. abmachung_dom abmachung \<subseteq> set psa \<Longrightarrow> aenderung_ausfuehren (abmachung_to_aenderung_list psa abmachung) welt p = (welt p::'etwas) + abmachung p\<close>
  then have f3: \<open>\<And>f. f p + (abmachunga(pa := 0)) p = aenderung_ausfuehren (abmachung_to_aenderung_list psa abmachunga) f p\<close>
    using a2 a1 by (metis (full_types) abmachung_to_aenderung_list_not_in_ps)
  then have \<open>pa = p \<longrightarrow> (0 < abmachunga pa \<longrightarrow> abmachunga pa \<noteq> 0 \<longrightarrow> aenderung_ausfuehren (abmachung_to_aenderung_list psa abmachunga) \<lbrakk>welta (pa += abmachunga pa)\<rbrakk> p = welta p + abmachunga p) \<and> (\<not> 0 < abmachunga pa \<longrightarrow> (abmachunga pa = 0 \<longrightarrow> aenderung_ausfuehren (abmachung_to_aenderung_list psa abmachunga) welta p = welta p + abmachunga p) \<and> (abmachunga pa \<noteq> 0 \<longrightarrow> aenderung_ausfuehren (abmachung_to_aenderung_list psa abmachunga) \<lbrakk>welta (pa += abmachunga pa)\<rbrakk> p = welta p + abmachunga p))\<close>
    by force
  then show \<open>(0 < abmachunga pa \<longrightarrow> abmachunga pa \<noteq> 0 \<longrightarrow> aenderung_ausfuehren (abmachung_to_aenderung_list psa abmachunga) \<lbrakk>welta (pa += abmachunga pa)\<rbrakk> p = welta p + abmachunga p) \<and> (\<not> 0 < abmachunga pa \<longrightarrow> (abmachunga pa = 0 \<longrightarrow> aenderung_ausfuehren (abmachung_to_aenderung_list psa abmachunga) welta p = welta p + abmachunga p) \<and> (abmachunga pa \<noteq> 0 \<longrightarrow> aenderung_ausfuehren (abmachung_to_aenderung_list psa abmachunga) \<lbrakk>welta (pa += abmachunga pa)\<rbrakk> p = welta p + abmachunga p))\<close>
    using f3 by (metis fun_upd_other)
qed


lemma aenderung_ausfuehren_abmachung_to_aenderung:
  fixes welt :: \<open>'person::enum \<Rightarrow> 'etwas::ordered_ab_group_add\<close>
  shows \<open>aenderung_ausfuehren (abmachung_to_aenderung abmachung) welt p = welt p + (abmachung p)\<close>
  apply(simp add: abmachung_to_aenderung_def)
  apply(rule aenderung_ausfuehren_abmachung_to_aenderung_induction_helper)
   apply(simp add: enum_class.enum_UNIV)
  apply(simp add: enum_class.enum_distinct)
  done

(*>*)


text\<open>Es ist equivalent eine Abmachung oder die entsprechende Änderungsliste auszuführen.\<close>
(*TODO: does this make a good [code] rule? I cannot measure performance changes.*)
lemma abmachung_ausfuehren_aenderung:
  fixes abmachung :: \<open>('person::enum, 'etwas::ordered_ab_group_add) abmachung\<close>
  shows \<open>abmachung_ausfuehren abmachung = aenderung_ausfuehren (abmachung_to_aenderung abmachung)\<close>
  by(simp add: abmachung_ausfuehren_def fun_eq_iff aenderung_ausfuehren_abmachung_to_aenderung)


subsection\<open>Konsens\<close>
text\<open>Laut \<^url>\<open>https://de.wikipedia.org/wiki/Konsens#Konsens_im_Rechtssystem\<close> lässt sich Konsens
wie folgt definieren:
"die Übereinstimmung der Willenserklärungen beider Vertragspartner über die Punkte des Vertrages".
Wir können also \<^term>\<open>to_abmachung [Gewinnt Alice 3, Verliert Bob 3]\<close> verwenden,
um Konsens zu modellieren.
Dabei müssen alle Betroffenen die gleiche Vorstellung der Abmachung haben.
Beispielsweise lässt sich der gesamte Konsens in einer Welt darstellen als
\<^typ>\<open>'person \<Rightarrow> ('person, 'etwas) abmachung list\<close>, wobei jeder Person genau die Abmachungen
zugeordnet werden, deren sie zustimmt.
Die Abmachungen sind in einer Liste und keiner Menge, da eine Person eventuell bereit ist,
Abmachungen mehrfach auszuführen.
\<close>

type_synonym ('person, 'etwas) globaler_konsens = \<open>'person \<Rightarrow> ('person, 'etwas) abmachung list\<close>

text\<open>
Folgendes Beispiel liest sich wie folgt:

\<^term>\<open>(\<lambda>_. [])(
    Alice := [to_abmachung [Gewinnt Alice 3], to_abmachung [Gewinnt Alice 3, Verliert Bob 3]],
    Bob := [to_abmachung [Gewinnt Alice 3, Verliert Bob 3]]) :: (person, int) globaler_konsens\<close>

\<^const>\<open>Alice\<close> stimmt folgendem zu:
  \<^item> \<^const>\<open>Alice\<close> bekommt 3.
  \<^item> \<^const>\<open>Alice\<close> bekommt 3 und \<^const>\<open>Bob\<close> muss 3 abgeben.

\<^const>\<open>Bob\<close> stimmt folgendem zu:
  \<^item> \<^const>\<open>Alice\<close> bekommt 3 und \<^const>\<open>Bob\<close> muss 3 abgeben.

Wir könnten also sagen, dass Konsens zwischen \<^const>\<open>Alice\<close> und \<^const>\<open>Bob\<close> herrscht,
dass 3 Besitz von \<^const>\<open>Bob\<close> auf \<^const>\<open>Alice\<close> übergehen.
Zusätzlich wäre es in diesem Beispiel auch okay für \<^const>\<open>Alice\<close>,
wenn sie 3 Besitz erhalten würde, ohne dass \<^const>\<open>Bob\<close> 3 Besitz verliert.
\<close>

(*<*)
definition konsensswap
:: \<open>'person \<Rightarrow> 'person \<Rightarrow> ('person, 'etwas) globaler_konsens
    \<Rightarrow> ('person, 'etwas) globaler_konsens\<close>
  where
\<open>konsensswap p1 p2 kons \<equiv> swap p1 p2 ((map (swap p1 p2)) \<circ> kons)\<close>

lemma konsensswap_id[simp]: \<open>konsensswap p1 p2 (konsensswap p1 p2 kons) = kons\<close>
  apply(simp add: konsensswap_def)
  apply(subst swap_fun_map_comp_id)
  by simp

lemma konsensswap_sym: \<open>konsensswap p1 p2 = konsensswap p2 p1\<close>
  by(simp add: fun_eq_iff konsensswap_def swap_symmetric)

lemma konsensswap_apply:
  \<open>konsensswap p1 p2 kons p =  map (swap p1 p2) (swap p1 p2 kons p)\<close>
  apply(simp add: konsensswap_def comp_def)
  by(rule swap_cases, simp_all add: swap_a swap_b swap_nothing)

lemma konsensswap_same[simp]:
  \<open>konsensswap p p konsens = konsens\<close>
  by(simp add: konsensswap_def swap_id_comp)

lemma konsensswap_swap_id:
  \<open>konsensswap p1 p2 konsens (swap p1 p2 id p) = map (swap p1 p2) (konsens p)\<close>
  apply(simp add: konsensswap_apply)
  by (simp add: swap_fun_swap_id)
(*>*)


text\<open>Folgendes Prädikat prüft, ob für eine gegebene Abmachung Konsens herrscht.\<close>
definition enthaelt_konsens
  :: \<open>('person::enum, 'etwas::zero) abmachung \<Rightarrow> ('person, 'etwas) globaler_konsens \<Rightarrow> bool\<close>
where
  \<open>enthaelt_konsens abmachung konsens \<equiv> \<forall>betroffene_person \<in> set (abmachungs_betroffene abmachung).
      abmachung \<in> set (konsens betroffene_person)\<close>

(*<*)
lemma swap_konsensswap_swap:
  \<open>swap p2 p1 ` set (konsensswap p1 p2 konsens (swap p1 p2 id p)) =
  (set (konsens p))\<close>
  apply(simp add: konsensswap_apply)
  apply(simp add: swap_fun_swap_id)
  by (simp add: image_comp)

lemma enthaelt_konsens_swap:
  \<open>enthaelt_konsens (swap p1 p2 a) (konsensswap p1 p2 konsens) = enthaelt_konsens a konsens\<close> 
  apply(simp add: enthaelt_konsens_def abmachungs_betroffene_is_dom)
  apply(simp add: abmachung_dom_swap)
  apply(rule ball_cong)
   apply(simp; fail)
  by(simp add: swap_in_set_of_functions swap_konsensswap_swap)
(*>*)


text\<open>Eine (ausgeführte) Abmachung einlösen, bzw. entfernen.\<close>
definition konsens_entfernen
 :: \<open>('person::enum, 'etwas::zero) abmachung \<Rightarrow> ('person \<Rightarrow> ('person, 'etwas) abmachung list)
   \<Rightarrow> ('person \<Rightarrow> ('person, 'etwas) abmachung list)\<close>
 where
\<open>konsens_entfernen abmachung kons =
      fold (\<lambda>p k. k(p := remove1 abmachung (k p))) (abmachungs_betroffene abmachung) kons\<close>


beispiel
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
  \<open>a \<notin> set as \<Longrightarrow> fold (\<lambda>a k. k(a := f (k a))) as kons a = kons a\<close>
  by(induction \<open>as\<close> arbitrary: \<open>kons\<close>) simp+
lemma konsens_entfernen_fold_induct_helper:
  \<open>x \<in> set as \<Longrightarrow> distinct as \<Longrightarrow>
         fold (\<lambda>a k. k(a := f (k a))) as kons x = f (kons x)\<close>
  apply(induction \<open>as\<close> arbitrary: \<open>kons\<close>)
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
  \<open>konsens_entfernen a kons
    = (\<lambda>p. if p \<in> set (abmachungs_betroffene a) then remove1 a (kons p) else (kons p))\<close>
  apply(simp add: konsens_entfernen_def fun_eq_iff)
  apply(intro allI conjI impI)
   apply(subst konsens_entfernen_fold_induct_helper, simp_all)
   apply(simp add: abmachungs_betroffene_distinct)
  apply(simp add: konsens_entfernen_fold_induct_helper_helper)
  done


(*<*)  
lemma remove1_konsensswap:
  \<open>remove1 (swap p1 p2 a) (konsensswap p1 p2 kons p)
    = map (swap p1 p2) (remove1 a (swap p1 p2 kons p))\<close>
  by(simp add: konsensswap_apply remove1_swap)

lemma konsens_entfernen_konsensswap:
  \<open>konsensswap p2 p1 (konsens_entfernen (swap p1 p2 a) (konsensswap p1 p2 kons))
    = konsens_entfernen a kons\<close>
  apply(simp add: konsens_entfernen_simp fun_eq_iff)
  apply(safe)
   apply(simp add: set_abmachungs_betroffene_swap)
   apply(simp add: konsensswap_apply)
   apply(simp add: swap_if_move_inner)
   apply(simp add: swap_id_in_set)
   apply(subst(2) remove1_swap2[of \<open>p1\<close> \<open>p2\<close>, symmetric])
   apply(auto simp add: konsensswap_apply swap_def Fun.swap_def)[1] (*wants helper*)

  apply(simp add: set_abmachungs_betroffene_swap)
  apply(simp add: konsensswap_apply)
  apply(simp add: swap_if_move_inner)
  apply(simp add: swap_id_in_set)
  apply(simp add: konsensswap_apply swap_def comp_def)
  by (simp add: transpose_commute)

lemma to_abmachung_delta_num_fun_simp_call:
  (*stronger than the usual ordered_ab_group_add*)
  fixes vor::\<open>('person::enum \<Rightarrow> 'etwas::linordered_ab_group_add)\<close>
  shows \<open>to_abmachung (delta_num_fun (Handlung vor nach)) p = nach p - vor p\<close>
  apply(simp)
  apply(subst to_abmachung_List_map_filter_enum_simp_call)
  subgoal by(auto simp add: delta_num_def split: if_split_asm)
  by(simp add: delta_num_def)
(*>*)

text\<open>Folgendes Prädikat prüft ob eine Abmachung korrekt aus dem Konsens entfernt wurde.
Dies sollte normalerweise direkt nachdem eine Abmachung eingelöst wurde geschehen.\<close>
definition konsens_wurde_entfernt
  :: \<open>('person::enum, 'etwas::zero) abmachung \<Rightarrow>
      ('person, 'etwas) globaler_konsens \<Rightarrow> ('person, 'etwas) globaler_konsens \<Rightarrow> bool\<close>
where
  \<open>konsens_wurde_entfernt abmachung konsens_vor konsens_nach \<equiv>
    \<forall>betroffene_person \<in> set (abmachungs_betroffene abmachung).
       mset (konsens_vor betroffene_person) = mset (abmachung#(konsens_nach betroffene_person))\<close>

text\<open>Wir müssen hier Multisets (\<^const>\<open>mset\<close>) verwenden,
da eine Abmachung sowohl mehrfach vorkommen kann aber nur einmal eingelöst wird
und die Reihenfolge in welcher die Abmachungen angeordnet sind egal ist.\<close>
(*TODO: will ich multiset von Anfang an verwenden?*)


text\<open>Folgendes gilt nicht \<^term>\<open>konsens_wurde_entfernt a konsens (konsens_entfernen a konsens)\<close>,
da \<^const>\<open>konsens_entfernen\<close> nur einen existierenden Konsens entfernt.
Sollte der gegebene Konsens nicht existieren passiert nichts!
\<close>
beispiel
\<open>konsens = (\<lambda>_. []) \<Longrightarrow> a = to_abmachung [Gewinnt Alice (3::int), Verliert Bob 3]
  \<Longrightarrow> \<not> konsens_wurde_entfernt a konsens (konsens_entfernen a konsens)\<close>
  by(simp, eval)

text\<open>Wenn wir allerdings Konsens haben, dann verhalten sich \<^const>\<open>konsens_wurde_entfernt\<close> und
\<^const>\<open>konsens_entfernen\<close> doch wie erwartet.\<close>
lemma konsens_wurde_entfernt_konsens_entfernen:
  \<open>enthaelt_konsens a konsens \<Longrightarrow> konsens_wurde_entfernt a konsens (konsens_entfernen a konsens)\<close>
  apply(simp add: konsens_wurde_entfernt_def)
  apply(simp add: konsens_entfernen_simp)
  by (simp add: enthaelt_konsens_def)

(*<*)

(*makes the simplifier loop*)
lemma
  \<open>add_mset (swap p1 p2 a) (image_mset (swap p1 p2) M) =
     image_mset (swap p1 p2) (add_mset a M)\<close>
  by simp

lemma konsens_wurde_entfernt_swap:
  \<open>konsens_wurde_entfernt (swap p1 p2 a) (konsensswap p1 p2 konsens_vor) (konsensswap p1 p2 konsens_nach)
    = konsens_wurde_entfernt a konsens_vor konsens_nach\<close> 
  apply(simp add: konsens_wurde_entfernt_def abmachungs_betroffene_is_dom)
  apply(simp add: abmachung_dom_swap)
  apply(rule ball_cong)
   apply(simp; fail)
  apply(simp add: konsensswap_swap_id)
  (*TODO: wow, ugly*)
  by (metis (no_types, opaque_lifting) comp_apply image_mset_add_mset multiset.map_comp multiset.map_ident_strong swap1)
(*>*)

text\<open>Gegeben eine Handlung berechnet folgende Funktion die Abmachung,
aus der diese Handlung resultiert haben könnte.\<close>
definition reverse_engineer_abmachung
  :: \<open>('person::enum \<Rightarrow> 'etwas::linordered_ab_group_add) handlung \<Rightarrow> ('person, 'etwas) abmachung\<close>
where
  \<open>reverse_engineer_abmachung h \<equiv>
    fold (\<lambda>p acc. acc(p := (nachher h p) - (vorher h p))) Enum.enum (\<lambda>_. 0)\<close>

text\<open>Sollte die Abmachung vom Typ \<^typ>\<open>(person, int) abmachung\<close> sein, ist dies eindeutig.\<close>
lemma reverse_engineer_abmachung_delta_num_fun:
  \<open>reverse_engineer_abmachung h = to_abmachung (delta_num_fun h)\<close>
  apply(simp add: fun_eq_iff reverse_engineer_abmachung_def)
  apply(cases \<open>h\<close>, simp del: delta_num_fun.simps)
  apply(subst to_abmachung_delta_num_fun_simp_call)
  apply(subst fold_enum_fun_update_call)
  by simp

(*<*)
lemma reverse_engineer_abmachung_same:
  \<open>reverse_engineer_abmachung (Handlung v v) = (\<lambda>_. 0)\<close>
  by(simp add: reverse_engineer_abmachung_def fun_eq_iff fold_enum_fun_update_call)

lemma reverse_engineer_abmachung_swap:
  \<open>reverse_engineer_abmachung (Handlung (swap p1 p2 vor) (swap p1 p2 nach)) =
        swap p1 p2 (reverse_engineer_abmachung (Handlung vor nach))\<close>
  by(simp add: fun_eq_iff reverse_engineer_abmachung_def fold_enum_fun_update swap_def)
(*>*)

lemma reverse_engineer_abmachung:
  \<open>reverse_engineer_abmachung (Handlung welt welt') = a \<longleftrightarrow> abmachung_ausfuehren a welt = welt'\<close>
  apply(simp add: abmachung_ausfuehren_def fun_eq_iff)
  apply(simp add: reverse_engineer_abmachung_def fold_enum_fun_update_call)
  by (metis add_diff_cancel diff_add_cancel)

end
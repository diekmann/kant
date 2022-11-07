theory FailDraft
imports BeispielZahlenwelt
begin

thm maxime_und_handlungsabsicht_generalisieren_def
(*TODO: aber
maxime_und_handlungsabsicht_generalisieren (Maxime (\<lambda>(ich::person) h. (\<forall>pX. individueller_fortschritt pX h))) (Handlungsabsicht (stehlen4 1 10)) p
gilt damit nicht! Ich brauche was besseres, weniger strenges

definition maxime_und_handlungsabsicht_generalisieren
  :: \<open>('person, 'world) maxime \<Rightarrow> ('person, 'world) handlungsabsicht \<Rightarrow> 'person \<Rightarrow> bool\<close>
 where
  \<open>maxime_und_handlungsabsicht_generalisieren m h p =
    (\<forall>w1 w2. okay m p (handeln p w1 h) \<longleftrightarrow> okay m p (handeln p w2 h))\<close>
*)


(*TODO: experimental. Ist das ne gute Idee? Vermutlich, aber das sollte schon aus der
  wohlgeformten Handlung folgen? Ich brauche etwas, was betroffene Person und handelnde Person
auseinander reisst.*)
definition maxime_und_handlungsabsicht_generalisieren2
  :: \<open>('person, 'world) wp_swap \<Rightarrow> ('person, 'world) maxime \<Rightarrow> ('person, 'world) handlungsabsicht \<Rightarrow>  bool\<close>
where
  \<open>maxime_und_handlungsabsicht_generalisieren2 wps m h =
    (\<forall>w p1 p2. okay m p1 (handeln p1 w h) \<longleftrightarrow> okay m p2 (handeln p2 (wps p1 p2 w) h))\<close>

(*TODO: gut? warum ist da fuer alle welt drinnen?
Auf jeden fall scheint die zahlenwelt das zu moegen.*)
definition maxime_und_handlungsabsicht_generalisieren3
  :: \<open>('person, 'world) wp_swap \<Rightarrow> ('person, 'world) maxime \<Rightarrow> ('person, 'world) handlungsabsicht \<Rightarrow>  bool\<close>
where
  \<open>maxime_und_handlungsabsicht_generalisieren3 wps m h =
    (\<forall>ich p2 welt. okay m ich (handeln ich welt h)
      \<longleftrightarrow> okay m p2 ((map_handlung (wps p2 ich) (handeln ich welt h))))\<close>

(* gilt NICHT fuer generalisierte individueller fortschritt und stehlen4:
definition maxime_und_handlungsabsicht_generalisieren4
  :: \<open>('person, 'world) wp_swap \<Rightarrow> ('person, 'world) maxime \<Rightarrow> ('person, 'world) handlungsabsicht \<Rightarrow>  bool\<close>
where
  \<open>maxime_und_handlungsabsicht_generalisieren4 wps m h =
    (\<forall>ich p2 welt. okay m ich (handeln ich welt h)
      \<longleftrightarrow> okay m ich ((map_handlung (wps p2 ich) (handeln p2 welt h))))\<close>
*)







(*TODO: das ganze in eine Fail.thy*)
fun handeln_partial :: \<open>'person \<Rightarrow> 'world \<Rightarrow> ('person \<Rightarrow> 'world \<Rightarrow> 'world option) \<Rightarrow> 'world handlung\<close> where
\<open>handeln_partial handelnde_person welt h = 
 (case h handelnde_person welt of None \<Rightarrow> Handlung welt welt
                             | Some welt' \<Rightarrow> Handlung welt welt')\<close>

fun stehlen4_partial :: \<open>int \<Rightarrow> int \<Rightarrow> person \<Rightarrow> zahlenwelt \<Rightarrow> zahlenwelt option\<close> where
    \<open>stehlen4_partial beute opfer_nach_besitz dieb (Zahlenwelt besitz) =
      (case opfer_eindeutig_nach_besitz_auswaehlen opfer_nach_besitz besitz Enum.enum
         of None \<Rightarrow> None
          | Some opfer \<Rightarrow> if opfer = dieb
                          then None
                          else Some (Zahlenwelt (besitz(opfer -= beute)(dieb += beute)))
      )\<close>

definition maxime_und_handlungsabsicht_generalisieren_partial
  :: \<open>('person, 'world) maxime \<Rightarrow> ('person \<Rightarrow> 'world \<Rightarrow> 'world option) \<Rightarrow> 'person \<Rightarrow> bool\<close>
where
  \<open>maxime_und_handlungsabsicht_generalisieren_partial m h p =
    (\<forall>w1 w2. h p w1 \<noteq> None \<and> h p w2 \<noteq> None \<longrightarrow> okay m p (handeln_partial p w1 h) = okay m p (handeln_partial p w2 h))\<close>

lemma
    \<open>maxime_und_handlungsabsicht_generalisieren_partial
  (Maxime (\<lambda>(ich::person) h. (\<forall>pX. individueller_fortschritt pX h)))
  ((stehlen4_partial 1 10)) p\<close>
  apply(simp add: maxime_und_handlungsabsicht_generalisieren_partial_def maxime_zahlenfortschritt_def, intro allI impI)
  apply(elim exE conjE)
  apply(simp)
  apply(case_tac \<open>w1\<close>, case_tac \<open>w2\<close>, simp)
  apply(simp add: opfer_eindeutig_nach_besitz_auswaehlen_the_single_elem_enumall)
  apply(simp split: option.split_asm if_split_asm)
  by force
lemma
    \<open>maxime_und_handlungsabsicht_generalisieren_partial
  (Maxime (\<lambda>(ich::person) h. (\<forall>pX. individueller_fortschritt pX h)))
  (\<lambda>p w. Some (reset p w)) p\<close>
  apply(simp add: maxime_und_handlungsabsicht_generalisieren_partial_def maxime_zahlenfortschritt_def, intro allI impI)
  apply(case_tac \<open>w1\<close>, case_tac \<open>w2\<close>, simp)
(*Nitpick found a counterexample:
  Skolem constants:
    w1 = Zahlenwelt ((\<lambda>x. _)(p\<^sub>1 := - 2, p\<^sub>2 := 3, p\<^sub>3 := 1, p\<^sub>4 := 0))
    w2 = Zahlenwelt ((\<lambda>x. _)(p\<^sub>1 := 0, p\<^sub>2 := - 1, p\<^sub>3 := - 2, p\<^sub>4 := 0))
    x = (\<lambda>x. _)(p\<^sub>1 := - 2, p\<^sub>2 := 3, p\<^sub>3 := 1, p\<^sub>4 := 0)
    xa = (\<lambda>x. _)(p\<^sub>1 := 0, p\<^sub>2 := - 1, p\<^sub>3 := - 2, p\<^sub>4 := 0)*)
  oops


(*Muss ich partielle handlungen bauen oder kann ich hier einfach no-ops ausschliessen?*)
definition maxime_und_handlungsabsicht_generalisieren_aussernoop
  :: \<open>('person, 'world) maxime \<Rightarrow> ('person, 'world) handlungsabsicht \<Rightarrow> 'person \<Rightarrow> bool\<close>
where
  \<open>maxime_und_handlungsabsicht_generalisieren_aussernoop m h p =
    (\<forall>w1 w2. (handeln p w1 h) \<noteq> (Handlung w1 w1) \<and> (handeln p w2 h) \<noteq> (Handlung w2 w2)
      \<longrightarrow> okay m p (handeln p w1 h) = okay m p (handeln p w2 h))\<close>

lemma
    \<open>maxime_und_handlungsabsicht_generalisieren_aussernoop
  (Maxime (\<lambda>(ich::person) h. (\<forall>pX. individueller_fortschritt pX h)))
  (Handlungsabsicht (stehlen4 1 10)) p\<close>
  apply(simp add: maxime_und_handlungsabsicht_generalisieren_aussernoop_def maxime_zahlenfortschritt_def, intro allI impI)
  apply(elim conjE)
  apply(case_tac \<open>w1\<close>, case_tac \<open>w2\<close>, simp)
  apply(simp add: opfer_eindeutig_nach_besitz_auswaehlen_the_single_elem_enumall)
  apply(simp split: option.split_asm if_split_asm)
  done

lemma
    \<open>maxime_und_handlungsabsicht_generalisieren_aussernoop
  (Maxime (\<lambda>(ich::person) h. (\<forall>pX. individueller_fortschritt pX h)))
  (Handlungsabsicht reset) p\<close>
(*
nitpick:
    w1 = Zahlenwelt ((\<lambda>x. _)(p\<^sub>1 := 1, p\<^sub>2 := - 1, p\<^sub>3 := - 2, p\<^sub>4 := 2))  <-- reset ist schlecht fuer p1
    w2 = Zahlenwelt ((\<lambda>x. _)(p\<^sub>1 := 0, p\<^sub>2 := 0, p\<^sub>3 := - 2, p\<^sub>4 := 0))    <--- reset ist okay fuer alle
*)
  oops

lemma
    \<open>\<forall>welt. wohlgeformte_handlungsabsicht zahlenwps welt h \<Longrightarrow>
  maxime_und_handlungsabsicht_generalisieren_aussernoop
  (Maxime (\<lambda>(ich::person) h. (\<forall>pX. individueller_fortschritt pX h)))
  h p\<close>
  apply(simp add: maxime_und_handlungsabsicht_generalisieren_aussernoop_def maxime_zahlenfortschritt_def, intro allI impI)
  apply(elim conjE)
  apply(case_tac \<open>w1\<close>, case_tac \<open>w2\<close>, simp)
  apply(case_tac h, simp)
  apply(simp add: wohlgeformte_handlungsabsicht_def)
  oops (*kann ich eine welt in eine andere durch swappen umbauen, so dass das gilt?
    Vermutlich nicht, Leute koennen ja ganz beliebig besitz haben*)
  



lemma
  \<open>maxime_und_handlungsabsicht_generalisieren2 zahlenwps
    (Maxime (\<lambda>(ich::person) h. (\<forall>pX. individueller_fortschritt pX h))) (Handlungsabsicht (stehlen4 1 10))\<close>
  apply(simp add: maxime_und_handlungsabsicht_generalisieren2_def maxime_zahlenfortschritt_def, intro allI)
  apply(case_tac \<open>w\<close>, simp)
  apply(simp add: opfer_eindeutig_nach_besitz_auswaehlen_the_single_elem_enumall)
  apply(simp split: option.split)
  apply(safe, simp_all)
  using the_single_elem_None_swap apply fastforce
  using the_single_elem_Some_Some_swap apply fast
  using the_single_elem_Some_ex_swap apply fast
  by (metis swap2 the_single_elem_Some_Some_swap)

lemma
  \<open>maxime_und_handlungsabsicht_generalisieren3 zahlenwps
    (Maxime (\<lambda>ich h. individueller_fortschritt ich h)) (Handlungsabsicht (stehlen4 1 10))\<close>
  apply(simp add: maxime_und_handlungsabsicht_generalisieren3_def maxime_zahlenfortschritt_def, intro allI)
  apply(case_tac \<open>welt\<close>, simp)
  apply(simp add: opfer_eindeutig_nach_besitz_auswaehlen_the_single_elem_enumall)
  apply(simp split: option.split)
  apply(safe, simp_all)
  by (simp add: swap_a)
  

lemma
  \<open>maxime_und_handlungsabsicht_generalisieren3 zahlenwps
    (Maxime (\<lambda>(ich::person) h. (\<forall>pX. individueller_fortschritt pX h))) (Handlungsabsicht (stehlen4 1 10))\<close>
  apply(simp add: maxime_und_handlungsabsicht_generalisieren3_def maxime_zahlenfortschritt_def, intro allI)
  apply(case_tac \<open>welt\<close>, simp)
  apply(simp add: opfer_eindeutig_nach_besitz_auswaehlen_the_single_elem_enumall)
  apply(simp split: option.split)
  apply(safe, simp_all)
  by (smt (verit, del_insts) fun_upd_apply swap_b swap_nothing)
  (* hierran arbeite ich gerade*)

  
  



end
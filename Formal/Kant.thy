theory Kant
imports Handlung
begin

text\<open>
Beschreibt ob eine Handlung in einer gegebenen Welt gut ist.
Passt nicht so ganz auf die Definition von Maxime?
TODO: ich sollte Maxime als axiom betrachten.
\<close>
datatype ('person, 'world) Maxime = Maxime "'person \<Rightarrow> 'world Handlung \<Rightarrow> bool"
                                 (*          ich    -> Auswirkung      -> gut/böse  *)

text\<open>Beispiel\<close>
definition maxime_mir_ist_alles_recht :: "('person, 'world) Maxime" where
  "maxime_mir_ist_alles_recht \<equiv> Maxime (\<lambda>_ _. True)"

(*
TODO: in einer Maxime darf keine konkrete Person hardcoded sein.
 Verboten: Maxime (\ich _ -> if ich == "konkrete Person" then ...)
*)


text\<open>
Wir testen:
  * Was wenn jeder so handeln würde?
  * Was wenn jeder diese maxime hätte? Bsp: stehlen und bestohlen werden.
Faktisch: Kreuzprodukt Bevölkerung x Bevölkerung,
          wobei jeder einmal als handelnde Person auftritt
          und einmal als betroffene Person (durch Auswertung der Maxime).
\<close>
definition bevoelkerung :: "'person set" where "bevoelkerung \<equiv> UNIV"
definition wenn_jeder_so_handelt
    :: "'world \<Rightarrow> ('person, 'world) HandlungF \<Rightarrow> ('world Handlung) set"
  where
    "wenn_jeder_so_handelt welt handlung \<equiv>
      (\<lambda>handelnde_person. handeln handelnde_person welt handlung) ` bevoelkerung"
fun was_wenn_jeder_so_handelt_aus_sicht_von
    :: "'world \<Rightarrow> ('person, 'world) HandlungF \<Rightarrow> ('person, 'world) Maxime \<Rightarrow> 'person \<Rightarrow> bool"
  where
    "was_wenn_jeder_so_handelt_aus_sicht_von welt handlung (Maxime m) betroffene_person =
        (\<forall> h \<in> wenn_jeder_so_handelt welt handlung. m betroffene_person h)"
(*forall person world. (Enum person, Bounded person)*)
(*
(*Welt in ihrem aktuellen Zustand. TODO: eigentlich sollten wir für jede mögliche Welt testen!*)
  Zu untersuchende Handlung
*)
definition teste_maxime ::
  "'world \<Rightarrow> ('person, 'world) HandlungF \<Rightarrow> ('person, 'world) Maxime \<Rightarrow> bool" where
"teste_maxime welt handlung maxime \<equiv>
  \<forall>p \<in> bevoelkerung. was_wenn_jeder_so_handelt_aus_sicht_von welt handlung maxime p"

lemma teste_maxime_unfold:
  "teste_maxime welt handlung (Maxime m) =
        (\<forall>p\<in>bevoelkerung. \<forall>x\<in>bevoelkerung. m p (handeln x welt handlung))"
  by(simp add: teste_maxime_def wenn_jeder_so_handelt_def)
lemma teste_maxime_crossproduct_unfold: (*WARNING: rhs not fully simp'ed!*)
  "teste_maxime welt handlung (Maxime m) =
        (\<forall>(p,x)\<in>bevoelkerung\<times>bevoelkerung. m p (handeln x welt handlung))"
  unfolding teste_maxime_unfold by simp

definition teste_maxime_exhaust where
  "teste_maxime_exhaust bevoelk welt handlung maxime \<equiv>
    (case maxime of (Maxime m) \<Rightarrow> 
      list_all (\<lambda>(p,x). m p (handeln x welt handlung)) (List.product bevoelk bevoelk))"

lemma teste_maxime_exhaust: "set b = (UNIV::'person set) \<Longrightarrow>
        teste_maxime welt handlung maxime = teste_maxime_exhaust b welt handlung maxime"
  apply(case_tac maxime, rename_tac m, simp)
  unfolding teste_maxime_crossproduct_unfold teste_maxime_exhaust_def bevoelkerung_def
  apply(simp)
  by(simp add: list_all_iff)
  
  

datatype example_very_finite_population = Alice | Bob
(*lemma UNIV_example_very_finite_world [code_unfold]:
  "UNIV = {AliceHappy, AliceSad, BobHappy, BobSad}"
  by(auto intro:example_very_finite_world.exhaust UNIV_eq_I)
lemma coset_example_very_finite_world [code_unfold]:
  "List.coset [] = {AliceHappy, AliceSad, BobHappy, BobSad}"
  using UNIV_example_very_finite_world by simp*)
lemma bevoelkerung_example_very_finite_population [code_unfold]:
  "bevoelkerung = {Alice, Bob}"
  unfolding bevoelkerung_def
  by(auto intro:example_very_finite_population.exhaust UNIV_eq_I)

declare UNIV_coset[code del]
declare bevoelkerung_def[code del]
code_thms teste_maxime

(*does not replace bevoekerung with the set for this type*)
value[nbe] \<open>teste_maxime
            (42::nat)
            (HandlungF (\<lambda>(person::example_very_finite_population) welt. welt + 1))
            (Maxime (\<lambda>_ _. True))\<close>
value \<open>teste_maxime_exhaust [Alice, Bob]
            (42::nat)
            (HandlungF (\<lambda>(person::example_very_finite_population) welt. welt + 1))
            (Maxime (\<lambda>_ _. True))\<close>
end
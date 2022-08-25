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

lemma "teste_maxime welt handlung (Maxime m) =
        (\<forall>p\<in>bevoelkerung. \<forall>x\<in>bevoelkerung. m p (handeln x welt handlung))"
  by(simp add: teste_maxime_def wenn_jeder_so_handelt_def)
end
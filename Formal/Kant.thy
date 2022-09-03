theory Kant
imports Handlung Gesetz BeispielPerson
begin

text\<open>
Beschreibt ob eine Handlung in einer gegebenen Welt gut ist.
Passt nicht so ganz auf die Definition von Maxime?
TODO: ich sollte Maxime als axiom betrachten.
\<close>
(*TODO: wenn ich Steuersysteme als Maxime encoden will muss ich welten vergleichen.
  Es ist eh ein TODO unten, dass ich alle welten testen muss.
  Um ausfuehrbaren code zu haben sollte eventuell hier noch eine vergleichswelt eingefuehrt werden?
  Oder eine vergleichsperson? Oder kann ich Vergelichspersonsn in die aktuelle maxime encoded,
  z.B. jeder der mehr hat als ich muss mehr steuern zahlen
   (und jeder der weniger hat zahlt weniger steuern?)
   \<forall>p\<in>{p \<in> dom (einkommen::person \<Rightarrow> int option). einkommen p \<ge> ich}
    wenn person::enum dann sollte auch `dom einkommen`:: enum
*)
datatype ('person, 'world) maxime = Maxime "'person \<Rightarrow> 'world handlung \<Rightarrow> bool"
                                 (*          ich    -> Auswirkung      -> gut/böse  *)

text\<open>Beispiel\<close>
definition maxime_mir_ist_alles_recht :: "('person, 'world) maxime" where
  "maxime_mir_ist_alles_recht \<equiv> Maxime (\<lambda>_ _. True)"

(*
TODO: in einer Maxime darf keine konkrete Person hardcoded sein.
 Verboten: Maxime (\ich _ -> if ich == "konkrete Person" then ...)
*)


text\<open>
Wir testen:
  \<^item> Was wenn jeder so handeln würde?
  \<^item> Was wenn jeder diese maxime hätte? Bsp: stehlen und bestohlen werden.
Faktisch: Kreuzprodukt Bevölkerung x Bevölkerung,
          wobei jeder einmal als handelnde Person auftritt
          und einmal als betroffene Person (durch Auswertung der Maxime).
\<close>
definition bevoelkerung :: "'person set" where "bevoelkerung \<equiv> UNIV"
definition wenn_jeder_so_handelt
    :: "'world \<Rightarrow> ('person, 'world) handlungF \<Rightarrow> ('world handlung) set"
  where
    "wenn_jeder_so_handelt welt handlung \<equiv>
      (\<lambda>handelnde_person. handeln handelnde_person welt handlung) ` bevoelkerung"
fun was_wenn_jeder_so_handelt_aus_sicht_von
    :: "'world \<Rightarrow> ('person, 'world) handlungF \<Rightarrow> ('person, 'world) maxime \<Rightarrow> 'person \<Rightarrow> bool"
  where
    "was_wenn_jeder_so_handelt_aus_sicht_von welt handlung (Maxime m) betroffene_person =
        (\<forall> h \<in> wenn_jeder_so_handelt welt handlung. m betroffene_person h)"
(*forall person world. (Enum person, Bounded person)*)
(*
(*Welt in ihrem aktuellen Zustand. TODO: eigentlich sollten wir für jede mögliche Welt testen!*)
  Zu untersuchende Handlung
*)
definition teste_maxime ::
  "'world \<Rightarrow> ('person, 'world) handlungF \<Rightarrow> ('person, 'world) maxime \<Rightarrow> bool" where
"teste_maxime welt handlung maxime \<equiv>
  \<forall>p \<in> bevoelkerung. was_wenn_jeder_so_handelt_aus_sicht_von welt handlung maxime p"

lemma teste_maxime_unfold:
  "teste_maxime welt handlung (Maxime m) =
        (\<forall>p\<in>bevoelkerung. \<forall>x\<in>bevoelkerung. m p (handeln x welt handlung))"
  by(simp add: teste_maxime_def wenn_jeder_so_handelt_def)
lemma "teste_maxime welt handlung (Maxime m) =
        (\<forall>(p,x)\<in>bevoelkerung\<times>bevoelkerung. m p (handeln x welt handlung))"
  unfolding teste_maxime_unfold by simp

text\<open>Versuch eine executable version zu bauen.
Wir müssen die Bevölkerung enumerieren.\<close>
definition teste_maxime_exhaust where
  "teste_maxime_exhaust bevoelk welt handlung maxime \<equiv>
    (case maxime of (Maxime m) \<Rightarrow> 
      list_all (\<lambda>(p,x). m p (handeln x welt handlung)) (List.product bevoelk bevoelk))"

lemma teste_maxime_exhaust_univ: "set b = (UNIV::'person set) \<Longrightarrow>
        teste_maxime welt handlung maxime = teste_maxime_exhaust b welt handlung maxime"
  apply(case_tac maxime, rename_tac m, simp)
  unfolding teste_maxime_unfold teste_maxime_exhaust_def bevoelkerung_def
  apply(simp)
  by(simp add: list_all_iff)

subsection \<open>Making it executable\<close>
  (*TODO: for reasons I do not understand,
    teste_maxime_exhaust [Alice, Bob, Carol, Eve] (not enum) needs [code_unfold]
    but
    teste_maxime_exhaust (enum) needs [code]
    ? ? ?*)
  lemma teste_maxime_exhaust [code]: "teste_maxime = teste_maxime_exhaust enum_class.enum"
    apply(simp add: fun_eq_iff)
    apply(rule allI)+
    apply(rule teste_maxime_exhaust_univ)
    using enum_UNIV by simp
  
  declare teste_maxime_def[code del] \<comment>\<open>Only use executable \<^const>\<open>teste_maxime_exhaust\<close>\<close>
  
subsection \<open>Beispiel\<close>
(*TODO: bekomme ich das irgendwie in einen eignenen namespace?*)

(*this causes
  fun teste_maxime _ _ _ = raise Fail "Kant.teste_maxime";
when we don't use teste_maxime_exhaust.
So when code fails with "Kant.teste_maxime", make sure the 'person implements enum.*)

text\<open>Beispiel: Die Mir-ist-alles-Recht Maxime ist erfüllt.\<close>
lemma \<open>teste_maxime
            (42::nat)
            (HandlungF (\<lambda>(person::person) welt. welt + 1))
            (Maxime (\<lambda>_ _. True))\<close> by eval

text\<open>Beispiel:
Die Welt ist modelliert als eine Abbildung von Person auf Besitz.
Die Maxime sagt, dass Leute immer mehr oder gleich viel wollen, aber nie etwas verlieren wollen.
In einer Welt in der keiner etwas hat, erfuellt die Handlung jemanden 3 zu geben die Maxime.
\<close>
lemma \<open>teste_maxime
            [Alice \<mapsto> (0::nat), Bob \<mapsto> 0, Carol \<mapsto> 0, Eve \<mapsto> 0]
            (HandlungF (\<lambda>person welt. welt(person \<mapsto> 3)))
            (Maxime (\<lambda>person handlung. (the ((vorher handlung) person)) \<le> (the ((nachher handlung) person))))\<close>
  by eval
text\<open>Wenn nun \<^const>\<open>Bob\<close> allerdings bereits 4 hat, würde die obige Handlung ein Verlust
für ihn bedeuten und die Maxime ist nicht erfüllt.\<close>
lemma \<open>\<not> teste_maxime
            [Alice \<mapsto> (0::nat), Bob \<mapsto> 4, Carol \<mapsto> 0, Eve \<mapsto> 0]
            (HandlungF (\<lambda>person welt. welt(person \<mapsto> 3)))
            (Maxime (\<lambda>person handlung. (the ((vorher handlung) person)) \<le> (the ((nachher handlung) person))))\<close>
  by eval



text\<open>Versuch ein allgemeines Gesetz abzuleiten:
TODO: Nur aus einer von außen betrachteten Handlung
      und einer Entscheidung ob diese Handlung ausgeführt werden soll
      wird es schwer ein allgemeines Gesetz abzuleiten.
\<close>
type_synonym ('world, 'a, 'b) allgemeines_gesetz_ableiten =
  "'world handlung \<Rightarrow> sollensanordnung \<Rightarrow> ('a, 'b) rechtsnorm"


text\<open>

Handle nur nach derjenigen Maxime, durch die du zugleich wollen kannst,
dass sie ein allgemeines Gesetz werde.

\<close>
(*TODO: unterstütze viele Maximen, wobei manche nicht zutreffen können?*)
text\<open>Parameter

 \<^item> \<^typ>\<open>'person\<close>: handelnde Person
 \<^item> \<^typ>\<open>'world\<close>: Die Welt in ihrem aktuellen Zustand
 \<^item> \<^typ>\<open>('person, 'world) handlungF\<close>: Eine mögliche Handlung,
    über die wir entscheiden wollen ob wir sie ausführen sollten.
 \<^item> \<^typ>\<open>('person, 'world) maxime\<close>: Persönliche Ethik?
 \<^item> \<^typ>\<open>('world, 'a, 'b) allgemeines_gesetz_ableiten\<close>:
    wenn man keinen Plan hat wie man sowas implementiert, einfach als Eingabe annehmen.
 \<^item> \<^typ>\<open>(nat, 'a, 'b) gesetz\<close>: Allgemeines Gesetz (für alle Menschen)
  Ergebnis:
   \<^typ>\<open>sollensanordnung\<close>: Sollen wir die Handlung ausführen?
   \<^typ>\<open>(nat, 'a, 'b) gesetz\<close>: Soll das allgemeine Gesetz entsprechend angepasst werden?
\<close>
definition kategorischer_imperativ ::
  "'person \<Rightarrow> 'world \<Rightarrow> ('person, 'world) handlungF \<Rightarrow>
  ('person, 'world) maxime \<Rightarrow> ('world, 'a, 'b) allgemeines_gesetz_ableiten \<Rightarrow>
  (nat, 'a, 'b) gesetz
  \<Rightarrow> (sollensanordnung \<times> (nat, 'a, 'b) gesetz)" where
  (*TODO: Wenn unsere Maximen perfekt und die Maximen aller Menschen konsisten sind,
        soll das Gesetz nur erweitert werden.*)
(*
  -- Es fehlt: ich muss nach allgemeinem Gesetz handeln.
  --           Wenn das Gesetz meinen Fall nicht abdeckt,
  --           dann muss meine Maxime zum Gesetz erhoben werden.
  -- Es fehlt: "Wollen"
  -- TODO: Wir unterstützen nur Erlaubnis/Verbot.
*)
"kategorischer_imperativ ich welt handlung maxime gesetz_ableiten gesetz \<equiv>
  let soll_handeln = if teste_maxime welt handlung maxime
                     then
                       Erlaubnis
                     else
                       Verbot in
    (
      soll_handeln,
      hinzufuegen (gesetz_ableiten (handeln ich welt handlung) soll_handeln) gesetz
    )
  "


end
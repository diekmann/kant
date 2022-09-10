theory Gesetze
imports Gesetz Kant Aenderung
begin

section\<open>Gesetze\<close>

subsection\<open>Case Law\<close>

text\<open>
Gesetz beschreibt: (wenn vorher, wenn nachher) dann Erlaubt/Verboten,
                    wobei vorher/nachher die Welt beschreiben.
Paragraphen sind einfache \<^typ>\<open>nat\<close>\<close>
type_synonym 'world case_law = "(nat, ('world \<times> 'world), sollensanordnung) gesetz"

text\<open>
Überträgt einen Tatbestand wörtlich ins Gesetz.
Nicht sehr allgemein.\<close>
definition case_law_ableiten_absolut
    :: "('world, ('world \<times> 'world), sollensanordnung) allgemeines_gesetz_ableiten"
  where
    "case_law_ableiten_absolut handlung sollensanordnung =
        Rechtsnorm
            (Tatbestand (vorher handlung, nachher handlung))
            (Rechtsfolge sollensanordnung)"

definition printable_case_law_ableiten_absolut
  :: "('world \<Rightarrow>'printable_world) \<Rightarrow>
     ('world, ('printable_world \<times> 'printable_world), sollensanordnung) allgemeines_gesetz_ableiten"
  where
  "printable_case_law_ableiten_absolut print_world h \<equiv>
      case_law_ableiten_absolut (map_handlung print_world h)"
  

text\<open>Case Law etwas besser, wir zeigen nur die Änderung.\<close>
fun case_law_ableiten_relativ
    :: "('world \<Rightarrow> 'world \<Rightarrow> (('person, 'etwas) aenderung) list)
        \<Rightarrow> ('world, (('person, 'etwas) aenderung) list, sollensanordnung)
              allgemeines_gesetz_ableiten"
  where
    "case_law_ableiten_relativ delta (Handlung vor nach) erlaubt =
      Rechtsnorm (Tatbestand (delta vor nach)) (Rechtsfolge erlaubt)"

end
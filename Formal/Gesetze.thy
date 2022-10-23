theory Gesetze
imports Gesetz KategorischerImperativ Aenderung
begin

section\<open>Gesetze\<close>
text\<open>Wir implementieren Strategien um \<^typ>\<open>('world, 'a, 'b) allgemeines_gesetz_ableiten\<close>
zu implementieren.\<close>

subsection\<open>Case Law Absolut\<close>

text\<open>
Gesetz beschreibt: wenn (vorher, nachher) dann Erlaubt/Verboten,
                    wobei vorher/nachher die Welt beschreiben.
Paragraphen sind einfache natürliche Zahlen.\<close>
type_synonym 'world case_law = \<open>(nat, ('world \<times> 'world), sollensanordnung) gesetz\<close>

text\<open>
Überträgt einen Tatbestand wörtlich ins Gesetz.
Nicht sehr allgemein.\<close>
definition case_law_ableiten_absolut
    :: \<open>('world, ('world \<times> 'world), sollensanordnung) allgemeines_gesetz_ableiten\<close>
  where
    \<open>case_law_ableiten_absolut handlung sollensanordnung =
        Rechtsnorm
            (Tatbestand (vorher handlung, nachher handlung))
            (Rechtsfolge sollensanordnung)\<close>

definition printable_case_law_ableiten_absolut
  :: \<open>('world \<Rightarrow>'printable_world) \<Rightarrow>
     ('world, ('printable_world \<times> 'printable_world), sollensanordnung) allgemeines_gesetz_ableiten\<close>
  where
  \<open>printable_case_law_ableiten_absolut print_world h \<equiv>
      case_law_ableiten_absolut (map_handlung print_world h)\<close>

subsection\<open>Case Law Relativ\<close>

text\<open>Case Law etwas besser, wir zeigen nur die Änderungen der Welt.\<close>
fun case_law_ableiten_relativ
    :: \<open>('world handlung \<Rightarrow> (('person, 'etwas) aenderung) list)
        \<Rightarrow> ('world, (('person, 'etwas) aenderung) list, sollensanordnung)
              allgemeines_gesetz_ableiten\<close>
  where
    \<open>case_law_ableiten_relativ delta handlung erlaubt =
      Rechtsnorm (Tatbestand (delta handlung)) (Rechtsfolge erlaubt)\<close>

end
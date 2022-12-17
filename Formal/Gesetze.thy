theory Gesetze
imports Gesetz AllgemeinesGesetz Aenderung
begin

section\<open>Gesetze\<close>
text\<open>Wir implementieren Strategien um \<^typ>\<open>('welt, 'a, 'b) allgemeines_gesetz_ableiten\<close>
zu implementieren.\<close>

subsection\<open>Case Law Absolut\<close>

text\<open>
Gesetz beschreibt: wenn (vorher, nachher) dann Erlaubt/Verboten,
                    wobei vorher/nachher die Welt beschreiben.
Paragraphen sind einfache natürliche Zahlen.\<close>
type_synonym 'welt case_law = \<open>(nat, ('welt \<times> 'welt), sollensanordnung) gesetz\<close>

text\<open>
Überträgt einen Tatbestand wörtlich ins Gesetz.
Nicht sehr allgemein.\<close>
definition case_law_ableiten_absolut
    :: \<open>('welt, ('welt \<times> 'welt), sollensanordnung) allgemeines_gesetz_ableiten\<close>
  where
    \<open>case_law_ableiten_absolut handlung sollensanordnung =
        Rechtsnorm
            (Tatbestand (vorher handlung, nachher handlung))
            (Rechtsfolge sollensanordnung)\<close>

definition printable_case_law_ableiten_absolut
  :: \<open>('welt \<Rightarrow>'printable_world) \<Rightarrow>
     ('welt, ('printable_world \<times> 'printable_world), sollensanordnung) allgemeines_gesetz_ableiten\<close>
  where
  \<open>printable_case_law_ableiten_absolut print_world h \<equiv>
      case_law_ableiten_absolut (map_handlung print_world h)\<close>

subsection\<open>Case Law Relativ\<close>

text\<open>Case Law etwas besser, wir zeigen nur die Änderungen der Welt.\<close>
fun case_law_ableiten_relativ
    :: \<open>('welt handlung \<Rightarrow> (('person, 'etwas) aenderung) list)
        \<Rightarrow> ('welt, (('person, 'etwas) aenderung) list, sollensanordnung)
              allgemeines_gesetz_ableiten\<close>
  where
    \<open>case_law_ableiten_relativ delta handlung erlaubt =
      Rechtsnorm (Tatbestand (delta handlung)) (Rechtsfolge erlaubt)\<close>

end
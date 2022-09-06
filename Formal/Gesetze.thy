theory Gesetze
imports Gesetz Kant
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
definition case_law_ableiten
    :: "('world, ('world \<times> 'world), sollensanordnung) allgemeines_gesetz_ableiten"
  where
    "case_law_ableiten handlung sollensanordnung =
        Rechtsnorm
            (Tatbestand (vorher handlung, nachher handlung))
            (Rechtsfolge sollensanordnung)"

(*
show_CaseLaw :: Show w => CaseLaw w -> String
show_CaseLaw (G.Gesetz g) = Set.foldl (\s p-> s ++ show_paragraph p ++ "\n") "" g
  where
    show_paragraph (p, rechtsnorm) = show p ++ ": " ++ show_rechtsnorm rechtsnorm
    show_rechtsnorm (G.Rechtsnorm (G.Tatbestand (a,b)) (G.Rechtsfolge f)) =
        "Wenn die welt " ++ show a ++ " ist und wir die welt nach " ++ show b ++
        " aendern wollen, dann " ++ show f

*)

end
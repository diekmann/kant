theory Slides
  imports Main "../Formal/Kant" "../Formal/Steuern"
begin

section\<open>Wie ein Gesetz entsteht\<close>
(*https://www.bpb.de/themen/politisches-system/24-deutschland/40463/wie-ein-gesetz-entsteht/*)
text_raw\<open>
  \begin{center}
    \includegraphics[height=0.8\textheight]{bpbgesetz}
  \end{center}
\<close>

(*chapter\<open>Stuff\<close>*)
section\<open>Stuff 2\<close>
text\<open>Foo
  \<^item> bar @{value "(2::nat)+4"}
  \<^item> baz @{term teste_maxime} How Do I Print the definition? @{thm teste_maxime_def}
  \<^item> The @{thm teste_maxime_unfold}
\<close>

section\<open>Bevölööökerung\<close>

datatype foobar = Foo | Bar

text\<open>Foo
  \<^item> @{datatype foobar}
  \<^item> @{locale steuersystem}: @{thm steuersystem_def}
\<close>

print_antiquotations!

end
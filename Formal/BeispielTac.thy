theory BeispielTac
  imports Main
  keywords "beispiel" :: thy_goal_stmt
begin

section\<open>The beispiel Isar Keyword\<close>

text\<open>The following is a copy of the @{command lemma} Isar keyword.
The name "beispiel" is German for "example".

I learned that there are two kinds of people:
  \<^item> People who use unnamed lemmas as examples and who emphasize examples.
  \<^item> People who simply delete unnamed lemmas.

To clearly indicate that many unnamed lemmas are meant as examples and are crucial part
of the compiled proof document, I decided to explicitly create a new command for examples.
\<close>
ML \<open>
local

val long_keyword =
  Parse_Spec.includes >> K "" ||
  Parse_Spec.long_statement_keyword;

val long_statement =
  Scan.optional (Parse_Spec.opt_thm_name ":" --| Scan.ahead long_keyword) Binding.empty_atts --
  Scan.optional Parse_Spec.includes [] -- Parse_Spec.long_statement
    >> (fn ((binding, includes), (elems, concl)) => (true, binding, includes, elems, concl));

val short_statement =
  Parse_Spec.statement -- Parse_Spec.if_statement -- Parse.for_fixes
    >> (fn ((shows, assumes), fixes) =>
      (false, Binding.empty_atts, [], [Element.Fixes fixes, Element.Assumes assumes],
        Element.Shows shows));

fun theorem spec schematic descr =
  Outer_Syntax.local_theory_to_proof' spec ("state " ^ descr)
    ((long_statement || short_statement) >> (fn (long, binding, includes, elems, concl) =>
      ((if schematic then Specification.schematic_theorem_cmd else Specification.theorem_cmd)
        long Thm.theoremK NONE (K I) binding includes elems concl)));

val _ = theorem \<^command_keyword>\<open>beispiel\<close> false "beispiel";

in end\<close>

end
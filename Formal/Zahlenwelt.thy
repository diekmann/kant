theory Zahlenwelt
imports BeispielPerson ExecutableHelper
begin

section\<open>Zahlenwelt Helper\<close>
text\<open>Wir werden Beispiele betrachten, in denen wir Welten modellieren, in denen jeder Person eine
Zahl zugewiesen wird: \<^typ>\<open>person \<Rightarrow> int\<close>.
Diese Zahl kann zum Beispiel der Besitz oder Wohlstand einer Person sein, oder das Einkommen.
Wobei Gesamtbesitz und Einkommen über einen kurzen Zeitraum recht unterschiedliche Sachen
modellieren.

Hier sind einige Hilfsfunktionen um mit \<^typ>\<open>person \<Rightarrow> int\<close> allgmein zu arbeiten.\<close>

text\<open>Default: Standardmäßig hat jede Person \<^term>\<open>0\<close>:\<close>
definition DEFAULT :: "person \<Rightarrow> int" where
  "DEFAULT \<equiv> \<lambda>p. 0"

(*<*)
syntax
  "_ZahlenWelt"  :: "updbinds \<Rightarrow> 'a" ("(1\<^url>[_])")

translations
  "_ZahlenWelt ms"                     \<rightleftharpoons> "_Update (CONST DEFAULT) ms"

(*>*)


text\<open>Beispiel:\<close>
lemma \<open>(DEFAULT(Alice:=8, Bob:=3, Eve:= 5)) Bob = 3\<close> by eval

text\<open>Beispiel mit fancy Syntax:\<close>
lemma \<open>\<^url>[Alice:=8, Bob:=3, Eve:= 5] Bob = 3\<close> by eval

lemma \<open>show_fun \<^url>[Alice := 4, Carol := 4] = [(Alice, 4), (Bob, 0), (Carol, 4), (Eve, 0)]\<close> by eval
lemma \<open>show_num_fun \<^url>[Alice := 4, Carol := 4] = [(Alice, 4), (Carol, 4)]\<close> by eval


(*from joint_probability
abbreviation joint_probability ("\<P>'(_ ; _') _") where
"\<P>(X ; Y) x \<equiv> \<P>(\<lambda>x. (X x, Y x)) x
*)

abbreviation num_fun_add_syntax ("_ '(_ += _')") where
  "f(p += n) \<equiv> (f(p := (f p) + n))"

abbreviation num_fun_minus_syntax ("_ '(_ -= _')") where
  "f(p -= n) \<equiv> (f(p := (f p) - n))"

lemma \<open>(\<^url>[Alice:=8, Bob:=3, Eve:= 5])(Bob += 4) Bob = 7\<close> by eval
lemma \<open>(\<^url>[Alice:=8, Bob:=3, Eve:= 5])(Bob -= 4) Bob = -1\<close> by eval


lemma fixes n:: int shows "f(p += n)(p -= n) = f" by(simp)

end
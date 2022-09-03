theory Handlung
imports Main
begin

text\<open>
Beschreibt Handlungen als Änderung der Welt. Unabhängig von der handelnden Person.
Beschreibt vergangene Handlung.

Handlungen können Leute betreffen.
Handlungen können aus Sicht Anderer wahrgenommen werden.
Ich brauche nur Welt vorher und Welt nachher.
So kann ich handelnde Person und beobachtende Person trennen.
\<close>
datatype 'world handlung = Handlung (vorher: 'world) (nachher: 'world)

(*<*)
text\<open>The datatype-generated functions are really cool:\<close>
lemma \<open>map_handlung Suc (Handlung 1 2) = Handlung 2 3\<close> by eval
(*>*)

text \<open>
Handlung als Funktion gewrapped.
Was ist das? Abstrakte Handlung? Plan zu handeln? Absicht?
Von Außen können wir Funktionen nur extensional betrachten, d.h. Eingabe und Ausgabe anschauen.
Die Absicht die sich in einer Funktion verstecken kann ist schwer zu erkennen.
\<close>
datatype ('person, 'world) handlungF = HandlungF "'person \<Rightarrow> 'world \<Rightarrow> 'world"

text \<open>Eine \<^typ>\<open>('person, 'world) handlungF\<close> kann nicht geprinted werden!\<close>


fun handeln :: "'person \<Rightarrow> 'world \<Rightarrow> ('person, 'world) handlungF \<Rightarrow> 'world handlung" where
"handeln handelnde_person welt (HandlungF h) = Handlung welt (h handelnde_person welt)"

text\<open>
Beispiel, für eine Welt die nur aus einer Zahl besteht.
Wenn die Zahl kleiner als 9000 ist erhöhe ich sie, ansonsten bleibt sie unverändert.
\<close>
definition "beispiel_handlungf \<equiv> HandlungF (\<lambda>p n. if n < 9000 then n+1 else n)"


end
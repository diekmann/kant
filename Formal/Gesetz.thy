theory Gesetz
imports Main ExecutableHelper
begin

section\<open>Gesetz\<close>
text\<open>Definiert einen Datentyp um Gesetzestext zu modellieren.\<close>

datatype 'a tatbestand = Tatbestand \<open>'a\<close>
 
datatype 'a rechtsfolge = Rechtsfolge \<open>'a\<close>

datatype ('a, 'b) rechtsnorm = Rechtsnorm \<open>'a tatbestand\<close> \<open>'b rechtsfolge\<close>

datatype 'p prg = Paragraph \<open>'p\<close> ("\<section>")

datatype ('p, 'a, 'b) gesetz = Gesetz \<open>('p prg \<times> ('a, 'b) rechtsnorm) set\<close>

(*
instance (Show a, Show b) => Show (Rechtsnorm a b) where
  show (Rechtsnorm tb folge) = "Wenn " ++ show tb ++ ", dann " ++ show folge
instance Show p => Show (Paragraph p) where
  show (Paragraph p) = "\<section>" ++ show p

instance (Show p, Show a, Show b) => Show (Gesetz p a b) where
  show (Gesetz g) = S.foldl (\s p-> s ++ show_paragraph p ++ "\n") "" g
    where show_paragraph (p, rechtsnorm) = show p ++ ": " ++ show rechtsnorm

*)

text\<open>Beispiel, von \<^url>\<open>https://de.wikipedia.org/wiki/Rechtsfolge\<close>:\<close>
value \<open>Gesetz {
  (\<section> ''823 BGB'',
   Rechtsnorm
     (Tatbestand ''Wer vorsaetzlich oder fahrlaessig das Leben, den Koerper, die Gesundheit, (...),
                   das Eigentum oder (...) eines anderen widerrechtlich verletzt,'')
     (Rechtsfolge ''ist dem anderen zum Ersatz des daraus entstehenden Schadens verpflichtet.'')
  ),
  (\<section> ''985 BGB'',
   Rechtsnorm
     (Tatbestand ''Der Eigentuemer einer Sache kann von dem Besitzer'')
     (Rechtsfolge ''die Herausgabe der Sache verlangen'')
  ),
  (\<section> ''303 StGB'',
   Rechtsnorm
     (Tatbestand ''Wer rechtswidrig eine fremde Sache beschaedigt oder zerstoert,'')
     (Rechtsfolge ''wird mit Freiheitsstrafe bis zu zwei Jahren oder mit Geldstrafe bestraft.'')
  )
  }\<close>


(*<*)
definition max_paragraph :: \<open>nat prg set \<Rightarrow> nat\<close> where
  [code del]: \<open>max_paragraph ps \<equiv> if card ps = 0 then 0 else Max {p. (\<section> p)\<in>ps}\<close>

lemma prg_set_deconstruct: \<open>{p. \<section> p \<in> ps} = (\<lambda>x. case x of \<section> p \<Rightarrow> p) ` ps\<close>
  apply(rule set_of_constructor)
   apply(simp add: bij_def)
   apply (meson injI prg.exhaust prg.inject surj_def)
  by (metis prg.case prg.exhaust surj_def surj_f_inv_f)

lemma [code_unfold]:
  \<open>max_paragraph ps = (if card ps = 0 then 0 else Max ((\<lambda>pa. case pa of \<section> p \<Rightarrow> p) ` ps))\<close>
  by(simp add: max_paragraph_def prg_set_deconstruct)
  
lemma \<open>max_paragraph {} = 0\<close> by eval
lemma \<open>max_paragraph {\<section> 1, \<section> 7, \<section> 2} = 7\<close> by eval
(*>*)

fun neuer_paragraph :: \<open>(nat, 'a, 'b) gesetz \<Rightarrow> nat prg\<close> where
 \<open>neuer_paragraph (Gesetz G) = \<section> ((max_paragraph (fst ` G)) + 1)\<close>

text\<open>Fügt eine Rechtsnorm als neuen Paragraphen hinzu:\<close>
fun hinzufuegen :: \<open>('a,'b) rechtsnorm \<Rightarrow> (nat,'a,'b) gesetz \<Rightarrow> (nat,'a,'b) gesetz\<close> where
  \<open>hinzufuegen rn (Gesetz G) =
    (if rn \<in> (snd ` G) then Gesetz G else Gesetz (insert (neuer_paragraph (Gesetz G), rn) G))\<close>


text\<open>Moelliert ob eine Handlung ausgeführt werden muss, darf, kann, nicht muss:\<close>
datatype sollensanordnung = Gebot | Verbot | Erlaubnis | Freistellung


text\<open>Beispiel:\<close>
lemma \<open>hinzufuegen
        (Rechtsnorm (Tatbestand ''tb2'') (Rechtsfolge Verbot))
        (Gesetz {(\<section> 1, (Rechtsnorm (Tatbestand ''tb1'') (Rechtsfolge Erlaubnis)))}) =
 Gesetz
  {(\<section> 2, Rechtsnorm (Tatbestand ''tb2'') (Rechtsfolge Verbot)),
   (\<section> 1, Rechtsnorm (Tatbestand ''tb1'') (Rechtsfolge Erlaubnis))}\<close> by eval

end
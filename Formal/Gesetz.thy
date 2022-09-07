theory Gesetz
imports Main ExecutableHelper
begin

section\<open>Gesetz\<close>

datatype 'a tatbestand = Tatbestand 'a
 
datatype 'a rechtsfolge = Rechtsfolge 'a

datatype ('a, 'b) rechtsnorm = Rechtsnorm "'a tatbestand" "'b rechtsfolge"

datatype 'p prg = Paragraph 'p

datatype ('p, 'a, 'b) gesetz = Gesetz "('p prg \<times> ('a, 'b) rechtsnorm) set"

(*
instance (Show a, Show b) => Show (Rechtsnorm a b) where
  show (Rechtsnorm tb folge) = "Wenn " ++ show tb ++ ", dann " ++ show folge
instance Show p => Show (Paragraph p) where
  show (Paragraph p) = "\<section>" ++ show p

instance (Show p, Show a, Show b) => Show (Gesetz p a b) where
  show (Gesetz g) = S.foldl (\s p-> s ++ show_paragraph p ++ "\n") "" g
    where show_paragraph (p, rechtsnorm) = show p ++ ": " ++ show rechtsnorm

*)

text\<open>From \<^url>\<open>https://de.wikipedia.org/wiki/Rechtsfolge\<close>\<close>
value \<open>Gesetz {
  (Paragraph ''823 BGB'',
   Rechtsnorm
     (Tatbestand ''Wer vorsaetzlich oder fahrlaessig das Leben, den Koerper, die Gesundheit, (...),
                   das Eigentum oder (...) eines anderen widerrechtlich verletzt,'')
     (Rechtsfolge ''ist dem anderen zum Ersatz des daraus entstehenden Schadens verpflichtet.'')
  ),
  (Paragraph ''985 BGB'',
   Rechtsnorm
     (Tatbestand ''Der Eigentuemer einer Sache kann von dem Besitzer'')
     (Rechtsfolge ''die Herausgabe der Sache verlangen'')
  ),
  (Paragraph ''303 StGB'',
   Rechtsnorm
     (Tatbestand ''Wer rechtswidrig eine fremde Sache beschaedigt oder zerstoert,'')
     (Rechtsfolge ''wird mit Freiheitsstrafe bis zu zwei Jahren oder mit Geldstrafe bestraft.'')
  )
  }\<close>



definition max_paragraph :: "nat prg set \<Rightarrow> nat" where
  [code del]: "max_paragraph ps \<equiv> if card ps = 0 then 0 else Max {p. (Paragraph p)\<in>ps}"

lemma prg_set_deconstruct: "{p. Paragraph p \<in> ps} = (\<lambda>x. case x of Paragraph p \<Rightarrow> p) ` ps"
  apply(rule set_of_constructor)
   apply(simp add: bij_def)
   apply (meson injI prg.exhaust prg.inject surj_def)
  by (metis prg.case prg.exhaust surj_def surj_f_inv_f)

lemma [code_unfold]:
  "max_paragraph ps = (if card ps = 0 then 0 else Max ((\<lambda>pa. case pa of Paragraph p \<Rightarrow> p) ` ps))"
  by(simp add: max_paragraph_def prg_set_deconstruct)
  
lemma \<open>max_paragraph {} = 0\<close> by eval
lemma \<open>max_paragraph {Paragraph 1, Paragraph 7, Paragraph 2} = 7\<close> by eval

fun neuer_paragraph :: "(nat, 'a, 'b) gesetz \<Rightarrow> nat prg" where
 "neuer_paragraph (Gesetz G) = Paragraph ((max_paragraph (fst ` G)) + 1)"

text\<open>Fügt eine Rechtsnorm als neuen Paragraphen hinzu.\<close>
fun hinzufuegen :: "('a,'b) rechtsnorm \<Rightarrow> (nat,'a,'b) gesetz \<Rightarrow> (nat,'a,'b) gesetz" where
  "hinzufuegen rn (Gesetz G) =
    (if rn \<in> (snd ` G) then Gesetz G else Gesetz (insert (neuer_paragraph (Gesetz G), rn) G))"


text\<open>ob eine Handlung ausgeführt werden muss, darf, kann, nicht muss.\<close>
datatype sollensanordnung = Gebot | Verbot | Erlaubnis | Freistellung


lemma \<open>hinzufuegen
        (Rechtsnorm (Tatbestand ''tb2'') (Rechtsfolge Verbot))
        (Gesetz {(Paragraph 1, (Rechtsnorm (Tatbestand ''tb1'') (Rechtsfolge Erlaubnis)))}) =
 Gesetz
  {(Paragraph 2, Rechtsnorm (Tatbestand ''tb2'') (Rechtsfolge Verbot)),
   (Paragraph 1, Rechtsnorm (Tatbestand ''tb1'') (Rechtsfolge Erlaubnis))}\<close> by eval

end
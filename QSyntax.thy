theory QSyntax
  imports HOL.Complex vars HOL.Orderings
begin

subsection \<open>Syntax\<close>

text \<open>Datatype for quantum programs\<close>


type_synonym 'q qheap = "'q set \<times> complex"
type_synonym ('s,'q) state = "real \<times> 's \<times> 'q qheap"
type_synonym 's pred = "'s \<Rightarrow> bool" 
type_synonym 's assn = "'s set"
type_synonym ('s,'q) expr_q = "'s \<Rightarrow> 'q set"
type_synonym ('s) expr_c = "'s \<Rightarrow> complex"
type_synonym ('s) expr_n = "'s \<Rightarrow> nat"

datatype ('a,'s,'q::linorder) com = 
    Skip
  | SMod "'s \<Rightarrow> 's"
  | QMod "'q qheap \<Rightarrow> 'q qheap" "('s,'q) expr_q"
  | IF "'s assn" "('a, 's,'q) com" "('a, 's,'q) com"
  | While "'s assn" "('a, 's,'q) com"
  | Seq "('a,'s,'q) com" "('a, 's,'q) com"  ("_;/ _" [60, 61] 60)
  | Measure "'a"   "('s,'q) expr_q" ("_:=meassure / _" [60, 61] 60)
  | Alloc "'a" "('s) expr_n"  "('s) expr_c"  ("_:=alloc/[_/]/(_/)" [60, 61] 60)
  | Dispose "('s,'q) expr_q" 


context vars 
begin

lemma "(l::('a, 's, 'q) com) = l"
  by auto

end

end


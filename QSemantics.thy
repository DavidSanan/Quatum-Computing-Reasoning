theory QSemantics
  imports QSyntax vars
begin

subsection \<open>Syntax\<close>

text \<open>Semantics for quantum programs\<close>

type_synonym ('v,'s,'q) QConf = "('v,'s,'q) com \<times> ('s,'q) state"


context vars 
begin

inductive QSemantics::"'v set \<Rightarrow> ('v,'s,'q::linorder) QConf \<Rightarrow> ('v,'s,'q) QConf \<Rightarrow> bool" 
  ("_ \<turnstile> _ \<rightarrow> _" [81,81] 80) for \<Gamma>::"'v set"
  where 
   StackMod:"\<Gamma> \<turnstile> (SMod f, (\<delta>,\<sigma>,\<Q>)) \<rightarrow> (Skip, (\<delta>,f \<sigma>,\<Q>))"
 | QMod:"\<Gamma> \<turnstile> (QMod f q, (\<delta>,\<sigma>,\<Q>)) \<rightarrow> (Skip, (\<delta>, \<sigma>,\<Q>))"
 | Alloc:"\<lbrakk> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> (Alloc q e v, (\<delta>,\<sigma>,\<Q>)) \<rightarrow> (Skip, (\<delta>, \<sigma>,\<Q>))"
 | CondTrueQ:"\<sigma>\<in>b  \<Longrightarrow> \<Gamma> \<turnstile> (IF b c1 c2, (\<delta>,\<sigma>,\<Q>)) \<rightarrow> (c1, (\<delta>,\<sigma>,\<Q>))"
 | CondFalseQ:"\<sigma>\<notin>b  \<Longrightarrow> \<Gamma> \<turnstile> (IF b c1 c2, (\<delta>,\<sigma>,\<Q>)) \<rightarrow> (c2, (\<delta>,\<sigma>,\<Q>))"
 | WhileTruec: "s\<in>b \<Longrightarrow> 
                \<Gamma>\<turnstile>(While b c,(\<delta>,\<sigma>,\<Q>)) \<rightarrow> (Seq c (While b c),(\<delta>,\<sigma>,\<Q>))"

 | WhileFalsec: "s\<notin>b \<Longrightarrow> 
                 \<Gamma>\<turnstile>(While b c,(\<delta>,\<sigma>,\<Q>)) \<rightarrow> (Skip,(\<delta>,\<sigma>,\<Q>))"
 | Seqc:"\<lbrakk>\<Gamma> \<turnstile> (C1, \<sigma>) \<rightarrow> (C1', \<sigma>')\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> (C1;C2, \<sigma>) \<rightarrow> (C1'C2, \<sigma>')"
 | SeqSkipc: "\<Gamma>\<turnstile>(Skip;C2,\<sigma>) \<rightarrow> (C2, \<sigma>)"


end

end


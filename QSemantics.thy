theory QSemantics
  imports QSyntax vars "HOL-Library.Permutations" "List_Inversions.List_Inversions" "Tensor_Permutation"
begin

subsection \<open>Syntax\<close>

text \<open>Semantics for quantum programs\<close>

lemma "(1,2) \<in> inversions [0::nat,7,3,4] \<and> (1,3)\<in>inversions [0::nat,7,3,4]"
  by (simp add: inversions.simps) 
  

type_synonym ('v,'b,'s,'q) QConf = "('v,'b,'s,'q) com \<times> ('s,'q) state"

definition Q_domain::"'q::linorder q_vars \<Rightarrow> 'q set" 
  where "Q_domain q_vars \<equiv> \<Union> (q_vars ` UNIV)"

definition ket_dim ::"'q::linorder q_vars \<Rightarrow> nat"
  where "ket_dim q_vars \<equiv>  card (Q_domain q_vars)"

definition new_q_addr::"nat \<Rightarrow> 'q::linorder q_vars \<Rightarrow> ('q set) set"
  where "new_q_addr n q_dom \<equiv> {s.  card s = n \<and> (Min s > Max (Q_domain q_dom))}"           

lemma all_gt: "finite s' \<Longrightarrow> finite s \<Longrightarrow> 
       Min s > Max s' \<Longrightarrow> (e::'q::linorder) \<in> s \<Longrightarrow> e' \<in> s' \<Longrightarrow> e > e'"
  using Max_less_iff less_le_trans by fastforce

lemma neq_q_addr_finites:"n\<noteq>0 \<Longrightarrow> S \<in> new_q_addr n q_dom \<Longrightarrow> finite S"
  unfolding new_q_addr_def
  using card_infinite by force

lemma new_q_addr_gt_old_q_addr:
  "n\<noteq>0 \<Longrightarrow> finite (Q_domain q_dom) \<Longrightarrow> 
   S \<in> new_q_addr n q_dom \<Longrightarrow> e \<in> S \<Longrightarrow>
   e' \<in> (Q_domain q_dom) \<Longrightarrow> e > e'"
  unfolding new_q_addr_def using all_gt 
  by (metis (mono_tags, lifting) card_infinite mem_Collect_eq)

lemma new_q_addr_ortho_old_q_addr:
  assumes a0:"n\<noteq>0" and a1:"finite (Q_domain q_dom)" and a2:"S \<in> new_q_addr n q_dom" 
  shows "S \<subseteq> -(Q_domain q_dom)"
proof - 
  have f4: "card S = n \<and> Max (Q_domain q_dom) < Min S"
    using a2 unfolding new_q_addr_def  by fastforce
  then have "card S \<noteq> 0"
    using a0 by meson
  then have "finite S"
    by (meson card_infinite)
  then show ?thesis
    using f4 a1 by (meson ComplI Max.coboundedI Min.coboundedI le_less_trans 
                    less_le_not_le subsetI)
qed 
 
definition list_dims::"'q::linorder set \<Rightarrow> nat list"
  where "list_dims qvars \<equiv> replicate (card qvars) 2"

definition dom_q_vars::"'q::linorder q_vars \<Rightarrow> nat set"
  where "dom_q_vars q_vars \<equiv> Set.filter (\<lambda>e. q_vars e\<noteq>{}) UNIV"
                                                  
definition dims_heap::"'q::linorder q_vars \<Rightarrow> nat list"
  where "dims_heap q_vars \<equiv> (list_dims o Q_domain) q_vars"

definition qvars_lin_set::"'q::linorder q_vars \<Rightarrow> nat set"
  where "qvars_lin_set q_vars \<equiv> {0 ..< (ket_dim q_vars)}"

definition qvars_lin_sets::"'q::linorder q_vars \<Rightarrow> 'q::linorder q_vars \<Rightarrow> nat set"
  where "qvars_lin_sets q_vars q_vars' \<equiv> {(ket_dim q_vars) ..< (ket_dim q_vars')}"

definition sorted_list_from_set::"'q::linorder set \<Rightarrow> 'q::linorder list"
  where "sorted_list_from_set s \<equiv> THE l. strict_sorted l \<and> set l = s"


context vars
begin


(* abbreviation "tensor_vec \<equiv> partial_state2.ptensor_vec" *)

inductive QSemantics::"'v set \<Rightarrow> ('v,'b,'s,'q::linorder) QConf \<Rightarrow> ('v,'b,'s,'q) QConf \<Rightarrow> bool" 
  ("_ \<turnstile> _ \<rightarrow> _" [81,81] 80) for \<Gamma>::"'v set" 
  where 
   StackMod:"\<Gamma> \<turnstile> (SMod f, (\<delta>,\<sigma>,\<Q>)) \<rightarrow> (Skip, (\<delta>,f \<sigma>,\<Q>))"

| QMod:"(q \<sigma>)\<noteq>{} \<Longrightarrow> (q \<sigma>) \<subseteq> (Q_domain \<vv>) \<Longrightarrow> 
         \<qq>' =  Normal_Tensor ((Q_domain \<vv>)-(q \<sigma>)) (Q_domain \<vv>) \<qq> \<Longrightarrow>
         \<Gamma> \<turnstile> (QMod f q, (\<delta>,\<sigma>,(\<vv>,\<qq>))) \<rightarrow> (Skip, (\<delta>, \<sigma>,(\<vv>,\<qq>)))"

 | Alloc:"q' \<notin> (dom_q_vars \<vv>) \<Longrightarrow> q'_addr \<in> new_q_addr (e \<sigma>) \<vv> \<Longrightarrow> 
          \<vv>' = \<vv>(q' := q'_addr)  \<Longrightarrow> length (v \<sigma>) = (e \<sigma>) \<Longrightarrow> \<sigma>' = set_value \<sigma> q (nat_to_typ q') \<Longrightarrow>          
          \<qq>' = partial_state2.ptensor_vec 
                     (dims_heap \<vv>') (qvars_lin_set \<vv>') (qvars_lin_sets \<vv> \<vv>') (vec_of_list (v \<sigma>)) \<qq>  \<Longrightarrow>
          \<Gamma> \<turnstile> (Alloc q e v, (\<delta>,\<sigma>,(\<vv>,\<qq>))) \<rightarrow> (Skip, (\<delta>, \<sigma>',(\<vv>',\<qq>')))"

 | CondTrueQ:"\<sigma>\<in>b  \<Longrightarrow> \<Gamma> \<turnstile> (IF b c1 c2, (\<delta>,\<sigma>,\<Q>)) \<rightarrow> (c1, (\<delta>,\<sigma>,\<Q>))"

 | CondFalseQ:"\<sigma>\<notin>b  \<Longrightarrow> \<Gamma> \<turnstile> (IF b c1 c2, (\<delta>,\<sigma>,\<Q>)) \<rightarrow> (c2, (\<delta>,\<sigma>,\<Q>))"

 | WhileTruec: "s\<in>b \<Longrightarrow> 
                \<Gamma>\<turnstile> (While b c,(\<delta>,\<sigma>,\<Q>)) \<rightarrow> (Seq c (While b c),(\<delta>,\<sigma>,\<Q>))"

 | WhileFalsec: "s\<notin>b \<Longrightarrow> 
                 \<Gamma>\<turnstile> (While b c,(\<delta>,\<sigma>,\<Q>)) \<rightarrow> (Skip,(\<delta>,\<sigma>,\<Q>))"

| Seqc:"\<lbrakk>\<Gamma> \<turnstile> (C1, \<sigma>) \<rightarrow> (C1', \<sigma>')\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> (C1;C2, \<sigma>) \<rightarrow> (C1'C2, \<sigma>')"

| SeqSkipc: "\<Gamma>\<turnstile> (Skip;C2,\<sigma>) \<rightarrow> (C2, \<sigma>)"

 | Dispose: "\<vv> (q \<sigma>)\<noteq>{} \<Longrightarrow> \<vv>' = \<vv>((q \<sigma>):={}) \<Longrightarrow> 
             \<qq>n = Normal_Tensor (\<vv> (q \<sigma>)) (Q_domain \<vv>) \<qq> \<Longrightarrow>
             \<qq>n = partial_state2.ptensor_vec (dims_heap \<vv>) (qvars_lin_set \<vv>') (qvars_lin_sets \<vv>' \<vv>) \<qq>1 \<qq>2 \<Longrightarrow>  
             \<Gamma> \<turnstile> (Dispose q, (\<delta>,\<sigma>,(\<vv>,\<qq>))) \<rightarrow> (Skip,(\<delta>,\<sigma>,(\<vv>',\<qq>1)))"

 | Measure: "\<Gamma> \<turnstile> (Measure v qe, (\<delta>,\<sigma>,(\<vv>,\<qq>))) \<rightarrow> (Skip,(\<delta>,\<sigma>,(\<vv>',v1)))" 
 


end

end


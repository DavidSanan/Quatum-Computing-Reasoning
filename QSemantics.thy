(* Title:     Quantum-Semantics/QSemantics.thy
   Author:    David Sanan, Nanyang Technological University 
   Copyright   2020
   License:     BSD
*)

theory QSemantics
  imports QSyntax vars "HOL-Library.Permutations" "List_Inversions.List_Inversions"
begin

subsection \<open>Syntax\<close>

text \<open>Semantics for quantum programs\<close>

lemma "(1,2) \<in> inversions [0::nat,7,3,4] \<and> (1,3)\<in>inversions [0::nat,7,3,4]"
  by (simp add: inversions.simps) 
  


context vars
begin

(* m = partial_state2.ptensor_mat (dims_heap \<vv>) (q \<sigma>) ((Q_domain \<vv>)-(q \<sigma>)) (M::complex mat) (1\<^sub>m (card ((Q_domain \<vv>) - (q \<sigma>))))*)
(* abbreviation "tensor_vec \<equiv> partial_state2.ptensor_vec" *)
term  partial_state2.ptensor_mat

definition apply_matrix_sep :: "'q::linorder set \<Rightarrow> ('q, complex) QState \<Rightarrow> complex mat \<Rightarrow> complex vec" 
  where "apply_matrix_sep sep_vars qs M \<equiv>
           let var_d = QState_vars qs in 
           let v = QState_vector qs in
           let t = sorted_list_of_set  sep_vars in
           let l = sorted_list_of_set (var_d - sep_vars) in
           let vs = sorted_list_of_set sep_vars in
           let vs' = (t@l) in
           let m = partial_state2.ptensor_mat (list_dims sep_vars @list_dims (var_d - sep_vars)) 
                                        (lin_set sep_vars) (lin_sets (top_lin_set sep_vars) (var_d - sep_vars))
                                        (M::complex mat) (1\<^sub>m (2^(card (var_d - sep_vars)))) in
           let q = change_base vs v vs' in
               change_base vs' (m *\<^sub>v q) vs
        "

definition alloc_vars :: "'q::linorder set \<Rightarrow> ('q, complex) QState \<Rightarrow> complex vec \<Rightarrow> complex vec"
  where "alloc_vars sep_vars qs v \<equiv>            
           partial_state2.ptensor_vec (list_dims (QState_vars qs)@list_dims sep_vars)
                  (lin_set (QState_vars qs)) (lin_sets (top_lin_set ((QState_vars qs))) sep_vars)
                  ( QState_vector qs) v"

definition dispose_vars:: " 'q::linorder set \<Rightarrow> ('q, complex) QState \<Rightarrow> complex vec set"
  where "dispose_vars sep_vars qs \<equiv> 
   let vars_dom = QState_vars qs in
   let v =   QState_vector qs in
   let qv = (sorted_list_of_set vars_dom) in
   let t = sorted_list_of_set sep_vars in
   let l =  sorted_list_of_set (vars_dom - sep_vars) in
   let qv' = t @ l in
   let qn =  change_base qv v qv' in 
   let vars_dom' = vars_dom \<union> sep_vars in
    {q. (\<exists>q2. qn = partial_state2.ptensor_vec 
                     ((list_dims vars_dom')@list_dims sep_vars)
                     (lin_set vars_dom') (lin_sets (top_lin_set vars_dom') sep_vars ) 
                      q q2)}"

definition measure_vars::"nat \<Rightarrow>  'q::linorder set \<Rightarrow> ('q, complex) QState  \<Rightarrow> (real\<times>complex vec)"
  where "measure_vars k  sep_vars qs \<equiv>
   let vars_dom = QState_vars qs in
    let v =   QState_vector qs in
    let vars= (vars_dom - sep_vars) in
    let l = (sorted_list_of_set sep_vars) in
    let t = (sorted_list_of_set vars) in
    let qv = (sorted_list_of_set vars_dom) in
    let qv' = l @ t in 
    let qn = change_base qv v qv' in
    let mk = partial_state2.ptensor_mat (list_dims sep_vars @ list_dims vars)
                 (lin_set sep_vars) (lin_sets (top_lin_set sep_vars) vars) (1\<^sub>k (2^(length l))) (1\<^sub>m (2^(length t))) in
    let qn' =  mk  *\<^sub>v qn in 
    let \<delta>k =  Re (((mat_adjoint (mat_of_rows (dim_vec v) [v]) *\<^sub>v qn') $ 0) div vec_norm qn') in    
    let qnprod = ((sqrt \<delta>k)::complex) \<cdot>\<^sub>v qn' in
       (\<delta>k, change_base qv' qnprod qv)" 

inductive QSemantics::"'v set \<Rightarrow> ('v,'b,'s,'q::linorder) QConf \<Rightarrow> ('v,'b,'s,'q) QConf \<Rightarrow> bool" 
  ("_ \<turnstile> _ \<rightarrow> _" [81,81] 80) for \<Gamma>::"'v set" 
  where 
   StackMod:"\<Gamma> \<turnstile> (SMod f, (\<delta>,\<sigma>,\<Q>)) \<rightarrow> (Skip, (\<delta>,f \<sigma>,\<Q>))"

| QMod:"(q \<sigma>)\<noteq>{} \<Longrightarrow> (q \<sigma>) \<subseteq> (QState_vars \<qq>) \<Longrightarrow> 
         \<qq>' = apply_matrix_sep (q \<sigma>) \<qq> m \<Longrightarrow>
         \<Gamma> \<turnstile> (QMod M q, (\<delta>,\<sigma>,(\<vv>,\<qq>))) \<rightarrow> (Skip, (\<delta>, \<sigma>,(\<vv>,QState(QState_vars \<qq>, list_of_vec  \<qq>'))))"

 | Alloc:"q' \<notin> (dom_q_vars \<vv>) \<Longrightarrow> q'_addr \<in> new_q_addr (e \<sigma>) \<vv> \<Longrightarrow> 
          \<vv>' = \<vv>(q' := q'_addr)  \<Longrightarrow> length (v \<sigma>) = (e \<sigma>) \<Longrightarrow> \<sigma>' = set_value \<sigma> q (nat_to_typ q') \<Longrightarrow>          
          \<qq>' = alloc_vars q'_addr \<qq> (vec_of_list (v \<sigma>)) \<Longrightarrow>
          \<Gamma> \<turnstile> (Alloc q e v, (\<delta>,\<sigma>,(\<vv>,\<qq>))) \<rightarrow> (Skip, (\<delta>, \<sigma>',(\<vv>',QState(Q_domain \<vv>', list_of_vec  \<qq>'))))"

 | CondTrueQ:"\<sigma>\<in>b  \<Longrightarrow> \<Gamma> \<turnstile> (IF b c1 c2, (\<delta>,\<sigma>,\<Q>)) \<rightarrow> (c1, (\<delta>,\<sigma>,\<Q>))"

 | CondFalseQ:"\<sigma>\<notin>b  \<Longrightarrow> \<Gamma> \<turnstile> (IF b c1 c2, (\<delta>,\<sigma>,\<Q>)) \<rightarrow> (c2, (\<delta>,\<sigma>,\<Q>))"

 | WhileTruec: "s\<in>b \<Longrightarrow> 
                \<Gamma>\<turnstile> (While b c,(\<delta>,\<sigma>,\<Q>)) \<rightarrow> (Seq c (While b c),(\<delta>,\<sigma>,\<Q>))"

 | WhileFalsec: "s\<notin>b \<Longrightarrow> 
                 \<Gamma>\<turnstile> (While b c,(\<delta>,\<sigma>,\<Q>)) \<rightarrow> (Skip,(\<delta>,\<sigma>,\<Q>))"

| Seqc:"\<lbrakk>\<Gamma> \<turnstile> (C1, \<sigma>) \<rightarrow> (C1', \<sigma>')\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> (C1;C2, \<sigma>) \<rightarrow> (C1'C2, \<sigma>')"

| SeqSkipc: "\<Gamma>\<turnstile> (Skip;C2,\<sigma>) \<rightarrow> (C2, \<sigma>)"

| Dispose: "\<vv> (q \<sigma>) \<noteq> {} \<Longrightarrow> \<vv>' = \<vv>((q \<sigma>):={}) \<Longrightarrow> q1 ## q2  \<Longrightarrow> 
            \<vv> (q \<sigma>) = QState_vars \<qq> \<Longrightarrow> \<qq> =   \<qq>1 +  \<qq>2 \<Longrightarrow>
            \<qq>' \<in> dispose_vars (\<vv> (q \<sigma>)) \<qq> \<Longrightarrow>
             \<Gamma> \<turnstile> (Dispose q, (\<delta>,\<sigma>,(\<vv>,\<qq>))) \<rightarrow> (Skip,(\<delta>,\<sigma>,(\<vv>',QState(Q_domain \<vv>', list_of_vec  \<qq>'))))"

| Measure: "q \<sigma> \<subseteq> (Q_domain \<vv>) \<Longrightarrow> 
            (\<delta>k, \<qq>') = measure_vars k (q \<sigma>) \<qq> \<Longrightarrow>
            \<delta>k > 0 \<Longrightarrow> \<delta>' = \<delta> * \<delta>k \<Longrightarrow> 
            \<Gamma> \<turnstile> (Measure v q, (\<delta>,\<sigma>,(\<vv>,\<qq>))) \<rightarrow> (Skip,(\<delta>',\<sigma>,(\<vv>',\<qq>')))" 
 


end

end


(* Title:     Quantum-Semantics/QSemantics.thy
   Author:    David Sanan, Nanyang Technological University 
   Copyright   2020
   License:     BSD
*)

theory QSemanticsBig
  imports QSyntax  
begin           

subsection \<open>Syntax\<close>

text \<open>Semantics for quantum programs\<close>

(* m = partial_state2.ptensor_mat (dims_heap \<vv>) (q \<sigma>) ((Q_domain \<vv>)-(q \<sigma>)) (M::complex mat) (1\<^sub>m (card ((Q_domain \<vv>) - (q \<sigma>))))*)
(* abbreviation "tensor_vec \<equiv> partial_state2.ptensor_vec" *)

definition
  unit_vecl :: "nat \<Rightarrow> nat \<Rightarrow> complex list"
  where "unit_vecl n i = list_of_vec (unit_vec n i)"

definition Q_domain_var::"nat set \<Rightarrow> q_vars \<Rightarrow> nat set "
  where "Q_domain_var q qvars \<equiv> \<Union> (qvars ` q)"

definition matrix_sep :: "nat set \<Rightarrow> complex QStateM \<Rightarrow> complex mat \<Rightarrow> complex QStateM" 
  where "matrix_sep heap_ind q M \<equiv>
           let sep_vars = \<Union> ((QStateM_map q) ` heap_ind)  in
           let var_d = QStateM_vars q in 
           let var_r = var_d - sep_vars in
           let v = QStateM_vector q in           
           let m = ptensor_mat sep_vars var_r
                               (M::complex mat) (1\<^sub>m (2^(card var_r)))  in 
             QStateM (QStateM_map q, QState (var_d, list_of_vec (m *\<^sub>v v)))"

lemma "\<Union> (QStateM_map q ` hi) \<noteq> {} \<Longrightarrow> sep_vars = \<Union> ((QStateM_map q) ` hi) \<Longrightarrow>
       var_d =  QStateM_vars q \<Longrightarrow> var_r = var_d - sep_vars \<Longrightarrow> v = QStateM_vector q \<Longrightarrow> 
       QStateM_map (matrix_sep hi q M) = QStateM_map q \<and> 
       QStateM_vars (matrix_sep hi q M) = QStateM_vars q \<and>
       QStateM_list (matrix_sep hi q M) = 
         list_of_vec (ptensor_mat sep_vars var_r
                               (M::complex mat) (1\<^sub>m (2^(card var_r))) *\<^sub>v 
                      QStateM_vector q)"  
proof- 
  assume a0:"\<Union> (QStateM_map q ` hi) \<noteq> {}" and
   a1:"sep_vars = \<Union> ((QStateM_map q) ` hi)" and
   a2:"var_d =  QStateM_vars q" and a3:"var_r = var_d - sep_vars" and
   a4:"v = QStateM_vector q"

  then have hi_not_e:"hi\<noteq>{}" by auto
  have "\<Union> (QStateM_map q ` hi) \<subseteq> Q_domain (QStateM_map q)"
    unfolding Q_domain_def
    by blast
  then have domain_map_not_e:"Q_domain (QStateM_map q) \<noteq> {}"
    using a0 hi_not_e apply transfer by auto  
  let ?sep_vars = "\<Union> (QStateM_map q ` hi)" and
      ?var_d = "QStateM_vars q" 
  let ?var_r = "?var_d - ?sep_vars" and ?v = "QStateM_vector q" 
  let ?m = "ptensor_mat ?sep_vars ?var_r M (1\<^sub>m (2 ^ card ?var_r))"
  have qm_wf: "QStateM_wf (QStateM_unfold q)"
    using QStateM_wf by blast
  moreover have q_wf:"QState_wf (QState_unfold (qstate q))"
    using qm_wf QState_wf by blast
  ultimately have finite_Q_domain:"finite (Q_domain (QStateM_map q))" by auto   
  interpret ps2:partial_state2 "replicate (card (QStateM_vars q)) 2" "?sep_vars" "?var_r"
    apply standard
    apply blast
      apply simp using finite_Q_domain
    unfolding Q_domain_def 
     apply auto      
     apply (subgoal_tac "\<Union> (QStateM_map q ` hi) \<subseteq> \<Union> (range (QStateM_map q))") 
      apply auto
    using finite_subset apply blast  
    using q_wf eq_QStateM_vars
    by (metis QState_rel3' finite_Diff)
  have eq_domain_vars_map:"QStateM_vars q = {} \<Longrightarrow> 
        Q_domain (QStateM_map q) = {}" 
    apply auto unfolding qstate_def by (transfer, auto)  
  have Q_wf:"QState_wf (QStateM_vars q, list_of_vec (?m *\<^sub>v ?v))"
    unfolding matrix_sep_def Let_def apply auto
    unfolding ps2.d0_def ps2.dims0_def ps2.vars0_def apply transfer   
    unfolding Q_domain_def apply auto
     apply (metis UN_Un Un_UNIV_right)
    apply (simp add: QStateM_vars.rep_eq QState_rel3')
    using a0 ps2.finite_v1 ps2.finite_v2 by auto
  then have f1:"QState_vars (QState (QStateM_vars q, list_of_vec (?m *\<^sub>v ?v))) = 
             QStateM_vars q"
    using QState_var_idem
    by blast   
  then have q:"QStateM_wf (QStateM_map q, QState (?var_d, list_of_vec (?m *\<^sub>v ?v)))"    
    using eq_QStateM_vars qm_wf by auto      
  then show ?thesis unfolding matrix_sep_def Let_def 
    using  f1 a1 a2 a3 a4
    apply (auto simp add:  QStateM_wf_map QStateM_wf_vars )
    using a1 a2 a3 a4 Q_wf q
    by (metis QStateM_wf_list QState_list_idem q)
qed


(* definition matrix_sep :: "nat set \<Rightarrow> qstate \<Rightarrow> complex mat \<Rightarrow> qstate" 
  where "matrix_sep sep_vars q M \<equiv>
           let qs = snd q in
           let var_d = QState_vars qs in 
           let var_r = var_d - sep_vars in
           let v = QState_vector qs in           
           let m = partial_state2.ptensor_mat sep_vars var_r
                                        (M::complex mat) (1\<^sub>m (2^(card var_r)))  in           
             (fst q, QState (var_d, list_of_vec (m *\<^sub>v v)))
        " *)

(* definition measure_vars1::"nat \<Rightarrow>  nat set \<Rightarrow> qstate  \<Rightarrow> (real \<times> qstate)"
  where "measure_vars1 k  sep_vars q \<equiv>
   let qs = snd q in
   let vars_dom = QState_vars qs in
    let v =   QState_vector qs in
    let vars= (vars_dom - sep_vars) in    
    let mk = partial_state2.ptensor_mat  vars_dom vars (1\<^sub>k (2^(card vars_dom))) (1\<^sub>m (2^(card vars))) in
    let qn' =  mk  *\<^sub>v v in 
    let \<delta>k =  Re (((mat_adjoint (mat_of_rows (dim_vec v) [v]) *\<^sub>v qn') $ 0) div vec_norm qn') in    
    let qnprod = list_of_vec (((sqrt \<delta>k)::complex) \<cdot>\<^sub>v qn') in
       (\<delta>k, (fst q, QState (vars_dom, qnprod)))" *)

definition measure_vars1::"nat \<Rightarrow>  nat set \<Rightarrow> qstate  \<Rightarrow> (real \<times> qstate)"
  where "measure_vars1 k  sep_vars q \<equiv>
   let qs = snd q in
   let vars_dom = QState_vars qs in
    let v =   QState_vector qs in
    let vars= (vars_dom - sep_vars) in        
    let mk = partial_state2.ptensor_mat  sep_vars vars (1\<^sub>k (2^(card sep_vars))) (1\<^sub>m (2^(card vars))) in
    let v' =  mk  *\<^sub>v v in 
    let \<delta>k =  Re ((vec_norm v')^2 div (vec_norm v)^2) in    
    let qnprod = list_of_vec (((sqrt \<delta>k)::complex) \<cdot>\<^sub>v v') in
       (\<delta>k, (fst q, QState (vars_dom, qnprod)))" 

definition measure_vars::"nat \<Rightarrow>  nat set \<Rightarrow> complex QStateM  \<Rightarrow> (real \<times> complex QStateM)"
  where "measure_vars k  sep_addr q \<equiv>
   let (qm, qs) = QStateM_unfold q in
   let vars_dom = QState_vars qs in
    let v =   QState_vector qs in
    let sep_vars = \<Union>(qm ` sep_addr) in
    let rest_vars= (vars_dom - sep_vars) in        
    let mk = partial_state2.ptensor_mat  sep_vars rest_vars (1\<^sub>k (2^(card sep_vars))) (1\<^sub>m (2^(card rest_vars))) in
    let v' =  mk  *\<^sub>v v in 
    let \<delta>k =  Re ((vec_norm v')^2 div (vec_norm v)^2) in    
    let qnprod = list_of_vec (((sqrt \<delta>k)::complex) \<cdot>\<^sub>v v') in
       (\<delta>k, QStateM(qm, QState (vars_dom, qnprod)))" 

lemma allocate_wf1:
  assumes a0:"\<Q>' = QStateM(\<vv>', QState (q'_addr,(v \<sigma>)))" and  a1:"length (v \<sigma>) > 1" and     
       a2:"\<vv>' = (\<lambda>i. {})(q' := q'_addr)" and 
      a3:"q'_addr \<in> new_q_addr v \<sigma> (QStateM_map \<Q>) " 
    shows "QState_wf (q'_addr, v \<sigma>) \<and> 
           QStateM_wf ((\<lambda>i. {})(q' := q'_addr), QState (q'_addr, v \<sigma>))  \<and>
           QStateM_map \<Q>' = (\<lambda>i. {})(q' := q'_addr)"
proof-
   have Qstate_wf:"QState_wf (q'_addr, v \<sigma>)"
     using assms
     unfolding new_q_addr_def
     using assms snd_conv
     using card_infinite by force
   moreover have QStateM_wf:"QStateM_wf ((\<lambda>i. {})(q' := q'_addr), QState (q'_addr, v \<sigma>))"
     using calculation
     unfolding Q_domain_def using QState_var_idem by auto
   moreover have QState_mapQ':"QStateM_map \<Q>' = (\<lambda>i. {})(q' := q'_addr)"
     using calculation
     apply auto
     by (auto simp add: QStateM_wf_map a0 local.a2)
   ultimately show ?thesis by auto
 qed

lemma allocate_wf:
  assumes a0:"\<Q>' = QStateM(\<vv>', QState (q'_addr,(v \<sigma>)))" and a1':"length (v \<sigma>) > 1" and
       a1:"q' \<notin> (dom_q_vars (QStateM_map \<Q>))" and
       a2:"\<vv>' = (\<lambda>i. {})(q' := q'_addr)" and 
      a3:"q'_addr \<in> new_q_addr v \<sigma> (QStateM_map \<Q>) " 
    shows "QStateM_wf (QStateM_map \<Q> + QStateM_map \<Q>',
                  qstate \<Q> + qstate \<Q>')"
proof-  
  have "QState_wf (q'_addr, v \<sigma>) \<and> 
           QStateM_wf ((\<lambda>i. {})(q' := q'_addr), QState (q'_addr, v \<sigma>))  \<and>
           QStateM_map \<Q>' = (\<lambda>i. {})(q' := q'_addr)"
    using allocate_wf1[of  \<Q>' \<vv>' q'_addr v \<sigma>, OF a0  a1' a2  a3 ]
    by auto
  moreover have d1:"QStateM_map \<Q> ## QStateM_map \<Q>'"
    using assms calculation
    unfolding dom_q_vars_def sep_disj_fun_def opt_class.domain_def
    by auto 
  moreover have d2:"qstate \<Q> ## qstate \<Q>'" 
unfolding sep_disj_QState disj_QState_def calculation
    using QStateM_wf QState_wf a3 unfolding new_q_addr_def
    apply auto
    by (smt QStateM_rel1 QState_rel3' QState_var_idem a3  
           calculation(1) fst_conv new_q_addr_gt_old_q_addr not_less_iff_gr_or_eq snd_conv)                        
  ultimately show ?thesis   
    using plus_wf
    by metis 
qed

lemma disjoint_allocate: 
  assumes a0:"\<Q>' = QStateM(\<vv>', QState (q'_addr,(v \<sigma>)))" and a1':"length (v \<sigma>) > 1" and
       a1:"q' \<notin> (dom_q_vars (QStateM_map \<Q>))" and
       a2:"\<vv>' = (\<lambda>i. {})(q' := q'_addr)" and
      a3:"q'_addr \<in> new_q_addr v \<sigma> (QStateM_map \<Q>) " 
    shows "\<Q> ## \<Q>'"
proof-  
  have "QState_wf (q'_addr, v \<sigma>) \<and> 
           QStateM_wf ((\<lambda>i. {})(q' := q'_addr), QState (q'_addr, v \<sigma>))  \<and>
           QStateM_map \<Q>' = (\<lambda>i. {})(q' := q'_addr)"
    using allocate_wf1[of  \<Q>' \<vv>' q'_addr v \<sigma>, OF a0  a1' a2 a3 ]
    by auto
  moreover have d1:"QStateM_map \<Q> ## QStateM_map \<Q>'"
    using assms calculation
    unfolding dom_q_vars_def sep_disj_fun_def opt_class.domain_def
    by auto 
  moreover have d2:"qstate \<Q> ## qstate \<Q>'" 
    unfolding sep_disj_QState disj_QState_def calculation
    using QStateM_wf QState_wf a3 unfolding new_q_addr_def
    apply auto
    by (smt QStateM_rel1 QState_rel3' QState_var_idem a3  
           calculation(1) fst_conv new_q_addr_gt_old_q_addr not_less_iff_gr_or_eq snd_conv)                        
  ultimately show ?thesis   
    using plus_wf
    by (simp add: sep_disj_QStateM)
qed

lemma sep_Q_eq_Q'_Q''_empty: 
     assumes a0:"\<Q> =  \<Q>' + \<Q>'' " and 
              a1:"\<Q>' ## \<Q>''" and
              a2:"Q_domain (QStateM_map \<Q>') = Q_domain (QStateM_map \<Q>)"
      shows "(QStateM_map \<Q>'') = {}\<^sub>q" 
proof-
  have Q''0:"Q_domain (QStateM_map \<Q>'') = {}"
    using a0 a1 a2 unfolding  plus_QStateM sep_disj_QStateM     
    by (smt QStateM_rel1  Qstate_vector disj_QState_def 
           disjoint_x_y_wf1_x_plus_y fst_conv inf.idem plus_wf 
           sep_add_disjD sep_disj_QState)
  then show ?thesis unfolding Q_domain_def by auto
qed

lemma sep_eq: 
     assumes a0:"\<Q> =  \<Q>' + \<Q>'' " and 
              a1:"\<Q>' ## \<Q>''" and
              a2:"Q_domain (QStateM_map \<Q>') = Q_domain (QStateM_map \<Q>)"
      shows "\<Q> = ((QStateM_list \<Q>'' ! 0)) \<cdot>\<^sub>Q \<Q>' \<and> (inverse(QStateM_list \<Q>'' ! 0)) \<cdot>\<^sub>Q \<Q>'' = 0" 
proof-
  have Q''0:"Q_domain (QStateM_map \<Q>'') = {}"
    using a0 a1 a2 unfolding  plus_QStateM sep_disj_QStateM     
    by (smt QStateM_rel1  Qstate_vector disj_QState_def 
           disjoint_x_y_wf1_x_plus_y fst_conv inf.idem plus_wf 
           sep_add_disjD sep_disj_QState)  
  then have  "inverse(QStateM_list \<Q>'' ! 0) \<cdot>\<^sub>Q \<Q>'' = 0" 
    unfolding zero_QStateM  zero_fun_def      
    by (simp add: QStateM_list_inv zero_QState)
  moreover have "\<Q> = 1 \<cdot>\<^sub>Q \<Q>' + \<Q>''" 
    unfolding sca_mult_qstatem_def sca_mult_qstate_def
    by (simp add: QState_refl QState_vector.rep_eq a0 idem_QState list_vec uqstate_snd)
  moreover have "\<And>a::'a::field. a \<noteq> 0 \<Longrightarrow> a * inverse a = 1"
    using right_inverse by blast
  moreover have "QStateM_list \<Q>'' ! 0 \<noteq> 0" using Q''0 QStateM_empty_not_zero by auto
  ultimately have "\<Q> = ((QStateM_list \<Q>'' ! 0) * (inverse (QStateM_list \<Q>'' ! 0))) \<cdot>\<^sub>Q 
                        (\<Q>' + \<Q>'')"
    by (metis QState_list.rep_eq QState_refl QState_vector.rep_eq a0 
              idem_QState list_vec one_smult_vec sca_mult_qstate_def 
              sca_mult_qstatem_def) 
  then have "\<Q> = (QStateM_list \<Q>'' ! 0) \<cdot>\<^sub>Q 
                  ( inverse (QStateM_list \<Q>'' ! 0) \<cdot>\<^sub>Q (\<Q>' + \<Q>''))"
    using \<open>QStateM_list \<Q>'' ! 0 \<noteq> 0\<close> inverse_nonzero_iff_nonzero sca_mult_qstatem_assoc by blast
       
  then have "\<Q> = (QStateM_list \<Q>'' ! 0) \<cdot>\<^sub>Q 
                  (\<Q>' + (inverse (QStateM_list \<Q>'' ! 0) \<cdot>\<^sub>Q \<Q>''))"
    by (simp add: \<open>QStateM_list \<Q>'' ! 0 \<noteq> 0\<close> local.a1 scalar_mult_QStateM_plus_r)    
  then have "\<Q> = ((QStateM_list \<Q>'' ! 0) \<cdot>\<^sub>Q \<Q>' + (inverse (QStateM_list \<Q>'' ! 0) \<cdot>\<^sub>Q \<Q>''))"
    by (simp add: \<open>inverse (QStateM_list \<Q>'' ! 0) \<cdot>\<^sub>Q \<Q>'' = 0\<close>)
  thus ?thesis
    by (simp add: \<open>inverse (QStateM_list \<Q>'' ! 0) \<cdot>\<^sub>Q \<Q>'' = 0\<close>)
qed

(* lemma assumes f1:"sn = (\<delta>, \<sigma>, \<Q>' + \<Q>'')" and
      f3:"\<Q>' ## \<Q>''" and f4:"QStateM_map \<Q>'' (to_nat (get_value \<sigma> q)) \<noteq> {}" and
      f5:"Q_domain (QStateM_map \<Q>'') = QStateM_map \<Q>'' (to_nat (get_value \<sigma> q))"
    shows "QState_wf (QState_vars (vec_norm (QStateM_vector \<Q>'') \<cdot>\<^sub>q qstate \<Q>'),
                      QState_list (vec_norm (QStateM_vector \<Q>'') \<cdot>\<^sub>q qstate \<Q>')) \<and>
           QStateM_wf (QStateM_map \<Q>',vec_norm (QStateM_vector \<Q>'') \<cdot>\<^sub>q qstate \<Q>') \<and> 
           QStateM_map \<Q>' = (\<lambda>i. if i \<in> fst (qstate \<Q>') then )"
proof-
qed *)

(* lemma dispose_Q'_sep: 
  assumes a0:"sn = (\<rho>, \<sigma>, \<Q>' + \<Q>'')" and
      a1:"s' = Normal (\<rho>, \<sigma>, QStateM (QStateM_map \<Q>', vec_norm (QStateM_vector \<Q>'') \<cdot>\<^sub>q qstate \<Q>'))" and
      a3:"\<Q>' ## \<Q>''" and a4:"Q_domain_var vs (QStateM_map \<Q>'') \<noteq> {}" and
      a5:"Q_domain (QStateM_map \<Q>'') = Q_domain_var vs (QStateM_map \<Q>'')"
    shows "\<forall>Q' Q''. Q' \<noteq> \<Q>' \<or> Q'' \<noteq> \<Q>'' \<longrightarrow> 
             QStateM (QStateM_map Q', vec_norm (QStateM_vector Q'') \<cdot>\<^sub>q qstate Q') \<noteq>
             QStateM (QStateM_map \<Q>', vec_norm (QStateM_vector \<Q>'') \<cdot>\<^sub>q qstate \<Q>')"
proof-
  { fix Q' Q''
    assume a00:"Q' \<noteq> \<Q>' \<or> Q'' \<noteq> \<Q>''"
    have "QStateM (QStateM_map Q', vec_norm (QStateM_vector Q'') \<cdot>\<^sub>q qstate Q') \<noteq>
          QStateM (QStateM_map \<Q>', vec_norm (QStateM_vector \<Q>'') \<cdot>\<^sub>q qstate \<Q>')"
      sorry
  } thus ?thesis by auto
qed

lemma dispose_Q'_sep': 
  assumes a0:"sn = (\<rho>, \<sigma>, \<Q>' + \<Q>'')" and
      a1:"s' = Normal (\<rho>, \<sigma>, QStateM (QStateM_map \<Q>', vec_norm (QStateM_vector \<Q>'') \<cdot>\<^sub>q qstate \<Q>'))" and
      a3:"\<Q>' ## \<Q>''" and a4:"Q_domain_var vs (QStateM_map \<Q>'') \<noteq> {}" and
      a5:"Q_domain (QStateM_map \<Q>'') = Q_domain_var vs (QStateM_map \<Q>'')"
    shows "\<forall>Q' Q''. 
             QStateM (QStateM_map Q', vec_norm (QStateM_vector Q'') \<cdot>\<^sub>q qstate Q') \<noteq>
             QStateM (QStateM_map \<Q>', vec_norm (QStateM_vector \<Q>'') \<cdot>\<^sub>q qstate \<Q>') \<longrightarrow>
           Q'\<noteq> \<Q>' \<or> Q'' \<noteq> \<Q>''"
proof-
  { fix Q' Q''
    assume a00:"QStateM (QStateM_map Q', vec_norm (QStateM_vector Q'') \<cdot>\<^sub>q qstate Q') \<noteq>
              QStateM (QStateM_map \<Q>', vec_norm (QStateM_vector \<Q>'') \<cdot>\<^sub>q qstate \<Q>')"
    have "Q'\<noteq> \<Q>' \<or> Q'' \<noteq> \<Q>''"
      sorry
  } thus ?thesis by auto
qed

lemma dispose_Q_sep: 
  assumes a0:"sn = (\<rho>, \<sigma>, \<Q>' + \<Q>'')" and
      a1:"s' = Normal (\<rho>, \<sigma>, QStateM (QStateM_map \<Q>', vec_norm (QStateM_vector \<Q>'') \<cdot>\<^sub>q qstate \<Q>'))" and
      a2:"\<Q>' ## \<Q>''" and a3:"Q_domain_var vs (QStateM_map \<Q>'') \<noteq> {}" and
      a4:"Q_domain (QStateM_map \<Q>'') = Q_domain_var vs (QStateM_map \<Q>'')"
    shows "\<forall>Q' Q''. snd (snd sn) = Q' + Q'' \<longrightarrow> Q' = \<Q>' \<and> Q'' = \<Q>''"
proof-
  { fix Q' Q''
    assume a00:"snd (snd sn) = Q' + Q''"
    {  assume "Q' \<noteq> \<Q>' \<or> Q'' \<noteq> \<Q>''"
      then have 
         "QStateM (QStateM_map Q', vec_norm (QStateM_vector Q'') \<cdot>\<^sub>q qstate Q') \<noteq>
          QStateM (QStateM_map \<Q>', vec_norm (QStateM_vector \<Q>'') \<cdot>\<^sub>q qstate \<Q>')"
        using dispose_Q'_sep[OF a0 a1 a2 a3 a4] by auto
        have False sorry
    }
  } thus ?thesis by auto
qed
*)

context vars
begin



inductive QExec::"('v, 's) com \<Rightarrow> 's XQState \<Rightarrow> 's XQState \<Rightarrow> bool" 
  ("\<turnstile> \<langle>_,_\<rangle> \<Rightarrow> _"  [20,98,98] 89)  
  where 
  Skip : "\<turnstile>  \<langle>Skip, Normal \<sigma>\<rangle> \<Rightarrow> Normal \<sigma>" 
\<comment>\<open>SMod  modifies the stack of non-qubits variables \<sigma> with f \<sigma>, where f is a 
  function modifying the stack\<close>
 | StackMod: "\<turnstile> \<langle>SMod f, Normal (\<delta>,\<sigma>,\<Q>)\<rangle> \<Rightarrow>  Normal (\<delta>,f \<sigma>,\<Q>)"

\<comment>\<open>QMod modifies the set of qubits of the Quantum State given by q \<sigma> with the 
  transformation matrix M, any qubit not included in q \<sigma> remains the same\<close>

 | QMod:"\<Union>(QStateM_map \<Q> ` (q \<sigma>)) \<noteq> {} \<Longrightarrow> 
         \<Q>' = matrix_sep (q \<sigma>) \<Q> M \<Longrightarrow>
         \<turnstile> \<langle>QMod M q, Normal (\<delta>,\<sigma>,\<Q>)\<rangle> \<Rightarrow> Normal (\<delta>, \<sigma>, \<Q>')"

\<comment>\<open>QMod fails if the set of qubits to be modified is not included in the quantum state\<close>
 | QMod_F:"(QStateM_map \<Q> ` (q \<sigma>)) = {} \<Longrightarrow>          
          \<turnstile> \<langle>QMod M q, Normal (\<delta>,\<sigma>,\<Q>)\<rangle> \<Rightarrow> Fault"

\<comment>\<open>Alloc takes a normal variable "q" representing the variable where the index to the qubits is store
   an function e from the state \<sigma> to a natural number representing the number of qubits to allocate
  and an initialization value for the allocated qubits 


  We will require that a program is well formed, meaning that the types are correct.
  A call to Alloc is well formed if the type of q is a natural number\<close>

(* | Alloc1:"\<forall>q'. q' \<notin> (dom_q_vars (QStateM_map \<Q>)) \<longrightarrow> 
              \<vv>' = (QStateM_map \<Q>)(q' := q'_addr) \<and>  \<sigma>' = set_value \<sigma> q (from_nat q') \<Longrightarrow> 
          q'_addr \<in> new_q_addr e \<sigma> (QStateM_map \<Q>)  \<Longrightarrow> e \<sigma> \<noteq> 0 \<Longrightarrow> length (v \<sigma>) = (e \<sigma>) \<Longrightarrow>                     
          \<turnstile> \<langle>Alloc q e v, Normal (\<delta>,\<sigma>,\<Q>)\<rangle> \<Rightarrow> Normal (\<delta>, \<sigma>',QStateM(\<vv>',\<qq> + QState (q'_addr,(v \<sigma>)) ))" *)

| Alloc:"q' \<notin> (dom_q_vars (QStateM_map \<Q>)) \<Longrightarrow> (length (v \<sigma>) > 1) \<Longrightarrow>
              \<vv>' = (\<lambda>i. {})(q' := q'_addr) \<and>  \<sigma>' = set_value \<sigma> q (from_nat q') \<Longrightarrow> 
          q'_addr \<in> new_q_addr v \<sigma> (QStateM_map \<Q>)  \<Longrightarrow>                     
          \<turnstile> \<langle>Alloc q e v, Normal (\<delta>,\<sigma>,\<Q>)\<rangle> \<Rightarrow> Normal (\<delta>, \<sigma>',\<Q> + QStateM(\<vv>', QState (q'_addr,(v \<sigma>)) ))"
(* | Alloc:"q' \<notin> (dom_q_vars (QStateM_map \<Q>)) \<Longrightarrow> q'_addr \<in> new_q_addr e \<sigma> (QStateM_map \<Q>)  \<Longrightarrow> e \<sigma> \<noteq> 0 \<Longrightarrow>
          \<vv>' = (QStateM_map \<Q>)(q' := q'_addr)  \<Longrightarrow> length (v \<sigma>) = (e \<sigma>) \<Longrightarrow> \<sigma>' = set_value \<sigma> q (from_nat q') \<Longrightarrow>                    
          \<turnstile> \<langle>Alloc q e v, Normal (\<delta>,\<sigma>,\<Q>)\<rangle> \<Rightarrow> Normal (\<delta>, \<sigma>',QStateM(\<vv>',\<qq> + QState (q'_addr,(v \<sigma>)) ))" *)
\<comment>\<open>Alloc will fail if the length of the initial value is not equal to the number of qubits allocated \<close>


 | Alloc_F:"length (v \<sigma>) \<le> 1 \<Longrightarrow>                    
          \<turnstile> \<langle>Alloc q e v, Normal (\<delta>,\<sigma>,\<Q>)\<rangle> \<Rightarrow> Fault"

\<comment>\<open>the conditional, while, and seq statements follow the standard definitions\<close>

 | CondTrue:"\<sigma>\<in>b \<Longrightarrow>  \<turnstile> \<langle>c1, Normal (\<delta>,\<sigma>,\<Q>)\<rangle> \<Rightarrow> \<sigma>' \<Longrightarrow> \<turnstile> \<langle>IF b c1 c2, Normal  (\<delta>,\<sigma>,\<Q>)\<rangle> \<Rightarrow> \<sigma>'"

 | CondFalse:"\<sigma>\<notin>b  \<Longrightarrow>  \<turnstile> \<langle>c2, Normal (\<delta>,\<sigma>,\<Q>)\<rangle> \<Rightarrow> \<sigma>' \<Longrightarrow> 
           \<turnstile> \<langle>IF b c1 c2, Normal (\<delta>,\<sigma>,\<Q>)\<rangle> \<Rightarrow> \<sigma>'"

 | WhileTrue: "\<sigma>\<in>b \<Longrightarrow> \<turnstile> \<langle>c, Normal (\<delta>,\<sigma>,\<Q>)\<rangle> \<Rightarrow> \<sigma>' \<Longrightarrow> \<turnstile> \<langle>While b c,\<sigma>'\<rangle> \<Rightarrow>  \<sigma>'' \<Longrightarrow>
                \<turnstile> \<langle>While b c,Normal (\<delta>,\<sigma>,\<Q>)\<rangle> \<Rightarrow> \<sigma>''"

 | WhileFalse: "\<sigma>\<notin>b \<Longrightarrow> 
                 \<turnstile> \<langle>While b c,Normal  (\<delta>,\<sigma>,\<Q>)\<rangle> \<Rightarrow> Normal  (\<delta>,\<sigma>,\<Q>)"

 | Seq:"\<lbrakk>\<turnstile> \<langle>C1, Normal \<sigma>\<rangle> \<Rightarrow> \<sigma>'; \<turnstile> \<langle>C2, \<sigma>'\<rangle> \<Rightarrow> \<sigma>'' \<rbrakk> \<Longrightarrow> \<turnstile> \<langle>Seq C1 C2, Normal \<sigma>\<rangle> \<Rightarrow> \<sigma>''"


\<comment>\<open>Dispose takes an expression from the stack to a natural number and removes those qubits
  from the quantum state if they are not entangled with the rest of qubits in the current
  Quantum state. The entanglement condition is that it is possible to find a vector \<qq>1 such that
  \<qq> =  \<qq>' +  \<qq>''\<close>


(* | Dispose: "  \<Q> = \<Q>' + \<Q>'' \<Longrightarrow> \<Q>' ## \<Q>'' \<Longrightarrow> n = vec_norm (QStateM_vector \<Q>'') \<Longrightarrow>
              (\<Union>((QStateM_map \<Q>'') ` (q \<sigma>))) \<noteq> {} \<Longrightarrow> 
              Q_domain (QStateM_map \<Q>'') =(\<Union>((QStateM_map \<Q>'') ` (q \<sigma>))) \<Longrightarrow>                                      
             \<turnstile> \<langle>Dispose q, Normal (\<delta>,\<sigma>,\<Q>)\<rangle> \<Rightarrow> Normal (\<delta>,\<sigma>,QStateM(m', n \<cdot>\<^sub>q Q'))" *)

 | Dispose: "  \<Q> = \<Q>' + \<Q>'' \<Longrightarrow> \<Q>' ## \<Q>'' \<Longrightarrow> n = vec_norm (QStateM_vector \<Q>') \<Longrightarrow>
              QStateM_vars \<Q>' \<noteq> {} \<Longrightarrow> 
              QStateM_vars \<Q>' = (Q_domain_var (var_set q i \<sigma>) (QStateM_map \<Q>')) \<Longrightarrow>                                      
              \<forall>e \<in> (var_set q i \<sigma>). (QStateM_map \<Q>') e \<noteq> {} \<Longrightarrow>
             \<turnstile> \<langle>Dispose q i, Normal (\<delta>,\<sigma>,\<Q>)\<rangle> \<Rightarrow> Normal (\<delta>,\<sigma>, n \<cdot>\<^sub>Q  \<Q>'')"

\<comment>\<open>Dispose dispose will fail if it is not possible to find such states \<qq>',  \<qq>''\<close>

(* | Dispose_F: "\<nexists>\<Q>' \<Q>''.(\<Union>((QStateM_map \<Q>'') ` (q \<sigma>))) \<noteq> {} \<and> 
                Q_domain (QStateM_map \<Q>'') = (\<Union>((QStateM_map \<Q>'') ` (q \<sigma>)))  \<and> 
               \<Q> = \<Q>' + \<Q>'' \<and> \<Q>' ## \<Q>'' \<Longrightarrow>
               \<turnstile> \<langle>Dispose q, Normal (\<delta>,\<sigma>,\<Q>)\<rangle> \<Rightarrow> Fault" *)

| Dispose_F: "\<nexists>\<Q>' \<Q>''.  \<Q> = \<Q>' + \<Q>'' \<and> \<Q>' ## \<Q>'' \<and> QStateM_vars \<Q>' \<noteq> {} \<and> 
               QStateM_vars \<Q>' = (Q_domain_var (var_set q i \<sigma>) (QStateM_map \<Q>')) \<and>
               (\<forall>e \<in> (var_set q i \<sigma>). (QStateM_map \<Q>') e \<noteq> {}) \<Longrightarrow>
               \<turnstile> \<langle>Dispose q i, Normal (\<delta>,\<sigma>,\<Q>)\<rangle> \<Rightarrow> Fault"

\<comment>\<open>Measure measures the value of the set of qubits given by q \<sigma> and it stores the result in 
  the stack variable v. Similar to allocate, we will require that the construct is well formed
 and that the type of v is a real number\<close>

 (* | Measure: "q (\<sigma>,\<vv>) = (QState_vars \<qq>1) \<Longrightarrow> k \<in> {0.. 2^(card (q (\<sigma>,\<vv>)))} \<Longrightarrow>
            (\<delta>k, (\<vv>',\<qq>')) = measure_vars k (q (\<sigma>,\<vv>)) (\<vv>,\<qq>) \<Longrightarrow> \<qq> =   \<qq>1 +  \<qq>2 \<and> \<qq>1 ## \<qq>2 \<Longrightarrow>            
            \<delta>k > 0 \<Longrightarrow> \<delta>' = \<delta> * \<delta>k \<Longrightarrow> \<sigma>' = set_value \<sigma> v (from_nat k) \<Longrightarrow>
            \<turnstile> \<langle>Measure v q, Normal (\<delta>,\<sigma>,(\<vv>,\<qq>))\<rangle> \<Rightarrow> Normal (\<delta>',\<sigma>',(\<vv>',\<qq>'))"  *)

| Measure: "addr1 = \<Union>((QStateM_map \<Q>) ` (q \<sigma>)) \<Longrightarrow>
            (QStateM_vars \<Q>) = addr1 \<union> addr2 \<Longrightarrow>            
            k \<in> {0.. 2^(card addr1)} \<Longrightarrow>              
            (\<delta>k, \<Q>') = measure_vars k addr1 \<Q> \<Longrightarrow>             
            \<delta>k > 0 \<Longrightarrow> \<delta>' = \<delta> * \<delta>k \<Longrightarrow> \<sigma>' = set_value \<sigma> v (from_nat k) \<Longrightarrow>
            \<turnstile> \<langle>Measure v q, Normal (\<delta>,\<sigma>,\<Q>)\<rangle> \<Rightarrow> Normal (\<delta>',\<sigma>',\<Q>')"
\<comment>\<open>Since Measure access to the values of the qubits given by q \<sigma> as QMod, 
  Measure will similarly fail if the set of qubits to be mesured does not
  belong to the set of allocated qubits\<close>

 | Measure_F: "\<nexists>\<Q>' \<Q>''. \<not>(\<Union>((QStateM_map \<Q>') ` (q \<sigma>)) = (QStateM_vars \<Q>')) \<and>  
               \<Q> = \<Q>' + \<Q>'' \<and> \<Q>' ## \<Q>'' \<Longrightarrow> 
              \<turnstile> \<langle>Measure v q, Normal (\<delta>,\<sigma>,\<Q>)\<rangle> \<Rightarrow> Fault" 

| Fault_Prop:"\<turnstile> \<langle>C, Fault\<rangle> \<Rightarrow> Fault"



inductive_cases QExec_elim_cases [cases set]:
 "\<turnstile>\<langle>c,Fault\<rangle> \<Rightarrow>  t"  
  "\<turnstile>\<langle>Skip,s\<rangle> \<Rightarrow>  t"
  "\<turnstile>\<langle>SMod f,s\<rangle> \<Rightarrow>  t"
  "\<turnstile>\<langle>QMod m q,s\<rangle> \<Rightarrow>  t"
  "\<turnstile>\<langle>Seq c1 c2,s\<rangle> \<Rightarrow>  t"
  "\<turnstile>\<langle>While b c,s\<rangle> \<Rightarrow>  t"
  "\<turnstile>\<langle>IF b c1 c2,s\<rangle> \<Rightarrow>  t"
  "\<turnstile>\<langle>Measure v q,s\<rangle> \<Rightarrow>  t"
  "\<turnstile>\<langle>Alloc v q e,s\<rangle> \<Rightarrow>  t"
  "\<turnstile>\<langle>Dispose q i,s\<rangle> \<Rightarrow>  t"

inductive_cases QExec_Normal_elim_cases [cases set]:
 "\<turnstile>\<langle>c,Fault\<rangle> \<Rightarrow>  t"  
  "\<turnstile>\<langle>Skip,Normal s\<rangle> \<Rightarrow>  t"
  "\<turnstile>\<langle>SMod f,Normal s\<rangle> \<Rightarrow>  t"
  "\<turnstile>\<langle>QMod m q,Normal s\<rangle> \<Rightarrow>  t"
  "\<turnstile>\<langle>Seq c1 c2,Normal s\<rangle> \<Rightarrow>  t"
  "\<turnstile>\<langle>While b c1,Normal s\<rangle> \<Rightarrow>  t"
  "\<turnstile>\<langle>IF b c1 c2,Normal s\<rangle> \<Rightarrow>  t"
  "\<turnstile>\<langle>Measure v q,Normal s\<rangle> \<Rightarrow>  t"
  "\<turnstile>\<langle>Alloc v q e,Normal s\<rangle> \<Rightarrow>  t"
  "\<turnstile>\<langle>Dispose q v,Normal s\<rangle> \<Rightarrow>  t"

primrec modify_locals :: "('v, 's) com  \<Rightarrow> 'v set" where 
  "modify_locals  Skip = {}"
| "modify_locals (SMod f) = {v. modify_v f v = True}"
| "modify_locals (QMod _ _) = {}"
| "modify_locals (IF b c1 c2) = modify_locals c1 \<union> modify_locals c2"
| "modify_locals (While b c) = modify_locals c"
| "modify_locals (Seq c1 c2) = modify_locals c1 \<union> modify_locals c2"
| "modify_locals (Measure v e) = {v}"
| "modify_locals (Alloc v e val) = {v}"
| "modify_locals (Dispose q v) = {}"

thm QExec_Normal_elim_cases

lemma exec_Fault_end: assumes exec: "\<turnstile>\<langle>c,s\<rangle> \<Rightarrow>  t" and s: "s=Fault"
  shows "t=Fault"
using exec s by (induct) auto

end 

end


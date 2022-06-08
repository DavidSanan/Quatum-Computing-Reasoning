(* Title:     Quantum-Semantics/QSemantics.thy
   Author:    David Sanan, Nanyang Technological University m
   Copyright   2020
   License:     BSD
*)

theory QSemanticsSmall
  imports QSyntax  
begin           

subsection \<open>Syntax\<close>

text \<open>Semantics for quantum programs\<close>

(* m = partial_state2.ptensor_mat (dims_heap \<vv>) (q \<sigma>) ((Q_domain \<vv>)-(q \<sigma>)) (M::complex mat) (1\<^sub>m (card ((Q_domain \<vv>) - (q \<sigma>))))*)
(* abbreviation "tensor_vec \<equiv> partial_state2.ptensor_vec" *)

(* definition
  unit_vecl :: "nat \<Rightarrow> nat \<Rightarrow> complex list"
  where "unit_vecl n i = list_of_vec (unit_vec n i)" *)



definition aijv::"nat set \<Rightarrow> nat set \<Rightarrow> complex vec  \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>  complex"
  where "aijv d1 d2 v i j\<equiv>  v$(partial_state2.pencode12 d1 d2 (i,j))"

lemma eq_vec_aijv:
      assumes a0:"i<(dim_vec v)" and a1:"dim_vec (v::complex vec) = (2^(card v1)) * (2^(card v2))" and
              a2:"finite v1" and a3:"finite v2" and a4:"v1 \<inter> v2 = {}"        
       shows "v $ i = aijv v1 v2 v 
                    (partial_state.encode1 (list_dims (v1 \<union> v2))
                       (partial_state2.vars1' v1 v2) i) 
                    (partial_state.encode2 (list_dims (v1 \<union> v2)) 
                       (partial_state2.vars1' v1 v2) i)"
proof-
  interpret ps2:partial_state2 "(replicate ((2^(card v1)) * (2^(card v2))) 2)" v1 v2
    apply standard using a2 a3 a4  by auto
  let ?i = "(\<lambda>i. partial_state.encode1 ps2.dims0 (partial_state2.vars1' v1 v2) i)"
  let ?j = "(\<lambda>i. partial_state.encode2 ps2.dims0 (partial_state2.vars1' v1 v2) i)"
   have "v $ i = aijv v1 v2 v (?i i) (?j i)"
    unfolding aijv_def using a0
    by (simp add: a1 card_Un_disjoint partial_state.encode12_inv power_add ps2.dims0_def 
          ps2.disjoint ps2.finite_v1 
        ps2.finite_v2 ps2.pencode12_def ps2.vars0_def state_sig.d_def)  
  moreover have "ps2.dims0 = (list_dims (v1 \<union> v2))"
    by (simp add: list_dims_def ps2.dims0_def ps2.vars0_def)
  ultimately show ?thesis 
    unfolding  list_dims_def ps2.dims0_def ps2.vars0_def  by auto
qed

lemma eq_vec_aijv_v2_empty:
      assumes a0:"i<(dim_vec v)" and a1:"dim_vec (v::complex vec) = (2^(card v1)) * (2^(card v2))" and
              a2:"finite v1" and a3:"v2 = {}" and a4:"v1 \<inter> v2 = {}"        
       shows "v $ i = aijv v1 v2 v i 0"
proof-
  interpret ps2:partial_state2 "(replicate ((2^(card v1)) * (2^(card v2))) 2)" v1 v2
    apply standard using a2 a3 a4  by auto
  let ?i = "(\<lambda>i. partial_state.encode1 ps2.dims0 (partial_state2.vars1' v1 v2) i)"
  let ?j = "(\<lambda>i. partial_state.encode2 ps2.dims0 (partial_state2.vars1' v1 v2) i)"
  have "v $ i = aijv v1 v2 v (?i i) (?j i)"
    unfolding aijv_def using a0
    by (simp add: a1 card_Un_disjoint partial_state.encode12_inv power_add ps2.dims0_def 
          ps2.disjoint ps2.finite_v1 
        ps2.finite_v2 ps2.pencode12_def ps2.vars0_def state_sig.d_def)  
  moreover have "(?j i) = 0" 
    unfolding partial_state.encode2_def ps2.dims0_def    
    using a3 digit_decode_non_vars1 partial_state.dims2_def 
          partial_state2.vars1'_def ps2.partial_state2_axioms ps2.vars0_def 
    by auto
  moreover have "(?i i) = i" using a3
    unfolding  list_dims_def ps2.dims0_def ps2.vars0_def apply auto
    by (metis Int_absorb a0 digit_decode_vars ind_in_set_id length_replicate local.a1 order_refl partial_state.dims2_def partial_state.encode2_alter partial_state2.length_dims0_minus_vars2'_is_vars1' partial_state2.vars1'_def prod_list_replicate ps2.d0_def ps2.d1_def ps2.d2_def ps2.dims0_def ps2.dims1_def ps2.dims2_def ps2.dims_product ps2.finite_v1 ps2.nths_vars1' ps2.nths_vars1'_comp ps2.partial_state2_axioms ps2.ptensor_encode1_encode2 ps2.vars0_def sup_bot.right_neutral)   
  ultimately show ?thesis using a3
     by auto    
qed

definition vector_aij::"nat set \<Rightarrow> nat set \<Rightarrow> complex vec  \<Rightarrow> nat \<Rightarrow> complex vec"
  where "vector_aij d1 d2 v i \<equiv> Matrix.vec (2^card d2) (\<lambda>j. aijv d1 d2 v i j)"

definition list_aij::"nat set \<Rightarrow> nat set \<Rightarrow> complex vec  \<Rightarrow> nat \<Rightarrow> complex list"
  where "list_aij d1 d2 v i \<equiv> map (\<lambda>j. aijv d1 d2 v i j) [0..<2^card d2]"

definition aij ::"'s state \<Rightarrow> 's expr_q  \<Rightarrow> ('s, complex list) expr \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>complex" 
  where "aij s q v i j \<equiv> let st = get_stack s ; qv = fst (get_qstate s); 
                             vars = Q_domain qv; d1 = q st; d2 = vars - d1;
                             vec = vec_of_list (v st) in 
                             aijv d1 d2 vec i j"


definition matrix_sep :: "nat set \<Rightarrow>  QStateM \<Rightarrow> complex mat \<Rightarrow>  QStateM" 
  where "matrix_sep heap_ind q M \<equiv>
           let sep_vars = \<Union> ((QStateM_map q) ` heap_ind)  in
           let var_d = QStateM_vars q in 
           let var_r = var_d - sep_vars in
           let v = QStateM_vector q in           
           let m = ptensor_mat sep_vars var_r
                               (M::complex mat) (1\<^sub>m (2^(card var_r)))  in 
             Q_State.QStateM (QStateM_map q, QState (var_d, list_of_vec (m *\<^sub>v v)))"
                                      
definition matrix_sep_var :: "nat set \<Rightarrow>  QStateM \<Rightarrow> complex mat \<Rightarrow>  complex vec" 
  where "matrix_sep_var heap_ind q M \<equiv>
           let sep_vars = \<Union> ((QStateM_map q) ` heap_ind)  in
           let var_d = QStateM_vars q in 
           let var_r = var_d - sep_vars in
           let v = QStateM_vector q in           
           let m = ptensor_mat sep_vars var_r
                               (M::complex mat) (1\<^sub>m (2^(card var_r)))  in 
              m *\<^sub>v v"

definition matrix_sep_not_zero :: "nat set \<Rightarrow>  QStateM \<Rightarrow> complex mat \<Rightarrow>  bool" 
  where "matrix_sep_not_zero heap_ind q M \<equiv>             
             \<exists>i<length (list_of_vec (matrix_sep_var heap_ind q M)). 
                list_of_vec (matrix_sep_var heap_ind q M)!i \<noteq> 0"


lemma matrix_sep_wf:
      "\<Union> (QStateM_map q ` hi) \<noteq> {} \<Longrightarrow> sep_vars = \<Union> ((QStateM_map q) ` hi) \<Longrightarrow>
       var_d =  QStateM_vars q \<Longrightarrow> var_r = var_d - sep_vars \<Longrightarrow>  
       matrix_sep_not_zero hi q M \<Longrightarrow> 
       Q_State.QStateM(m, QState(vs,v')) = matrix_sep hi q M \<Longrightarrow>
       QState_wf (vs,v') \<and> QStateM_wf (m,QState(vs,v'))"
proof-     
  assume a0:"\<Union> (QStateM_map q ` hi) \<noteq> {}" and
   a1:"sep_vars = \<Union> ((QStateM_map q) ` hi)" and
   a2:"var_d =  QStateM_vars q" and a3:"var_r = var_d - sep_vars" and
   a4:"matrix_sep_not_zero hi q M" and
   a5:"Q_State.QStateM(m, QState(vs,v')) = matrix_sep hi q M"  
  have hi_not_e:"hi\<noteq>{}" using a1 a0 by auto
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
  ultimately have finite_Q_domain:"finite (Q_domain (QStateM_map q))" 
    unfolding QState_wf_def by auto   
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
  have Q_wf:"QState_wf (QStateM_vars q, list_of_vec (?m *\<^sub>v ?v))" unfolding QState_wf_def using a4
    unfolding matrix_sep_def Let_def matrix_sep_not_zero_def 
    apply (auto simp add: matrix_sep_var_def)
    unfolding ps2.d0_def ps2.dims0_def ps2.vars0_def apply transfer   
    unfolding Q_domain_def apply auto
     apply (metis UN_Un Un_UNIV_right )
    by (simp add: QStateM_vars.rep_eq QState_rel3')    
  then have f1:"QState_vars (QState (QStateM_vars q, list_of_vec (?m *\<^sub>v ?v))) = 
             QStateM_vars q"
    using QState_var_idem
    by blast   
  then have q:"QStateM_wf (QStateM_map q, QState (?var_d, list_of_vec (?m *\<^sub>v ?v)))"    
    using eq_QStateM_vars qm_wf by auto      
  then have "m = QStateM_map q" using a5 unfolding matrix_sep_def Let_def 
    using eq_QStateM_dest[OF  domain_map_not_e q] by metis
  then show ?thesis using a5 unfolding matrix_sep_def Let_def 
    using  eq_QStateM_dest[OF domain_map_not_e q]
    by (metis QState.rep_eq QState_vars.rep_eq domain_map_not_e fst_conv q snd_conv)    
qed

lemma matrix_sep_dest:
      "sep_vars \<noteq> {} \<Longrightarrow> sep_vars = Q_domain_var hi (QStateM_map q)  \<Longrightarrow>
       var_d =  QStateM_vars q \<Longrightarrow> var_r = var_d - sep_vars \<Longrightarrow>   matrix_sep_not_zero hi q  M \<Longrightarrow>
       QStateM_map (matrix_sep hi q M) = QStateM_map q \<and> 
       QStateM_vars (matrix_sep hi q M) = QStateM_vars q \<and>
       QStateM_list (matrix_sep hi q M) = 
         list_of_vec (ptensor_mat sep_vars var_r
                               (M::complex mat) (1\<^sub>m (2^(card var_r))) *\<^sub>v 
                      QStateM_vector q)"  
proof- 
  assume a0:"sep_vars \<noteq> {}" and
   a1:"sep_vars = Q_domain_var hi (QStateM_map q)" and
   a2:"var_d =  QStateM_vars q" and a3:"var_r = var_d - sep_vars" and a4:" matrix_sep_not_zero hi q M"
  note a1= a1[simplified Q_domain_var_def] and a0 = a0[simplified a1]
  
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
  obtain vs vas v' where 
   matrix_sep_eq:"Q_State.QStateM(vs, QState(vas,v')) = matrix_sep hi q M"
    unfolding matrix_sep_def Let_def by auto
  then have QState_wf:"QState_wf (vas,v')" and QStateM_wf:"QStateM_wf (vs,QState(vas,v'))"
    using matrix_sep_wf[OF a0 a1 a2 a3 a4  matrix_sep_eq]
    by auto    
  then have "QStateM_map (matrix_sep hi q M) = QStateM_map q"         
    using  matrix_sep_eq
    unfolding matrix_sep_def Let_def
    by (smt (verit, ccfv_threshold) QStateM_wf_map a0 a4 matrix_sep_eq matrix_sep_wf)    
  moreover have "QStateM_vars (matrix_sep hi q M) = QStateM_vars q"
    using matrix_sep_eq calculation
    unfolding matrix_sep_def Let_def
    by (metis QStateM_rel1 QStateM_vars.rep_eq qstate_def)
  moreover have "QStateM_list (matrix_sep hi q M) = 
         list_of_vec (ptensor_mat sep_vars var_r
                               (M::complex mat) (1\<^sub>m (2^(card var_r))) *\<^sub>v 
                      QStateM_vector q)"          
    using matrix_sep_wf[OF a0 a1 a2 a3 a4, of "QStateM_map q" ?var_d "list_of_vec (?m *\<^sub>v ?v)"]
    unfolding matrix_sep_def Let_def
    by (metis QStateM_wf_list QState_list_idem a3 local.a1 local.a2)
  ultimately show ?thesis by auto
qed


lemma i_less_union: 
  assumes a0:"(i::nat) < 2 ^ card v1 * 2 ^ card v2" and
    a1:"v1 \<inter> v2 = {}" and
    a2:"finite v1" and
    a3:"finite v2"
  shows"i < 2 ^ card (v1 \<union> v2)"
  using a0 a1 a2 a3
  by (simp add: card_Un_disjoint power_add)

lemma mat_extend_M_1k_zero: 
     assumes a0:"finite v1" and a1:"finite v2" and a2:"v1 \<inter> v2 = {}" and
       a3:"i < (2^(card v1)) * (2^(card v2))" and
       a4:"j < (2^(card v1)) * (2^(card v2))" and 
       a7:"partial_state.encode2 (list_dims (v1 \<union> v2)) (partial_state2.vars1' v1 v2) i \<noteq>
           partial_state.encode2 (list_dims (v1 \<union> v2)) (partial_state2.vars1' v1 v2) j"
       shows "ptensor_mat v1 v2 M (1\<^sub>m (2^(card v2))) $$ (i,j) = 0"
proof-
  let ?m1 = "M" and ?m2 = "1\<^sub>m (2^(card v2))" and ?d = "list_dims (v1 \<union> v2)"
  let ?v = "partial_state2.vars1' v1 v2"   

  interpret ps2:partial_state2 "list_dims (v1 \<union> v2)" v1 v2
    apply standard using a0 a1 a2 unfolding list_dims_def by auto

 let ?enc1 = "partial_state.encode1 ps2.dims0 ?v" and
     ?enc2 = "partial_state.encode2 ps2.dims0 ?v"

  have "ps2.dims0 = ?d" unfolding ps2.dims0_def list_dims_def ps2.vars0_def by auto
  moreover have "ps2.ptensor_mat ?m1 ?m2 $$ (i,j) = 
        ?m1 $$ (?enc1 i, ?enc1 j) * ?m2 $$ (?enc2 i, ?enc2  j)"
    unfolding ps2.ptensor_mat_def 
    apply (rule  partial_state.tensor_mat_eval, auto simp add: ps2.dims0_def state_sig.d_def ps2.vars0_def) 
    using i_less_union[OF _ a2 a0 a1] a3 a4 by auto
  moreover have " ?m2 $$ (?enc2 i, ?enc2  j) = 0"
    by (metis a3 a4 a7 calculation(1) index_one_mat(1) partial_state.d2_def partial_state.dims2_def 
              partial_state.encode2_lt prod_list_replicate ps2.d0_def 
                ps2.d1_def ps2.d2_def ps2.d_def ps2.dims1_def ps2.dims2_def 
              ps2.dims_product ps2.nths_vars2')
  ultimately show ?thesis
    using mult_not_zero by auto   
qed


lemma mat_extend_M_1k_M: 
     assumes a0:"finite v1" and a1:"finite v2" and a2:"v1 \<inter> v2 = {}" and
       a3:"i < (2^(card v1)) * (2^(card v2))" and
       a4:"j < (2^(card v1)) * (2^(card v2))" and 
       a7:"partial_state.encode2 (list_dims (v1 \<union> v2)) (partial_state2.vars1' v1 v2) i =
           partial_state.encode2 (list_dims (v1 \<union> v2)) (partial_state2.vars1' v1 v2) j"
     shows "ptensor_mat v1 v2 M (1\<^sub>m (2^(card v2))) $$ (i,j) = 
            M $$ (partial_state.encode1 (list_dims (v1 \<union> v2)) (partial_state2.vars1' v1 v2) i,
                 (partial_state.encode1 (list_dims (v1 \<union> v2)) (partial_state2.vars1' v1 v2) j))"
proof-
  let ?m1 = "M" and ?m2 = "1\<^sub>m (2^(card v2))" and ?d = "list_dims (v1 \<union> v2)"
  let ?v = "partial_state2.vars1' v1 v2"   

  interpret ps2:partial_state2 "list_dims (v1 \<union> v2)" v1 v2
    apply standard using a0 a1 a2 unfolding list_dims_def by auto

 let ?enc1 = "partial_state.encode1 ps2.dims0 ?v" and
     ?enc2 = "partial_state.encode2 ps2.dims0 ?v"

  have "ps2.dims0 = ?d" unfolding ps2.dims0_def list_dims_def ps2.vars0_def by auto
  moreover have "ps2.ptensor_mat ?m1 ?m2 $$ (i,j) = 
        ?m1 $$ (?enc1 i, ?enc1 j) * ?m2 $$ (?enc2 i, ?enc2  j)"
    unfolding ps2.ptensor_mat_def 
    apply (rule  partial_state.tensor_mat_eval, auto simp add: ps2.dims0_def state_sig.d_def ps2.vars0_def) 
    using i_less_union[OF _ a2 a0 a1] a3 a4 by auto
  moreover have " ?m2 $$ (?enc2 i, ?enc2  j) = 1"
    by (metis  a4 a7 calculation(1) index_one_mat(1) partial_state.d2_def partial_state.dims2_def 
              partial_state.encode2_lt prod_list_replicate ps2.d0_def 
                ps2.d1_def ps2.d2_def ps2.d_def ps2.dims1_def ps2.dims2_def 
              ps2.dims_product ps2.nths_vars2')
  ultimately show ?thesis using mult.comm_neutral by metis    
qed

lemma inn_mat_extend_M_1k_M_v: 
     assumes a0:"finite v1" and a1:"finite v2" and a2:"v1 \<inter> v2 = {}" and
       a3:"i < (2^(card v1)) * (2^(card v2))" and
       a5:"dim_vec (V::complex vec) = (2^(card v1)) * (2^(card v2))"
     shows "(ptensor_mat v1 v2 M (1\<^sub>m (2^(card v2))) *\<^sub>v V) $ i = 
             row (ptensor_mat v1 v2 M (1\<^sub>m (2^(card v2)))) i \<bullet> V"
proof -
  have "i < dim_row (ptensor_mat v1 v2 M (1\<^sub>m (2 ^ card v2)))"
    by (simp add: a0 a3 local.a1 local.a2 ptensor_mat_dim_row)
  then show ?thesis
    by (meson index_mult_mat_vec)
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

(* definition measure_vars1::"nat \<Rightarrow>  nat set \<Rightarrow> qstate  \<Rightarrow> (real \<times> qstate)"
  where "measure_vars1 k  sep_vars q \<equiv>
   let qs = snd q in
   let vars_dom = QState_vars qs in
    let v =   QState_vector qs in
    let vars= (vars_dom - sep_vars) in        
    let mk = partial_state2.ptensor_mat  sep_vars vars (1\<^sub>k (2^(card sep_vars))) (1\<^sub>m (2^(card vars))) in
    let v' =  mk  *\<^sub>v v in 
    let \<delta>k =  Re ((vec_norm v')^2 div (vec_norm v)^2) in    
    let qnprod = list_of_vec (((sqrt \<delta>k)::complex) \<cdot>\<^sub>v v') in
       (\<delta>k, (fst q, QState (vars_dom, qnprod)))"  *)

(* definition measure_vars::"nat \<Rightarrow>  nat set \<Rightarrow>  QStateM  \<Rightarrow> (real \<times>  QStateM)"
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
       (\<delta>k, QStateM(qm, QState (vars_dom, qnprod)))" *)

definition measure_vars::"nat \<Rightarrow>  nat set \<Rightarrow>  QStateM  \<Rightarrow> (real \<times>  QStateM)"
  where "measure_vars k  heap_ind q \<equiv>
   let sep_vars = \<Union>((QStateM_map q) ` heap_ind) in
   let Q' = matrix_sep heap_ind q (1\<^sub>k (2^(card sep_vars))) in
   let \<delta>k =  Re ((vec_norm (matrix_sep_var heap_ind q (1\<^sub>k (2^(card sep_vars)))))^2 div (vec_norm (QStateM_vector q))^2) in
     (\<delta>k, (1 / sqrt (\<delta>k)) \<cdot>\<^sub>Q Q')"


definition measure_vars'::"nat \<Rightarrow>  nat set \<Rightarrow>  QStateM  \<Rightarrow> (real \<times>  QStateM)"
  where "measure_vars' k  heap_ind q \<equiv>   
   let sep_vars = \<Union>((QStateM_map q) ` heap_ind) in  
   let Q' = matrix_sep heap_ind q (1\<^sub>k (2^(card sep_vars))) in
   let \<delta>k =  Re ((vec_norm (matrix_sep_var heap_ind q (1\<^sub>k (2^(card sep_vars)))))^2 div (vec_norm (QStateM_vector q))^2) in   
     if sep_vars = QStateM_vars q then 
       (\<delta>k, Q_State.QStateM (QStateM_map q, Q_State.QState(QStateM_vars q, list_of_vec (unit_vec (2^(card sep_vars)) k))))
     else (\<delta>k, (1 / sqrt (\<delta>k)) \<cdot>\<^sub>Q Q')"

lemma measure_vars'_neq:"QStateM_vars Q \<noteq> \<Union>((QStateM_map Q) ` q) \<Longrightarrow> 
      measure_vars' k q Q = measure_vars k q Q"
  unfolding measure_vars'_def measure_vars_def Let_def by auto



lemma eq_QState_dest: "vs \<noteq> {} \<Longrightarrow>
       QState_wf (vs, v) \<Longrightarrow> 
       QState(vs, v) = QState(vs', v') \<Longrightarrow> 
       vs = vs' \<and> v = v'" 
   apply transfer'
  by (metis Pair_inject prod.collapse)

lemma measure_vars_dest:
  assumes 
       a0:"n = Re ((vec_norm (matrix_sep_var q Q 1\<^sub>i (2 ^ card (\<Union> (QStateM_map Q ` q)))))\<^sup>2 /
             (vec_norm (QStateM_vector Q))\<^sup>2)"
     shows "measure_vars i q Q = (n, (1 / sqrt (n)) \<cdot>\<^sub>Q matrix_sep q Q (1\<^sub>i ((2::nat) ^ card (\<Union> (QStateM_map Q ` q)))))"
  using a0
  unfolding measure_vars_def Let_def by auto

lemma measure_vars'_dest:  
  assumes a0:"QStateM_vars Q = \<Union>((QStateM_map Q) ` q)" and 
          a1:"n = Re ((vec_norm ((matrix_sep_var q Q 1\<^sub>i (2 ^ card (\<Union> (QStateM_map Q ` q))))))\<^sup>2 /
             (vec_norm (QStateM_vector Q))\<^sup>2)"
  shows "measure_vars' i q Q = 
       (n, Q_State.QStateM (QStateM_map Q, QState(QStateM_vars Q, 
           list_of_vec (unit_vec (2^(card (\<Union> (QStateM_map Q ` q)))) i))))"  
  using a0 a1
  unfolding measure_vars'_def Let_def by auto

lemma matrix_sep_var_not_zero:
  assumes a0:"\<delta>k = Re ((vec_norm ((matrix_sep_var q Q 1\<^sub>i (2 ^ card (\<Union> (QStateM_map Q ` q))))))\<^sup>2 /
             (vec_norm (QStateM_vector Q))\<^sup>2)" and
          a1:"\<delta>k > 0"
  shows "(matrix_sep_var q Q 1\<^sub>i (2 ^ card (\<Union> (QStateM_map Q ` q)))) \<noteq> 
         0\<^sub>v (dim_vec (matrix_sep_var q Q 1\<^sub>i (2 ^ card (\<Union> (QStateM_map Q ` q)))))"
proof-
  have "vec_norm (matrix_sep_var q Q 1\<^sub>i (2 ^ card (\<Union> (QStateM_map Q ` q)))) \<noteq> 0"
    using a0 a1 by auto  
  then show ?thesis using vec_norm_zero
    by (metis  zero_carrier_vec)
qed
  

lemma measure_vars_wf:
  assumes
   a0:"(\<delta>k, Q_State.QStateM(qm, QState (vars_dom, qnprod))) = measure_vars i q Q" and
   a1:"\<forall>e \<in> q. QStateM_map Q e \<noteq> {}" and a2:"q \<noteq> {}" and a4:"\<delta>k > 0"
  shows "QState_wf (vars_dom,qnprod) \<and> QStateM_wf (qm, QState(vars_dom,qnprod))"
proof-
  let ?sep_vars = "Q_domain_var q (QStateM_map Q)" 
  let ?var_r = "(QStateM_vars Q) - ?sep_vars"
  let ?m = "1\<^sub>i ((2::nat) ^ card ?sep_vars)"
  let ?v = "matrix_sep q Q ?m"
  let ?v' = "matrix_sep_not_zero q Q ?m"
  let ?n = "Re ((vec_norm ((matrix_sep_var q Q 1\<^sub>i (2 ^ card (\<Union> (QStateM_map Q ` q))))))\<^sup>2 /
             (vec_norm (QStateM_vector Q))\<^sup>2)"  
  have \<delta>:"\<delta>k = ?n"
    using a0 unfolding measure_vars_def Let_def vec_norm_def Q_domain_var_def by auto
  have re_p_gt0:"Re ?n > 0"  and im_p_0:"Im ?n = 0"
    using a0 a4 unfolding measure_vars_def Let_def vec_norm_def Q_domain_var_def by auto
  then have not_zero:"1 / sqrt (Re ?n)\<noteq> 0"
    by auto
  then have QStateM_map_v:"QStateM_map ((1 / sqrt (Re ?n)) \<cdot>\<^sub>Q ?v) = QStateM_map ?v"
    using sca_mult_qstatem_var_map
    by (simp add: QStateM_rel1 QStateM_rel2 QStateM_wf_map sca_mult_qstate_vars sca_mult_qstatem_def)

  have qstate_eq:"qstate ((1 / sqrt (Re ?n)) \<cdot>\<^sub>Q ?v) = (1 / sqrt (Re ?n)) \<cdot>\<^sub>q qstate ?v"
    using  not_zero
    by (simp add: QStateM_rel1 QStateM_rel2 QStateM_wf_qstate sca_mult_qstate_vars sca_mult_qstatem_def)
    
  have measure_eq:"Q_State.QStateM(QStateM_map ?v, (1 / sqrt (Re ?n)) \<cdot>\<^sub>q qstate ?v) = 
             Q_State.QStateM(qm, QState (vars_dom, qnprod))"
    using a0 unfolding sca_mult_qstatem_def measure_vars_def Let_def Q_domain_var_def  by auto
    
  have f1:"QStateM_wf (QStateM_map ?v, (1 / sqrt (Re ?n)) \<cdot>\<^sub>q qstate ?v) \<and> 
           QState_wf (QState_vars ((1 / sqrt (Re ?n)) \<cdot>\<^sub>q qstate ?v), 
                      QState_list ((1 / sqrt (Re ?n)) \<cdot>\<^sub>q qstate ?v))"    
    by (metis qstate_eq QState_wf QStateM_wf QStateM_map_v) 
  have  "matrix_sep_not_zero q Q ?m"
    unfolding  Q_domain_var_def Let_def matrix_sep_not_zero_def using matrix_sep_var_not_zero[OF \<delta> a4]
    using zero_vec_list by auto
  moreover have "?sep_vars \<noteq> {}" unfolding Q_domain_var_def using a1 a2 by auto
  ultimately have qmap:"QStateM_map ?v = QStateM_map Q"     
    by (auto simp add: matrix_sep_dest local.a1 local.a2)
  have h1:"Q_domain (QStateM_map ?v) \<noteq> {}"
    unfolding Q_domain_def
    using local.a1 local.a2 qmap by auto
  have "QStateM_map Q = qm" and eq_QState:"(1 / sqrt (Re ?n)) \<cdot>\<^sub>q qstate ?v = QState(vars_dom,qnprod)"
    using eq_QStateM_dest[OF h1 conjunct1[OF f1] measure_eq] qmap  by auto  
  then have QStateM_wf:"QStateM_wf (qm, QState(vars_dom,qnprod))"
    using f1 qmap by auto 
  
  have "QState_vars ((1 / sqrt (Re ?n)) \<cdot>\<^sub>q qstate ?v) = vars_dom \<and>
             QState_list ((1 / sqrt (Re ?n)) \<cdot>\<^sub>q qstate ?v) = qnprod"
    using eq_QState_dest
    by (metis QStateM_rel1 QState_refl QStateM_map_v qstate_eq eq_QState f1 local.h1)
  moreover have "QState (vars_dom,qnprod) = (1 / sqrt (Re ?n)) \<cdot>\<^sub>q qstate ?v"
    using eq_QState by auto
  moreover have "QState_wf (QState_vars ((1 / sqrt (Re ?n)) \<cdot>\<^sub>q qstate ?v), QState_list ((1 / sqrt (Re ?n)) \<cdot>\<^sub>q qstate ?v))"
    using f1
    by auto
  ultimately have "QState_wf (vars_dom, qnprod)" by auto
  then show ?thesis using QStateM_wf by auto
qed

lemma measure_vars'_wf1:
  assumes a0:"QStateM_vars Q = \<Union>((QStateM_map Q) ` q)" and
   a1:"\<forall>e \<in> q. QStateM_map Q e \<noteq> {}" and a2:"q \<noteq> {}" and a3:"2 ^ card (\<Union> (QStateM_map Q ` q)) > i"
 shows "QState_wf (QStateM_vars Q,list_of_vec (unit_vec (2 ^ card (\<Union> (QStateM_map Q ` q))) i)) \<and> 
        QStateM_wf (QStateM_map Q, QState(QStateM_vars Q,list_of_vec (unit_vec (2 ^ card (\<Union> (QStateM_map Q ` q))) i)))"
proof-
  have "QState_wf (QStateM_vars Q, QStateM_list Q)" 
    using QStateM_list.rep_eq QStateM_vars.rep_eq QState_wf by auto    
  then have "QState_wf (QStateM_vars Q,list_of_vec (unit_vec (2 ^ card (\<Union> (QStateM_map Q ` q))) i))"
    using a0 a1 a2 a3 apply simp unfolding unit_vec_def QState_wf_def by auto
  moreover have "QStateM_wf (QStateM_map Q, QState(QStateM_vars Q,list_of_vec (unit_vec (2 ^ card (\<Union> (QStateM_map Q ` q))) i)))"
    using a0 a1 a2 apply auto
    using QStateM_wf QState_var_idem calculation eq_QStateM_vars apply auto[1]
    using QState.rep_eq QStateM_wf QState_vars.rep_eq calculation eq_QStateM_vars apply auto[1]
    using QStateM_wf by fastforce
  ultimately show ?thesis by auto  
qed

lemma measure_vars'_wf:
  assumes
   a0:"(\<delta>k, Q_State.QStateM(qm, QState (vars_dom, qnprod))) = measure_vars' i q Q" and
   a1:"\<forall>e \<in> q. QStateM_map Q e \<noteq> {}" and a2:"q \<noteq> {}" and 
   a4:"(2 ^ card (\<Union> (QStateM_map Q ` q))) > i" and a5:"\<delta>k > 0"
 shows "QState_wf (vars_dom,qnprod) \<and> QStateM_wf (qm, QState(vars_dom,qnprod))"
proof-
  let ?\<delta> = "Re ((vec_norm
        (QStateM_vector (matrix_sep q Q 1\<^sub>i (2 ^ card (\<Union> (QStateM_map Q ` q))))))\<^sup>2 /
      (vec_norm (QStateM_vector Q))\<^sup>2)" and 
     ?v = " list_of_vec (unit_vec (2 ^ card (\<Union> (QStateM_map Q ` q))) i)"
  { assume a00:"QStateM_vars Q = \<Union>((QStateM_map Q) ` q)"    
    note measure = measure_vars'_dest[OF a00, of ?\<delta> i, simplified]  
    
    have QStateM_wf:"QStateM_wf (QStateM_map Q, QState (QStateM_vars Q, ?v))" and
         QState_wf:"QState_wf (QStateM_vars Q,?v) "
      using measure_vars'_wf1[OF a00 a1 a2 a4] by blast+      
    
    have q_domain:"Q_domain (QStateM_map Q) \<noteq> {}"
      using Q_domain_def local.a1 local.a2 by auto        
    then have vars_not_empty:"QStateM_vars Q \<noteq> {}"
      using QStateM_rel1 QStateM_vars.rep_eq  qstate_def by auto
    
    have QStateM_eq:"Q_State.QStateM (QStateM_map Q, QState (QStateM_vars Q, ?v)) =
                   Q_State.QStateM(qm, QState (vars_dom, qnprod))" using measure a0
      using a00 measure_vars'_dest by auto
    
    have eq_qm:"QStateM_map Q = qm"
      using  measure q_domain QStateM_wf QStateM_eq
      by (simp add: eq_QStateM_dest)                 
    
    have "QStateM_vars Q = vars_dom" 
      using eq_QStateM_dest[OF q_domain QStateM_wf  QStateM_eq]
      eq_QState_dest[OF vars_not_empty QState_wf] by blast
    moreover have "?v = qnprod"   
      using eq_QStateM_dest[OF q_domain QStateM_wf  QStateM_eq]
      eq_QState_dest[OF vars_not_empty QState_wf] by blast
    ultimately have ?thesis
      using eq_qm local.QStateM_wf local.QState_wf by blast
  }
  moreover {
    assume a00:"QStateM_vars Q \<noteq> \<Union>((QStateM_map Q) ` q)"
    have eq:"(\<delta>k, Q_State.QStateM(qm, QState (vars_dom, qnprod))) = measure_vars i q Q" 
      using measure_vars'_neq[OF a00] a0 by auto
    note measure_vars_wf[OF eq a1 a2 a5] 
    then have ?thesis by auto
  } ultimately show ?thesis by fastforce
qed


lemma measure_vars_dest_QStateM:
  assumes   
   a1:"\<forall>e \<in> q. QStateM_map Q e \<noteq> {}" and a2:"q \<noteq> {}" and a4:"0 < n" and 
   a3:"n = Re ((vec_norm
             ((matrix_sep_var q Q 1\<^sub>i (2 ^ card (\<Union> (QStateM_map Q ` q))))))\<^sup>2 /
             (vec_norm (QStateM_vector Q))\<^sup>2)"
 shows "QStateM_map (snd (measure_vars i q Q)) = QStateM_map Q \<and> 
        QStateM_vars (snd (measure_vars i q Q)) = QStateM_vars Q \<and>
        QStateM_vector (snd (measure_vars i q Q)) = 
        QStateM_vector ((1 / sqrt (n)) \<cdot>\<^sub>Q (matrix_sep q Q (1\<^sub>i ((2::nat) ^ card (\<Union> (QStateM_map Q ` q))))))"
proof-
  let ?sep_vars = "Q_domain_var q (QStateM_map Q)" 
  let ?m = "1\<^sub>i ((2::nat) ^ card ?sep_vars)"
  let ?v = "matrix_sep q Q ?m"  
  let ?var_r = "(QStateM_vars Q) - ?sep_vars"
  have scalar_not_zero:"1 / sqrt n \<noteq> 0"
    using a4 by force 
  have m:"measure_vars i q Q = (n, (1 / sqrt (n)) \<cdot>\<^sub>Q matrix_sep q Q 1\<^sub>i (2 ^ card (\<Union> (QStateM_map Q ` q))))" 
    using measure_vars_dest[OF a3] by auto
  have "?sep_vars \<noteq> {}" unfolding Q_domain_var_def using a1 a2 by auto 
  moreover have "matrix_sep_not_zero q Q 1\<^sub>i (2 ^ card (\<Union> (QStateM_map Q ` q)))"
    by (metis a3 a4 matrix_sep_not_zero_def matrix_sep_var_not_zero zero_vec_list) 
  ultimately have  maps:"QStateM_map ?v = QStateM_map Q" and 
       vars:"QStateM_vars ?v = QStateM_vars Q" and
       list:"QStateM_list ?v = 
         list_of_vec (ptensor_mat ?sep_vars ?var_r
                               ?m (1\<^sub>m (2^(card ?var_r))) *\<^sub>v 
                      QStateM_vector Q) "
    using Q_domain_var_def matrix_sep_dest by presburger+
  then have "QStateM_map (snd (measure_vars i q Q)) = QStateM_map Q"
    using a3 a4 m sca_mult_qstatem_var_map scalar_not_zero 
    unfolding Q_domain_var_def
    by (smt (verit, ccfv_threshold) QStateM_wf QStateM_wf_map of_real_eq_0_iff prod.sel(1) sca_mult_qstate_vars sca_mult_qstatem_def snd_conv)
  moreover have "QStateM_vars (snd (measure_vars i q Q)) = QStateM_vars Q"
    using a3 a4 m sca_mult_qstatem_var_map vars
    by (metis QStateM_rel1 QStateM_vars.rep_eq calculation qstate_def)
  moreover have  "QStateM_vector (snd (measure_vars i q Q)) = 
                  QStateM_vector ((1 / sqrt (n)) \<cdot>\<^sub>Q (matrix_sep q Q (1\<^sub>i ((2::nat) ^ card (\<Union> (QStateM_map Q ` q))))))"
    using a3 a4 m sca_mult_qstatem_var_map vars
    by simp
  ultimately show ?thesis by auto
qed

lemma QStateM_wf_vector:"QStateM_wf (vs, v) \<Longrightarrow> 
                       QStateM_vector (Q_State.QStateM (vs, v)) = QState_vector v"
  apply transfer' by auto

lemma QState_vector_idem:"QState_wf (vs, list_of_vec v) \<Longrightarrow> 
       QState_vector (QState (vs, list_of_vec v)) =  v"
  apply transfer'
  using vec_list by auto
  

lemma measure_vars'_dest_QStateM:
  assumes a0:"QStateM_vars Q = \<Union>((QStateM_map Q) ` q)"   and   
   a1:"\<forall>e \<in> q. QStateM_map Q e \<noteq> {}" and a2:"q \<noteq> {}" and a4:"0 < n" and 
   a5:"(2 ^ card (\<Union> (QStateM_map Q ` q))) > i" and
   a3:"n = Re ((vec_norm
             (matrix_sep_var q Q 1\<^sub>i (2 ^ card (\<Union> (QStateM_map Q ` q)))))\<^sup>2 /
             (vec_norm (QStateM_vector Q))\<^sup>2)"
 shows "QStateM_map (snd (measure_vars' i q Q)) = QStateM_map Q \<and> 
        QStateM_vars (snd (measure_vars' i q Q)) = QStateM_vars Q \<and>
        QStateM_vector (snd (measure_vars' i q Q)) = unit_vec (2^(card (\<Union> (QStateM_map Q ` q)))) i"
proof-
  let ?sep_vars = "Q_domain_var q (QStateM_map Q)" 
  let ?v = "unit_vec (2^(card (\<Union> (QStateM_map Q ` q)))) i"  
  let ?var_r = "(QStateM_vars Q) - ?sep_vars"
  note m = measure_vars'_dest[OF a0 a3] 
  have "?sep_vars \<noteq> {}" unfolding Q_domain_var_def using a1 a2 by auto   
  then have "QStateM_map (snd (measure_vars' i q Q)) = QStateM_map Q"
    using a3 a4 m a5  unfolding Q_domain_var_def apply auto
    by (metis QStateM_wf_map local.a1 local.a2 measure_vars'_wf)
  moreover have "QStateM_vars (snd (measure_vars' i q Q)) = QStateM_vars Q"
    using a3 a4 m 
    by (metis QStateM_rel1 QStateM_vars.rep_eq calculation qstate_def)
  moreover have  "QStateM_vector (snd (measure_vars' i q Q)) = ?v"
    using a3 a4 m a5  measure_vars'_wf[OF m[THEN sym] a1 a2 a5 a4]
    by (metis QStateM_wf_vector QState_vector_idem snd_conv) 
  ultimately show ?thesis by auto
qed


lemma proj1_kk:
  "k < 2^(card sep_vars) \<Longrightarrow> (1\<^sub>k (2^(card sep_vars))) $$ (k,k) = 1"
    unfolding projection1_def by auto

lemma proj1_not_kk:
 "n < 2^(card v) \<Longrightarrow> m < 2^(card v) \<Longrightarrow> n\<noteq>k \<or> m\<noteq>k \<Longrightarrow>
    (1\<^sub>k (2^(card v))) $$ (n,m) = 0"
  unfolding projection1_def by auto 

lemma proj1_one:"n < 2^(card v) \<Longrightarrow> m < 2^(card v) \<Longrightarrow> 
  (1\<^sub>k (2^(card v))) $$ (n,m) = 1 \<longleftrightarrow> n = k \<and> m = k"
  unfolding projection1_def by auto

lemma one_mat_one:
  "n < 2^(card v) \<Longrightarrow>  1\<^sub>m (2^(card v)) $$ (n,n) = 1"
  by auto

lemma one_mat_zero:
  "i < 2^(card v) \<Longrightarrow> j < 2^(card v) \<Longrightarrow> i\<noteq>j \<Longrightarrow>  1\<^sub>m (2^(card v)) $$ (i,j) = 0"
  by auto


lemma mat_extend_1k_zero1: 
     assumes a0:"finite v1" and a1:"finite v2" and a2:"v1 \<inter> v2 = {}" and
       a3:"i < (2^(card v1)) * (2^(card v2))" and
       a4:"j < (2^(card v1)) * (2^(card v2))" and "k < (2^(card v1))" and "i\<noteq>j"
       shows "ptensor_mat v1 v2 ((1\<^sub>k (2^(card v1)))) (1\<^sub>m (2^(card v2))) $$ (i,j) = 0"
proof-
  let ?m1 = "1\<^sub>k (2^(card v1))" and ?m2 = "1\<^sub>m (2^(card v2))" and ?d = "list_dims (v1 \<union> v2)"
  let ?v = "partial_state2.vars1' v1 v2"
  interpret ps2:partial_state2 "list_dims (v1 \<union> v2)" v1 v2
    apply standard using a0 a1 a2 unfolding list_dims_def by auto
  have "ps2.dims0 = ?d" unfolding ps2.dims0_def list_dims_def ps2.vars0_def by auto
  moreover have "ps2.ptensor_mat ?m1 ?m2 $$ (i,j) = 
        ?m1 $$ (partial_state.encode1 ps2.dims0 ?v i, partial_state.encode1 ps2.dims0 ?v j) * 
        ?m2 $$ (partial_state.encode2 ps2.dims0 ?v i, partial_state.encode2 ps2.dims0 ?v j)"
    unfolding ps2.ptensor_mat_def 
    apply (rule  partial_state.tensor_mat_eval, auto simp add: ps2.dims0_def state_sig.d_def ps2.vars0_def) 
    using i_less_union[OF _ a2 a0 a1] a3 a4 by auto
  ultimately show ?thesis
    by (smt a3 a4 assms(7) length_replicate mult_not_zero one_mat_zero 
            partial_state.d1_def partial_state.dims1_def 
            partial_state.encode12_inv partial_state.encode1_lt 
            power_add prod_list_replicate proj1_not_kk ps2.d_def 
            ps2.dims0_def ps2.dims1_def ps2.dims2_def ps2.length_dims0 
           ps2.nths_vars1' ps2.nths_vars2'_comp ps2.ptensor_encode2_encode1)
qed

lemma mat_extend_1k_zero2: 
     assumes a0:"finite v1" and a1:"finite v2" and a2:"v1 \<inter> v2 = {}" and
       a3:"i < (2^(card v1)) * (2^(card v2))" and
       a4:"j < (2^(card v1)) * (2^(card v2))" and a5:"k < (2^(card v1))" and a6:"i=j" and
       a7:"partial_state.encode1 (list_dims (v1 \<union> v2)) (partial_state2.vars1' v1 v2) i\<noteq>k"
     shows "ptensor_mat v1 v2 ((1\<^sub>k (2^(card v1)))) (1\<^sub>m (2^(card v2))) $$ (i,j) = 0"
proof-
  let ?m1 = "1\<^sub>k (2^(card v1))" and ?m2 = "1\<^sub>m (2^(card v2))" and ?d = "list_dims (v1 \<union> v2)"
  let ?v = "partial_state2.vars1' v1 v2"
  interpret ps2:partial_state2 "list_dims (v1 \<union> v2)" v1 v2
    apply standard using a0 a1 a2 unfolding list_dims_def by auto
  have eq:"ps2.dims0 = ?d" unfolding ps2.dims0_def list_dims_def ps2.vars0_def by auto
  have "ps2.ptensor_mat ?m1 ?m2 $$ (i,j) = 
        ?m1 $$ (partial_state.encode1 ps2.dims0 ?v i, partial_state.encode1 ps2.dims0 ?v j) * 
        ?m2 $$ (partial_state.encode2 ps2.dims0 ?v i, partial_state.encode2 ps2.dims0 ?v j)"
    unfolding ps2.ptensor_mat_def 
    apply (rule  partial_state.tensor_mat_eval, auto simp add: ps2.dims0_def state_sig.d_def ps2.vars0_def) 
    using i_less_union[OF _ a2 a0 a1] a3 a4 by auto
  also have "?m1 $$ (partial_state.encode1 ps2.dims0 ?v i, partial_state.encode1 ps2.dims0 ?v j) = 0"         
    using a4 a6 a7 eq  partial_state.encode1_lt  prod_list_replicate length_replicate
          power_add ps2.length_dims0 ps2.nths_vars1'
    unfolding partial_state.d1_def projection1_def ps2.dims0_def 
              ps2.dims1_def partial_state.dims1_def
    by (smt index_mat(1) prod.simps(2) ps2.d_def )
  finally show ?thesis by auto
qed

lemma mat_extend_1k_zero: 
     assumes a0:"finite v1" and a1:"finite v2" and a2:"v1 \<inter> v2 = {}" and
       a3:"i < (2^(card v1)) * (2^(card v2))" and
       a4:"j < (2^(card v1)) * (2^(card v2))" and a5:"k < (2^(card v1))" and
       a7:"partial_state.encode1 (list_dims (v1 \<union> v2)) (partial_state2.vars1' v1 v2) i\<noteq>k"
     shows "ptensor_mat v1 v2 ((1\<^sub>k (2^(card v1)))) (1\<^sub>m (2^(card v2))) $$ (i,j) = 0"
  using mat_extend_1k_zero2[OF a0 a1 a2 a3 a4 a5 _ a7] mat_extend_1k_zero1[OF a0 a1 a2 a3 a4 a5]
  by auto

lemma mat_extend_1k_one:
assumes a0:"finite v1" and a1:"finite v2" and a2:"v1 \<inter> v2 = {}" and
       a3:"i < (2^(card v1)) * (2^(card v2))" and
       a4:"j < (2^(card v1)) * (2^(card v2))" and a5:"k < (2^(card v1))" and a6:"i=j" and
       a7:"partial_state.encode1 (list_dims (v1 \<union> v2)) (partial_state2.vars1' v1 v2) i = k"
     shows "ptensor_mat v1 v2 ((1\<^sub>k (2^(card v1)))) (1\<^sub>m (2^(card v2))) $$ (i,j) = 1"
proof-
  let ?m1 = "1\<^sub>k (2^(card v1))" and ?m2 = "1\<^sub>m (2^(card v2))" and ?d = "list_dims (v1 \<union> v2)"
  let ?v = "partial_state2.vars1' v1 v2"
  interpret ps2:partial_state2 "list_dims (v1 \<union> v2)" v1 v2
    apply standard using a0 a1 a2 unfolding list_dims_def by auto
  have eq:"ps2.dims0 = ?d" unfolding ps2.dims0_def list_dims_def ps2.vars0_def by auto
  have "ps2.ptensor_mat ?m1 ?m2 $$ (i,j) = 
        ?m1 $$ (partial_state.encode1 ps2.dims0 ?v i, partial_state.encode1 ps2.dims0 ?v j) * 
        ?m2 $$ (partial_state.encode2 ps2.dims0 ?v i, partial_state.encode2 ps2.dims0 ?v j)"
    unfolding ps2.ptensor_mat_def 
    apply (rule  partial_state.tensor_mat_eval, auto simp add: ps2.dims0_def state_sig.d_def ps2.vars0_def) 
    using i_less_union[OF _ a2 a0 a1] a3 a4 by auto
  also have "?m1 $$ (partial_state.encode1 ps2.dims0 ?v i, partial_state.encode1 ps2.dims0 ?v j) = 1"
    using a7 a6 a5
    by (simp add: eq proj1_one)
  also have  "?m2 $$ (partial_state.encode2 ps2.dims0 ?v i, partial_state.encode2 ps2.dims0 ?v j) = 1"
    by (metis a4 a6 eq length_replicate list_dims_def one_mat_one 
              partial_state.d1_def partial_state.dims1_def 
              partial_state.encode1_lt power_add prod_list_replicate 
              ps2.dims2_def ps2.length_dims0 ps2.nths_vars2'_comp 
               ps2.ptensor_encode2_encode1 state_sig.d_def)    
  finally show ?thesis by auto
qed


lemma row_i_not_k_zero:
  assumes a0:"finite v1" and a1:"finite v2" and a2:"v1 \<inter> v2 = {}" and
       a3:"i < (2^(card v1)) * (2^(card v2))" and
       a4:"j < (2^(card v1)) * (2^(card v2))" and a5:"k < (2^(card v1))" and
       a7:"partial_state.encode1 (list_dims (v1 \<union> v2)) (partial_state2.vars1' v1 v2) i \<noteq> k"  
     shows "row (ptensor_mat v1 v2 ((1\<^sub>k (2^(card v1)))) (1\<^sub>m (2^(card v2))))  i $ j = 0"
proof-
  have "i < dim_col (ptensor_mat v1 v2 ((1\<^sub>k (2^(card v1)))) (1\<^sub>m (2^(card v2))))"    
    using a3
    by (simp add: ptensor_mat_dim_col[OF a0 a1 a2, of "(1\<^sub>k (2^(card v1)))" "1\<^sub>m (2^(card v2))"])       
  moreover have " j < dim_col (ptensor_mat v1 v2 ((1\<^sub>k (2^(card v1)))) (1\<^sub>m (2^(card v2))))"
    using a4
    by (simp add: ptensor_mat_dim_col[OF a0 a1 a2, of "(1\<^sub>k (2^(card v1)))" "1\<^sub>m (2^(card v2))"])
  ultimately have "row (ptensor_mat v1 v2 ((1\<^sub>k (2^(card v1)))) (1\<^sub>m (2^(card v2))))  i $ j = 
        ptensor_mat v1 v2 ((1\<^sub>k (2^(card v1)))) (1\<^sub>m (2^(card v2)))$$(i,j)"          
    unfolding row_def
    apply (subst index_vec)
    by auto  
  then show ?thesis using mat_extend_1k_zero[OF a0 a1 a2 a3 a4 a5 a7]
    by metis    
qed


lemma row_i_k_one:
  assumes a0:"finite v1" and a1:"finite v2" and a2:"v1 \<inter> v2 = {}" and
       a3:"i < (2^(card v1)) * (2^(card v2))" and
       a4:"j < (2^(card v1)) * (2^(card v2))" and a5:"k < (2^(card v1))" and a6:"i=j" and
       a7:"partial_state.encode1 (list_dims (v1 \<union> v2)) (partial_state2.vars1' v1 v2) i = k"  
     shows "row (ptensor_mat v1 v2 ((1\<^sub>k (2^(card v1)))) (1\<^sub>m (2^(card v2))))  i $ j = 1"
proof-
  have "i < dim_col (ptensor_mat v1 v2 ((1\<^sub>k (2^(card v1)))) (1\<^sub>m (2^(card v2))))"    
    using a3
    by (simp add: ptensor_mat_dim_col[OF a0 a1 a2, of "(1\<^sub>k (2^(card v1)))" "1\<^sub>m (2^(card v2))"])       
  moreover have " j < dim_col (ptensor_mat v1 v2 ((1\<^sub>k (2^(card v1)))) (1\<^sub>m (2^(card v2))))"
    using a4
    by (simp add: ptensor_mat_dim_col[OF a0 a1 a2, of "(1\<^sub>k (2^(card v1)))" "1\<^sub>m (2^(card v2))"])
  ultimately have "row (ptensor_mat v1 v2 ((1\<^sub>k (2^(card v1)))) (1\<^sub>m (2^(card v2))))  i $ j = 
        ptensor_mat v1 v2 ((1\<^sub>k (2^(card v1)))) (1\<^sub>m (2^(card v2)))$$(i,j)"          
    unfolding row_def
    apply (subst index_vec)
    by auto
  then show ?thesis 
    using mat_extend_1k_one[OF a0 a1 a2 a3 a4 a5 a6 a7]
    by metis    
qed

lemma row_i_k_zero:
  assumes a0:"finite v1" and a1:"finite v2" and a2:"v1 \<inter> v2 = {}" and
       a3:"i < (2^(card v1)) * (2^(card v2))" and
       a4:"j < (2^(card v1)) * (2^(card v2))" and a5:"k < (2^(card v1))" and a6:"i\<noteq>j" and
       a7:"partial_state.encode1 (list_dims (v1 \<union> v2)) (partial_state2.vars1' v1 v2) i = k"  
     shows "row (ptensor_mat v1 v2 ((1\<^sub>k (2^(card v1)))) (1\<^sub>m (2^(card v2))))  i $ j = 0"
proof-
  have "i < dim_col (ptensor_mat v1 v2 ((1\<^sub>k (2^(card v1)))) (1\<^sub>m (2^(card v2))))"    
    using a3
    by (simp add: ptensor_mat_dim_col[OF a0 a1 a2, of "(1\<^sub>k (2^(card v1)))" "1\<^sub>m (2^(card v2))"])       
  moreover have " j < dim_col (ptensor_mat v1 v2 ((1\<^sub>k (2^(card v1)))) (1\<^sub>m (2^(card v2))))"
    using a4
    by (simp add: ptensor_mat_dim_col[OF a0 a1 a2, of "(1\<^sub>k (2^(card v1)))" "1\<^sub>m (2^(card v2))"])
  ultimately have "row (ptensor_mat v1 v2 ((1\<^sub>k (2^(card v1)))) (1\<^sub>m (2^(card v2))))  i $ j = 
        ptensor_mat v1 v2 ((1\<^sub>k (2^(card v1)))) (1\<^sub>m (2^(card v2)))$$(i,j)"          
    unfolding row_def
    apply (subst index_vec)
    by auto
  then show ?thesis using mat_extend_1k_zero1[OF a0 a1 a2 a3 a4 a5 a6]
    by metis    
qed

lemma row_ptensor_i_unit:
  assumes a0:"finite v1" and a1:"finite v2" and a2:"v1 \<inter> v2 = {}" and      
       a3:"i < (2^(card v1)) * (2^(card v2))" and
       a5:"k < (2^(card v1))" and 
       a7:"partial_state.encode1 (list_dims (v1 \<union> v2)) (partial_state2.vars1' v1 v2) i = k"
     shows "row (ptensor_mat v1 v2 ((1\<^sub>k (2^(card v1)))) (1\<^sub>m (2^(card v2)))) i = 
            unit_vec ((2^(card v1)) * (2^(card v2))) i"
  apply rule
  subgoal for j
    using row_i_k_zero[OF a0 a1 a2 a3 _ a5, of j] row_i_k_one[OF a0 a1 a2 a3 _ a5, of j]
    using a3 a7 by auto
  by (simp add: a0 local.a1 local.a2 ptensor_mat_dim_col)  

lemma row_ptensor_i_zero:
  assumes a0:"finite v1" and a1:"finite v2" and a2:"v1 \<inter> v2 = {}" and      
       a3:"i < (2^(card v1)) * (2^(card v2))" and
       a5:"k < (2^(card v1))" and 
       a7:"partial_state.encode1 (list_dims (v1 \<union> v2)) (partial_state2.vars1' v1 v2) i \<noteq> k"
     shows "row (ptensor_mat v1 v2 ((1\<^sub>k (2^(card v1)))) (1\<^sub>m (2^(card v2)))) i = 
            0\<^sub>v ((2^(card v1)) * (2^(card v2)))"
  apply rule
  subgoal for j
    using row_i_not_k_zero[OF a0 a1 a2 a3 _ a5, of j]
    using a3 a7 by auto
  by (simp add: a0 local.a1 local.a2 ptensor_mat_dim_col)  


lemma mat_product_vector_k:
  assumes a0:"finite v1" and a1:"finite v2" and a2:"v1 \<inter> v2 = {}" and      
       a3:"i < (2^(card v1)) * (2^(card v2))" and
       a5:"k < (2^(card v1))" and 
       a7:"partial_state.encode1 (list_dims (v1 \<union> v2)) (partial_state2.vars1' v1 v2) i = k" and
       a8:"dim_vec v = (2^(card v1)) * (2^(card v2))"
     shows "((ptensor_mat v1 v2 ((1\<^sub>k (2^(card v1)))) (1\<^sub>m (2^(card v2)))) *\<^sub>v v) $ i = v $ i"
proof-
  let ?m = "ptensor_mat v1 v2 ((1\<^sub>k (2^(card v1)))) (1\<^sub>m (2^(card v2)))"  
  have a01:"(2 ^ card v1 * 2 ^ card v2) = dim_vec (?m *\<^sub>v v)"
    by (simp add: a0 a3 local.a1 local.a2 ptensor_mat_dim_row)
  have "i < (2 ^ card v1 * 2 ^ card v2)"
    by (simp add: a0 a3 local.a1 local.a2 ptensor_mat_dim_row)
  then show ?thesis using a01
    apply auto
    using scalar_prod_left_unit a8  
    by (auto simp add: row_ptensor_i_unit[OF a0 a1 a2 a3 a5 a7] dest: carrier_vecI)
qed

lemma mat_product_vector_not_k:
  assumes a0:"finite v1" and a1:"finite v2" and a2:"v1 \<inter> v2 = {}" and      
       a3:"i < (2^(card v1)) * (2^(card v2))" and
       a5:"k < (2^(card v1))" and 
       a7:"partial_state.encode1 (list_dims (v1 \<union> v2)) (partial_state2.vars1' v1 v2) i \<noteq> k" and
       a8:"dim_vec v = (2^(card v1)) * (2^(card v2))"
     shows "((ptensor_mat v1 v2 ((1\<^sub>k (2^(card v1)))) (1\<^sub>m (2^(card v2)))) *\<^sub>v v) $ i = 0"
proof-
  let ?m = "ptensor_mat v1 v2 ((1\<^sub>k (2^(card v1)))) (1\<^sub>m (2^(card v2)))"  
  have a01:"(2 ^ card v1 * 2 ^ card v2) = dim_vec (?m *\<^sub>v v)"
    by (simp add: a0 a3 local.a1 local.a2 ptensor_mat_dim_row)
  have "i < (2 ^ card v1 * 2 ^ card v2)"
    by (simp add: a0 a3 local.a1 local.a2 ptensor_mat_dim_row)
  then show ?thesis using a01
    apply auto
    using scalar_prod_left_unit a8  
    by (auto simp add: row_ptensor_i_zero[OF a0 a1 a2 a3 a5 a7] dest: carrier_vecI)
qed

lemma v_scalar_mat_product_vector_not_k:
  assumes a0:"finite v1" and a1:"finite v2" and a2:"v1 \<inter> v2 = {}" and      
       a3:"i < (2^(card v1)) * (2^(card v2))" and
       a5:"k < (2^(card v1))" and 
       a7:"partial_state.encode1 (list_dims (v1 \<union> v2)) (partial_state2.vars1' v1 v2) i \<noteq> k" and
       a8:"dim_vec v = (2^(card v1)) * (2^(card v2))"
     shows "(a \<cdot>\<^sub>v ((ptensor_mat v1 v2 ((1\<^sub>k (2^(card v1)))) (1\<^sub>m (2^(card v2)))) *\<^sub>v v)) $ i = 0"
  using mat_product_vector_not_k[OF a0 a1 a2 a3 a5 a7 a8]
  by (simp add: a0 a3 local.a1 local.a2 ptensor_mat_dim_row) 

lemma v_scalar_mat_product_vector_k:
  assumes a0:"finite v1" and a1:"finite v2" and a2:"v1 \<inter> v2 = {}" and      
       a3:"i < (2^(card v1)) * (2^(card v2))" and
       a5:"k < (2^(card v1))" and 
       a7:"partial_state.encode1 (list_dims (v1 \<union> v2)) (partial_state2.vars1' v1 v2) i = k" and
       a8:"dim_vec v = (2^(card v1)) * (2^(card v2))"
     shows "(a \<cdot>\<^sub>v ((ptensor_mat v1 v2 ((1\<^sub>k (2^(card v1)))) (1\<^sub>m (2^(card v2)))) *\<^sub>v v)) $ i = a * v $ i"
  using mat_product_vector_k[OF a0 a1 a2 a3 a5 a7 a8]
  by (simp add: a0 a3 local.a1 local.a2 ptensor_mat_dim_row) 

lemma ptensor_unit_v_v_aij_not_k_zero:
  assumes a0:"finite v1" and a1:"finite v2" and a2:"v1 \<inter> v2 = {}" and      
       a3:"i < (2^(card v1)) * (2^(card v2))" and
       a5:"k < (2^(card v1))" and 
       a7:"partial_state.encode1 (list_dims (v1 \<union> v2)) (partial_state2.vars1' v1 v2) i \<noteq> k" and
       a8:"dim_vec v = (2^(card v1)) * (2^(card v2))" 
     shows "ptensor_vec v1 v2 (unit_vec (2 ^ card v1) k) (vector_aij v1 v2 v k) $ i = 0"
proof-
  let ?v1 = "unit_vec (2 ^ card v1) k" and ?v2 = "vector_aij v1 v2 v k"
  interpret ps2:partial_state2 "replicate ((2^(card v1)) * (2^(card v2))) 2" "v1" "v2"
    apply standard using a2 a1 a0 by auto
  have "ptensor_vec v1 v2 (unit_vec (2 ^ card v1) k) (vector_aij v1 v2 v k) $ i = 
        (?v1 $ (partial_state.encode1 (list_dims (v1 \<union> v2)) (partial_state2.vars1' v1 v2) i)) * 
        (?v2 $ (partial_state.encode2  (list_dims (v1 \<union> v2)) (partial_state2.vars1' v1 v2) i))"
    unfolding  ps2.ptensor_vec_def  ps2.dims0_def
    by (simp add: a3 i_less_union list_dims_def local.a2 partial_state.tensor_vec_eval  
                  ps2.finite_v1 ps2.finite_v2 ps2.vars0_def state_sig.d_def)
  thus ?thesis
    by (metis a3 a5 a7 i_less_union index_unit_vec(1) list_dims_def 
         local.a2 mult_not_zero partial_state.d1_def partial_state.dims1_def 
         partial_state.encode1_lt prod_list_replicate ps2.dims0_def ps2.dims1_def 
         ps2.finite_v1 ps2.finite_v2 ps2.nths_vars1' ps2.vars0_def state_sig.d_def)  
qed

lemma ptensor_unit_v_v_aij_k_v_i:
  assumes a0:"finite v1" and a1:"finite v2" and a2:"v1 \<inter> v2 = {}" and      
       a3:"i < (2^(card v1)) * (2^(card v2))" and
       a5:"k < (2^(card v1))" and 
       a7:"partial_state.encode1 (list_dims (v1 \<union> v2)) (partial_state2.vars1' v1 v2) i = k" and
       a8:"dim_vec v = (2^(card v1)) * (2^(card v2))" 
     shows "ptensor_vec v1 v2 (unit_vec (2 ^ card v1) k) (vector_aij v1 v2 v k) $ i = v $ i"
proof-
  let ?v1 = "unit_vec (2 ^ card v1) k" and ?v2 = "vector_aij v1 v2 v k"
  interpret ps2:partial_state2 "replicate ((2^(card v1)) * (2^(card v2))) 2" "v1" "v2"
    apply standard using a2 a1 a0 by auto
  have "ptensor_vec v1 v2 (unit_vec (2 ^ card v1) k) (vector_aij v1 v2 v k) $ i = 
        (?v1 $ (partial_state.encode1 (list_dims (v1 \<union> v2)) (partial_state2.vars1' v1 v2) i)) * 
        (?v2 $ (partial_state.encode2  (list_dims (v1 \<union> v2)) (partial_state2.vars1' v1 v2) i))"
    unfolding  ps2.ptensor_vec_def  ps2.dims0_def
    by (simp add: a3 i_less_union list_dims_def local.a2 partial_state.tensor_vec_eval  
                  ps2.finite_v1 ps2.finite_v2 ps2.vars0_def state_sig.d_def)
  moreover have "partial_state.encode2 (list_dims (v1 \<union> v2)) ps2.vars1' i < (2 ^ card v2)"
    by (metis a3 i_less_union list_dims_def partial_state.d1_def partial_state.dims1_def 
              partial_state.encode1_lt prod_list_replicate ps2.dims0_def 
              ps2.dims2_def ps2.disjoint ps2.finite_v1 ps2.finite_v2 ps2.nths_vars2'_comp 
              ps2.ptensor_encode2_encode1 ps2.vars0_def state_sig.d_def)    
  then have "(?v2 $ (partial_state.encode2 (list_dims (v1 \<union> v2)) (partial_state2.vars1' v1 v2) i)) = 
            v $ ps2.pencode12 (k, partial_state.encode2 (list_dims (v1 \<union> v2)) ps2.vars1' i) " 
    unfolding vector_aij_def aijv_def using a7 a3  by auto        
  then have "(?v2 $ (partial_state.encode2 (list_dims (v1 \<union> v2)) (partial_state2.vars1' v1 v2) i)) = v $ i"  
    unfolding vector_aij_def aijv_def using a7 a3 apply auto
    by (simp add:  i_less_union list_dims_def partial_state.encode12_inv 
                  ps2.dims0_def ps2.disjoint ps2.finite_v1 ps2.finite_v2 
                  ps2.pencode12_def ps2.vars0_def state_sig.d_def)    
  moreover have "(?v1 $ (partial_state.encode1 (list_dims (v1 \<union> v2)) (partial_state2.vars1' v1 v2) i)) = 1"    
    by (simp add: a7 a5)  
  ultimately show ?thesis by auto  
qed

lemma mat_eq_ptensor_product_vector_i:
  assumes a0:"finite v1" and a1:"finite v2" and a2:"v1 \<inter> v2 = {}" and      
       a3:"(i::nat) < (2^(card v1)) * (2^(card v2))" and
       a5:"k < (2^(card v1))" and
       a8:"dim_vec v = (2^(card v1)) * (2^(card v2))" 
     shows "(ptensor_mat v1 v2 (1\<^sub>k (2 ^ card v1)) (1\<^sub>m (2 ^ card v2)) *\<^sub>v v) $ i =
            ptensor_vec v1 v2 (unit_vec (2 ^ card v1) k) (vector_aij v1 v2 v k) $ i"
  using ptensor_unit_v_v_aij_k_v_i[OF a0 a1 a2 a3 a5 _ a8] 
        ptensor_unit_v_v_aij_not_k_zero[OF a0 a1 a2 a3 a5 _ a8] 
        mat_product_vector_not_k[OF a0 a1 a2 a3 a5 _ a8]  
        mat_product_vector_k[OF a0 a1 a2 a3 a5 _ a8] 
  by fastforce


lemma mat_eq_ptensor_product_vector:
  assumes a0:"finite v1" and a1:"finite v2" and a2:"v1 \<inter> v2 = {}" and             
       a5:"k < (2^(card v1))" and
       a8:"dim_vec v = (2^(card v1)) * (2^(card v2))"
     shows "(ptensor_mat v1 v2 ((1\<^sub>k (2^(card v1)))) (1\<^sub>m (2^(card v2)))) *\<^sub>v v = 
            ptensor_vec v1 v2 (unit_vec (2^(card v1)) k) (vector_aij v1 v2 v k)"
proof-
  let ?v = "(ptensor_mat v1 v2 ((1\<^sub>k (2^(card v1)))) (1\<^sub>m (2^(card v2)))) *\<^sub>v v"
  let ?w = "ptensor_vec v1 v2 (unit_vec (2^(card v1)) k) (vector_aij v1 v2 v k)"
  have "dim_vec ?v = dim_vec ?w"
  proof- 
    have "dim_vec ?v = (2^(card v1)) * (2^(card v2))"
      by (simp add: a0 local.a1 local.a2 ptensor_mat_dim_row)
    moreover have "dim_vec ?w = (2^(card v1)) * (2^(card v2))"   
      by (metis a0  length_replicate local.a1 local.a2 nth_replicate
                partial_state2.intro partial_state2.ptensor_mat_dim_col 
               partial_state2.ptensor_vec_dim ptensor_mat_dim_col)
    ultimately show ?thesis by auto
  qed
  moreover have "\<And>i. i < dim_vec ?w \<Longrightarrow> ?v $ i = ?w $ i"
    using mat_eq_ptensor_product_vector_i[OF a0 a1 a2 _ a5 a8]
    by (metis a0 calculation dim_mult_mat_vec local.a1 local.a2 ptensor_mat_dim_row)
  ultimately show ?thesis by auto
qed


lemma v_scalar_mat_product_eq_ptensor:
  assumes a0:"finite v1" and a1:"finite v2" and a2:"v1 \<inter> v2 = {}" and             
       a5:"k < (2^(card v1))" and
       a8:"dim_vec v = (2^(card v1)) * (2^(card v2))"
     shows "a \<cdot>\<^sub>v ((ptensor_mat v1 v2 ((1\<^sub>k (2^(card v1)))) (1\<^sub>m (2^(card v2)))) *\<^sub>v v) = 
            a \<cdot>\<^sub>v ptensor_vec v1 v2 (unit_vec (2^(card v1)) k) (vector_aij v1 v2 v k)"
  using mat_eq_ptensor_product_vector[OF a0 a1 a2 a5 a8] by auto
  



lemma eq_sum_v_p_encode:
assumes a0:"finite v1" and a1:"finite v2" and a2:"v1 \<inter> v2 = {}" and       
       a3:"dim_vec (v::complex vec) = (2^(card v1)) * (2^(card v2))" 
     shows "(\<Sum>i = 0..< (dim_vec v). (cmod (v $ i))\<^sup>2) = 
           (\<Sum>i = 0 ..<2^(card v1). \<Sum>j = 0 ..<2^(card v2). (cmod (aijv v1 v2 v i j))\<^sup>2)"
proof-
  interpret ps2:
    partial_state2 "replicate ((2^(card v1)) * (2^(card v2))) 2" "v1" "v2"
    apply standard using a2 a1 a0 by auto
  let ?i = "(\<lambda>i. partial_state.encode1 ps2.dims0 (partial_state2.vars1' v1 v2) i)"
  let ?j = "(\<lambda>i. partial_state.encode2 ps2.dims0 (partial_state2.vars1' v1 v2) i)"
  have "\<And>i. i<(dim_vec v) \<Longrightarrow>  
              v $ i = aijv v1 v2 v (?i i) (?j i)"
    unfolding aijv_def
    by (simp add: a3 card_Un_disjoint partial_state.encode12_inv power_add ps2.dims0_def 
          ps2.disjoint ps2.finite_v1 
        ps2.finite_v2 ps2.pencode12_def ps2.vars0_def state_sig.d_def)
  then have eq:"\<And>i. i<(dim_vec v) \<Longrightarrow>  
              (cmod (v $ i))\<^sup>2 = (cmod (aijv v1 v2 v (?i i) (?j i)))\<^sup>2" by auto
  have "(\<Sum>i = 0..< (dim_vec v). (cmod (v $ i))\<^sup>2) = 
        (\<Sum>i = 0..< (dim_vec v). (cmod (v $ partial_state2.pencode12 v1 v2 (?i i,?j i)))\<^sup>2)"
    using partial_state.encode12_inv ps2.dims_product 
         ps2.partial_state2_axioms a3 partial_state2.pencode12_def 
    unfolding  ps2.d0_def ps2.d1_def ps2.d2_def ps2.dims1_def ps2.dims2_def  state_sig.d_def by auto
  also have "\<dots> = 
             (\<Sum>i = 0 ..<2^(card v1). \<Sum>j = 0 ..<2^(card v2). (cmod (v $ partial_state2.pencode12 v1 v2 (i,j)))\<^sup>2)"    
  proof-
    have "dim_vec v = state_sig.d ps2.dims0" and
         "partial_state.d2 ps2.dims0 ps2.vars1' = 2 ^ card v2" and
         "partial_state.d1 ps2.dims0 ps2.vars1' = 2 ^ card v1"
      using a3 unfolding state_sig.d_def
      using ps2.d0_def ps2.d1_def ps2.dims0_def ps2.dims1_def 
            ps2.dims2_def ps2.dims_product       
      using partial_state.d2_def partial_state.dims2_def ps2.d2_def ps2.nths_vars2'
      using partial_state.d1_def partial_state.dims1_def ps2.nths_vars1' by auto
    thus ?thesis  
      using partial_state.sum_encode[THEN sym, where dims1 = ps2.dims0 and vars1 = ps2.vars1']
      by fastforce
  qed       
  finally show ?thesis unfolding aijv_def by auto
qed
  
              
lemma eq_v_aijv_i_j:  
    assumes a0:"finite v1" and a1:"finite v2" and a2:"v1 \<inter> v2 = {}" and
       a5:"k < (2^(card v1))" and
       a8:"dim_vec v = (2^(card v1)) * (2^(card v2))"
     shows "(vec_norm v)^2 = 
            (\<Sum>i = 0 ..<2^(card v1). \<Sum>j = 0 ..<2^(card v2). (norm (aijv v1 v2 v i j))^2)"
proof-
  have " v \<bullet>c v = (\<Sum>i = 0 ..<dim_vec v. (v$i) * (conjugate (v$i)))"
   unfolding scalar_prod_def by auto
  also have "\<dots> =  (\<Sum>i = 0 ..<dim_vec v. (norm (v$i))\<^sup>2)"
    using complex_norm_square conjugate_complex_def
    by auto
  also have " \<dots> = (\<Sum>i = 0 ..<2^(card v1). \<Sum>j = 0 ..<2^(card v2). (norm (aijv v1 v2 v i j))^2)"
    using eq_sum_v_p_encode[OF a0 a1 a2 a8] by auto
  finally have "v \<bullet>c v = (\<Sum>i = 0 ..<2^(card v1). \<Sum>j = 0 ..<2^(card v2). (norm (aijv v1 v2 v i j))^2)"
    by auto
  moreover have "(vec_norm v)^2 = v \<bullet>c v"
    using power2_csqrt vec_norm_def by presburger
  ultimately show ?thesis
    by auto
qed

lemma 
  assumes a0:"l \<noteq> k" and a1:"\<forall>i j. j < n \<and> i < m \<and> i \<noteq> k \<longrightarrow> f i j = 0" 
  and a2:"l<m" 
shows "(\<Sum>j = 0 ..<n. f l j) = 0"
  using  a2 a0 a1
  by simp

lemma sum_f_i_lt_k_0:
  assumes a0:"(m::nat) \<le> k" and a1:"\<forall>i j. j < n \<and> i < m \<and> i \<noteq> k \<longrightarrow> f i j = 0" and a2:"0<m"
  shows "(\<Sum>i = 0 ..<m. \<Sum>j = 0 ..<n. f i j) = 0"
  using a2 a1 a0
proof(induct m rule:nat_induct_non_zero)
  case 1
  then show ?case by auto
next
  case (Suc m)
  then have "(\<Sum>i = 0..<Suc m. sum (f i) {0..<n}) = 
             (\<Sum>i = 0..< m. sum (f i) {0..<n}) + sum (f m) {0..<n} "
    by auto
  moreover have "sum (f m) {0..<n} = 0"
    using Suc.prems(1) Suc.prems(2) by auto
  moreover have "(\<Sum>i = 0..< m. sum (f i) {0..<n}) = 0"
    by (metis Suc.hyps(2) Suc.prems(1) Suc.prems(2) Suc_eq_plus1 add_leD1 less_SucI)
  ultimately show ?case by auto
qed

lemma sum_eq_sum_k_j:
  assumes a0:"k < (m::nat)" and a1:"\<forall>i j. j < n \<and> i < m \<and> i \<noteq> k \<longrightarrow> f i j = 0" and a2:"0<m"
  shows "(\<Sum>i = 0 ..<m. \<Sum>j = 0 ..<n. f i j) = (\<Sum>j = 0 ..<n. f k j)"

  using a2 a0 a1 
proof(induct m rule:nat_induct_non_zero)
  case 1
  then show ?case by auto
next
  case (Suc m)
  then have sum_eq:"(\<Sum>i = 0..<Suc m. sum (f i) {0..<n}) = 
             (\<Sum>i = 0..< m. sum (f i) {0..<n}) + sum (f m) {0..<n} "
    by auto  
  { assume a00:"k=m"        
    then have "(\<Sum>i = 0..< m. sum (f i) {0..<n}) = 0"
      using sum_f_i_lt_k_0[of m k n f]  a00 by (simp add: Suc.prems(2))
    then have ?case using sum_eq a00 by auto
  }
  moreover { 
    assume a00:"k\<noteq>m"    
    then have ?case using sum_eq a00
      using Suc.hyps(2) Suc.prems(1) Suc.prems(2) by auto 
  }
  ultimately show ?case by auto
qed

lemma  vec_norm_ptensor_eq_sum_norm_k:
  assumes a0:"finite v1" and a1:"finite v2" and a2:"v1 \<inter> v2 = {}" and
       a5:"k < (2^(card v1))" and
       a8:"dim_vec v = (2^(card v1)) * (2^(card v2))"
  shows "(vec_norm (((ptensor_mat v1 v2 ((1\<^sub>k (2^(card v1)))) (1\<^sub>m (2^(card v2)))) *\<^sub>v v)))^2  = 
         (\<Sum>j = 0..<2^(card v2). norm (aijv v1 v2 v k j )^2)"
proof-
  interpret ps2:
    partial_state2 "replicate ((2^(card v1)) * (2^(card v2))) 2" "v1" "v2"
    apply standard using a2 a1 a0 by auto
  let ?i = "(\<lambda>i. partial_state.encode1 ps2.dims0 (partial_state2.vars1' v1 v2) i)"
  let ?j = "(\<lambda>i. partial_state.encode2 ps2.dims0 (partial_state2.vars1' v1 v2) i)"
  let ?v = "(((ptensor_mat v1 v2 ((1\<^sub>k (2^(card v1)))) (1\<^sub>m (2^(card v2)))) *\<^sub>v v))"   
  have dim_v:"dim_vec v = dim_vec ?v"
    by (simp add: a8 ps2.d1_def ps2.d2_def ps2.dims1_def ps2.dims2_def ps2.dims_product)
  then have "(vec_norm ?v)^2 = 
            (\<Sum>i = 0 ..<2^(card v1). \<Sum>j = 0 ..<2^(card v2). (norm (aijv v1 v2 ?v i j))^2)"
    using eq_v_aijv_i_j[OF a0 a1 a2 a5 a8[simplified dim_v]] by fastforce
  also have "(\<Sum>i = 0 ..<2^(card v1). \<Sum>j = 0 ..<2^(card v2). (norm (aijv v1 v2 ?v i j))^2) = 
             (\<Sum>j = 0..<2^(card v2). norm (aijv v1 v2 v k j )^2)"
  proof-
    have "\<And>i. i<(dim_vec ?v) \<Longrightarrow>  
                 ?v $ i = aijv v1 v2 ?v (?i i) (?j i)"
      unfolding aijv_def
      by (simp add: partial_state.encode12_inv ps2.d0_def ps2.pencode12_def state_sig.d_def)
    let ?f = "\<lambda>i j. (cmod (aijv v1 v2 ?v i j))\<^sup>2"
    have "(\<Sum>i = 0..<2 ^ card v1.
             \<Sum>j = 0..<2 ^ card v2.
                (cmod (aijv v1 v2 ?v i j))\<^sup>2) =
         (\<Sum>j = 0..<2 ^ card v2. (cmod (aijv v1 v2 ?v k j))\<^sup>2)"
      apply (rule sum_eq_sum_k_j[of k "2 ^ card v1" "2 ^ card v2" ?f])
      using a5 apply fastforce
      unfolding aijv_def 
      apply auto apply (rule  mat_product_vector_not_k[OF a0 a1 a2 _ _ _  a8])
        apply (metis a8 dim_mult_mat_vec dim_v partial_state.d1_def 
                     partial_state.d2_def partial_state.dims1_def 
                     partial_state.dims2_def partial_state.encode12_lt 
                     partial_state2.ptensor_mat_dim_row prod_list_replicate 
                     ps2.d0_def ps2.dims1_def ps2.dims2_def 
                     ps2.nths_vars1' ps2.nths_vars2' 
                     ps2.partial_state2_axioms ps2.pencode12_def state_sig.d_def)
      using a5 apply blast unfolding ps2.pencode12_def
      by (metis list_dims_def partial_state.d1_def partial_state.d2_def 
                partial_state.dims1_def partial_state.dims2_def 
                partial_state.encode12_inv1 prod_list_replicate ps2.dims0_def 
                ps2.dims1_def ps2.dims2_def ps2.nths_vars1' ps2.nths_vars2' ps2.vars0_def)          
    also have "(\<Sum>j = 0..<2 ^ card v2. (cmod (aijv v1 v2 ?v k j))\<^sup>2) = 
               (\<Sum>j = 0..<2 ^ card v2. (cmod (aijv v1 v2  v k j))\<^sup>2)"    
    proof-
      have "\<And>j. j < 2^card v2 \<Longrightarrow> (cmod (aijv v1 v2 ?v k j))\<^sup>2 = (cmod (aijv v1 v2 v k j))\<^sup>2"      
        unfolding aijv_def using mat_product_vector_k[OF a0 a1 a2 _ _ _ a8]      
        by (metis a5 list_dims_def partial_state.d1_def partial_state.d2_def
                partial_state.dims1_def partial_state.dims2_def 
                partial_state.encode12_inv1 partial_state.encode12_lt 
                prod_list_replicate ps2.d0_def ps2.d1_def ps2.d2_def ps2.dims0_def 
                ps2.dims1_def ps2.dims2_def ps2.dims_product ps2.nths_vars1' 
                ps2.nths_vars2' ps2.pencode12_def ps2.vars0_def state_sig.d_def)                       
      then show ?thesis by simp
   qed         
   finally show ?thesis by auto
  qed
  finally show ?thesis by auto
qed

lemma eq_norm: assumes a0:"finite v1" and a1:"finite v2" and a2:"v1 \<inter> v2 = {}" and             
       a5:"k < (2^(card v1))" and
       a8:"dim_vec v = (2^(card v1)) * (2^(card v2))"
     shows "Re ((vec_norm (((ptensor_mat v1 v2 ((1\<^sub>k (2^(card v1)))) (1\<^sub>m (2^(card v2)))) *\<^sub>v v)))^2 
                div (vec_norm v)^2) =
            (\<Sum>j = 0..<2^(card v2). norm (aijv v1 v2 v k j )^2) / 
             (\<Sum>i = 0 ..<2^(card v1). \<Sum>j = 0 ..<2^(card v2). norm (aijv v1 v2 v i j)^2 )"
proof-
  have "(vec_norm (((ptensor_mat v1 v2 ((1\<^sub>k (2^(card v1)))) (1\<^sub>m (2^(card v2)))) *\<^sub>v v)))^2 =
        (\<Sum>j = 0..<2^(card v2). norm (aijv v1 v2 v k j )^2)"
    using vec_norm_ptensor_eq_sum_norm_k[OF a0 a1 a2 a5 a8] by auto
  moreover have "(vec_norm v)^2 = 
                 (\<Sum>i = 0 ..<2^(card v1). 
                    \<Sum>j = 0 ..<2^(card v2). norm (aijv v1 v2 v i j)^2 )"
    using eq_v_aijv_i_j[OF a0 a1 a2 a5 a8] by auto
  ultimately show ?thesis by auto
qed

lemma norm_v2_empty: assumes a0:"finite v1" and a1:"v2 = {}" and             
       a5:"k < (2^(card v1))" and
       a8:"dim_vec v = (2^(card v1)) * (2^(card v2))"
     shows "Re ((vec_norm (((ptensor_mat v1 v2 ((1\<^sub>k (2^(card v1)))) (1\<^sub>m (2^(card v2)))) *\<^sub>v v)))^2 
                div (vec_norm v)^2) =
            (norm (v$k)^2) / (\<Sum>i = 0 ..<2^(card v1). norm (v$i)^2 )"
proof-
  have "Re ((vec_norm (((ptensor_mat v1 v2 ((1\<^sub>k (2^(card v1)))) (1\<^sub>m (2^(card v2)))) *\<^sub>v v)))^2 
                div (vec_norm v)^2) = (\<Sum>j = 0..<2^(card v2). norm (aijv v1 v2 v k j )^2) / 
             (\<Sum>i = 0 ..<2^(card v1). \<Sum>j = 0 ..<2^(card v2). norm (aijv v1 v2 v i j)^2 )"
    using eq_norm[OF a0 _ _ a5 a8] using a1 by auto
  moreover have "\<And>i. i <(2^(card v1)) \<Longrightarrow> aijv v1 v2 v k 0 = v $ k" using a1 unfolding aijv_def
    using eq_vec_aijv_v2_empty
    using a0 a5 a8 aijv_def by auto
  moreover have "(\<Sum>j = 0..<2^(card v2). norm (aijv v1 v2 v k j )^2) =  norm (v$k)^2"
    using a1 calculation(2)
    by fastforce  
  moreover have "(\<Sum>i = 0 ..<2^(card v1). \<Sum>j = 0 ..<2^(card v2). norm (aijv v1 v2 v i j)^2 )= 
                 (\<Sum>i = 0 ..<2^(card v1). norm (v$i)^2)"
    using a1 
    by (metis (no_types) a0 a8 card.empty eq_sum_v_p_encode 
            finite.emptyI inf_bot_right mult.right_neutral power.simps(1))    
  ultimately show ?thesis by auto
qed



lemma  sqrt_norm_eq:
   assumes a0:"finite v1" and a1:"v2 = {}" and             
       a5:"k < (2^(card v1))" and
       a8:"dim_vec v = (2^(card v1)) * (2^(card v2))" and 
       a9:"\<delta>k = (norm (v$k))^2 / (\<Sum>i = 0 ..<2^(card v1). (norm (v$i))^2 )"
     shows "sqrt \<delta>k = norm (v$k)  / sqrt (\<Sum>i = 0 ..<2^(card v1). norm (v$i)^2 )"
proof-
  have "\<And>a b. sqrt (a/b) = sqrt a / sqrt b"
    using real_sqrt_divide by auto
  moreover have "\<And>a. norm a \<ge> 0" by auto
  then have "\<And>a. a\<ge>0 \<Longrightarrow> sqrt (a\<^sup>2) = a" by auto
  ultimately show ?thesis using a9 by auto
qed
  
lemma  vector_aij_v2_empty:
  assumes a0:"finite v1" and a1:"v2 = {}" and             
       a5:"k < (2^(card v1))" and
       a8:"dim_vec v = (2^(card v1)) * (2^(card v2))" 
     shows "vector_aij v1 v2 v k $ 0 = v$k"
 unfolding vector_aij_def 
 using eq_vec_aijv_v2_empty[OF _ a8 a0 a1 _] a5 a8 a1  by auto

(*
lemma  assumes a0:"finite v1" and a1:"v2 = {}" and             
       a5:"k < (2^(card v1))" and
       a8:"dim_vec v = (2^(card v1)) * (2^(card v2))" and 
       a9:"\<delta>k = Re ((norm (v$k)^2) / (\<Sum>i = 0 ..<2^(card v1). norm (v$i)^2 ))" and 
       a10:"(v'::complex vec) =(((1 / sqrt \<delta>k)\<cdot>\<^sub>v(vector_aij v1 v2 v k))) " 
     shows "v' = ((\<Sum>i = 0 ..<2^(card v1). norm (v$i)^2))" *)

lemma measure_vars_QStateM_map:
  assumes           
     a0:"(\<forall>e\<in>q. QStateM_map Q e \<noteq> {})" and a1:"q \<noteq> {}" and a2:"p>0" and
     a3:"(p,Q') = measure_vars i q Q" 
   shows "QStateM_map Q' = QStateM_map Q"
     using measure_vars_dest_QStateM[OF a0 a1 a2]
     by (metis a3 fst_conv measure_vars_dest snd_conv)

lemma measure_vars'_QStateM_map:
  assumes           
     a0:"(\<forall>e\<in>q. QStateM_map Q e \<noteq> {})" and a1:"q \<noteq> {}" and a2:"p>0" and
     a3:"(p,Q') = measure_vars' i q Q" and a4:"i<2 ^ card (\<Union> (QStateM_map Q ` q))"
   shows "QStateM_map Q' = QStateM_map Q"
  apply (cases "QStateM_vars Q = \<Union>((QStateM_map Q) ` q)")
  using measure_vars'_dest_QStateM[OF _ a0 a1 a2 a4]
  apply (metis a3 fst_conv measure_vars'_dest snd_conv)
  using measure_vars_dest_QStateM[OF a0 a1 a2]
  by (metis (full_types) a0 a3 local.a1 local.a2 measure_vars'_neq measure_vars_QStateM_map)
  
lemma  measure_vars_eq_length_vector:
  assumes
   a0:"(\<delta>k, Q_State.QStateM(qm, QState (vars_dom, qnprod))) = measure_vars i q Q" and
   a1:"\<forall>e \<in> q. QStateM_map Q e \<noteq> {}" and a2:"q \<noteq> {}" and a4:"\<delta>k > 0" and
   a3:"QStateM_vector Q \<noteq> 0\<^sub>v (2^(card (QStateM_vars Q)))"
  shows "length (QStateM_list Q) = length qnprod"
proof-  
  have wf:"QState_wf (vars_dom,qnprod)" and wfm:"QStateM_wf (qm, QState(vars_dom,qnprod))"
    using measure_vars_wf[OF a0 a1 a2 a4] by auto
  then have "QStateM_map (Q_State.QStateM(qm, QState (vars_dom, qnprod))) = QStateM_map Q"
    using measure_vars_QStateM_map[OF a1 a2 a4 a0]
    by auto
  then have "QStateM_vars Q = QStateM_vars (Q_State.QStateM(qm, QState (vars_dom, qnprod)))"
    by (metis QStateM_wf eq_QStateM_vars fst_conv)
  thus ?thesis 
    using QStateM_wf_vars QState_rel1' QState_var_idem local.wf wfm unfolding QState_wf_def
    by (metis QStateM_list_dim dim_vec_of_list fst_conv snd_conv)
qed

lemma  measure_vars'_eq_length_vector:
  assumes
   a0:"(\<delta>k, Q_State.QStateM(qm, QState (vars_dom, qnprod))) = measure_vars' i q Q" and
   a1:"\<forall>e \<in> q. QStateM_map Q e \<noteq> {}" and a2:"q \<noteq> {}" and a4:"\<delta>k > 0" and
   a3:"QStateM_vector Q \<noteq> 0\<^sub>v (2^(card (QStateM_vars Q)))" and a5:"i<2 ^ card (\<Union> (QStateM_map Q ` q))"
  shows "length (QStateM_list Q) = length qnprod"
proof-  
  have wf:"QState_wf (vars_dom,qnprod)" and wfm:"QStateM_wf (qm, QState(vars_dom,qnprod))"
    using measure_vars'_wf[OF a0 a1 a2  a5 a4] by auto
  then have "QStateM_map (Q_State.QStateM(qm, QState (vars_dom, qnprod))) = QStateM_map Q"
    using measure_vars'_QStateM_map[OF a1 a2 a4 a0 a5]
    by auto
  then have "QStateM_vars Q = QStateM_vars (Q_State.QStateM(qm, QState (vars_dom, qnprod)))"
    by (metis QStateM_wf eq_QStateM_vars fst_conv)
  thus ?thesis 
    using QStateM_wf_vars QState_rel1' QState_var_idem local.wf wfm unfolding QState_wf_def
    by (metis QStateM_list_dim dim_vec_of_list fst_conv snd_conv)
qed

lemma a_div_b_gt_0_b_not_zero:"(a::('a::linordered_field)) div b = \<sigma> \<Longrightarrow>  0 < \<sigma> \<Longrightarrow> b\<noteq>0"  
  by force

lemma a_div_b_gt_0_a_gt_zero:
      assumes a0:"(a::('a::linordered_field)) div b = \<sigma>" and a1:"b\<ge>0" and a2:"\<sigma> > 0" 
      shows "a > 0"
  apply (cases "a=0")
  using a0 a1 a2 divide_neg_pos  
  by (auto simp add:zero_less_divide_iff)




definition pr ::"'s expr_q  \<Rightarrow> ('s \<Rightarrow> complex list) \<Rightarrow> nat \<Rightarrow>  's state \<Rightarrow> real" 
  where "pr q v i s \<equiv> let st = get_stack s ; qv = fst (get_qstate s); 
                         vars = Q_domain qv; d1 = Q_domain_set q qv st; d2 = vars - d1 in 
                     (\<Sum>j = 0..<2^(card d2). norm (aij s q v i j )^2) / 
                        (\<Sum>i = 0 ..<2^(card d1). 
                            \<Sum>j = 0 ..<2^(card d2). norm (aij s q v i j)^2 )"

definition vector_i::"'s state \<Rightarrow> 's expr_q  \<Rightarrow>  ('s, complex list) expr \<Rightarrow> nat \<Rightarrow> ('s, complex list) expr"
  where "vector_i s q v i \<equiv> 
     let st = get_stack s ; qv = fst (get_qstate s); 
               vars = Q_domain qv; d1 = Q_domain_set q qv st; d2 = vars - d1;
        elem_ij  = (\<lambda>j. (aij s q v i j) / sqrt (pr q v i s)) in
     (\<lambda>st. map (\<lambda>e. elem_ij e) [0..<2^card d2])"

definition
  unit_vecl :: "'s state \<Rightarrow> 's expr_q  \<Rightarrow> nat \<Rightarrow> ('s, complex list) expr"
  where "unit_vecl s q i \<equiv>
    let st = get_stack s ; qv = fst (get_qstate s); 
        d1 = Q_domain_set q qv st in
      (\<lambda>s. list_of_vec (unit_vec (2^card d1) i))"




(*  " v \<in> nat_vars \<Longrightarrow>
           not_access_v q v \<Longrightarrow>  not_access_v vl v \<Longrightarrow>                                             
           \<turnstile> (q \<cdot> qr \<mapsto> vl)
                (Measure v q)   
              {s. s \<in> (\<Union>i\<in>{q}\<^sub>s. (v\<down>\<^sub>(from_nat i)) \<inter> ((q \<mapsto> (unit_vecl s q i)) \<and>\<^sup>* 
                                  (qr  \<mapsto> (vector_i s q vl i)))\<smile>(\<rho> q vl i s))}" 
*)
(* lemma measure_vars_list:
  assumes 
     a0:"QStateM_vars Q = Q_domain_var (q \<union> qr) (QStateM_map Q)" and
     a1:"QStateM_list Q = vl" and
     a2:"QStateM_vars Q \<noteq> {}" and a3:"(\<forall>e\<in>q. QStateM_map Q e \<noteq> {})" and
     a4:"q  \<inter> qr = {}" and
     a5:"(p,Q') = measure_vars i q Q"
   shows "QStateM_vector Q'  = Q
             partial_state2.ptensor_vec (\<Union> (QStateM_map Q ` q)) 
                                        (\<Union> (QStateM_map Q ` qr))  
                                        (vec_of_list (unit_vecl (p,\<sigma>,Q) q i \<sigma>))
                                        (vec_of_list (vector_i (p,\<sigma>,Q) q vl i \<sigma>))"
proof-
  have "a \<cdot>\<^sub>v ((ptensor_mat v1 v2 ((1\<^sub>k (2^(card v1)))) (1\<^sub>m (2^(card v2)))) *\<^sub>v v) = 
            a \<cdot>\<^sub>v ptensor_vec v1 v2 (unit_vec (2^(card v1)) k) (vector_aij v1 v2 v k)"
qed
 *)


(*lemma measure_vars_pr:
  assumes 
     a0:"QStateM_vars Q = Q_domain_var (q \<sigma> \<union> qr \<sigma>) (QStateM_map Q)" and
     a1:"QStateM_list Q = vl \<sigma>" and
     a2:"QStateM_vars Q \<noteq> {}" and a3:"(\<forall>e\<in>q \<sigma>. QStateM_map Q e \<noteq> {})" and
     a4:"q \<sigma> \<inter> qr \<sigma> = {}" and
     a5:"(p,Q') = measure_vars i (\<Union> (QStateM_map Q ` q \<sigma>)) Q"
   shows "p = pr q vl i (pq,\<sigma>,Q')"
  unfolding pr_def
  sorry *)


lemma allocate_wf1:
  assumes a0:"\<Q>' = Q_State.QStateM(\<vv>', QState (q'_addr,(v \<sigma>)))" and  a1:"length (v \<sigma>) > 1" and     
       a2:"\<vv>' = (\<lambda>i. {})(q' := q'_addr)" and 
      a3:"q'_addr \<in> new_q_addr v \<sigma> (QStateM_map \<Q>) " and
      a4:"\<exists>i<length (v \<sigma>). (v \<sigma>)!i\<noteq>0"
    shows "QState_wf (q'_addr, v \<sigma>) \<and> 
           QStateM_wf ((\<lambda>i. {})(q' := q'_addr), QState (q'_addr, v \<sigma>))  \<and>
           QStateM_map \<Q>' = (\<lambda>i. {})(q' := q'_addr)"
proof-
  have Qstate_wf:"QState_wf (q'_addr, v \<sigma>)"
    unfolding QState_wf_def
     using assms
     unfolding new_q_addr_def
     using assms snd_conv
     using card.infinite by force
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
  assumes a0:"\<Q>' = Q_State.QStateM(\<vv>', QState (q'_addr,(v \<sigma>)))" and a1':"length (v \<sigma>) > 1" and
       a1:"q' \<notin> (dom_q_vars (QStateM_map \<Q>))" and
       a2:"\<vv>' = (\<lambda>i. {})(q' := q'_addr)" and 
      a3:"q'_addr \<in> new_q_addr v \<sigma> (QStateM_map \<Q>) " and a4:"\<exists>i<length (v \<sigma>). (v \<sigma>)!i\<noteq>0"
    shows "QStateM_wf (QStateM_map \<Q> + QStateM_map \<Q>',
                  qstate \<Q> + qstate \<Q>')"
proof-  
  have "QState_wf (q'_addr, v \<sigma>) \<and> 
           QStateM_wf ((\<lambda>i. {})(q' := q'_addr), QState (q'_addr, v \<sigma>))  \<and>
           QStateM_map \<Q>' = (\<lambda>i. {})(q' := q'_addr)"
    using allocate_wf1[of  \<Q>' \<vv>' q'_addr v \<sigma>, OF a0  a1' a2  a3 a4]
    by auto
  moreover have d1:"QStateM_map \<Q> ## QStateM_map \<Q>'"
    using assms calculation
    unfolding dom_q_vars_def sep_disj_fun_def opt_class.domain_def
    by auto 
  moreover have d2:"qstate \<Q> ## qstate \<Q>'" 
unfolding sep_disj_QState disj_QState_def calculation
    using QStateM_wf QState_wf a3 unfolding new_q_addr_def
    apply auto
    by (metis IntI QState_var_idem calculation(1) empty_iff fst_conv snd_conv)             
  ultimately show ?thesis   
    using plus_wf
    by metis 
qed

lemma disjoint_allocate: 
  assumes a0:"\<Q>' = Q_State.QStateM(\<vv>', QState (q'_addr,(v \<sigma>)))" and a1':"length (v \<sigma>) > 1" and
       a1:"q' \<notin> (dom_q_vars (QStateM_map \<Q>))" and
       a2:"\<vv>' = (\<lambda>i. {})(q' := q'_addr)" and
      a3:"q'_addr \<in> new_q_addr v \<sigma> (QStateM_map \<Q>) " and a4:"\<exists>i<length (v \<sigma>). (v \<sigma>)!i\<noteq>0"
    shows "\<Q> ## \<Q>'"
proof-  
  have "QState_wf (q'_addr, v \<sigma>) \<and> 
           QStateM_wf ((\<lambda>i. {})(q' := q'_addr), QState (q'_addr, v \<sigma>))  \<and>
           QStateM_map \<Q>' = (\<lambda>i. {})(q' := q'_addr)"
    using allocate_wf1[of  \<Q>' \<vv>' q'_addr v \<sigma>, OF a0  a1' a2 a3 a4]
    by auto
  moreover have d1:"QStateM_map \<Q> ## QStateM_map \<Q>'"
    using assms calculation
    unfolding dom_q_vars_def sep_disj_fun_def opt_class.domain_def
    by auto 
  moreover have d2:"qstate \<Q> ## qstate \<Q>'" 
    unfolding sep_disj_QState disj_QState_def calculation
    using QStateM_wf QState_wf a3 unfolding new_q_addr_def
    apply auto  
    by (metis IntI QState_var_idem calculation(1) empty_iff fst_conv snd_conv)            
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
  moreover have n_zero:"QStateM_list \<Q>'' ! 0\<noteq>0"
    using Q''0 QStateM_empty_not_zero
    by fastforce
  ultimately have "\<Q> = ((QStateM_list \<Q>'' ! 0) * (inverse (QStateM_list \<Q>'' ! 0))) \<cdot>\<^sub>Q 
                        (\<Q>' + \<Q>'')"
    using scalar_mult_QStateM_plus_l  idem_QState sca_mult_qstatem_def sca_mult_qstate_one by force             
  
  then have "\<Q> = (QStateM_list \<Q>'' ! 0) \<cdot>\<^sub>Q 
                  ( inverse (QStateM_list \<Q>'' ! 0) \<cdot>\<^sub>Q (\<Q>' + \<Q>''))"
    using n_zero inverse_nonzero_iff_nonzero sca_mult_qstatem_assoc
    unfolding sca_mult_qstatem_def
    by (smt (verit, best) QStateM_wf QStateM_wf_map QStateM_wf_qstate prod.sel(1) prod.sel(2) sca_mult_qstate_assoc sca_mult_qstate_vars sca_mult_qstatem_def)
       
  then have "\<Q> = (QStateM_list \<Q>'' ! 0) \<cdot>\<^sub>Q 
                  (\<Q>' + (inverse (QStateM_list \<Q>'' ! 0) \<cdot>\<^sub>Q \<Q>''))"
    using local.a1 scalar_mult_QStateM_plus_r
    by (smt (verit, del_insts) QStateM_disj_dest(2) QStateM_list.rep_eq QStateM_map_plus 
            QStateM_map_qstate QState_list_inv Qstate_map_0_0 a0 a2 
            empty_qstate_def eq_QStateM_vars n_zero nonzero_imp_inverse_nonzero 
            plus_QStateM prod.sel(2) qstate_def sca_mult_qstatem_def 
            scalar_mult_QState_plus_r sep_Q_eq_Q'_Q''_empty 
            sep_add_zero sep_disj_zero zero_QState zero_QStateM)
   
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

primrec redex:: "('v,'s)com \<Rightarrow> ('v,'s)com"
where
"redex Skip = Skip" |
"redex (SMod f) = (SMod f)" |
"redex (QMod f e) = (QMod f e)" |
"redex (Seq c\<^sub>1 c\<^sub>2) = redex c\<^sub>1" |
"redex (IF b c\<^sub>1 c\<^sub>2) = (IF b c\<^sub>1 c\<^sub>2)" |
"redex (While b c) = (While b c)" |
"redex (Measure v e) = (Measure v e)" |
"redex (Alloc v e) = (Alloc v e)" |
"redex (Dispose v e) = (Dispose v e)" 

inductive step::"[('v,'s) QConfE, ('v,'s) QConfE] \<Rightarrow> bool" 
  ("\<turnstile> (_ \<rightarrow>/ _)" [81,81] 100)
  where 
\<comment>\<open>SMod  modifies the stack of non-qubits variables \<sigma> with f \<sigma>, where f is a 
  function modifying the stack\<close>
 StackMod: "\<turnstile> (SMod f, Normal (\<delta>,\<sigma>,\<Q>)) \<rightarrow>  (Skip, Normal (\<delta>,f \<sigma>,\<Q>))"

\<comment>\<open>QMod modifies the set of qubits of the Quantum State given by q \<sigma> with the 
  transformation matrix M, any qubit not included in q \<sigma> remains the same\<close>

 | QMod:"\<Inter>(QStateM_map \<Q> ` (q \<sigma>)) \<noteq> {} \<Longrightarrow> (q \<sigma>)\<noteq>{} \<Longrightarrow> \<Q> = QT \<T> \<Longrightarrow>
         \<Q>' = matrix_sep (q \<sigma>) \<Q> M \<Longrightarrow> matrix_sep_not_zero (q \<sigma>) \<Q> M \<Longrightarrow>         
         \<turnstile>(QMod M q, Normal (\<delta>,\<sigma>,\<T>)) \<rightarrow> (Skip, Normal (\<delta>, \<sigma>, Single \<Q>'))"

\<comment>\<open>QMod fails if the set of qubits to be modified is not included in the quantum state\<close>
| QMod_F:"\<Inter>(QStateM_map \<Q> ` (q \<sigma>)) = {} \<or> (q \<sigma>) = {} \<or> \<not> matrix_sep_not_zero (q \<sigma>) \<Q> M \<Longrightarrow>  \<Q> = QT \<T> \<Longrightarrow>        
          \<turnstile> (QMod M q, Normal (\<delta>,\<sigma>,\<T>))\<rightarrow> (Skip, Fault)"
 
\<comment>\<open>Alloc takes a normal variable "q" representing the variable where the index to the qubits is store
   an function e from the state \<sigma> to a natural number representing the number of qubits to allocate
  and an initialization value for the allocated qubits 


  We will require that a program is well formed, meaning that the types are correct.
  A call to Alloc is well formed if the type of q is a natural number\<close>

(* | Alloc1:"\<forall>q'. q' \<notin> (dom_q_vars (QStateM_map \<Q>)) \<longrightarrow> 
              \<vv>' = (QStateM_map \<Q>)(q' := q'_addr) \<and>  \<sigma>' = set_value \<sigma> q (from_nat q') \<Longrightarrow> 
          q'_addr \<in> new_q_addr e \<sigma> (QStateM_map \<Q>)  \<Longrightarrow> e \<sigma> \<noteq> 0 \<Longrightarrow> length (v \<sigma>) = (e \<sigma>) \<Longrightarrow>                     
          \<turnstile> \<langle>Alloc q e v, Normal (\<delta>,\<sigma>,\<Q>)\<rangle> \<Rightarrow> Normal (\<delta>, \<sigma>',QStateM(\<vv>',\<qq> + QState (q'_addr,(v \<sigma>)) ))" *)

| Alloc:"q' \<notin> (dom_q_vars (QStateM_map \<Q>)) \<Longrightarrow> (length (v \<sigma>) > 1) \<Longrightarrow> \<Q> = QT \<T> \<Longrightarrow>
              \<vv>' = (\<lambda>i. {})(q' := q'_addr) \<and>  \<sigma>' = set_value \<sigma> q (from_nat q') \<Longrightarrow> 
          q'_addr \<in> new_q_addr v \<sigma> (QStateM_map \<Q>)  \<Longrightarrow> \<exists>i<length (v \<sigma>). (v \<sigma>)!i \<noteq>0 \<Longrightarrow>
          \<turnstile> (Alloc q v, Normal (\<delta>,\<sigma>,\<T>)) \<rightarrow> 
             (Skip, Normal (\<delta>, \<sigma>',Single (\<Q> + Q_State.QStateM(\<vv>', QState (q'_addr,(v \<sigma>)) ))))"
(* | Alloc:"q' \<notin> (dom_q_vars (QStateM_map \<Q>)) \<Longrightarrow> q'_addr \<in> new_q_addr e \<sigma> (QStateM_map \<Q>)  \<Longrightarrow> e \<sigma> \<noteq> 0 \<Longrightarrow>
          \<vv>' = (QStateM_map \<Q>)(q' := q'_addr)  \<Longrightarrow> length (v \<sigma>) = (e \<sigma>) \<Longrightarrow> \<sigma>' = set_value \<sigma> q (from_nat q') \<Longrightarrow>                    
          \<turnstile> \<langle>Alloc q e v, Normal (\<delta>,\<sigma>,\<Q>)\<rangle> \<Rightarrow> Normal (\<delta>, \<sigma>',QStateM(\<vv>',\<qq> + QState (q'_addr,(v \<sigma>)) ))" *)
\<comment>\<open>Alloc will fail if the length of the initial value is not equal to the number of qubits allocated \<close>


 | Alloc_F:"length (v \<sigma>) \<le> 1 \<or>  \<not>(\<exists>i<length (v \<sigma>). (v \<sigma>)!i \<noteq>0) \<Longrightarrow>                    
          \<turnstile> (Alloc q v, Normal (\<delta>,\<sigma>,\<Q>)) \<rightarrow>(Skip, Fault)"

\<comment>\<open>the conditional, while, and seq statements follow the standard definitions\<close>

 | CondTrue:"\<sigma>\<in>b \<Longrightarrow>  \<turnstile> (IF b c1 c2, Normal  (\<delta>,\<sigma>,\<Q>)) \<rightarrow> (c1, Normal  (\<delta>,\<sigma>,\<Q>))"

 | CondFalse:"\<sigma>\<notin>b  \<Longrightarrow> \<turnstile> (IF b c1 c2, Normal  (\<delta>,\<sigma>,\<Q>)) \<rightarrow> (c2, Normal  (\<delta>,\<sigma>,\<Q>))"

 | WhileTrue: "\<lbrakk>s\<in>b\<rbrakk>
              \<Longrightarrow> 
                \<turnstile> (While b c,Normal (\<delta>,\<sigma>,\<Q>)) \<rightarrow>  (Seq c (While b c), Normal (\<delta>,\<sigma>,\<Q>))"

 | WhileFalse: "\<sigma>\<notin>b \<Longrightarrow> 
                \<turnstile> (While b c,Normal (\<delta>,\<sigma>,\<Q>)) \<rightarrow>  (Skip, Normal (\<delta>,\<sigma>,\<Q>))"

| Seq: "\<turnstile>(c\<^sub>1,s) \<rightarrow> (c\<^sub>1',s')
        \<Longrightarrow>
        \<turnstile>(Seq c\<^sub>1 c\<^sub>2,s) \<rightarrow> (Seq c\<^sub>1' c\<^sub>2, s')"

| SeqSkip: "\<turnstile>(Seq Skip c\<^sub>2,s) \<rightarrow> (c\<^sub>2, s)"


\<comment>\<open>Dispose takes an expression from the stack to a natural number and removes those qubits
  from the quantum state if they are not entangled with the rest of qubits in the current
  Quantum state. The entanglement condition is that it is possible to find a vector \<qq>1 such that
  \<qq> =  \<qq>' +  \<qq>''\<close>


(* | Dispose: "  \<Q> = \<Q>' + \<Q>'' \<Longrightarrow> \<Q>' ## \<Q>'' \<Longrightarrow> n = vec_norm (QStateM_vector \<Q>'') \<Longrightarrow>
              (\<Union>((QStateM_map \<Q>'') ` (q \<sigma>))) \<noteq> {} \<Longrightarrow> 
              Q_domain (QStateM_map \<Q>'') =(\<Union>((QStateM_map \<Q>'') ` (q \<sigma>))) \<Longrightarrow>                                      
             \<turnstile> \<langle>Dispose q, Normal (\<delta>,\<sigma>,\<Q>)\<rangle> \<Rightarrow> Normal (\<delta>,\<sigma>,QStateM(m', n \<cdot>\<^sub>q Q'))" *)

 | Dispose: "  \<Q>' ## \<Q>'' \<Longrightarrow> n = vec_norm (QStateM_vector \<Q>') \<Longrightarrow> \<Q>' = QT T' \<Longrightarrow> \<Q>'' = QT T'' \<Longrightarrow>
              QStateM_vars \<Q>' \<noteq> {} \<Longrightarrow> 
              QStateM_vars \<Q>' = (Q_domain_var (the (var_set q i \<sigma>)) (QStateM_map \<Q>')) \<Longrightarrow>                                      
              \<forall>e \<in> (the (var_set q i \<sigma>)). (QStateM_map \<Q>') e \<noteq> {} \<Longrightarrow>
             \<turnstile>(Dispose q i, Normal (\<delta>,\<sigma>,Plus T' T'')) \<rightarrow> (Skip, Normal (\<delta>,\<sigma>, Single (n \<cdot>\<^sub>Q  \<Q>'')))"

\<comment>\<open>Dispose dispose will fail if it is not possible to find such states \<qq>',  \<qq>''\<close>

(* | Dispose_F: "\<nexists>\<Q>' \<Q>''.(\<Union>((QStateM_map \<Q>'') ` (q \<sigma>))) \<noteq> {} \<and> 
                Q_domain (QStateM_map \<Q>'') = (\<Union>((QStateM_map \<Q>'') ` (q \<sigma>)))  \<and> 
               \<Q> = \<Q>' + \<Q>'' \<and> \<Q>' ## \<Q>'' \<Longrightarrow>
               \<turnstile> \<langle>Dispose q, Normal (\<delta>,\<sigma>,\<Q>)\<rangle> \<Rightarrow> Fault" *)

| Dispose_F: "(\<nexists>\<Q>' \<Q>''.  \<Q> = Plus (Single \<Q>') (Single \<Q>'') \<and> \<Q>' ## \<Q>'' \<and> QStateM_vars \<Q>' \<noteq> {} \<and> 
               QStateM_vars \<Q>' = (Q_domain_var (the (var_set q i \<sigma>)) (QStateM_map \<Q>')) \<and>
               (\<forall>e \<in> (the (var_set q i \<sigma>)). (QStateM_map \<Q>') e \<noteq> {})) \<Longrightarrow>
               \<turnstile> (Dispose q i, Normal (\<delta>,\<sigma>,\<Q>)) \<rightarrow>(Skip, Fault)"

\<comment>\<open>Measure measures the value of the set of qubits given by q \<sigma> and it stores the result in 
  the stack variable v. Similar to allocate, we will require that the construct is well formed
 and that the type of v is a real number\<close>

 (* | Measure: "q (\<sigma>,\<vv>) = (QState_vars \<qq>1) \<Longrightarrow> k \<in> {0.. 2^(card (q (\<sigma>,\<vv>)))} \<Longrightarrow>
            (\<delta>k, (\<vv>',\<qq>')) = measure_vars k (q (\<sigma>,\<vv>)) (\<vv>,\<qq>) \<Longrightarrow> \<qq> =   \<qq>1 +  \<qq>2 \<and> \<qq>1 ## \<qq>2 \<Longrightarrow>            
            \<delta>k > 0 \<Longrightarrow> \<delta>' = \<delta> * \<delta>k \<Longrightarrow> \<sigma>' = set_value \<sigma> v (from_nat k) \<Longrightarrow>
            \<turnstile> \<langle>Measure v q, Normal (\<delta>,\<sigma>,(\<vv>,\<qq>))\<rangle> \<Rightarrow> Normal (\<delta>',\<sigma>',(\<vv>',\<qq>'))"  *)

| Measure: "addr1 = \<Union>((QStateM_map \<Q>) ` (q \<sigma>)) \<Longrightarrow> \<forall>e \<in> (q \<sigma>). (QStateM_map \<Q>) e \<noteq> {} \<Longrightarrow>                      
            k \<in> {0..<2^(card addr1)} \<Longrightarrow> \<Q> = QT \<T> \<Longrightarrow>       
            (\<delta>k, \<Q>') = measure_vars' k (q \<sigma>) \<Q> \<Longrightarrow>             
            \<delta>k > 0 \<Longrightarrow> \<delta>' = \<delta> * \<delta>k \<Longrightarrow> \<sigma>' = set_value \<sigma> v (from_nat k) \<Longrightarrow>
            \<turnstile> (Measure v q, Normal (\<delta>,\<sigma>,\<T>)) \<rightarrow> (Skip, Normal (\<delta>',\<sigma>',Single \<Q>'))"
\<comment>\<open>Since Measure access to the values of the qubits given by q \<sigma> as QMod, 
  Measure will similarly fail if the set of qubits to be mesured does not
  belong to the set of allocated qubits\<close>

 | Measure_F: "\<exists>e. e \<in> q \<sigma> \<and> (QStateM_map \<Q>) e = {}  \<Longrightarrow> \<Q> = QT \<T> \<Longrightarrow>
              \<turnstile>(Measure v q, Normal (\<delta>,\<sigma>,\<T>)) \<rightarrow> (Skip, Fault)" 

| Fault_Prop:"\<lbrakk>c\<noteq>Skip; redex c = c\<rbrakk> \<Longrightarrow> \<turnstile> (c, Fault) \<rightarrow> (Skip, Fault)"



inductive_cases QExec_elim_cases [cases set]:
 "\<turnstile>(c,Fault) \<rightarrow>  t"  
  "\<turnstile>(Skip,s) \<rightarrow>  t"
  "\<turnstile>(SMod f,s) \<rightarrow>  t"
  "\<turnstile>(QMod m q,s) \<rightarrow>  t"
  "\<turnstile>(Seq c1 c2,s) \<rightarrow> t"
  "\<turnstile>(While b c,s) \<rightarrow>  t"
  "\<turnstile>(IF b c1 c2,s) \<rightarrow>  t"
  "\<turnstile>(Measure v q,s) \<rightarrow>  t"
  "\<turnstile>(Alloc v  e,s) \<rightarrow>  t"
  "\<turnstile>(Dispose q i,s) \<rightarrow>  t"

inductive_cases QExec_Normal_elim_cases [cases set]:
 "\<turnstile>(c,Fault) \<rightarrow>  t"  
  "\<turnstile>(Skip,Normal s) \<rightarrow>  t"
  "\<turnstile>(SMod f,Normal s) \<rightarrow>  t"
  "\<turnstile>(QMod m q,Normal s) \<rightarrow>  t"
  "\<turnstile>(Seq c1 c2,Normal s) \<rightarrow>  t"
  "\<turnstile>(While b c1,Normal s) \<rightarrow>  t"
  "\<turnstile>(IF b c1 c2,Normal s) \<rightarrow>  t"
  "\<turnstile>(Measure v q,Normal s) \<rightarrow>  t"
  "\<turnstile>(Alloc v  e,Normal s) \<rightarrow>  t"
  "\<turnstile>(Dispose q v,Normal s) \<rightarrow>  t"

primrec modify_locals :: "('v, 's) com  \<Rightarrow> 'v set" where 
  "modify_locals  Skip = {}"
| "modify_locals (SMod f) = {v. modify_v f v = True}"
| "modify_locals (QMod _ _) = {}"
| "modify_locals (IF b c1 c2) = modify_locals c1 \<union> modify_locals c2"
| "modify_locals (While b c) = modify_locals c"
| "modify_locals (Seq c1 c2) = modify_locals c1 \<union> modify_locals c2"
| "modify_locals (Measure v e) = {v}"
| "modify_locals (Alloc v val) = {v}"
| "modify_locals (Dispose q v) = {}"

definition final:: "('v,'s) QConf \<Rightarrow> bool" where
"final cfg = (fst cfg=Skip)"


abbreviation
 "step_rtrancl" :: "[('v,'s) QConf,('v,'s) QConf] \<Rightarrow> bool"
                                ("\<turnstile> (_ \<rightarrow>\<^sup>*/ _)" [81,81] 100)
 where
  "\<turnstile>cf0 \<rightarrow>\<^sup>* cf1 \<equiv> (CONST step)\<^sup>*\<^sup>* cf0 cf1"
abbreviation
 "step_trancl" :: "[('v,'s) QConf,('v,'s) QConf] \<Rightarrow> bool"
                                ("\<turnstile> (_ \<rightarrow>\<^sup>+/ _)" [81,81] 100)
 where
  "\<turnstile>cf0 \<rightarrow>\<^sup>+ cf1 \<equiv> (CONST step)\<^sup>+\<^sup>+ cf0 cf1"

lemma redex_not_Seq: "redex c = Seq c1 c2 \<Longrightarrow> P"
  apply (induct c)
  apply auto
  done

lemma no_step_final:
  assumes step: "\<turnstile>(c,s) \<rightarrow> (c',s')"
  shows "final (c,s) \<Longrightarrow> P"
using step
by induct (auto simp add: final_def)

lemma no_step_final':
  assumes step: "\<turnstile> cfg \<rightarrow> cfg'"
  shows "final cfg \<Longrightarrow> P"
  using step
  by (cases cfg', cases cfg) (auto intro:no_step_final)

lemma step_Fault': 
  assumes step: "\<turnstile> (c,s) \<rightarrow>  (c',s')" and s1:"snd (c,s) = Fault"
  shows "snd (c',s') = Fault"
  using step s1 by (induct, auto)

lemma step_Fault: 
  assumes step: "\<turnstile> (c,s) \<rightarrow>  (c',s')"
  shows "s = Fault \<Longrightarrow> s' = Fault"
  using step_Fault'[OF step] by auto

lemma SeqSteps:
  assumes steps: "\<turnstile>cfg\<^sub>1\<rightarrow>\<^sup>* cfg\<^sub>2"
  shows "\<And> c\<^sub>1 s c\<^sub>1' s'. \<lbrakk>cfg\<^sub>1 = (c\<^sub>1,s);cfg\<^sub>2=(c\<^sub>1',s')\<rbrakk>
          \<Longrightarrow> \<turnstile>(Seq c\<^sub>1 c\<^sub>2,s) \<rightarrow>\<^sup>* (Seq c\<^sub>1' c\<^sub>2, s')"
using steps
proof (induct rule: converse_rtranclp_induct [case_names Refl Trans])
  case Refl
  thus ?case
    by simp
next
  case (Trans cfg\<^sub>1 cfg'')
  have step: "\<turnstile> cfg\<^sub>1 \<rightarrow> cfg''" by fact
  have steps: "\<turnstile> cfg'' \<rightarrow>\<^sup>* cfg\<^sub>2" by fact
  have cfg\<^sub>1: "cfg\<^sub>1 = (c\<^sub>1, s)" and cfg\<^sub>2: "cfg\<^sub>2 = (c\<^sub>1', s')"  by fact+
  obtain c\<^sub>1'' s'' where cfg'': "cfg''=(c\<^sub>1'',s'')"
    by (cases cfg'') auto
  from step cfg\<^sub>1 cfg''
  have "\<turnstile> (c\<^sub>1,s) \<rightarrow> (c\<^sub>1'',s'')"
    by simp
  hence "\<turnstile> (Seq c\<^sub>1 c\<^sub>2,s) \<rightarrow> (Seq c\<^sub>1'' c\<^sub>2,s'')"
    by (rule step.Seq)
  also from Trans.hyps (3) [OF cfg'' cfg\<^sub>2]
  have "\<turnstile> (Seq c\<^sub>1'' c\<^sub>2, s'') \<rightarrow>\<^sup>* (Seq c\<^sub>1' c\<^sub>2, s')" .
  finally show ?case .
qed

lemma steps_Fault: "\<turnstile> (c, Fault) \<rightarrow>\<^sup>* (Skip, Fault)"
proof (induct c)
  case (Seq c\<^sub>1 c\<^sub>2)
  have steps_c\<^sub>1: "\<turnstile> (c\<^sub>1, Fault) \<rightarrow>\<^sup>* (Skip, Fault)" by fact
  have steps_c\<^sub>2: "\<turnstile> (c\<^sub>2, Fault) \<rightarrow>\<^sup>* (Skip, Fault)" by fact
  from SeqSteps [OF steps_c\<^sub>1 refl refl]
  have "\<turnstile> (Seq c\<^sub>1 c\<^sub>2, Fault) \<rightarrow>\<^sup>* (Seq Skip c\<^sub>2, Fault)".
  also
  have "\<turnstile> (Seq Skip c\<^sub>2, Fault) \<rightarrow> (c\<^sub>2, Fault)" by (rule SeqSkip)
  also note steps_c\<^sub>2
  finally show ?case by simp
qed (fastforce intro: step.intros)+

lemma steps_Fault_prop:
  assumes step: "\<turnstile> (c, s) \<rightarrow>\<^sup>* (c', s')"
  shows "s=Fault  \<Longrightarrow> s'=Fault "
using step
proof (induct rule: converse_rtranclp_induct2 [case_names Refl Trans])
  case Refl thus ?case by simp
next
  case (Trans c s c'' s'')
  thus ?case
    by (auto intro: step_Fault)
qed

end 

end


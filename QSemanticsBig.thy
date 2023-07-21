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

(* definition
  unit_vecl :: "nat \<Rightarrow> nat \<Rightarrow> complex list"
  where "unit_vecl n i = list_of_vec (unit_vec n i)" *)


lemma i_less_union: 
  assumes a0:"(i::nat) < 2 ^ card v1 * 2 ^ card v2" and
    a1:"v1 \<inter> v2 = {}" and
    a2:"finite v1" and
    a3:"finite v2"
  shows"i < 2 ^ card (v1 \<union> v2)"
  using a0 a1 a2 a3
  by (simp add: card_Un_disjoint power_add)

context partial_state2 
begin

lemma ptensor_mat_M_N_row: 
     assumes 
       a0:"i < d0" and
       a1:"dim_vec (V::complex vec) = d0"
     shows "(ptensor_mat M N *\<^sub>v V) $ i = 
             row (ptensor_mat M N) i \<bullet> V"
proof -
  have "i < dim_row (ptensor_mat  M N)"
    by (simp add: a0 )
  then show ?thesis
    by (meson index_mult_mat_vec)
qed

lemma ptensor_map_M_N: 
     assumes 
       a0:"i < d0" and
       a1:"j < d0" 
     shows "ptensor_mat M N $$ (i,j) = 
            M $$ (partial_state.encode1 dims0 vars1' i,
                 (partial_state.encode1 dims0 vars1' j)) *
            N $$ (partial_state.encode2 dims0 vars1' i,
                 (partial_state.encode2 dims0 vars1' j))"
proof-
  let ?m1 = "M" and ?m2 = "N" and ?d = "dims0"
  let ?v = "vars1'"  let  ?v' = "vars2'"

 let ?enc1 = "partial_state.encode1 dims0 ?v" and
     ?enc2 = "partial_state.encode2 dims0 ?v"

  have "dims0 = ?d" unfolding dims0_def list_dims_def vars0_def by auto
  moreover have "ptensor_mat ?m1 ?m2 $$ (i,j) = 
        ?m1 $$ (?enc1 i, ?enc1 j) * ?m2 $$ (?enc2 i, ?enc2  j)"
    unfolding ptensor_mat_def 
    apply (rule  partial_state.tensor_mat_eval, auto simp add:  state_sig.d_def vars0_def)
    using a0 a1 d0_def   by auto
  ultimately show ?thesis
    using ptensor_encode2_encode1 by presburger 
qed


lemma row_i_ptensor_M_N: 
     assumes 
       a0:"i < d0" 
     shows "row (ptensor_mat M N) i =
            Matrix.vec d0 
        (\<lambda>j.  M $$ (partial_state.encode1 dims0 vars1' i,
                 (partial_state.encode1 dims0 vars1' j)) *
            N $$ (partial_state.encode2 dims0 vars1' i,
                 (partial_state.encode2 dims0 vars1' j)))"
proof-
  have "row (ptensor_mat M N) i = 
        Matrix.vec (dim_col (ptensor_mat M N)) (\<lambda> j. (ptensor_mat M N) $$ (i,j))"
    using row_def by blast
  also have "Matrix.vec (dim_col (ptensor_mat M N)) (\<lambda> j. (ptensor_mat M N) $$ (i,j)) =
             Matrix.vec (dim_col (ptensor_mat M N)) 
                (\<lambda>j. M $$ (partial_state.encode1 dims0 vars1' i,
                 (partial_state.encode1 dims0 vars1' j)) *
               N $$ (partial_state.encode2 dims0 vars1' i,
                 (partial_state.encode2 dims0 vars1' j)))"
    using a0 ptensor_map_M_N by fastforce
   finally show ?thesis
     by (simp add: a0 )
qed

definition aijv::"complex vec  \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>  complex"
  where "aijv v i j\<equiv>  v$(pencode12 (i,j))"

lemma eq_vec_aijv:
      assumes a0:"i<d0" and a1:"dim_vec (v::complex vec) = d0"         
       shows "v $ i = aijv v                        
                    (partial_state.encode1 dims0 vars1' i) 
                    (partial_state.encode2 dims0 vars1' i)"
proof-
  
  let ?i = "(\<lambda>i. partial_state.encode1 dims0 vars1'  i)"
  let ?j = "(\<lambda>i. partial_state.encode2 dims0 vars1'  i)"
   have "v $ i = aijv  v (?i i) (?j i)"
    unfolding aijv_def using a0
    by (simp add: d0_def partial_state.encode12_inv pencode12_def state_sig.d_def) 
  then show ?thesis 
    unfolding  list_dims_def dims0_def vars0_def  by auto
qed

lemma eq_vec_aijv_v2_empty:
      assumes a0:"i < d0" and a1:"dim_vec (v::complex vec) = d0" and
              a2:"vars2 = {}"        
       shows "v $ i = aijv v i 0"
proof-
  
  let ?i = "(\<lambda>i. partial_state.encode1 dims0 vars1' i)"
  let ?j = "(\<lambda>i. partial_state.encode2 dims0 vars1' i)"
  have "v $ i = aijv v (?i i) (?j i)"
    unfolding aijv_def using a0
    using a1 aijv_def eq_vec_aijv by presburger  
  moreover have "(?j i) = 0" 
    unfolding partial_state.encode2_def dims0_def
    using a2 digit_decode_non_vars1 partial_state.dims2_def vars0_def vars1'_def by auto    
  moreover have "(?i i) = i" using a2
    unfolding  list_dims_def dims0_def vars0_def apply auto
    by (metis Int_absorb a0 digit_decode_vars ind_in_set_id length_replicate order_refl 
            partial_state.dims2_def partial_state.encode2_alter length_dims0_minus_vars2'_is_vars1' vars1'_def 
          prod_list_replicate d0_def d1_def d2_def dims0_def dims1_def dims_product 
         finite_v1 nths_vars1' nths_vars1'_comp  ptensor_encode1_encode2 vars0_def sup_bot.right_neutral)   
  ultimately show ?thesis using a2
     by auto    
qed

definition vector_aij::"complex vec  \<Rightarrow> nat \<Rightarrow> complex vec"
  where "vector_aij  v i \<equiv> Matrix.vec d2 (\<lambda>j. aijv v i j)"

definition list_aij::"complex vec  \<Rightarrow> nat \<Rightarrow> complex list"
  where "list_aij v i \<equiv> map (\<lambda>j. aijv  v i j) [0..< d2]"


end


definition aij ::"'s state \<Rightarrow> 's expr_q  \<Rightarrow> ('s, complex list) expr \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>complex" 
  where "aij s q v i j \<equiv> let st = get_stack s ; qv = fst (get_qstate s); 
                             vars = Q_domain qv; d1 = q st; d2 = vars - d1;
                             vec = vec_of_list (v st) in 
                             partial_state2.aijv d1 d2 vec i j"


lemma ptensor_mat_M_1m_assoc:
      assumes a0:"finite vars1" and a1:"finite vars2" and a2:"vars1 \<inter> vars2 = {}" and             
              a3:"vars1 = vars0 \<union> vars0'" and a4:"vars0 \<inter> vars0' = {}" 
     shows "ptensor_mat vars0 (vars0' \<union> vars2) (M::complex mat) (1\<^sub>m (2^(card (vars0' \<union> vars2)))) = 
           ptensor_mat vars1 vars2 (ptensor_mat vars0 vars0' M (1\<^sub>m (2^(card vars0')))) (1\<^sub>m (2^(card vars2)))"
proof-
  interpret ps21:partial_state2 "list_dims (vars1 \<union> vars2)" vars1 vars2
    apply standard unfolding list_dims_def by (auto simp add: a0 a1 a2)
  
  interpret ps22:partial_state2 "list_dims (vars0 \<union> (vars0' \<union> vars2))" vars0 "(vars0' \<union> vars2)"
    apply standard unfolding list_dims_def
    apply (auto simp add: a0 a1 a2 a3 a4 )
    using a0 a2 a3 a4 by fast+
  
  interpret ps23:partial_state2 "list_dims (vars0 \<union> vars0')" vars0 vars0'
    apply standard unfolding list_dims_def
    apply (auto simp add: a4)
    using a0 a3 by fast+
  
  interpret ps24:partial_state2 "list_dims (vars0' \<union> vars2)" vars0' vars2
    apply standard unfolding list_dims_def
    apply (auto simp add: a0 a1 a2 a3 a4 )
    using a0 a2 a3 a4 by fast+

  have f1:"1\<^sub>m (2^(card (vars0' \<union> vars2))) = 
          ps24.ptensor_mat (1\<^sub>m (2^(card vars0'))) (1\<^sub>m (2^(card vars2)))"
    by (metis prod_list_replicate ps24.d0_def ps24.d1_def ps24.d2_def ps24.dims0_def 
         ps24.dims1_def ps24.dims2_def ps24.pmat_extension_def 
         ps24.pmat_extension_id ps24.vars0_def)
  have "{} = (vars0 \<union> vars0') \<inter> vars2"
      using a2 a3 by auto
  then have "ptensor_mat (vars0 \<union> vars0') vars2 (ps23.ptensor_mat M (1\<^sub>m (2 ^ card vars0'))) (1\<^sub>m (2 ^ card vars2)) = 
               ps22.ptensor_mat M (ps24.ptensor_mat (1\<^sub>m (2 ^ card vars0')) (1\<^sub>m (2 ^ card vars2)))"
    by (simp add: a1 ps23.disjoint ps23.finite_v1 ps24.finite_v1 ptensor_mat_assoc)
  then show ?thesis  by (simp add: f1 a3)
qed

lemma ptensor_mat_M_m1_mult_tensor_prod_assoc:
     assumes a0:"finite vars1" and a1:"finite vars2" and a2:"vars1 \<inter> vars2 = {}" and             
             a3:"vars1 = vars0 \<union> vars0'" and a4:"vars0 \<inter> vars0' = {}" and 
             a6:"v1 \<in> carrier_vec (2 ^ card vars1)" and a7:"v2 \<in> carrier_vec (2^card vars2)"
     shows "ptensor_mat vars0 ((vars1 \<union> vars2) - vars0) (M::complex mat) (1\<^sub>m (2 ^ card ((vars1 \<union> vars2) - vars0))) *\<^sub>v 
              (ptensor_vec vars1 vars2 v1 v2) = 
            ptensor_vec vars1 vars2 ((ptensor_mat vars0 vars0' M (1\<^sub>m (2 ^ card vars0'))) *\<^sub>v v1) 
                                    ((1\<^sub>m (2 ^ card vars2)) *\<^sub>v v2)"
proof-
  interpret ps21:partial_state2 "list_dims (vars1 \<union> vars2)" vars1 vars2
    apply standard unfolding list_dims_def by (auto simp add: a0 a1 a2)
  
  interpret ps22:partial_state2 "list_dims (vars0 \<union> (vars0' \<union> vars2))" vars0 "(vars0' \<union> vars2)"
    apply standard unfolding list_dims_def
    apply (auto simp add: a0 a1 a2 a3 a4 )
    using a0 a2 a3 a4 by fast+
  
  interpret ps23:partial_state2 "list_dims (vars0 \<union> vars0')" vars0 vars0'
    apply standard unfolding list_dims_def
    apply (auto simp add: a4)
    using a0 a3 by fast+
  
  interpret ps24:partial_state2 "list_dims (vars0' \<union> vars2)" vars0' vars2
    apply standard unfolding list_dims_def
    apply (auto simp add: a0 a1 a2 a3 a4 )
    using a0 a2 a3 a4 by fast+
  have "ptensor_mat vars0 (vars0' \<union> vars2) (M::complex mat) (1\<^sub>m (2^(card (vars0' \<union> vars2)))) *\<^sub>v 
              (ptensor_vec vars1 vars2 v1 v2) = 
        ptensor_mat vars1 vars2 (ptensor_mat vars0 vars0' M (1\<^sub>m (2^(card vars0')))) (1\<^sub>m (2^(card vars2)))  *\<^sub>v 
              (ptensor_vec vars1 vars2 v1 v2)"
    using a0 a1 a2 a3 ps23.disjoint ptensor_mat_M_1m_assoc by auto
  moreover have "(ptensor_mat vars0 vars0' M (1\<^sub>m (2^(card vars0')))) \<in> carrier_mat (2^ card vars1)  (2^ card vars1)"
    using a3 ps23.d0_def ps23.dims0_def ps23.vars0_def by auto
  moreover have " (1\<^sub>m (2^(card vars2))) \<in>  carrier_mat (2^ card vars2)  (2^ card vars2)"
    by simp
  moreover have "(vars1 \<union> vars2) - vars0 = vars0' \<union> vars2"
    by (metis Diff_cancel Int_Diff_Un Int_commute Un_Diff Un_assoc a3 ps22.disjoint)
  ultimately  show ?thesis using a6 a7 
    by (metis  partial_state2.d1_def prod_list_replicate ps21.dims1_def ps21.partial_state2_axioms 
             ps21.ptensor_mat_mult_vec ps24.d2_def ps24.dims2_def)

qed


definition matrix_sep :: "nat set \<Rightarrow>  QStateM \<Rightarrow> complex mat \<Rightarrow>  complex vec"
  where "matrix_sep heap_ind q M \<equiv>
           let sep_vars = \<Union> ((QStateM_map q) ` heap_ind)  in
           let var_d = QStateM_vars q in 
           let var_r = var_d - sep_vars in
           let v = QStateM_vector q in           
           let m = ptensor_mat sep_vars var_r
                               (M::complex mat) (1\<^sub>m (2^(card var_r)))  in 
              m *\<^sub>v v"
\<comment>\<open> To proof frame rule, it is necessary to adapt the previous definition to a semantics in which we don't 
   check whether the matrix size is equal to the size of the qubits we are modifying, but
   checking whether it is bigger than the size of the current state.

   As a consequence, the definition of matrix_sep doesn't use the qubits we are modifying rather the
   size of the matrix. The operation will be correct (according to the intuition of what the operation must do) 
   only when the size of the matrix is equal to the size of the qubits we want to modify
   \<close>
definition matrix_sep_a :: "nat set \<Rightarrow>  QStateM \<Rightarrow> complex mat \<Rightarrow>  complex vec"
  where "matrix_sep_a heap_ind q M \<equiv>
           let sep_vars = \<Union> ((QStateM_map q) ` heap_ind)  in
           let var_d = QStateM_vars q in 
           let var_r = var_d - sep_vars in
           let v = QStateM_vector q in           
           let m = ptensor_mat sep_vars var_r
                               (M::complex mat) (1\<^sub>m (2^(card var_r)))  in 
              if (dim_row M = 2^(card sep_vars)) then
                m *\<^sub>v v
              else v"

lemma matrix_sep_tensor_product':
  assumes a0:"Q =  Q1 + Q2" and a1:"\<Union> ((QStateM_map Q) ` q) \<subseteq> QStateM_vars Q1" and  
          a4:"vars0' = (QStateM_vars Q1) - \<Union> ((QStateM_map Q) ` q)" and
          a6:"Q1##Q2" 
     shows "matrix_sep q Q M = 
            ptensor_vec (QStateM_vars Q1) (QStateM_vars Q2) ((ptensor_mat (\<Union> ((QStateM_map Q) ` q)) vars0' M (1\<^sub>m (2 ^ card vars0'))) *\<^sub>v QStateM_vector Q1) 
                                    ((1\<^sub>m (2 ^ card (QStateM_vars Q2))) *\<^sub>v QStateM_vector Q2)"
proof-
  let ?sep_vars = "\<Union> ((QStateM_map Q) ` q)"
  let ?var_d = "QStateM_vars Q"
  let ?var_r = "?var_d - ?sep_vars"
  let ?v = "QStateM_vector Q"
  let ?m = "ptensor_mat ?sep_vars ?var_r M (1\<^sub>m (2^(card ?var_r)))"
  have "?v = ptensor_vec (QStateM_vars Q1) (QStateM_vars Q2) (QStateM_vector Q1) (QStateM_vector Q2)"
    using a0 a6 apply auto
    by (simp add: QStateM_list_plus vec_list vec_of_list_QStateM_list) 
  then have m:"matrix_sep q Q M = ?m *\<^sub>v ptensor_vec (QStateM_vars Q1) (QStateM_vars Q2) (QStateM_vector Q1) (QStateM_vector Q2)" 
    unfolding matrix_sep_def  by auto
  have f0:"finite (QStateM_vars Q1)"
    by (simp add: QStateM_vars.rep_eq QState_rel2')
  have f1:"finite (QStateM_vars Q2)"
    by (simp add: QStateM_vars.rep_eq QState_rel2')
  have f2:"QStateM_vars Q1 \<inter> QStateM_vars Q2 = {}"
    using QStateM_disj_dest(2) QStateM_vars.rep_eq a6 disj_QState_def qstate_def sep_disj_QState by force
  have f3:"QStateM_vars Q1 = \<Union> (QStateM_map Q ` q) \<union> vars0'"
    using a1 a4 by auto
  have f4:"\<Union> (QStateM_map Q ` q) \<inter> vars0' = {}"
    using a4 by blast
  have f5:"QStateM_vector Q1 \<in> carrier_vec (2 ^ card (QStateM_vars Q1))"
    by (metis (no_types) QStateM_list_dim carrier_vecI vec_of_list_QStateM_list)
  have f6:"QStateM_vector Q2 \<in> carrier_vec (2 ^ card (QStateM_vars Q2))"
    by (metis (no_types) QStateM_list_dim carrier_vecI vec_of_list_QStateM_list)
  have "QStateM_vars Q = QStateM_vars Q1 \<union> QStateM_vars Q2"
    by (simp add: QStateM_vars_plus a0 a6)
  then have "?m *\<^sub>v ptensor_vec (QStateM_vars Q1) (QStateM_vars Q2) (QStateM_vector Q1) (QStateM_vector Q2) = ptensor_vec (QStateM_vars Q1) (QStateM_vars Q2)
     (ptensor_mat (\<Union> (QStateM_map Q ` q)) vars0' M (1\<^sub>m (2 ^ card vars0')) *\<^sub>v QStateM_vector Q1)
     (1\<^sub>m (2 ^ card (QStateM_vars Q2)) *\<^sub>v QStateM_vector Q2)" 
    using ptensor_mat_M_m1_mult_tensor_prod_assoc[OF f0 f1 f2 f3 f4 f5 f6]
     by presburger
  thus ?thesis using m 
    by presburger 
qed

lemma matrix_sep_tensor_product'_a1:
  assumes a0:"Q =  Q1 + Q2" and a1:"\<Union> ((QStateM_map Q) ` q) \<subseteq> QStateM_vars Q1" and  
          a4:"vars0' = (QStateM_vars Q1) - \<Union> ((QStateM_map Q) ` q)" and
          a6:"Q1##Q2" and a7:"dim_row M = 2^(card (\<Union> ((QStateM_map Q) ` q)))"
     shows "matrix_sep_a q Q M = 
            ptensor_vec (QStateM_vars Q1) (QStateM_vars Q2) ((ptensor_mat (\<Union> ((QStateM_map Q) ` q)) vars0' M (1\<^sub>m (2 ^ card vars0'))) *\<^sub>v QStateM_vector Q1) 
                                    ((1\<^sub>m (2 ^ card (QStateM_vars Q2))) *\<^sub>v QStateM_vector Q2)"
proof-
  let ?sep_vars = "\<Union> ((QStateM_map Q) ` q)"
  let ?var_d = "QStateM_vars Q"
  let ?var_r = "?var_d - ?sep_vars"
  let ?v = "QStateM_vector Q"
  let ?m = "ptensor_mat ?sep_vars ?var_r M (1\<^sub>m (2^(card ?var_r)))"
  have v:"?v = ptensor_vec (QStateM_vars Q1) (QStateM_vars Q2) (QStateM_vector Q1) (QStateM_vector Q2)"
    using a0 a6 apply auto
    by (simp add: QStateM_list_plus vec_list vec_of_list_QStateM_list) 
  moreover have m:"matrix_sep q Q M = ?m *\<^sub>v ptensor_vec (QStateM_vars Q1) (QStateM_vars Q2) (QStateM_vector Q1) (QStateM_vector Q2)" 
    unfolding matrix_sep_def using calculation  by auto
  moreover have f0:"finite (QStateM_vars Q1)"
    by (simp add: QStateM_vars.rep_eq QState_rel2')
  have f1:"finite (QStateM_vars Q2)"
    by (simp add: QStateM_vars.rep_eq QState_rel2')
  have f2:"QStateM_vars Q1 \<inter> QStateM_vars Q2 = {}"
    using QStateM_disj_dest(2) QStateM_vars.rep_eq a6 disj_QState_def qstate_def sep_disj_QState by force
  have f3:"QStateM_vars Q1 = \<Union> (QStateM_map Q ` q) \<union> vars0'"
    using a1 a4 by auto
  have f4:"\<Union> (QStateM_map Q ` q) \<inter> vars0' = {}"
    using a4 by blast
  have f5:"QStateM_vector Q1 \<in> carrier_vec (2 ^ card (QStateM_vars Q1))"
    by (metis (no_types) QStateM_list_dim carrier_vecI vec_of_list_QStateM_list)
  have f6:"QStateM_vector Q2 \<in> carrier_vec (2 ^ card (QStateM_vars Q2))"
    by (metis (no_types) QStateM_list_dim carrier_vecI vec_of_list_QStateM_list)
  have "QStateM_vars Q = QStateM_vars Q1 \<union> QStateM_vars Q2"
    by (simp add: QStateM_vars_plus a0 a6)
  then have "?m *\<^sub>v ptensor_vec (QStateM_vars Q1) (QStateM_vars Q2) (QStateM_vector Q1) (QStateM_vector Q2) = ptensor_vec (QStateM_vars Q1) (QStateM_vars Q2)
     (ptensor_mat (\<Union> (QStateM_map Q ` q)) vars0' M (1\<^sub>m (2 ^ card vars0')) *\<^sub>v QStateM_vector Q1)
     (1\<^sub>m (2 ^ card (QStateM_vars Q2)) *\<^sub>v QStateM_vector Q2)" 
    using ptensor_mat_M_m1_mult_tensor_prod_assoc[OF f0 f1 f2 f3 f4 f5 f6]
     by presburger
  ultimately show ?thesis using a7 matrix_sep_a_def by presburger 
qed

lemma matrix_sep_tensor_product'_a2:
  assumes a0:"Q =  Q1 + Q2" and a1:"\<Union> ((QStateM_map Q) ` q) \<subseteq> QStateM_vars Q1" and  
          a4:"vars0' = (QStateM_vars Q1) - \<Union> ((QStateM_map Q) ` q)" and
          a6:"Q1##Q2" and a7:"dim_row M \<noteq> 2^(card (\<Union> ((QStateM_map Q) ` q)))"
     shows "matrix_sep_a q Q M = 
            ptensor_vec (QStateM_vars Q1) (QStateM_vars Q2) (QStateM_vector Q1) (QStateM_vector Q2)"
proof-
  let ?sep_vars = "\<Union> ((QStateM_map Q) ` q)"
  let ?var_d = "QStateM_vars Q"
  let ?var_r = "?var_d - ?sep_vars"
  let ?v = "QStateM_vector Q"
  let ?m = "ptensor_mat ?sep_vars ?var_r M (1\<^sub>m (2^(card ?var_r)))"
  have v:"?v = ptensor_vec (QStateM_vars Q1) (QStateM_vars Q2) (QStateM_vector Q1) (QStateM_vector Q2)"
    using a0 a6 apply auto
    by (simp add: QStateM_list_plus vec_list vec_of_list_QStateM_list) 
  then show ?thesis unfolding matrix_sep_a_def using a7
    by auto
qed

lemma matrix_sep_tensor_product_a1:
  assumes a0:"Q =  Q1 + Q2" and a1:"\<Union> ((QStateM_map Q) ` q) \<subseteq> QStateM_vars Q1" and  
          a4:"vars0' = (QStateM_vars Q1) - \<Union> ((QStateM_map Q) ` q)" and a3:"\<forall>e\<in>q. QStateM_map Q1 e \<noteq> {}" and
          a6:"Q1##Q2" and a7:"dim_row M = 2^(card (\<Union> ((QStateM_map Q) ` q)))"
     shows "matrix_sep_a q Q M = 
            ptensor_vec (QStateM_vars Q1) (QStateM_vars Q2) (matrix_sep q Q1 M) (QStateM_vector Q2)"
proof-
  have f1:"\<Union> ((QStateM_map Q) ` q) = \<Union> ((QStateM_map Q1) ` q)" using a1
    by (metis QStateM_map_plus SUP_cong Sep_Prod_Instance.none_def a0 a3 a6 plus_fun_def sep_add_commute sep_disj_commuteI)
  moreover have "matrix_sep_a q Q M = 
            ptensor_vec (QStateM_vars Q1) (QStateM_vars Q2) ((ptensor_mat (\<Union> ((QStateM_map Q) ` q)) vars0' M (1\<^sub>m (2 ^ card vars0'))) *\<^sub>v QStateM_vector Q1) 
                                    ((1\<^sub>m (2 ^ card (QStateM_vars Q2))) *\<^sub>v QStateM_vector Q2)"
    using matrix_sep_tensor_product'[OF a0 a1 a4 a6]
    by (simp add: a7 matrix_sep_a_def matrix_sep_def)
  moreover have "matrix_sep q Q1 M = (ptensor_mat (\<Union> ((QStateM_map Q1) ` q)) vars0' M (1\<^sub>m (2 ^ card vars0'))) *\<^sub>v QStateM_vector Q1"
    using a4 calculation unfolding matrix_sep_def Let_def by auto
  ultimately have "matrix_sep_a q Q M = 
                     ptensor_vec (QStateM_vars Q1) (QStateM_vars Q2) (matrix_sep q Q1 M) 
                       ((1\<^sub>m (2 ^ card (QStateM_vars Q2))) *\<^sub>v QStateM_vector Q2)"  
    by auto
  then show ?thesis using f1
    by (metis QStateM_list_dim carrier_vec_dim_vec one_mult_mat_vec vec_of_list_QStateM_list) 
qed

lemma matrix_sep_tensor_product_a2:
  assumes a0:"Q =  Q1 + Q2" and a1:"\<Union> ((QStateM_map Q) ` q) \<subseteq> QStateM_vars Q1" and  
          a4:"vars0' = (QStateM_vars Q1) - \<Union> ((QStateM_map Q) ` q)" and a3:"\<forall>e\<in>q. QStateM_map Q1 e \<noteq> {}" and
          a6:"Q1##Q2" and a7:"dim_row M \<noteq> 2^(card (\<Union> ((QStateM_map Q) ` q)))"
     shows "matrix_sep_a q Q M = 
            ptensor_vec (QStateM_vars Q1) (QStateM_vars Q2) (QStateM_vector Q1) (QStateM_vector Q2)"
  using a0 a1 a6 a7 matrix_sep_tensor_product'_a2 by presburger

lemma matrix_sep_tensor_product:
  assumes a0:"Q =  Q1 + Q2" and a1:"\<Union> ((QStateM_map Q) ` q) \<subseteq> QStateM_vars Q1" and  
          a4:"vars0' = (QStateM_vars Q1) - \<Union> ((QStateM_map Q) ` q)" and a3:"\<forall>e\<in>q. QStateM_map Q1 e \<noteq> {}" and
          a6:"Q1##Q2" and a7:"dim_row M = 2^(card (\<Union> ((QStateM_map Q) ` q)))"
     shows "matrix_sep q Q M = 
            ptensor_vec (QStateM_vars Q1) (QStateM_vars Q2) (matrix_sep q Q1 M) (QStateM_vector Q2)"
proof-
  have f1:"\<Union> ((QStateM_map Q) ` q) = \<Union> ((QStateM_map Q1) ` q)" using a1
    by (metis QStateM_map_plus SUP_cong Sep_Prod_Instance.none_def a0 a3 a6 plus_fun_def sep_add_commute sep_disj_commuteI)
  moreover have "matrix_sep q Q M = 
            ptensor_vec (QStateM_vars Q1) (QStateM_vars Q2) ((ptensor_mat (\<Union> ((QStateM_map Q) ` q)) vars0' M (1\<^sub>m (2 ^ card vars0'))) *\<^sub>v QStateM_vector Q1) 
                                    ((1\<^sub>m (2 ^ card (QStateM_vars Q2))) *\<^sub>v QStateM_vector Q2)"
    using matrix_sep_tensor_product'[OF a0 a1 a4 a6] by auto
  moreover have "matrix_sep q Q1 M = (ptensor_mat (\<Union> ((QStateM_map Q1) ` q)) vars0' M (1\<^sub>m (2 ^ card vars0'))) *\<^sub>v QStateM_vector Q1"
    using a4 calculation unfolding matrix_sep_def Let_def by auto
  ultimately have "matrix_sep q Q M = 
                     ptensor_vec (QStateM_vars Q1) (QStateM_vars Q2) (matrix_sep q Q1 M) 
                       ((1\<^sub>m (2 ^ card (QStateM_vars Q2))) *\<^sub>v QStateM_vector Q2)"  
    by auto
  then show ?thesis using f1
    by (metis QStateM_list_dim carrier_vec_dim_vec one_mult_mat_vec vec_of_list_QStateM_list) 
qed

definition matrix_sep_QStateM :: "nat set \<Rightarrow>  QStateM \<Rightarrow> complex mat \<Rightarrow>  QStateM" 
  where "matrix_sep_QStateM heap_ind q M \<equiv>
           let matrix_sep_var = matrix_sep heap_ind q M in 
             QStateM (QStateM_map q, QState (QStateM_vars q, list_of_vec (matrix_sep_var)))"

definition matrix_sep_QStateM_a :: "nat set \<Rightarrow>  QStateM \<Rightarrow> complex mat \<Rightarrow>  QStateM" 
  where "matrix_sep_QStateM_a heap_ind q M \<equiv>
           let matrix_sep_var = matrix_sep_a heap_ind q M in 
             QStateM (QStateM_map q, QState (QStateM_vars q, list_of_vec (matrix_sep_var)))"

(* definition matrix_sep_var' :: "nat set \<Rightarrow>  QStateM \<Rightarrow> complex mat \<Rightarrow>  complex vec" 
  where "matrix_sep_var' heap_ind q M \<equiv>
           QStateM_vector (matrix_sep heap_ind q M)" *)




(* definition matrix_sep_not_zero :: "nat set \<Rightarrow>  QStateM \<Rightarrow> complex mat \<Rightarrow>  bool" 
  where "matrix_sep_not_zero heap_ind q M \<equiv>             
             \<exists>i<length (list_of_vec (matrix_sep heap_ind q M)). 
                list_of_vec (matrix_sep heap_ind q M)!i \<noteq> 0" *)

lemma dest_var:
      "sep_vars = \<Union> ((QStateM_map q) ` hi) \<Longrightarrow> var_r = (QStateM_vars q) - sep_vars \<Longrightarrow> 
       m = ptensor_mat sep_vars var_r (M::complex mat) (1\<^sub>m (2^(card var_r))) \<Longrightarrow> 
       dim_row M = 2^(card sep_vars) \<Longrightarrow>
       matrix_sep_QStateM hi q M = 
         QStateM (QStateM_map q, QState (QStateM_vars q, list_of_vec (m *\<^sub>v QStateM_vector q)))" 
  unfolding matrix_sep_QStateM_def matrix_sep_def  Let_def by auto

lemma dest_var_a_1:
      "sep_vars = \<Union> ((QStateM_map q) ` hi) \<Longrightarrow> var_r = (QStateM_vars q) - sep_vars \<Longrightarrow> 
       m = ptensor_mat sep_vars var_r (M::complex mat) (1\<^sub>m (2^(card var_r))) \<Longrightarrow> 
       dim_row M = 2^(card sep_vars) \<Longrightarrow>
       matrix_sep_QStateM_a hi q M = 
         QStateM (QStateM_map q, QState (QStateM_vars q, list_of_vec (m *\<^sub>v QStateM_vector q)))" 
  unfolding matrix_sep_QStateM_a_def matrix_sep_a_def  Let_def by auto

lemma dest_var_a_2:
      "sep_vars = \<Union> ((QStateM_map q) ` hi) \<Longrightarrow> 
       dim_row M \<noteq> 2^(card sep_vars) \<Longrightarrow>
       matrix_sep_QStateM_a hi q M = 
         QStateM (QStateM_map q, QState (QStateM_vars q, list_of_vec (QStateM_vector q)))" 
  unfolding matrix_sep_QStateM_a_def matrix_sep_a_def  Let_def by auto

lemma unitary_1m:"unitary (1\<^sub>m n)"
  using unitary_one by auto

lemma unitary_preserves_norm:
  assumes a0:"unitary M" and a1:"vec_norm v = 1" and 
          a2:"M \<in> carrier_mat m m" and a3:"v \<in> carrier_vec m"
        shows "vec_norm (M *\<^sub>v v) = 1"
proof-
  have M_1:"adjoint M * M = 1\<^sub>m m"
    by (simp add: a0 a2)
  have neutre_1m:"1\<^sub>m m  *\<^sub>v v = v"
    using a3 one_mult_mat_vec by blast
  have "vec_norm v = (csqrt (v \<bullet>c v))" using vec_norm_def by auto
  also  have "(csqrt (v \<bullet>c v)) = (csqrt (v \<bullet>c ((adjoint M * M) *\<^sub>v v)))"
    using M_1 neutre_1m by presburger
  also have "(csqrt (v \<bullet>c ((adjoint M * M) *\<^sub>v v))) = 
             (csqrt ((M *\<^sub>v v) \<bullet>c (M *\<^sub>v v)))"
    by (smt (verit, best) a2 a3 adjoint_def_alter 
         adjoint_dim assoc_mult_mat_vec mult_mat_vec_carrier)
  finally show ?thesis unfolding vec_norm_def a1
    using \<open>vec_norm v = csqrt (inner_prod v v)\<close> a1 by presburger
qed
  

lemma ptensor_mat_mult_QStateM_norm:
  assumes 
      a2:"M' = ptensor_mat (\<Union> ((QStateM_map q) ` hi)) ((QStateM_vars q) - (\<Union> ((QStateM_map q) ` hi))) 
                          (M::complex mat) (1\<^sub>m (2^(card ((QStateM_vars q) - (\<Union> ((QStateM_map q) ` hi))))))" and
       a4:"unitary M" and a5:"M \<in> carrier_mat (2^(card (\<Union> ((QStateM_map q) ` hi)))) (2^(card (\<Union> ((QStateM_map q) ` hi))))"
    shows "vec_norm (M' *\<^sub>v QStateM_vector q) = 1"
proof-
  let ?sep_vars = "\<Union> ((QStateM_map q) ` hi)" 
  let ?var_r = "(QStateM_vars q) - (\<Union> ((QStateM_map q) ` hi))"
  interpret ps2: partial_state2 "list_dims (?sep_vars \<union> ?var_r)" ?sep_vars ?var_r 
    apply standard  apply (auto simp add: list_dims_def)
    using Q_domain_var_def finite_Q_domain_var apply presburger
    by (metis QStateM_rel1 QStateM_vars.rep_eq Q_domain_def Q_domain_var_def 
             finite_Diff finite_Q_domain_var qstate_def)
  interpret ps: partial_state "list_dims (?sep_vars \<union> ?var_r)" ps2.vars1'  .
  have M_carrier_d1:"M \<in> carrier_mat ps2.d1 ps2.d1" 
    using a5
    by (simp add: ps2.d1_def ps2.dims1_def)
  moreover have onem_carrier_d2:"1\<^sub>m (2^(card ?var_r)) \<in> carrier_mat ps2.d2 ps2.d2"
    by (simp add: ps2.d2_def ps2.dims2_def)
  ultimately have "M' \<in> carrier_mat ps2.d0 ps2.d0"
    using a2 ps2.ptensor_mat_carrier by blast 
  
  moreover have "unitary M'" using ps.tensor_mat_unitary M_carrier_d1 onem_carrier_d2 a4
    by (metis a2 ps.d1_def ps.d2_def ps.dims1_def ps.dims2_def ps2.d1_def 
              ps2.d2_def ps2.dims0_def ps2.dims_vars1_2 ps2.nths_vars1' 
              ps2.nths_vars2' ps2.ptensor_mat_def ps2.vars0_def unitary_one)
    
  moreover have "vec_norm (QStateM_vector q) = 1"
    by (simp add: QStateM_vector.rep_eq QState_rel3')
  moreover have "QStateM_vector q \<in> carrier_vec ps2.d0"
  proof-
    have "dim_vec (QStateM_vector q) = ps2.d0" 
      by (metis QStateM_list_dim QStateM_rel1 QStateM_vars.rep_eq 
         Q_domain_def UNIV_I UN_Un Un_Diff_cancel2 Un_commute 
         partial_state2.dims0_def prod_list_replicate ps2.d0_def 
         ps2.partial_state2_axioms ps2.vars0_def qstate_def subsetI sup.absorb2 
         vec_of_list_QStateM_list)
    thus ?thesis
      by (metis carrier_vec_dim_vec) 
  qed
  ultimately show ?thesis using unitary_preserves_norm
    by presburger
qed

lemma matrix_sep_norm:
  assumes a0:"unitary M" and a1:"M \<in> carrier_mat (2^(card (\<Union> ((QStateM_map q) ` hi)))) (2^(card (\<Union> ((QStateM_map q) ` hi))))" and
    a3:"v' = matrix_sep hi q M" 
  shows "vec_norm v' = 1" 
proof-
  let  ?var_d = "QStateM_vars q" and ?sep_vars = "\<Union> ((QStateM_map q) ` hi)"
  let ?var_r = "?var_d - ?sep_vars" and ?v = "QStateM_vector q"
  let ?m = "ptensor_mat ?sep_vars ?var_r
                               (M::complex mat) (1\<^sub>m (2^(card ?var_r)))"
  show "vec_norm v' = 1" 
    using a3 unfolding matrix_sep_def  apply auto
    using a0 a1  ptensor_mat_mult_QStateM_norm by blast
qed

lemma matrix_sep_norm_a:
  assumes a0:"unitary M" and  a1:"M \<in> carrier_mat m m" and
    a3:"v' = matrix_sep_a hi q M" 
  shows "vec_norm v' = 1" 
proof-
  let  ?var_d = "QStateM_vars q" and ?sep_vars = "\<Union> ((QStateM_map q) ` hi)"
  let ?var_r = "?var_d - ?sep_vars" and ?v = "QStateM_vector q"
  let ?m = "ptensor_mat ?sep_vars ?var_r
                               (M::complex mat) (1\<^sub>m (2^(card ?var_r)))"
  { 
    assume "m = (2^(card (\<Union> ((QStateM_map q) ` hi))))"
    then have "vec_norm v' = 1" 
      using a3  a0  a1  ptensor_mat_mult_QStateM_norm  unfolding matrix_sep_a_def  
      by auto
  }
  moreover{
     assume "m \<noteq> (2^(card (\<Union> ((QStateM_map q) ` hi))))"
     then have "vec_norm v' = 1" 
       using QStateM_vector.rep_eq QState_rel3' a1 a3 unfolding matrix_sep_a_def  by force
   }
   ultimately show ?thesis by auto
qed

lemma matrix_sep_eq_len:
  assumes 
      a0:"M \<in> carrier_mat (2^(card (\<Union> ((QStateM_map q) ` hi)))) (2^(card (\<Union> ((QStateM_map q) ` hi))))"
    shows "dim_vec (matrix_sep hi q M) = dim_vec (QStateM_vector q)"
proof-
  let ?sep_vars = "\<Union> ((QStateM_map q) ` hi)" and ?var_d = "QStateM_vars q" 
  let ?var_r = "?var_d - ?sep_vars"
  let ?prod = "M *\<^sub>v QStateM_vector q"
  let ?l = "list_of_vec ?prod"
  
  let  ?v = "QStateM_vector q" 
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
    apply (metis QStateM_rel1 Q_domain_def UNIV_I UN_Un UnCI eq_QStateM_vars snd_conv subsetI subset_antisym)
    apply (metis UNIV_I UN_Un UnCI rev_finite_subset subsetI subset_antisym)
    by (metis QStateM_rel1 QStateM_vars.rep_eq finite_Diff finite_Q_domain qstate_def)
  show ?thesis unfolding matrix_sep_def Let_def apply auto
    by (metis QStateM_list_dim prod_list_replicate ps2.d0_def ps2.dims0_def 
              ps2.dims_vars1_2 ps2.vars0_def vec_of_list_QStateM_list) 
qed

lemma matrix_sep_a_eq_len:
  assumes 
      a0:"M \<in> carrier_mat m m"
  shows "dim_vec (matrix_sep_a hi q M) = dim_vec (QStateM_vector q)"
proof-
  let ?sep_vars = "\<Union> ((QStateM_map q) ` hi)" and ?var_d = "QStateM_vars q" 
  let ?var_r = "?var_d - ?sep_vars"
  let ?prod = "M *\<^sub>v QStateM_vector q"
  let ?l = "list_of_vec ?prod"
  
  let  ?v = "QStateM_vector q" 
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
    apply (metis QStateM_rel1 Q_domain_def UNIV_I UN_Un UnCI eq_QStateM_vars snd_conv subsetI subset_antisym)
    apply (metis UNIV_I UN_Un UnCI rev_finite_subset subsetI subset_antisym)
    by (metis QStateM_rel1 QStateM_vars.rep_eq finite_Diff finite_Q_domain qstate_def)
  show ?thesis unfolding matrix_sep_a_def Let_def apply auto
  by (metis QStateM_list_dim prod_list_replicate ps2.d0_def ps2.dims0_def 
            ps2.dims_vars1_2 ps2.vars0_def vec_of_list_QStateM_list) 
qed


lemma matrix_sep_QState_wf:
  assumes 
      a3:"unitary M" and a4:"M \<in> carrier_mat (2^(card ( \<Union> ((QStateM_map q) ` hi)))) (2^(card ( \<Union> ((QStateM_map q) ` hi))))"
    shows "QState_wf(QStateM_vars q, list_of_vec (matrix_sep hi q M)) \<and> 
           QStateM_wf (QStateM_map q, QState (QStateM_vars q, list_of_vec (matrix_sep hi q M)))"
proof-
  let ?var_d = "QStateM_vars q" 
  let ?sep_vars = "\<Union> (QStateM_map q ` hi)" and
       ?var_d = "QStateM_vars q" 
  let ?var_r = "?var_d - ?sep_vars" and ?v = "QStateM_vector q" 
  let ?m = "ptensor_mat ?sep_vars ?var_r M (1\<^sub>m (2 ^ card ?var_r))"
  let ?prod = "?m *\<^sub>v QStateM_vector q"
  let ?l = "list_of_vec ?prod"
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
    apply (metis QStateM_rel1 Q_domain_def UNIV_I UN_Un UnCI eq_QStateM_vars snd_conv subsetI subset_antisym)
    apply (metis UNIV_I UN_Un UnCI rev_finite_subset subsetI subset_antisym)
    by (metis QStateM_rel1 QStateM_vars.rep_eq finite_Diff finite_Q_domain qstate_def)
  
  have Q_wf:"QState_wf (QStateM_vars q, list_of_vec (?m *\<^sub>v ?v))" unfolding QState_wf_def using a4
    unfolding matrix_sep_def Let_def  
    apply (auto simp add: matrix_sep_def )
    unfolding ps2.d0_def ps2.dims0_def ps2.vars0_def apply transfer   
    unfolding Q_domain_def apply auto
     apply (metis UN_Un Un_UNIV_right )
    using Diff_infinite_finite ps2.finite_v1 ps2.finite_v2 apply blast
    by (metis a3 ptensor_mat_mult_QStateM_norm vec_list)
  

  moreover have "QState_vars (QState (QStateM_vars q, list_of_vec (?m *\<^sub>v ?v))) = 
             QStateM_vars q"
    using QState_var_idem calculation
    by blast   
  ultimately show ?thesis unfolding matrix_sep_def Let_def 
    using  eq_QStateM_vars qm_wf by auto 
qed

lemma matrix_sep_QState_a_wf:
  assumes 
      a3:"unitary M" and a4:"M \<in> carrier_mat m m"
    shows "QState_wf(QStateM_vars q, list_of_vec (matrix_sep_a hi q M)) \<and> 
           QStateM_wf (QStateM_map q, QState (QStateM_vars q, list_of_vec (matrix_sep_a hi q M)))"
proof-
  let ?var_d = "QStateM_vars q" 
  let ?sep_vars = "\<Union> (QStateM_map q ` hi)" and
       ?var_d = "QStateM_vars q" 
  let ?var_r = "?var_d - ?sep_vars" and ?v = "QStateM_vector q" 
  let ?m = "ptensor_mat ?sep_vars ?var_r M (1\<^sub>m (2 ^ card ?var_r))"
  let ?prod = "?m *\<^sub>v QStateM_vector q"
  let ?l = "list_of_vec ?prod"
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
    apply (metis QStateM_rel1 Q_domain_def UNIV_I UN_Un UnCI eq_QStateM_vars snd_conv subsetI subset_antisym)
    apply (metis UNIV_I UN_Un UnCI rev_finite_subset subsetI subset_antisym)
    by (metis QStateM_rel1 QStateM_vars.rep_eq finite_Diff finite_Q_domain qstate_def)
  { assume a00:"m = 2^(card ( ?sep_vars))"
    then have Q_wf:"QState_wf (QStateM_vars q, list_of_vec (?m *\<^sub>v ?v))" unfolding QState_wf_def using a4
      unfolding matrix_sep_a_def Let_def  
      apply (auto simp add: matrix_sep_a_def )
      unfolding ps2.d0_def ps2.dims0_def ps2.vars0_def apply transfer   
      unfolding Q_domain_def apply auto
       apply (metis UN_Un Un_UNIV_right )
      using Diff_infinite_finite ps2.finite_v1 ps2.finite_v2 apply blast
      by (metis a3 ptensor_mat_mult_QStateM_norm vec_list)
    moreover have "QState_vars (QState (QStateM_vars q, list_of_vec (?m *\<^sub>v ?v))) = 
             QStateM_vars q"
      using QState_var_idem calculation
      by blast   
    ultimately have ?thesis unfolding matrix_sep_a_def Let_def 
      using  eq_QStateM_vars qm_wf
      using a00 a4 by auto
  }
  moreover {
    assume "m \<noteq> 2^(card ( ?sep_vars))"
    then have ?thesis
      using QStateM_list.rep_eq QStateM_rel1 QStateM_rel2 QStateM_vars.rep_eq QState_var_idem 
      QState_wf a4 list_of_vec_QStateM_vec matrix_sep_a_def qstate_def by force
  }
  ultimately show ?thesis by auto
qed

(* lemma matrix_sep_QState_wf:
  assumes a0:"sep_vars = \<Union> ((QStateM_map q) ` hi)" and a1:"var_r = (QStateM_vars q) - sep_vars" and
      a2:"m = ptensor_mat sep_vars var_r (M::complex mat) (1\<^sub>m (2^(card var_r)))" and
      a3:"unitary M" and a4:"M \<in> carrier_mat (2^(card (sep_vars))) (2^(card (sep_vars)))"
    shows "QState_wf(QStateM_vars q, list_of_vec (m *\<^sub>v QStateM_vector q)) \<and> 
           QStateM_wf (QStateM_map q, QState (QStateM_vars q, list_of_vec (m *\<^sub>v QStateM_vector q)))"
proof-
  let ?prod = "m *\<^sub>v QStateM_vector q"
  let ?l = "list_of_vec ?prod"
  
  let ?var_d = "QStateM_vars q" 
   let ?sep_vars = "\<Union> (QStateM_map q ` hi)" and
       ?var_d = "QStateM_vars q" 
  let ?var_r = "?var_d - ?sep_vars" and ?v = "QStateM_vector q" 
  let ?m = "ptensor_mat sep_vars var_r M (1\<^sub>m (2 ^ card var_r))"
  have qm_wf: "QStateM_wf (QStateM_unfold q)"
    using QStateM_wf by blast
  moreover have q_wf:"QState_wf (QState_unfold (qstate q))"
    using qm_wf QState_wf by blast
  ultimately have finite_Q_domain:"finite (Q_domain (QStateM_map q))" 
    unfolding QState_wf_def by auto   
  interpret ps2:partial_state2 "replicate (card (QStateM_vars q)) 2" "?sep_vars" "?var_r"
    apply standard using a0 a1
    apply blast
      apply simp using finite_Q_domain
    unfolding Q_domain_def 
     apply auto      
     apply (subgoal_tac "\<Union> (QStateM_map q ` hi) \<subseteq> \<Union> (range (QStateM_map q))") 
      apply auto
    apply (metis QStateM_rel1 Q_domain_def UNIV_I UN_Un UnCI eq_QStateM_vars snd_conv subsetI subset_antisym)
    apply (metis UNIV_I UN_Un UnCI rev_finite_subset subsetI subset_antisym)
    by (metis QStateM_rel1 QStateM_vars.rep_eq finite_Diff finite_Q_domain qstate_def)
  
  have Q_wf:"QState_wf (QStateM_vars q, list_of_vec (?m *\<^sub>v ?v))" unfolding QState_wf_def using a4
    unfolding matrix_sep_def Let_def matrix_sep_not_zero_def 
    apply (auto simp add: matrix_sep_def a0 a1 a2)
    unfolding ps2.d0_def ps2.dims0_def ps2.vars0_def apply transfer   
    unfolding Q_domain_def apply auto
     apply (metis UN_Un Un_UNIV_right )
    using Diff_infinite_finite ps2.finite_v1 ps2.finite_v2 apply blast
    by (metis a3 ptensor_mat_mult_QStateM_norm vec_list)

  moreover have "QState_vars (QState (QStateM_vars q, list_of_vec (?m *\<^sub>v ?v))) = 
             QStateM_vars q"
    using QState_var_idem calculation
    by blast   
  ultimately show ?thesis using a2 eq_QStateM_vars qm_wf by auto 
qed
*)


lemma matrix_sep_QStateM_wf:
      "unitary M \<Longrightarrow>  M \<in> carrier_mat (2^(card ( \<Union> ((QStateM_map q) ` hi)))) (2^(card ( \<Union> ((QStateM_map q) ` hi)))) \<Longrightarrow>
       QState_wf ((QStateM_vars ((matrix_sep_QStateM hi q M)),QStateM_list (matrix_sep_QStateM hi q M))) \<and> 
       QStateM_wf (QStateM_map (matrix_sep_QStateM hi q M), qstate(matrix_sep_QStateM hi q M))"
proof-     
  
  let ?sep_vars = "\<Union> ((QStateM_map q) ` hi)" 
  let ?var_r = "(QStateM_vars q) - ?sep_vars" 
  assume a0:"unitary M" and 
         a1:"M \<in> carrier_mat (2^(card (?sep_vars))) (2^(card ( ?sep_vars)))" 

  obtain mp' vs' v'' where "QStateM(mp', QState(vs', v'')) = matrix_sep_QStateM hi q M" and 
                       "mp' = QStateM_map q" and "vs' = QStateM_vars q" and "v'' = list_of_vec (matrix_sep hi q M)"
    unfolding matrix_sep_QStateM_def by auto
  moreover have "QState_wf(vs', v'') \<and> 
            QStateM_wf (mp', QState (vs',v''))" 
    using calculation matrix_sep_QState_wf[OF a0 a1] by auto
  ultimately show ?thesis
    using QStateM_list.rep_eq QStateM_vars.rep_eq QStateM_wf QState_wf by auto 
qed

lemma matrix_sep_QStateM_a_wf:
      "unitary M \<Longrightarrow>  M \<in> carrier_mat m m \<Longrightarrow>
       QState_wf ((QStateM_vars ((matrix_sep_QStateM hi q M)),QStateM_list (matrix_sep_QStateM hi q M))) \<and> 
       QStateM_wf (QStateM_map (matrix_sep_QStateM hi q M), qstate(matrix_sep_QStateM hi q M))"
proof-     
  
  let ?sep_vars = "\<Union> ((QStateM_map q) ` hi)" 
  let ?var_r = "(QStateM_vars q) - ?sep_vars" 
  assume a0:"unitary M" and 
         a1:"M \<in> carrier_mat m m" 
  { assume "m = (2^(card ( \<Union> ((QStateM_map q) ` hi))))"
    then obtain mp' vs' v'' where "QStateM(mp', QState(vs', v'')) = matrix_sep_QStateM_a hi q M" and 
                       "mp' = QStateM_map q" and "vs' = QStateM_vars q" and "v'' = list_of_vec (matrix_sep_a hi q M)"
    unfolding matrix_sep_QStateM_a_def by auto
    moreover have "QState_wf(vs', v'') \<and> 
            QStateM_wf (mp', QState (vs',v''))" 
      using calculation matrix_sep_QState_a_wf[OF a0 a1] by auto
    ultimately have ?thesis
      using QStateM_list.rep_eq QStateM_vars.rep_eq QStateM_wf QState_wf by auto 
  }
  moreover {
    assume "m \<noteq> (2^(card ( \<Union> ((QStateM_map q) ` hi))))"
    have ?thesis
      by (metis QStateM_list.rep_eq QStateM_wf QState_wf eq_QStateM_vars qstate_def snd_conv)
  }
  ultimately show ?thesis by auto
qed


lemma matrix_sep_dest:
  assumes  a3:"unitary M" and 
     a4:"M \<in> carrier_mat (2^(card ( \<Union> (QStateM_map q ` hi)))) (2^(card (\<Union> (QStateM_map q ` hi))))"
  shows "QStateM_map (matrix_sep_QStateM hi q M) = QStateM_map q \<and> 
       QStateM_vars (matrix_sep_QStateM hi q M) = QStateM_vars q \<and>
       QStateM_list (matrix_sep_QStateM hi q M) = 
         list_of_vec (matrix_sep hi q M)"  
  using a3 a4 unfolding matrix_sep_QStateM_def Let_def
  using QStateM_wf_list QStateM_wf_map QStateM_wf_vars 
        QState_list_idem QState_var_idem matrix_sep_QState_wf by presburger

lemma matrix_sep_a_dest:
  assumes  a3:"unitary M" and 
     a4:"M \<in> carrier_mat m m"
  shows "QStateM_map (matrix_sep_QStateM_a hi q M) = QStateM_map q \<and> 
       QStateM_vars (matrix_sep_QStateM_a hi q M) = QStateM_vars q \<and>
       QStateM_list (matrix_sep_QStateM_a hi q M) = 
         list_of_vec (matrix_sep_a hi q M)"  
  using a3 a4 unfolding matrix_sep_QStateM_a_def Let_def
  using QStateM_wf_list QStateM_wf_map QStateM_wf_vars 
        QState_list_idem QState_var_idem matrix_sep_QState_a_wf[of M m]
  by presburger 
   

context partial_state2
begin

lemma mat_extend_M_1k_zero: 
  assumes
       a3:"i < d0" and
       a4:"j < d0" and 
       a7:"partial_state.encode2 dims0 vars1' i \<noteq>
           partial_state.encode2 dims0 vars1' j"
       shows "ptensor_mat M (1\<^sub>m d2) $$ (i,j) = 0"
proof-
  let ?m1 = "M" and ?m2 = "1\<^sub>m d2" and ?d = "dims0"
  let ?v = "vars1'"   

 let ?enc1 = "partial_state.encode1 dims0 ?v" and
     ?enc2 = "partial_state.encode2 dims0 ?v"

  have "dims0 = ?d" unfolding dims0_def list_dims_def vars0_def by auto
  moreover have "ptensor_mat ?m1 ?m2 $$ (i,j) = 
        ?m1 $$ (?enc1 i, ?enc1 j) * ?m2 $$ (?enc2 i, ?enc2  j)"
    unfolding ptensor_mat_def 
    apply (rule  partial_state.tensor_mat_eval, auto simp add: dims0_def state_sig.d_def vars0_def)
    using a3 d0_def dims0_def vars0_def apply auto[1]
    using a4 d0_def dims0_def vars0_def by force 
    
  moreover have " ?m2 $$ (?enc2 i, ?enc2  j) = 0"
    by (metis a3 a4 a7 d0_def d2_def index_one_mat(1) nths_vars2' partial_state.d2_def 
      partial_state.dims2_def partial_state.encode2_lt state_sig.d_def)
  ultimately show ?thesis
    using mult_not_zero by auto   
qed


lemma mat_extend_M_1k_M: 
     assumes 
       a0:"i < d0" and
       a1:"j < d0" and 
       a2:"partial_state.encode2 dims0 vars1' i =
           partial_state.encode2 dims0 vars1' j"
     shows "ptensor_mat M (1\<^sub>m d2) $$ (i,j) = 
            M $$ (partial_state.encode1 dims0 vars1' i,
                 (partial_state.encode1 dims0 vars1' j))"
proof-
  let ?m1 = "M" and ?m2 = "1\<^sub>m d2" and ?d = "dims0"
  let ?v = "vars1'"   

 let ?enc1 = "partial_state.encode1 dims0 ?v" and
     ?enc2 = "partial_state.encode2 dims0 ?v"

  have "dims0 = ?d" unfolding dims0_def list_dims_def vars0_def by auto
  moreover have "ptensor_mat ?m1 ?m2 $$ (i,j) = 
        ?m1 $$ (?enc1 i, ?enc1 j) * ?m2 $$ (?enc2 i, ?enc2  j)"
    unfolding ptensor_mat_def
    by (metis a0 a1 d0_def partial_state.tensor_mat_eval state_sig.d_def)
  moreover have " ?m2 $$ (?enc2 i, ?enc2  j) = 1"
    by (metis a1 a2 d0_def d2_def index_one_mat(1) nths_vars2' partial_state.d2_def 
             partial_state.dims2_def partial_state.encode2_lt state_sig.d_def)
  ultimately show ?thesis using mult.comm_neutral by metis    
qed

lemma row_mat_extend_M_v: 
     assumes 
       a0:"i < d0" 
     shows "row (ptensor_mat M (1\<^sub>m d2)) i =
            Matrix.vec d0 
        (\<lambda>j. if (partial_state.encode2 dims0 vars1' j) = 
                 (partial_state.encode2 dims0 vars1' i)  then 
                 M $$ (partial_state.encode1 dims0 vars1' i,
                      (partial_state.encode1 dims0 vars1' j))
             else 0)"
proof-
  have "row (ptensor_mat M (1\<^sub>m d2)) i = 
       Matrix.vec d0
        (\<lambda>j.  M $$ (partial_state.encode1 dims0 vars1' i,
                   (partial_state.encode1 dims0 vars1' j)) *
            ((1\<^sub>m d2) $$ (partial_state.encode2 dims0 vars1' i,
                        (partial_state.encode2 dims0 vars1' j))))"
    using a0  row_i_ptensor_M_N by blast
  thus ?thesis
    by (smt (verit, best) a0  dim_vec eq_vecI index_vec mat_extend_M_1k_M mat_extend_M_1k_zero row_def)
qed



lemma mat_extend_M_M_v_scalar_product_i': 
  assumes
       a0:"i < d0" and
       a1:"dim_vec (V::complex vec) = d0"
     shows "(ptensor_mat M (1\<^sub>m d2) *\<^sub>v V) $ i = row (ptensor_mat  M (1\<^sub>m d2)) i \<bullet> V"
  by (meson a0 a1  ptensor_mat_M_N_row)


(* 
extend_vec takes a vector v of size 2^card vars1  and a j < 2^card vars2
and returns a vector of size d0 (2^card vars1+card vars2) equivalent to 
tensor_product v v', where v' is defined as the vector such that 
for all j'< 2^cards vars2  v'$j' = 1 if j' = j and v'$j' = 0 if j' \<noteq> j

*)
definition extend_vec::"complex vec \<Rightarrow> nat \<Rightarrow> complex vec"
  where "extend_vec v j \<equiv> 
    Matrix.vec d0 
      (\<lambda>i. if (partial_state.encode2 dims0 vars1' i) = j then 
                v$(partial_state.encode1 dims0 vars1' i)
           else 0)"

lemma d0_card_v1_v2:"d0 = ((2^(card vars1)) * (2^(card vars2)))"
  by (simp add: d1_def d2_def dims1_def dims2_def dims_product)

lemma extend_vec_equiv:
    assumes a0:"dim_vec v = d1" and
            a1:"j<d2" and a2:"v2 = Matrix.vec d2 (\<lambda>i. if i=j then 1 else 0)"
          shows "extend_vec v j = ptensor_vec v v2"
proof-
  have p0:"ptensor_vec v v2 = 
        Matrix.vec d0 
                  (\<lambda>i. v$(partial_state.encode1 dims0 vars1' i) * 
                       v2$(partial_state.encode2 dims0 vars1' i))"
    using a0 a2 unfolding partial_state.tensor_vec_def ptensor_vec_def 
    apply auto
    using d0_def state_sig.d_def by presburger
  moreover {fix i
    assume "i < dim_vec (local.ptensor_vec v v2)"
    then have "Matrix.vec d0
          (\<lambda>i. if partial_state.encode2 dims0 vars1' i = j
               then v $ partial_state.encode1 dims0 vars1' i else 0) $
         i =
         local.ptensor_vec v v2 $ i" 
      using p0 a0 a1 a2
      apply auto
      by (smt (verit, best) d0_def d2_def index_vec nths_vars2' partial_state.d2_def 
             partial_state.dims2_def partial_state.encode2_lt state_sig.d_def)
  }
  ultimately show ?thesis unfolding  extend_vec_def   by auto   
qed


lemma row_tensor_map_eq_extend_row:
     assumes 
       a0:"i < d0" and
       a1:"dim_col M = d1"
     shows "row (ptensor_mat M (1\<^sub>m d2)) i = 
            extend_vec (row M (partial_state.encode1 dims0 vars1'  i)) (partial_state.encode2 dims0 vars1'  i)"
proof-
  have "row (ptensor_mat M (1\<^sub>m d2)) i =
        Matrix.vec d0
        (\<lambda>j. if (partial_state.encode2 dims0 vars1' j) = 
                 (partial_state.encode2 dims0 vars1' i)  then 
                 M $$ (partial_state.encode1 dims0 vars1' i,
                      (partial_state.encode1 dims0 vars1' j))
             else 0)"
    using row_mat_extend_M_v
    using a0  disjoint finite_v1 finite_v2 
    unfolding dims0_def list_dims_def vars0_def
    using d0_card_v1_v2
    using dim_vec by blast
  also have "Matrix.vec d0
   (\<lambda>j. if partial_state.encode2 dims0 vars1' j = partial_state.encode2 dims0 vars1' i
        then M $$
             (partial_state.encode1 dims0 vars1' i, partial_state.encode1 dims0 vars1' j)
        else 0) = 
       extend_vec (row M (partial_state.encode1 dims0 vars1' i))
                   (partial_state.encode2 dims0 vars1' i)" 
    unfolding extend_vec_def row_def 
    apply rule
     apply (metis (no_types, lifting) a1 d1_def dim_vec index_vec 
          local.ptensor_mat_dim_col partial_state.d2_def 
          partial_state.dims2_def partial_state.encode2_lt 
          partial_state.tensor_mat_dim_col partial_state2.nths_vars1'_comp 
          partial_state2_axioms ptensor_encode1_encode2 ptensor_mat_def)
    by auto 
  finally show ?thesis by auto
qed

definition trim_vec::"complex vec \<Rightarrow> nat \<Rightarrow> complex vec"
  where "trim_vec v j \<equiv> 
          Matrix.vec d1 (\<lambda>i. v$partial_state.encode12 dims0 vars1' (i,j))"

lemma sum_v_as_sum_v1_v2:
  assumes a0:"dim_vec v = d0" and a1:"dim_vec V = d0"
  shows "(\<Sum>i = 0..< d0. v $ i * V $ i) = 
       (\<Sum>i = 0 ..< d1. \<Sum>j = 0 ..<d2. (v $ (pencode12 (i,j))) * (V$ (pencode12 (i,j))))"
proof-
  let ?i = "(\<lambda>i. partial_state.encode1 dims0 vars1' i)"
  let ?j = "(\<lambda>i. partial_state.encode2 dims0 vars1' i)"
  have "(\<Sum>i = 0..< d0. v $ i *  V $ i) = (\<Sum>i = 0..< d0. v $ (pencode12 (?i i, ?j i)) * V $ (pencode12 (?i i, ?j i)))"
    using partial_state.encode12_inv dims_product 
         partial_state2_axioms  partial_state2.pencode12_def 
    unfolding  d0_def d1_def d2_def dims1_def dims2_def  state_sig.d_def by auto
  also have "\<dots> = (\<Sum>i = 0 ..<d1. \<Sum>j = 0 ..<d2. v $ pencode12 (i,j) *  V $ pencode12 (i,j))"    
  proof-
    have "dim_vec v = state_sig.d dims0" and
         "partial_state.d2 dims0 vars1' = d2" and
         "partial_state.d1 dims0 vars1' = d1"
       unfolding state_sig.d_def
      using d0_def d1_def dims0_def dims1_def 
            dims2_def dims_product a0
      using partial_state.d2_def partial_state.dims2_def d2_def nths_vars2'
      using partial_state.d1_def partial_state.dims1_def nths_vars1' by auto
    thus ?thesis  
      using partial_state.sum_encode[THEN sym, where dims1 = dims0 and vars1 = vars1'] a0
      by fastforce
  qed
  finally show ?thesis by auto
qed

lemma split_sum:
  assumes a0:"i<(m::nat)"
  shows "(\<Sum>j = 0..<m. f (j::nat)) = (\<Sum>j = 0..<i. f j) + f i + (\<Sum>j = i+1..<m. f j)"
proof-
  show ?thesis using sum_Un[of "{0..i}" " {i + 1..<m}" "\<lambda>j. j"] a0
    by (metis Suc_leI add.commute assms plus_1_eq_Suc sum.atLeast0_lessThan_Suc sum.atLeastLessThan_concat zero_le)
qed

lemma row_tensor_mat_M_1_V_only_M: assumes a0:"i < d0" and 
             a1:"dim_col M = d1"and a2:"dim_row M = d1"
  shows "(\<Sum>ia = 0..<d1.
        \<Sum>j = 0..<d2.
           Matrix.vec d0
            (\<lambda>j. if partial_state.encode2 dims0 vars1' j = partial_state.encode2 dims0 vars1' i
                 then M $$ (partial_state.encode1 dims0 vars1' i, partial_state.encode1 dims0 vars1' j) else 0) $
           pencode12 (ia, j) *  V $ (pencode12(ia,j))) =
    (\<Sum>ia = 0..<d1. M $$ (partial_state.encode1 dims0 vars1' i, ia) *  
                    (V::('a::field) vec) $ (pencode12(ia,partial_state.encode2 dims0 vars1' i)))"
proof-
  let ?MV = "Matrix.vec d0
            (\<lambda>j. if partial_state.encode2 dims0 vars1' j = partial_state.encode2 dims0 vars1' i
                 then M $$ (partial_state.encode1 dims0 vars1' i, partial_state.encode1 dims0 vars1' j) else 0)" and
      ?i = "partial_state.encode2 dims0 vars1' i"

  
  have a0':"partial_state.encode2 dims0 vars1' i < d2"
    using a0
    by (metis d0_def d2_def nths_vars2' partial_state.d2_def 
        partial_state.dims2_def partial_state.encode2_lt state_sig.d_def)
  { fix ia::nat
    let ?f = "\<lambda>j. ?MV $ pencode12(ia,j)* V$(pencode12(ia,j))"
    have "(\<Sum>j = 0..<d2. (?MV $ pencode12 (ia, j)) *  (V $ (pencode12(ia,j)))) = 
              (\<Sum>j = 0..<?i. (?MV $ pencode12 (ia, j)) *  (V $ (pencode12(ia,j)))) + 
                            (?MV $ pencode12 (ia, ?i)) *  (V $ (pencode12(ia,?i))) +
              (\<Sum>j = ?i+1..<d2. (?MV $ pencode12 (ia, j)) *  (V $ (pencode12(ia,j))))"
      using split_sum[of ?i d2 ?f, OF a0'] by auto 
  } 
  moreover { fix ia::nat
    assume a0:"ia <d1"
    have p0:"\<forall>j. 0 \<le> j \<and> j< ?i \<longrightarrow> partial_state.encode2 dims0 vars1' (pencode12(ia,j))\<noteq> ?i" 
      unfolding pencode12_def using a0' a0 partial_state.encode12_inv2 
      by (simp add: d1_def d2_def nths_vars1' nths_vars2' partial_state.d1_def 
           partial_state.d2_def partial_state.dims1_def partial_state.dims2_def)
    then have p0:"\<forall>j. 0 \<le> j \<and> j< ?i \<longrightarrow> ?MV $ pencode12 (ia, j) * V $ pencode12 (ia, j) = 0"
    proof-
      { fix j
        assume a00:"0\<le>j \<and> j < ?i"
        then have "partial_state.encode2 dims0 vars1' (pencode12 (ia, j)) \<noteq> 
                   partial_state.encode2 dims0 vars1' i" using p0 by auto
        moreover have "pencode12 (ia, j) < d0" using a0 a0' a00 apply auto
          using d0_def d1_def d2_def nths_vars1' partial_state.d1_def partial_state.d2_def 
                partial_state.dims1_def partial_state.dims2_def partial_state.encode12_lt 
                partial_state2.nths_vars2' partial_state2_axioms pencode12_def state_sig.d_def by force
        then have "Matrix.vec d0
     (\<lambda>j. if partial_state.encode2 dims0 vars1' j = partial_state.encode2 dims0 vars1' i
          then M $$ (partial_state.encode1 dims0 vars1' i, partial_state.encode1 dims0 vars1' j) else 0) $
    pencode12 (ia, j) = (if partial_state.encode2 dims0 vars1' (pencode12 (ia, j)) = partial_state.encode2 dims0 vars1' i
          then M $$ (partial_state.encode1 dims0 vars1' i, partial_state.encode1 dims0 vars1' (pencode12 (ia, j))) else 0)"
          by auto
        ultimately have "?MV $ pencode12 (ia, j) = 0" by auto 
      }
      then show ?thesis by auto
    qed
    
    have p1:"\<forall>j. ?i+1 \<le> j \<and> j< d2 \<longrightarrow> partial_state.encode2 dims0 vars1' (pencode12(ia,j))\<noteq> ?i"
      unfolding pencode12_def using a0' a0 partial_state.encode12_inv2 
      by (simp add: d1_def d2_def nths_vars1' nths_vars2' partial_state.d1_def 
           partial_state.d2_def partial_state.dims1_def partial_state.dims2_def)
    then have p1:"\<forall>j. ?i+1 \<le> j \<and> j< d2 \<longrightarrow> ?MV $ pencode12 (ia, j) * V $ pencode12 (ia, j) = 0"
    proof-
      { fix j
        assume a00:"?i+1 \<le> j \<and> j< d2"
        then have "partial_state.encode2 dims0 vars1' (pencode12 (ia, j)) \<noteq> 
                   partial_state.encode2 dims0 vars1' i" using p1 by auto
        moreover have "pencode12 (ia, j) < d0" using a0 a0' a00 apply auto
          using d0_def d1_def d2_def nths_vars1' partial_state.d1_def partial_state.d2_def 
                partial_state.dims1_def partial_state.dims2_def partial_state.encode12_lt 
                partial_state2.nths_vars2' partial_state2_axioms pencode12_def state_sig.d_def by force
        then have "Matrix.vec d0
     (\<lambda>j. if partial_state.encode2 dims0 vars1' j = partial_state.encode2 dims0 vars1' i
          then M $$ (partial_state.encode1 dims0 vars1' i, partial_state.encode1 dims0 vars1' j) else 0) $
    pencode12 (ia, j) = (if partial_state.encode2 dims0 vars1' (pencode12 (ia, j)) = partial_state.encode2 dims0 vars1' i
          then M $$ (partial_state.encode1 dims0 vars1' i, partial_state.encode1 dims0 vars1' (pencode12 (ia, j))) else 0)"
          by auto
        ultimately have "?MV $ pencode12 (ia, j) = 0" by auto 
        } thus ?thesis by auto
    qed
    
    have "(\<Sum>j = 0..<?i. (?MV $ pencode12 (ia, j)) *  (V $ (pencode12(ia,j)))) = 0" and
         "(\<Sum>j = ?i+1..<d2. (?MV $ pencode12 (ia, j)) *  (V $ (pencode12(ia,j)))) = 0" and
         "(?MV $ pencode12 (ia, ?i)) *  (V $ (pencode12(ia,?i))) = 
          (M $$ (partial_state.encode1 dims0 vars1' i, ia) *  
                    V $ (pencode12(ia,partial_state.encode2 dims0 vars1' i)))"
        apply (simp add: p0)
      apply (simp add: p1)
      using a0 assms(1) d0_def d1_def nths_vars1' partial_state.d1_def partial_state.dims1_def 
            partial_state.encode12_inv1 partial_state.encode12_inv2 partial_state.encode12_lt 
            partial_state.encode2_lt pencode12_def state_sig.d_def by auto
      
     
  } 
  ultimately show ?thesis
    by (metis (no_types, lifting) add.right_neutral add_0 atLeastLessThan_iff sum.cong)
 
qed
  
lemma mat_extend_M_M_v_scalar_product_i: 
     assumes 
       a0:"i < d0" and
       a1:"dim_vec (V::complex vec) = d0" and a2:"dim_col M = d1" and a3:"dim_row M = d1"
     shows "(ptensor_mat M (1\<^sub>m d2) *\<^sub>v V) $ i = 
             (row M (partial_state.encode1 dims0 vars1'  i)) \<bullet> (trim_vec V (partial_state.encode2 dims0 vars1'  i))"
proof-
  have "(ptensor_mat M (1\<^sub>m d2) *\<^sub>v V) $ i = 
         row (ptensor_mat M (1\<^sub>m d2)) i \<bullet> V"
    using mat_extend_M_M_v_scalar_product_i'
    by (metis a0 a1 ptensor_mat_M_N_row)
  also have "row (ptensor_mat M (1\<^sub>m d2)) i =
            Matrix.vec d0 
        (\<lambda>j. if (partial_state.encode2 dims0 vars1' j) = 
                 (partial_state.encode2 dims0 vars1' i)  then 
                 M $$ (partial_state.encode1 dims0 vars1' i,
                      (partial_state.encode1 dims0 vars1' j))
             else 0)"
    using row_mat_extend_M_v[OF a0] by auto
  also have "Matrix.vec d0 
        (\<lambda>j. if (partial_state.encode2 dims0 vars1' j) = 
                 (partial_state.encode2 dims0 vars1' i)  then 
                 M $$ (partial_state.encode1 dims0 vars1' i,
                      (partial_state.encode1 dims0 vars1' j))
             else 0) \<bullet> V = (\<Sum> ia = 0 ..< dim_vec V. Matrix.vec d0 
        (\<lambda>j. if (partial_state.encode2 dims0 vars1' j) = 
                 (partial_state.encode2 dims0 vars1' i)  then 
                 M $$ (partial_state.encode1 dims0 vars1' i,
                      (partial_state.encode1 dims0 vars1' j))
             else 0) $ ia * V $ ia)" unfolding scalar_prod_def by auto
  also have "\<dots> = (\<Sum>ia = 0 ..< d1. \<Sum>j = 0 ..<d2. 
                  Matrix.vec d0 
                  (\<lambda>j. if (partial_state.encode2 dims0 vars1' j) = 
                       (partial_state.encode2 dims0 vars1' i)  then 
                       M $$ (partial_state.encode1 dims0 vars1' i,
                             (partial_state.encode1 dims0 vars1' j))
                   else 0) $(pencode12(ia,j)) *  V $ (pencode12(ia,j)))"
    using sum_v_as_sum_v1_v2[OF _ a1, of "Matrix.vec d0 
                  (\<lambda>j. if (partial_state.encode2 dims0 vars1' j) = 
                       (partial_state.encode2 dims0 vars1' i)  then 
                       M $$ (partial_state.encode1 dims0 vars1' i,
                             (partial_state.encode1 dims0 vars1' j))
                   else 0)"] a1 by auto
  finally show ?thesis using row_tensor_mat_M_1_V_only_M[OF a0 a2 a3] unfolding trim_vec_def row_def
    by (auto simp add: a2 scalar_prod_def pencode12_def)
qed


lemma vars1_empty_encode1_i_0:assumes a0:"vars1 = {}" and a1:"i<d2" 
  shows "partial_state.encode1 dims0 vars1' i = 0" 
  by (metis One_nat_def a0 a1  card.empty  d2_def 
                dims0_def dims2_def disjoint encode_lt_card(1) 
                finite_v1 finite_v2 less_Suc0 list_dims_def 
                power.simps(1) prod_list_replicate sup_bot_left vars0_def)
 
lemma vars1_empty_encode2_i_i:
  assumes a0:"vars1 = {}" and a1:"i<d2"
  shows "partial_state.encode2 dims0 vars1' i = i" 
  unfolding partial_state.encode2_def using encode
  by (metis Un_commute a0 a1 card_Un_disjoint d2_def dims0_def dims2_def disjoint 
            finite_v1 finite_v2 length_digit_encode length_dims0 
            nths_complement_ind_in_set partial_state.dims2_def 
            prod_list_replicate vars0_def vars1'_def)

lemma vars2_empty_encode1_i_i:
  assumes a0:"vars2 = {}" and a1:"i<d1"
  shows "partial_state.encode1 dims0 vars1' i = i"
  using a0 a1 d1_def dims0_def dims1_def encode finite_v1 partial_state.dims1_def 
        partial_state.encode1_def vars0_def vars1'_def by auto 
 



lemma empty_vars_eq_ptensor_mat:"vars1 = {} \<Longrightarrow> 
      ptensor_mat
     (mat (Suc 0) (Suc 0) (\<lambda>(i, j). if i = 0 \<and> j = 0 then 1 else 0))
     (1\<^sub>m (2 ^ card vars2)) =  (1\<^sub>m (2 ^ card vars2))" 
proof- 
  assume a0:"vars1 = {}"
  have c1:"dim_row (ptensor_mat
     (mat (Suc 0) (Suc 0) (\<lambda>(i, j). if i = 0 \<and> j = 0 then 1 else 0))
     (1\<^sub>m (2 ^ card vars2))) = dim_row (1\<^sub>m (2 ^ card vars2))"
    by (simp add: Q_State.ptensor_mat_dim_row a0 finite_v2)
  moreover have c2:"dim_col (ptensor_mat
     (mat (Suc 0) (Suc 0) (\<lambda>(i, j). if i = 0 \<and> j = 0 then 1 else 0))
     (1\<^sub>m (2 ^ card vars2))) = dim_row (1\<^sub>m (2 ^ card vars2))"
    by (simp add: Q_State.ptensor_mat_dim_col a0 finite_v2)
  moreover have 
          c3:"\<And>i j. i < dim_row (1\<^sub>m (2 ^ card vars2)) \<Longrightarrow>
                 j < dim_col (1\<^sub>m (2 ^ card vars2)) \<Longrightarrow>
                local.ptensor_mat
                  (mat (Suc 0) (Suc 0) (\<lambda>(i, j). if i = 0 \<and> j = 0 then 1 else 0))
                  (1\<^sub>m (2 ^ card vars2)) $$ (i, j) =
           1\<^sub>m (2 ^ card vars2) $$ (i, j)"
  proof-
    let ?m1 = "(mat (Suc 0) (Suc 0) (\<lambda>(i, j). if i = 0 \<and> j = 0 then 1 else 0))" and
        ?m2 = "1\<^sub>m (2 ^ card vars2)"
    fix i j
    assume a00:"i < dim_row (1\<^sub>m (2 ^ card vars2))" and
           a01:"j < dim_col (1\<^sub>m (2 ^ card vars2))"
    have i:"partial_state.encode2 dims0 vars1' i = i"
      using a0 a00 d2_def dims2_def vars1_empty_encode2_i_i by auto 
    have j:"partial_state.encode2 dims0 vars1' j = j"
      using a0 a01 d2_def dims2_def vars1_empty_encode2_i_i by auto
    have ptensor_mat_eval:"ptensor_mat  ?m1 ?m2 $$ (i, j) = 
            ?m1 $$ (partial_state.encode1 dims0 vars1' i, partial_state.encode1 dims0 vars1' j) * 
            ?m2 $$ (partial_state.encode2 dims0 vars1' i, partial_state.encode2 dims0 vars1' j)"
        using a00 a01 c1 ptensor_map_M_N by auto   
    { assume a000: "i=j"
      have "?m1 $$ (partial_state.encode1 dims0 vars1' i, 
                    partial_state.encode1 dims0 vars1' j) = 1"
        using a0 a00 a000 d2_def dims2_def vars1_empty_encode1_i_0 by fastforce
      then have "ptensor_mat ?m1 ?m2 $$ (i, j) =
           ?m2 $$ (partial_state.encode2 dims0 vars1' i, partial_state.encode2 dims0 vars1' j)"
        using mult_1 ptensor_mat_eval by metis       
      then have "ptensor_mat ?m1 ?m2 $$(i,j) = 1\<^sub>m (2 ^ card vars2) $$ (i, j)"
        using a000 i by fastforce
    }
    moreover { assume a00:"i\<noteq>j"
      have f1: "partial_state2 (replicate (card (({}::nat set) \<union> {})) 2) {} {}"
        by (simp add: partial_state2.intro)
      then have "Suc 0 = prod_list (partial_state2.dims1 {})"
        by (simp add: partial_state2.dims1_def)
      then have "Suc 0 = partial_state2.d1 {}"
        using f1 by (simp add: partial_state2.d1_def)
      then have "Suc 0 = d1"
        using a0 by fastforce
      then have "ptensor_mat ?m1 ?m2 $$ (i, j) =
           1\<^sub>m (2 ^ card vars2) $$ (i, j)"
        by (smt (z3) c1 cong_mat d2_def dims2_def index_one_mat(2) 
           less_Suc0 one_mat_def prod.simps(2) prod_list_replicate ptensor_mat_id)
    }
    ultimately show "ptensor_mat
                  (mat (Suc 0) (Suc 0) (\<lambda>(i, j). if i = 0 \<and> j = 0 then 1 else 0))
                  (1\<^sub>m (2 ^ card vars2)) $$ (i, j) =
           1\<^sub>m (2 ^ card vars2) $$ (i, j)"  by auto
      (* by (smt (verit) a0 a1 c2 index_one_mat(2) index_one_mat(3) index_row(1) 
          local.ptensor_mat_dim_col local.ptensor_mat_dim_row) *) 
  qed
  show ?thesis apply rule using c1 c2  by (auto simp add:  c3)
qed

lemma empty_vars_ptensor_mat_1k_1m:"vars1 = {} \<Longrightarrow> 
      ptensor_mat 1\<^sub>0 (2^(card vars1))
     (1\<^sub>m (2 ^ card vars2)) =  (1\<^sub>m (2 ^ card vars2))" 
  unfolding projection1_def
  using empty_vars_eq_ptensor_mat by force

end
(* lemma 
  assumes dims: "v \<in> carrier_vec n" "M \<in> carrier_mat n n"
  shows "((M *\<^sub>v v) \<bullet>c (M *\<^sub>v v)) = (adjoint M *\<^sub>v (M *\<^sub>v v)) \<bullet>c v"
  using adjoint_def_alter
  by (metis adjoint_adjoint adjoint_dim dims(1) dims(2) mult_mat_vec_carrier)


lemma 
  assumes dims: "v \<in> carrier_vec n" "M \<in> carrier_mat n n"
  shows "(adjoint M *\<^sub>v (M *\<^sub>v v)) \<bullet>c v = (v \<bullet>c (adjoint M *\<^sub>v (M *\<^sub>v v)))"
  by (metis (no_types, lifting) adjoint_adjoint adjoint_def_alter adjoint_dim_col 
     carrier_matD(2) carrier_matI dims(1) dims(2) mult_mat_vec_carrier) 
 
   
lemma assumes dims: "v \<in> carrier_vec n" "M \<in> carrier_mat n n"
  shows " ((M *\<^sub>v v) \<bullet>c (M *\<^sub>v v)) = (v \<bullet>c (adjoint M *\<^sub>v (M *\<^sub>v v)))"
  using adjoint_def_alter
  by (metis  dims(1) dims(2) mult_mat_vec_carrier)

lemma assumes dims: "v \<in> carrier_vec n" "M \<in> carrier_mat n n" "hermitian M"
  shows "(v \<bullet>c (adjoint M *\<^sub>v (M *\<^sub>v v))) = (v \<bullet>c (( v))) " sorry
  by (metis adjoint_dim assoc_mult_mat_vec dims(1) dims(2) dims(3) one_mult_mat_vec unitary_simps(1)) 

lemma assumes a0:"M \<in> carrier_mat n n" and a1:"hermitian M"
  shows "adjoint M * M = M"
proof-
  have "adjoint M = M" using a1 a0
    by (simp add: hermitian_def)
  then have "adjoint M * M = M*M"
    by simp
  then have "M*M = M" using a0 a1
qed *)
  

\<comment>\<open>The probability of a meassurement m  as the square norm of the vector product of the 
measurable operator M_m and 
the norm of \<psi>. P(m) = \<parallel>M_m |\<psi>>\<parallel>^2, with \<parallel>\<psi>\<parallel> = square_root (inner_prod \<psi> \<psi>) 
and inner_prod \<psi> \<phi> = scalar_prod \<psi> (conjugate \<phi>). 
Hence  \<parallel>M_m |\<psi>>\<parallel>^2 = inner_prod (M_m |\<psi>>) (M_m |\<psi>>) and 
inner_prod (M_m |\<psi>>) (M_m |\<psi>>) = inner_prod |\<psi>> (adjoint M_m *v  M_m *v |\<psi>> 
because the sum of all the observables M_i = I_H we have that (adjoint M_m) *  M_m = M_m and
P(m) = inner_prod |\<psi>> ( M_m * |\<psi>> .

The resulting vector |\<psi>_m> = M_m |\<psi>> \ square_root P(m) == M_m |\<psi>> / \<parallel>M_m |\<psi>>\<parallel>, 
that is the vector normalized

let assume that the vector to measure, \<psi> is not normalized. To have a consistent measurement,
    we work over the normalized vector \<psi>' = \<psi>\ \<parallel>\<psi> \<parallel>. 
Then \<parallel>M_m |\<psi>'>\<parallel>^2 = \<parallel>(M_m *v 1 / \<parallel>\<psi> \<parallel>*\<psi>)\<parallel>^2 = \<parallel>(M_m *v \<psi>)\<parallel>^2 / \<parallel>\<psi> \<parallel>^2
and M_m |\<psi> / \<parallel>\<psi> \<parallel>> = 1 / \<parallel>\<psi> \<parallel> * M_m |\<psi>> and 
1/\<parallel>\<psi> \<parallel> * M_m |\<psi>\ > / square_root P(m) == 
1/\<parallel>\<psi> \<parallel> * M_m |\<psi>\ > / square_root (\<parallel>(M_m *v \<psi>)\<parallel>^2  / \<parallel>\<psi> \<parallel>^2) ==
1/\<parallel>\<psi> \<parallel> * M_m |\<psi>\ > /  (\<parallel>(M_m *v \<psi>)\<parallel> / \<parallel>\<psi> \<parallel>) =  M_m |\<psi>\ > / (\<parallel>(M_m *v \<psi>)\<parallel>
\<close>



definition measure_vars::"nat \<Rightarrow>  nat set \<Rightarrow>  QStateM  \<Rightarrow> (real \<times>  QStateM)"
  where "measure_vars k  q Q \<equiv>
   let sep_vars = \<Union>((QStateM_map Q) ` q) in
   let Q' = matrix_sep q Q (1\<^sub>k (2^(card sep_vars))) in
   let \<delta>k =  Re ((vec_norm Q')^2) in
     (\<delta>k,  QStateM(QStateM_map Q, QState(QStateM_vars Q, list_of_vec ((1 / sqrt \<delta>k) \<cdot>\<^sub>v Q'))))"

lemma matrix_sep_empty_sep_id:"matrix_sep {} Q (1\<^sub>0 (2^(card {}))) = QStateM_vector Q"
proof-
  let ?sep_vars = "\<Union> ((QStateM_map Q) ` {})"
  let ?var_d = "QStateM_vars Q"  
  let ?var_r = "?var_d - ?sep_vars" 
  let ?v = "QStateM_vector Q"    
  let ?M = "1\<^sub>0 (2^(card ?sep_vars))"
  let ?m = "ptensor_mat ?sep_vars ?var_r
                               (?M::complex mat) (1\<^sub>m (2^(card ?var_r)))"
  let ?r = "?m *\<^sub>v ?v"

  interpret ps2:partial_state2 "list_dims (QStateM_vars Q)" "{}" "QStateM_vars Q" 
    apply standard unfolding list_dims_def 
    by (auto simp add: QStateM_vars.rep_eq QState_rel2')
  have f1:"ptensor_mat {} (QStateM_vars Q) (1\<^sub>0 (Suc 0)) (1\<^sub>m (2 ^ card (QStateM_vars Q))) = 
        (1\<^sub>m (2 ^ card (QStateM_vars Q)))"
    using ps2.empty_vars_ptensor_mat_1k_1m by auto
  have " 1\<^sub>m (2 ^ card (QStateM_vars Q)) *\<^sub>v QStateM_vector Q = QStateM_vector Q"
    by (metis QStateM_list_dim carrier_vecI one_mult_mat_vec vec_of_list_QStateM_list)
  then show ?thesis unfolding matrix_sep_def Let_def
    by (simp add: f1) 
qed




lemma matrix_sep_empty_sep:"matrix_sep {} Q 1\<^sub>0 2 ^ card (\<Union> (QStateM_map Q ` {})) = QStateM_vector Q"
  using matrix_sep_empty_sep_id by auto

lemma measure_vars_zero:
  shows "measure_vars 0 {} Q = (1,Q)"
proof-
  let ?sep_vars = " \<Union>((QStateM_map Q) ` {}) "
  let ?Q' = "matrix_sep {} Q (1\<^sub>0 (2^(card ?sep_vars)))"
  
  have f1:"1 / complex_of_real (sqrt (Re ((vec_norm (QStateM_vector Q))\<^sup>2))) \<cdot>\<^sub>v
          QStateM_vector Q = QStateM_vector Q "
    by (simp add: QStateM_vector.rep_eq QState_rel3')
  have "?Q' = QStateM_vector Q"
    using matrix_sep_empty_sep by blast
  then show ?thesis unfolding measure_vars_def Let_def apply auto  
     apply (simp add: QStateM_vector.rep_eq QState_rel3')
    using f1 idem_QState1 list_of_vec_QStateM_vec by fastforce
qed
  

(* definition measure_vars::"nat \<Rightarrow>  nat set \<Rightarrow>  QStateM  \<Rightarrow> (real \<times>  QStateM)"
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
       (\<delta>k, QStateM (QStateM_map q, QState(QStateM_vars q, list_of_vec (unit_vec (2^(card sep_vars)) k))))
     else (\<delta>k, (1 / sqrt (\<delta>k)) \<cdot>\<^sub>Q Q')" *)

(* lemma measure_vars'_neq:"QStateM_vars Q \<noteq> \<Union>((QStateM_map Q) ` q) \<Longrightarrow> 
      measure_vars' k q Q = measure_vars k q Q"
  unfolding measure_vars'_def measure_vars_def Let_def by auto *)



lemma eq_QState_dest: "vs \<noteq> {} \<Longrightarrow>
       QState_wf (vs, v) \<Longrightarrow> 
       QState(vs, v) = QState(vs', v') \<Longrightarrow> 
       vs = vs' \<and> v = v'" 
   apply transfer'
  by (metis Pair_inject prod.collapse)



lemma measure_vars_dest:
  assumes 
       a0:"\<delta>k = Re ((vec_norm (matrix_sep q Q (1\<^sub>i (2^(card sep_vars)))))^2)" and
       a1:"Q' = matrix_sep q Q (1\<^sub>i (2^(card sep_vars)))" and
       a2:"sep_vars = \<Union>((QStateM_map Q) ` q)"
     shows "measure_vars i q Q = (\<delta>k,  QStateM(QStateM_map Q, QState(QStateM_vars Q, list_of_vec ((1 / sqrt \<delta>k) \<cdot>\<^sub>v Q'))))"
  using a0 a1 a2
  unfolding measure_vars_def Let_def by auto


(* lemma measure_vars_dest':
  assumes 
       a0:"n = Re ((vec_norm (Q_v))^2 div (vec_norm (QStateM_vector Q))^2)" and
       a0':"Q_v = matrix_sep q Q (1\<^sub>i (2^(card sep_vars)))" and
       a1:"Q' = matrix_sep_QStateM q Q (1\<^sub>i (2^(card sep_vars)))" and
       a2:"sep_vars = \<Union>((QStateM_map Q) ` q)"
     shows "measure_vars i q Q = (n, (1 / vec_norm (Q_v)) \<cdot>\<^sub>Q QStateM(QStateM_map Q, QState(QStateM_vars Q,list_of_vec q_v )))"
  using a0 a1 a2
  unfolding measure_vars_def Let_def  by auto  *)

(* lemma measure_vars'_dest:  
  assumes a0:"QStateM_vars Q = \<Union>((QStateM_map Q) ` q)" and 
          a1:"n = Re ((vec_norm ((matrix_sep_var q Q 1\<^sub>i (2 ^ card (\<Union> (QStateM_map Q ` q))))))\<^sup>2 /
             (vec_norm (QStateM_vector Q))\<^sup>2)"
  shows "measure_vars' i q Q = 
       (n, QStateM (QStateM_map Q, QState(QStateM_vars Q, 
           list_of_vec (unit_vec (2^(card (\<Union> (QStateM_map Q ` q)))) i))))"  
  using a0 a1
  unfolding measure_vars'_def Let_def by auto *)

lemma matrix_sep_var_not_zero:
  assumes a0:"\<delta>k = Re ((vec_norm ((matrix_sep q Q 1\<^sub>i (2 ^ card (\<Union> (QStateM_map Q ` q))))))\<^sup>2)" and
          a1:"\<delta>k > 0"
  shows "(matrix_sep q Q 1\<^sub>i (2 ^ card (\<Union> (QStateM_map Q ` q)))) \<noteq> 
         0\<^sub>v (dim_vec (matrix_sep q Q 1\<^sub>i (2 ^ card (\<Union> (QStateM_map Q ` q)))))"
proof-
  have "vec_norm (matrix_sep q Q 1\<^sub>i (2 ^ card (\<Union> (QStateM_map Q ` q)))) \<noteq> 0"
    using a0 a1 by auto  
  then show ?thesis using vec_norm_zero
    by (metis  zero_carrier_vec)
qed




lemma matrix_sep_var_norm_1:
assumes a0:"\<delta>k = Re ((vec_norm ((matrix_sep q Q 1\<^sub>i (2 ^ card (\<Union> (QStateM_map Q ` q))))))\<^sup>2)" and
          a1:"\<delta>k > 0" 
        shows "vec_norm (1/(sqrt \<delta>k) \<cdot>\<^sub>v matrix_sep q Q 1\<^sub>i (2 ^ card (\<Union> (QStateM_map Q ` q)))) = 1"
proof-
  let ?v = "matrix_sep q Q 1\<^sub>i (2 ^ card (\<Union> (QStateM_map Q ` q)))"
  have "sqrt \<delta>k > 0" using a1 by auto
  moreover have "sqrt \<delta>k = vec_norm ?v"  
    using a0 apply auto
    by (metis conjugate_scalar_prod_Im conjugate_scalar_prod_Re csqrt_of_real_nonneg power2_csqrt vec_norm_def)
  moreover have "1/(sqrt \<delta>k) \<cdot>\<^sub>v ?v = 
       1/(vec_norm ?v) \<cdot>\<^sub>v ?v " using calculation by auto
  moreover have "1/(vec_norm ?v) \<cdot>\<^sub>v ?v\<noteq> 0\<^sub>v (2 ^ card (\<Union> (QStateM_map Q ` q)))" 
    using calculation matrix_sep_var_not_zero[OF a0 a1] apply auto
    by (metis (no_types, opaque_lifting) index_zero_vec(2) mult_zero_right 
        norm_complex_absolutely_homogenous vec_eq_norm_smult_normalized 
        vec_norm_zero vec_normalize_def zero_carrier_vec)
  ultimately have  "1/(sqrt \<delta>k) \<cdot>\<^sub>v ?v = vec_normalize ?v " unfolding vec_normalize_def
    using a0 a1 matrix_sep_var_not_zero
    by metis 
  then show ?thesis unfolding vec_norm_def using a1 apply auto
    by (metis a0 carrier_vec_dim_vec matrix_sep_var_not_zero normalized_vec_norm one_complex.simps(1))
qed

lemma measure_vars_wf:
  assumes
   a0:"\<delta>k = Re ((vec_norm (matrix_sep q Q (1\<^sub>i (2^(card sep_vars)))))^2)" and
   a1:"Q' = matrix_sep q Q (1\<^sub>i (2^(card sep_vars)))" and
   a2:"sep_vars = \<Union>((QStateM_map Q) ` q)" and a3:"\<delta>k > 0"
 shows "QState_wf (QStateM_vars Q, list_of_vec ((1 / sqrt \<delta>k) \<cdot>\<^sub>v Q')) \<and> 
        QStateM_wf (QStateM_map Q, QState(QStateM_vars Q, list_of_vec ((1 / sqrt \<delta>k) \<cdot>\<^sub>v Q')))"
proof-
  let ?sep_vars = "Q_domain_var q (QStateM_map Q)" 
  let ?var_r = "(QStateM_vars Q) - ?sep_vars"
  let ?m = "1\<^sub>i ((2::nat) ^ card ?sep_vars)"
  let ?v = "matrix_sep q Q ?m"
  let ?n = "Re ((vec_norm ?v)\<^sup>2)"
  let ?n' = "1/sqrt (?n)"
  have \<delta>:"\<delta>k = ?n" using a2 a0
    using Q_domain_var_def by presburger
  
  note norm_res=matrix_sep_var_norm_1[OF \<delta>[simplified Q_domain_var_def] a3] 
  have "(?n, QStateM(QStateM_map Q, QState (QStateM_vars Q, list_of_vec(?n'\<cdot>\<^sub>v ?v)))) = measure_vars i q Q"
    using measure_vars_dest Q_domain_var_def by presburger
  have "length (list_of_vec(?n'\<cdot>\<^sub>v ?v)) = 2^card (QStateM_vars Q)"
      using matrix_sep_eq_len[of ?m Q q] QStateM_list_dim vec_of_list_QStateM_list 
      unfolding Q_domain_var_def projection1_def by auto

  moreover have "finite((QStateM_vars Q))"
    by (simp add: QStateM_vars.rep_eq QState_rel2')
  moreover have "vec_norm (vec_of_list (list_of_vec(?n'\<cdot>\<^sub>v ?v))) = 1"
    by (metis Q_domain_var_def \<delta> norm_res vec_list) 
  ultimately 
  have QState_wf_Q:"QState_wf (QStateM_vars Q, list_of_vec(?n'\<cdot>\<^sub>v ?v))"
    unfolding QState_wf_def  by auto
    
  moreover have f1:"QStateM_wf (QStateM_map Q, QState(QStateM_vars Q, list_of_vec(?n'\<cdot>\<^sub>v ?v)))"  
    using QState_wf_Q
    using QStateM_rel1 QStateM_rel2 QState_var_idem eq_QStateM_vars by force
 
  ultimately show ?thesis
    by (simp add: Q_domain_var_def \<delta> a1 a2)
qed


lemma measure_vars_dest_QStateM:
  assumes   
   a3':"norm_q' = vec_norm ((matrix_sep q Q 1\<^sub>i (2 ^ card (\<Union> (QStateM_map Q ` q)))))" and
   a3:"\<delta>k = Re (norm_q'\<^sup>2)" and a4:"\<delta>k > 0"
 shows "QStateM_map (snd (measure_vars i q Q)) = QStateM_map Q \<and> 
        QStateM_vars (snd (measure_vars i q Q)) = QStateM_vars Q \<and>
        QStateM_vector (snd (measure_vars i q Q)) = 1 / sqrt \<delta>k \<cdot>\<^sub>v matrix_sep q Q (1\<^sub>i ((2::nat) ^ card (Q_domain_var q (QStateM_map Q))))"

proof-
  have "measure_vars i q Q = (\<delta>k,  QStateM(QStateM_map Q, QState(QStateM_vars Q, list_of_vec ((1 / sqrt \<delta>k) \<cdot>\<^sub>v matrix_sep q Q (1\<^sub>i (2^(card (\<Union> (QStateM_map Q ` q)))))))))"
    using a3 a3' measure_vars_dest by presburger
  moreover have "QState_wf (QStateM_vars Q,list_of_vec ((1 / sqrt \<delta>k) \<cdot>\<^sub>v matrix_sep q Q (1\<^sub>i (2^(card (\<Union> (QStateM_map Q ` q))))))) \<and> 
             QStateM_wf (QStateM_map Q, QState(QStateM_vars Q,list_of_vec ((1 / sqrt \<delta>k) \<cdot>\<^sub>v matrix_sep q Q (1\<^sub>i (2^(card (\<Union> (QStateM_map Q ` q))))))))"
    using measure_vars_wf calculation
    using a3 a3' a4 by presburger 
  ultimately show ?thesis
    by (simp add: QStateM_wf_list QStateM_wf_map QStateM_wf_vars QState_list_idem 
             QState_var_idem Q_domain_var_def vec_list vec_of_list_QStateM_list)                                                                                                             
qed




lemma QStateM_wf_vector:"QStateM_wf (vs, v) \<Longrightarrow> 
                       QStateM_vector (QStateM (vs, v)) = QState_vector v"
  apply transfer' by auto

lemma QState_vector_idem:"QState_wf (vs, list_of_vec v) \<Longrightarrow> 
       QState_vector (QState (vs, list_of_vec v)) =  v"
  apply transfer'
  using vec_list by auto
  

(* lemma measure_vars'_dest_QStateM:
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
*)

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
     shows "ptensor_vec v1 v2 (unit_vec (2 ^ card v1) k) (partial_state2.vector_aij v1 v2 v k) $ i = 0"
proof-
  let ?v1 = "unit_vec (2 ^ card v1) k" and ?v2 = "partial_state2.vector_aij v1 v2 v k"
  interpret ps2:partial_state2 "replicate (card (v1 \<union>  v2)) 2" "v1" "v2"
    apply standard using a2 a1 a0 by auto 
  have "ptensor_vec v1 v2 (unit_vec (2 ^ card v1) k) (partial_state2.vector_aij v1 v2 v k) $ i = 
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
     shows "ptensor_vec v1 v2 (unit_vec (2 ^ card v1) k) (partial_state2.vector_aij v1 v2 v k) $ i = v $ i"
proof-
  let ?v1 = "unit_vec (2 ^ card v1) k" and ?v2 = "partial_state2.vector_aij v1 v2 v k"
  interpret ps2:partial_state2 "replicate (card (v1 \<union>  v2)) 2" "v1" "v2"
    apply standard using a2 a1 a0 by auto
  have "ptensor_vec v1 v2 (unit_vec (2 ^ card v1) k) (partial_state2.vector_aij v1 v2 v k) $ i = 
        (?v1 $ (partial_state.encode1 (list_dims (v1 \<union> v2)) (partial_state2.vars1' v1 v2) i)) * 
        (?v2 $ (partial_state.encode2  (list_dims (v1 \<union> v2)) (partial_state2.vars1' v1 v2) i))"
    unfolding  ps2.ptensor_vec_def  ps2.dims0_def
    by (simp add: a3 i_less_union list_dims_def local.a2 partial_state.tensor_vec_eval  
                  ps2.finite_v1 ps2.finite_v2 ps2.vars0_def state_sig.d_def)
  moreover have "partial_state.encode2 (list_dims (v1 \<union> v2)) ps2.vars1' i < ps2.d2" and "i<ps2.d0"
    apply (simp add: a0 a1 a2 a3 encode_lt_card(2) i_less_union ps2.d2_def ps2.dims2_def)
    using a3 ps2.d0_card_v1_v2 by presburger 
  then have "(?v2 $ (partial_state.encode2 (list_dims (v1 \<union> v2)) (partial_state2.vars1' v1 v2) i)) = 
            v $ ps2.pencode12 (k, partial_state.encode2 (list_dims (v1 \<union> v2)) ps2.vars1' i) " 
    unfolding ps2.vector_aij_def ps2.aijv_def   by auto        
  then have "(?v2 $ (partial_state.encode2 (list_dims (v1 \<union> v2)) (ps2.vars1') i)) = v $ i"  
    unfolding ps2.vector_aij_def ps2.aijv_def using a7 a3 apply auto
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
            ptensor_vec v1 v2 (unit_vec (2 ^ card v1) k) (partial_state2.vector_aij v1 v2 v k) $ i"
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
            ptensor_vec v1 v2 (unit_vec (2^(card v1)) k) (partial_state2.vector_aij v1 v2 v k)"
proof-
  let ?v = "(ptensor_mat v1 v2 ((1\<^sub>k (2^(card v1)))) (1\<^sub>m (2^(card v2)))) *\<^sub>v v"
  let ?w = "ptensor_vec v1 v2 (unit_vec (2^(card v1)) k) (partial_state2.vector_aij v1 v2 v k)"
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
            a \<cdot>\<^sub>v ptensor_vec v1 v2 (unit_vec (2^(card v1)) k) (partial_state2.vector_aij v1 v2 v k)"
  using mat_eq_ptensor_product_vector[OF a0 a1 a2 a5 a8] by auto

lemma v_scalar_mat_product_eq_ptensor_ptensora:
  assumes a0:"finite vars1" and a1:"finite vars2" and a2:"vars1 \<inter> vars2 = {}" and             
       a5:"k < (2^(card vars0))" and a6:"vars1 = vars0 \<union> vars0'" and a6':"vars0 \<inter> vars0' = {}" and
       a9:"v = ptensor_vec vars1 vars2 v1 v2" and a10:"dim_vec v1 = (2^(card vars1))" and a11:"dim_vec v2 = (2^(card vars2))"
     shows "a \<cdot>\<^sub>v ((ptensor_mat vars0 (vars0' \<union> vars2) ((1\<^sub>k (2^(card vars0)))) (1\<^sub>m (2^(card (vars0' \<union> vars2))))) *\<^sub>v v) = 
            a \<cdot>\<^sub>v ptensor_vec vars0 (vars0' \<union> vars2) (unit_vec (2^(card vars0)) k) (partial_state2.vector_aij vars0 (vars0' \<union> vars2) v k)"
proof-
  have "finite vars0"
    using a0 a6 by blast
  moreover have "finite (vars0' \<union> vars1)"
    using a0 a6 by blast
  moreover have "vars0 \<inter> (vars0' \<union> vars2) = {}" using a2 a6 a6' by auto 
  moreover have dim_vec:"dim_vec v = (2^(card vars1)) * (2^(card vars2))"
    by (metis a0 a1 a2 a9 length_replicate nth_replicate partial_state2.d0_card_v1_v2 
          partial_state2.intro partial_state2.ptensor_vec_dim)
  then have "(2::nat)^(card vars1) = 2^(card vars0)*2^(card vars0')"
    by (metis a0 a6 a6' card_Un_disjoint finite_Un power_add)
  then have dim_vec:"dim_vec v = (2^(card vars0)) * (2^(card (vars0' \<union> vars2)))"  
    using a9 a10 a11 a0 a1 a2 a6 dim_vec
    by (simp add: Int_Un_distrib2 card_Un_disjoint power_add) 
  ultimately show ?thesis using v_scalar_mat_product_eq_ptensor
    by (meson a1 a5 finite_Un)
qed 


lemma eq_sum_v_p_encode:
assumes a0:"finite v1" and a1:"finite v2" and a2:"v1 \<inter> v2 = {}" and       
       a3:"dim_vec (v::complex vec) = (2^(card v1)) * (2^(card v2))" 
     shows "(\<Sum>i = 0..< (dim_vec v). (cmod (v $ i))\<^sup>2) = 
           (\<Sum>i = 0 ..<2^(card v1). \<Sum>j = 0 ..<2^(card v2). (cmod (partial_state2.aijv v1 v2 v i j))\<^sup>2)"
proof-
  interpret ps2:
    partial_state2 "replicate (card (v1 \<union> v2)) 2" "v1" "v2"
    apply standard using a2 a1 a0 by auto
  let ?i = "(\<lambda>i. partial_state.encode1 ps2.dims0 (partial_state2.vars1' v1 v2) i)"
  let ?j = "(\<lambda>i. partial_state.encode2 ps2.dims0 (partial_state2.vars1' v1 v2) i)"
  have "\<And>i. i<(dim_vec v) \<Longrightarrow>  
              v $ i = partial_state2.aijv v1 v2 v (?i i) (?j i)"
    unfolding ps2.aijv_def
    by (simp add: a3 card_Un_disjoint partial_state.encode12_inv power_add ps2.dims0_def 
          ps2.disjoint ps2.finite_v1 
        ps2.finite_v2 ps2.pencode12_def ps2.vars0_def state_sig.d_def)
  then have eq:"\<And>i. i<(dim_vec v) \<Longrightarrow>  
              (cmod (v $ i))\<^sup>2 = (cmod (ps2.aijv  v (?i i) (?j i)))\<^sup>2" by auto
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
  finally show ?thesis unfolding ps2.aijv_def by auto
qed

lemma "(cmod a)^2 = (Re a)\<^sup>2 + (Im a)\<^sup>2" using Complex.cmod_power2 by auto

lemma vec_norm_square:
  "(vec_norm v)^2 = complex_of_real (\<Sum>i = 0 ..<dim_vec v. (norm (v$i))^2)"  
proof-
  have "(vec_norm v)^2 = v \<bullet>c v"
    using power2_csqrt vec_norm_def by presburger
  also have " v \<bullet>c v = (\<Sum>i = 0 ..<dim_vec v. (v$i) * (conjugate (v$i)))"
    unfolding scalar_prod_def by auto
  also have "\<dots> =  complex_of_real (\<Sum>i = 0 ..<dim_vec v. (norm (v$i))^2)"
    using complex_norm_square conjugate_complex_def
    by auto
  finally have "(vec_norm v)\<^sup>2 = complex_of_real (\<Sum>i = 0..<dim_vec v. (cmod (v $ i))\<^sup>2)"
    by auto
  then show ?thesis by auto
qed

lemma self_scalar_prod: 
  " v \<bullet>c (v::complex vec) = (\<Sum>i = 0 ..<dim_vec v. (norm (v$i))\<^sup>2)"
proof-
 have " v \<bullet>c v = (\<Sum>i = 0 ..<dim_vec v. (v$i) * (conjugate (v$i)))"
   unfolding scalar_prod_def by auto
  also have "\<dots> =  (\<Sum>i = 0 ..<dim_vec v. (norm (v$i))\<^sup>2)"
    using complex_norm_square conjugate_complex_def
    by auto
  finally show ?thesis by auto
qed

lemma vec_norm_dest: 
  "(vec_norm (v::complex vec)) = sqrt ((\<Sum>i = 0 ..<dim_vec v. (norm (v$i))\<^sup>2))"
  unfolding vec_norm_def using self_scalar_prod
  using Re_complex_of_real conjugate_scalar_prod_Im 
        conjugate_scalar_prod_Re csqrt_of_real_nonneg by presburger 
  
lemma eq_v_aijv_i_j:  
    assumes a0:"finite v1" and a1:"finite v2" and a2:"v1 \<inter> v2 = {}" and
       a8:"dim_vec v = (2^(card v1)) * (2^(card v2))"
     shows "(vec_norm v)^2 = 
            (\<Sum>i = 0 ..<2^(card v1). \<Sum>j = 0 ..<2^(card v2). (norm (partial_state2.aijv v1 v2 v i j))^2)"
proof-
  have " v \<bullet>c v = (\<Sum>i = 0 ..<dim_vec v. (v$i) * (conjugate (v$i)))"
   unfolding scalar_prod_def by auto
  also have "\<dots> =  (\<Sum>i = 0 ..<dim_vec v. (norm (v$i))\<^sup>2)"
    using complex_norm_square conjugate_complex_def
    by auto
  also have " \<dots> = (\<Sum>i = 0 ..<2^(card v1). \<Sum>j = 0 ..<2^(card v2). (norm (partial_state2.aijv v1 v2 v i j))^2)"
    using eq_sum_v_p_encode[OF a0 a1 a2 a8] by auto
  finally have "v \<bullet>c v = (\<Sum>i = 0 ..<2^(card v1). \<Sum>j = 0 ..<2^(card v2). (norm (partial_state2.aijv v1 v2 v i j))^2)"
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
         (\<Sum>j = 0..<2^(card v2). norm (partial_state2.aijv v1 v2 v k j )^2)"
proof-
  interpret ps2:
    partial_state2 "replicate (card (v1 \<union>v2)) 2" "v1" "v2"
    apply standard using a2 a1 a0 by auto
  let ?i = "(\<lambda>i. partial_state.encode1 ps2.dims0 (partial_state2.vars1' v1 v2) i)"
  let ?j = "(\<lambda>i. partial_state.encode2 ps2.dims0 (partial_state2.vars1' v1 v2) i)"
  let ?v = "(((ptensor_mat v1 v2 ((1\<^sub>k (2^(card v1)))) (1\<^sub>m (2^(card v2)))) *\<^sub>v v))"   
  have dim_v:"dim_vec v = dim_vec ?v"
    by (simp add: a8 ps2.d1_def ps2.d2_def ps2.dims1_def ps2.dims2_def ps2.dims_product)
  then have "(vec_norm ?v)^2 = 
            (\<Sum>i = 0 ..<2^(card v1). \<Sum>j = 0 ..<2^(card v2). (norm (ps2.aijv ?v i j))^2)"
    using eq_v_aijv_i_j[OF a0 a1 a2  a8[simplified dim_v]] by fastforce
  also have "(\<Sum>i = 0 ..<2^(card v1). \<Sum>j = 0 ..<2^(card v2). (norm (ps2.aijv ?v i j))^2) = 
             (\<Sum>j = 0..<2^(card v2). norm (ps2.aijv v k j )^2)"
  proof-
    have "\<And>i. i<(dim_vec ?v) \<Longrightarrow>  
                 ?v $ i = ps2.aijv ?v (?i i) (?j i)"
      unfolding ps2.aijv_def
      by (simp add: partial_state.encode12_inv ps2.d0_def ps2.pencode12_def state_sig.d_def)
    let ?f = "\<lambda>i j. (cmod (ps2.aijv ?v i j))\<^sup>2"
    have "(\<Sum>i = 0..<2 ^ card v1.
             \<Sum>j = 0..<2 ^ card v2.
                (cmod (ps2.aijv  ?v i j))\<^sup>2) =
         (\<Sum>j = 0..<2 ^ card v2. (cmod (ps2.aijv ?v k j))\<^sup>2)"
      apply (rule sum_eq_sum_k_j[of k "2 ^ card v1" "2 ^ card v2" ?f])
      using a5 apply fastforce
      unfolding ps2.aijv_def 
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
    also have "(\<Sum>j = 0..<2 ^ card v2. (cmod (ps2.aijv ?v k j))\<^sup>2) = 
               (\<Sum>j = 0..<2 ^ card v2. (cmod (ps2.aijv   v k j))\<^sup>2)"    
    proof-
      have "\<And>j. j < 2^card v2 \<Longrightarrow> (cmod (ps2.aijv ?v k j))\<^sup>2 = (cmod (ps2.aijv v k j))\<^sup>2"      
        unfolding ps2.aijv_def using mat_product_vector_k[OF a0 a1 a2 _ _ _ a8]      
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

lemma  sqrt_sqr_norm_eq_norm:
  assumes a0:"finite v1" and a1:"finite v2" and a2:"v1 \<inter> v2 = {}" and
       a5:"k < (2^(card v1))" and
       a8:"dim_vec v = (2^(card v1)) * (2^(card v2))"
  shows "sqrt (Re(vec_norm (((ptensor_mat v1 v2 ((1\<^sub>k (2^(card v1)))) (1\<^sub>m (2^(card v2)))) *\<^sub>v v)))^2)  = 
         vec_norm (((ptensor_mat v1 v2 ((1\<^sub>k (2^(card v1)))) (1\<^sub>m (2^(card v2)))) *\<^sub>v v))"
  using Im_complex_of_real Re_complex_of_real complex.expand real_sqrt_unique vec_norm_Re_0 by presburger



lemma  vec_norm_ptensor_eq_sum_norm_k':
  assumes a0:"finite v1" and a1:"finite v2" and a2:"v1 \<inter> v2 = {}" and
       a5:"k < (2^(card v1))" and
       a8:"dim_vec v = (2^(card v1)) * (2^(card v2))"
  shows "vec_norm (((ptensor_mat v1 v2 ((1\<^sub>k (2^(card v1)))) (1\<^sub>m (2^(card v2)))) *\<^sub>v v))  = 
         sqrt(\<Sum>j = 0..<2^(card v2). norm (partial_state2.aijv v1 v2 v k j )^2)"
  using vec_norm_ptensor_eq_sum_norm_k[OF a0 a1 a2 a5 a8] 
        sqrt_sqr_norm_eq_norm[OF a0 a1 a2 a5 a8]
  by (metis Re_complex_of_real Re_power_real vec_norm_Re_0) 
  
(* lemma eq_norm: assumes a0:"finite v1" and a1:"finite v2" and a2:"v1 \<inter> v2 = {}" and             
       a5:"k < (2^(card v1))" and
       a8:"dim_vec v = (2^(card v1)) * (2^(card v2))"
     shows "Re ((vec_norm (((ptensor_mat v1 v2 ((1\<^sub>k (2^(card v1)))) (1\<^sub>m (2^(card v2)))) *\<^sub>v v)))^2 
                div (vec_norm v)^2) =
            (\<Sum>j = 0..<2^(card v2). norm (partial_state2.aijv v1 v2 v k j )^2) / 
             (\<Sum>i = 0 ..<2^(card v1). \<Sum>j = 0 ..<2^(card v2). norm (partial_state2.aijv v1 v2 v i j)^2 )"
proof-
  have "(vec_norm (((ptensor_mat v1 v2 ((1\<^sub>k (2^(card v1)))) (1\<^sub>m (2^(card v2)))) *\<^sub>v v)))^2 =
        (\<Sum>j = 0..<2^(card v2). norm (partial_state2.aijv v1 v2 v k j )^2)"
    using vec_norm_ptensor_eq_sum_norm_k[OF a0 a1 a2 a5 a8] by auto
  moreover have "(vec_norm v)^2 = 
                 (\<Sum>i = 0 ..<2^(card v1). 
                    \<Sum>j = 0 ..<2^(card v2). norm (partial_state2.aijv v1 v2 v i j)^2 )"
    using eq_v_aijv_i_j[OF a0 a1 a2 a8] by auto
  ultimately show ?thesis by auto
qed *)

(* lemma norm_v2_empty: assumes a0:"finite v1" and a1:"v2 = {}" and             
       a5:"k < (2^(card v1))" and
       a8:"dim_vec v = (2^(card v1)) * (2^(card v2))"
     shows "Re ((vec_norm (((ptensor_mat v1 v2 ((1\<^sub>k (2^(card v1)))) (1\<^sub>m (2^(card v2)))) *\<^sub>v v)))^2 
                div (vec_norm v)^2) =
            (norm (v$k)^2) / (\<Sum>i = 0 ..<2^(card v1). norm (v$i)^2 )"
proof-
  interpret ps2:
    partial_state2 "replicate (card (v1 \<union>v2)) 2" "v1" "v2"
    apply standard using a1 a1 a0 by auto
  have "Re ((vec_norm (((ptensor_mat v1 v2 ((1\<^sub>k (2^(card v1)))) (1\<^sub>m (2^(card v2)))) *\<^sub>v v)))^2 
                div (vec_norm v)^2) = (\<Sum>j = 0..<2^(card v2). norm (partial_state2.aijv v1 v2 v k j )^2) / 
             (\<Sum>i = 0 ..<2^(card v1). \<Sum>j = 0 ..<2^(card v2). norm (partial_state2.aijv v1 v2 v i j)^2 )"
    using eq_norm[OF a0 _ _ a5 a8] using a1 by auto
  moreover have "\<And>i. i <(2^(card v1)) \<Longrightarrow> partial_state2.aijv v1 v2 v k 0 = v $ k" 
    using a1 unfolding partial_state2.aijv_def
    using ps2.eq_vec_aijv_v2_empty
    using a0 a5 a8 partial_state2.aijv_def ps2.d0_card_v1_v2 by auto
  moreover have "(\<Sum>j = 0..<2^(card v2). norm (partial_state2.aijv v1 v2 v k j )^2) =  norm (v$k)^2"
    using a1 calculation(2)
    by fastforce  
  moreover have "(\<Sum>i = 0 ..<2^(card v1). \<Sum>j = 0 ..<2^(card v2). norm (partial_state2.aijv v1 v2 v i j)^2 )= 
                 (\<Sum>i = 0 ..<2^(card v1). norm (v$i)^2)"
    using a1 
    by (metis (no_types) a0 a8 card.empty eq_sum_v_p_encode 
            finite.emptyI inf_bot_right mult.right_neutral power.simps(1))    
  ultimately show ?thesis by auto
qed *)



(* lemma  sqrt_norm_eq:
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
qed *)


  
lemma  vector_aij_v2_empty:
  assumes a0:"finite v1" and a1:"v2 = {}" and             
       a5:"k < (2^(card v1))" and
       a8:"dim_vec v = (2^(card v1)) * (2^(card v2))" 
     shows "partial_state2.vector_aij v1 v2 v k $ 0 = v$k"
    apply standard using a1 a1 a0 apply auto
  by (metis One_nat_def a5 a8 card.empty finite.emptyI index_vec inf_bot_right length_replicate 
                lessI mult.right_neutral nth_replicate partial_state2.d0_card_v1_v2 
                 partial_state2.d2_def partial_state2.dims2_def 
                 partial_state2.eq_vec_aijv_v2_empty partial_state2.intro 
                partial_state2.vector_aij_def power_0 prod_list_replicate)+
(*
lemma  assumes a0:"finite v1" and a1:"v2 = {}" and             
       a5:"k < (2^(card v1))" and
       a8:"dim_vec v = (2^(card v1)) * (2^(card v2))" and 
       a9:"\<delta>k = Re ((norm (v$k)^2) / (\<Sum>i = 0 ..<2^(card v1). norm (v$i)^2 ))" and 
       a10:"(v'::complex vec) =(((1 / sqrt \<delta>k)\<cdot>\<^sub>v(vector_aij v1 v2 v k))) " 
     shows "v' = ((\<Sum>i = 0 ..<2^(card v1). norm (v$i)^2))" *)

lemma measure_vars_QStateM_map:
  assumes           
     a2:"p>0" and
     a3:"(p,Q') = measure_vars i q Q" 
   shows "QStateM_map Q' = QStateM_map Q"
     using measure_vars_dest_QStateM[OF  _ _ a2]
     by (metis a3 fst_conv measure_vars_dest snd_conv)

(* lemma measure_vars'_QStateM_map:
  assumes           
     a0:"(\<forall>e\<in>q. QStateM_map Q e \<noteq> {})" and a1:"q \<noteq> {}" and a2:"p>0" and
     a3:"(p,Q') = measure_vars' i q Q" and a4:"i<2 ^ card (\<Union> (QStateM_map Q ` q))"
   shows "QStateM_map Q' = QStateM_map Q"
  apply (cases "QStateM_vars Q = \<Union>((QStateM_map Q) ` q)")
  using measure_vars'_dest_QStateM[OF _ a0 a1 a2 a4]
  apply (metis a3 fst_conv measure_vars'_dest snd_conv)
  using measure_vars_dest_QStateM[OF a0 a1 a2]
  by (metis (full_types) a0 a3 local.a1 local.a2 measure_vars'_neq measure_vars_QStateM_map)
*)

(*lemma  measure_vars_eq_length_vector:
  assumes
   a0:"(\<delta>k, QStateM(qm, QState (vars_dom, qnprod))) = measure_vars i q Q" and
    a4:"\<delta>k > 0" and
   a3:"QStateM_vector Q \<noteq> 0\<^sub>v (2^(card (QStateM_vars Q)))"
  shows "length (QStateM_list Q) = length qnprod"
proof-  
  have wf:"QState_wf (vars_dom,qnprod)" and wfm:"QStateM_wf (qm, QState(vars_dom,qnprod))"
    using measure_vars_wf[OF a0 a1 a2 a4] by auto
  then have "QStateM_map (QStateM(qm, QState (vars_dom, qnprod))) = QStateM_map Q"
    using measure_vars_QStateM_map[OF a1 a2 a4 a0]
    by auto
  then have "QStateM_vars Q = QStateM_vars (QStateM(qm, QState (vars_dom, qnprod)))"
    by (metis QStateM_wf eq_QStateM_vars fst_conv)
  thus ?thesis 
    using QStateM_wf_vars QState_rel1' QState_var_idem local.wf wfm unfolding QState_wf_def
    by (metis QStateM_list_dim dim_vec_of_list fst_conv snd_conv)
qed *)

lemma  measure_vars_eq_length_vector:
  assumes
   a0:"(\<delta>k, Q') = measure_vars i q Q" and
    a4:"\<delta>k > 0" 
  shows "length (QStateM_list Q) = length (QStateM_list Q')"
  by (metis QStateM_list_dim a0 a4 dim_vec_of_list eq_QStateMap_vars measure_vars_QStateM_map) 


(*lemma  measure_vars'_eq_length_vector:
  assumes
   a0:"(\<delta>k, QStateM(qm, QState (vars_dom, qnprod))) = measure_vars' i q Q" and
   a1:"\<forall>e \<in> q. QStateM_map Q e \<noteq> {}" and a2:"q \<noteq> {}" and a4:"\<delta>k > 0" and
   a3:"QStateM_vector Q \<noteq> 0\<^sub>v (2^(card (QStateM_vars Q)))" and a5:"i<2 ^ card (\<Union> (QStateM_map Q ` q))"
  shows "length (QStateM_list Q) = length qnprod"
proof-  
  have wf:"QState_wf (vars_dom,qnprod)" and wfm:"QStateM_wf (qm, QState(vars_dom,qnprod))"
    using measure_vars'_wf[OF a0 a1 a2  a5 a4] by auto
  then have "QStateM_map (QStateM(qm, QState (vars_dom, qnprod))) = QStateM_map Q"
    using measure_vars'_QStateM_map[OF a1 a2 a4 a0 a5]
    by auto
  then have "QStateM_vars Q = QStateM_vars (QStateM(qm, QState (vars_dom, qnprod)))"
    by (metis QStateM_wf eq_QStateM_vars fst_conv)
  thus ?thesis 
    using QStateM_wf_vars QState_rel1' QState_var_idem local.wf wfm unfolding QState_wf_def
    by (metis QStateM_list_dim dim_vec_of_list fst_conv snd_conv)
qed
*)

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
  assumes a0:"\<Q>' = QStateM(\<vv>', QState (q'_addr,(v \<sigma>)))" and  a1:"length (v \<sigma>) > 1" and 
          a1':"vec_norm (vec_of_list (v \<sigma>)) = 1" and    
       a2:"\<vv>' = (\<lambda>i. {})(q' := q'_addr)" and 
      a3:"q'_addr \<in> new_q_addr v \<sigma> (QStateM_map \<Q>) " 
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
  assumes a0:"\<Q>' = QStateM(\<vv>', QState (q'_addr,(v \<sigma>)))" and a1':"length (v \<sigma>) > 1" and 
          a1'':"vec_norm (vec_of_list (v \<sigma>)) = 1" and
       a1:"q' \<notin> (dom_q_vars (QStateM_map \<Q>))" and
       a2:"\<vv>' = (\<lambda>i. {})(q' := q'_addr)" and 
      a3:"q'_addr \<in> new_q_addr v \<sigma> (QStateM_map \<Q>) " 
    shows "QStateM_wf (QStateM_map \<Q> + QStateM_map \<Q>',
                  qstate \<Q> + qstate \<Q>')"
proof-  
  have "QState_wf (q'_addr, v \<sigma>) \<and> 
           QStateM_wf ((\<lambda>i. {})(q' := q'_addr), QState (q'_addr, v \<sigma>))  \<and>
           QStateM_map \<Q>' = (\<lambda>i. {})(q' := q'_addr)"
    using allocate_wf1[of  \<Q>' \<vv>' q'_addr v \<sigma>, OF a0  a1' a1'' a2  a3]
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
  assumes a0:"\<Q>' = QStateM(\<vv>', QState (q'_addr,(v \<sigma>)))" and a1':"length (v \<sigma>) > 1" and
       a1:"q' \<notin> (dom_q_vars (QStateM_map \<Q>))" and a1'':"vec_norm (vec_of_list (v \<sigma>)) = 1" and
       a2:"\<vv>' = (\<lambda>i. {})(q' := q'_addr)" and
      a3:"q'_addr \<in> new_q_addr v \<sigma> (QStateM_map \<Q>) " 
    shows "\<Q> ## \<Q>'"
proof-  
  have "QState_wf (q'_addr, v \<sigma>) \<and> 
           QStateM_wf ((\<lambda>i. {})(q' := q'_addr), QState (q'_addr, v \<sigma>))  \<and>
           QStateM_map \<Q>' = (\<lambda>i. {})(q' := q'_addr)"
    using allocate_wf1[of  \<Q>' \<vv>' q'_addr v \<sigma>, OF a0  a1' a1'' a2 a3]
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

(***** lemma sep_eq: 
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
qed **** *)

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
definition
  zero_dic_vec :: "nat \<Rightarrow> complex Matrix.vec" ("|0>\<^sub>_")
  where "|0>\<^sub>n \<equiv> Matrix.vec (2^n) (\<lambda> i. if i=0 then 1 else 0)"

definition Zero::"QStateM \<Rightarrow> bool"
  where "Zero Q \<equiv> QStateM_vector Q $ 0 = 1 \<and> 
                  (\<forall>i <  dim_vec (QStateM_vector Q). i>0 \<longrightarrow> QStateM_vector Q $ i = 0)"

lemma ZeroQ_vector_Zero_dic:"Zero Q \<Longrightarrow> card (QStateM_vars Q) = n \<Longrightarrow> QStateM_vector Q = |0>\<^sub>n"
  unfolding Zero_def zero_dic_vec_def
  apply auto
  using QStateM_list_dim vec_of_list_QStateM_list by auto

lemma ZeroQ_vector_Zero_eq:"card (QStateM_vars Q) = n \<Longrightarrow> Zero Q = (QStateM_vector Q = |0>\<^sub>n)"
  unfolding Zero_def zero_dic_vec_def
  apply auto
  using QStateM_list_dim vec_of_list_QStateM_list by auto

 
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

 (* | QMod:"\<Inter>(QStateM_map \<Q> ` (q \<sigma>)) \<noteq> {} \<Longrightarrow> (q \<sigma>)\<noteq>{} \<Longrightarrow> unitary M \<Longrightarrow>
         \<Q>' = matrix_sep_QStateM (q \<sigma>) \<Q> M \<Longrightarrow>  
         M \<in> carrier_mat (2 ^ card (\<Union> (QStateM_map \<Q> ` (q \<sigma>))))  
                         (2 ^ card (\<Union> (QStateM_map \<Q> ` (q \<sigma>)))) \<Longrightarrow>      
         \<turnstile> \<langle>QMod M q, Normal (\<delta>,\<sigma>, \<Q>)\<rangle> \<Rightarrow> Normal (\<delta>, \<sigma>,  \<Q>')" *)

(* | QMod:"\<forall>e \<in> (q \<sigma>). (QStateM_map \<Q>) e \<noteq> {}  \<Longrightarrow> unitary M \<Longrightarrow>
         \<Q>' = matrix_sep_QStateM (q \<sigma>) \<Q> M \<Longrightarrow>  
         M \<in> carrier_mat (2 ^ card (\<Union> (QStateM_map \<Q> ` (q \<sigma>))))  
                         (2 ^ card (\<Union> (QStateM_map \<Q> ` (q \<sigma>)))) \<Longrightarrow>      
         \<turnstile> \<langle>QMod M q, Normal (\<delta>,\<sigma>, \<Q>)\<rangle> \<Rightarrow> Normal (\<delta>, \<sigma>,  \<Q>')" *)

 | QMod:"\<forall>e \<in> (q \<sigma>). (QStateM_map \<Q>) e \<noteq> {}  \<Longrightarrow> unitary M \<Longrightarrow>
         \<Q>' = matrix_sep_QStateM (q \<sigma>) \<Q> M \<Longrightarrow> 
         M \<in> carrier_mat m m  \<Longrightarrow>      
         \<turnstile> \<langle>QMod M q, Normal (\<delta>,\<sigma>, \<Q>)\<rangle> \<Rightarrow> Normal (\<delta>, \<sigma>,  \<Q>')" 

\<comment>\<open>QMod fails if the set of qubits to be modified is not included in the quantum state\<close>
 | QMod_F:"\<exists>e. e \<in> q \<sigma> \<and> (QStateM_map \<Q>) e = {}  \<or>  \<not> unitary M  \<or> 
         M \<notin> carrier_mat m m  \<Longrightarrow>        
          \<turnstile> \<langle>QMod M q, Normal (\<delta>,\<sigma>, \<Q>)\<rangle> \<Rightarrow> Fault"
(* | QMod_F:"\<Inter>(QStateM_map \<Q> ` (q \<sigma>)) = {} \<or> (q \<sigma>) = {} \<or> \<not> unitary M  \<or> 
         M \<notin> carrier_mat (2 ^ card (\<Union> (QStateM_map \<Q> ` (q \<sigma>))))  
                         (2 ^ card (\<Union> (QStateM_map \<Q> ` (q \<sigma>))))  \<Longrightarrow>        
          \<turnstile> \<langle>QMod M q, Normal (\<delta>,\<sigma>, \<Q>)\<rangle> \<Rightarrow> Fault" *)


\<comment>\<open>QMod fails if the set of qubits to be modified is not included in the quantum state\<close>
(* | QMod_F:"\<Inter>(QStateM_map \<Q> ` (q \<sigma>)) = {} \<or> (q \<sigma>) = {} \<or> \<not> unitary M   \<Longrightarrow>        
          \<turnstile> \<langle>QMod M q, Normal (\<delta>,\<sigma>, \<Q>)\<rangle> \<Rightarrow> Fault"
*)
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
          q'_addr \<in> new_q_addr v \<sigma> (QStateM_map \<Q>)  \<Longrightarrow> vec_norm (vec_of_list (v \<sigma>)) = 1 \<Longrightarrow>
          \<turnstile> \<langle>Alloc q v, Normal (\<delta>,\<sigma>, \<Q>)\<rangle> \<Rightarrow> Normal (\<delta>, \<sigma>', \<Q> + Q_State.QStateM(\<vv>', QState (q'_addr,(v \<sigma>)) ))"
(* | Alloc:"q' \<notin> (dom_q_vars (QStateM_map \<Q>)) \<Longrightarrow> q'_addr \<in> new_q_addr e \<sigma> (QStateM_map \<Q>)  \<Longrightarrow> e \<sigma> \<noteq> 0 \<Longrightarrow>
          \<vv>' = (QStateM_map \<Q>)(q' := q'_addr)  \<Longrightarrow> length (v \<sigma>) = (e \<sigma>) \<Longrightarrow> \<sigma>' = set_value \<sigma> q (from_nat q') \<Longrightarrow>                    
          \<turnstile> \<langle>Alloc q e v, Normal (\<delta>,\<sigma>,\<Q>)\<rangle> \<Rightarrow> Normal (\<delta>, \<sigma>',QStateM(\<vv>',\<qq> + QState (q'_addr,(v \<sigma>)) ))" *)
\<comment>\<open>Alloc will fail if the length of the initial value is not equal to the number of qubits allocated \<close>


 | Alloc_F:"length (v \<sigma>) \<le> 1 \<or>  vec_norm (vec_of_list (v \<sigma>)) \<noteq> 1 \<Longrightarrow>                    
          \<turnstile> \<langle>Alloc q v, Normal (\<delta>,\<sigma>,\<Q>)\<rangle> \<Rightarrow> Fault"

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

 | Dispose: "  \<Q>' ## \<Q>'' \<Longrightarrow> \<Q> =  \<Q>' + \<Q>'' \<Longrightarrow> 
              QStateM_vars \<Q>' \<noteq> {} \<Longrightarrow> Zero \<Q>' \<Longrightarrow>
              QStateM_vars \<Q>' = (Q_domain_var (the (var_set q i \<sigma>)) (QStateM_map \<Q>')) \<Longrightarrow>                                      
              \<forall>e \<in> (the (var_set q i \<sigma>)). (QStateM_map \<Q>') e \<noteq> {} \<Longrightarrow>
             \<turnstile> \<langle>Dispose q i, Normal (\<delta>,\<sigma>,\<Q>)\<rangle> \<Rightarrow> Normal (\<delta>,\<sigma>,  \<Q>'')"

\<comment>\<open>Dispose dispose will fail if it is not possible to find such states \<qq>',  \<qq>''\<close>

(* | Dispose_F: "\<nexists>\<Q>' \<Q>''.(\<Union>((QStateM_map \<Q>'') ` (q \<sigma>))) \<noteq> {} \<and> 
                Q_domain (QStateM_map \<Q>'') = (\<Union>((QStateM_map \<Q>'') ` (q \<sigma>)))  \<and> 
               \<Q> = \<Q>' + \<Q>'' \<and> \<Q>' ## \<Q>'' \<Longrightarrow>
               \<turnstile> \<langle>Dispose q, Normal (\<delta>,\<sigma>,\<Q>)\<rangle> \<Rightarrow> Fault" *)

| Dispose_F: "(\<nexists>\<Q>' \<Q>''.  \<Q> = \<Q>' + \<Q>'' \<and> \<Q>' ## \<Q>'' \<and> QStateM_vars \<Q>' \<noteq> {} \<and> Zero \<Q>' \<and> 
               QStateM_vars \<Q>' = (Q_domain_var (the (var_set q i \<sigma>)) (QStateM_map \<Q>')) \<and>
               (\<forall>e \<in> (the (var_set q i \<sigma>)). (QStateM_map \<Q>') e \<noteq> {})) \<Longrightarrow>
               \<turnstile> \<langle>Dispose q i, Normal (\<delta>,\<sigma>,\<Q>)\<rangle> \<Rightarrow> Fault"

\<comment>\<open>Measure measures the value of the set of qubits given by q \<sigma> and it stores the result in 
  the stack variable v. Similar to allocate, we will require that the construct is well formed
 and that the type of v is a real number\<close>

 (* | Measure: "q (\<sigma>,\<vv>) = (QState_vars \<qq>1) \<Longrightarrow> k \<in> {0.. 2^(card (q (\<sigma>,\<vv>)))} \<Longrightarrow>
            (\<delta>k, (\<vv>',\<qq>')) = measure_vars k (q (\<sigma>,\<vv>)) (\<vv>,\<qq>) \<Longrightarrow> \<qq> =   \<qq>1 +  \<qq>2 \<and> \<qq>1 ## \<qq>2 \<Longrightarrow>            
            \<delta>k > 0 \<Longrightarrow> \<delta>' = \<delta> * \<delta>k \<Longrightarrow> \<sigma>' = set_value \<sigma> v (from_nat k) \<Longrightarrow>
            \<turnstile> \<langle>Measure v q, Normal (\<delta>,\<sigma>,(\<vv>,\<qq>))\<rangle> \<Rightarrow> Normal (\<delta>',\<sigma>',(\<vv>',\<qq>'))"  *)

| Measure: "addr1 = \<Union>((QStateM_map \<Q>) ` (q \<sigma>)) \<Longrightarrow> \<forall>e \<in> (q \<sigma>). (QStateM_map \<Q>) e \<noteq> {} \<Longrightarrow>                      
            k \<in> {0..<2^(card addr1)} \<Longrightarrow>          
            (\<delta>k, \<Q>') = measure_vars k (q \<sigma>) \<Q> \<Longrightarrow>             
            \<delta>k > 0 \<Longrightarrow> \<delta>' = \<delta> * \<delta>k \<Longrightarrow> \<sigma>' = set_value \<sigma> v (from_nat k) \<Longrightarrow>
            \<turnstile> \<langle>Measure v q, Normal (\<delta>,\<sigma>,\<Q>)\<rangle> \<Rightarrow> Normal (\<delta>',\<sigma>', \<Q>')"
\<comment>\<open>Since Measure access to the values of the qubits given by q \<sigma> as QMod, 
  Measure will similarly fail if the set of qubits to be mesured does not
  belong to the set of allocated qubits\<close>

(* | Measure_F: "\<exists>e. e \<in> q \<sigma> \<and> (QStateM_map \<Q>) e = {} \<or> 
              (\<exists>k addr1. k < 2^(card addr1) \<and> addr1 = \<Union>((QStateM_map \<Q>) ` (q \<sigma>)) \<and> (\<delta>k, \<Q>') = measure_vars k (q \<sigma>) \<Q> \<and> \<delta>k \<le> 0) \<Longrightarrow> 
              \<turnstile> \<langle>Measure v q, Normal (\<delta>,\<sigma>,\<Q>)\<rangle> \<Rightarrow> Fault" 
*)

| Measure_F: "\<exists>e. e \<in> q \<sigma> \<and> (QStateM_map \<Q>) e = {}  \<Longrightarrow> 
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
  "\<turnstile>\<langle>Alloc v  e,s\<rangle> \<Rightarrow>  t"
  "\<turnstile>\<langle>Dispose q i,s\<rangle> \<Rightarrow>  t"

thm QExec_elim_cases(10)
(*lemma "s = Normal (\<delta>1, \<sigma>1, Plus T1' T1'') \<Longrightarrow>
       s = Normal (\<delta>, \<sigma>, Plus T' T'') \<Longrightarrow>
       \<delta>1 = \<delta> \<and> \<sigma>1 = \<sigma> \<and> T1' = T' \<and> T1'' = T''"
  by auto*)
      

inductive_cases QExec_Normal_elim_cases [cases set]:
 "\<turnstile>\<langle>c,Fault\<rangle> \<Rightarrow>  t"  
  "\<turnstile>\<langle>Skip,Normal s\<rangle> \<Rightarrow>  t"
  "\<turnstile>\<langle>SMod f,Normal s\<rangle> \<Rightarrow>  t"
  "\<turnstile>\<langle>QMod m q,Normal s\<rangle> \<Rightarrow>  t"
  "\<turnstile>\<langle>Seq c1 c2,Normal s\<rangle> \<Rightarrow>  t"
  "\<turnstile>\<langle>While b c1,Normal s\<rangle> \<Rightarrow>  t"
  "\<turnstile>\<langle>IF b c1 c2,Normal s\<rangle> \<Rightarrow>  t"
  "\<turnstile>\<langle>Measure v q,Normal s\<rangle> \<Rightarrow>  t"
  "\<turnstile>\<langle>Alloc v  e,Normal s\<rangle> \<Rightarrow>  t"
  "\<turnstile>\<langle>Dispose q v,Normal s\<rangle> \<Rightarrow>  t"

inductive_cases QExec_Fault_elim_cases [cases set]:
 "\<turnstile>\<langle>c,Fault\<rangle> \<Rightarrow>  Fault"  
  "\<turnstile>\<langle>Skip,Normal s\<rangle> \<Rightarrow>  Fault"
  "\<turnstile>\<langle>SMod f,Normal s\<rangle> \<Rightarrow>  Fault"
  "\<turnstile>\<langle>QMod m q,Normal s\<rangle> \<Rightarrow>  Fault"
  "\<turnstile>\<langle>Seq c1 c2,Normal s\<rangle> \<Rightarrow>  Fault"
  "\<turnstile>\<langle>While b c1,Normal s\<rangle> \<Rightarrow>  Fault"
  "\<turnstile>\<langle>IF b c1 c2,Normal s\<rangle> \<Rightarrow>  Fault"
  "\<turnstile>\<langle>Measure v q,Normal s\<rangle> \<Rightarrow>  Fault"
  "\<turnstile>\<langle>Alloc v  e,Normal s\<rangle> \<Rightarrow>  Fault"
  "\<turnstile>\<langle>Dispose q v,Normal s\<rangle> \<Rightarrow>  Fault"

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

thm QExec_Normal_elim_cases

lemma exec_Fault_end: assumes exec: "\<turnstile>\<langle>c,s\<rangle> \<Rightarrow>  t" and s: "s=Fault"
  shows "t=Fault"
  using exec s by (induct) auto




end

end


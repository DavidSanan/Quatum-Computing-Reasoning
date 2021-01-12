theory Q_State
imports HOL.Complex vars HOL.Orderings  
          Deep_Learning.Tensor_Matricization Separation_Algebra.Separation_Algebra
          QHLProver.Partial_State Tensor_Permutation HOL.Finite_Set
begin               
\<comment>\<open>Function to obtain the index of variables in the vector\<close>
definition to_nat_set::"'q::linorder set \<Rightarrow> ('q \<Rightarrow> nat)"
  where "to_nat_set s \<equiv> (\<lambda>q. the (find_index q (sorted_list_of_set s)))"
                                       


lemma 
  unique_nat_q:"finite s \<Longrightarrow> q \<in> s \<Longrightarrow> (\<exists>!i. to_nat_set s q = i) \<and> to_nat_set s q < card s"
proof-
  assume a0:"q \<in> s" and a1:"finite s"
  then have h:"q \<in> set (sorted_list_of_set s)" by auto
  moreover have q:"distinct (sorted_list_of_set s)" by auto
  ultimately show "(\<exists>!i. to_nat_set s q = i) \<and> to_nat_set s q < card s"
    unfolding to_nat_set_def using distinct_xs_index_a[OF q h]
    by (metis a1 distinct_card option.sel set_sorted_list_of_set)        
qed

lemma 
  distinct_nat_q:
  assumes a0:"finite s" and a1:"q1 \<in> s" and
     a2:"q2 \<in> s" and "q1\<noteq>q2"
   shows "to_nat_set s q1 \<noteq> to_nat_set s q2"
proof-
  have h:"q1 \<in> set (sorted_list_of_set s)" using a0 a1 by auto
  moreover have q:"distinct (sorted_list_of_set s)" by auto
  ultimately show ?thesis
    unfolding to_nat_set_def using distinct_xs_index_a[OF q h]
      find_index_equiv_less_i
    by (metis a0 a2 assms(4) distinct_xs_index_a option.distinct(1) 
          option.expand set_sorted_list_of_set)    
qed


lemma to_nat_set_lt:
  assumes a0:"q1 < q2" and a1:"q1 \<in> s" and a2:"q2 \<in> s" and
     a3:"finite s"
   shows "to_nat_set s q1 < to_nat_set s q2"
proof-
  let ?sl = "sorted_list_of_set s"
  obtain i where f1:"?sl ! i = q1 \<and> i < length ?sl " 
    using a1 a3
    by (metis in_set_conv_nth set_sorted_list_of_set)
  moreover obtain j where f2:"?sl ! j = q2 \<and> j < length ?sl "
    using a2 a3
    by (metis in_set_conv_nth set_sorted_list_of_set)
  moreover have f3:"\<forall>i j. i \<le> j \<longrightarrow> j < length (?sl) \<longrightarrow> 
                     ?sl ! i \<le> ?sl ! j"
    using sorted_nth_mono sorted_sorted_list_of_set by blast
  ultimately have "i<j"
    using not_less  a0 leD
    by metis
  then show ?thesis unfolding to_nat_set_def
    by (metis a1 a2 a3 distinct_sorted_list_of_set distinct_xs_index_b f1 f2 
        find_index_distinct option.sel set_sorted_list_of_set)
qed

definition set_vars::"'q::linorder set \<Rightarrow> 'q::linorder set \<Rightarrow> nat set"
  where "set_vars vs s \<equiv> to_nat_set vs ` s"

lemma set_vars_empty:
  assumes a0:"s1 \<inter> s2 = {}" and a1:"finite s1" and a2:"finite s2"
  shows "set_vars (s1 \<union> s2) s1 \<inter> set_vars (s1 \<union> s2) s2 = {}"
proof-
  have t:"finite (s1 \<union> s2)" using a1 a2 by auto
  show ?thesis 
    using a0 distinct_nat_q[OF t]
    unfolding set_vars_def by auto
qed


definition list_dims::"'q set \<Rightarrow> nat list"
  where "list_dims qvars \<equiv> replicate (card qvars) 2"

definition dims :: "'a list \<Rightarrow> nat set \<Rightarrow> 'a list" where
  "dims tv vs = nths tv vs"

\<comment>\<open> Lemmas on ptensor_vec \<close>


lemma tensor_neutral:     
      shows "list_of_vec
             (partial_state2.ptensor_vec  {} {} (vec_of_list [1])
               (vec_of_list [1])) = [1::'a::comm_ring_1]"
proof-
  interpret ps2:partial_state2 "[]" "{}" "{}" apply standard by auto
  show ?thesis  unfolding ps2.ptensor_vec_def unfolding  
   ind_in_set_def partial_state.tensor_vec_def  state_sig.d_def 
   partial_state.encode1_def partial_state.dims1_def 
    partial_state.encode2_def partial_state.dims2_def ps2.dims0_def ps2.vars0_def 
    by auto
qed

lemma nths_set_gt_list_length:"nths l (- {0..<length l}) = []"
proof -
  have "nths l (- {0..<length l}) ! 0 \<notin> set (nths l (- {0..<length l}))"
    by (simp add: set_nths)
  then show ?thesis
    by (meson length_greater_0_conv nth_mem)
qed

lemma digit_decode_non_vars:"digit_decode 
    (nths (nths (replicate (card d1) 2) d1) (- ind_in_set (d1 \<union> {}) ` d1))
    (nths (digit_encode (nths (replicate (card d1) 2) d1) i) (- ind_in_set (d1 \<union> {}) ` d1)) = 0"   
proof-
  have "length (nths (nths (replicate (card d1) 2) d1) (- ind_in_set d1 ` d1)) = 0"
    using nths_reencode_eq_comp[of d1 d1 "(replicate (card d1) 2)",simplified] by auto    
  then have 
     "length (nths (digit_encode (nths (replicate (card d1) 2) d1) i) (- ind_in_set d1 ` d1)) = 0"    
    by (simp add: length_digit_encode length_nths')           
  then show ?thesis 
    by (simp add: nths_reencode_eq_comp)
qed

lemma digit_decode_non_vars1:"digit_decode (nths (replicate (card (d1::nat set)) 2) (- ind_in_set (d1 \<union> {}) ` d1))
          (nths (digit_encode (replicate (card d1) 2) i) (- ind_in_set (d1 \<union> {}) ` d1)) = 0"
  by (metis boolean_algebra_cancel.sup0 digit_decode.simps(1) image_empty inf_bot_right 
            length_digit_encode length_replicate nths_complement_ind_in_set nths_empty)

lemma digit_decode_vars:
   "i< (2::nat) ^ card (d1) \<Longrightarrow> finite (d1::nat set)  \<Longrightarrow>
     digit_decode (nths (replicate (card (d1 \<union> {})) 2) (ind_in_set (d1 \<union> {}) ` d1))
     (nths (digit_encode (replicate (card (d1 \<union> {})) 2) i) (ind_in_set (d1 \<union> {}) ` d1))   = i"
  by (metis atLeast0LessThan digit_decode_encode_lt  
            length_digit_encode length_replicate lessThan_iff nths_all 
            prod_list_replicate ind_in_set_id sup_bot.right_neutral)  
                                                             
lemma list_of_neutral:"list_of_vec (vCons 1 vNil) = [1::'a::comm_ring_1]"
  unfolding vCons_def by auto  

lemma list_ptensor_neutral:"list_of_vec
       (partial_state2.ptensor_vec  {} {}
       (vCons (1::'a) vNil) (vCons (1::'a::comm_ring_1) vNil)) =
       [1::'a::comm_ring_1]"
  using tensor_neutral by auto

lemma idempoten_qstate1: 
  assumes 
    a0:"dim_vec (v::('a::comm_ring_1) vec) = (2::nat) ^ card (d1)" and
    a1:"i < dim_vec v" and a2:"finite d1"
  shows 
     "partial_state2.ptensor_vec 
             d1 {} v (vCons 1 vNil) $ i = 
         v $ i"
proof-
  interpret ps2:partial_state2 "(replicate (card d1) (2::nat))" d1 "{}" apply standard
    using a2 by auto
  let  ?d0 = "digit_decode (nths ps2.dims0 (- ps2.vars1'))
                 (nths (digit_encode ps2.dims0 i) (- ps2.vars1'))" 
  have  "digit_decode (nths ps2.dims0 ps2.vars1') (nths (digit_encode ps2.dims0 i) ps2.vars1') = i"
    unfolding ps2.dims0_def ps2.vars0_def ps2.vars1'_def using a0 a1 digit_decode_vars[OF _ a2]  
    by  auto    
  then show ?thesis unfolding ps2.ptensor_vec_def 
      partial_state.tensor_vec_def state_sig.d_def partial_state.encode1_def 
      partial_state.encode2_def partial_state.dims1_def partial_state.dims2_def ps2.dims0_def
                                ps2.vars0_def                         
    using a1 a0   apply clarsimp unfolding ps2.vars0_def ps2.vars1'_def
    using digit_decode_non_vars1
    by auto
qed                         

lemma nths_a_as1:
     "nths (n # replicate m n) {0..(Suc m)} = 
       n # (nths (replicate m n) {0..< (m)})"  
proof (induct m)
  case 0
  then show ?case by auto
next
  case (Suc m)
  then show ?case
    by (simp add: nths_all)
qed 
  
lemma nths_a_as:
     "nths (n # replicate m n) (insert (Suc m) {0..<Suc m}) = 
       n # (nths (replicate m n) (insert m {0..< m}))"  
proof-
  have "nths (n # replicate m n) (insert (Suc m) {0..<Suc m}) = 
        nths (n # replicate m n) {0..<Suc (Suc m)}"
    using set_upt_Suc by presburger
  moreover have "n # (nths (replicate m n) (insert m {0..< m})) = 
                 n # (nths (replicate m n) {0..< Suc m})"
    using set_upt_Suc by presburger
  ultimately show ?thesis using nths_a_as1
    by (simp add: atLeast0LessThan)
qed

lemma prod_list_dims_eq_2_pow_card_a:
   "finite (d1) \<Longrightarrow> d1 \<noteq> {} \<Longrightarrow>    
    prod_list
     (nths (replicate (card d1) (2::nat))
       (insert (card d1) {0..<card  d1})) = 2 ^ card d1"
proof(induct "d1" rule:finite_induct)
  case empty
  then show ?case by auto
next
  case (insert x F)
  { assume a00:"F = {}" 
    then have "insert x F = {x}" using insert by auto
    then have "card  {x} = 1"
      by (simp add: card_1_singleton_iff)
    moreover have "prod_list (nths (replicate 1 (2::nat)) {0,1}) = 2 ^ card  {x}"
      using calculation by auto
    ultimately have ?case
      by (simp add: a00)
  }
  moreover { 
    assume F:"F\<noteq> {}"
    have "x \<notin> F" using insert by auto    
    then have "prod_list (nths (replicate (card F) (2::nat)) (insert (card F) {0..<card F})) = 
               2 ^ card F" using insert(3)[OF F] by auto    
    then have ?case using insert(4)
      by (simp add: nths_all)             
  }
  ultimately show ?case
    by blast
qed

lemma idempoten_qstate2:
  assumes a1:"dim_vec v = (2::nat) ^ card d " and a2:"finite d"
  shows "dim_vec (partial_state2.ptensor_vec  d {} v (vCons 1 vNil)) =
   dim_vec v"
proof-
  interpret ps2:partial_state2 "(replicate (card d) (2::nat))" 
                               d "{}" apply standard using a2 by auto
  show ?thesis unfolding vCons_def        
    using  ps2.ptensor_vec_dim a1  
    unfolding  ps2.d1_def ps2.d2_def ps2.dims1_def ps2.dims2_def ps2.dims_product
    by auto
qed

lemma idempoten_qstate:
  assumes 
    a1:"dim_vec (v::('a::comm_ring_1) vec) = (2::nat) ^ card d" and a2:"finite d"
  shows "partial_state2.ptensor_vec  d {} v (vCons (1) vNil) = v"
  unfolding list_dims_def
  using idempoten_qstate1[OF a1 _ a2]  idempoten_qstate2[OF  a1 a2] by auto


definition mapping::"'q set \<Rightarrow> 'q set \<Rightarrow> nat set \<times> nat set"
  where "mapping s1 s2 \<equiv>({},{})"

typedef (overloaded) ('a::comm_ring_1)
  QState = "{(s,v)| (s::nat set) (v::'a list).                                   
              length v = (2^(card s)) \<and> finite s \<and>
              (s = {} \<longrightarrow> ((v!0) = (1::'a)))}"
  morphisms uQState Abs_QState  
  by (rule exI[where x ="({},[1])"], auto)

setup_lifting type_definition_QState

definition tensor_mat_ord::"'a QState \<Rightarrow> nat set \<Rightarrow> 'a::comm_ring_1 mat \<Rightarrow> 'a QState set"
  where "tensor_mat_ord Q q M \<equiv> {}"

lemma QState_rel1:"length(snd(uQState x)) = 2 ^ card (fst(uQState x))"  
proof -
  have "\<exists>B v. uQState x = (B, v) \<and> length v = (2 ^ card B) \<and> 
              (B = {}) \<longrightarrow> (v ! 0 = 1)"
    using uQState by fastforce
  then show ?thesis using uQState  by (auto simp add:  split_beta)    
qed

lemma QState_rel2:"fst (uQState (x::('a::comm_ring_1) QState )) = {} \<longrightarrow> 
                  (((snd (uQState x)) ! 0) = 1)"
proof -
  have "\<exists>B v. uQState x = (B, v) \<and> length v = (2 ^ card B) \<and> 
              (B = {}) \<longrightarrow> (v ! 0 = 1)"
    using uQState by fastforce
  then show ?thesis using uQState  by (auto simp add:  split_beta)       
qed

lemma QState_rel3:"finite (fst (uQState (x::('a::comm_ring_1) QState )))"
  apply transfer by auto
 
lift_definition QState_vars :: "('a::comm_ring_1) QState \<Rightarrow> nat set" is fst .
lift_definition QState_list :: "('a::comm_ring_1) QState \<Rightarrow> 'a::comm_ring_1 list" is snd .
lift_definition QState_vector::"('a::comm_ring_1) QState \<Rightarrow> 'a::comm_ring_1 vec" is "\<lambda>s. vec_of_list (snd s)" .
lift_definition QState :: "nat set \<times> 'a::comm_ring_1 list \<Rightarrow> 'a QState" is  
  "\<lambda>s. (if fst s = {} \<and> snd s = [1] then (fst s, snd s)
       else (if finite (fst s) \<and> fst s \<noteq> {} \<and> length (snd s) = 2 ^ (card (fst s)) then (fst s, snd s)
       else ({}, [1])))"  by auto

lift_definition Conc :: " 'a QState \<Rightarrow> nat set \<times> 'a::comm_ring_1 vec" is
  "\<lambda>s. (QState_vars s, QState_vector s)" .

lemma uqstate_fst:"fst (uQState a) = QState_vars a" apply transfer' by auto
lemma uqstate_snd:"snd (uQState a) = QState_list a" apply transfer' by auto

lemma QState_rel3':"finite (QState_vars (x::('a::comm_ring_1) QState ))"
  apply transfer by auto

lemma QState_rel1':"length(QState_list x) = 2 ^ card (QState_vars x)"
  using uqstate_fst uqstate_snd  QState_rel1
  by metis 

lemma QState_rel2':"QState_vars x = {} \<Longrightarrow> 
                  (((QState_list x) ! 0) = 1)"
using uqstate_fst uqstate_snd  QState_rel2
  by metis 

lemma QState_empty0:"QState_vars x = {} \<Longrightarrow> 
                     QState_list x = [1]"
  apply (frule QState_rel2'[of x]) apply (insert QState_rel1'[of x])
  apply auto
  by (metis Suc_length_conv list_exhaust_size_eq0 nth_Cons_0)

lemma QState_empty1:"QState_list x = [1] \<Longrightarrow> QState_vars x = {}"
  using QState_rel1' QState_rel3'
  by (metis One_nat_def card_eq_0_iff length_Cons list.size(3) nat_power_eq_Suc_0_iff 
     numeral_eq_one_iff semiring_norm(85)) 

lemma QState_empty:"QState_vars x = {} = ((QState_list x) = [1])"
  using QState_empty1 QState_empty0 by auto


lemma uQState_fst_id_concat:"fst (uQState a) \<union> fst (uQState (QState ({}, [1]))) = fst (uQState a)"
  by (simp add: QState.rep_eq)

lemma QState_vars_id:"QState_vars a \<union> QState_vars (QState ({},[1])) = QState_vars a"
  by (simp add: uqstate_fst[THEN sym] uQState_fst_id_concat)  

lemma fst_uQState_empty: "fst (uQState (QState ({}, [1]))) = {}"
  apply transfer by auto

lemma snd_uQState_empty: "snd (uQState (QState ({}, [1]))) = [1]"
  apply transfer by auto

lemma q_state_eq:
 "a = b = 
 (QState_vars a = QState_vars b \<and> QState_list a = QState_list b)"
  apply transfer by auto


lemma QState_id_fst_empty:
    "a = QState ({}, [1]) \<Longrightarrow>
    fst (uQState a) = {}"
  apply transfer by auto

lemma fst_uQState_empty_snd_1:"a \<noteq> QState ({}, [1]) \<Longrightarrow>
       fst (uQState a) = {} \<Longrightarrow> snd (uQState a) = [1]"
  apply (cases "QState_vars a \<noteq> {} \<and> length (QState_list a) = 2^(card (QState_vars a)) ")
  apply transfer'
   apply (simp add: QState_list.rep_eq QState_rel1 QState_vars.rep_eq)
  apply transfer apply auto using  List.list_eq_iff_nth_eq by fastforce


lemma fst_uQState_not_empty_wf_uQState:"fst (uQState a) \<noteq> {} \<Longrightarrow> 
      length (snd (uQState a)) =  2^(card (fst (uQState a)))"
  apply transfer by auto

lemma QState_refl:"QState (QState_vars a, QState_list a) = a"
  apply transfer apply auto using List.list_eq_iff_nth_eq by fastforce

lemma "QState_vars (QState (QState_vars a, QState_list a)) = QState_vars a"
  by (simp add:  QState_refl)

lemma "QState_list (QState (QState_vars a, QState_list a)) = QState_list a"
  by (simp add:  QState_refl)


definition plus_QState_vector::"('a::comm_ring_1) QState \<Rightarrow> 'a QState \<Rightarrow>nat set \<times> 'a list"
  where "plus_QState_vector q1 q2 \<equiv> 
     let d1 = QState_vars q1; 
         d2 = QState_vars q2; 
         l1 = QState_vector q1; l2 = QState_vector q2 in
          (d1 \<union> d2, list_of_vec(partial_state2.ptensor_vec d1 d2 l1 l2))"

lemma plus_QState_vector_vars:
 "fst (plus_QState_vector q1 q2) = (QState_vars q1) \<union> (QState_vars q2)"
  unfolding plus_QState_vector_def Let_def by auto

lemma plus_QState_vector_vector: 
 "snd (plus_QState_vector q1 q2) = 
  list_of_vec(partial_state2.ptensor_vec (QState_vars q1) (QState_vars q2) (QState_vector q1) (QState_vector q2))"
  unfolding plus_QState_vector_def Let_def by auto

lemma QState_vars_empty:"QState_vars (QState ({}, [1])) = {}"
  by (metis (no_types) QState_id_fst_empty uqstate_fst)
  

lemma plus_QState_vector_a_idem:
  "snd (plus_QState_vector a (QState ({}, [1]))) = QState_list a"  
proof-
  let ?v0 = "QState ({}, [1])::('a) QState"  
  let ?v = "(QState_vars a)"
  let ?v1 = "{}"
  let ?s = "list_dims ?v"
  have card_vars_a:"dim_vec (QState_vector a) = 2^card (QState_vars a)"
    by (simp add: QState_rel1' QState_vector.rep_eq uqstate_snd)
  moreover have finite_vars_a:"finite (QState_vars a)"
    by (simp add: QState_rel3')
  moreover have v1:"?v = (QState_vars a)" and v2:"?v1 = {}"     
    by auto     
  ultimately have 
    tensor_prod:"partial_state2.ptensor_vec   
                                (QState_vars a) {}
                                (QState_vector a) (vCons (1) vNil) = QState_vector a"
    by (fastforce intro:idempoten_qstate)
  then show ?thesis unfolding plus_QState_vector_def Let_def
     using  v1  apply transfer' by (auto simp add: list_vec)          
qed

definition plus_QState:: "('a::comm_ring_1) QState \<Rightarrow> 'a QState \<Rightarrow> 'a QState"
  where "plus_QState q1 q2 \<equiv> 
    let d1 = (QState_vars q1); d2 = (QState_vars q2) in
      if (d1 \<inter> d2 \<noteq> {}) then QState ({},[1])
      else QState (plus_QState_vector q1 q2)"

definition disj_QState::"('a::comm_ring_1) QState \<Rightarrow> 'a QState \<Rightarrow> bool"
  where "disj_QState q1 q2 \<equiv> QState_vars q1 \<inter> QState_vars q2 = {}"

\<comment>\<open>Lemmas on plus_QState_vector\<close>

\<comment>\<open>plus_QState_vector is well formed: 
   the set of vars is finite, the length of the product tensor is 2^ of the cardinality of the vars
   if the set of vars is empty, then the tensor is [1]
\<close>

lemma plus_QState_set_wf:"\<lbrakk>d1 = (QState_vars q1); d2 = (QState_vars q2);
          s = d1 \<union> d2\<rbrakk> \<Longrightarrow> finite s"
  apply transfer by fastforce

lemma plus_QState_vector_set_wf:"finite (fst (plus_QState_vector q1 q2))"
  unfolding plus_QState_vector_def Let_def using plus_QState_set_wf
  by fastforce 

lemma prod_list_card_d_empty_one:" d\<noteq>{} \<Longrightarrow>
       prod_list (nths (replicate (card d) 2) {0..<Suc (card d)}) = 2 ^ card d"
  by (metis atLeast0LessThan length_replicate lessI lessThan_iff 
           less_trans nths_all prod_list_replicate)

lemma card_ind_in_set:
   assumes a0: "(v1::nat set) \<inter> v2 = {}" and
           a1:"finite v1"
   shows "card (ind_in_set (v1 \<union> v2) ` v1) = card v1"
proof-  
  have f1: "finite (ind_in_set (v1 \<union> v2) ` v1)"
    using a1 by blast
  moreover have  "v1 \<subseteq> v1"
    by simp
  ultimately show ?thesis
    by (metis a1 card_atLeastLessThan diff_zero ind_in_set_assoc ind_in_set_id sup_ge1) 
qed

lemma dim_vec_plus_2_pow_s:
  assumes a0:"d1 =  QState_vars q1" and 
          a1:"d2 =  QState_vars q2" and
          a2:"s = d1 \<union> d2" and a3:"l1 = QState_vector q1" and a4:"l2 = QState_vector q2" and
          a5:"ds = list_dims s" and
          a6:"v = partial_state2.ptensor_vec  d1 d2 l1 l2"  and 
          a7:"QState_vars q1 \<inter> QState_vars q2 = {}"
  shows "dim_vec v = (2^(card ((QState_vars q1) \<union> (QState_vars q2))))"
proof-
  have f1:"finite (QState_vars q1)" and f2:"finite (QState_vars q2)"
    using QState_rel3' by auto
  have int_d1_d2:"d1 \<inter> d2 = {}" using a0 a1 a7
    by (smt disjoint_iff_not_equal image_iff ind_in_set_inj subset_eq 
          sup_commute sup_ge1)       
  interpret ps2:partial_state2 ds  d1 d2  apply standard using int_d1_d2 
    using f1 f2 a0 a1 a5 f1 f2 unfolding list_dims_def
    by auto    
 
   have "dim_vec v = prod_list ds"
    using a6  a5 a7 a2 unfolding ps2.ptensor_vec_def partial_state.tensor_vec_def   
      state_sig.d_def 
   partial_state.encode1_def partial_state.dims1_def ps2.dims0_def ps2.vars0_def
    partial_state.encode2_def partial_state.dims2_def list_dims_def
    by auto    
  moreover have "card s = card ((QState_vars q1) \<union> (QState_vars q2))"
    using a0 a1 a2 by blast
  ultimately show ?thesis using a5 unfolding list_dims_def by auto
qed    
  

lemma plus_QState_vector_wf':
  assumes a9:"QState_vars q1 \<inter> QState_vars q2 = {}" and
          a0:"d1 = QState_vars q1" and 
          a1:"d2 = QState_vars q2" and
          a2:"s = d1 \<union> d2" and a3:"l1 = QState_vector q1" and a4:"l2 = QState_vector q2" and
          a5:"ds = list_dims s" and
          a6:"v = partial_state2.ptensor_vec  d1 d2 l1 l2" 
        shows "dim_vec v =  2 ^ card (QState_vars q1 \<union> QState_vars q2)"
  using dim_vec_plus_2_pow_s[OF a0 a1 a2 a3 a4 a5 a6 a9] by auto

lemma plus_QState_vector_wf: assumes a0: "QState_vars q1 \<inter> QState_vars q2 = {}"
  shows "length (snd (plus_QState_vector q1 q2)) =
        2 ^ card (fst (plus_QState_vector q1 q2))"
  unfolding plus_QState_vector_def Let_def using a0
  apply clarsimp  apply (frule plus_QState_vector_wf')  
  by force+

lemma plus_QState_vector_empty_vars_one_wf:
  assumes a0:"fst (plus_QState_vector q1 q2) = {} " 
  shows "snd (plus_QState_vector q1 q2) = [1]"
proof-
  have "QState_vars q1 = {} \<and> QState_vars q2 = {}"
    using a0 unfolding plus_QState_vector_def Let_def by  auto
  moreover have "QState_list q1 = [1] \<and> QState_list q2 = [1]" 
    using QState_empty calculation
    by auto  
  ultimately show ?thesis 
    unfolding plus_QState_vector_def Let_def list_dims_def  
    apply auto apply transfer'
    using tensor_neutral by auto 
qed                                             

 
lemma QState_vars_Plus:"(QState_vars q1 \<inter> QState_vars q2 \<noteq> {} \<longrightarrow>
          QState_vars (plus_QState q1 q2) = {}) \<and>        
       (QState_vars q1 \<inter> QState_vars q2 = {} \<longrightarrow> 
           QState_vars (plus_QState q1 q2) = fst (plus_QState_vector q1 q2))"  
    apply (auto simp add: plus_QState_def ) apply transfer
    apply simp 
   apply transfer' using plus_QState_vector_set_wf plus_QState_vector_wf  
   apply (smt fst_conv)
   apply transfer' using plus_QState_vector_set_wf plus_QState_vector_wf
  by fastforce

lemma QState_list_Plus:"(QState_vars q1 \<inter> QState_vars q2 \<noteq> {} \<longrightarrow>
          QState_list (plus_QState q1 q2) = [1]) \<and>        
       (QState_vars q1 \<inter> QState_vars q2 = {} \<longrightarrow> 
           QState_list (plus_QState q1 q2) = snd (plus_QState_vector q1 q2))"  
    apply (auto simp add: plus_QState_def ) apply transfer
    apply auto
  apply transfer 
  apply auto 
  using plus_QState_vector_set_wf plus_QState_vector_wf plus_QState_vector_empty_vars_one_wf
  by  blast+

lemma neutral_vector_wf:"length [1] = (2^(card {}))" by auto

lemma plus_QState_finite:"finite (QState_vars (plus_QState q1 q2))"  
  by (simp add: QState_rel3')

lemma plus_QState_length:"length (QState_list (plus_QState q1 q2)) =  2^card (QState_vars (plus_QState q1 q2))"  
  by (simp add: QState_rel1')

lemma plus_QState_neutral:
  "QState_vars (plus_QState q1 q2) = {} = 
   ((QState_list (plus_QState q1 q2)) = [1])"  
  using QState_empty by auto

lemma plus_idem:"plus_QState a (QState ({},[1])) = a"
proof-
  {
    assume a00:"QState_vars a = {}"
    have ?thesis
      by (metis (no_types) QState_empty QState_list_Plus QState_refl a00 plus_QState_vector_a_idem) 
  }
  moreover {
    let ?n = "QState ({},[1])"
    assume a00:"QState_vars a \<noteq>{}"
    have "fst (plus_QState_vector a ?n) = QState_vars a"
      by (simp add: QState_vars_empty plus_QState_vector_vars)
    moreover have "snd (plus_QState_vector a ?n) = QState_list a"
      by (simp add: plus_QState_vector_a_idem)
    moreover have "QState_vars (plus_QState a ?n) = fst (plus_QState_vector a ?n) "
      using QState_vars_Plus
      by (metis fst_uQState_empty inf_bot_right uqstate_fst)
    moreover have "QState_list (plus_QState a ?n) = snd (plus_QState_vector a ?n)"            
      by (simp add: QState_list_Plus QState_vars.rep_eq fst_uQState_empty)
    ultimately have ?thesis using q_state_eq by auto
  }
  ultimately show ?thesis by auto 
qed
typedef natsub = "{x. x<(10::nat)}"
  by (meson mem_Collect_eq zero_less_numeral)
  

lemma plus_comm:"disj_QState x y \<Longrightarrow> plus_QState x y = plus_QState y x"
proof-
  assume "disj_QState x y"
  then have disj:"QState_vars x  \<inter> QState_vars y = {}"
    unfolding disj_QState_def by auto
  moreover have f1:"finite (QState_vars x)" and f2:"finite (QState_vars y)"
    by (auto simp add: QState_rel3') 
  then have "QState_vars (plus_QState x y)  = QState_vars (plus_QState y x)"
    by (metis QState_vars_Plus fst_conv inf_commute plus_QState_vector_def sup_commute)
  moreover have "snd (plus_QState_vector x y) = snd (plus_QState_vector y x)"    
    unfolding plus_QState_vector_def Let_def using sup_commute     
    by (auto simp add: ptensor_vec_comm[OF disj f1 f2])    
  then have  "QState_list  (plus_QState x y) = QState_list (plus_QState y x)"
    by (metis QState_list_Plus inf_commute)     
  ultimately show "plus_QState x y = plus_QState y x" using q_state_eq by auto
qed

lemma ind_in_set_union:"(ind_in_set (A \<union> B) ` A) \<union> (ind_in_set (A \<union> B) ` B) = ind_in_set (A \<union> B) ` (A \<union> B)"
  by blast

lemma ind_in_set_int:"A \<inter> B = {} \<Longrightarrow> finite (A::nat set) \<Longrightarrow> finite B \<Longrightarrow>
      ind_in_set (A \<union> B) ` A \<inter> ind_in_set (A \<union> B) ` B = {}"
  by (smt add_cancel_left_right add_diff_cancel_right' card_0_eq card_Un_Int 
          card_atLeastLessThan card_ind_in_set finite_Int finite_UnI 
          finite_imageI ind_in_set_union inf_commute ind_in_set_id sup_commute)

lemma ind_in_set_subset:
  assumes a0:"finite (A::nat set)" and a1:"finite B" 
  shows "ind_in_set A ` A \<subseteq> ind_in_set (A \<union> B) ` (A \<union> B)"
  by (simp add: a0 a1 card_mono ind_in_set_id)



value "ind_in_set {0::nat,1,2,3,4,5} ` {1,2,3}"
value "ind_in_set {1,2,3::nat} ` {1,2,3}"

lemma ind_in_set_absorb:"finite (A::nat set) \<Longrightarrow> finite B \<Longrightarrow> finite C \<Longrightarrow> 
      ((ind_in_set (A \<union> B) ` (A \<union> B)) \<union> (ind_in_set (A \<union> B \<union> C) ` (A \<union> B \<union> C))) = ind_in_set (A \<union> B \<union> C) ` (A \<union> B \<union> C) "
  by (simp add: ind_in_set_subset sup.absorb2)

lemma nths_eq:"v = {0..<card v} \<Longrightarrow>
       nths (list_dims v @ ds'') v = 
       nths (list_dims v) v"
  unfolding list_dims_def
  by (smt Collect_cong add_cancel_left_right append_Nil2 atLeast0LessThan le_add_same_cancel1 
          length_append length_nths length_replicate lessThan_iff less_le_trans 
          list_exhaust_size_eq0 nths_append zero_le)



lemma QState_list_assoc:
   assumes a0:"QState_vars x  \<inter> QState_vars y = {}" and
              a1:"QState_vars y  \<inter> QState_vars z = {}" and
              a2:"QState_vars x  \<inter> QState_vars z = {}" and 
              a3:"QState_vars (plus_QState  x y) \<inter> QState_vars z = {}" and
              a4:"QState_vars x \<inter> QState_vars (plus_QState y z) = {}" 
            shows "QState_list (plus_QState (plus_QState x y) z) = 
                     QState_list (plus_QState x (plus_QState y z))"
proof-
  have fx:"finite (QState_vars x)" and fy:"finite (QState_vars y)" and fz:"finite (QState_vars z)"
    by (auto simp add: QState_rel3')    
    
  have "QState_vars (plus_QState x y) = QState_vars x \<union> QState_vars y" and 
                "QState_vars (plus_QState y z) = QState_vars y \<union> QState_vars z"
    by (auto simp add: QState_vars_Plus a0 a1 plus_QState_vector_vars)
  moreover have "QState_vector (plus_QState x y) = vec_of_list (snd (plus_QState_vector x y))"
    using QState_list_Plus a0
    by (simp add: QState_list_Plus QState_vector.rep_eq uqstate_snd)
  moreover have "QState_vector (plus_QState y z) = vec_of_list (snd (plus_QState_vector y z))"
    using QState_list_Plus a1
    by (simp add: QState_list_Plus QState_vector.rep_eq uqstate_snd)
  moreover have f1:"QState_list (plus_QState (plus_QState x y) z) = snd (plus_QState_vector (plus_QState x y) z)"
    using QState_list_Plus a3
    by blast 
  moreover have f2:" QState_list (plus_QState x (plus_QState y z)) = snd (plus_QState_vector x (plus_QState y z))"
    using QState_list_Plus a4 by blast  
  ultimately show ?thesis unfolding plus_QState_vector_vector vec_list apply auto
    by (metis a0 a3 fx fy fz ptensor_vec_assoc)
qed

lemma plus_assoc:
  assumes a0:"disj_QState x y" and a1:"disj_QState y z" and a2:"disj_QState x z"
  shows "plus_QState (plus_QState x y) z = plus_QState x (plus_QState y z)"
proof-
  have disjxy:"QState_vars x  \<inter> QState_vars y = {}" and 
       disjyz:"QState_vars y  \<inter> QState_vars z = {}" and
       disjxz:"QState_vars x  \<inter> QState_vars z = {}"
    using a0 a1 a2 unfolding disj_QState_def by auto
  have disjxyz1:"QState_vars (plus_QState  x y) \<inter> QState_vars z = {}"
    by (metis QState_vars_Plus Un_subset_iff disjoint_eq_subset_Compl 
              disjxy disjxz disjyz plus_QState_vector_vars)    
  have disjxyz2:"QState_vars x \<inter> QState_vars (plus_QState y z) = {}"
    by (metis QState_vars_Plus disjoint_eq_subset_Compl disjxy disjxz disjyz inf_sup_aci(1) 
              plus_QState_vector_vars sup.bounded_iff)     
  have "QState_vars (plus_QState (plus_QState x y) z) = QState_vars (plus_QState x  (plus_QState y z))"
    unfolding plus_QState_def Let_def using disjxy disjyz disjxz disjxyz1 disjxyz2 apply simp
    by (metis (no_types, lifting) QState_vars_Plus inf_sup_aci(6) plus_QState_def plus_QState_vector_vars)        
  moreover have "QState_vars (plus_QState x y) = QState_vars x \<union> QState_vars y" and 
                "QState_vars (plus_QState y z) = QState_vars y \<union> QState_vars z"
    by (auto simp add: QState_vars_Plus disjxy disjyz plus_QState_vector_vars)  
  have "QState_list (plus_QState (plus_QState x y) z) = QState_list (plus_QState x (plus_QState y z))"
    using QState_list_assoc[OF disjxy disjyz disjxz disjxyz1 disjxyz2] by auto        
  ultimately show ?thesis
    by (simp add: q_state_eq)

qed
  


lemma plus_disj_dist:"\<lbrakk>disj_QState x (plus_QState y z); disj_QState y z\<rbrakk> \<Longrightarrow> disj_QState x y"
  unfolding disj_QState_def  Let_def plus_QState_def  plus_QState_vector_vars apply auto  
  by (metis QState_vars_Plus UnCI disjoint_iff_not_equal plus_QState_def plus_QState_vector_vars)
  
  

lemma plus_dis_dist2:" \<lbrakk>disj_QState x (plus_QState y z); disj_QState y z\<rbrakk> \<Longrightarrow> disj_QState (plus_QState x y) z"
proof-
  assume a0:"disj_QState x (plus_QState y z)" and a1:"disj_QState y z"  
  have "disj_QState x y" using plus_disj_dist[OF a0 a1] by auto
  then show ?thesis  using QState_vars_Plus a0 a1 unfolding disj_QState_def
    by (simp add: QState_vars_Plus inf_sup_distrib1 inf_sup_distrib2 plus_QState_vector_vars)
qed


instantiation QState :: (comm_ring_1) sep_algebra
begin
definition zero_QState: "0 \<equiv> QState ({},[1])"
definition plus_QState: "s1 + s2 \<equiv> plus_QState s1 s2" 
definition sep_disj_QState: "s1 ## s2 \<equiv> disj_QState s1 s2"
instance 
  apply standard
  apply (simp add: zero_QState sep_disj_QState)        
        apply (simp add: QState_vars_empty disj_QState_def)   
       apply (simp add: disj_QState_def inf_commute sep_disj_QState)
      apply (auto simp add: zero_QState  plus_QState Let_def intro:plus_idem)[1]
     apply (auto simp add: sep_disj_QState plus_QState intro:plus_comm)[1]
    apply (auto simp add: sep_disj_QState plus_QState intro:plus_assoc)[1]
   apply (auto simp add: sep_disj_QState plus_QState intro:plus_disj_dist)[1]
  apply (auto simp add: sep_disj_QState plus_QState intro:plus_dis_dist2)[1]
  done
end

end
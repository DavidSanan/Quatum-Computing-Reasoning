theory Q_State
imports QAux.QAux Sep_Prod_Instance "HOL.Relation" (*HOL.Complex vars HOL.Orderings  
          Deep_Learning.Tensor_Matricization Separation_Algebra.Separation_Algebra
          QHLProver.Partial_State  HOL.Finite_Set Sep_Prod_Instance "HOL-Library.Word" *)
begin            
\<comment>\<open>Function to obtain the index of variables in the vector\<close>
(* definition to_nat_set::"'q::linorder set \<Rightarrow> ('q \<Rightarrow> nat)"
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
*)

definition list_dims::"'q set \<Rightarrow> nat list"
  where "list_dims qvars \<equiv> replicate (card qvars) 2"

definition dims :: "'a list \<Rightarrow> nat set \<Rightarrow> 'a list" where
  "dims tv vs = nths tv vs"

\<comment>\<open> Lemmas on ptensor_vec \<close>

lemma tensor_neutral:     
      shows "list_of_vec
             (ptensor_vec  {} {} (vec_of_list [1])
               (vec_of_list [1])) = [1::'a::comm_ring_1]"
proof-
  interpret ps2:partial_state2 "[]" "{}" "{}" apply standard by auto
  show ?thesis  unfolding ps2.ptensor_vec_def unfolding  
   ind_in_set_def partial_state.tensor_vec_def  state_sig.d_def 
   partial_state.encode1_def partial_state.dims1_def 
    partial_state.encode2_def partial_state.dims2_def ps2.dims0_def ps2.vars0_def 
    by auto
qed

lemma ptensor_empty:"(ptensor_vec {} {} q1 q2) $ 0 = q1 $ 0 * q2 $ 0"
proof-
  interpret ps2:partial_state2 "[]" "{}" "{}" apply standard by auto
  show ?thesis  unfolding ps2.ptensor_vec_def unfolding  
    partial_state.tensor_vec_def  state_sig.d_def 
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

(* lemma digit_decode_vars2:
   "i< (2::nat) ^ card (d) \<Longrightarrow> finite (d::nat set)  \<Longrightarrow> d1 \<subseteq> d \<Longrightarrow>
     digit_decode (nths (replicate (card d) 2) (ind_in_set d ` d1))
     (nths (digit_encode (replicate (card (d1 \<union> {})) 2) i) (ind_in_set (d1 \<union> {}) ` d1))   = i"
  by (metis atLeast0LessThan digit_decode_encode_lt  
            length_digit_encode length_replicate lessThan_iff nths_all 
            prod_list_replicate ind_in_set_id sup_bot.right_neutral)  *)
                                                             
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

\<comment>\<open>lemmas on ptensor_mat \<close>

lemma ptensor_mat_dim_row: 
  assumes 
    a0:"finite sep_vars" and a1:"finite var_r" and      
    a2:"sep_vars \<inter> var_r = {}" 
  shows "dim_row (ptensor_mat sep_vars var_r M1 M2) = 
         2^(card sep_vars) * 2^(card var_r)"
proof-
  interpret ps2:partial_state2 "replicate (card ((sep_vars \<union> var_r))) 2" "sep_vars" "var_r"
    apply standard 
    using a0 a1 a2 by auto 
  show ?thesis unfolding ps2.ptensor_mat_def  partial_state.tensor_mat_def 
     state_sig.d_def 
    using ps2.dims_product
    by (simp add: ps2.d0_def ps2.d1_def ps2.d2_def ps2.dims0_def 
                 ps2.dims1_def ps2.dims2_def)
qed

lemma ptensor_mat_dim_col: 
  assumes 
    a0:"finite sep_vars" and a1:"finite var_r" and      
    a2:"sep_vars \<inter> var_r = {}" 
  shows "dim_col (ptensor_mat sep_vars var_r M1 M2) = 
         2^(card sep_vars) * 2^(card var_r)"
proof-
  interpret ps2:partial_state2 "replicate (card ((sep_vars \<union> var_r))) 2" "sep_vars" "var_r"
    apply standard 
    using a0 a1 a2 by auto 
  show ?thesis unfolding ps2.ptensor_mat_def  partial_state.tensor_mat_def 
     state_sig.d_def 
    using ps2.dims_product
    by (simp add: ps2.d0_def ps2.d1_def ps2.d2_def ps2.dims0_def 
                 ps2.dims1_def ps2.dims2_def)
qed

\<comment>\<open>QState definition\<close>

\<comment>\<open>when the length of the vector is 1 the quantum state does not have variables
  in that case the real component of the single vector must be greater than zero
  this is necessary to prove eq_vec_norm_q_empty \<close>



typedef  
  QState = "{(s,v)| (s::nat set) (v::complex list).                                   
              length v = (2^(card s)) \<and> finite s \<and> (\<exists>i<length v. v!i\<noteq>0)}"
  morphisms uQState Abs_QState  
  by (rule exI[where x ="({},[1])"], auto)
  

lemma zero_vec_list:"v \<noteq> 0\<^sub>v (dim_vec v) \<Longrightarrow>
      \<exists>i < length (list_of_vec v). list_of_vec v ! i \<noteq> 0"
  unfolding zero_vec_def by auto

lemma zero_list_vec:"
      \<exists>i < length (list_of_vec v). list_of_vec v ! i \<noteq> 0 \<Longrightarrow> 
      v \<noteq> 0\<^sub>v (dim_vec v)"  
  by (metis index_zero_vec(1) length_list_of_vec list_of_vec_index) 

lemma zero_vec_list_eq:"
      (\<exists>i < length (list_of_vec v). list_of_vec v ! i \<noteq> 0) = 
      (v \<noteq> 0\<^sub>v (dim_vec v))" 
  using zero_vec_list zero_list_vec by auto

setup_lifting type_definition_QState

definition tensor_mat_ord::"QState \<Rightarrow> nat set \<Rightarrow> complex mat \<Rightarrow> QState set"
  where "tensor_mat_ord Q q M \<equiv> {}"

lemma QState_rel1:"length(snd(uQState x)) = 2 ^ card (fst(uQState x))"    
  by (transfer, auto)
(* lemma QState_rel2:"fst (uQState (x::('a::comm_ring_1) QState )) = {} \<longrightarrow> 
                  (((snd (uQState x)) ! 0) = 1)"
  by (transfer, auto) *)

(* lemma QState_rel2:"length(snd(uQState x)) =  1 \<longrightarrow>
                   Im (snd (uQState x) ! 0) = 0 \<and> Re (snd (uQState x) ! 0) > 0"
  apply transfer by auto *)


lemma QState_rel2:"finite (fst (uQState (x:: QState )))"
  apply transfer by auto

lemma QState_rel3:"\<exists>i<length (snd(uQState(x::QState))). 
                     snd(uQState(x::QState))!i \<noteq> 0"  
  by (transfer, auto)

lift_definition QState_vars :: "QState \<Rightarrow> nat set" is fst .
lift_definition QState_list :: "QState \<Rightarrow> complex list" is snd .
lift_definition QState_vector::"QState \<Rightarrow> complex vec" is "\<lambda>s. vec_of_list (snd s)" .

definition QState_wf::"nat set \<times> complex list \<Rightarrow> bool"
  where "QState_wf s \<equiv> 
      length (snd s) = (2^(card (fst s))) \<and> 
      finite (fst s) \<and> (\<exists>i<length (snd s). (snd s)!i\<noteq>0)"

lift_definition QState :: "nat set \<times> complex list \<Rightarrow> QState" is  
  "\<lambda>s. if QState_wf s then (fst s, snd s)
       else ({}, [1])" unfolding QState_wf_def by auto

abbreviation QState_unfold ::"QState \<Rightarrow> nat set \<times> complex list"
  where "QState_unfold x \<equiv> (QState_vars x, QState_list x)"

lemma QState_wf:"QState_wf (QState_unfold x)"  unfolding QState_wf_def  
  by (transfer, auto)

lemma QState_var_idem:"QState_wf (vs, v) \<Longrightarrow> 
       QState_vars (QState (vs, v)) = vs"
  apply transfer'
  by auto
  
lemma QState_list_idem:"QState_wf (vs, v) \<Longrightarrow> 
       QState_list (QState (vs, v)) = v"
  apply transfer'
  by auto

lemma eq_QState_dest: "vs \<noteq> {} \<Longrightarrow> 
       QState_wf (vs, v) \<Longrightarrow> 
       QState(vs, v) = QState(vs', v') \<Longrightarrow> 
       vs = vs' \<and> v = v'" 
   apply transfer'
  by (metis prod.collapse prod.inject)

lift_definition Conc :: " QState \<Rightarrow> nat set \<times> complex vec" is
  "\<lambda>s. (QState_vars s, QState_vector s)" .

definition sca_mult_qstate::"complex \<Rightarrow>  QState \<Rightarrow>  QState"  (infixl "\<cdot>\<^sub>q" 70) 
  where "sca_mult_qstate s qs \<equiv> QState(QState_vars qs, list_of_vec (s \<cdot>\<^sub>v (QState_vector qs)))"


lemma sca_mult_qstate_wf:
  assumes a0:"s \<noteq>0" 
  shows "QState_wf (QState_vars qs, list_of_vec (s \<cdot>\<^sub>v (QState_vector qs)))"  
proof-
  have wf:"QState_wf (QState_unfold qs)"
    using QState_wf by blast 
  { assume "length (QState_list qs) = 1"   
    then obtain v where v:"QState_list qs = [v] \<and> v\<noteq>0"
      using wf using One_nat_def Suc_length_conv  nth_Cons_0 sndI unfolding QState_wf_def      
      by (metis length_0_conv less_one)
    then have f1:"s * v \<noteq>0" using a0 by auto
    then have ?thesis using v
    proof -
      have "snd (uQState qs) = [v]"
        by (metis (no_types) QState_list.rep_eq v)
      then show ?thesis      unfolding QState_wf_def   
        using  f1 local.wf v  apply transfer by auto 
    qed                                             
  }
  moreover { 
    assume "length (QState_list qs) \<noteq> 1"
    then have "dim_vec (vec_of_list (snd (uQState qs))) \<noteq> 1"
        by (metis (full_types) QState_list.rep_eq  dim_vec_of_list)
    then have ?thesis unfolding QState_wf_def
      apply  (simp add: QState_rel1 QState_rel2 QState_vars.rep_eq QState_vector.rep_eq)
      using QState_rel1 QState_rel3 card_0_eq QState_wf assms QState_rel3 
      apply auto
      by (smt (z3) list_of_vec_index list_vec)         
  }
  ultimately show ?thesis by auto
qed



lemma sca_mult_qstate_vars:"s\<noteq>0 \<Longrightarrow>QState_vars (s \<cdot>\<^sub>q qs) = QState_vars qs"
  unfolding sca_mult_qstate_def using sca_mult_qstate_wf
  using QState_var_idem by meson

lemma sca_mult_qstate_quantum: 
  "s\<noteq>0  \<Longrightarrow> 
   QState_vector (s \<cdot>\<^sub>q qs) = s \<cdot>\<^sub>v (QState_vector qs)"
  unfolding sca_mult_qstate_def using sca_mult_qstate_wf[of  s]
  apply transfer 
  by (auto simp add: vec_list)

lemma sca_mult_qstate_assoc: 
  "a1\<noteq>0 \<Longrightarrow> a2\<noteq>0 \<Longrightarrow> 
   a1 * a2 \<cdot>\<^sub>q qs = a1 \<cdot>\<^sub>q (a2 \<cdot>\<^sub>q qs)" 
  by (metis (no_types) sca_mult_qstate_def 
    sca_mult_qstate_quantum sca_mult_qstate_vars smult_smult_assoc)

  (* definition equiv_vectors::"complex vec \<Rightarrow> complex vec \<Rightarrow> bool"
  where "equiv_vectors v1 v2 \<equiv> \<exists>c. v1 = c \<cdot>\<^sub>v v2 \<and> \<bar>c\<bar> = 1"

lemma equiv_comm:"equiv_vectors v1 v2 = equiv_vectors v2 v1"
  unfolding equiv_vectors_def apply auto
  by (metis abs_0 abs_mult mult.commute mult.left_neutral 
   one_smult_vec right_inverse smult_smult_assoc)+

lemma equiv_assoc:"equiv_vectors v1 v2 \<Longrightarrow>
                   equiv_vectors v2 v3 \<Longrightarrow>
                   equiv_vectors v1 v3"
  unfolding equiv_vectors_def apply auto
  by (metis abs_1 abs_minus abs_mult mult_minus1_right smult_smult_assoc)

lemma "\<bar>c::complex\<bar> = 1 = (\<bar>inverse c\<bar> = 1)"
  by auto

lemma sca_mult_qstate_one: "x = 1 \<cdot>\<^sub>q x"
  unfolding sca_mult_qstate_def apply auto
  by (metis QState.rep_eq QState_list.rep_eq QState_vars.rep_eq 
         QState_vector.rep_eq 
      QState_wf list_vec prod.exhaust_sel uQState_inject)

definition equiv_qstate::"QState \<Rightarrow> QState \<Rightarrow> bool"
  where "equiv_qstate k l \<equiv> \<exists>c. k = c \<cdot>\<^sub>q l \<and> \<bar>c\<bar> = 1 "



lemma equiv_qstate_sym:"equiv_qstate k l = equiv_qstate l k"
  unfolding equiv_qstate_def sca_mult_qstate_def
  apply transfer'
  apply auto
  sorry

quotient_type (overloaded) QState_equiv = "QState" /
  equiv_qstate
  morphisms rep QState  
  apply (rule equivpI)
    apply (rule reflpI)
  using sca_mult_qstate_one  
    apply (auto simp add: equiv_qstate_def intro: abs_1)[1]
  using equiv_qstate_sym
  apply (simp add: symp_def)  
  sorry

*)
definition empty_qstate::"QState"  ("|>") 
  where "empty_qstate  \<equiv> QState({}, [1])"


lemma uqstate_fst:"fst (uQState a) = QState_vars a" apply transfer' by auto
lemma uqstate_snd:"snd (uQState a) = QState_list a" apply transfer' by auto


lemma QState_rel2':"\<exists>i<length (QState_list (x::QState)). QState_list (x::QState)!i\<noteq>0"
  by (transfer, auto)

lemma QState_rel2a':"\<exists>i<dim_vec (QState_vector (x::QState)). QState_vector (x::QState)$i\<noteq>0"
  using QState_rel2'
  by (simp add: QState_list.rep_eq QState_vector.rep_eq vec_of_list_index)

lemma QState_rel3a':"QState_vector (x::QState)\<noteq> 0\<^sub>v (dim_vec (QState_vector (x::QState)))"
  using QState_rel2a'
  by (simp add: list_of_vec_index zero_list_vec)

lemma QState_rel3':"finite (QState_vars (x:: QState ))"
  by (transfer, auto)

lemma QState_rel1':"length(QState_list x) = 2 ^ card (QState_vars x)"
  by (transfer, auto)

lemma QState_rel1a':"dim_vec (QState_vector x) = 2 ^ card (QState_vars x)"
  by (transfer, auto)


(* lemma QState_rel2':"QState_vars x = {} \<Longrightarrow> 
                  (((QState_list x) ! 0) = 1)"
  by (transfer, auto) *)

(* lemma QState_empty0:"QState_vars x = {} \<Longrightarrow> 
                     QState_list x = [1]"
  apply (frule QState_rel2'[of x]) apply (insert QState_rel1'[of x])
  apply auto
  by (metis Suc_length_conv list_exhaust_size_eq0 nth_Cons_0) *)

lemma QState_empty1:"QState_list x = [1] \<Longrightarrow> QState_vars x = {}"
  using QState_rel1' QState_rel3'
  by (metis One_nat_def card_eq_0_iff length_Cons list.size(3) nat_power_eq_Suc_0_iff 
     numeral_eq_one_iff semiring_norm(85)) 

(* lemma QState_empty:"QState_vars x = {} = ((QState_list x) = [1])"
  using QState_empty1 QState_empty0 by auto *)


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

(* lemma fst_uQState_empty_snd_1:"a \<noteq> QState ({}, [1]) \<Longrightarrow>
       fst (uQState a) = {} \<Longrightarrow> snd (uQState a) = [1]"
  apply (cases "QState_vars a \<noteq> {} \<and> length (QState_list a) = 2^(card (QState_vars a)) ")
  apply transfer'
   apply (simp add: QState_list.rep_eq QState_rel1 QState_vars.rep_eq)
  apply transfer apply auto using  List.list_eq_iff_nth_eq by fastforce *)


lemma fst_uQState_not_empty_wf_uQState:"fst (uQState a) \<noteq> {} \<Longrightarrow> 
      length (snd (uQState a)) =  2^(card (fst (uQState a)))"
  by (transfer, auto)

lemma QState_refl:"QState (QState_vars a, QState_list a) = a"
  by (transfer, auto simp add: QState_wf_def)

lemma QState_var_qstate:"QState_vars (QState (QState_vars a, QState_list a)) = QState_vars a"
  by (simp add:  QState_refl)

lemma QState_list_qstate:"QState_list (QState (QState_vars a, QState_list a)) = QState_list a"
  by (simp add:  QState_refl)

lemma QState_list_empty:"QState_vars Q = {} \<Longrightarrow> \<exists>v. QState_list Q = [v]"
  using  One_nat_def QState_rel1' Suc_length_conv card.empty 
       power.simps(1)
  by (metis length_0_conv)

lemma QState_list_inv: assumes a0:"QState_vars Q = {}"
  shows "inverse(QState_list Q ! 0) \<cdot>\<^sub>q Q = |>"
  unfolding empty_qstate_def sca_mult_qstate_def using a0 apply transfer' 
  apply auto
  subgoal for b
    apply (subgoal_tac "b ! 0 \<noteq> 0")
     apply (auto simp add: list_of_vec_map vec_of_list_index  QState_wf_def)
    done
  done

definition plus_QState_vector::"QState \<Rightarrow>  QState \<Rightarrow>nat set \<times> complex list"
  where "plus_QState_vector q1 q2 \<equiv> 
     let d1 = QState_vars q1; 
         d2 = QState_vars q2; 
         l1 = QState_vector q1; l2 = QState_vector q2 in
          (d1 \<union> d2, list_of_vec(partial_state2.ptensor_vec d1 d2 l1 l2))"

definition vector_element_12::"QState \<Rightarrow> nat set \<Rightarrow> nat \<times> nat \<Rightarrow> complex"
  where "vector_element_12 v d1 p \<equiv> 
         let d = QState_vars v; 
         d2 = d - d1; 
         l1 = QState_vector v in l1$(partial_state2.pencode12 d1 d2 p)"

lemma vector_element12_equiv:
  assumes a0:"dim_vec v  = 2^(card d)" and a1:"d1 \<subseteq> d" and a2:"finite d" and 
         a3:"i < 2^(card d1)" and a4:"j < 2^(card (d - d1))"
  shows "partial_state2.pencode12 d1 (d - d1) (i,j) < dim_vec v"
proof-
  interpret ps2:partial_state2 "(replicate (card d) (2::nat))" "d1" "(d - d1)" apply standard
    using a2 a1 infinite_super apply auto
    by (simp add: subset_Un_eq)
    
  show ?thesis unfolding  ps2.pencode12_def                                      
    using a1 a0 a2 a3 partial_state.encode12_lt          
     apply auto
    by (metis Diff_partition Un_Diff_cancel a4 partial_state.d1_def 
         partial_state.d2_def partial_state.dims1_def partial_state.dims2_def 
         partial_state2.nths_vars1' partial_state2.nths_vars2' prod_list_replicate 
      ps2.d_def ps2.dims0_def ps2.dims1_def 
         ps2.dims2_def ps2.partial_state2_axioms ps2.vars0_def ps2.vars1'_def) 
qed



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
  let ?v0 = "QState ({}, [1]):: QState"  
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

definition plus_QState:: "QState \<Rightarrow>  QState \<Rightarrow> QState"
  where "plus_QState q1 q2 \<equiv> 
    let d1 = (QState_vars q1); d2 = (QState_vars q2) in
      if (d1 \<inter> d2 \<noteq> {}) then QState ({},[1])
      else QState (plus_QState_vector q1 q2)"

definition disj_QState::"QState \<Rightarrow>  QState \<Rightarrow> bool"
  where "disj_QState q1 q2 \<equiv> QState_vars q1 \<inter> QState_vars q2 = {}"

\<comment>\<open>Lemmas on plus_QState_vector\<close>

\<comment>\<open>plus_QState_vector is well formed: 
   the set of vars is finite, the length of the product tensor is 2^ of the cardinality of the vars
   if the set of vars is empty, then the tensor is [1]
\<close>

lemma plus_QState_set_wf:"\<lbrakk>d1 = (QState_vars q1); d2 = (QState_vars q2);
          s = d1 \<union> d2\<rbrakk> \<Longrightarrow> finite s"
  apply transfer by fastforce

lemma plus_QState_vector_set_finite:"finite (fst (plus_QState_vector q1 q2))"
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
    using f1 f2 a0 a1 a2 a5 f1 f2 unfolding list_dims_def by auto   
 
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

lemma plus_QState_vector_length_card: assumes a0: "QState_vars q1 \<inter> QState_vars q2 = {}"
  shows "length (snd (plus_QState_vector q1 q2)) =
        2 ^ card (fst (plus_QState_vector q1 q2))"
  unfolding plus_QState_vector_def Let_def using a0
  apply clarsimp  apply (frule plus_QState_vector_wf')  
  by force+


lemma plus_QState_vector_wf_empty:
  assumes a0:"QState_vars q1 \<inter> QState_vars q2 = {}" and
          a1:"fst (plus_QState_vector q1 q2) = {}"
        shows "(snd (plus_QState_vector q1 q2)) ! 0 \<noteq> 0"
proof-
  let ?pt = "(ptensor_vec (QState_vars q1) (QState_vars q2) (QState_vector q1) (QState_vector q2))"
  have "QState_vars q1 = {}" and "QState_vars q2 = {}"
    using a1 unfolding plus_QState_vector_def Let_def by auto
  moreover have "QState_vector q1 $ 0 \<noteq> 0" and 
                "QState_vector q2 $ 0 \<noteq> 0"
    using calculation apply auto apply transfer
    apply (metis card.empty fst_conv less_one power_0 snd_conv vec_of_list_index)
      apply transfer
    by (metis card.empty fst_conv less_one power_0 snd_conv vec_of_list_index)  
  ultimately have "?pt$0 \<noteq> 0" 
    using ptensor_empty[of "QState_vector q1" "QState_vector q2"] 
    by simp
  then show ?thesis unfolding plus_QState_vector_def Let_def 
    by (metis snd_conv vec_list vec_of_list_index)                                                     
qed

(* lemma "\<forall>i<length (snd (plus_QState_vector q1 q2)). plus_QState_vector q1 q2" *)
(* lemma plus_QState_vector_empty_vars_one_wf:
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
qed   *)   

lemma plus_QState_vector_wf_pencode_not_zero: 
  assumes a0:"i<length (QState_list q1)" and a1:"QState_list q1 ! i \<noteq> 0" and
              a2:"j <length (QState_list q2)" and a3:"QState_list q2 ! j \<noteq> 0" and 
              a4:"QState_vars q1 \<inter> QState_vars q2 = {}" 
       shows "partial_state2.pencode12 (QState_vars q1) (QState_vars q2) (i,j) < 
                   length (snd (plus_QState_vector q1 q2)) \<and> 
              snd (plus_QState_vector q1 q2) ! 
                (partial_state2.pencode12 (QState_vars q1) (QState_vars q2) (i,j)) \<noteq> 0"
proof-
  interpret ps2:partial_state2 "replicate (card (((QState_vars q1) \<union> (QState_vars q2)))) 2" 
                  "QState_vars q1" "QState_vars q2"
    apply standard using a4 apply auto
    by (auto simp add: QState_rel3')
  have "partial_state2.pencode12 (QState_vars q1) (QState_vars q2) (i,j) < 
                   length (snd (plus_QState_vector q1 q2))"
    by (metis QState_rel1' a0 a2 partial_state.d1_def partial_state.d2_def 
         partial_state.dims1_def partial_state.dims2_def 
        partial_state.encode12_lt plus_QState_vector_vars plus_QState_vector_length_card 
        prod_list_replicate ps2.dims0_def ps2.dims1_def ps2.dims2_def ps2.disjoint 
        ps2.nths_vars1' ps2.nths_vars2' ps2.pencode12_def ps2.vars0_def state_sig.d_def) 
  moreover have "snd (plus_QState_vector q1 q2) ! 
            (partial_state2.pencode12 (QState_vars q1) (QState_vars q2) (i,j)) \<noteq> 0"
    using calculation
    unfolding plus_QState_vector_def Let_def
    using a0 a1 a2 a3 apply auto
    by (metis QState_list.rep_eq QState_rel1' QState_vector.rep_eq 
              mult_eq_0_iff partial_state.d1_def partial_state.d2_def 
              partial_state.dims1_def partial_state.dims2_def 
              partial_state.encode12_inv1 partial_state.encode12_inv2 
              partial_state.tensor_vec_eval partial_state2.dims1_def 
              partial_state2.dims2_def partial_state2.ptensor_vec_def 
              prod_list_replicate ps2.d0_def ps2.d_def ps2.dims0_def 
              ps2.nths_vars1' ps2.nths_vars2' ps2.partial_state2_axioms 
              ps2.pencode12_def ps2.vars0_def vec_of_list_index)
  ultimately show ?thesis by auto 
qed

lemma plus_QState_vector_wf_not_zero:
  assumes a0:"QState_vars q1 \<inter> QState_vars q2 = {}"     
  shows "\<exists>i<2 ^ card (fst (plus_QState_vector q1 q2)).
          snd (plus_QState_vector q1 q2) ! i \<noteq> 0"
proof-
  obtain i j where "i<length (QState_list q1) \<and> QState_list q1 ! i \<noteq> 0" and
       "j <length (QState_list q2) \<and>  QState_list q2 ! j \<noteq> 0"
    by (transfer,auto)+
  then show ?thesis using a0 plus_QState_vector_wf_pencode_not_zero
    by (metis plus_QState_vector_length_card)
    
qed


lemma 
  plus_QState_vector_wf:
  assumes a0:"QState_vars Q1 \<inter> QState_vars Q2 = {} "
  shows "QState_wf (plus_QState_vector Q1 Q2)"
  using a0 unfolding plus_QState_vector_def Let_def QState_wf_def apply auto
  apply (auto simp add: dim_vec_plus_2_pow_s QState_rel3')
  using plus_QState_vector_vars plus_QState_vector_vector plus_QState_vector_wf_not_zero by presburger


lemma QState_vars_Plus:"(QState_vars q1 \<inter> QState_vars q2 \<noteq> {} \<longrightarrow>
          QState_vars (plus_QState q1 q2) = {}) \<and>        
       (QState_vars q1 \<inter> QState_vars q2 = {} \<longrightarrow> 
           QState_vars (plus_QState q1 q2) = fst (plus_QState_vector q1 q2))"  
    apply (auto simp add: plus_QState_def ) apply transfer    
   apply transfer' using plus_QState_vector_set_finite plus_QState_vector_wf
  apply (auto simp add: fstI) 
  apply transfer' using plus_QState_vector_set_finite plus_QState_vector_wf plus_QState_vector_wf_not_zero
  apply (metis (mono_tags, lifting)  prod.exhaust_sel )
  by (simp add: QState.rep_eq QState_vars.rep_eq QState_wf_def 
       plus_QState_vector_wf_empty plus_QState_vector_wf_not_zero) 
  

lemma QState_list_Plus:"(QState_vars q1 \<inter> QState_vars q2 \<noteq> {} \<longrightarrow>
          QState_list (plus_QState q1 q2) = [1]) \<and>        
       (QState_vars q1 \<inter> QState_vars q2 = {} \<longrightarrow> 
           QState_list (plus_QState q1 q2) = snd (plus_QState_vector q1 q2))"  
    apply (auto simp add: plus_QState_def ) apply transfer
    apply (auto simp add:  QState_wf_def)
  apply transfer 
  apply auto 
  using plus_QState_vector_set_finite
  by (simp add: QState_wf_def plus_QState_vector_length_card plus_QState_vector_wf_empty 
                 plus_QState_vector_wf_not_zero)   

lemma neutral_vector_wf:"length [1] = (2^(card {}))" by auto

lemma plus_QState_finite:"finite (QState_vars (plus_QState q1 q2))"  
  by (simp add: QState_rel3')

lemma plus_QState_length:"length (QState_list (plus_QState q1 q2)) =  2^card (QState_vars (plus_QState q1 q2))"  
  by (simp add: QState_rel1')

(* lemma plus_QState_neutral:
  "QState_vars (plus_QState q1 q2) = {} = 
   ((QState_list (plus_QState q1 q2)) = [1])"  
  using QState_empty by auto *)

lemma plus_idem:"plus_QState a (QState ({},[1])) = a"
proof-
  {
    assume a00:"QState_vars a = {}"
    have ?thesis
      by (metis QState_refl QState_vars_id a00 inf_bot_left plus_QState_def 
        plus_QState_vector_a_idem plus_QState_vector_vars surjective_pairing)       
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
          length_0_conv nths_append zero_le)

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


instantiation QState ::  sep_algebra
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

lemma plus_QState_vector_cancellative:  
     assumes a0:"plus_QState_vector Q1 Q3 = plus_QState_vector Q2 Q3" and
       a1:"QState_vars Q1 \<inter> QState_vars Q3 = {}" and a2:"QState_vars Q2 \<inter> QState_vars Q3 = {}" 
     shows "Q1 = Q2"
proof-
  let ?v1 = "QState_vars Q1" and ?v2 = "QState_vars Q2" and ?v3 = "QState_vars Q3"
  let ?V1 = "QState_vector Q1" and ?V2 = "QState_vector Q2" and ?V3 = "QState_vector Q3"
  have v3_not_zero:"\<exists>i < 2^(card ?v3). ?V3$i\<noteq> 0"
    by (metis QState_rel1a' QState_rel3 QState_vector.rep_eq dim_vec_of_list vec_of_list_index)
  have eq_v1_v2:"?v1 = ?v2"
    by (metis Int_Un_eq(1) a0 a1 a2 plus_QState_vector_vars sup_commute sup_inf_distrib1)
  interpret ps2:partial_state2 "(replicate (card (?v1 \<union> ?v3)) (2::nat))" ?v1 ?v3 
    apply standard using a1
    using QState_rel3'  
    by auto
  interpret ps:partial_state "ps2.dims0" "ps2.vars1'" .
  have "partial_state2.ptensor_vec ?v1 ?v3 ?V1 ?V3 = 
                 partial_state2.ptensor_vec ?v1 ?v3 ?V2 ?V3"
    by (metis a0 eq_v1_v2 plus_QState_vector_vector vec_list)

  have "dim_vec (ps2.ptensor_vec ?V1 ?V3) = 
               2^(card (?v1 \<union> ?v3))"
    using a1 dim_vec_plus_2_pow_s by blast

  have "dim_vec (ps2.ptensor_vec ?V2 ?V3) = 
               2^(card (?v1 \<union> ?v3))"
    using a2 dim_vec_plus_2_pow_s eq_v1_v2
    by presburger 
  have "\<forall>i<2^(card (?v1 \<union> ?v3)). ps2.ptensor_vec ?V1 ?V3 $ i = ?V1$(ps.encode1 i) * ?V3 $(ps.encode2 i)"
    by (simp add: partial_state.tensor_vec_eval ps2.d_def ps2.dims0_def ps2.ptensor_vec_def ps2.vars0_def)
  moreover have "\<forall>i<2^(card (?v1 \<union> ?v3)). ps2.ptensor_vec ?V2 ?V3 $ i = ?V2$(ps.encode1 i) * ?V3 $(ps.encode2 i)"
    by (simp add: partial_state.tensor_vec_eval ps2.d_def ps2.dims0_def ps2.ptensor_vec_def ps2.vars0_def)
  moreover have "\<forall>i<2^(card (?v1 \<union> ?v3)). ps2.ptensor_vec ?V1 ?V3 $ i = ps2.ptensor_vec ?V2 ?V3 $ i"
    using \<open>ps2.ptensor_vec (QState_vector Q1) (QState_vector Q3) = ps2.ptensor_vec (QState_vector Q2) (QState_vector Q3)\<close> by presburger
  ultimately have "\<forall>i<2^(card (?v1 \<union> ?v3)). 
                     ?V1$(ps.encode1 i) * ?V3 $(ps.encode2 i) =  
                     ?V2$(ps.encode1 i) * ?V3 $(ps.encode2 i)"
    by auto
  then have v1:"\<forall>i j. i<2^(card ?v1 ) \<and> j < 2^(card ?v3) \<longrightarrow> 
              ?V1$i * ?V3 $j = ?V2$i * ?V3 $j"
    by (metis \<open>dim_vec (ps2.ptensor_vec (QState_vector Q2) (QState_vector Q3)) = 2 ^ card (QState_vars Q1 \<union> QState_vars Q3)\<close> 
             partial_state.d1_def partial_state.d2_def partial_state.dims1_def partial_state.dims2_def 
             prod_list_replicate ps.encode12_inv1 ps.encode12_inv2 
             ps.encode12_lt ps2.d0_def ps2.dims1_def ps2.dims2_def 
             ps2.nths_vars1' ps2.nths_vars2' ps2.ptensor_vec_dim state_sig.d_def)
  then have "\<forall>i<2^(card ?v1). ?V1$i = ?V2$i"
  proof-
    { assume "\<exists>i<2^(card ?v1). ?V1$i \<noteq> ?V2$i"
      then obtain i where "i<2^(card ?v1)" and 
                         "?V1$i \<noteq> ?V2$i"
        by auto
      then have "\<forall>i < 2^(card ?v3). ?V3 $ i = 0"
        using v1 by auto
      then have False using v3_not_zero by auto
    }
    thus ?thesis by auto
  qed
  then have "QState_vector Q1 = QState_vector Q2"
    using  eq_v1_v2
    by (metis QState_rel1a' eq_vecI)
  then show ?thesis using eq_v1_v2 apply transfer
    by (metis fst_conv list_vec snd_conv)
qed

instantiation QState :: cancellative_sep_algebra
begin
instance 
  apply standard 
  apply (simp add: plus_QState sep_disj_QState plus_QState_def disj_QState_def) 
  apply transfer' apply (auto simp add: plus_QState_vector_wf)
  using plus_QState_vector_cancellative by presburger 
end

(* lemma  assumes a0:"(Q::QState) = Q1 + Q2" and
       a1:"Q1##Q2" and a2:"Q = Q1" 
     shows "Q2 = 0"
proof-
  let ?v = "QState_vars Q" and ?v1 = "QState_vars Q1" and ?v2 = "QState_vars Q2"
  let ?V = "QState_vector Q" and ?V1 = "QState_vector Q1" and ?V2 = "QState_vector Q2"
  
  interpret ps2:partial_state2 "(replicate (card (?v1 \<union> ?v2)) (2::nat))" ?v1 ?v2
    apply standard using a1
    using QState_rel3'
    by (auto simp add: disj_QState_def sep_disj_QState)  
  interpret ps:partial_state "ps2.dims0" "ps2.vars1'" .
  have "Q = Q + Q2" using a0 a2 by auto
  moreover have "?v2 = {}"
    by (metis QState_vars_Plus a0 a2 add_cancel_left_right card_eq_0_iff length_replicate 
              plus_QState plus_QState_vector_vars ps2.dims0_def ps2.disjoint 
              ps2.finite_v2 ps2.length_dims0 ps2.vars0_def)*)

lemma encode_lt_card:
  assumes a0:"vs1 \<inter> vs2 = {}" and a1:"finite vs1" and a2:"finite vs2" and                            
            a4:"i<(2^card(vs1 \<union> vs2))" 
  shows "(partial_state.encode1 (list_dims (vs1 \<union> vs2)) (partial_state2.vars1' vs1 vs2) i) < 2 ^ card vs1" and
        "(partial_state.encode2 (list_dims (vs1 \<union> vs2)) (partial_state2.vars1' vs1 vs2) i) < 2 ^ card vs2"    
proof-
  interpret ps2:partial_state2 "list_dims (vs1 \<union> vs2)" vs1 vs2
    apply standard using a0 a1 a2 unfolding list_dims_def by auto    
  interpret ps:partial_state "ps2.dims0" "ps2.vars1'" .
  have "prod_list ps2.dims0 = 2 ^ card (vs1 \<union> vs2)"
    unfolding ps2.dims0_def ps2.vars0_def by auto
  moreover have "ps.d = 2 ^ card (vs1 \<union> vs2)"
    using calculation ps.d_def by presburger
  moreover have "ps.d1 = 2 ^ card vs1"
    by (simp add: ps.d1_def ps.dims1_def ps2.dims1_def ps2.nths_vars1')
  moreover have "ps.d2 = 2 ^ card vs2"
    by (simp add: ps.d2_def ps.dims2_def ps2.dims2_def ps2.nths_vars2')
  moreover have "(ps.encode1  i) < 2 ^ card vs1"
    using a4 calculation
    using ps.encode1_lt by presburger
  moreover have "(ps.encode2  i) < 2 ^ card vs2"
    using a4 calculation
    using ps.encode2_lt by presburger
  ultimately show "(partial_state.encode1 (list_dims (vs1 \<union> vs2)) (partial_state2.vars1' vs1 vs2) i) < 2 ^ card vs1" and
                  "(partial_state.encode2 (list_dims (vs1 \<union> vs2)) (partial_state2.vars1' vs1 vs2) i) < 2 ^ card vs2"
    unfolding list_dims_def  ps2.dims0_def ps2.vars0_def  by auto
qed

lemma not_zero_vector_index:assumes a0:"v \<noteq> 0\<^sub>v m" and a1:"dim_vec v = m"
  shows "\<exists>i<m. v$i \<noteq> 0"
proof-
  { assume a00:"\<not>(\<exists>i<m. v$i \<noteq> 0)"   
    have "dim_vec v = dim_vec (0\<^sub>v m)"
      by (simp add: a1)
    moreover have "\<forall>i< dim_vec (0\<^sub>v m).  v $ i = (0\<^sub>v m) $ i"
      using a00 by auto
    ultimately have "v = 0\<^sub>v m" by auto
    then have False using a0 by auto
  } thus ?thesis by auto
qed

lemma not_zero_tensor_product_index:
  assumes a0:"vs1 \<inter> vs2 = {}" and a1:"finite vs1" and a2:"finite vs2" and                            
              a3:"ptensor_vec vs1 vs2 v1 v2 \<noteq> 0\<^sub>v (2^card(vs1 \<union> vs2))"
   shows "\<exists>i<(2^card(vs1 \<union> vs2)). ptensor_vec vs1 vs2 v1 v2 $ i \<noteq> 0"
proof-
  interpret ps2:partial_state2 "list_dims (vs1 \<union> vs2)" vs1 vs2
    apply standard using a0 a1 a2 unfolding list_dims_def by auto
  have "dim_vec (ptensor_vec vs1 vs2 v1 v2) = 2^card(vs1 \<union> vs2)"
    by (simp add: ps2.d0_def ps2.dims0_def ps2.vars0_def)
  then show ?thesis using a3
    using not_zero_vector_index by blast  
qed

lemma not_zero_tensor_product_comp_index:
  assumes a0:"vs1 \<inter> vs2 = {}" and a1:"finite vs1" and a2:"finite vs2" and                            
              a3:"ptensor_vec vs1 vs2 (v1::('a::comm_ring_1) vec) v2 \<noteq> 0\<^sub>v (2^card(vs1 \<union> vs2))"            
            shows "\<exists>i<(2^card vs1). v1 $ i \<noteq> 0" and "\<exists>i<(2^card vs2). v2 $ i \<noteq> 0"
proof-
  interpret ps2:partial_state2 "list_dims (vs1 \<union> vs2)" vs1 vs2
    apply standard using a0 a1 a2 unfolding list_dims_def by auto  
  obtain i where i:"i < 2^card(vs1 \<union> vs2) \<and>  (ptensor_vec vs1 vs2 v1 v2 $ i \<noteq> 0)"
    using not_zero_tensor_product_index[OF a0 a1 a2 a3] by auto
  moreover have "prod_list ps2.dims0 = 2 ^ card (vs1 \<union> vs2)"
    unfolding ps2.dims0_def ps2.vars0_def by auto
  moreover have "v1$(partial_state.encode1 ps2.dims0 ps2.vars1' i) \<noteq> 0" and 
            "v2$(partial_state.encode2 ps2.dims0 ps2.vars1' i) \<noteq> 0" using calculation
    unfolding  ps2.ptensor_vec_def  partial_state.tensor_vec_def state_sig.d_def   by auto
  ultimately show "\<exists>i<(2^card vs1). v1 $ i \<noteq> 0" and "\<exists>i<(2^card vs2). v2 $ i \<noteq> 0"    
    apply auto
     apply (metis partial_state.d2_def partial_state.dims2_def partial_state.encode2_lt 
                  prod_list_replicate ps2.dims1_def ps2.nths_vars1'_comp 
                  ps2.ptensor_encode1_encode2 state_sig.d_def)
    by (metis partial_state.d2_def partial_state.dims2_def partial_state.encode2_lt prod_list_replicate ps2.dims2_def ps2.nths_vars2' state_sig.d_def)
qed

lemma not_zero_tensor_product_comp_vectors:
  assumes a0:"vs1 \<inter> vs2 = {}" and a1:"finite vs1" and a2:"finite vs2" and 
             a3:"dim_vec v1 = 2^card vs1" and a4:"dim_vec v2 = 2^card vs2" and
              a5:"ptensor_vec vs1 vs2 (v1::('a::comm_ring_1) vec) v2 \<noteq> 0\<^sub>v (2^card(vs1 \<union> vs2))"            
            shows "v1 \<noteq> 0\<^sub>v (dim_vec v1)" and "v2 \<noteq> 0\<^sub>v (dim_vec v2)"
  using not_zero_tensor_product_comp_index[OF a0 a1 a2 a5]
  using a3 a4 by auto

lemma not_zero_tensor_product_comp_index_1:
  assumes a0:"vs1 \<inter> vs2 = {}" and a1:"finite vs1" and a2:"finite vs2" and                            
              a3:"ptensor_vec vs1 vs2 (v1::('a::comm_ring_1) vec) v2 \<noteq> 0\<^sub>v (2^card(vs1 \<union> vs2))" and
            a4:"i<(2^card(vs1 \<union> vs2))" and a5:"ptensor_vec vs1 vs2 v1 v2 $ i \<noteq> 0"
          shows "v1 $(partial_state.encode1 (list_dims (vs1 \<union> vs2)) (partial_state2.vars1' vs1 vs2) i) \<noteq> 0" and 
                "v2 $(partial_state.encode2 (list_dims (vs1 \<union> vs2)) (partial_state2.vars1' vs1 vs2) i) \<noteq> 0"
proof-
  interpret ps2:partial_state2 "list_dims (vs1 \<union> vs2)" vs1 vs2
    apply standard using a0 a1 a2 unfolding list_dims_def by auto    
  interpret ps:partial_state "ps2.dims0" "ps2.vars1'" .
  have "prod_list ps2.dims0 = 2 ^ card (vs1 \<union> vs2)"
    unfolding ps2.dims0_def ps2.vars0_def by auto
  moreover have "ps.d = 2 ^ card (vs1 \<union> vs2)"
    using calculation ps.d_def by presburger
  moreover have "ps.d1 = 2 ^ card vs1"
    by (simp add: ps.d1_def ps.dims1_def ps2.dims1_def ps2.nths_vars1')
  moreover have "ps.d2 = 2 ^ card vs2"
    by (simp add: ps.d2_def ps.dims2_def ps2.dims2_def ps2.nths_vars2')
  moreover have "(ps.encode1  i) < 2 ^ card vs1"
    using a4 calculation
    using ps.encode1_lt by presburger
  moreover have "(ps.encode2  i) < 2 ^ card vs2"
    using a4 calculation
    using ps.encode2_lt by presburger
  moreover show "v1$(partial_state.encode1 (list_dims (vs1 \<union> vs2)) ps2.vars1' i) \<noteq> 0" and 
            "v2$(partial_state.encode2 (list_dims (vs1 \<union> vs2)) ps2.vars1' i) \<noteq> 0" 
    using calculation a4 a5
    unfolding  ps2.ptensor_vec_def  partial_state.tensor_vec_def state_sig.d_def list_dims_def ps2.dims0_def  
    by auto
qed


lemma not_zero_tensor_product_comp_index_2:
  assumes a0:"vs1 \<inter> vs2 = {}" and a1:"finite vs1" and a2:"finite vs2" and                            
              a3:"ptensor_vec vs1 vs2 (v1::('a::field) vec) v2 \<noteq> 0\<^sub>v (2^card(vs1 \<union> vs2))" and            
              a4:"i<(2^card(vs1 \<union> vs2))" and
              a5:"v1 $(partial_state.encode1 (list_dims (vs1 \<union> vs2)) (partial_state2.vars1' vs1 vs2) i) \<noteq> 0" and 
              a6:"v2 $(partial_state.encode2 (list_dims (vs1 \<union> vs2)) (partial_state2.vars1' vs1 vs2) i) \<noteq> 0" 
            shows "ptensor_vec vs1 vs2 v1 v2 $ i \<noteq> 0"
proof-
  interpret ps2:partial_state2 "list_dims (vs1 \<union> vs2)" vs1 vs2
    apply standard using a0 a1 a2 unfolding list_dims_def by auto      
  interpret ps:partial_state "ps2.dims0" "ps2.vars1'" .  
  have prod_list:"prod_list ps2.dims0 = 2 ^ card (vs1 \<union> vs2)"
    unfolding ps2.dims0_def ps2.vars0_def by auto  
  have i_lt_d:"i< ps.d" unfolding ps.d_def using a4 prod_list by auto
  then have enc1_lt_d1:"ps.encode1 i < ps.d1" and enc1_lt_d2:"ps.encode2 i < ps.d2" by auto    
  have "ps.encode12 ((ps.encode1 i), (ps.encode2  i)) = i"
    using prod_list a4  ps.encode12_inv state_sig.d_def by presburger   
  then show ?thesis using a5 a6 enc1_lt_d1 enc1_lt_d2 unfolding ps2.ptensor_vec_def ps.tensor_vec_def 
    unfolding state_sig.d_def ps2.dims0_def  ps2.vars0_def partial_state.d1_def partial_state.d2_def
    using a4 unfolding list_dims_def by auto   
qed

lemma v1_eq_0_v1'_eq_0:assumes a0:"vs1 \<inter> vs2 = {}" and a1:"finite vs1" and a2:"finite vs2" and   
              a3:"ptensor_vec vs1 vs2 (v1::('a::field) vec) v2 \<noteq> 0\<^sub>v (2^card(vs1 \<union> vs2))" and
              a4:"ptensor_vec vs1 vs2 (v1::('a::field) vec) v2 = 
                  ptensor_vec vs1 vs2 v1' v2'" and 
              a5:"i< 2 ^ card vs1"
            shows "(v1 $ i) = 0 \<longrightarrow> (v1' $ i) = 0"
proof-
  have a3':"ptensor_vec vs1 vs2 v1' v2' \<noteq> 0\<^sub>v (2^card(vs1 \<union> vs2))"
    using a3 a4 by auto
  { assume a00:"v1 $ i = 0" and a01:"v1' $ i \<noteq> 0"
    interpret ps2:partial_state2 "list_dims (vs1 \<union> vs2)" vs1 vs2
      apply standard using a0 a1 a2 unfolding list_dims_def by auto      
    interpret ps:partial_state "ps2.dims0" "ps2.vars1'" . 
    have i_lt_d1:"i< ps.d1"
      by (simp add: a5 ps.d1_def ps.dims1_def ps2.dims1_def ps2.nths_vars1') 
    have "\<forall>j<(2 ^ card vs2). ps2.ptensor_vec v1 v2 $ ps.encode12 (i, j) = 0"
    proof-
      { fix j
        assume a000:"(j::nat) < 2^card vs2"
        then have j_lt_d2:"j < ps.d2"
          by (simp add: ps.d2_def ps.dims2_def ps2.dims2_def ps2.nths_vars2')
        then have "ps.encode12 (i, j) < ps.d"
          using i_lt_d1 partial_state.encode12_lt by presburger
        moreover have "v1 $ ps.encode1 (ps.encode12 (i, j)) = 0" 
          using a00
          by (simp add: i_lt_d1 j_lt_d2 partial_state.encode12_inv1)          
        ultimately have "ps2.ptensor_vec v1 v2 $ ps.encode12 (i, j) = 0"
          unfolding ps2.ptensor_vec_def ps.tensor_vec_def 
          by auto
      } thus ?thesis by auto
    qed
    moreover obtain j where j_lt_card_vs2:"j < 2^card vs2" and v2:"v2' $ j\<noteq>0"  
      using not_zero_tensor_product_comp_index[OF a0 a1 a2 a3'] by auto
    then have j_lt_d2:"j < ps.d2" 
      by (simp add: ps.d2_def ps.dims2_def ps2.dims2_def ps2.nths_vars2')
    then have  "ps2.ptensor_vec v1' v2' $ ps.encode12 (i, j) \<noteq> 0"
      using a01 v2
      by (simp add: i_lt_d1 partial_state.encode12_lt ps.encode12_inv1 ps.encode12_inv2 ps.tensor_vec_eval ps2.ptensor_vec_def)    
    ultimately have False using a4 
      by (simp add:j_lt_card_vs2)               
  } thus ?thesis by auto
qed

lemma v1_neq_0_nv1'_neq_0:
  assumes a0:"vs1 \<inter> vs2 = {}" and a1:"finite vs1" and a2:"finite vs2" and   
              a3:"ptensor_vec vs1 vs2 (v1::('a::field) vec) v2 \<noteq> 0\<^sub>v (2^card(vs1 \<union> vs2))" and
              a4:"ptensor_vec vs1 vs2 (v1::('a::field) vec) v2 = 
                  ptensor_vec vs1 vs2 v1' v2'" and 
              a5:"i< 2 ^ card vs1"
            shows "(v1 $ i) \<noteq> 0 \<longrightarrow> (v1' $ i) \<noteq> 0"
proof-
  have a3':"ptensor_vec vs1 vs2 v1' v2' \<noteq> 0\<^sub>v (2^card(vs1 \<union> vs2))"
    using a3 a4 by auto
  { assume a00:"v1 $ i \<noteq> 0" and a01:"v1' $ i = 0"
    interpret ps2:partial_state2 "list_dims (vs1 \<union> vs2)" vs1 vs2
      apply standard using a0 a1 a2 unfolding list_dims_def by auto      
    interpret ps:partial_state "ps2.dims0" "ps2.vars1'" . 
    have i_lt_d1:"i< ps.d1"
      by (simp add: a5 ps.d1_def ps.dims1_def ps2.dims1_def ps2.nths_vars1') 
    have "\<forall>j<(2 ^ card vs2). ps2.ptensor_vec v1' v2' $ ps.encode12 (i, j) = 0"
    proof-
      { fix j
        assume a000:"(j::nat) < 2^card vs2"
        then have j_lt_d2:"j < ps.d2"
          by (simp add: ps.d2_def ps.dims2_def ps2.dims2_def ps2.nths_vars2')
        then have "ps.encode12 (i, j) < ps.d"
          using i_lt_d1 partial_state.encode12_lt by presburger
        moreover have "v1' $ ps.encode1 (ps.encode12 (i, j)) = 0" 
          using a01
          by (simp add: i_lt_d1 j_lt_d2 partial_state.encode12_inv1)          
        ultimately have "ps2.ptensor_vec v1' v2' $ ps.encode12 (i, j) = 0"
          unfolding ps2.ptensor_vec_def ps.tensor_vec_def 
          by auto
      } thus ?thesis by auto
    qed
    moreover obtain j where j_lt_card_vs2:"j < 2^card vs2" and v2:"v2 $ j\<noteq>0"  
      using not_zero_tensor_product_comp_index[OF a0 a1 a2 a3] by auto
    then have j_lt_d2:"j < ps.d2" 
      by (simp add: ps.d2_def ps.dims2_def ps2.dims2_def ps2.nths_vars2')
    then have  "ps2.ptensor_vec v1 v2 $ ps.encode12 (i, j) \<noteq> 0"
      using a00 v2
      by (simp add: i_lt_d1 partial_state.encode12_lt ps.encode12_inv1 ps.encode12_inv2 ps.tensor_vec_eval ps2.ptensor_vec_def)    
    ultimately have False using a4 
      by (simp add:j_lt_card_vs2)               
  } thus ?thesis by auto
qed

lemma v1_nv1': 
  assumes a0:"vs1 \<inter> vs2 = {}" and a1:"finite vs1" and a2:"finite vs2" and   
              a3:"ptensor_vec vs1 vs2 (v1::('a::field) vec) v2 \<noteq> 0\<^sub>v (2^card(vs1 \<union> vs2))" and
              a4:"ptensor_vec vs1 vs2 (v1::('a::field) vec) v2 = 
                  ptensor_vec vs1 vs2 v1' v2'" and 
              a5:"i< 2 ^ card vs1"
   shows "(v1 $ i) = 0 \<longleftrightarrow> (v1' $ i) = 0"
  using v1_neq_0_nv1'_neq_0[OF a0 a1 a2 a3 a4 a5] 
        v1_eq_0_v1'_eq_0[OF a0 a1 a2 a3 a4 a5 ] by auto

lemma ptensor_comm_zero:
  assumes a0:"vs1 \<inter> vs2 = {}" and a1:"finite vs1" and a2:"finite vs2" and   
          a3:"ptensor_vec vs1 vs2 (v1::('a::field) vec) v2 \<noteq> 0\<^sub>v (2^card(vs1 \<union> vs2))" 
  shows "ptensor_vec vs2 vs1 (v2::('a::field) vec) v1 \<noteq> 0\<^sub>v (2^card(vs2 \<union> vs1))"
  by (metis a0 a1 a2 a3 ptensor_vec_comm sup_commute)


lemma ptensors_comm_eq:
  assumes a0:"vs1 \<inter> vs2 = {}" and a1:"finite vs1" and a2:"finite vs2" and   
          a3:"ptensor_vec vs1 vs2 (v1::('a::field) vec) v2 \<noteq> 0\<^sub>v (2^card(vs1 \<union> vs2))" and
          a4:"ptensor_vec vs1 vs2 (v1::('a::field) vec) v2 = 
                  ptensor_vec vs1 vs2 v1' v2'"
      shows "ptensor_vec vs2 vs1 (v2::('a::field) vec) v1 = 
                   ptensor_vec vs2 vs1 v2' v1'"
  by (metis a0 a1 a2 a4 ptensor_vec_comm)


lemma v2_nv2': 
  assumes a0:"vs1 \<inter> vs2 = {}" and a1:"finite vs1" and a2:"finite vs2" and   
              a3:"ptensor_vec vs1 vs2 (v1::('a::field) vec) v2 \<noteq> 0\<^sub>v (2^card(vs1 \<union> vs2))" and
              a4:"ptensor_vec vs1 vs2 (v1::('a::field) vec) v2 = 
                  ptensor_vec vs1 vs2 v1' v2'" and 
              a5:"i < 2 ^ card vs2"
            shows "(v2 $ i) = 0 \<longleftrightarrow> (v2' $ i) = 0"  
  using v1_nv1'[OF _ a2 a1  ptensor_comm_zero[OF a0 a1 a2 a3] ptensors_comm_eq[OF a0 a1 a2 a3 a4] a5] a0
  by auto


lemma v_eq_k_times_v': 
  assumes a0:"vs1 \<inter> vs2 = {}" and a1:"finite vs1" and a2:"finite vs2" and   
              a3:"ptensor_vec vs1 vs2 (v1::('a::field) vec) v2 \<noteq> 0\<^sub>v (2^card(vs1 \<union> vs2))" and
              a4:"ptensor_vec vs1 vs2 v1 v2 = 
                  ptensor_vec vs1 vs2 v1' v2'" and 
              a5:"i< 2 ^ card vs1" and a6:"j < 2 ^ card vs2" and a7:"v1 $ i \<noteq> 0" and a8:"v2 $ j \<noteq> 0"
            shows "v1$i = ((v1$i) * (inverse (v1'$i))) * (v1'$i)"  and 
                  "v2$j = ((inverse (v2'$j)) * (v2$j)) * (v2'$j)"
proof-
  have "v1' $ i \<noteq> 0" using v1_nv1'[OF a0 a1 a2 a3 a4 a5] a7 by auto 
  then show "v1$i = ((v1$i) * (inverse (v1'$i))) * (v1'$i)" 
    by simp
  have "v2' $ j \<noteq> 0" using v2_nv2'[OF a0 a1 a2 a3 a4 a6] a8 by auto
  then show "v2$j = ((inverse (v2'$j)) * (v2$j)) * (v2'$j)" by simp
qed

lemma v1_div_v1'_eq_v2'_div_v2: 
  assumes a0:"vs1 \<inter> vs2 = {}" and a1:"finite vs1" and a2:"finite vs2" and   
              a3:"ptensor_vec vs1 vs2 (v1::('a::field) vec) v2 \<noteq> 0\<^sub>v (2^card(vs1 \<union> vs2))" and
              a4:"ptensor_vec vs1 vs2 v1 v2 = 
                  ptensor_vec vs1 vs2 v1' v2'" 
            shows "\<forall>i j. i<2 ^ card vs1 \<and> j < 2 ^ card vs2 \<and> v1$i\<noteq>0 \<and> v2$j\<noteq>0 \<longrightarrow>
                   v1$i * inverse(v1'$i) = v2'$j * inverse (v2$j)"
proof-
  { fix i j
    assume a00:"i < 2 ^ card vs1" and a01:"j < 2 ^ card vs2" and a02:"v1$i\<noteq>0" and a03:"v2$j\<noteq>0"
    have a02':"v1'$i \<noteq> 0" using v1_neq_0_nv1'_neq_0[OF a0 a1 a2 a3 a4  a00] a02 by auto
    have a03':"v2'$j \<noteq> 0" using v2_nv2'[OF a0 a1 a2 a3 a4 a01] a03 by auto
    interpret ps2:partial_state2 "list_dims (vs1 \<union> vs2)" vs1 vs2
      apply standard using a0 a1 a2 unfolding list_dims_def by auto      
    interpret ps:partial_state "ps2.dims0" "ps2.vars1'" . 
    have "ps2.ptensor_vec v1 v2 $ ps.encode12 (i, j) = v1 $ i * v2 $ j" using a00 a01
      by (simp add: partial_state.encode12_inv1 partial_state.encode12_lt ps.d1_def ps.d2_def 
                    ps.dims1_def ps.dims2_def ps.encode12_inv2 ps.tensor_vec_eval 
                    ps2.dims1_def ps2.dims2_def ps2.nths_vars1' ps2.nths_vars2' ps2.ptensor_vec_def) 
    moreover have "ps2.ptensor_vec v1' v2' $ ps.encode12 (i, j) = v1' $ i * v2' $ j" using a00 a01
      by (simp add: partial_state.encode12_lt partial_state.tensor_vec_eval ps.d1_def 
                    ps.d2_def ps.dims1_def ps.dims2_def ps.encode12_inv1 ps.encode12_inv2 
                    ps2.dims1_def ps2.dims2_def ps2.nths_vars1' ps2.nths_vars2' ps2.ptensor_vec_def)
    ultimately have "v1 $ i * v2 $ j = v1' $ i * v2' $ j" using a4
      by simp
    then have "v1$i * inverse(v1'$i) = v2'$j * inverse (v2$j)"
      using a02 a03  a02' a03'
      by (smt (verit, best) field_class.field_inverse mult.comm_neutral mult.left_commute)      
  } thus ?thesis by auto
qed

lemma all_v1i_neq_zero_div_v1'i_eq: 
  assumes a0:"vs1 \<inter> vs2 = {}" and a1:"finite vs1" and a2:"finite vs2" and   
              a3:"ptensor_vec vs1 vs2 (v1::('a::field) vec) v2 \<noteq> 0\<^sub>v (2^card(vs1 \<union> vs2))" and
              a4:"ptensor_vec vs1 vs2 v1 v2 = 
                  ptensor_vec vs1 vs2 v1' v2'" 
            shows "\<forall>i j. i<2 ^ card vs1 \<and> j < 2 ^ card vs1 \<and> v1$i\<noteq>0 \<and> v1$j\<noteq>0 \<longrightarrow>
                   v1$i * inverse(v1'$i) = v1$j * inverse (v1'$j)"
proof-
 { fix i j
    assume a00:"i < 2 ^ card vs1" and a01:"j < 2 ^ card vs1" and a02:"v1$i\<noteq>0" and a03:"v1$j\<noteq>0"
    have a02':"v1'$i \<noteq> 0" using v1_neq_0_nv1'_neq_0[OF a0 a1 a2 a3 a4  a00] a02 by auto
    moreover have a03':"v1'$j \<noteq> 0" using v1_neq_0_nv1'_neq_0[OF a0 a1 a2 a3 a4 a01] a03 by auto
    interpret ps2:partial_state2 "list_dims (vs1 \<union> vs2)" vs1 vs2
      apply standard using a0 a1 a2 unfolding list_dims_def by auto      
    interpret ps:partial_state "ps2.dims0" "ps2.vars1'" . 
    obtain k where "k<2^card vs2" and "v2$k\<noteq>0"
      using not_zero_tensor_product_comp_index[OF a0 a1 a2 a3] by auto  
    then have "v1$i * inverse(v1'$i) = v2'$k * inverse (v2$k)" and "v1$j * inverse(v1'$j) = v2'$k * inverse (v2$k)"
      using v1_div_v1'_eq_v2'_div_v2[OF a0 a1 a2 a3 a4 ] a00 a02 a01 a03 a02' a03'
      by auto      
    then have "v1$i * inverse(v1'$i) = v1$j * inverse (v1'$j)" by auto  
  }
  thus ?thesis by auto
qed

lemma all_v2'i_neq_zero_div_v2i_eq: 
  assumes a0:"vs1 \<inter> vs2 = {}" and a1:"finite vs1" and a2:"finite vs2" and   
              a3:"ptensor_vec vs1 vs2 (v1::('a::field) vec) v2 \<noteq> 0\<^sub>v (2^card(vs1 \<union> vs2))" and
              a4:"ptensor_vec vs1 vs2 v1 v2 = 
                  ptensor_vec vs1 vs2 v1' v2'" 
            shows "\<forall>i j. i<2 ^ card vs2 \<and> j < 2 ^ card vs2 \<and> v2$i\<noteq>0 \<and> v2$j\<noteq>0 \<longrightarrow>
                   v2'$i * inverse(v2$i) = v2'$j * inverse (v2$j)"
proof-
 { fix i j
    assume a00:"i < 2 ^ card vs2" and a01:"j < 2 ^ card vs2" and a02:"v2$i\<noteq>0" and a03:"v2$j\<noteq>0"
    have a02':"v2'$i \<noteq> 0" using v2_nv2'[OF a0 a1 a2 a3 a4  a00] a02 by auto
    moreover have a03':"v2'$j \<noteq> 0" using v2_nv2'[OF a0 a1 a2 a3 a4  a01] a03 by auto
    interpret ps2:partial_state2 "list_dims (vs1 \<union> vs2)" vs1 vs2
      apply standard using a0 a1 a2 unfolding list_dims_def by auto      
    interpret ps:partial_state "ps2.dims0" "ps2.vars1'" . 
    obtain k where "k<2^card vs1" and "v1$k\<noteq>0"
      using not_zero_tensor_product_comp_index[OF a0 a1 a2 a3] by auto  
    then have "v1$k * inverse(v1'$k) = v2'$i * inverse (v2$i)" and "v1$k * inverse(v1'$k) = v2'$j * inverse (v2$j)"
      using v1_div_v1'_eq_v2'_div_v2[OF a0 a1 a2 a3 a4] a00 a02 a01 a03 a02' a03'
      by blast+      
    then have "v2'$i * inverse(v2$i) = v2'$j * inverse (v2$j)" by auto  
  }
  thus ?thesis by auto
qed

lemma exists_k_v1_prod_scalar_k_v1': 
  assumes a0:"vs1 \<inter> vs2 = {}" and a1:"finite vs1" and a2:"finite vs2" and              
              a3:"ptensor_vec vs1 vs2 (v1::('a::field) vec) v2 = 
                  ptensor_vec vs1 vs2 v1' v2'" and
              a4:"ptensor_vec vs1 vs2 v1 v2 \<noteq> 0\<^sub>v (2^card(vs1 \<union> vs2))" and
              a5:"dim_vec v1 = 2 ^ card vs1" and a6:"dim_vec v1' = 2 ^ card vs1"
   shows "\<exists>i < dim_vec v1. v1$i\<noteq>0 \<and> v1 = (v1$i * inverse (v1'$i)) \<cdot>\<^sub>v v1'"
proof-
  obtain i where a00:"i<2^card vs1" and a01:"v1$i\<noteq>0" 
    using not_zero_tensor_product_comp_index[OF a0 a1 a2 a4] by auto
  moreover have a01':"v1'$i\<noteq>0"  
    using v1_nv1'[OF a0 a1 a2 a4 a3 a00] a01  by auto  
  let ?k = "v1$i * inverse (v1'$i)"
  have "dim_vec v1 = dim_vec (?k \<cdot>\<^sub>v v1')" using a5 a6 by auto
  moreover have "\<And>i. i < dim_vec v1 \<Longrightarrow> v1 $i = (?k \<cdot>\<^sub>v v1') $ i"
    (* by (smt (verit, ccfv_SIG) \<open>v1' $ i \<noteq> 0\<close> a0 a00 a1 a2 a3 a4 a5 all_v1i_neq_zero_div_v1'i_eq 
            divide_divide_eq_left divide_inverse_commute index_smult_vec(1) inverse_1 inverse_unique 
            left_inverse mult.commute mult_eq_0_iff v1_nv1') *)
  proof-
    fix k
    assume a000:"k < dim_vec v1"
    { assume "v1 $ k = 0" moreover have "v1' $ k = 0"
        using v1_nv1'[OF a0 a1 a2 a4 a3] a000 a5 a6 calculation
        by auto
      ultimately have "v1 $k = (?k \<cdot>\<^sub>v v1') $ k" using a000 a5 a6 by auto
    }
    moreover{ 
      assume "v1 $ k \<noteq> 0"
      moreover have "v1' $ k \<noteq> 0"
        using  v1_nv1'[OF a0 a1 a2 a4 a3] a5 a000 calculation by auto      
      moreover have "v1 $ k = v1 $ k * inverse (v1' $ k) * v1' $ k" 
        using calculation by auto  
      ultimately have "v1 $k = (?k \<cdot>\<^sub>v v1') $ k"   
        using a000 a00 a5 a6 a01 all_v1i_neq_zero_div_v1'i_eq[rule_format, OF a0 a1 a2 a4 a3,of  k i] 
        by auto
    } ultimately show "v1 $k = (?k \<cdot>\<^sub>v v1') $ k" by blast
  qed    
  ultimately have "v1 = ?k \<cdot>\<^sub>v v1'" by auto
  thus ?thesis
    using a00 a01 a5 by auto
qed

lemma exists_k_v2_prod_scalar_k_v2': 
  assumes a0:"vs1 \<inter> vs2 = {}" and a1:"finite vs1" and a2:"finite vs2" and              
              a3:"ptensor_vec vs1 vs2 (v1::('a::field) vec) v2 = 
                  ptensor_vec vs1 vs2 v1' v2'" and
              a4:"ptensor_vec vs1 vs2 v1 v2 \<noteq> 0\<^sub>v (2^card(vs1 \<union> vs2))" and
              a5:"dim_vec v2 = 2 ^ card vs2" and a6:"dim_vec v2' = 2 ^ card vs2"
            shows "\<exists>i < dim_vec v2. v2$i\<noteq>0 \<and> v2 = (v2$i * inverse (v2'$i)) \<cdot>\<^sub>v v2'"
  using exists_k_v1_prod_scalar_k_v1'[OF _ a2 a1  ptensors_comm_eq[OF a0 a1 a2 a4 a3]  ptensor_comm_zero[OF a0 a1 a2 a4]  a5 a6] a0 
  by auto

lemma eq_tensor_inverse_1:
  assumes a0:"vs1 \<inter> vs2 = {}" and a1:"finite vs1" and a2:"finite vs2" and              
              a3:"ptensor_vec vs1 vs2 (v1::('a::field) vec) v2 = 
                  ptensor_vec vs1 vs2 v1' v2'" and
              a4:"ptensor_vec vs1 vs2 v1 v2 \<noteq> 0\<^sub>v (2^card(vs1 \<union> vs2))" and
              a5:"dim_vec v1 = 2 ^ card vs1" and a6:"dim_vec v1' = 2 ^ card vs1" and
              a7:"dim_vec v2 = 2 ^ card vs2" and a8:"dim_vec v2' = 2 ^ card vs2"
            shows "\<exists>k. k\<noteq> 0 \<and> v1 = k \<cdot>\<^sub>v v1' \<and> v2 = inverse k \<cdot>\<^sub>v v2'"
proof-  
  obtain i where "i < dim_vec v1" and "v1$i\<noteq>0" and "v1 = (v1$ i * inverse (v1'$i))\<cdot>\<^sub>v v1'"
    using exists_k_v1_prod_scalar_k_v1'[OF a0 a1 a2 a3 a4 a5 a6] by auto
  moreover obtain j where "j < dim_vec v2" and "v2$j\<noteq>0" and "v2 = (v2$ j * inverse (v2'$j))\<cdot>\<^sub>v v2'"
    using exists_k_v2_prod_scalar_k_v2'[OF a0 a1 a2 a3 a4 a7 a8] by auto
  moreover have  "v1$ i * inverse (v1'$i) = v2'$ j * inverse (v2$j)"
    using v1_div_v1'_eq_v2'_div_v2[OF a0 a1 a2 a4 a3] calculation
    by (metis a5 a7)
  then have "v2$ j * inverse (v2'$j) = inverse (v1$ i * inverse (v1'$i))"
    using calculation by auto
  moreover have "v1$ i * inverse (v1'$i) \<noteq> 0" using calculation by auto
  ultimately show ?thesis 
    by metis 
qed
(* definition equiv_vectors::"complex vec \<Rightarrow> complex vec \<Rightarrow> bool"
  where "equiv_vectors v1 v2 \<equiv> \<exists>c. v1 = c \<cdot>\<^sub>v v2 \<and> \<bar>c\<bar> = 1"

lemma equiv_comm:"equiv_vectors v1 v2 = equiv_vectors v2 v1"
  unfolding equiv_vectors_def apply auto
  by (metis abs_0 abs_mult mult.commute mult.left_neutral 
   one_smult_vec right_inverse smult_smult_assoc)+

lemma equiv_assoc:"equiv_vectors v1 v2 \<Longrightarrow>
                   equiv_vectors v2 v3 \<Longrightarrow>
                   equiv_vectors v1 v3"
  unfolding equiv_vectors_def apply auto
  by (metis abs_1 abs_minus abs_mult mult_minus1_right smult_smult_assoc)

lemma "\<bar>c::complex\<bar> = 1 = (\<bar>inverse c\<bar> = 1)"
  by auto

lemma sca_mult_qstate_one: "x = 1 \<cdot>\<^sub>q x"
  unfolding sca_mult_qstate_def apply auto
  by (metis QState.rep_eq QState_list.rep_eq QState_vars.rep_eq 
         QState_vector.rep_eq 
      QState_wf list_vec prod.exhaust_sel uQState_inject)

definition equiv_qstate::"QState \<Rightarrow> QState \<Rightarrow> bool"
  where "equiv_qstate k l \<equiv> \<exists>c. k = c \<cdot>\<^sub>q l \<and> \<bar>c\<bar> = 1 "



lemma equiv_qstate_sym:"equiv_qstate k l = equiv_qstate l k"
  unfolding equiv_qstate_def sca_mult_qstate_def
  apply transfer'
  apply auto
  sorry

quotient_type (overloaded) QState_equiv = "QState" /
  equiv_qstate
  morphisms rep QState  
  apply (rule equivpI)
    apply (rule reflpI)
  using sca_mult_qstate_one  
    apply (auto simp add: equiv_qstate_def intro: abs_1)[1]
  using equiv_qstate_sym
  apply (simp add: symp_def)  
  sorry

*)
lemma eq_tensor_inverse_1':
  assumes a0:"vs1 \<inter> vs2 = {}" and a1:"finite vs1" and a2:"finite vs2" and              
              a3:"ptensor_vec vs1 vs2 (v1::complex vec) v2 = 
                  ptensor_vec vs1 vs2 v1' v2'" and
              a4:"ptensor_vec vs1 vs2 v1 v2 \<noteq> 0\<^sub>v (2^card(vs1 \<union> vs2))" and
              a5:"dim_vec v1 = 2 ^ card vs1" and a6:"dim_vec v1' = 2 ^ card vs1" and
              a7:"dim_vec v2 = 2 ^ card vs2" and a8:"dim_vec v2' = 2 ^ card vs2" and
              a9:"vs1 = {}" 
            shows "\<exists>k. k\<noteq> 0 \<and> v1 = k \<cdot>\<^sub>v v1' \<and> v2 = inverse k \<cdot>\<^sub>v v2'"
proof-  
  obtain i where "i < dim_vec v1" and "v1$i\<noteq>0" and "v1 = (v1$ i * inverse (v1'$i))\<cdot>\<^sub>v v1'"
    using exists_k_v1_prod_scalar_k_v1'[OF a0 a1 a2 a3 a4 a5 a6] by auto
  moreover have "i=0" using a9 a5 a6 calculation
    by (metis One_nat_def assms(10) card.empty less_Suc0 power.simps(1))
  then have "v1$ i * inverse (v1'$i) \<noteq> 0"
    using a6 calculation(2) calculation(3) by force
  moreover obtain j where "j < dim_vec v2" and "v2$j\<noteq>0" and "v2 = (v2$ j * inverse (v2'$j))\<cdot>\<^sub>v v2'"
    using exists_k_v2_prod_scalar_k_v2'[OF a0 a1 a2 a3 a4 a7 a8] by auto
  moreover have  "v1$ i * inverse (v1'$i) = v2'$ j * inverse (v2$j)"
    using v1_div_v1'_eq_v2'_div_v2[OF a0 a1 a2 a4 a3] calculation
    by (metis a5 a7)
  then have "v2$ j * inverse (v2'$j) = inverse (v1$ i * inverse (v1'$i))"
    using calculation by auto
  moreover have "v1$ i * inverse (v1'$i) \<noteq> 0" using calculation by auto
  ultimately show ?thesis 
    by metis 
qed

lemma eq_tensor_inverse_1'':
  assumes a0:"vs1 \<inter> vs2 = {}" and a1:"finite vs1" and a2:"finite vs2" and              
              a3:"ptensor_vec vs1 vs2 (v1::complex vec) v2 = 
                  ptensor_vec vs1 vs2 v1' v2'" and
              a4:"ptensor_vec vs1 vs2 v1 v2 \<noteq> 0\<^sub>v (2^card(vs1 \<union> vs2))" and
              a5:"dim_vec v1 = 2 ^ card vs1" and a6:"dim_vec v1' = 2 ^ card vs1" and
              a7:"dim_vec v2 = 2 ^ card vs2" and a8:"dim_vec v2' = 2 ^ card vs2" and
              a9:"vs2 = {}"
            shows "\<exists>k. k\<noteq> 0 \<and> v1 = k \<cdot>\<^sub>v v1' \<and> v2 = inverse k \<cdot>\<^sub>v v2'"
proof-  
  obtain i where "i < dim_vec v1" and "v1$i\<noteq>0" and "v1 = (v1$ i * inverse (v1'$i))\<cdot>\<^sub>v v1'"
    using exists_k_v1_prod_scalar_k_v1'[OF a0 a1 a2 a3 a4 a5 a6] by auto
  moreover obtain j where "j < dim_vec v2" and "v2$j\<noteq>0" and "v2 = (v2$ j * inverse (v2'$j))\<cdot>\<^sub>v v2'"
    using exists_k_v2_prod_scalar_k_v2'[OF a0 a1 a2 a3 a4 a7 a8] by auto
  moreover have "j=0" using a9 a6 a7 calculation
    by (metis One_nat_def assms(10) card.empty less_Suc0 power.simps(1))
  then have "v2$ j * inverse (v2'$j) \<noteq>0"
    using calculation by fastforce
  moreover have  "v1$ i * inverse (v1'$i) = v2'$ j * inverse (v2$j)"
    using v1_div_v1'_eq_v2'_div_v2[OF a0 a1 a2 a4 a3] calculation
    by (metis a5 a7)
  then have "v2$ j * inverse (v2'$j) = inverse (v1$ i * inverse (v1'$i))"
    using calculation by auto
  moreover have "v1$ i * inverse (v1'$i) \<noteq> 0" using calculation
     \<open>j = 0\<close> 
    using calculation(7) calculation(8) by force  
  ultimately show ?thesis 
    by metis 
qed

lemma eq_tensor_inverse':
  assumes a0:"vs1 \<inter> vs2 = {}" and a1:"finite vs1" and a2:"finite vs2" and              
              a3:"ptensor_vec vs1 vs2 (v1::complex vec) v2 = 
                  ptensor_vec vs1 vs2 v1' v2'" and
              a4:"ptensor_vec vs1 vs2 v1 v2 \<noteq> 0\<^sub>v (2^card(vs1 \<union> vs2))" and
              a5:"dim_vec v1 = 2 ^ card vs1" and a6:"dim_vec v1' = 2 ^ card vs1" and
              a7:"dim_vec v2 = 2 ^ card vs2" and a8:"dim_vec v2' = 2 ^ card vs2"               
            shows "\<exists>k. k\<noteq> 0 \<and> v1 = k \<cdot>\<^sub>v v1' \<and> v2 = inverse k \<cdot>\<^sub>v v2'"
  using eq_tensor_inverse_1[OF assms] eq_tensor_inverse_1'[OF assms] eq_tensor_inverse_1''[OF assms]
  by blast 

lemma "a\<ge>0 \<Longrightarrow> (a::complex) > 0 \<or> a = 0"
  using le_less by blast

lemma "a\<le>0 \<Longrightarrow> (a::complex) < 0 \<or> a = 0"
  using le_less by blast
  
  
lemma "(a::complex) \<ge> 0 \<or> (a::complex) \<le> 0"
  apply auto 
  oops


lemma eq_tensor_inverse_2:
  assumes a0:"vs1 \<inter> vs2 = {}" and a1:"finite vs1" and a2:"finite vs2" and              
        a3:"ptensor_vec vs1 vs2 (v1::('a::field) vec) v2 = 
            ptensor_vec vs1 vs2 v1' v2'" and
        a4:"ptensor_vec vs1 vs2 v1 v2 \<noteq> 0\<^sub>v (2^card(vs1 \<union> vs2))" and
        a5:"dim_vec v1 = 2 ^ card vs1" and a6:"dim_vec v1' = 2 ^ card vs1" and
        a7:"dim_vec v2 = 2 ^ card vs2" and a8:"dim_vec v2' = 2 ^ card vs2"
      shows "\<exists>k. k\<noteq>0 \<and> v1' = k \<cdot>\<^sub>v v1 \<and> v2' = inverse k \<cdot>\<^sub>v v2" 
  using a0 a1 a2 a3 a4 a5 a6 a7 a8 
  by (auto simp add: eq_tensor_inverse_1)

lemma eq_tensor_inverse_2':
  assumes a0:"vs1 \<inter> vs2 = {}" and a1:"finite vs1" and a2:"finite vs2" and              
        a3:"ptensor_vec vs1 vs2 (v1:: complex vec) v2 = 
            ptensor_vec vs1 vs2 v1' v2'" and
        a4:"ptensor_vec vs1 vs2 v1 v2 \<noteq> 0\<^sub>v (2^card(vs1 \<union> vs2))" and
        a5:"dim_vec v1 = 2 ^ card vs1" and a6:"dim_vec v1' = 2 ^ card vs1" and
        a7:"dim_vec v2 = 2 ^ card vs2" and a8:"dim_vec v2' = 2 ^ card vs2" and       a9:"vs1 = {}" 
      shows "\<exists>k. k\<noteq>0 \<and> v1' = k \<cdot>\<^sub>v v1 \<and> v2' = inverse k \<cdot>\<^sub>v v2 " 
  using a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 
  using eq_tensor_inverse_1' by auto

lemma eq_tensor_inverse_2'':
  assumes a0:"vs1 \<inter> vs2 = {}" and a1:"finite vs1" and a2:"finite vs2" and              
        a3:"ptensor_vec vs1 vs2 (v1:: complex vec) v2 = 
            ptensor_vec vs1 vs2 v1' v2'" and
        a4:"ptensor_vec vs1 vs2 v1 v2 \<noteq> 0\<^sub>v (2^card(vs1 \<union> vs2))" and
        a5:"dim_vec v1 = 2 ^ card vs1" and a6:"dim_vec v1' = 2 ^ card vs1" and
        a7:"dim_vec v2 = 2 ^ card vs2" and a8:"dim_vec v2' = 2 ^ card vs2" and
       a9:"vs2 = {}"
      shows "\<exists>k. k\<noteq>0 \<and> v1' = k \<cdot>\<^sub>v v1 \<and> v2' = inverse k \<cdot>\<^sub>v v2" 
  using a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 
  using eq_tensor_inverse_1'' by auto

lemma eq_tensor_inverse:
  assumes a0:"vs1 \<inter> vs2 = {}" and a1:"finite vs1" and a2:"finite vs2" and              
        a3:"ptensor_vec vs1 vs2 (v1:: complex vec) v2 = 
            ptensor_vec vs1 vs2 v1' v2'" and
        a4:"ptensor_vec vs1 vs2 v1 v2 \<noteq> 0\<^sub>v (2^card(vs1 \<union> vs2))" and
        a5:"dim_vec v1 = 2 ^ card vs1" and a6:"dim_vec v1' = 2 ^ card vs1" and
        a7:"dim_vec v2 = 2 ^ card vs2" and a8:"dim_vec v2' = 2 ^ card vs2" 
  shows "\<exists>k. k\<noteq> 0 \<and> v1' = k \<cdot>\<^sub>v v1 \<and> v2' = inverse k \<cdot>\<^sub>v v2"
  using eq_tensor_inverse_2[OF assms] eq_tensor_inverse_2'[OF assms] eq_tensor_inverse_2''[OF assms]
  by blast 

lemma  disjoint_vars_ptensor:
  assumes a0:"Q1 ## Q2"
  shows "QState_vector (Q1 + Q2) = 
         ptensor_vec (QState_vars Q1) (QState_vars Q2)  
              (QState_vector Q1) (QState_vector Q2)"
proof-
  have f0:"QState_vars Q1 \<inter> QState_vars Q2 = {}"
    by (meson a0 disj_QState_def sep_disj_QState) 
  then show ?thesis using a0 f0 unfolding  plus_QState plus_QState_def Let_def     
    apply transfer'  
    apply (auto  simp add: QState_wf_def dim_vec_plus_2_pow_s plus_QState_vector_set_finite f0 plus_QState_vector_vector QState_list_Plus vec_list)           
   using plus_QState_vector_vars plus_QState_vector_wf' apply auto
   by (metis plus_QState_vector_vector plus_QState_vector_wf_not_zero vec_list vec_of_list_index)
qed

lemma eq_tensor_inverse_QState_vector: 
  assumes a0:"Q1 ## Q2" and
       a1:"QState_vars Q1 = QState_vars Q1'" and
       a2:"QState_vars Q2 = QState_vars Q2'" and
       a3:"Q1 + Q2 = Q1' + Q2'" 
     shows "\<exists>k. k \<noteq> 0 \<and> (QState_vector Q1') = k \<cdot>\<^sub>v(QState_vector Q1) \<and> 
                (QState_vector Q2') = inverse k \<cdot>\<^sub>v(QState_vector Q2)"
proof-
  have f0:"QState_vars Q1 \<inter> QState_vars Q2 = {}"
    by (meson a0 disj_QState_def sep_disj_QState)
  have f1:"finite (QState_vars Q1)" and f2:"finite (QState_vars Q2)"
    using QState_rel3' apply presburger
    using QState_rel3' by auto
  have f3:"ptensor_vec (QState_vars Q1) (QState_vars Q2)  
                             (QState_vector Q1) (QState_vector Q2) = 
                 ptensor_vec (QState_vars Q1) (QState_vars Q2)  
                             (QState_vector Q1') (QState_vector Q2')"    
    by (metis QState_list_Plus a1 a2 a3 f0 plus_QState plus_QState_vector_vector vec_list)
  have f5:"dim_vec (QState_vector Q1) = 2^card(QState_vars Q1)" and 
       f6:"dim_vec (QState_vector Q1') = 2^card(QState_vars Q1)" and
       f7:"dim_vec (QState_vector Q2) = 2^card(QState_vars Q2)" and 
       f8:"dim_vec (QState_vector Q2') = 2^card(QState_vars Q2)"       
    using QState_rel1a' a1 a2 by auto
  have "QState_vector (Q1 + Q2) \<noteq>  0\<^sub>v (2^card((QState_vars Q1) \<union> (QState_vars Q2)))"
    by (metis a0 disjoint_vars_ptensor f0 index_zero_vec(1) list_of_vec_index 
              plus_QState_vector_vars plus_QState_vector_vector 
              plus_QState_vector_wf_not_zero)     
  then have f4:"ptensor_vec (QState_vars Q1) (QState_vars Q2) (QState_vector Q1) (QState_vector Q2) \<noteq>  
           0\<^sub>v (2^card((QState_vars Q1) \<union> (QState_vars Q2)))"
    using disjoint_vars_ptensor[OF a0]  by auto
  show ?thesis using eq_tensor_inverse[OF f0 f1 f2 f3 f4 f5 f6 f7 f8]
    by fastforce    
qed

lemma eq_tensor_inverse_QState: 
  assumes a0:"Q1 ## Q2" and
       a1:"QState_vars Q1 = QState_vars Q1'" and
       a2:"QState_vars Q2 = QState_vars Q2'" and
       a3:"Q1 + Q2 = Q1' + Q2'" 
     shows "\<exists>k. k \<noteq> 0 \<and> Q1' = k \<cdot>\<^sub>q Q1 \<and> Q2' = inverse k \<cdot>\<^sub>q Q2"
  using eq_tensor_inverse_QState_vector[OF a0 a1 a2 a3] 
  by (metis QState_list.rep_eq QState_refl QState_vector.rep_eq a1 a2 list_vec sca_mult_qstate_def)


lemma eq_tensor_inverse_QState_wf: 
  assumes a0:"Q1 ## Q2" and
       a1:"QState_vars Q1 = QState_vars Q1'" and
       a2:"QState_vars Q2 = QState_vars Q2'" and
       a3:"Q1 + Q2 = Q1' + Q2'" 
     shows "\<exists>k. k\<noteq>0 \<and> Q1' = k \<cdot>\<^sub>q Q1 \<and> Q2' = inverse k \<cdot>\<^sub>q Q2 \<and> 
               QState_wf (QState_vars Q1', list_of_vec (k \<cdot>\<^sub>v (QState_vector Q1))) \<and>
               QState_wf (QState_vars Q2', list_of_vec (inverse k \<cdot>\<^sub>v (QState_vector Q2)))"
proof-
  obtain k where k:"k \<noteq> 0" and "Q1' = k \<cdot>\<^sub>q Q1 \<and> Q2' = inverse k \<cdot>\<^sub>q Q2" 
    using eq_tensor_inverse_QState[OF a0 a1 a2 a3] by auto
  moreover have " QState_wf (QState_vars Q1', list_of_vec (k \<cdot>\<^sub>v (QState_vector Q1)))"   
    using sca_mult_qstate_wf a1 calculation by metis
  moreover have "(inverse k) \<noteq>0"
    using a2 calculation(2) k by force     
  then have "QState_wf (QState_vars Q2', list_of_vec (inverse k \<cdot>\<^sub>v (QState_vector Q2)))"   
    using sca_mult_qstate_wf a2 calculation
    by metis
  ultimately show ?thesis by blast
qed


lemma QState_plus_intro:assumes a0:"vars1 \<inter> vars2 = {}" and a1:"QState_wf (vars1, v1)" and a2:"QState_wf (vars2, v2)" and
       a3:"QState_vars \<Q> = vars1 + vars2" and
       a4:"QState_vector \<Q> = ptensor_vec vars1 vars2 (vec_of_list v1) (vec_of_list v2)" 
     shows "QState(vars1, v1) + QState(vars2, v2) = \<Q>"
proof-
  have "QState(vars1, v1) + QState(vars2, v2) = 
        QState(vars1 \<union> vars2, list_of_vec(ptensor_vec vars1 vars2 (vec_of_list v1) (vec_of_list v2)))"
    unfolding  plus_QState plus_QState_def plus_QState_vector_def Let_def
      apply auto
    using QState_var_idem a0 local.a1 local.a2 apply auto[1]    
    using QState.rep_eq QState_var_idem QState_vector.rep_eq local.a1 local.a2 by auto 
  thus ?thesis
    by (metis QState_list.rep_eq QState_refl QState_vector.rep_eq a3 a4 list_vec plus_set_def)
qed



lemma scalar_mult_QState_plus_l:
  assumes a0: "a\<noteq>0" and 
          a1:"Q' ## Q''"
        shows "a  \<cdot>\<^sub>q (Q' + Q'') = (a  \<cdot>\<^sub>q Q' + Q'')"
proof-
  let ?q'vs = "QState_vars Q'" and ?q''vs = "QState_vars Q''" and
      ?q'v = "QState_vector Q'" and ?q''v = "QState_vector Q''"
  note a1 = a1[simplified disj_QState_def sep_disj_QState]
  have "QState_vars (a  \<cdot>\<^sub>q (Q' + Q'')) = QState_vars (Q' + Q'')"
    by (simp add: a0 sca_mult_qstate_vars)
  moreover have "QState_vector (a  \<cdot>\<^sub>q (Q' + Q'')) = a \<cdot>\<^sub>v (QState_vector (Q' + Q''))"
    by (meson a0 sca_mult_qstate_quantum)  
  moreover have "a \<cdot>\<^sub>v (QState_vector (Q' + Q'')) = 
                 a \<cdot>\<^sub>v (ptensor_vec ?q'vs ?q''vs ?q'v ?q''v)"
    using a1 
    unfolding plus_QState_vector_def disj_QState_def sep_disj_QState plus_QState plus_QState_def Let_def sca_mult_qstate_def
    apply auto    
    by (metis QState_list_Plus QState_vector.rep_eq plus_QState_def plus_QState_vector_def plus_QState_vector_vector uqstate_snd vec_list)
  then have " a \<cdot>\<^sub>v (QState_vector (Q' + Q'')) = 
                  (ptensor_vec ?q'vs ?q''vs (a \<cdot>\<^sub>v ?q'v) ?q''v)" 
    by (simp add:pscalar_ptensor_1[OF a1] QState_rel1' QState_rel3' QState_vector.rep_eq uqstate_snd)   
  moreover have  "QState_vars (a  \<cdot>\<^sub>q Q' + Q'') = QState_vars (Q' + Q'')"
    by (metis (no_types, lifting) QState_vars_Plus a0 plus_QState plus_QState_vector_vars sca_mult_qstate_vars)
  moreover have "QState_vector (a  \<cdot>\<^sub>q Q' + Q'') =  
                 ptensor_vec ?q'vs ?q''vs (a  \<cdot>\<^sub>v ?q'v) ?q''v"
    using calculation(3)
    by (smt QState_vars_Plus a0 a1  plus_QState plus_QState_def 
            plus_QState_vector_def plus_QState_vector_vars 
            sca_mult_qstate_def sca_mult_qstate_quantum sca_mult_qstate_vars)
  ultimately show ?thesis
    by (metis QState_refl QState_vector.rep_eq list_vec uqstate_snd)
qed


lemma scalar_mult_QState_plus_r: 
  assumes a0: "a \<noteq> 0" and 
          a1:"Q' ## Q''" 
  shows "a  \<cdot>\<^sub>q (Q' + Q'') = ( Q' + a  \<cdot>\<^sub>q Q'')"
proof-      
let ?q'vs = "QState_vars Q'" and ?q''vs = "QState_vars Q''" and
      ?q'v = "QState_vector Q'" and ?q''v = "QState_vector Q''"
  note a1 = a1[simplified disj_QState_def sep_disj_QState]
  have "QState_vars (a  \<cdot>\<^sub>q (Q' + Q'')) = QState_vars (Q' + Q'')"
    by (simp add: a0 sca_mult_qstate_vars)
  moreover have "QState_vector (a  \<cdot>\<^sub>q (Q' + Q'')) = a \<cdot>\<^sub>v (QState_vector (Q' + Q''))"
    by (meson a0 sca_mult_qstate_quantum)  
  moreover have "a \<cdot>\<^sub>v (QState_vector (Q' + Q'')) = 
                 a \<cdot>\<^sub>v (ptensor_vec ?q'vs ?q''vs ?q'v ?q''v)"
    using a1 
    unfolding plus_QState_vector_def disj_QState_def sep_disj_QState plus_QState plus_QState_def Let_def sca_mult_qstate_def
    apply auto    
    by (metis QState_list_Plus QState_vector.rep_eq plus_QState_def plus_QState_vector_def plus_QState_vector_vector uqstate_snd vec_list)
  then have " a \<cdot>\<^sub>v (QState_vector (Q' + Q'')) = 
                  (ptensor_vec ?q'vs ?q''vs ?q'v (a \<cdot>\<^sub>v ?q''v))" 
    by (simp add:pscalar_ptensor_2[OF a1] QState_rel1' QState_rel3' QState_vector.rep_eq uqstate_snd)   
  moreover have  "QState_vars (Q' + a  \<cdot>\<^sub>q Q'') = QState_vars (Q' + Q'')"
    by (metis (no_types, lifting) QState_vars_Plus a0 plus_QState plus_QState_vector_vars sca_mult_qstate_vars)
  moreover have "QState_vector (Q' + a  \<cdot>\<^sub>q Q'') =  
                 ptensor_vec ?q'vs ?q''vs ?q'v (a  \<cdot>\<^sub>v ?q''v)"
    using calculation(3) 
    by (smt QState_vars_Plus a0 a1  plus_QState plus_QState_def 
            plus_QState_vector_def plus_QState_vector_vars 
            sca_mult_qstate_def sca_mult_qstate_quantum sca_mult_qstate_vars)
  ultimately show ?thesis
    by (metis QState_refl QState_vector.rep_eq list_vec uqstate_snd)
qed

definition equiv_vectors::"complex vec \<Rightarrow> complex vec \<Rightarrow> bool"
  where "equiv_vectors v1 v2 \<equiv> \<exists>c. v1 = c \<cdot>\<^sub>v v2 \<and> \<bar>c\<bar> = 1"

lemma equiv_comm:"equiv_vectors v1 v2 = equiv_vectors v2 v1"
  unfolding equiv_vectors_def apply auto
  by (metis abs_0 abs_mult mult.commute mult.left_neutral 
   one_smult_vec right_inverse smult_smult_assoc)+

lemma equiv_assoc:"equiv_vectors v1 v2 \<Longrightarrow>
                   equiv_vectors v2 v3 \<Longrightarrow>
                   equiv_vectors v1 v3"
  unfolding equiv_vectors_def apply auto
  by (metis abs_1 abs_minus abs_mult mult_minus1_right smult_smult_assoc)

lemma "\<bar>c::complex\<bar> = 1 = (\<bar>inverse c\<bar> = 1)"
  by auto

definition equiv_qstate::"QState \<Rightarrow> QState \<Rightarrow> bool"
  where "equiv_qstate k l \<equiv> \<exists>c. k = c \<cdot>\<^sub>q l \<and> \<bar>c\<bar> = 1 "

lemma sca_mult_qstate_one: "x = 1 \<cdot>\<^sub>q x"
  unfolding sca_mult_qstate_def apply auto
  by (metis QState.rep_eq QState_list.rep_eq QState_vars.rep_eq 
         QState_vector.rep_eq 
      QState_wf list_vec prod.exhaust_sel uQState_inject)

lemma equiv_qstate_sym:"equiv_qstate k l = equiv_qstate l k"
  unfolding equiv_qstate_def 
  apply auto
  apply (metis abs_0 abs_mult mult.commute mult.left_neutral right_inverse sca_mult_qstate_assoc sca_mult_qstate_one)
  by (metis abs_0 abs_mult mult.commute mult.left_neutral 
        right_inverse sca_mult_qstate_def sca_mult_qstate_one 
      sca_mult_qstate_quantum sca_mult_qstate_vars smult_smult_assoc)

quotient_type (overloaded) QState_equiv = "QState" /
  equiv_qstate 
  morphisms rep QState_equiv  
  apply (rule equivpI)
    apply (rule reflpI)
  using sca_mult_qstate_one  
    apply (auto simp add: equiv_qstate_def intro: abs_1)[1]
  using equiv_qstate_sym
   apply (simp add: symp_def)  
  apply (auto simp add: transp_def equiv_qstate_def)
  by (metis abs_0 abs_mult mult.left_neutral sca_mult_qstate_assoc zero_neq_one)
  

quotient_definition "sca_mult :: complex \<Rightarrow> QState_equiv \<Rightarrow> QState_equiv"
is "sca_mult_qstate" unfolding equiv_qstate_def  
  apply auto
  by (smt (verit, best) abs_1 abs_eq_0_iff mult.commute 
          mult_zero_right sca_mult_qstate_def 
          sca_mult_qstate_one sca_mult_qstate_quantum 
   sca_mult_qstate_vars smult_smult_assoc)


type_synonym q_vars = "(nat \<Rightarrow>nat set)"
type_synonym qstate = "q_vars \<times>  QState"

definition Q_domain::"q_vars \<Rightarrow> nat set" 
  where "Q_domain q_vars \<equiv> \<Union> (range q_vars)"

definition ket_dim ::"q_vars \<Rightarrow> nat"
  where "ket_dim q_vars \<equiv>  card (Q_domain q_vars)"

definition Q_domain_var::"nat set \<Rightarrow> q_vars \<Rightarrow> nat set "
  where "Q_domain_var q qvars \<equiv> \<Union> (qvars ` q)"

definition Q_domain_set::"('s \<Rightarrow> nat set) \<Rightarrow> q_vars \<Rightarrow> ('s \<Rightarrow> nat set)"
  where "Q_domain_set q qvars \<equiv> (\<lambda>s. \<Union> (qvars ` q s))"

\<comment>\<open>\<close>
abbreviation QStateM_wf::"q_vars \<times>  QState \<Rightarrow> bool"
  where "QStateM_wf s \<equiv> 
        Q_domain (fst s) = QState_vars (snd s) \<and>
        (\<forall>x y. x\<noteq>y \<and> x\<in> domain (fst s) \<and> y \<in> domain (fst s) \<longrightarrow> (fst s) x \<inter> (fst s) y = {})"


typedef 
  QStateM = "{(m,q)| (m::q_vars) (q:: QState). QStateM_wf (m,q)}"
  morphisms uQStateM Abs_QStateM              
  unfolding Q_domain_def  apply auto apply transfer
  apply (rule exI[where x ="\<lambda>x. {}"], auto)
  by (rule exI[where x ="[1]"], auto)


setup_lifting type_definition_QStateM

lift_definition QStateM_map :: "QStateM \<Rightarrow> q_vars" is fst .

lemma finite_Q_domain_var:"finite (Q_domain_var q (QStateM_map \<Q>))"
  unfolding Q_domain_var_def apply transfer apply auto unfolding Q_domain_def 
  using QState_rel3'
  by (metis UNIV_I UN_Un UnCI finite_Un subsetI subset_antisym) 

abbreviation empty_map::"q_vars" ("{}\<^sub>q")
  where "empty_map \<equiv> (\<lambda>n. {})"

definition qstate :: "QStateM \<Rightarrow> QState" 
  where "qstate s \<equiv> snd (uQStateM s)"

lift_definition QStateM_vars::"QStateM \<Rightarrow> nat set" is "(\<lambda>s. QState_vars (snd s))" .
lift_definition QStateM_list::"QStateM \<Rightarrow> complex list" is "(\<lambda>s. QState_list (snd s))" .
lift_definition QStateM_vector::" QStateM \<Rightarrow> complex vec" is "(\<lambda>s. QState_vector (snd s))" .

lift_definition QStateM ::"q_vars \<times>  QState \<Rightarrow> QStateM" is
"\<lambda>s. if QStateM_wf s then (fst s, snd s) else (\<lambda>s. {}, QState ({},[1]))"
  unfolding Q_domain_def by (auto simp add:  QState_vars_empty)

definition constrain_map::"q_vars \<Rightarrow> nat set \<Rightarrow> q_vars"
  where "constrain_map m q \<equiv> (\<lambda>x. if x \<in> q then m x else none)"

definition split_map::"q_vars \<Rightarrow> nat set \<Rightarrow> q_vars \<times> q_vars"
  where "split_map q_vars q \<equiv> (constrain_map q_vars q, constrain_map q_vars (-q))"

lemma q_map_split:"\<forall>e\<in>q. q_map e \<noteq> {} \<Longrightarrow> 
       q_map = fst (split_map q_map q) + snd (split_map q_map q)"
  unfolding split_map_def constrain_map_def none_def plus_fun_def apply auto  
proof -
  have "\<forall>n na. n \<in> q \<and> na \<notin> q \<and> q_map na \<noteq> {} \<or> 
               n \<in> q \<and> fst (\<lambda>n. if n \<in> q then q_map n else {}, 
                            \<lambda>n. if n \<in> - q then q_map n else {}) na = q_map na \<or> 
              snd (\<lambda>n. if n \<in> q then q_map n else {}, 
                               \<lambda>n. if n \<in> - q then q_map n else {}) n = q_map n \<and>
                 na \<notin> q \<and> q_map na \<noteq> {} \<or> 
              snd (\<lambda>n. if n \<in> q then q_map n else {}, 
                       \<lambda>n. if n \<in> - q then q_map n else {}) n = q_map n \<and> 
              fst (\<lambda>n. if n \<in> q then q_map n else {}, 
                   \<lambda>n. if n \<in> - q then q_map n else {}) na = q_map na"
    by simp
  then show "q_map = 
             (\<lambda>n. if (if n \<notin> q then q_map n else {}) = {} then 
                  fst (\<lambda>n. if n \<in> q then q_map n else {}, 
                       \<lambda>n. if n \<in> - q then q_map n else {}) n else 
                  snd (\<lambda>n. if n \<in> q then q_map n else {}, 
                           \<lambda>n. if n \<in> - q then q_map n else {}) n)"
  by (metis (no_types))
qed 

lemma q_map_int:"\<forall>e\<in>q. q_map e \<noteq> {} \<Longrightarrow> 
       fst (split_map q_map q) ## snd (split_map q_map q)"
  unfolding split_map_def constrain_map_def none_def plus_fun_def sep_disj_fun_def domain_def
  by auto

lemma q_var_inter_empty:
  " \<forall>x y. x\<in> domain q_map \<and> y \<in> domain q_map \<and> x\<noteq>y  \<longrightarrow> q_map x \<inter> q_map y = {} \<Longrightarrow>
     q  \<inter> qr  = {} \<Longrightarrow>   
     Q_domain_var q q_map \<inter> 
     Q_domain_var qr q_map = {}"
  unfolding Q_domain_var_def domain_def Q_domain_def by auto

lemma q_var_in_q1_q2: assumes      
      a2:"Q_domain q_map = Q_domain_var (q1 \<union> q2) q_map" and
      a3:"q_map x \<noteq> {}" and a4:"\<forall>x y. x\<in> domain q_map \<and> y \<in> domain q_map \<and> x\<noteq>y  \<longrightarrow> q_map x \<inter> q_map y = {}"
    shows "x \<in> q1 \<or> x \<in> q2"
proof-
  obtain xa where a3:"xa \<in> q_map x" using a3 by auto
  have f4: "\<forall>N. - (N::nat set) \<inter> N = {}"
    by simp
  have "xa \<in> \<Union> (range q_map)"
    using a3 by blast
  then have "xa \<notin> \<Union> (q_map ` (- (q1 \<union> q2)))"
    using f4 using  a2   a3      
    unfolding  Q_domain_def Q_domain_var_def 
    by (metis Q_domain_var_def disjoint_iff_not_equal q_var_inter_empty[OF a4])
  then show ?thesis using a3
    by blast
qed

lemma split_q1_constrain_q2:
  assumes a0:"q1 \<inter> q2 = {}" and 
              a2:"\<forall>x y. x\<in> domain q_map \<and> y \<in> domain q_map \<and> x\<noteq>y  \<longrightarrow> q_map x \<inter> q_map y = {}" and
              a3:"q_vars = Q_domain_var (q1 \<union> q2) q_map" and 
              a4:"Q_domain q_map = q_vars"
  shows "snd (split_map q_map q1) = constrain_map q_map q2"
proof-
  have "q2 \<subseteq> -q1"
    using a0 by blast
  moreover have "\<forall>x. x \<notin> q1 \<and> x \<notin> q2 \<longrightarrow> q_map x = {}"
    apply auto using q_var_in_q1_q2
    using a4 a2 a3 by blast
  ultimately show ?thesis 
    unfolding split_map_def constrain_map_def none_def apply auto
    by (metis IntI a0 empty_iff)     
qed

lemma q_vars_q2: assumes 
      a0:"q1 \<inter> q2 = {}" and
      a1:"\<forall>x y. x\<in> domain q_map \<and> y \<in> domain q_map \<and> x\<noteq>y  \<longrightarrow> q_map x \<inter> q_map y = {}" and
      a2:"q_vars = Q_domain_var (q1 \<union> q2) q_map" and      
      a3:"Q_domain q_map = q_vars" and       
      a4:"v1 = Q_domain_var q1 q_map" and  
      a5:"v2 = Q_domain_var q2 q_map"
    shows "v2 = q_vars - v1"
proof-
  note split = split_q1_constrain_q2[OF a0 a1 a2 a3]
  note q_var_inter = q_var_inter_empty[OF a1 a0]
  show ?thesis using split q_var_inter
    using Q_domain_var_def a4 a5 a2 by auto         
qed

lemma q_domain_constrain_eq_q_domain_var:
 "Q_domain (constrain_map q_map q) = Q_domain_var q q_map"
  unfolding Q_domain_def Q_domain_var_def constrain_map_def
  by auto

lemma q_domain_split_eq_q_domain_var:
 "Q_domain (fst (split_map q_map q)) = Q_domain_var q q_map"
  unfolding split_map_def Q_domain_def Q_domain_var_def constrain_map_def
  by auto

lemma constrain_map_wf1:
   "\<forall>x y. x\<noteq>y \<and> x\<in> domain q_map \<and> y \<in> domain q_map \<longrightarrow> q_map x \<inter> q_map y = {} \<Longrightarrow>
       \<forall>x y. x \<noteq> y \<and>
          x \<in> opt_class.domain (constrain_map q_map q) \<and>
          y \<in> opt_class.domain (constrain_map q_map q) \<longrightarrow> 
          (constrain_map q_map q) x \<inter>
          (constrain_map q_map q) y = {}"
  unfolding constrain_map_def
  apply auto
  using opt_class.domain_def by fastforce

abbreviation QStateM_unfold::"QStateM \<Rightarrow> (q_vars \<times>  QState)"
  where "QStateM_unfold q \<equiv> (QStateM_map q, qstate q)"

lemma vec_of_list_QStateM_list:"QStateM_vector Q = vec_of_list (QStateM_list Q)"
  by (simp add: QStateM_list.rep_eq QStateM_vector.rep_eq QState_list.rep_eq QState_vector.rep_eq)

lemma list_of_vec_QStateM_vec:"QStateM_list Q = list_of_vec (QStateM_vector Q)"
  by (simp add: list_vec vec_of_list_QStateM_list)

lemma list_of_vec_elim:"list_of_vec Q = list_of_vec Q1 \<Longrightarrow> Q = Q1"
  by (metis vec_list)


lemma eq_QStateM_vars:"QState_vars (snd (QStateM_unfold q)) = QStateM_vars q"
  unfolding qstate_def
  by (transfer, auto)

lemma QStateM_wf:"QStateM_wf (QStateM_unfold x)"
  unfolding qstate_def  apply transfer by fastforce

lemma QStateM_wf_map:"QStateM_wf (vs, v) \<Longrightarrow> QStateM_map (QStateM (vs, v)) = vs"
  by (transfer, auto)

lemma QStateM_wf_qstate:"QStateM_wf (vs, v) \<Longrightarrow> qstate (QStateM (vs, v)) = v"
  unfolding qstate_def by (transfer, auto)

lemma QStateM_wf_vars:"QStateM_wf (vs, v) \<Longrightarrow> QStateM_vars (QStateM (vs, v)) = QState_vars v"
  apply transfer'
  by simp

lemma QStateM_wf_list:"QStateM_wf (vs, v) \<Longrightarrow> QStateM_list (QStateM (vs, v)) = QState_list v"
  apply transfer'
  by simp

lemma QStateM_rel1:"Q_domain (QStateM_map x) = QState_vars (qstate x)" 
  unfolding qstate_def  apply transfer by fastforce

lemma QStateM_rel2:
   "x\<in> domain (QStateM_map s) \<and> y \<in> domain (QStateM_map s) \<and> x\<noteq>y \<longrightarrow> 
    (QStateM_map s) x \<inter> (QStateM_map s) y = {}" 
  apply transfer 
  by (fastforce simp add: Q_domain_def)

lemma QStateM_rel2fa:
   "\<forall>x y. x\<in> domain (QStateM_map s) \<and> y \<in> domain (QStateM_map s) \<and> x\<noteq>y \<longrightarrow> 
    (QStateM_map s) x \<inter> (QStateM_map s) y = {}" 
  apply transfer 
  by (fastforce simp add: Q_domain_def)

lemma Qstate_map_0_0:"QStateM_map (QStateM (0, 0)) = 0"
  apply transfer' apply (auto, simp add: Q_domain_def)
  apply (simp add: zero_fun_def)
  by (auto simp add: QState_vars_empty zero_QState zero_fun_def)


lemma idem_QState:"QStateM (QStateM_map x, qstate x) = x"  
  unfolding qstate_def apply transfer by fastforce


lemma eq_QStateM_dest: "Q_domain vs \<noteq> {} \<Longrightarrow> 
       QStateM_wf (vs, v) \<Longrightarrow> 
       QStateM(vs, v) = QStateM(vs', v') \<Longrightarrow> 
       vs = vs' \<and> v = v'" 
   apply transfer' apply auto
  apply (metis Pair_inject QState_vars_empty empty_iff prod.collapse)
  by (metis QState_vars_empty empty_iff snd_conv)

(* lemma eq_QStateM_dest': 
  assumes a0:"QStateM_wf (vs, v)" and 
       a1:"QStateM(vs, v) = QStateM(vs', v')" 
  shows "vs = vs' \<and> v = v'" 
proof-
  { assume "Q_domain vs \<noteq> {}" 
    then have ?thesis using eq_QStateM_dest[OF _ a0 a1] by auto
  }
  { assume "Q_domain vs = {}"
    then have "{} = QState_vars v \<and>
        (\<forall>x y. x\<noteq>y \<and> x\<in> domain vs \<and> y \<in> domain vs \<longrightarrow> vs x \<inter> vs y = {})"
      using a0 by auto
    then have ?thesis using a0 a1 unfolding Q_domain_def apply auto
      apply transfer' apply auto apply transfer' apply auto unfolding Q_domain_def apply auto
      sorry
qed *)

lemma eq_QStateM_dest1: " 
       QStateM_wf (vs, v) \<Longrightarrow> QStateM_wf (vs', v') \<Longrightarrow> 
       QStateM(vs, v) = QStateM(vs', v') \<Longrightarrow> 
       vs = vs' \<and> v = v'" 
   apply transfer' by auto


lemma eq_QStateMap_vars:
  assumes a0:"QStateM_map Q1 = QStateM_map Q2" 
  shows "QStateM_vars Q1 = QStateM_vars Q2"
  by (metis QStateM_rel1 QStateM_vars.rep_eq assms qstate_def)

lemma QStateM_eq_intro[intro]:
  assumes a0:"QStateM_map Q1 = QStateM_map Q2" and
          a1:"QStateM_list Q1 = QStateM_list Q2"
        shows "Q1 = Q2"
  by (metis QStateM_list.rep_eq QStateM_rel1 a0 a1 idem_QState q_state_eq qstate_def)

   

lemma Qstate_mapf:
  assumes a0:"Q_domain (f (QStateM_map q)) =  QState_vars (g (qstate q))" and 
          a1:"(\<forall>x y. x\<noteq>y \<and> x\<in> domain (f (QStateM_map q)) \<and> 
                      y \<in> domain (f (QStateM_map q)) \<longrightarrow> 
                     (f (QStateM_map q)) x \<inter> (f (QStateM_map q)) y = {})"
        shows "QStateM_map (QStateM (f (QStateM_map q), g (qstate q))) = 
               f (QStateM_map q)"  
  using a0 a1 apply transfer' by auto 
   

lemma Qstate_vector:
  assumes a0:"Q_domain (f (QStateM_map q)) =  QState_vars (g (qstate q))" and 
          a1:"\<forall>x y. x\<noteq>y \<and> x\<in> domain (f (QStateM_map q)) \<and> 
                      y \<in> domain (f (QStateM_map q)) \<longrightarrow> 
                     (f (QStateM_map q)) x \<inter> (f (QStateM_map q)) y = {}"
        shows "qstate (QStateM (f (QStateM_map q), g (qstate q))) = 
               g (qstate q)"  
  using a0 a1 unfolding qstate_def apply transfer' by auto
  
lemma Q_domain_unfold_rel1:
  "Q_domain (fst (QStateM_unfold q)) = QState_vars(snd (QStateM_unfold q))"
  by (simp add: QStateM_rel1)

lemma Q_domain_unfold_rel2:
  "\<forall>x y. x\<noteq>y \<and> x\<in> domain (fst (QStateM_unfold q)) \<and> 
                y \<in> domain (fst (QStateM_unfold q)) \<longrightarrow> 
        (fst (QStateM_unfold q)) x \<inter> (fst (QStateM_unfold q)) y = {}" 
  by (simp add: QStateM_rel2)

lemma q_var_in_q_qr:
  assumes 
    a0:"Q_domain (QStateM_map \<Q>) =  Q_domain_var (q \<union> qr) (QStateM_map \<Q>)" and    
    a2:"xa \<in> QStateM_map \<Q> x"
 shows "x \<in> q \<or> x \<in> qr"  using q_var_in_q1_q2
  using QStateM_rel2 a0 a2 by blast

lemma 
  assumes a0:"Q_domain (QStateM_map \<Q>) = QStateM_vars \<Q>" and
          a1:"QStateM_vars \<Q> = Q_domain_var (q \<union> qr) (QStateM_map \<Q>)"
        shows "\<forall>x. x \<notin> q  \<and> x \<notin> qr \<longrightarrow> QStateM_map \<Q> x = {}"  
  apply auto
proof -
  fix x :: nat and xa :: nat
  assume a2: "xa \<in> QStateM_map \<Q> x"
  assume a3: "x \<notin> q"
  assume a4: "x \<notin> qr"
  have "\<forall>N. xa \<in> \<Union> (QStateM_map \<Q> ` N) \<or> x \<notin> N"
    using a2 QStateM_map.rep_eq by force
  then have "x \<in> q \<union> qr"
    using a0 a1 a2 q_var_in_q_qr by fastforce
  then show False
    using a4 a3 by fastforce
qed
 

lemma domain_qr:"q  \<inter> qr  = {} \<Longrightarrow> 
       QStateM_vars \<Q> = Q_domain_var (q \<union> qr) (QStateM_map \<Q>) \<Longrightarrow>
       Q_domain_var qr (QStateM_map \<Q>) =
       Q_domain (QStateM_map \<Q>) - Q_domain_var q (QStateM_map \<Q>)"  
  apply(frule q_var_inter_empty[of "QStateM_map \<Q>", OF QStateM_rel2fa]) 
  using QStateM_rel1 unfolding Q_domain_def Q_domain_var_def   
  by (auto simp add: QStateM_vars.rep_eq qstate_def)

lemma Q_domain_var_in_vars:
  assumes a1:"\<Inter> (QStateM_map Q1 ` q) \<noteq> {}" and a2:"q\<noteq>{}" 
  shows "Q_domain_var q (QStateM_map Q1) \<subseteq> QStateM_vars Q1"
    using QStateM_rel1 a1 a2 apply auto
    unfolding Q_domain_def Q_domain_var_def qstate_def apply transfer
    using iso_tuple_UNIV_I by blast

lemma range_0_none:"\<Union> (range (0::nat \<Rightarrow> nat set)) = none"
  unfolding zero_set_def zero_fun_def by auto

lemma QState_vars_0_0:"QState_vars 0 = 0"
  by (simp add: QState_vars_empty zero_QState zero_set_def)

lemma QStateM_list_dim:
   "QStateM_list \<Q> = vl \<Longrightarrow>
    dim_vec (vec_of_list vl) = 2^card (QStateM_vars \<Q>)"
  using QStateM_list.rep_eq QStateM_vars.rep_eq QState_rel1' by auto

lemma QStateM_list_dim_union_vars:"QStateM_vars \<Q> = q1 \<union> q2 \<Longrightarrow> q1 \<inter> q2 = {} \<Longrightarrow>
       dim_vec (vec_of_list (QStateM_list \<Q>)) = 2^card q1 * 2^card q2"
  using QStateM_list_dim
  by (metis QStateM_vars.rep_eq QState_rel3' card_Un_disjoint finite_Un power_add)


definition sca_mult_qstatem::"complex \<Rightarrow>  QStateM \<Rightarrow> QStateM"  (infixl "\<cdot>\<^sub>Q" 70)
  where "sca_mult_qstatem s qs \<equiv> QStateM(QStateM_map qs, s \<cdot>\<^sub>q (qstate qs))"


lemma sca_mult_qstatem_wf:
  assumes a0:"QStateM_vars qs\<noteq>{} \<and> s\<noteq>0" 
  shows "QStateM_wf (QStateM_map qs, s \<cdot>\<^sub>q (qstate qs))"
proof-
  have "QStateM_wf (QStateM_unfold qs)"
    using QStateM_wf by blast
  thus ?thesis using sca_mult_qstate_vars a0
    using QStateM_vars.rep_eq assms qstate_def sca_mult_qstate_vars  by force       
qed

lemma sca_mult_qstatem_var_map:
  "QStateM_vars qs\<noteq>{} \<and> s\<noteq>0  \<Longrightarrow> QStateM_map (s \<cdot>\<^sub>Q qs) = QStateM_map qs"
  unfolding sca_mult_qstatem_def using sca_mult_qstatem_wf[of qs s]
  by (auto simp add: QStateM_wf_map)

lemma sca_mult_qstatem_var_qstate:
  "QStateM_vars qs\<noteq>{} \<and> s\<noteq>0  \<Longrightarrow> qstate (s \<cdot>\<^sub>Q qs) = s \<cdot>\<^sub>q qstate qs"
  unfolding sca_mult_qstatem_def using sca_mult_qstatem_wf[of qs s]
  by (auto simp add: QStateM_wf_qstate)

lemma sca_mult_q_statem_qstate_vars: 
   "QStateM_vars qs\<noteq>{} \<and> s\<noteq>0  \<Longrightarrow> 
    QStateM_vars (s \<cdot>\<^sub>Q qs) = QStateM_vars qs"
  using QStateM_vars.rep_eq qstate_def sca_mult_qstate_vars sca_mult_qstatem_var_qstate 
  by auto

lemma sca_mult_q_statem_qstate_vector: 
   "QStateM_vars qs\<noteq>{} \<and> s\<noteq>0  \<Longrightarrow> QStateM_vector (s \<cdot>\<^sub>Q qs) = s  \<cdot>\<^sub>v QStateM_vector qs"
  using QStateM_vector.rep_eq qstate_def sca_mult_qstate_quantum sca_mult_qstatem_var_qstate
  using QStateM_vars.rep_eq by force 



lemma QStateM_list_inv: assumes a0:"Q_domain (QStateM_map \<Q>) = {}"
  shows "inverse(QStateM_list \<Q> ! 0) \<cdot>\<^sub>Q \<Q> = QStateM (\<lambda>x. {}, 0)"
proof-
  have "QStateM_map \<Q> = {}\<^sub>q" using a0 unfolding Q_domain_def by auto       
  moreover have "QStateM_list \<Q> = QState_list (qstate \<Q>)"
    unfolding qstate_def apply transfer by auto
  moreover have  "inverse(QState_list (qstate \<Q>) ! 0) \<cdot>\<^sub>q (qstate \<Q>) = 0"  
    unfolding zero_QState empty_qstate_def
    using QStateM_rel1 QState_list_inv assms empty_qstate_def by fastforce
  ultimately show ?thesis unfolding sca_mult_qstatem_def 
    by auto
qed

lemma sca_mult_qstatem_assoc: 
  "QStateM_vars Q\<noteq>{} \<and> a1\<noteq>0 \<and> a2\<noteq>0
   \<Longrightarrow> a1 * a2 \<cdot>\<^sub>Q Q = a1 \<cdot>\<^sub>Q (a2 \<cdot>\<^sub>Q Q)"
  using sca_mult_qstate_assoc sca_mult_qstatem_def sca_mult_qstatem_var_map 
        sca_mult_qstatem_var_qstate by presburger

lemma QStateM_empty_not_zero: assumes a0:"Q_domain (QStateM_map \<Q>) = {}"
  shows "QStateM_list \<Q> ! 0 \<noteq> 0"
proof-
  have "QStateM_map \<Q> = {}\<^sub>q" using a0 unfolding Q_domain_def by auto       
  then have "QStateM_list \<Q> = QState_list (qstate \<Q>)"
    unfolding qstate_def apply transfer by auto  
  then show ?thesis apply auto unfolding qstate_def 
    using QStateM_rel1 QState_wf  assms qstate_def unfolding QState_wf_def
    by (metis One_nat_def QState_list_empty length_Cons less_one list.size(3) prod.sel(2))
qed 

lemma disjoint_x_y_wf1_x_plus_y:
       assumes a0:"QStateM_map x ## QStateM_map y "  and 
              a1:"qstate x ## qstate y"
      shows "Q_domain (QStateM_map x + QStateM_map y) = 
                   QState_vars (qstate x + qstate y)"
proof-
  have wr_x:"QStateM_wf (QStateM_map x, qstate x)" and
       wr_y:"QStateM_wf (QStateM_map y, qstate y)"
    using QStateM_wf by blast+
  { fix xa 
    assume a00:"xa \<in> Q_domain (QStateM_map x + QStateM_map y)"        
    then have "xa \<in> QState_vars (qstate x + qstate y)"
      using a0 a1 wr_x wr_y unfolding Q_domain_def  plus_fun_def apply auto
      by (metis QState_vars_Plus UNIV_I UN_iff Un_iff disj_QState_def plus_QState plus_QState_vector_vars sep_disj_QState)+            
  }
  moreover 
  { fix xa 
    assume a00: "xa \<in> QState_vars (qstate x + qstate y)"         
    then have "xa \<in> QState_vars (qstate x) \<or> xa \<in> QState_vars (qstate y)"
      by (metis QState_vars_Plus Un_iff empty_iff plus_QState plus_QState_vector_vars)
    moreover have "QState_vars (qstate x) \<inter> QState_vars (qstate y) = {}" using a1
      by (simp add: disj_QState_def sep_disj_QState)      
    ultimately have "xa \<in> Q_domain (QStateM_map x + QStateM_map y)"
      using a0 a1 wr_x wr_y unfolding Q_domain_def  domain_def sep_disj_fun_def plus_fun_def 
      apply (auto simp add:)
      by (metis (mono_tags) IntI UN_iff empty_iff mem_Collect_eq)+
  } ultimately show ?thesis by auto
qed

lemma disjoint_x_y_wf2_x_plus_y:
      assumes a0:"QStateM_map q1 ## QStateM_map q2"  and 
              a1:"qstate q1 ## qstate q2" and 
              a2:"x\<noteq>y \<and> x\<in> domain (QStateM_map q1 + QStateM_map q2)" 
            shows "((QStateM_map q1 + QStateM_map q2) x) \<inter> ((QStateM_map q1 + QStateM_map q2) y) = {}"  
proof-
  have wr_x:"QStateM_wf (QStateM_map q1, qstate q1)" and
       wr_y:"QStateM_wf (QStateM_map q2, qstate q2)"
    using QStateM_wf by blast+
  thus ?thesis using a0 a1 a2   
    unfolding Q_domain_def  domain_def sep_disj_fun_def plus_fun_def 
      apply (auto simp add:)
      apply blast
    by (metis IntI Sup_upper disj_QState_def empty_iff range_eqI sep_disj_QState subsetD)+

qed



lemma plus_wf: assumes a0:"QStateM_map x ## QStateM_map y "  and 
              a1:"qstate x ## qstate y"
            shows "QStateM_wf (QStateM_map x + QStateM_map y, qstate x + qstate y)"  
  using disjoint_x_y_wf1_x_plus_y[OF a0 a1] 
     disjoint_x_y_wf2_x_plus_y[OF a0 a1 ] by force


(* lemma assumes a0:"QStateM_map x ## QStateM_map y" 
  shows "QStateM_map
               (QStateM
                 (QStateM_map x + QStateM_map y, qstate x + qstate y)) =
      QStateM_map x + QStateM_map y"
   apply transfer'    
  unfolding plus_fun_def plus_QState plus_QState_def 
   sep_disj_fun_def opt_class.domain_def Q_domain_def qstate_def Let_def  
  apply transfer' apply auto 
  sorry *)

instantiation QStateM ::  sep_algebra
begin
definition zero_QStateM: "0 \<equiv> QStateM (0, 0)"
definition plus_QStateM: "s1 + s2 \<equiv> QStateM (QStateM_map s1 + QStateM_map s2, qstate s1 + qstate s2)" 
definition sep_disj_QStateM: "s1 ## s2 \<equiv> (QStateM_map s1 ## QStateM_map s2) \<and> qstate s1 ## qstate s2"

lemma h:"QStateM_map x + QStateM_map 0 = QStateM_map x"
  unfolding zero_QStateM using Qstate_map_0_0
  by (simp add: Qstate_map_0_0) 

lemma qstate_idem:"qstate x + qstate 0 = qstate x"    
proof -
  have "uQStateM (0::QStateM) = (0, 0) \<or> 
       snd (uQStateM (0::QStateM)) = 0"
    by (simp add: QStateM.rep_eq zero_QState zero_QStateM)
  then show ?thesis unfolding qstate_def
    by fastforce
qed

instance 
  apply standard 
  using sep_disj_QStateM sep_disj_zero zero_QState zero_QStateM Qstate_map_0_0 apply auto[1]
  apply (metis disj_QState_def plus_QState plus_QState_def qstate_idem sep_disj_QState sep_disj_commuteI sep_disj_zero)
       apply (simp add: sep_disj_QStateM sep_disj_commute)
      apply (metis plus_QStateM qstate_idem Qstate_map_0_0 idem_QState sep_add_zero zero_QStateM)
     apply (metis plus_QStateM sep_add_commute sep_disj_QStateM)
  subgoal for x y z
    apply  (auto simp add: sep_disj_QStateM plus_QStateM)
    using plus_wf[of x y] plus_wf[of y z]
    by (simp add: Qstate_mapf Qstate_vector sep_add_assoc)
   apply (smt sep_disj_QStateM Qstate_mapf Qstate_vector disjoint_x_y_wf1_x_plus_y 
             fst_conv plus_QStateM plus_wf sep_disj_addD)
  by (smt sep_disj_QStateM Qstate_mapf Qstate_vector 
          disjoint_x_y_wf1_x_plus_y fst_conv plus_QStateM plus_wf 
           sep_disj_add sep_disj_addD)  
end 


  

instantiation QStateM :: cancellative_sep_algebra
begin

lemma cancelative_mapping:assumes a0:" (\<lambda>x. if m x = {} then fst (ma, qa) x else fst (m, q) x) =
       (\<lambda>x. if m x = {} then fst (mb, qb) x else fst (m, q) x)" and
       a1:"{x. ma x \<noteq> {}} \<inter> {x. m x \<noteq> {}} = {}" and
       a2:"{x. mb x \<noteq> {}} \<inter> {x. m x \<noteq> {}} = {}"
     shows "ma = mb"
proof-
  { fix x
    { assume "m x = {}" 
      then have "ma x = mb x" using a0 
        by (metis fstI)
    }
    moreover { 
      assume "m x \<noteq>{}"
      then have "ma x = mb x" using a0 a1 a2
        by blast
    }
    ultimately have "ma x = mb x" by auto
  } then show ?thesis by blast
qed


lemma QStateM_map_cancellative:
  assumes a0:"QStateM_map x + QStateM_map z = QStateM_map y + QStateM_map z" and
              a1:"QStateM_map x ## QStateM_map z" and a2:"QStateM_map y ## QStateM_map z"
            shows "QStateM_map x = QStateM_map y"
  using a0 a1 a2 unfolding plus_fun_def sep_disj_fun_def opt_class.domain_def 
  apply transfer 
  by (auto intro:cancelative_mapping)

lemma QStateM_Cancellative:
  assumes a0:"QStateM_map x + QStateM_map z = QStateM_map y + QStateM_map z" and
       a1:"qstate x + qstate z = qstate y + qstate z" and
       a2:"QStateM_map x ## QStateM_map z" and a3:"qstate x ## qstate z" and 
       a4:"QStateM_map y ## QStateM_map z" and "qstate y ## qstate z"
     shows "x = y"
proof-
  have "QStateM_map x = QStateM_map y" using QStateM_map_cancellative[OF a0 a2 a4] by auto
  moreover have "qstate x = qstate y"
    by (metis QStateM_rel1 a1 a3 calculation disj_QState_def sep_add_cancelD sep_disj_QState) 
  ultimately show ?thesis
    by (metis idem_QState)
qed

instance 
  apply standard 
  apply (simp add: plus_QStateM sep_disj_QStateM ) 
  apply transfer' using plus_wf apply (auto)
  using QStateM_Cancellative by presburger 
end


lemma QStateM_disj_dest:
  assumes a0:"Q1 ## Q2"
  shows "QStateM_map Q1 ## QStateM_map Q2" and "qstate Q1 ## qstate Q2"
  using assms sep_disj_QStateM by auto

lemma QStateM_map_qstate:assumes a0:"Q1 ## Q2"  
     shows "qstate (Q1 + Q2) = qstate Q1 + qstate Q2"
  using plus_wf[OF QStateM_disj_dest[OF a0]]
  by (simp add: QStateM_wf_qstate plus_QStateM)

lemma QStateM_map_plus:assumes a0:"Q1 ## Q2" 
     shows "QStateM_map (Q1 + Q2) = QStateM_map Q1 + QStateM_map Q2"
  using plus_wf[OF QStateM_disj_dest[OF a0]]
  by (simp add: QStateM_wf_map plus_QStateM)

lemma QState_vars_plus:
  assumes a0:"Q1 ## Q2"
  shows "QState_vars (Q1 + Q2) = QState_vars Q1 + QState_vars Q2"
  using QState_vars_Plus assms disj_QState_def plus_QState plus_QState_vector_vars 
         plus_set_def sep_disj_QState by fastforce

lemma QStateM_vars_plus:assumes a0:"Q1 ## Q2" 
     shows "QStateM_vars (Q1 + Q2) = QStateM_vars Q1 \<union> QStateM_vars Q2"
  using plus_wf[OF QStateM_disj_dest[OF a0]]
  using QStateM_map_qstate QStateM_vars.rep_eq 
        QState_vars_plus assms qstate_def sep_disj_QStateM
  by (simp add: plus_set_def) 
 

lemma QState_list_plus:
  assumes a0:"Q1 ## Q2"
  shows "QState_list (Q1 + Q2) = 
         list_of_vec
           (partial_state2.ptensor_vec 
                (QState_vars Q1) (QState_vars Q2) 
                (QState_vector Q1) (QState_vector Q2) )"
  by (metis (no_types) QState_list_Plus assms disj_QState_def 
       plus_QState plus_QState_vector_vector sep_disj_QState)

lemma QStateM_list_plus:
  assumes a0:"Q1 ## Q2" 
  shows "QStateM_list (Q1 + Q2) = 
         list_of_vec
           (partial_state2.ptensor_vec 
                (QStateM_vars Q1) (QStateM_vars Q2) 
                (QStateM_vector Q1) (QStateM_vector Q2) )"
  using QStateM_disj_dest(2) QStateM_list.rep_eq QStateM_map_qstate 
        QStateM_vars.rep_eq QStateM_vector.rep_eq QState_list_plus 
       assms qstate_def by auto

lemma scalar_mult_QStateM_plus_l:
  "QStateM_vars \<Q>' \<noteq> {} \<and> a\<noteq>0  \<Longrightarrow> 
    \<Q>' ## \<Q>'' \<Longrightarrow> a  \<cdot>\<^sub>Q (\<Q>' + \<Q>'') = (a  \<cdot>\<^sub>Q \<Q>' + \<Q>'')"  
  using QStateM_rel1 QStateM_rel2 QStateM_wf_map QStateM_wf_qstate plus_wf 
         sca_mult_qstate_vars scalar_mult_QState_plus_l sca_mult_qstatem_def
        QStateM_disj_dest(2) QStateM_map_plus QStateM_map_qstate 
         QStateM_vars.rep_eq plus_QStateM qstate_def by force 
  
  

lemma scalar_mult_QStateM_plus_r:
  assumes a0:"QStateM_vars \<Q>'' \<noteq> {} \<and> a\<noteq>0 " and a1:"\<Q>' ## \<Q>''" 
  shows "a  \<cdot>\<^sub>Q (\<Q>' + \<Q>'') = ( \<Q>' + a  \<cdot>\<^sub>Q \<Q>'')"
  using a0 local.a1 plus_QStateM sca_mult_qstatem_var_map 
        sca_mult_qstatem_var_qstate
         scalar_mult_QState_plus_r 
        sep_disj_QStateM QStateM_map_plus QStateM_map_qstate 
        QStateM_vars.rep_eq qstate_def sca_mult_qstatem_def by force

value "(5::nat) * ((vec_of_list[3,1,3])\<bullet>(vec_of_list[3,1,3]))"
value " (((5::nat)\<cdot>\<^sub>v(vec_of_list[3,1,3]))\<bullet>(vec_of_list[3,1,3]))"
value "((vec_of_list[3::nat,1,3,4])\<bullet>(vec_of_list[3,1,3]))"

lemma "v \<in> carrier_vec n \<Longrightarrow> 
       w \<in> carrier_vec n \<Longrightarrow> 
       a * (v \<bullet> w) = (a \<cdot>\<^sub>v v) \<bullet> w"
  by auto


thm complex_norm_square
lemma "\<bar>u::complex\<bar> = norm u"
  by (simp add: abs_complex_def  of_real_def)

 
lemma "(conjugate u::complex)\<cdot>\<^sub>v(conjugate v) = conjugate (u \<cdot>\<^sub>v v) "
  by auto

lemma Re_norm_v_gt_0:assumes a0:"Re u > 0 " and a1:"Re v > 0"
  shows "Re (\<bar>u\<bar> * v) > 0" using a0 a1
  proof -
    have f1: "\<And>c. complex_of_real (cmod c) = \<bar>c\<bar>"
      by (simp add: abs_complex_def)
    then have f2: "\<And>c. Im \<bar>c\<bar> = 0"
      by (metis (no_types) Im_complex_of_real)
    have f3: "\<And>c. Re \<bar>c\<bar> = cmod c"
      using f1 by (metis (no_types) Re_complex_of_real)
    have "0 \<noteq> u"
      using a0 by force
    then show ?thesis
      using f3 f2 by (simp add: a1)
  qed

lemma Re_norm_u_gt_0_Im_v_0:
  assumes a0:"Re u \<ge> 0 " and 
          a1:"Re v \<ge> 0 \<and> Im v = 0"
        shows "Re (\<bar>u\<bar> * v) \<ge> 0  \<and> Im (\<bar>u\<bar> * v) = 0" 
  using a0 a1
  by (simp add: abs_complex_def)

lemma vec_norm_Re_0:
   "Re (vec_norm v) \<ge> 0 \<and> Im (vec_norm v) = 0"
  unfolding vec_norm_def by auto

lemma norm_complex_absolutely_homogenous:  
  shows "\<bar>u::complex\<bar> * vec_norm v = vec_norm( u \<cdot>\<^sub>v v)"
proof-
  have "\<bar>u\<bar> * vec_norm v = \<bar>u\<bar> * csqrt (v \<bullet>c v) "
    unfolding vec_norm_def by auto
  then have "(\<bar>u\<bar> * vec_norm v)^2  = (\<bar>u\<bar> * csqrt (v \<bullet>c v))^2"
    by auto
  also have "(\<bar>u\<bar> * csqrt (v \<bullet>c v))^2 = \<bar>u\<bar>^2 * (v \<bullet> (conjugate v))"
    by (metis power2_csqrt power_mult_distrib)
  also have "\<bar>u\<bar>^2 * (v \<bullet> (conjugate v)) = (u*(conjugate u)) * (v \<bullet> (conjugate v))"
    using Complex.complex_norm_square by (simp add:  abs_complex_def) 
  also have "(u*(conjugate u)) * (v \<bullet> (conjugate v)) = (u\<cdot>\<^sub>v v)  \<bullet> ((conjugate u)\<cdot>\<^sub>v(conjugate v))"
    by auto
  also have "(conjugate u::complex)\<cdot>\<^sub>v(conjugate v) = conjugate (u \<cdot>\<^sub>v v)"
    by auto
  finally have "csqrt ((\<bar>u\<bar> * vec_norm v)\<^sup>2) = csqrt (inner_prod (u \<cdot>\<^sub>v v) (u \<cdot>\<^sub>v v))"
    by auto
  moreover have "csqrt ((\<bar>u\<bar> * vec_norm v)\<^sup>2) = \<bar>u\<bar> * vec_norm v"
  proof- 
    have  "0 < Re \<bar>u\<bar> \<or> (Re \<bar>u\<bar> = 0 \<and> 0 \<le> Im \<bar>u\<bar>)"
      by (simp add: abs_complex_def)
    moreover have  "Re (vec_norm v) \<ge> 0 \<and> Im (vec_norm v) = 0"
      using vec_norm_Re_0 by auto
    ultimately show ?thesis  apply auto
      using csqrt_square vec_norm_Re_0 apply auto
      apply (simp add: complex.expand vec_norm_Re_0)
      by (metis (no_types) Re_norm_v_gt_0 abs_abs complex.expand csqrt_principal 
               mult_eq_0_iff 
              vec_norm_Re_0 vec_norm_def zero_complex.simps(1) zero_complex.simps(2))   
  qed        
  finally show ?thesis
    by (simp add: vec_norm_def)  
qed


(* lemma eq_vec_norm_q_empty:
  assumes a0:"length (QStateM_list \<Q>'') = 1"
  shows "vec_norm (QStateM_vector (QStateM_list \<Q>'' ! 0 \<cdot>\<^sub>Q \<Q>')) \<cdot>\<^sub>Q
   (inverse (QStateM_list \<Q>'' ! 0) \<cdot>\<^sub>Q \<Q>'') = 
  vec_norm (QStateM_vector \<Q>') \<cdot>\<^sub>Q \<Q>''" sorry
proof-
  have f0:"Im (QStateM_list \<Q>'' ! 0) = 0 \<and> Re (QStateM_list \<Q>'' ! 0) > 0"
    using a0 apply transfer by (auto;transfer;auto)
  have f1:"Im (inverse (QStateM_list \<Q>'' ! 0)) = 0 \<and> Re (inverse (QStateM_list \<Q>'' ! 0)) > 0"
    using f0 by auto
  then have f2:"QStateM_vector (QStateM_list \<Q>'' ! 0 \<cdot>\<^sub>Q \<Q>') = 
            QStateM_list \<Q>'' ! 0 \<cdot>\<^sub>v QStateM_vector \<Q>'"
    using f0
    by (meson sca_mult_q_statem_qstate_vector)
  also have f3:"vec_norm (QStateM_list \<Q>'' ! 0 \<cdot>\<^sub>v QStateM_vector \<Q>') = 
                 QStateM_list \<Q>'' ! 0 * vec_norm (QStateM_vector \<Q>')"  
    using norm_complex_absolutely_homogenous[of "QStateM_list \<Q>'' ! 0" "QStateM_vector \<Q>'"] f0  
    apply auto
    by (simp add: abs_complex_def cmod_eq_Re complex_eq_iff) 
  also have "QStateM_list \<Q>'' ! 0  \<cdot>\<^sub>Q (inverse (QStateM_list \<Q>'' ! 0) \<cdot>\<^sub>Q \<Q>'') = 
            QStateM_list \<Q>'' ! 0 * (inverse (QStateM_list \<Q>'' ! 0))  \<cdot>\<^sub>Q \<Q>''"
    using f0 f1
    using sca_mult_qstatem_assoc by presburger 
  then have "QStateM_list \<Q>'' ! 0 * vec_norm (QStateM_vector \<Q>') \<cdot>\<^sub>Q
             (inverse (QStateM_list \<Q>'' ! 0) \<cdot>\<^sub>Q \<Q>'') = 
            QStateM_list \<Q>'' ! 0 * vec_norm (QStateM_vector \<Q>') * (inverse (QStateM_list \<Q>'' ! 0))  \<cdot>\<^sub>Q \<Q>''"     
    using f0
    by (metis (no_types, lifting) QStateM_rel1 QStateM_vector.rep_eq f1 
        qstate_def sca_mult_q_statem_qstate_vector sca_mult_qstate_def 
      sca_mult_qstatem_def sca_mult_qstatem_var_map smult_smult_assoc)
 
  finally show ?thesis
    by (smt divide_complex_def f0 f2 f3 nonzero_mult_div_cancel_left zero_complex.simps(1))
qed
*)

lemma vec_norm_square:
  "vec_norm ((u::complex) \<cdot>\<^sub>v q)^2 = \<bar>u\<bar>^2 * (vec_norm q)^2"
    using norm_complex_absolutely_homogenous
    by (metis power_mult_distrib)

lemma eq_tensor_inverse_QStateM_vector: 
  assumes a0:"Q1 ## Q2" and
       a1:"QStateM_map Q1 = QStateM_map Q1'" and
       a2:"QStateM_map Q2 = QStateM_map Q2'" and
       a3:"Q1 + Q2 = Q1' + Q2'" 
     shows "\<exists>k. k \<noteq> 0 \<and> (QStateM_vector Q1') = k \<cdot>\<^sub>v(QStateM_vector Q1) \<and> 
                (QStateM_vector Q2') = inverse k \<cdot>\<^sub>v(QStateM_vector Q2)"
  by (metis QStateM_map_qstate QStateM_rel1 QStateM_vars.rep_eq QStateM_vector.rep_eq a0 a3
       disj_QState_def eq_tensor_inverse_QState_vector local.a1 local.a2 qstate_def sep_disj_QState sep_disj_QStateM)

lemma eq_tensor_inverse_QStateM: 
  assumes a0:"Q1 ## Q2" and
       a1:"QStateM_map Q1 = QStateM_map Q1'" and
       a2:"QStateM_map Q2 = QStateM_map Q2'" and
       a3:"Q1 + Q2 = Q1' + Q2'" 
     shows "\<exists>k. k \<noteq> 0 \<and> Q1' = k \<cdot>\<^sub>Q Q1 \<and> Q2' = inverse k \<cdot>\<^sub>Q Q2"
  by (smt (verit, ccfv_threshold) QStateM_map_qstate a0 a3 disj_QState_def 
          eq_QStateM_vars eq_QStateMap_vars eq_tensor_inverse_QState idem_QState 
          local.a1 local.a2 sca_mult_qstatem_def sep_disj_QState sep_disj_QStateM snd_conv)

lemma eq_tensor_inverse_QStateM_wf: 
  assumes a0:"Q1 ## Q2" and
       a1:"QStateM_map Q1 = QStateM_map Q1'" and
       a2:"QStateM_map Q2 = QStateM_map Q2'" and
       a3:"Q1 + Q2 = Q1' + Q2'" 
     shows "\<exists>k. k\<noteq>0 \<and> Q1' = k \<cdot>\<^sub>Q Q1 \<and> Q2' = inverse k \<cdot>\<^sub>Q Q2 \<and>
               QStateM_wf (QStateM_map Q1', k \<cdot>\<^sub>q qstate Q1) \<and>
               QStateM_wf (QStateM_map Q2', (inverse k) \<cdot>\<^sub>q qstate Q2)"
proof-
  obtain k where k:"k \<noteq> 0" and "Q1' = k \<cdot>\<^sub>Q Q1 \<and> Q2' = inverse k \<cdot>\<^sub>Q Q2" 
    using eq_tensor_inverse_QStateM[OF a0 a1 a2 a3] by auto
  moreover have " QStateM_wf (QStateM_map Q1', k \<cdot>\<^sub>q qstate Q1)"   
    using sca_mult_qstatem_wf a1 calculation
    by (metis QStateM_rel1 QStateM_rel2 fst_conv sca_mult_qstate_vars snd_conv)  
  moreover have "QStateM_wf (QStateM_map Q2', (inverse k) \<cdot>\<^sub>q qstate Q2)"   
    using sca_mult_qstate_wf a2 calculation
    by (metis QStateM_rel1 QStateM_rel2fa fst_eqD inverse_nonzero_iff_nonzero sca_mult_qstate_vars snd_eqD)
  ultimately show ?thesis by blast
qed


lemma eq_tensor_inverse_QStateM_wf': 
  assumes a0:"Q1 ## Q2" and
       a1:"QStateM_map Q1 = QStateM_map Q1'" and
       a2:"QStateM_map Q2 = QStateM_map Q2'" and
       a3:"Q1 + Q2 = Q1' + Q2'" 
     shows "\<exists>k. k\<noteq>0 \<and> Q1' = k \<cdot>\<^sub>Q Q1 \<and> Q2' = inverse k \<cdot>\<^sub>Q Q2 \<and> 
               QStateM_wf (QStateM_map Q1', k \<cdot>\<^sub>q qstate Q1) \<and>
               QState_wf (QStateM_vars Q1', list_of_vec (k \<cdot>\<^sub>v QState_vector (qstate Q1))) \<and>
               QStateM_wf (QStateM_map Q2', (inverse k) \<cdot>\<^sub>q qstate Q2) \<and>
               QState_wf (QStateM_vars Q2', list_of_vec (inverse k \<cdot>\<^sub>v QState_vector (qstate Q2)))"
proof-
  obtain k where q0:"k\<noteq>0" and q1:"Q1' = k \<cdot>\<^sub>Q Q1" and q2:"Q2' = inverse k \<cdot>\<^sub>Q Q2" and 
               q4:"QStateM_wf (QStateM_map Q1', k \<cdot>\<^sub>q qstate Q1)" and
               q5:"QStateM_wf (QStateM_map Q2', (inverse k) \<cdot>\<^sub>q qstate Q2)" 
    using eq_tensor_inverse_QStateM_wf[OF a0 a1 a2 a3] by auto
  let ?v1 = "list_of_vec (k \<cdot>\<^sub>v QState_vector (qstate Q1))"
  let ?v2 = "list_of_vec (inverse k \<cdot>\<^sub>v QState_vector (qstate Q2))"
 
  have "QState_wf (QStateM_vars Q1',?v1)"
  proof-    
    have "2^card (QStateM_vars Q1') = length ?v1"
      using a1 apply transfer
      using QStateM_rel1 QState_rel1a' by fastforce
    moreover have "finite (QStateM_vars Q1')" using a1 
      by (simp add: QStateM_vars.rep_eq QState_rel3')
    moreover have "(\<exists>i<length ?v1. ?v1 !i\<noteq>0)"
      by (metis QState_wf_def q0 sca_mult_qstate_wf snd_conv)
    moreover have "length ?v1 = 1 \<longrightarrow> ?v1!0 \<noteq> 0"
      using calculation(3) by fastforce 
    ultimately show ?thesis unfolding QState_wf_def by auto
  qed
  moreover have  "QState_wf (QStateM_vars Q2',?v2)"
  proof-
    have "2^card (QStateM_vars Q2') = length ?v2"
      using a2 apply transfer 
      using QStateM_rel1 QState_rel1a' by fastforce      
    moreover have "finite (QStateM_vars Q2')" using a1 
      by (simp add: QStateM_vars.rep_eq QState_rel3')
    moreover have "(\<exists>i<length ?v2. ?v2 !i\<noteq>0)"
      by (metis QState_wf_def nonzero_imp_inverse_nonzero q0 sca_mult_qstate_wf snd_conv)      
    moreover have "length ?v2 = 1 \<longrightarrow> ?v2 !0 \<noteq> 0"
      using calculation(3) by fastforce
    ultimately show ?thesis unfolding QState_wf_def by auto
  qed
  ultimately show ?thesis using q0 q1 q2  q4 q5 by blast
qed




(* lemma eq_vec_norm_q_empty:
  assumes a0:"length (QStateM_list \<Q>'') = 1"
  shows "vec_norm (QStateM_vector (QStateM_list \<Q>'' ! 0 \<cdot>\<^sub>Q \<Q>')) \<cdot>\<^sub>Q
   (inverse (QStateM_list \<Q>'' ! 0) \<cdot>\<^sub>Q \<Q>'') = 
  vec_norm (QStateM_vector \<Q>') \<cdot>\<^sub>Q \<Q>''"
proof-
  have f0:"(QStateM_list \<Q>'' ! 0) \<noteq> 0 "
    using a0 apply transfer by (auto;transfer;auto)
  have f1:"(inverse (QStateM_list \<Q>'' ! 0)) \<noteq> 0"
    using f0 by auto
  then have f2:"QStateM_vector (QStateM_list \<Q>'' ! 0 \<cdot>\<^sub>Q \<Q>') = 
            QStateM_list \<Q>'' ! 0 \<cdot>\<^sub>v QStateM_vector \<Q>'"
    sorry
  also have f3:"vec_norm (QStateM_list \<Q>'' ! 0 \<cdot>\<^sub>v QStateM_vector \<Q>') = 
                 QStateM_list \<Q>'' ! 0 * vec_norm (QStateM_vector \<Q>')"  
    using norm_complex_absolutely_homogenous[of "QStateM_list \<Q>'' ! 0" "QStateM_vector \<Q>'"] f0 
    apply auto            
    by (simp add: abs_complex_def cmod_eq_Re complex_eq_iff) 
  also have "QStateM_list \<Q>'' ! 0  \<cdot>\<^sub>Q (inverse (QStateM_list \<Q>'' ! 0) \<cdot>\<^sub>Q \<Q>'') = 
            QStateM_list \<Q>'complex' ! 0 * (inverse (QStateM_list \<Q>'' ! 0))  \<cdot>\<^sub>Q \<Q>''"
    using sca_mult_qstatem_assoc[OF f0 f1] by simp
  then have "QStateM_list \<Q>'' ! 0 * vec_norm (QStateM_vector \<Q>') \<cdot>\<^sub>Q
             (inverse (QStateM_list \<Q>'' ! 0) \<cdot>\<^sub>Q \<Q>'') = 
            QStateM_list \<Q>'' ! 0 * vec_norm (QStateM_vector \<Q>') * (inverse (QStateM_list \<Q>'' ! 0))  \<cdot>\<^sub>Q \<Q>''"     
    using f0
    by (metis f1 sca_mult_qstate_def sca_mult_qstate_quantum sca_mult_qstate_vars 
       sca_mult_qstatem_def sca_mult_qstatem_var_map sca_mult_qstatem_var_qstate smult_smult_assoc) 
  finally show ?thesis
    by (smt divide_complex_def f0 f2 f3 nonzero_mult_div_cancel_left zero_complex.simps(1))
qed *)

lemma eq_tensor_inverse_QState_wf_split_Q':
  assumes a0: "Q1'' + Q2 = k \<cdot>\<^sub>q Qb" and a1:"Q1'' ## Q2"              
            shows "\<exists>Qb' Qb'' k'.  k \<cdot>\<^sub>q Qb = Qb' + Qb'' \<and> k'\<noteq>0 \<and> 
                  Q1'' = k' \<cdot>\<^sub>q Qb' \<and> Q2 = inverse k' \<cdot>\<^sub>q (Qb'')  \<and> 
                 QState_wf (QState_vars Q1'',list_of_vec (k' \<cdot>\<^sub>v QState_vector Qb')) \<and>
                 QState_wf (QState_vars Q2, list_of_vec((inverse k') \<cdot>\<^sub>v QState_vector Qb''))"
  using eq_tensor_inverse_QState_wf[OF a1 ] a0
  by metis 

lemma eq_tensor_inverse_QStateM_wf_split_Q':
  assumes a0: "Q1'' + Q2 = k \<cdot>\<^sub>Q Qb" and a1:"Q1'' ## Q2"              
            shows "\<exists>Qb' Qb'' k'.  k \<cdot>\<^sub>Q Qb = Qb' + Qb'' \<and> k'\<noteq>0 \<and> 
                  Q1'' = k' \<cdot>\<^sub>Q Qb' \<and> Q2 = inverse k' \<cdot>\<^sub>Q (Qb'')  \<and> 
                 QStateM_wf (QStateM_map Q1'',k' \<cdot>\<^sub>q qstate Qb') \<and>                 
                 QStateM_wf (QStateM_map Q2, (inverse k') \<cdot>\<^sub>q qstate Qb'')"
  using eq_tensor_inverse_QStateM_wf[OF a1 ] a0
  by metis 

lemma eq_tensor_inverse_QStateM_wf'_split_Q':
  assumes a0: "Q1'' + Q2 = k \<cdot>\<^sub>Q Qb" and a1:"Q1'' ## Q2"              
            shows "\<exists>Qb' Qb'' k'.  k \<cdot>\<^sub>Q Qb = Qb' + Qb'' \<and> k'\<noteq>0 \<and> 
                  Q1'' = k' \<cdot>\<^sub>Q Qb' \<and> Q2 = inverse k' \<cdot>\<^sub>Q (Qb'')  \<and> 
                 QStateM_wf (QStateM_map Q1'',k' \<cdot>\<^sub>q qstate Qb') \<and>
                 QState_wf (QStateM_vars Q1'',list_of_vec (k' \<cdot>\<^sub>v QState_vector (qstate Qb'))) \<and>
                 QStateM_wf (QStateM_map Q2, (inverse k') \<cdot>\<^sub>q qstate Qb'') \<and> 
                 QState_wf (QStateM_vars Q2,list_of_vec (inverse k' \<cdot>\<^sub>v QState_vector (qstate Qb'')))"
  using a0 a1
proof-
  obtain Qb' Qb'' k' where 
   q1:"k \<cdot>\<^sub>Q Qb = Qb' + Qb''" and q2:"k'\<noteq>0" and
   q3:"Q1'' = k' \<cdot>\<^sub>Q Qb'" and q4:"Q2 = inverse k' \<cdot>\<^sub>Q (Qb'')" and 
   q6:"QStateM_wf (QStateM_map Q1'',k' \<cdot>\<^sub>q qstate Qb')" and
   q7:"QStateM_wf (QStateM_map Q2, (inverse k') \<cdot>\<^sub>q qstate Qb'')"     
    using eq_tensor_inverse_QStateM_wf_split_Q'[OF a0 a1] by auto
  let ?v1 = "list_of_vec (k' \<cdot>\<^sub>v QState_vector (qstate Qb'))"
  let ?v2 = "list_of_vec (inverse k' \<cdot>\<^sub>v QState_vector (qstate Qb''))"
  
  have "QState_wf (QStateM_vars Q1'',?v1)"
  proof-    
    have "2^card (QStateM_vars Q1'') = length ?v1"
      using q2  q6 apply transfer 
      by (metis  QState_rel1a' fst_conv length_list_of_vec sca_mult_qstate_quantum snd_conv)
    moreover have "finite (QStateM_vars Q1'')" using a1 
      by (simp add: QStateM_vars.rep_eq QState_rel3')
    moreover have "(\<exists>i<length ?v1. ?v1 !i\<noteq>0)"
      by (metis QState_wf_def q2 sca_mult_qstate_wf snd_conv)
    moreover have "length ?v1 = 1 \<longrightarrow> ?v1!0 \<noteq> 0"
      using calculation(3) by auto
    ultimately show ?thesis unfolding QState_wf_def by auto
  qed
  moreover have  "QState_wf (QStateM_vars Q2,list_of_vec (inverse k' \<cdot>\<^sub>v QState_vector (qstate Qb'')))"
  proof-
    have "2^card (QStateM_vars Q2) = length ?v2"
      using q2  q7 apply transfer
      by (metis  QState_rel1a' fst_conv 
                index_smult_vec(2) length_list_of_vec nonzero_imp_inverse_nonzero 
                 sca_mult_qstate_vars snd_conv)      
    moreover have "finite (QStateM_vars Q2)" using a1 
      by (simp add: QStateM_vars.rep_eq QState_rel3')
    moreover have "(\<exists>i<length ?v2. ?v2 !i\<noteq>0)"
      by (metis QState_wf_def nonzero_imp_inverse_nonzero q2 sca_mult_qstate_wf snd_conv)
    moreover have "length ?v2 = 1 \<longrightarrow> ?v2!0 \<noteq> 0"
      using calculation(3) by force 
    ultimately show ?thesis unfolding QState_wf_def by auto
  qed
  ultimately show ?thesis using q1 q2 q3 q4 q6 q7 by blast  
qed
 

(* lemma
  assumes a0: "Q1'' + Q2 = k \<cdot>\<^sub>Q Qb" and a1:"Q1'' ## Q2" and
              "k \<cdot>\<^sub>Q Qb = Qb' + Qb''" and
             "QStateM_wf (QStateM_map Q1'', k' \<cdot>\<^sub>q (qstate Qb')) \<and>
             QStateM_wf (QStateM_map Q2, (inverse k') \<cdot>\<^sub>q (qstate Qb''))" and
             "Q1'' = k' \<cdot>\<^sub>Q Qb' \<and> Q2 = inverse k' \<cdot>\<^sub>Q (Qb'')"
           shows "True"*)
lemma assumes a0: "Q1'' + Q2 = k \<cdot>\<^sub>q Qb" and a1:"Q1'' ## Q2" and 
              a2:"QState_wf (QState_vars Qb, list_of_vec (k \<cdot>\<^sub>v QState_vector Qb))" and
              a3:"QState_vars Q1'' = {} \<or> QState_vars Q2 = {}"
            shows"\<exists>Qb' Qb'' k'. Qb = Qb' + Qb'' \<and> k'\<noteq>0 \<and> 
                  Q1'' = k' \<cdot>\<^sub>q (inverse k \<cdot>\<^sub>q Qb') \<and> Q2 = inverse k' \<cdot>\<^sub>q Qb'' \<and>
                 QState_wf (QState_vars Q1'',list_of_vec (k \<cdot>\<^sub>v QState_vector Qb')) \<and>
                 QState_wf (QState_vars Q2, list_of_vec((inverse k') \<cdot>\<^sub>v QState_vector Qb''))"
proof-  
   have "k \<cdot>\<^sub>q Qb = (k \<cdot>\<^sub>q Qb) + |>"
     using empty_qstate_def zero_QState by force
   moreover have "QState_vars (k \<cdot>\<^sub>q Qb) = QState_vars Qb" using a2 unfolding sca_mult_qstate_def
     using QState_var_idem by blast
  have k:"k\<noteq>0 " 
    using a2 by (auto simp add: QState_wf_def)
  then have "inverse k \<cdot>\<^sub>q (Q1'' + Q2) = Qb" using a0 a2 unfolding sca_mult_qstate_def    
    by (smt (z3) QState_list.rep_eq QState_refl QState_vector.rep_eq empty_iff 
               left_inverse list_vec sca_mult_qstate_quantum sca_mult_qstate_vars 
                scalar_vec_one smult_smult_assoc)
  ultimately have  "(inverse k \<cdot>\<^sub>q Q1'') + Q2 = Qb"
    using scalar_mult_QState_plus_l[OF _ a1, of "inverse k"]
    by (simp add: k)
  have "QState_vars (k \<cdot>\<^sub>q Qb) = QState_vars Qb" using a2 unfolding sca_mult_qstate_def
    using QState_var_idem by blast 
  moreover have  "QState_vars Q1'' + QState_vars Q2 = QState_vars Qb"
    using a0 a1 calculation a2 unfolding sca_mult_qstate_def
    by (metis QState_vars_plus) 
  then have "QState_vars Q1'' + QState_vars Q2 = QState_vars Qb"
    using a0 a1
    by blast   
  ultimately have  "(inverse k \<cdot>\<^sub>q Q1'') + Q2 = Qb"
    using scalar_mult_QState_plus_l[OF _ a1, of "inverse k"]
    using \<open>inverse k \<cdot>\<^sub>q Q1'' + Q2 = Qb\<close> by blast 
  have "QState_vars (k \<cdot>\<^sub>q Qb) = QState_vars Qb" using a2 unfolding sca_mult_qstate_def
    using QState_var_idem by blast 
  moreover have  "QState_vars Q1'' + QState_vars Q2 = QState_vars Qb"
    using a0 a1 calculation a2 unfolding sca_mult_qstate_def
    by (metis QState_vars_plus) 
  then have "QState_vars Q1'' + QState_vars Q2 = QState_vars Qb"
    using a0 a1
    by blast 
  then show ?thesis sorry
  qed 
 

  thm eq_tensor_inverse_QStateM_wf
lemma eq_tensor_inverse_QStateM_wf_split_Q: 
  assumes a0: "Q1'' + Q2 = k \<cdot>\<^sub>Q Qb" and a1:"Q1'' ## Q2"  
            shows"\<exists>Qb' Qb'' k'. k \<cdot>\<^sub>Q Qb = Qb' + Qb'' \<and> k'\<noteq>0 \<and> 
                  Q1'' = k' \<cdot>\<^sub>Q (Qb') \<and> Q2 = inverse k' \<cdot>\<^sub>Q Qb'' \<and>
                 QStateM_wf (QStateM_map Q1'', (k' \<cdot>\<^sub>q qstate Qb')) \<and>
                 QStateM_wf (QStateM_map Q2, (inverse k') \<cdot>\<^sub>q qstate Qb'')"
  using eq_tensor_inverse_QStateM_wf[OF a1] a0  by metis

       
end

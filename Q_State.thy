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

lemma "finite s \<Longrightarrow> x \<in> s \<Longrightarrow>
       (ind_in_set s) x =  to_nat_set s x"
  unfolding ind_in_set_def to_nat_set_def
  
  apply rule
  sorry

  value "to_nat_set {0::nat, 1,2,8,10,15} ` {2,10}"
  value "ind_in_set {0::nat, 1,2,8,10,15} ` {2,10} "


(* definition top_lin_set::"'q set \<Rightarrow> nat" where
  "top_lin_set qset \<equiv> if qset = {} then 1 else card qset"
*)
(* definition lin_set::"'q set \<Rightarrow> nat set"
  where "lin_set qset \<equiv> if qset = {} then {0} else {0 ..< (card qset)}"

definition lin_sets::"nat \<Rightarrow> 'q set \<Rightarrow> nat set"
  where "lin_sets n q_vars' \<equiv> if q_vars' = {} then  {n}
                                   else  {n ..< card (q_vars')+n}"
*)

definition list_dims::"'q set \<Rightarrow> nat list"
  where "list_dims qvars \<equiv> replicate (card qvars) 2"

definition dims :: "nat list \<Rightarrow> nat set \<Rightarrow> nat list" where
  "dims tv vs = nths tv vs"

\<comment>\<open> Lemmas on ptensor_vec \<close>

lemma tensor_neutral:"partial_state.tensor_vec [] {} (vCons (1::'a::comm_ring_1) vNil) (vCons 1 vNil) = vCons 1 vNil "
proof-
 interpret ps2:partial_state "[]" "{}" .
   
  show ?thesis  unfolding ps2.tensor_vec_def unfolding  
   ind_in_set_def partial_state.tensor_vec_def  state_sig.d_def 
   partial_state.encode1_def partial_state.dims1_def 
    partial_state.encode2_def partial_state.dims2_def  by auto
qed

lemma nths_set_gt_list_length:"nths l (- {0..<length l}) = []"
proof -
  have "nths l (- {0..<length l}) ! 0 \<notin> set (nths l (- {0..<length l}))"
    by (simp add: set_nths)
  then show ?thesis
    by (meson length_greater_0_conv nth_mem)
qed

lemma digit_decode_non_vars:"digit_decode (nths (replicate (card d1) 2) (- {0..<card d1}))
                  (nths (digit_encode (replicate (card d1) 2) i) (- {0..<card d1})) = 0"
  using nths_set_gt_list_length
  by (metis digit_decode.simps(1) length_digit_encode length_replicate)

lemma digit_decode_vars:
   "i< (2::nat) ^ card (d1) \<Longrightarrow> 
    digit_decode (nths (replicate (card d1) 2) {0..<card d1})
                 (nths (digit_encode (replicate (card d1) 2) i) {0..<card d1}) = i"  
  by (simp add: length_digit_encode nths_all)
  
lemma list_of_neutral:"list_of_vec (vCons 1 vNil) = [1::'a::comm_ring_1]"
  unfolding vCons_def by auto  

lemma list_ptensor_neutral:"list_of_vec
       (partial_state.tensor_vec [] {}
       (vCons (1::'a) vNil) (vCons (1::'a::comm_ring_1) vNil)) =
       [1::'a::comm_ring_1]"
  by (auto simp add: tensor_neutral list_of_neutral)

lemma idempoten_qstate1: 
  assumes 
    a0:"dim_vec (v::('a::comm_ring_1) vec) = (2::nat) ^ card (d1)" and
    a1:"i < dim_vec v"
  shows 
     "partial_state.tensor_vec (replicate (card d1) (2::nat))
             {0::nat..<card  d1} v (vCons 1 vNil) $ i = 
         v $ i"
proof-
  interpret ps2:partial_state "(replicate (card d1) (2::nat))" "{0::nat..<card  d1}" .
  let  ?d0 = "digit_decode (nths (replicate (card d1) 2) (- {0..<card d1}))
                  (nths (digit_encode (replicate (card d1) 2) i) (- {0..<card d1}))"
  have vcons_0:"vCons 1 vNil $ ?d0 = 1" by  (auto simp add: digit_decode_non_vars)
  moreover have  "digit_decode (nths (replicate (card d1) 2) {0..<card d1})
                 (nths (digit_encode (replicate (card d1) 2) i) {0..<card d1}) = i" 
    using digit_decode_vars a0 a1 by auto
  moreover have " (prod_list (replicate (card d1) 2)) = (2::nat) ^ card (d1)" by auto
  ultimately show ?thesis unfolding ps2.tensor_vec_def 
      partial_state.tensor_vec_def state_sig.d_def partial_state.encode1_def 
      partial_state.encode2_def partial_state.dims1_def partial_state.dims2_def     
    using a1 a0   apply clarsimp  by (auto simp add: vcons_0)
    
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
  assumes 
    a1:"dim_vec v = (2::nat) ^ card d " and a2:"finite d"
  shows "dim_vec
     (partial_state.tensor_vec (replicate (card d) 2)
       {0::nat..<card  d} v (vCons 1 vNil)) =
      dim_vec v"
proof-
  interpret ps2:partial_state "(replicate (card d) (2::nat))" 
                               "{0::nat..<card d}" .
  show ?thesis unfolding ps2.tensor_vec_def  
      partial_state.tensor_vec_def state_sig.d_def partial_state.encode1_def 
      partial_state.encode2_def partial_state.dims1_def vCons_def 
    using a1 by auto
qed

lemma idempoten_qstate:
  assumes 
    a1:"dim_vec (v::('a::comm_ring_1) vec) = (2::nat) ^ card d" and a2:"finite d"
  shows "partial_state.tensor_vec (list_dims d)  {0::nat..<card d} v (vCons (1) vNil) = v"
  unfolding list_dims_def
  using idempoten_qstate1[OF a1] idempoten_qstate2[OF  a1 a2]
  using a2 by blast


definition mapping::"'q set \<Rightarrow> 'q set \<Rightarrow> nat set \<times> nat set"
  where "mapping s1 s2 \<equiv>({},{})"

typedef (overloaded) ('q,'a::comm_ring_1)
  QState = "{(s,v)| (s::'q set) (v::'a list).                                   
              length v = (2^(card s)) \<and> finite s \<and>
              (s = {} \<longrightarrow> ((v!0) = (1::'a)))}"
  morphisms uQState Abs_QState  
  by (rule exI[where x ="({},[1])"], auto)

setup_lifting type_definition_QState

definition tensor_mat_ord::"('q,'a)QState \<Rightarrow> 'q set \<Rightarrow> 'a::comm_ring_1 mat \<Rightarrow> ('q,'a)QState set"
  where "tensor_mat_ord Q q M \<equiv> {}"

lemma QState_rel1:"length(snd(uQState x)) = 2 ^ card (fst(uQState x))"  
proof -
  have "\<exists>B v. uQState x = (B, v) \<and> length v = (2 ^ card B) \<and> 
              (B = {}) \<longrightarrow> (v ! 0 = 1)"
    using uQState by fastforce
  then show ?thesis using uQState  by (auto simp add:  split_beta)    
qed

lemma QState_rel2:"fst (uQState (x::('q,'a::comm_ring_1) QState )) = {} \<longrightarrow> 
                  (((snd (uQState x)) ! 0) = 1)"
proof -
  have "\<exists>B v. uQState x = (B, v) \<and> length v = (2 ^ card B) \<and> 
              (B = {}) \<longrightarrow> (v ! 0 = 1)"
    using uQState by fastforce
  then show ?thesis using uQState  by (auto simp add:  split_beta)       
qed

lemma QState_rel3:"finite (fst (uQState (x::('q,'a::comm_ring_1) QState )))"
  apply transfer by auto
 
lift_definition QState_vars :: "('q,'a::comm_ring_1) QState \<Rightarrow> 'q set" is fst .
lift_definition QState_list :: "('q,'a::comm_ring_1) QState \<Rightarrow> 'a::comm_ring_1 list" is snd .
lift_definition QState_vector::"('q,'a::comm_ring_1) QState \<Rightarrow> 'a::comm_ring_1 vec" is "\<lambda>s. vec_of_list (snd s)" .
lift_definition QState :: "'q set \<times> 'a::comm_ring_1 list \<Rightarrow> ('q,'a)QState" is  
  "\<lambda>s. (if fst s = {} \<and> snd s = [1] then (fst s, snd s)
       else (if finite (fst s) \<and> fst s \<noteq> {} \<and> length (snd s) = 2 ^ (card (fst s)) then (fst s, snd s)
       else ({}, [1])))"  by auto

lift_definition Conc :: " ('q,'a) QState \<Rightarrow> 'q set \<times> 'a::comm_ring_1 vec" is
  "\<lambda>s. (QState_vars s, QState_vector s)" .

lemma uqstate_fst:"fst (uQState a) = QState_vars a" apply transfer' by auto
lemma uqstate_snd:"snd (uQState a) = QState_list a" apply transfer' by auto

lemma QState_rel3':"finite (QState_vars (x::('q,'a::comm_ring_1) QState ))"
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

value "digit_decode [2,2,2] (nths (digit_encode [2,2,2,2] 9) {0,1,2})"
\<comment>\<open>Definition of plus_QState_vector\<close>
value "nths [2::nat,2,2] {(4::nat),5}"
value "(digit_encode [2,2,2,2] 9)"
value "nths (digit_encode [2,2,2,2] 9) {3}"
value "digit_decode [2] (nths (digit_encode [2,2,2,2] 9) {3})"
  
definition plus_QState_vector::"('q::linorder,'a::comm_ring_1) QState \<Rightarrow> ('q,'a::comm_ring_1) QState \<Rightarrow>'q set \<times> 'a::comm_ring_1 list"
  where "plus_QState_vector q1 q2 \<equiv> 
     let d1 = (QState_vars q1); d2 = (QState_vars q2); 
          s = d1 \<union> d2; l1 = QState_vector q1; l2 = QState_vector q2;
          dims = list_dims s;  
          v = partial_state.tensor_vec 
                     dims {0..<card d1} l1 l2;
          a = ((sorted_list_of_set d1)@(sorted_list_of_set d2));
          b = sorted_list_of_set s in (s,  (list_of_vec v).\<^sub>a \<^sub>\<leadsto> \<^sub>b)"

lemma QState_vars_empty:"QState_vars (QState ({}, [1])) = {}"
  by (metis (no_types) QState_id_fst_empty uqstate_fst)
  

lemma plus_QState_vector_a_idem:
  "snd (plus_QState_vector a (QState ({}, [1]))) = QState_list a"  
proof-
  let ?v0 = "QState ({}, [1])::('b, 'a) QState"  
  let ?s0 = "sorted_list_of_set (QState_vars ?v0)"
  let ?b = "sorted_list_of_set (QState_vars a)"
  let ?a = "?b @ ?s0" 
  have card_vars_a:"dim_vec (QState_vector a) = 2^card (QState_vars a)"
    by (simp add: QState_rel1' QState_vector.rep_eq uqstate_snd)
  moreover have finite_vars_a:"finite (QState_vars a)"
    by (simp add: QState_rel3')
  ultimately have 
    tensor_prod:"partial_state.tensor_vec (list_dims (QState_vars a))  {0::nat..<card ((QState_vars a))} 
                                (QState_vector a) (vCons (1) vNil) = QState_vector a"
    using idempoten_qstate by fastforce
  have  vars_v0:"QState_vars ?v0 = {}"
    by (simp add: QState_vars.rep_eq fst_uQState_empty)
  have  v0:"QState_vector ?v0 = vCons (1::'a::comm_ring_1) vNil"
    by (simp add: QState_vector.rep_eq snd_uQState_empty)
  have  s:"(QState_vars a) \<union> (QState_vars ?v0) = (QState_vars a)"
    by (simp add: QState_vars_id)
  then have  "sorted_list_of_set ((QState_vars a) \<union> (QState_vars ?v0)) = sorted_list_of_set (QState_vars a)"
    by metis
  moreover have  "sorted_list_of_set (QState_vars a)@sorted_list_of_set (QState_vars ?v0) = 
              sorted_list_of_set (QState_vars a)"
    by (simp add: vars_v0)
  then have  "QState_list a = (QState_list a).\<^sub>?a \<^sub>\<leadsto> \<^sub>?b"
    using eq_vector_same_permutation
    by (metis QState_rel1' distinct_card distinct_sorted_list_of_set 
          finite_vars_a set_sorted_list_of_set)    
  then show ?thesis unfolding plus_QState_vector_def Let_def
     using s v0 tensor_prod   apply transfer'
     by (simp add: list_vec )
qed

definition plus_QState:: "('q::linorder,'a::comm_ring_1) QState \<Rightarrow> ('q,'a::comm_ring_1) QState \<Rightarrow> ('q,'a::comm_ring_1) QState"
  where "plus_QState q1 q2 \<equiv> 
    let d1 = (QState_vars q1); d2 = (QState_vars q2) in
      if (d1 \<inter> d2 \<noteq> {}) then QState ({},[1])
      else QState (plus_QState_vector q1 q2)"

definition disj_QState::"('q,'a::comm_ring_1) QState \<Rightarrow> ('q,'a::comm_ring_1) QState \<Rightarrow> bool"
  where "disj_QState q1 q2 \<equiv> QState_vars q1 \<inter> QState_vars q2 = {}"

(* lift_definition disj_QState :: "('q,'a::comm_ring_1) QState \<Rightarrow> ('q,'a::comm_ring_1) QState \<Rightarrow> bool" is
  "\<lambda>a b. fst a \<inter> fst b = {}" . *)

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


lemma dim_vec_plus_2_pow_s:
  assumes a0:"d1 = QState_vars q1" and a1:"d2 = QState_vars q2" and
          a2:"s = d1 \<union> d2" and a3:"l1 = QState_vector q1" and a4:"l2 = QState_vector q2" and
          a5:"ds = list_dims s" and
          a6:"v = partial_state.tensor_vec 
                     ds  {0..<card d1} l1 l2"  and a7:"d1 \<inter> d2 = {}"
  shows "dim_vec v = (2^(card s))"
proof-
  interpret ps2:partial_state ds  "{0..<card d1}" .
  have "dim_vec l1 = 2^card d1" 
    using a0  QState_rel1'[of q1] a3 apply transfer' by auto
  moreover have "dim_vec l2 = 2^card d2" 
    using a1  QState_rel1'[of q2] a4 apply transfer' by auto
  moreover have "finite d2"
    by (simp add: QState_rel3' a1)
  moreover have "finite d1" by (simp add: QState_rel3' a0)
  ultimately have "dim_vec v = prod_list ds"
    using a6  a5 a7 a2 unfolding ps2.tensor_vec_def   
  partial_state.tensor_vec_def  state_sig.d_def 
   partial_state.encode1_def partial_state.dims1_def 
    partial_state.encode2_def partial_state.dims2_def by auto
  thus ?thesis using a5 unfolding list_dims_def by auto
qed    
  

lemma plus_QState_vector_wf':
  assumes a9:"d1 \<inter> d2 = {}" and
          a0:"d1 = (QState_vars q1)" and a1:"d2 = (QState_vars q2)" and
          a2:"s = d1 \<union> d2" and a3:"l1 = QState_vector q1" and a4:"l2 = QState_vector q2" and
          a5:"ds = list_dims s" and
          a6:"v = partial_state.tensor_vec ds  {0..<card d1} l1 l2" and
          a7:"a = ((sorted_list_of_set d1)@(sorted_list_of_set d2))" and
          a8:"b = sorted_list_of_set s" 
        shows "length (((list_of_vec v).\<^sub>a \<^sub>\<leadsto> \<^sub>b)) =  (2^(card s))"
proof-
  have "dim_vec v = (2^(card s))" using dim_vec_plus_2_pow_s[OF a0 a1 a2 a3 a4 a5 a6 a9] by auto
  moreover have "distinct a"
    using QState_rel3' a0 a1 a7 a9 set_sorted_list_of_set by auto
  moreover have "length a = length b"
    by (metis QState_rel3' a0 a1 a2 a7 a8 a9 card_Un_disjoint distinct_card 
              distinct_sorted_list_of_set finite_UnI length_append set_sorted_list_of_set)
  moreover have "set a = set b"
    by (simp add: QState_rel3' a0 a1 a2 a7 a8)
  ultimately show ?thesis using change_orientation_length
    by (metis length_list_of_vec)
qed        

lemma plus_QState_vector_wf: assumes a0: "QState_vars q1 \<inter> QState_vars q2 = {}"
  shows "length (snd (plus_QState_vector q1 q2)) =
        2 ^ card (fst (plus_QState_vector q1 q2))"
  unfolding plus_QState_vector_def Let_def using a0
  apply clarsimp apply (frule plus_QState_vector_wf')  
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
    by (simp add: eq_vector_same_permutation tensor_neutral)
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



(* lift_definition plus_QState :: "('q,'a::comm_ring_1) QState \<Rightarrow> ('q,'a::comm_ring_1) QState \<Rightarrow> ('q,'a::comm_ring_1) QState" is  
  "\<lambda>a b. let d1 = fst a; d2 = fst b; s = d1 \<union> d2; l1 = snd a; l2 = snd b;
             dims = list_dims s;
              v = partial_state2.ptensor_vec 
                     dims (lin_set d1) (lin_sets (top_lin_set d1) d2) 
                         (vec_of_list l1)  (vec_of_list l2) in
                  QState (s,list_of_vec v)" . *)


(* lemma uQState_fst_id_ptensor:"
       (partial_state.tensor_vec (list_dims (d \<union> {}))
          {0..<card d1}  v (vCons 1 vNil)) = v"  
  unfolding list_dims_def lin_set_def lin_sets_def top_lin_set_def apply auto
  using list_ptensor_neutral apply blast  
  apply (fastforce simp add: fst_uQState_empty_snd_1 list_ptensor_neutral) sorry
  by (metis QState_rel1 dim_vec_of_list equals0D idempoten_qstate list_vec) *)


lemma plus_idem:"plus_QState a (QState ({},[1])) = a"
proof-
  {
    assume a00:"QState_vars a = {}"
    have ?thesis
      by (metis (no_types, lifting) QState_empty QState_refl 
          QState_vars_Plus QState_vars_id a00 fst_conv plus_QState_vector_def) 
  }
  moreover {
    let ?n = "QState ({},[1])"
    assume a00:"QState_vars a \<noteq>{}"
    have "fst (plus_QState_vector a ?n) = QState_vars a"
      by (metis QState_vars_id fst_conv plus_QState_vector_def)
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
  

value "digit_decode [2,2] (nths (digit_encode [2,2,2,2] 4) {2,3})"

lemma
  assumes a0:"dim_vec (vx::('a::comm_ring_1) vec) = (2::nat) ^ card varx" and
          a1:"dim_vec (vy::('a::comm_ring_1) vec) = (2::nat) ^ card vary" and
          a2:"finite vary" and a3:"varx = {}"
shows"list_of_vec
     (partial_state.tensor_vec (list_dims (varx \<union> vary)) {0..<card (vary)} vy vx) =
    list_of_vec
     (partial_state.tensor_vec (list_dims (varx \<union> vary)) {0..<card (varx)} vx vy) . 
                      \<^sub>(sorted_list_of_set varx @ sorted_list_of_set vary) \<^sub>\<leadsto>  
                      \<^sub>(sorted_list_of_set vary @ sorted_list_of_set varx)"
proof-
  interpret st1:partial_state "(list_dims (varx \<union> vary))" .

  have "partial_state.tensor_vec (list_dims (varx \<union> vary)) {0..<card (vary)} vy vx = vx"
    using a0 a1 a2 a3 idempoten_qstate
  show ?thesis sorry
qed 

lemma 
  assumes a0:"dim_vec (vx::('a::comm_ring_1) vec) = (2::nat) ^ card varx" and
          a1:"dim_vec (vy::('a::comm_ring_1) vec) = (2::nat) ^ card vary" and
          a2:"finite varx" and a3:"finite vary"
shows"list_of_vec
     (partial_state.tensor_vec (list_dims (varx \<union> vary)) {0..<card (vary)} vy vx) =
    list_of_vec
     (partial_state.tensor_vec (list_dims (varx \<union> vary)) {0..<card (varx)} vx vy) . 
                      \<^sub>(sorted_list_of_set varx @ sorted_list_of_set vary) \<^sub>\<leadsto>  
                      \<^sub>(sorted_list_of_set vary @ sorted_list_of_set varx)"
proof-
  show ?thesis sorry
qed 

lemma comm_plus_QState_vector:
  assumes a0:"QState_vars x  \<inter> QState_vars y = {}"
  shows "snd (plus_QState_vector x y) = snd (plus_QState_vector y x)"
proof-
  let ?s = "QState_vars x \<union> QState_vars y"
  let ?x = "QState_vector x" and ?y = "QState_vector y"
  let ?vx = "QState_vars x" and  ?vy = "QState_vars y"
  let ?svx = "sorted_list_of_set ?vx" and ?svy = "sorted_list_of_set ?vy" and
      ?svs = "sorted_list_of_set ?s"
  let ?svxy = "?svx @ ?svy" and  ?svyx = "?svy @ ?svx"
  let ?tpxy = "partial_state.tensor_vec (list_dims ?s) {0..<card ?vx} ?x ?y"
  let ?tpyx = "partial_state.tensor_vec (list_dims ?s) {0..<card ?vy} ?y ?x"
  have  list:"(list_of_vec ?tpyx) = (list_of_vec ?tpxy). \<^sub>?svxy \<^sub>\<leadsto> \<^sub>?svyx" sorry
  then have  "(list_of_vec ?tpxy). \<^sub>?svxy \<^sub>\<leadsto> \<^sub>?svs  = (list_of_vec ?tpyx). \<^sub>?svyx \<^sub>\<leadsto> \<^sub>?svs" 
    using ordering_permutation_eq_orientation
    by (smt QState_rel3' add.commute assms list dim_vec_plus_2_pow_s 
           distinct_append distinct_card distinct_sorted_list_of_set length_append 
             length_list_of_vec plus_QState_set_wf 
            set_append sorted_list_of_set(1) sup_commute)
    
  then show ?thesis unfolding plus_QState_vector_def Let_def
    by (metis sup_commute)
qed

lemma plus_comm:"disj_QState x y \<Longrightarrow> plus_QState x y = plus_QState y x"
proof-
  assume "disj_QState x y"
  then have disj:"QState_vars x  \<inter> QState_vars y = {}"
    unfolding disj_QState_def by auto
  have "QState_vars (plus_QState x y)  = QState_vars (plus_QState y x)"
    by (metis QState_vars_Plus fst_conv inf_commute plus_QState_vector_def sup_commute)
  moreover have "snd (plus_QState_vector x y) = snd (plus_QState_vector y x)"
    using comm_plus_QState_vector disj by auto
  then have  "QState_list  (plus_QState x y) = QState_list (plus_QState y x)"    
    by (simp add: QState_list_Plus disj inf_commute)     
  ultimately show "plus_QState x y = plus_QState y x" using q_state_eq by auto
qed

lemma plus_assoc:" \<lbrakk>disj_QState x y; disj_QState y z; disj_QState x z\<rbrakk>
       \<Longrightarrow> plus_QState (plus_QState x y) z = plus_QState x (plus_QState y z)"
  sorry


lemma plus_disj_dist:"\<lbrakk>disj_QState x (plus_QState y z); disj_QState y z\<rbrakk> \<Longrightarrow> disj_QState x y"
  sorry

lemma plus_dis_dist2:" \<lbrakk>disj_QState x (plus_QState y z); disj_QState y z\<rbrakk> \<Longrightarrow> disj_QState (plus_QState x y) z"
  sorry



instantiation QState :: (linorder,comm_ring_1) sep_algebra
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
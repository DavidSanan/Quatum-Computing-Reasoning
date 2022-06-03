theory Q_State_Tensor
  imports Q_State
begin

datatype QStateT = Single QStateM | Plus QStateT QStateT

fun QStateT_QStates::"QStateT \<Rightarrow> QStateM list"
  where "QStateT_QStates (Single Q) = [Q]"
  | "QStateT_QStates (Plus Q1 Q2) = QStateT_QStates Q1 @ QStateT_QStates Q2"


definition QStateT_trav::"QStateT \<Rightarrow> QStateM \<times> bool"
  where "QStateT_trav Q \<equiv> foldr (\<lambda>a b. (a + (fst b), a ## (fst b) \<and> snd b)) (QStateT_QStates Q) (0,True)"

definition QStateT_Plus::"QStateT \<Rightarrow> QStateM"
  where "QStateT_Plus Q \<equiv> fst (QStateT_trav Q)"


definition QStateT_disj::"QStateT \<Rightarrow> bool"
  where "QStateT_disj Q \<equiv> snd (QStateT_trav Q)"

fun QStateT_Plus_tree::"QStateT \<Rightarrow> QStateM" ("QT")
  where "QStateT_Plus_tree (Single Q) = Q"
  | "QStateT_Plus_tree (Plus Q1 Q2) = QStateT_Plus_tree Q1 + QStateT_Plus_tree Q2"

fun QStateT_Plus_comb::"QStateT \<Rightarrow> QStateM \<times> bool"
  where "QStateT_Plus_comb (Single Q) = (Q,True)"
  | "QStateT_Plus_comb (Plus Q1 Q2) = (let (QM1, res1) = QStateT_Plus_comb Q1;
                                          (QM2, res2) = QStateT_Plus_comb Q2 in
                                         (QM1 + QM2, QM1 ## QM2))"
lemma "QStateT_Plus_tree (Single Q) = Q"
  by auto

definition equiv_QStateT::"QStateT \<Rightarrow> QStateT \<Rightarrow> bool"
  where "equiv_QStateT Q1 Q2 \<equiv> QStateT_Plus_tree Q1 = QStateT_Plus_tree Q2"

quotient_type QStateE = "QStateT" / equiv_QStateT
  morphisms rep QStateE
  apply (rule equivpI)
    apply (rule reflpI) 
  apply (simp add: equiv_QStateT_def) 
   apply (auto  intro: sympI simp add: equiv_QStateT_def )
  by (auto simp add: transp_def equiv_QStateT_def)

lift_definition QStateT::"QStateE \<Rightarrow> QStateT" is "Single o QStateT_Plus_tree"
  by (simp add: equiv_QStateT_def) 

lift_definition plus_E::"QStateE \<Rightarrow> QStateE \<Rightarrow> QStateE" is Plus 
  unfolding equiv_QStateT_def by auto

lift_definition disjoint_union::"QStateE \<Rightarrow> QStateE \<Rightarrow> bool" is "\<lambda>s1 s2. QT s1 ## QT s2"
  unfolding equiv_QStateT_def
  by simp

lemma eq_QState:"QStateE Q1 = QStateE Q2 \<Longrightarrow> QStateT_Plus_tree Q1 = QStateT_Plus_tree Q2"
  apply transfer' unfolding equiv_QStateT_def by auto

definition set_QState::"QStateM \<Rightarrow> QStateT set" ("{}\<^sub>_")
  where "set_QState Q = {Q'. QStateE Q' = QStateE (Single Q)}"

lemma QStateT_Plus_is_tensor:
  "QStateT_Plus_tree (Plus (Single Q1) (Single Q2)) = Q1 + Q2"
  by simp


lemma QStateE_QState_Q:"Q1 \<in> {}\<^sub>Q \<Longrightarrow> QStateT_Plus_tree Q1 = Q"
  by (simp add: eq_QState set_QState_def)

lemma product_Q_empty_in_QStateE_Q:"Plus (Single Q) (Single 0) \<in> {}\<^sub>Q"
  unfolding set_QState_def apply transfer
  by (simp add: equiv_QStateT_def)

lemma exits_product_Q_empty:"\<forall>Q. \<exists>Q'\<in> {}\<^sub>Q. Q' = Plus (Single Q) (Single 0)"
  using product_Q_empty_in_QStateE_Q by auto

lemma "QStateE(Single 0) = QStateE(Plus (Single 0) (Single 0))"
proof-
  have "QT (Plus (Single 0) (Single 0)) = 0" by auto
  moreover have "QT(Single 0) = 0" by auto
  ultimately show ?thesis
    using product_Q_empty_in_QStateE_Q set_QState_def by force
qed

lemma "QStateE(Single x) = QStateE(Plus (Single x) (Single 0))"
  using product_Q_empty_in_QStateE_Q set_QState_def by force

instantiation QStateE ::  sep_algebra
begin
definition zero_QStateT: "0 \<equiv> QStateE (Single 0)"
definition plus_QStateT: "s1 + s2 \<equiv> plus_E s1 s2" 
definition sep_disj_QStateT: "s1 ## s2 \<equiv> disjoint_union s1 s2"

lemma h:"QStateM_map x + QStateM_map 0 = QStateM_map x"
  unfolding zero_QStateM using Qstate_map_0_0
  by (simp add: Qstate_map_0_0) 

lemma "plus_E x 0 = x"
  unfolding zero_QStateT
  apply transfer'
  by (simp add: equiv_QStateT_def) 
  

lemma disjoint_union_0:"(x::QStateE) ## 0"
proof -
  fix x :: QStateE
  have "disjoint_union x (QStateE (Single 0))" apply transfer' by auto
  then show "x ## 0"
    by (simp add: Q_State_Tensor.sep_disj_QStateT zero_QStateT)
qed

instance 
  apply standard
   using disjoint_union_0 zero_QStateT apply fastforce
   unfolding sep_disj_QStateT zero_QStateT plus_QStateT
        apply (transfer', auto simp add: sep_disj_commute) 
       apply (transfer') apply(auto simp add: equiv_QStateT_def)[1]
      apply transfer'
        using sep_add_commute apply (auto simp add: equiv_QStateT_def sep_add_commute)[1]
          apply transfer'
        apply (simp add: equiv_QStateT_def sep_add_assoc)
         apply transfer'
        using sep_disj_addD1 apply auto[1]
      apply transfer'
      by (simp add: sep_disj_addI1)
end



end
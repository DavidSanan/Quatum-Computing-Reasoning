theory QStateVector
  imports Q_State
begin

definition equiv_qstate::"QState \<Rightarrow> QState \<Rightarrow> bool"
  where "equiv_qstate k l \<equiv> 
          (\<exists>c. QState_vector k = c \<cdot>\<^sub>v (QState_vector l) \<and>  QState_vars k = QState_vars l)"



definition equiv_qstatea::"QState \<Rightarrow> QState \<Rightarrow> bool"
  where "equiv_qstatea k l \<equiv> \<exists>c. k = c \<cdot>\<^sub>q l \<and> \<bar>c\<bar> = 1"

lemma equiv_qstates:"equiv_qstatea k l = equiv_qstate k l"
  unfolding equiv_qstatea_def equiv_qstate_def sca_mult_qstate_def 
  apply auto
  using sca_mult_qstate_def sca_mult_qstate_quantum apply auto[1]
  apply (simp add: QState_var_idem sca_mult_qstate_wf)
  using QState_var_idem sca_mult_qstate_wf apply blast
  by (metis QState_list.rep_eq QState_refl QState_rel3' QState_vector.rep_eq list_vec
         mult.right_neutral norm_complex_absolutely_homogenous)

lemma equiv_qstate_sym:"equiv_qstate k l = equiv_qstate l k"
  unfolding equiv_qstate_def 
  apply auto
  by (metis QState_rel3' equiv_comm equiv_vectors_def mult_cancel_left2 
      norm_complex_absolutely_homogenous)+ 
  

quotient_type (overloaded) QState_equiv = "QState" / equiv_qstate
  morphisms rep QState_equiv
  apply (rule equivpI)
  apply (rule reflpI)
    apply (metis  equiv_qstate_def one_smult_vec)
   apply (simp add: sympI equiv_qstate_sym) 
  apply (auto simp add: transp_def equiv_qstate_def)
  by (metis  smult_smult_assoc)


lemma "QState_equiv a = QState_equiv b  \<Longrightarrow>
      \<exists>c. QState_vector a = c \<cdot>\<^sub>v QState_vector b \<and>  QState_vars a = QState_vars b"
  by (simp add: QState_equiv.abs_eq_iff equiv_qstate_def)

lemma "QState_vector a = c \<cdot>\<^sub>v QState_vector b \<and> QState_vars a = QState_vars b \<Longrightarrow>
       QState_equiv a = QState_equiv b"
  using QState_equiv.abs_eq_iff equiv_qstate_def by blast
 

quotient_definition "QVector :: QState_equiv \<Rightarrow> complex list" is "QState_list" 
  sorry

quotient_definition "sca_mult :: complex \<Rightarrow> QState_equiv \<Rightarrow> QState_equiv" 
is "sca_mult_qstate"  using sca_mult_qstate_quantum 
  unfolding equiv_qstate_def equiv_qstatea_def sca_mult_qstate_def   
  apply auto 
  apply (metis QState.rep_eq QState_list.rep_eq QState_rel3' QState_vector.rep_eq mult.commute mult.right_neutral norm_complex_absolutely_homogenous one_smult_vec sca_mult_qstate_def sca_mult_qstate_quantum smult_smult_assoc snd_conv vec_list)
  apply (smt (verit, best) QState.rep_eq QState_rel3' QState_vars.rep_eq QState_wf_def fst_conv index_smult_vec(2) length_list_of_vec norm_complex_absolutely_homogenous sca_mult_qstate_def snd_conv vec_list)
  by (metis QState_list.rep_eq QState_refl QState_rel3 QState_vector.rep_eq QState_wf eq_QState_dest mult_cancel_left2 norm_complex_absolutely_homogenous sca_mult_qstate_def sca_mult_qstate_vars vec_list)

lemma QVe_tensor_product1:
  assumes 
    a0:"QState_vars x \<inter> QState_vars xa = {}" and
    a1:"QState_vars y \<inter> QState_vars ya = {}" and 
    a2:"QState_vars x = QState_vars y" and 
    a3:"QState_vars xa = QState_vars ya" and
    a4:"q \<in> QState_vars (QState (plus_QState_vector x xa))"
  shows" q \<in> QState_vars (QState (plus_QState_vector y ya))"
  using QState_vars_Plus a0 a2 a3 a4 plus_QState_def plus_QState_vector_vars by auto

lemma QVe_tensor_product2:
  assumes a0:"QState_vars x \<inter> QState_vars xa = {}" and
    a1:"QState_vars y \<inter> QState_vars ya = {}" and
    eq_vars_x:"QState_vars x = QState_vars y" and 
    eq_vars_y:"QState_vars xa = QState_vars ya" and
    equiv_x_y: "QState_vector x = c1 \<cdot>\<^sub>v (QState_vector y)" and
    equiv_xa_ya: "QState_vector xa = c2 \<cdot>\<^sub>v (QState_vector ya)" and
    normc1:"\<bar>c1\<bar> = 1" and normc2:"\<bar>c2\<bar> = 1"
  shows "\<exists>c. QState_vector (QState (plus_QState_vector x xa)) =
        c \<cdot>\<^sub>v QState_vector (QState (plus_QState_vector y ya))"
proof-
  let ?dx = "QState_vars x" and ?dxa = "QState_vars xa" and
      ?dy = "QState_vars y" and ?dya = "QState_vars ya" 
  let ?vx = "QState_vector x" and ?vxa = "QState_vector xa" and
      ?vy = "QState_vector y" and ?vya = "QState_vector ya"
  have plus:"plus_QState_vector x xa = 
        (?dx \<union>  ?dxa, 
        list_of_vec(partial_state2.ptensor_vec ?dx ?dxa ?vx ?vxa))"
    unfolding plus_QState_vector_def Let_def by auto
  also have "(?dx \<union>  ?dxa, 
              list_of_vec(partial_state2.ptensor_vec ?dx ?dxa ?vx ?vxa)) = 
             (?dy \<union>  ?dya, 
              list_of_vec(partial_state2.ptensor_vec ?dy ?dya (c1 \<cdot>\<^sub>v ?vy) (c2 \<cdot>\<^sub>v ?vya)))"
    using eq_vars_x eq_vars_y equiv_x_y equiv_xa_ya by presburger
  also have ptensory:"partial_state2.ptensor_vec ?dy ?dya (c1 \<cdot>\<^sub>v ?vy) (c2 \<cdot>\<^sub>v ?vya) =
             (c1*c2) \<cdot>\<^sub>v partial_state2.ptensor_vec ?dy ?dya ?vy ?vya"
    by (simp add: QState_rel1a' QState_rel2' a1 pscalar_ptensor)
  also have "
   (QState_vars y \<union> QState_vars ya,
   list_of_vec
    (ptensor_vec (QState_vars y) (QState_vars ya) (QState_vector y)
      (QState_vector ya))) = plus_QState_vector y ya "
    unfolding plus_QState_vector_def Let_def by auto
  ultimately have "QState_vector (QState (plus_QState_vector x xa)) = 
                    (c1*c2) \<cdot>\<^sub>v partial_state2.ptensor_vec ?dy ?dya ?vy ?vya" and
                  "QState_vector (QState (plus_QState_vector y ya)) = 
                     partial_state2.ptensor_vec ?dy ?dya ?vy ?vya"
    by (metis QState_list_Plus QState_vector.rep_eq a0 a1
           plus_QState_def snd_conv uqstate_snd vec_list)+
  then show ?thesis  by auto
qed

quotient_definition "QVe_tensor_product::QState_equiv \<Rightarrow> QState_equiv \<Rightarrow> QState_equiv"
is plus_QState 
proof-
  fix x y xa ya
  assume a0:"equiv_qstate x y" and 
       a1:"equiv_qstate xa ya" 
  then obtain c1 c2 where
       eq_vars_x:"QState_vars x = QState_vars y" and 
       eq_vars_y:"QState_vars xa = QState_vars ya" and
       equiv_x_y: "QState_vector x = c1 \<cdot>\<^sub>v (QState_vector y)" and
       equiv_xa_ya: "QState_vector xa = c2 \<cdot>\<^sub>v (QState_vector ya)"
    unfolding equiv_qstate_def by auto 
  then have normc1:"\<bar>c1\<bar> = 1" and normc2:"\<bar>c2\<bar> = 1"
    using QState_sca_mult_norm_eq_1 by auto
  { assume a00:"QState_vars x \<inter> QState_vars xa \<noteq> {}"
    moreover have "QState_vars y \<inter> QState_vars ya \<noteq> {}"
      using eq_vars_x eq_vars_y calculation by auto
    ultimately have "equiv_qstate (plus_QState x xa) (plus_QState y ya)"
      unfolding equiv_qstate_def plus_QState_def Let_def 
      using Q_State.sca_mult_qstate_one by force
  }
  moreover { 
    assume a00:"QState_vars x \<inter> QState_vars xa = {}"
    moreover have "QState_vars y \<inter> QState_vars ya = {}"
      using eq_vars_x eq_vars_y calculation by auto
    ultimately have "equiv_qstate (plus_QState x xa) (plus_QState y ya)"
      unfolding equiv_qstate_def plus_QState_def Let_def apply auto
        prefer 2
      using QVe_tensor_product1 eq_vars_x eq_vars_y apply blast
       prefer 2
      using QVe_tensor_product1 eq_vars_x eq_vars_y apply blast
      using eq_vars_x eq_vars_y equiv_x_y equiv_xa_ya normc1 normc2
      QVe_tensor_product2 by auto
  }
  ultimately show "equiv_qstate (plus_QState x xa) (plus_QState y ya)" by auto
qed


quotient_definition 
  "mult_mat_eq_qstate::complex mat \<Rightarrow> QState_equiv \<Rightarrow> QState_equiv" is mult_mat_qstate
proof-
  fix x y M
  assume a0:"equiv_qstate x y" 
  then have eq_vars_x:"QState_vars x = QState_vars y"
    unfolding equiv_qstate_def by auto 
  have f1: "equiv_qstate (M *\<^sub>q x) (M *\<^sub>q x)"
    by (simp add: QState_equiv_equivp equivp_reflp)
  have f2: "x = QState (QState_unfold x)"
    by (simp add: QState_refl)
  have "QState_list x = QState_list y"
    by (meson QVector.rsp a0 apply_rsp')
  then show "equiv_qstate (M *\<^sub>q x) (M *\<^sub>q y)"
    using f2 f1 QState_refl eq_vars_x by fastforce
qed
  
end
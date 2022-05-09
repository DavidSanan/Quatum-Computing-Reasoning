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
  

quotient_type (overloaded) QStateE = "QState" / equiv_qstate
  morphisms rep QStateE                            
  apply (rule equivpI)
  apply (rule reflpI)
    apply (metis  equiv_qstate_def one_smult_vec)
   apply (simp add: sympI equiv_qstate_sym) 
  apply (auto simp add: transp_def equiv_qstate_def)
  by (metis  smult_smult_assoc)


lemma QStateE_dest:"QStateE a = QStateE b  \<Longrightarrow>
      \<exists>c. QState_vector a = c \<cdot>\<^sub>v QState_vector b \<and>  QState_vars a = QState_vars b"
  by (simp add: QStateE.abs_eq_iff equiv_qstate_def)

lemma QStateE_intro:"QState_vector a = c \<cdot>\<^sub>v QState_vector b \<and> QState_vars a = QState_vars b \<Longrightarrow>
       QStateE a = QStateE b"
  using QStateE.abs_eq_iff equiv_qstate_def by blast
 


lift_definition sca_mult :: "complex \<Rightarrow> QStateE \<Rightarrow> QStateE" (infixl "\<cdot>\<^sub>q\<^sub>e" 70) 
is "sca_mult_qstate"  using sca_mult_qstate_quantum 
  unfolding equiv_qstate_def equiv_qstatea_def sca_mult_qstate_def   
  apply auto 
  apply (metis QState.rep_eq QState_list.rep_eq QState_rel3' QState_vector.rep_eq mult.commute mult.right_neutral norm_complex_absolutely_homogenous one_smult_vec sca_mult_qstate_def sca_mult_qstate_quantum smult_smult_assoc snd_conv vec_list)
  apply (smt (verit, best) QState.rep_eq QState_rel3' QState_vars.rep_eq QState_wf_def fst_conv index_smult_vec(2) length_list_of_vec norm_complex_absolutely_homogenous sca_mult_qstate_def snd_conv vec_list)
  by (metis QState_list.rep_eq QState_refl QState_rel3 QState_vector.rep_eq QState_wf eq_QState_dest mult_cancel_left2 norm_complex_absolutely_homogenous sca_mult_qstate_def sca_mult_qstate_vars vec_list)

lemma sca_mult_QE:"c \<cdot>\<^sub>q\<^sub>e QStateE Q = QStateE (c \<cdot>\<^sub>q Q)"
  using QStateVector.sca_mult.abs_eq by auto
  
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

lift_definition plus_QStateE::"QStateE \<Rightarrow> QStateE \<Rightarrow> QStateE"
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

lemma plus_QStateE_eq:"plus_QStateE (QStateE Q1) (QStateE Q2) = QStateE (Q1 + Q2)"
  unfolding plus_QState apply transfer'
  by (simp add: QStateE_equivp equivp_reflp)


lemma Mat_mul_preserves_quotient:
  assumes a0:"x = (c::complex)  \<cdot>\<^sub>v y " and a1:"dim_col M = dim_vec x"
  shows "M *\<^sub>v x  = c \<cdot>\<^sub>v (M *\<^sub>v y)"
proof-
  have "M *\<^sub>v x =  M *\<^sub>v (c  \<cdot>\<^sub>v y)" using a0 by auto
  moreover have "dim_vec x = dim_vec y"
    using a0 index_smult_vec(2) by blast
  ultimately show ?thesis using  a1 by auto
qed



lemma vec_normalize_preserves_quotient:
  assumes a0:"x =  (c::complex)  \<cdot>\<^sub>v y " and a1:"\<bar>c\<bar> = 1"
  shows "vec_normalize x = c  \<cdot>\<^sub>v vec_normalize y"
proof-
  { assume "x = 0\<^sub>v (dim_vec x)"
    then have ?thesis
      unfolding vec_normalize_def using a0 a1 apply auto
      by (metis carrier_vec_dim_vec vec_norm_id 
          vec_norm_zero zero_carrier_vec) 
  }
  moreover { assume a00:"x \<noteq> 0\<^sub>v (dim_vec x)"
    then have a00':"y\<noteq> 0\<^sub>v (dim_vec y)"
      by (metis a0 a1 carrier_vec_dim_vec vec_norm_id vec_norm_zero) 
    have "vec_normalize x = vec_normalize (c \<cdot>\<^sub>v y)"
      using a0 by auto
    also have "vec_normalize (c \<cdot>\<^sub>v y) =  
             1/ (vec_norm(y))  \<cdot>\<^sub>v (c \<cdot>\<^sub>v y)"
      using a0 a1 unfolding vec_normalize_def apply auto
      by (metis    vec_norm_id )
    also have "1/ (vec_norm(y))  \<cdot>\<^sub>v (c \<cdot>\<^sub>v y) = 
             c \<cdot>\<^sub>v (1/ (vec_norm(y)) \<cdot>\<^sub>v y)"
      by (simp add: mult.commute smult_smult_assoc)
    finally have ?thesis unfolding vec_normalize_def using a00 a00'
      by simp
  }
  ultimately show ?thesis by auto
qed
  


lift_definition
  mult_mat_eq_qstate::"complex mat \<Rightarrow> QStateE \<Rightarrow> QStateE" (infixl "*\<^sub>E" 70)  
is mult_mat_qstate 
proof-
{ fix x y M
  assume a0:"equiv_qstate x y" 
  then have eq_vars_x:"QState_vars x = QState_vars y"
    unfolding equiv_qstate_def by auto 
  moreover obtain c where quot:"x = c \<cdot>\<^sub>q y" and norm1:"\<bar>c\<bar> = 1"
    using a0 equiv_qstatea_def equiv_qstates by blast 
  {
    assume a00:"M \<in> carrier_mat (2^(card (QState_vars x))) (2^(card (QState_vars x)))" and
           a01:"M *\<^sub>v (QState_vector x)\<noteq> 0\<^sub>v (dim_row M)" 
    then have "M *\<^sub>v QState_vector x  = c \<cdot>\<^sub>v (M *\<^sub>v QState_vector y)"
      using Mat_mul_preserves_quotient
      by (metis QState_rel1a' carrier_matD(2) norm1 quot sca_mult_qstate_quantum) 
    moreover have "vec_normalize (M *\<^sub>v QState_vector x) = c \<cdot>\<^sub>v vec_normalize (M *\<^sub>v QState_vector y)"
      using vec_normalize_preserves_quotient[OF _ norm1] calculation
      by auto
    moreover have "QState_wf (QState_vars x, list_of_vec (vec_normalize (M *\<^sub>v QState_vector x)))"
      using mult_mat_qstate_wf[OF ] using a01  a00
      by metis
    ultimately have "M *\<^sub>q x = c \<cdot>\<^sub>q (M *\<^sub>q y)"
      unfolding mult_mat_qstate_def sca_mult_qstate_def 
      by (smt (verit, ccfv_threshold) QState.rep_eq QState_var_idem QState_vector.rep_eq
              QState_wf_def a00 carrier_matD(1) carrier_matD(2) dim_mult_mat_vec eq_vars_x 
            mult_mat_qstate_wf norm1 one_neq_zero snd_conv 
         vec_list vec_norm_id vec_norm_zero vec_normalize_def zero_carrier_vec) 
    then have "equiv_qstate (M *\<^sub>q x) (M *\<^sub>q y)"
      using equiv_qstate_def norm1 sca_mult_qstate_quantum sca_mult_qstate_vars by auto
  }
  moreover{
    assume a00:"(M::complex mat) \<notin> carrier_mat (2^(card (QState_vars x))) (2^(card (QState_vars x)))" 
    then have "equiv_qstate (M *\<^sub>q x) (M *\<^sub>q y)"
      by (simp add: QStateE_equivp eq_vars_x equivp_reflp mult_mat_no_wf_empty)
  } note M_not_dim_equiv = this
  moreover{
    assume a00:"M *\<^sub>v (QState_vector x) =  0\<^sub>v (dim_row M)" 
    { assume a000:"dim_col M = dim_vec (QState_vector x)"
      have "M *\<^sub>v (QState_vector x) = c \<cdot>\<^sub>v (M *\<^sub>v (QState_vector y))"
        using Mat_mul_preserves_quotient
        using a000 norm1 quot sca_mult_qstate_quantum by presburger
      then have "equiv_qstate (M *\<^sub>q x) (M *\<^sub>q y)" 
        unfolding equiv_qstate_def
        by (metis  a00  mult_mat_no_wf_empty norm1 one_smult_vec 
            smult_carrier_vec vec_norm_id vec_norm_zero zero_carrier_vec)
    }
    moreover { assume a000:"dim_col M \<noteq> dim_vec (QState_vector x)"
      then have "equiv_qstate (M *\<^sub>q x) (M *\<^sub>q y)" 
        unfolding equiv_qstate_def
        using QState_rel1a'  M_not_dim_equiv equiv_qstate_def by auto
    } ultimately have "equiv_qstate (M *\<^sub>q x) (M *\<^sub>q y)" by auto
  } ultimately have "equiv_qstate (M *\<^sub>q x) (M *\<^sub>q y)" by fastforce
} then show "\<And>mat QState1 QState2.
       equiv_qstate QState1 QState2 \<Longrightarrow>
       equiv_qstate (mat *\<^sub>q QState1) (mat *\<^sub>q QState2)" by auto
qed

lemma mult_mat_QE:"M *\<^sub>E (QStateE Q) = QStateE (M *\<^sub>q Q)"
  apply transfer
  by (simp add: QStateE_equivp equivp_reflp) 

lift_definition dim_vec_E::"QStateE \<Rightarrow> nat" is "\<lambda>s. dim_vec(QState_vector s)"
  unfolding equiv_qstate_def 
  apply transfer' apply auto
  by (metis dim_vec_of_list index_smult_vec(2))


lift_definition 
 QStateE_vars::"QStateE \<Rightarrow> nat set" is QState_vars unfolding equiv_qstate_def by auto

lemma eq_QVars_empty:
  shows "(QState_vars Q = {}) = (QStateE_vars (QStateE Q) = {})" 
  apply transfer by auto
  
lemma eq_QVar_empty_empty:
  assumes a0:"QStateE_vars (QStateE Q) = {}"
  shows "\<exists>c. Q = c \<cdot>\<^sub>q |>"
  using a0 apply transfer 
  by (metis QState.rep_eq QState_list.rep_eq QState_refl  QState_vars.rep_eq QState_vars_Plus 
            QState_vars_id disj_QState_def empty_qstate_def eq_tensor_inverse_QState fst_conv 
            inf_bot_right plus_QState plus_QState_def plus_QState_vector_a_idem
            plus_QState_vector_vars  prod.exhaust_sel sep_disj_QState )

lemma dim_vec_card_E:"dim_vec_E Q = 2 ^ card (QStateE_vars Q)"
  apply transfer'
  using QState_rel1a' by blast

lemma finite_vars_QStateE:"finite (QStateE_vars Q)"
  apply transfer
  by (simp add:  QState_rel2')


lemma sca_mult_qstatee_vars:"\<bar>s\<bar> = 1 \<Longrightarrow> QStateE_vars (s \<cdot>\<^sub>q\<^sub>e qs) = QStateE_vars qs"
  apply transfer'  
  unfolding sca_mult_qstate_def using QState_var_idem sca_mult_qstate_wf 
  by meson

lemma sca_mult_qstatee_assoc:"\<bar>a1\<bar> = 1 \<and> \<bar>a2\<bar> = 1
   \<Longrightarrow> a1 * a2 \<cdot>\<^sub>q\<^sub>e Q = a1 \<cdot>\<^sub>q\<^sub>e (a2 \<cdot>\<^sub>q\<^sub>e Q)"
  apply transfer apply auto
  by (simp add: QStateE_equivp equivp_reflp sca_mult_qstate_assoc)

instantiation QStateE:: sep_algebra 
begin

definition zero_QStateE: "0 \<equiv> QStateE |>"
definition plus_QStateE: "s1 + s2 \<equiv> plus_QStateE s1 s2"
definition sep_disj_QStateE: "s1 ## s2 \<equiv> QStateE_vars s1 \<inter> QStateE_vars s2 = {}"
instance
  apply standard
  unfolding sep_disj_QStateE zero_QStateE apply transfer'
  apply (simp add: QState_vars_empty empty_qstate_def)
       apply blast 
  unfolding empty_qstate_def plus_QStateE  apply transfer'
  unfolding equiv_qstate_def
  using plus_idem apply force
  apply transfer' unfolding equiv_qstate_def
     apply (metis disj_QState_def one_smult_vec plus_comm)
  apply transfer' unfolding equiv_qstate_def
    apply (metis Q_State.plus_assoc disj_QState_def one_smult_vec)
  apply transfer' apply auto
  using QState_vars_Plus plus_QState_vector_vars apply auto[1]
  apply transfer'
  by (meson disj_QState_def disjoint_iff_not_equal plus_dis_dist2)
end

lemma QStateE_vars_Plus:"(QStateE_vars q1 \<inter> QStateE_vars q2 \<noteq> {} \<longrightarrow>
          QStateE_vars (q1 + q2) = {}) \<and>        
       (QStateE_vars q1 \<inter> QStateE_vars q2 = {} \<longrightarrow> 
           QStateE_vars (q1 + q2) = QStateE_vars q1 \<union> QStateE_vars q2)" 
  unfolding plus_QStateE apply transfer' 
  by (auto simp add: QState_vars_Plus plus_QState_vector_vars)


lemma scalar_mult_QStateE_plus_l:
  "QStateE_vars \<Q>' \<noteq> {} \<and> \<bar>a\<bar> = 1  \<Longrightarrow> 
    \<Q>' ## \<Q>'' \<Longrightarrow> a  \<cdot>\<^sub>q\<^sub>e (\<Q>' + \<Q>'') = (a  \<cdot>\<^sub>q\<^sub>e \<Q>' + \<Q>'')"  
  unfolding plus_QStateE sep_disj_QStateE
  apply transfer'
  by (metis QStateE_equivp disj_QState_def equivp_reflp plus_QState 
            scalar_mult_QState_plus_l sep_disj_QState)

lemma scalar_mult_QStateE_plus_r: 
  assumes a0: "\<bar>a\<bar> = 1" and 
          a1:"Q' ## Q''" 
        shows "a  \<cdot>\<^sub>q\<^sub>e (Q' + Q'') = ( Q' + a  \<cdot>\<^sub>q\<^sub>e Q'')"
using a0 a1 unfolding plus_QStateE sep_disj_QStateE
  apply transfer'
  by (metis QStateE_equivp disj_QState_def equivp_reflp plus_QState 
     scalar_mult_QState_plus_r sep_disj_QState) 

(*lemma eq_tensor_inverse_QStateM_vector: 
  assumes a0:"Q1 ## Q2" and
       a1:"QStateE_vars Q1 = QStateE_vars Q1'" and
       a2:"QStateE_vars Q2 = QStateE_vars Q2'" and
       a3:"Q1 + Q2 = Q1' + Q2'" 
     shows "Q1 = Q1'" and "Q2 = Q2'"
  using a0 a1 a2 a3
  unfolding sep_disj_QStateE plus_QStateE apply transfer'
  apply auto unfolding equiv_qstate_def apply auto apply transfer' sorry
  apply (metis IntE IntI QState.rep_eq QState_list.rep_eq QState_list_Plus QState_rel1' QState_rel1a' QState_rel2' QState_rel3' QState_var_idem QState_vars.rep_eq QState_vars_Plus QState_vars_id QState_vector.rep_eq QState_wf QState_wf_def Un_iff all_not_in_conv disj_QState_def disjoint_iff disjoint_iff_not_equal distrib(4) empty_qstate_def eq_tensor_inverse_QState_vector equiv_qstate_def equiv_qstate_sym fst_uQState_empty inf_bot_right inf_commute list_vec mult_cancel_right1 norm_complex_absolutely_homogenous one_neq_zero plus_QState plus_QState_def plus_QState_vector_a_idem plus_QState_vector_vars plus_comm plus_idem prod.exhaust_sel sca_mult_qstate_def scalar_mult_QState_plus_l scalar_mult_QState_plus_r sep_disj_QState snd_uQState_empty sup_bot_left zero_QState) apply auto
  sorry
  using  QStateM_map_qstate QStateM_rel1 QStateM_vars.rep_eq  a0 a3
       disj_QState_def eq_tensor_inverse_QState_vector local.a1 local.a2
       qstate_def sep_disj_QState sep_disj_QStateM  apply auto
  by (metis)*)

lemma eq_tensor_inverse_QStateM_vector: 
  assumes a0:"Q1 ## Q2" and
       a1:"QStateE_vars Q1 = QStateE_vars Q1'" and
       a2:"QStateE_vars Q2 = QStateE_vars Q2'" and
       a3:"Q1 + Q2 = Q1' + Q2'" 
     shows "Q1 = Q1'" and "Q2 = Q2'"
proof-
  obtain QS1 QS2 QS1' QS2' where 
    QS1:"Q1 = QStateE QS1" and QS2:"Q2 = QStateE QS2" and 
    QS1':"Q1' = QStateE QS1'" and QS2':"Q2' = QStateE QS2'"
    by (metis Quotient_QStateE Quotient_abs_rep)
  then have "QS1##QS2" using a0 a1 a2 apply transfer'
    by (simp add: QStateE_vars.abs_eq disj_QState_def sep_disj_QState sep_disj_QStateE)
  moreover have "QState_vars QS1 = QState_vars QS1'"
    using QS1 QS1' QStateE_vars.abs_eq a1 by presburger
  moreover have "QState_vars QS2 = QState_vars QS2'"
    using QS2 QS2' QStateE_vars.abs_eq a2 by presburger
  moreover obtain c where "QS1 + QS2 = c \<cdot>\<^sub>q (QS1' + QS2')" and c:"\<bar>c\<bar> = 1"
    using a3 QS1 QS1' QS2 QS2' QStateE.abs_eq_iff 
         equiv_qstatea_def equiv_qstates plus_QStateE plus_QStateE_eq by auto 
  then have f5:"c \<cdot>\<^sub>q (QS1' + QS2') = (c \<cdot>\<^sub>q QS1') + (QS2')"
    unfolding sca_mult_qstate_def plus_QState
    using calculation(1) calculation(2) calculation(3) 
          disj_QState_def plus_QState sca_mult_qstate_def 
          scalar_mult_QState_plus_l sep_disj_QState by force
  then have "\<exists>c'. QS1 = (c' \<cdot>\<^sub>q(c \<cdot>\<^sub>q QS1')) \<and> QS2 =  (inverse(c')\<cdot>\<^sub>q(QS2')) \<and> \<bar>c'\<bar> = 1"
  proof-
    have f2':"QState_vars QS1 = QState_vars (c \<cdot>\<^sub>q QS1')"
      by (simp add: c calculation(2) sca_mult_qstate_vars)
    have f3':"QState_vars QS2 = QState_vars QS2'"
      by (simp add: calculation(3))
    have f5:"QS1 + QS2 = c \<cdot>\<^sub>q QS1' + QS2'"
      by (simp add: \<open>QS1 + QS2 = c \<cdot>\<^sub>q (QS1' + QS2')\<close> f5)
    show ?thesis
      using eq_tensor_inverse_QState'[OF calculation(1) f2' f3' f5] by auto
  qed
  then obtain c' where eq:"QS1 = (c' \<cdot>\<^sub>q(c \<cdot>\<^sub>q QS1')) \<and> QS2 =  (inverse(c')\<cdot>\<^sub>q(QS2')) \<and> \<bar>c'\<bar> = 1"
    by auto
  have "Q1 = Q1'" and "Q2 = Q2'" using eq QS1 QS1' c
    apply transfer' using QStateE_equivp
     apply (metis equiv_qstate_def equiv_qstate_sym sca_mult_qstate_quantum sca_mult_qstate_vars smult_smult_assoc)
    using eq QS2 QS2' c
      apply transfer' using QStateE_equivp
    by (metis QStateE.abs_eq_iff abs_inverse equiv_qstatea_def equiv_qstates inverse_1)
  then show "Q1 = Q1'" and "Q2 = Q2'" by auto
qed

type_synonym assrt = "QStateE set"

lemma "QStateE (QState({0},))"

definition ""

end
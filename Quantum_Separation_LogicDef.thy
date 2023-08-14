theory Quantum_Separation_LogicDef
  imports QSemantics
begin

context cancellative_sep_algebra 
begin
lemma Q2_is_zero:
  assumes a0:"Q = Q1 + Q2" and a1:"Q1 ## Q2" and a2:"Q = Q1"
  shows "Q2 = 0"
proof- 
  have "Q = Q + Q2" using a0 a2 by auto
  then show ?thesis
    by (metis a1 a2 local.disjoint_zero_sym local.sep_add_cancel local.sep_add_commute local.sep_add_zero_sym local.sep_disj_commute)  
qed
end

type_synonym ('s,'p) triplet = "('s state) assn \<times> 'p \<times> ('s state) assn"


definition comb_set::"('a \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'b set"
  where "comb_set f A B \<equiv> \<Union>a\<in>A. f a ` B " 


lemma "a \<in> A \<Longrightarrow> b \<in> B \<Longrightarrow> f a b \<in> comb_set f A B"  
  unfolding comb_set_def by auto

lemma "x \<in> comb_set f A B \<Longrightarrow> \<exists>a b. a \<in> A \<and> b \<in> B \<and> x = f a b"  
  unfolding comb_set_def by auto


definition stack\<^sub>s :: "('s state) set \<Rightarrow> 's set"
  where "stack\<^sub>s A \<equiv> fst ` (snd ` A)"

definition prob\<^sub>s :: "('s state) set \<Rightarrow> real set"
  where "prob\<^sub>s A \<equiv> fst ` A"

definition QState\<^sub>s :: "('s state) set \<Rightarrow>  QStateM set"
  where "QState\<^sub>s A \<equiv> snd ` (snd `  A)"


definition eq_stack::"(('s state) set) \<Rightarrow> (('s state) set) \<Rightarrow> 's set"
  where "eq_stack A B \<equiv> stack\<^sub>s A \<inter> stack\<^sub>s B"

definition eq_stack_S::"(('s state) set) \<Rightarrow> 's set \<Rightarrow> (('s state) set) "
  where "eq_stack_S A B \<equiv> {s. s \<in> A \<and> fst (snd s) \<in> B}"

lemma eq_stacks_AB: "stack\<^sub>s (eq_stack_S A (eq_stack A B)) = stack\<^sub>s (eq_stack_S B (eq_stack A B))"
  unfolding stack\<^sub>s_def eq_stack_S_def eq_stack_def
  apply auto
   apply (smt fst_conv image_iff mem_Collect_eq snd_conv)
  by (smt fst_conv image_iff mem_Collect_eq snd_conv)
  

lemma eq_stack_stackS1: "get_stack (a,b,c) \<in> (eq_stack A B) \<Longrightarrow> get_stack (a,b,c) \<in> stack\<^sub>s (eq_stack_S A (eq_stack A B))" 
  unfolding stack\<^sub>s_def eq_stack_S_def eq_stack_def
  apply auto
  by (smt fst_conv image_iff mem_Collect_eq snd_conv)

lemma  eq_stack_stackS2: "get_stack (a,b,c) \<in> stack\<^sub>s (eq_stack_S A (eq_stack A B)) \<Longrightarrow> get_stack (a,b,c) \<in> (eq_stack A B)"
  unfolding stack\<^sub>s_def eq_stack_S_def eq_stack_def
  apply auto
  by (smt fst_conv image_iff mem_Collect_eq snd_conv)

lemma eq_stack_stack:"stack\<^sub>s (eq_stack_S A (eq_stack A B)) = eq_stack A B"
  unfolding stack\<^sub>s_def eq_stack_S_def eq_stack_def
  apply rule using eq_stack_stackS1 apply blast
  using eq_stack_stackS2 by blast


lemma stack_set_intro:
  assumes a0:"(\<rho>a,\<sigma>,Q1) \<in> A" and a1:"(\<rho>b,\<sigma>,Q2) \<in> B"
  shows "\<sigma>\<in> eq_stack A B "
  using a0 a1 image_iff  unfolding eq_stack_def stack\<^sub>s_def by fastforce

lemma comb_set_prob\<^sub>s_intro:
  assumes 
   a0:"(\<rho>a,\<sigma>,Q1) \<in> A" and
   a1:"(\<rho>b,\<sigma>,Q2) \<in> B" 
 shows  "\<rho>a*\<rho>b \<in> comb_set (*) (prob\<^sub>s  (eq_stack_S A (eq_stack A B))) (prob\<^sub>s (eq_stack_S B (eq_stack A B)))"
proof-
  have "(\<rho>a,\<sigma>,Q1) \<in> eq_stack_S A (eq_stack A B)"
    unfolding eq_stack_S_def eq_stack_def stack\<^sub>s_def 
    using a0 a1  image_iff by fastforce 
  then have  "\<rho>a \<in> prob\<^sub>s  (eq_stack_S A (eq_stack A B))" 
    using a0  unfolding prob\<^sub>s_def by (force simp add: image_iff)
  moreover have "(\<rho>b,\<sigma>,Q2) \<in> eq_stack_S B (eq_stack A B)"
    unfolding eq_stack_S_def eq_stack_def stack\<^sub>s_def 
    using a0 a1  image_iff by fastforce
  then have  "\<rho>b \<in> prob\<^sub>s  (eq_stack_S B (eq_stack A B))" 
    using a1 unfolding prob\<^sub>s_def by (force simp add: image_iff)
  ultimately show ?thesis unfolding comb_set_def
    by blast
qed     

lemma quantu_set_QState\<^sub>s_intro:
  assumes 
   a0:"(\<rho>a,\<sigma>,Q1) \<in> A" and
   a1:"(\<rho>b,\<sigma>,Q2) \<in> B" and
   a2:"Q1 ## Q2" 
 shows  "((\<lambda>s. s \<in> (QState\<^sub>s (eq_stack_S A (eq_stack A B)))) \<and>* 
          (\<lambda>s. s \<in> (QState\<^sub>s (eq_stack_S B (eq_stack A B))))) (Q1 + Q2)"
proof-
  have "(\<rho>a,\<sigma>,Q1) \<in> eq_stack_S A (eq_stack A B)"
    unfolding eq_stack_S_def eq_stack_def stack\<^sub>s_def 
    using a0 a1  image_iff by fastforce 
  then have  "Q1 \<in> QState\<^sub>s  (eq_stack_S A (eq_stack A B))" 
    using a0  unfolding QState\<^sub>s_def by (force simp add: image_iff)
  moreover have "(\<rho>b,\<sigma>,Q2) \<in> eq_stack_S B (eq_stack A B)"
    unfolding eq_stack_S_def eq_stack_def stack\<^sub>s_def 
    using a0 a1  image_iff by fastforce
  then have  "Q2 \<in> QState\<^sub>s  (eq_stack_S B (eq_stack A B))" 
    using a1 unfolding QState\<^sub>s_def by (force simp add: image_iff)
  ultimately show ?thesis using a2 unfolding QState\<^sub>s_def unfolding sep_conj_def
    by auto
qed

definition Q_sep_dis_set1::"(('s state) set) \<Rightarrow> (('s state) set) \<Rightarrow>  (('s state) set)" 
(infixr "\<and>\<^sup>*1" 35)
where "Q_sep_dis_set1 A B \<equiv>           
         {(\<rho>,\<sigma>,Q). \<exists>\<rho>1 \<rho>2 Q1 Q2. (\<rho>1,\<sigma>,Q1) \<in> A \<and> (\<rho>2,\<sigma>,Q2) \<in> B \<and> 
                   \<rho> = \<rho>1 * \<rho>2 \<and> Q1 ## Q2 \<and> Q = Q1 + Q2}" 

definition Q_eq_stack_disj_heap::"(('s state) set) \<Rightarrow> (('s state) set) \<Rightarrow> ((('s state)\<times>('s state)) set)"
  where "Q_eq_stack_disj_heap A B = 
    {(a,b). a \<in> A \<and> b \<in> B \<and> get_stack a = get_stack b \<and>
            (get_QStateM a)##(get_QStateM b)}"

definition Q_sep_dis_set::"(('s state) set) \<Rightarrow> (('s state) set) \<Rightarrow>  (('s state) set)" 
(infixr "\<and>\<^sup>*" 35)
where "Q_sep_dis_set A B \<equiv>  
        (\<lambda>(a,b). (get_prob a * get_prob b, (get_stack a, get_QStateM a + get_QStateM b))) ` 
       Q_eq_stack_disj_heap A B" 

lemma eq_qsep1:"x \<in> (xa \<and>\<^sup>*1 xb) \<Longrightarrow> x \<in> (xa \<and>\<^sup>* xb)"
  unfolding Q_sep_dis_set_def Q_sep_dis_set1_def Let_def get_stack_def get_prob_def get_QStateM_def
            image_def Q_eq_stack_disj_heap_def
  apply (auto simp add: case_prod_beta)   
    by (metis prod.collapse)
  

lemma eq_qsep2:"xb \<in> (x \<and>\<^sup>* xa) \<Longrightarrow> xb \<in> (x \<and>\<^sup>*1 xa)"
  unfolding Q_sep_dis_set_def Q_sep_dis_set1_def Let_def get_stack_def get_prob_def get_QStateM_def
            image_def Q_eq_stack_disj_heap_def  
  by auto
  

lemma eq_Qsep_dis_sets:"Q_sep_dis_set1 =  Q_sep_dis_set"
  apply rule   
  apply rule 
  apply rule 
   apply rule 
   apply (rule eq_qsep1, simp)
  apply (rule)
  by (rule eq_qsep2, simp)

  
lemma Q_sep_dis_set_empty1:
  assumes  a0:"Q_eq_stack_disj_heap A B = {}"
         shows "Q_sep_dis_set A B = {}"
  using a0 
  unfolding Q_sep_dis_set_def 
  by auto


lemma Q_sep_dis_set_empty2:
  assumes  a0:"Q_sep_dis_set A B = {}" 
  shows "Q_eq_stack_disj_heap A B = {}"
  using a0 
  unfolding Q_sep_dis_set_def 
  by auto

lemma h0: assumes a0:"fst ` snd ` A \<inter> fst ` snd ` B \<noteq> {}"
  shows "\<exists>a aa.
       \<exists>ab\<in>B.
          fst (snd ab) \<in> fst ` snd ` A \<and>
          (\<exists>b. (aa, fst (snd ab), b) \<in> A) \<and>
          a \<in> (*) aa ` fst ` {s \<in> B. fst (snd s) \<in> fst ` snd ` A \<and> fst (snd s) \<in> fst ` snd ` B}"
proof-
  obtain aa ab x ba bb where 
      a1:"x\<in>fst ` snd ` A" and a2:"x\<in>fst ` snd ` B" and a3:"(aa,x,ab)\<in>A" and a4:"(ba,x,bb)\<in>B" 
    using a0 apply auto
    by (metis (no_types) fst_conv image_iff snd_conv)   
  then show ?thesis
    apply auto using a1 a2 a3 a4
    by (smt all_not_in_conv fst_conv image_is_empty mem_Collect_eq snd_conv)
qed      

lemma h1: assumes a0:"eq_stack A B \<noteq> {}"
  shows "\<exists>a aa.
       \<exists>ab\<in>A.
          fst (snd ab) \<in> fst ` snd ` B \<and>
          (\<exists>b. (aa, fst (snd ab), b) \<in> A) \<and>
          a \<in> (*) aa ` fst ` {s \<in> B. fst (snd s) \<in> fst ` snd ` A \<and> fst (snd s) \<in> fst ` snd ` B}"
proof-
  obtain aa ab x ba bb where 
      a1:"x\<in>fst ` snd ` A" and a2:"x\<in>fst ` snd ` B" and a3:"(aa,x,ab)\<in>A" and a4:"(ba,x,bb)\<in>B" 
    using a0 unfolding eq_stack_def stack\<^sub>s_def apply auto
    by (metis (no_types) fst_conv image_iff snd_conv)   
  then show ?thesis
    apply auto using a1 a2 a3 a4
    by (smt all_not_in_conv fst_conv image_is_empty mem_Collect_eq snd_conv)
qed      


lemma Q_sep_dis_set_dest:
  assumes a0:"(\<rho>, \<sigma>, Q) \<in> (A \<and>\<^sup>* B)"
  shows "\<exists>\<rho>1 \<rho>2 Q1 Q2. \<rho> = \<rho>1 * \<rho>2 \<and> 
           (\<rho>1, \<sigma>, Q1) \<in> A \<and> (\<rho>2, \<sigma>, Q2) \<in> B \<and> 
            Q =  Q1 + Q2 \<and> Q1 ## Q2"
  using a0  
  apply (auto simp add: eq_Qsep_dis_sets[THEN sym])
  unfolding Q_sep_dis_set1_def
  by auto     

lemma Q_sep_dis_set_elim:
  "(\<rho>, \<sigma>, Q) \<in> (A \<and>\<^sup>* B) \<Longrightarrow>
    \<lbrakk>\<And>\<rho>1 \<rho>2 Q1 Q2. \<rho> = \<rho>1 * \<rho>2 \<and> 
           (\<rho>1, \<sigma>, Q1) \<in> A \<and> (\<rho>2, \<sigma>, Q2) \<in> B \<and> 
            Q =  Q1 + Q2 \<and> Q1 ## Q2 \<Longrightarrow> P\<rbrakk> \<Longrightarrow>
    P" 
  by (auto dest:  Q_sep_dis_set_dest)

lemma Q_sep_dis_set_intro:
 assumes 
   a0:"(\<rho>a,\<sigma>,Q1) \<in> A" and
   a1:"(\<rho>b,\<sigma>,Q2) \<in> B" and
   a2:"Q1 ## Q2" 
 shows "(\<rho>a*\<rho>b, \<sigma>, Q1 + Q2) \<in> Q_sep_dis_set A B"   
  using a1 a2 a0
  unfolding Q_sep_dis_set_def get_prob_def get_stack_def get_QStateM_def Let_def
            eq_stack_def comb_set_def stack\<^sub>s_def prob\<^sub>s_def eq_stack_S_def QState\<^sub>s_def
  image_def Q_eq_stack_disj_heap_def
  apply (auto simp add: case_prod_beta)
  by blast


\<comment>\<open>map_assn' receives two sets of qbits q1 q2 addresses and a vector v. It represents that the current
  qstate is equal to v and that v can be split into two different separated qstates each
 of them is composed by the qubits contained by the sets q1 and q2\<close>
  
  
     
  
(*definition map_assn'::"'s expr_q \<Rightarrow> 's expr_q \<Rightarrow> ('s state, (complex) QState) expr \<Rightarrow> (('s state) set)"  
 ("_\<cdot>_ \<mapsto> _"  [1000, 20, 1000] 60)
  where "map_assn' q1 q2 v \<equiv> let qs = (\<lambda>s. snd (get_qstate s));
                                  st = (\<lambda>s. get_stack s) in   
                 {s. fst s = 1 \<and>(q1 (st s) \<union> q2 (st s)) \<noteq> {} \<and> (qs s) = (v s) \<and>
                      (\<exists>\<qq>' \<qq>''. (get_QStateM s) = \<qq>' +  \<qq>'' \<and> \<qq>' ## \<qq>'' \<and> 
                                (q1 (st s)) = QStateM_vars \<qq>' \<and>
                                (q1 (st s)) = QStateM_vars \<qq>')}" *)



(*definition map_assna::"('s,nat set) expr \<Rightarrow> ('s, (complex) QState) expr \<Rightarrow> (('s state) set)"  
 ("_ \<mapsto> _"   [20, 1000] 60)
  where "map_assna q v \<equiv> let qv = (\<lambda>s. fst (get_qstate s)); 
                            qs = (\<lambda>s. snd (get_qstate s));
                            st = (\<lambda>s. get_stack s) in   
                 {s. fst s = 1 \<and>(q1 (st s, qv s) \<union> q2 (st s, qv s)) \<noteq> {} \<and> 
                      (\<exists>\<qq>' \<qq>''. (qs s) = (v s) \<and> (v s) = \<qq>' +  \<qq>'' \<and> \<qq>' ## \<qq>'' \<and> 
                                (q1 (st s, qv s)) = QState_vars \<qq>' \<and>
                                (q1 (st s, qv s)) = QState_vars \<qq>')}" *)
\<comment>\<open>map_assn receives one set of qbits addresses and a vector. 
  It represents that the current qstate is v and that it can be split into two different separated qstates
  and the set of qubits of one of them is the set of qubits in q1\<close>

(* definition map_assn::"'s expr_q \<Rightarrow> ('s state, (complex) QState) expr \<Rightarrow> (('s state) set)"  (infixr "\<mapsto>\<^sub>q" 35)
  where "map_assn f v \<equiv> let qv = (\<lambda>s. fst (get_qstate s)); 
                            qs = (\<lambda>s. snd (get_qstate s));
                            st = (\<lambda>s. get_stack s) in   
                 {s. \<Union>((qv s) ` (f (st s))) \<noteq> {} \<and> (qs s) = (v s) \<and>
                  (\<exists>\<qq>' \<qq>''.  get_QStateM s = \<qq>' +  \<qq>'' \<and> \<qq>' ## \<qq>'' \<and> (\<Union>((qv s) ` (f (st s)))) = QStateM_vars \<qq>')}" *)

(* definition map_assn::"'s expr_q \<Rightarrow> ('s state, (complex) QState) expr \<Rightarrow> (('s state) set)"  (infixr "\<mapsto>\<^sub>q" 35)
  where "map_assn f v \<equiv> let qv = (\<lambda>s. fst (get_qstate s)); 
                            qs = (\<lambda>s. snd (get_qstate s));
                            st = (\<lambda>s. get_stack s) in   
                 {s. (f (st s, qv s)) \<noteq> {} \<and> (\<exists>\<qq>' \<qq>''. (qs s) = (v s) \<and> (v s) = \<qq>' +  \<qq>'' \<and> \<qq>' ## \<qq>'' \<and> (f (st s, qv s)) = QState_vars \<qq>')}"*)

\<comment>\<open>map_assnl receives one variable of qbits addresses and a vector. 
  It represents that the current qstate is v and that it can be split into two different separated qstates
  and the set of qubits of one of them is the set of qubits in q1\<close>

(* definition map_assnl::"('s,nat set) expr \<Rightarrow> ('s, (complex) QState) expr \<Rightarrow> (('s state) set)"  (infixr "\<mapsto>\<^sub>l" 35)
  where "map_assnl f v \<equiv> let qv = (\<lambda>s. fst (get_qstate s)); 
                            qs = (\<lambda>s. snd (get_qstate s));
                            st = (\<lambda>s. get_stack s) in   
                 {s. Q_domain_set f (qv s) (st s) \<noteq> {} \<and> Q_domain_set f (qv s) (st s) = QState_vars (v (st s)) \<and>
                     (\<exists>\<qq>' \<qq>''. (qs s) =  \<qq>' + \<qq>'' \<and> (v (st s)) = \<qq>''  \<and> \<qq>' ## \<qq>'' )}" *)

context vars 
begin

definition map_assnl::"('s,nat set) expr \<Rightarrow> ('s, (complex) list) expr \<Rightarrow> (('s state) set)"
(infixr "\<mapsto>\<^sub>l" 40)
  where "map_assnl f v \<equiv> let qv = (\<lambda>s. fst (get_qstate s)); 
                            qs = (\<lambda>s. snd (get_qstate s));
                            st = (\<lambda>s. get_stack s) in   
                 {s. (\<exists>\<qq>' \<qq>''. (qs s) =  \<qq>' + \<qq>'' \<and> \<qq>' ## \<qq>'' \<and>  
                                QState_vars \<qq>'' = Q_domain_set f (qv s) (st s) \<and>
                               QState_list \<qq>'' = (v (st s)))}"

definition map_assn::"('s,nat set) expr \<Rightarrow> ('s, (complex) list) expr \<Rightarrow> (('s state) set)"
(infixr "\<mapsto>" 40)
  where "map_assn f v \<equiv> let qv = (\<lambda>s. fst (get_qstate s)); 
                            qs = (\<lambda>s. snd (get_qstate s));
                            st = (\<lambda>s. get_stack s) in   
                 {s. QState_vars (qs s)  = Q_domain_set f (qv s) (st s) \<and>
                     QState_list (qs s) = (v (st s))}"

lemma map_assn_intro:
  assumes a0:"qs =  Q_domain_var (f \<sigma>) m" and
          a1:"v = l \<sigma>" and
          a2:"QStateM_wf (m, QState (qs, v))" and a3:"QState_wf (qs, v)"
        shows "(p,\<sigma>,QStateM (m, QState(qs, v))) \<in> (f \<mapsto> l)"
proof-
  let ?Q = "QState(qs, v)"
  let ?Qm = "QStateM (m, ?Q)"
  have f1:"QState_vars ?Q = qs" using a3
    using QState_var_idem by blast
  have f2:"QState_list ?Q = v" using a3
    using QState_list_idem by blast
  have f3:"QStateM_map ?Qm = m"
    using QStateM_wf_map local.a2 by auto
  have f4:"qstate ?Qm = ?Q"
    using QStateM_wf_qstate local.a2 by presburger  
  show ?thesis 
    unfolding map_assn_def Let_def get_qstate_def get_stack_def
    apply (auto simp add: f1 f2 f3 f4) 
    using a0 a1     
    unfolding Q_domain_set_def Q_domain_var_def by auto
qed
  



definition val_var::"'v \<Rightarrow> 'm \<Rightarrow> (('s state) set)" ("_\<down>\<^sub>_")
  where "val_var v vl \<equiv> {s. get_value (get_stack s) v = vl}"


definition map_assnv1::"'v  \<Rightarrow> ('s, (complex) list) expr \<Rightarrow> (('s state) set)"
(infixr "\<mapsto>\<^sub>v" 40)
  where "map_assnv1 v q \<equiv> let qv = (\<lambda>s. fst (get_qstate s)); 
                            qs = (\<lambda>s. snd (get_qstate s));
                            st = (\<lambda>s. get_stack s);
                            set_v = (\<lambda>st. {to_nat (get_value st v )}) in   
                 {s. QState_vars (qs s)  = Q_domain_var (set_v (st s)) (qv s) \<and>
                     QState_list (qs s) = (q (st s))}" 


definition map_assnv::"'v  \<Rightarrow> ('s, nat set) expr \<Rightarrow> ('s, (complex) list) expr \<Rightarrow> (('s state) set)"
("_\<cdot>_ \<mapsto>\<^sub>v _" [1000, 20, 1000] 60)
  where "map_assnv v i q \<equiv> let qv = (\<lambda>s. fst (get_qstate s)); 
                            qs = (\<lambda>s. snd (get_qstate s));
                            st = (\<lambda>s. get_stack s);
                            set_v = (\<lambda>st. var_set v i st) in   
                 {s. fst s  =  1 \<and> QState_vars (qs s)  = Q_domain_var (the (set_v (st s))) (qv s) \<and>
                     QState_vars (qs s) \<noteq> {} \<and> (\<forall>e \<in> the ((set_v (st s))). (qv s) e \<noteq> {}) \<and>
                     QState_list (qs s) = (q (st s))}"

definition map_assnzero::"'v  \<Rightarrow> ('s, nat set) expr \<Rightarrow>  (('s state) set)"
("_\<cdot>_ \<mapsto>\<^sub>v |0>" [1000, 20] 60)
  where "map_assnzero v i  \<equiv> let qv = (\<lambda>s. fst (get_qstate s)); 
                            qs = (\<lambda>s. snd (get_qstate s));
                            st = (\<lambda>s. get_stack s);
                            set_v = (\<lambda>st. var_set v i st) in   
                 {s. fst s  =  1 \<and> QState_vars (qs s)  = Q_domain_var (the (set_v (st s))) (qv s) \<and>
                     QState_vars (qs s) \<noteq> {} \<and> (\<forall>e \<in> the ((set_v (st s))). (qv s) e \<noteq> {}) \<and>
                     QState_vector (qs s) = |0>\<^sub>(card (QState_vars (qs s)))}"

definition map_assn'::"'s expr_q \<Rightarrow> 's expr_q \<Rightarrow> ('s, (complex) list) expr \<Rightarrow> ('s state) set"  
 ("_\<cdot>_ \<mapsto> _"  [1000, 20, 1000] 60)
 where "map_assn' q1 q2 v \<equiv> let qv = (\<lambda>s. fst (get_qstate s));
                                qs = (\<lambda>s. snd (get_qstate s));
                                  st = (\<lambda>s. get_stack s) in   
                 {s. QState_list (qs s) = (v (st s)) \<and>
                     (\<forall>e \<in> q1 (st s). (qv s) e \<noteq> {}) \<and> q1 (st s) \<noteq> {} \<and>
                     q1 (st s) \<inter> q2 (st s) = {} \<and>
                     QState_vars (qs s)  = Q_domain_var (q1 (st s) \<union> q2 (st s)) (qv s) }"

lemma map_assn'_dest:
  "(\<rho>,\<sigma>,Q) \<in> q\<cdot>qr \<mapsto> vl \<Longrightarrow> 
      QStateM_vars Q = Q_domain_var (q \<sigma> \<union> qr \<sigma>) (QStateM_map Q) \<and> 
      QStateM_list Q = vl \<sigma> \<and> QStateM_vars Q \<noteq> {} \<and> q \<sigma> \<inter> qr \<sigma> = {} \<and> q \<sigma> \<noteq> {} \<and>
      (\<forall>e \<in> q \<sigma>. (QStateM_map Q) e \<noteq> {})"
  unfolding map_assn'_def Let_def get_qstate_def get_stack_def qstate_def Q_domain_var_def
  by (auto simp add: QStateM_vars.rep_eq  QStateM_list.rep_eq)

lemma map_assn'_dest1:
  "(\<rho>,\<sigma>,Q) \<in> q\<cdot>qr \<mapsto> vl \<Longrightarrow> 
      QStateM_vars Q = Q_domain_var (q \<sigma> \<union> qr \<sigma>) (QStateM_map Q) \<and> 
      QStateM_list Q = vl \<sigma> \<and> QStateM_vars Q \<noteq> {} \<and> q \<sigma> \<inter> qr \<sigma> = {} \<and> q \<sigma> \<noteq> {} \<and>
      (\<forall>e \<in> q \<sigma>. (QStateM_map Q) e \<noteq> {})"
  unfolding map_assn'_def Let_def get_qstate_def get_stack_def qstate_def Q_domain_var_def
  by (auto simp add: QStateM_vars.rep_eq  QStateM_list.rep_eq)
  

definition map_assn1'::"'s expr_q \<Rightarrow> 's expr_q \<Rightarrow> ('s, QState) expr \<Rightarrow> (('s state) set)"  
 ("_\<cdot>_ \<mapsto>a _"  [1000, 20, 1000] 60)
  where "map_assn1' q1 q2 v \<equiv> let qs = (\<lambda>s. snd (get_qstate s));
                                  st = (\<lambda>s. get_stack s) in   
                 {s. fst s = 1 \<and>(q1 (st s) \<union> q2 (st s)) \<noteq> {} \<and> (qs s) = (v (st s)) \<and>
                      (\<exists>\<qq>' \<qq>''. (get_QStateM s) = \<qq>' +  \<qq>'' \<and> \<qq>' ## \<qq>'' \<and> 
                                (q1 (st s)) = QStateM_vars \<qq>' \<and>
                                (q1 (st s)) = QStateM_vars \<qq>')}"


lemma map_assn_zero_dest:
  "(\<rho>,\<sigma>,Q) \<in> q\<cdot>f \<mapsto>\<^sub>v |0> \<Longrightarrow> 
      QStateM_vars Q = Q_domain_var (the (var_set q f \<sigma>)) (QStateM_map Q) \<and> 
      (QStateM_vector Q =  |0>\<^sub>(card (QStateM_vars Q))) \<and> QStateM_vars Q \<noteq> {} \<and> 
      (\<forall>e \<in> (the (var_set q f \<sigma>)). (QStateM_map Q) e \<noteq> {}) \<and> \<rho> = 1"
  unfolding map_assnzero_def Let_def get_qstate_def get_stack_def qstate_def
  by (auto simp add: QStateM_vars.rep_eq  QStateM_vector.rep_eq)

lemma map_assnv_dest:
  "(\<rho>,\<sigma>,Q) \<in> q\<cdot>f \<mapsto>\<^sub>v v \<Longrightarrow> 
      QStateM_vars Q = Q_domain_var (the (var_set q f \<sigma>)) (QStateM_map Q) \<and> 
      QStateM_list Q = v \<sigma> \<and> QStateM_vars Q \<noteq> {} \<and> 
      (\<forall>e \<in> (the (var_set q f \<sigma>)). (QStateM_map Q) e \<noteq> {}) \<and> \<rho> = 1"
  unfolding map_assnv_def Let_def get_qstate_def get_stack_def qstate_def 
  by (auto simp add: QStateM_vars.rep_eq  QStateM_list.rep_eq)


definition prob_assert::" (('s state) set) \<Rightarrow>  real \<Rightarrow> (('s state) set)"
(infixr "\<smile>" 60)
where "prob_assert q p \<equiv> if p \<noteq> 0 then (\<lambda>s. (fst s * p, snd s)) ` q 
                          else (\<lambda>s. (fst s * p, snd s)) ` UNIV"

definition int_stack_ass::"('s,'a set) expr \<Rightarrow> ('s, 'a set) expr \<Rightarrow> (('s state) set)"
(infixr "\<inter>\<^sub>{\<^sub>}" 35)
  where "int_stack_ass q1 q2 \<equiv> let st = (\<lambda>s. get_stack s) in   
                 {s. q1 (st s) \<inter> q2 (st s) = {}}"

definition empty_qstatem_norm_expr::"('s, complex) expr \<Rightarrow> ('s ,  QStateM) expr"
("|>\<^sub>_" 50)
where "empty_qstatem_norm_expr n \<equiv> (\<lambda>s. (n s) \<cdot>\<^sub>Q 0)"


definition empty_qstatem_ass::" (('s state) set)"
("/|>a")
where "empty_qstatem_ass \<equiv> {s. fst s = 1 \<and> get_QStateM s = 0}"

definition Q_sep_dis_q::"(('s state) set) \<Rightarrow> (('s state) set) \<Rightarrow>  (('s state) set)" 
(infixr "\<and>\<^sub>q" 35)
where "Q_sep_dis_q q1 q2 \<equiv> {s. ((\<lambda>s. s \<in> (snd ` (snd ` q1))) \<and>* 
                                (\<lambda>s. s \<in> (snd ` (snd ` q2)))) (snd (snd s))}"

definition QState_expr::"('s , nat set) expr \<Rightarrow> ('s, complex list) expr \<Rightarrow> ('s, QState) expr"
  where "QState_expr v l \<equiv>  (\<lambda>s. QState (v s, l s))"

definition QState_plus_expr::"('s, QState) expr \<Rightarrow> ('s, QState) expr \<Rightarrow> ('s, QState) expr"
(infixr "+\<^sub>e" 50)
  where "QState_plus_expr q1 q2 \<equiv> (\<lambda>s. (q1 s) + (q2 s))"

definition QStateM_expr::"('s, QState) expr \<Rightarrow> ('s state,  QStateM) expr"
where "QStateM_expr q1 \<equiv> let qv = (\<lambda>s. fst (get_qstate s)); 
                            qs = (\<lambda>s. snd (get_qstate s));
                            st = (\<lambda>s. get_stack s);
                            f = (\<lambda>S qv s. if s \<in> S then qv s else {}) in
                          (\<lambda>s. QStateM(f (QState_vars (qs s)) (qv s), q1 (st s)))"

\<comment>\<open>aij returns the element equivalent to the position where 
       the element i*j of a tensor product would be the elements s q
    the state s is used to obtain the set of variables (q s)\<close>
definition aij ::"'s state \<Rightarrow> 's expr_q  \<Rightarrow> ('s, complex list) expr \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>complex" 
  where "aij s q v i j \<equiv> let st = get_stack s ; qv = fst (get_qstate s); 
                             vars = Q_domain qv; d1 = Q_domain_var (q st) qv; d2 = vars - d1 ;
                             vec = v st in 
                             partial_state2.aijv d1 d2 (vec_of_list vec) i j"


definition v_f::"'s expr_q \<Rightarrow> q_vars \<Rightarrow> ( nat \<Rightarrow>'s  \<Rightarrow>  complex) \<Rightarrow> ('s,  QState) expr"
  where "v_f q qvars f \<equiv> let vars = Q_domain_set q qvars in 
                     (\<lambda>s. QState(vars s, map (\<lambda>e. f e s) [0..<2^card (vars s)]))"


definition var_exp::"'v \<Rightarrow> 's \<Rightarrow> nat set"
("\<llangle>_\<rrangle>"  [] 1000)
where "var_exp q  \<equiv> \<lambda>\<sigma>. {to_nat (get_value \<sigma> q)}"

definition valid::"[('s state) assn,('v, 's) com,('s state) assn] \<Rightarrow> bool"
    ("\<Turnstile>_ _ _"  [1000, 20, 1000] 60)
    where "\<Turnstile> P c Q \<equiv>  \<forall>\<sigma> \<sigma>'. \<turnstile> \<langle>c,\<sigma>\<rangle> \<Rightarrow> \<sigma>' \<longrightarrow> \<sigma> \<in> Normal ` P \<longrightarrow> 
                              \<sigma>' \<in> Normal ` Q"

definition \<SS>::"('s state) set \<Rightarrow> ('s \<Rightarrow> real \<Rightarrow>  QStateM \<Rightarrow> bool)"
  where "\<SS> s \<equiv> (\<lambda>u p q. (p,u,q) \<in> s)"


lemma \<SS>_equiv:"s \<in> R \<longleftrightarrow> (\<SS> R) (get_stack s)  (get_prob s) (get_QStateM s)" 
  unfolding  \<SS>_def get_stack_def get_prob_def get_QStateM_def by auto

lemma allocate_preserves_R:
  assumes a2':"\<sigma>' = set_value \<sigma> q (from_nat q')" and       
       a6:"not_access_v (\<SS> R) q" and  
       a9:"(p,\<sigma>,\<Q>) \<in> R"
     shows "(p,\<sigma>',\<Q>) \<in> R"   
  using not_access_v_f_q_eq_set[OF  a2' a6] assms 
  unfolding \<SS>_equiv get_stack_def get_prob_def get_QStateM_def
  by auto

definition vector_s::"'s state \<Rightarrow> 's expr_q  \<Rightarrow>  ('s, complex list) expr \<Rightarrow> nat \<Rightarrow> complex Matrix.vec"
  where "vector_s s q v i \<equiv> 
     let st = get_stack s ; qv = fst (get_qstate s); 
        vars = Q_domain qv; d1 = Q_domain_var (q st) qv; d2 = vars - d1;
        elem_ij  = \<lambda>j. (aij s q v i j)  in
         Matrix.vec (2^card d2) elem_ij"

definition \<rho> ::"'s expr_q  \<Rightarrow> ('s, complex list) expr \<Rightarrow> nat \<Rightarrow>  's state \<Rightarrow> real" 
  where "\<rho> q v i s \<equiv>  Re (vec_norm (vector_s  s q v i )^2)"


definition vector_i::"'s state \<Rightarrow> 's expr_q  \<Rightarrow>  ('s, complex list) expr \<Rightarrow> nat \<Rightarrow> ('s, complex list) expr"
 where "vector_i s q v i \<equiv> 
     \<lambda>st. list_of_vec (1/vec_norm (vector_s s q v i) \<cdot>\<^sub>v (vector_s s q v i))"

lemma assest_vectors_aij:
  assumes 
      a0:"QStateM_vars \<Q> = Q_domain_var (q \<sigma> \<union> qr \<sigma>) (QStateM_map \<Q>)" and       
      a1:"ns' = (p * \<delta>k, \<sigma>', \<Q>')" and 
      a2:"q \<sigma>' = q \<sigma>" and a2':"qr \<sigma>' = qr \<sigma> " and a2'':"vl \<sigma>' = vl \<sigma>" and
      a3:"QStateM_map \<Q>' = QStateM_map \<Q>" and      
      a4:"v1 = Q_domain_var (q \<sigma>) (QStateM_map \<Q>)" and  
      a6:"v2 = Q_domain_var (qr \<sigma>) (QStateM_map \<Q>)" and      
      a7:"q \<sigma> \<inter> qr \<sigma> = {}" and a8:"\<delta>k = \<rho> q vl k ns'" and a9:"QStateM_list \<Q> = vl \<sigma> "
    shows "partial_state2.vector_aij (Q_domain_var (q \<sigma>) (QStateM_map \<Q>))
                       (Q_domain_var (qr \<sigma>) (QStateM_map \<Q>)) (QStateM_vector \<Q>) k =
           vector_s ns' q vl k"
proof-  
  interpret ps2:partial_state2 "list_dims (v1 \<union> v2)" v1 "v2"
    apply standard
    apply (auto simp add: list_dims_def finite_Q_domain_var a4 a6)
    using a0 a7 domain_qr by auto
  let ?v = "ps2.vector_aij (QStateM_vector \<Q>) k" 

  have Qstatem_wf_Q:"QStateM_wf (QStateM_unfold \<Q>)"
     using QStateM_wf by blast
  then have QStateM_wf1:"(\<forall>x y. x\<noteq>y \<and> x\<in> domain (QStateM_map \<Q>) \<and> y \<in> domain (QStateM_map \<Q>) \<longrightarrow> 
              QStateM_map \<Q> x \<inter> QStateM_map \<Q> y = {})"
    by auto
  
  have v2:"v2 = QStateM_vars \<Q> - v1"
    using q_vars_q2[of "q \<sigma>" "qr \<sigma>" "QStateM_map \<Q>" "QStateM_vars \<Q>" ] 
          a7  a6 Qstatem_wf_Q a0 a4 eq_QStateM_vars 
    by auto
  have len:"dim_vec ?v = dim_vec (vector_s ns' q vl k) "
    using v2 a3 a4 a6 a1 a2 QStateM_rel1
    unfolding vector_s_def Let_def  get_qstate_def get_stack_def Q_domain_set_def 
    unfolding ps2.vector_aij_def ps2.aijv_def ps2.d2_def aij_def Let_def
    apply auto
    using QStateM_vars.rep_eq ps2.dims2_def qstate_def  by fastforce  
  moreover have  "\<forall>i<dim_vec ?v. ?v$i = vector_s ns' q vl k $i"
  proof-
    { fix i 
      assume a00:"i<dim_vec ?v"
      moreover have "i<dim_vec (vector_s ns' q vl k)" 
        using len calculation by auto
      moreover have 
      "partial_state2.aijv (Q_domain_var (q \<sigma>) (QStateM_map \<Q>)) (Q_domain_var (qr \<sigma>) (QStateM_map \<Q>))
        (QStateM_vector \<Q>) k i =
      partial_state2.aijv (Q_domain_var (q (fst (snd ns'))) (QStateM_map (snd (snd ns'))))
        (Q_domain (QStateM_map (snd (snd ns'))) -
         Q_domain_var (q (fst (snd ns'))) (QStateM_map (snd (snd ns'))))
        (vec_of_list (vl (fst (snd ns')))) k i" 
        using a1 a2 a2' a2'' a3 v2 a4 a6 QStateM_rel1 
              QStateM_vars.rep_eq a9 qstate_def vec_of_list_QStateM_list by auto
      ultimately have "?v$i = vector_s ns' q vl k $ i" using  a8 v2 a4 a6
        unfolding get_qstate_def get_stack_def ps2.vector_aij_def vector_s_def Let_def aij_def 
        by auto 
    } thus ?thesis by auto
  qed
  ultimately show ?thesis using a4 a6 by auto
qed


definition
  unit_vecl :: "'s state \<Rightarrow> 's expr_q  \<Rightarrow> nat \<Rightarrow> ('s, complex list) expr"
  where "unit_vecl s q i \<equiv>
    let st = get_stack s ; qv = fst (get_qstate s); 
        d1 = Q_domain_set q qv st in
      (\<lambda>s. list_of_vec (unit_vec (2^card d1) i))"

definition card_set_q ::"'s expr_q \<Rightarrow> 's state \<Rightarrow> nat set"
  ("{_}\<^sub>_" [] 100)
  where "card_set_q q s \<equiv> 
    let st = get_stack s ; qv = fst (get_qstate s) in 
             {0..2^card(Q_domain_set q qv st)}"

lemma "1/((a::int)/b) = b/a" by auto

inductive "hoarep"::"[('s state) assn,('v,'s) com, ('s state) assn] => bool"
    ("\<turnstile>(_/ (_)/ _)" [1000,20,1000]60)
where
  Skip: "\<turnstile> Q Skip Q"

| SMod: "\<turnstile>{s.  set_stack s (f (get_stack s)) \<in> Q} (SMod f) Q"
         
| (* QMod: " unitary M \<Longrightarrow>
          \<turnstile> {s. q_v = fst (get_qstate s) \<and>  st = get_stack s \<and> \<Q> = get_QStateM s \<and> 
                 \<Inter> (q_v ` qs st) \<noteq> {} \<and> qs st \<noteq> {} \<and> 
                 M \<in> carrier_mat (2 ^ card (\<Union> (QStateM_map \<Q> ` (qs st))))  (2 ^ card (\<Union> (QStateM_map \<Q> ` (qs st)))) \<and>
                set_qstate s (matrix_sep_QStateM (qs st) (get_QStateM s) M) \<in> Q} 
                (QMod M qs) 
             Q" *)
   QMod: " unitary M \<Longrightarrow>
          \<turnstile> {s. q_v = fst (get_qstate s) \<and>  st = get_stack s \<and> \<Q> = get_QStateM s \<and> 
                 (\<forall>e \<in> (qs st). QStateM_map \<Q> e \<noteq> {})  \<and> 
                 M \<in> carrier_mat (2 ^ card (\<Union> (QStateM_map \<Q> ` (qs st))))  (2 ^ card (\<Union> (QStateM_map \<Q> ` (qs st)))) \<and>
                set_qstate s (matrix_sep_QStateM (qs st) (get_QStateM s) M) \<in> Q} 
                (QMod M qs) 
             Q" 

| Seq: "\<lbrakk>\<turnstile> P c\<^sub>1 R; \<turnstile> R c\<^sub>2 Q\<rbrakk>
        \<Longrightarrow>
        \<turnstile> P (Seq c\<^sub>1 c\<^sub>2) Q"

| Cond: "\<lbrakk>\<turnstile>(P \<inter> {s. get_stack s \<in> b}) c\<^sub>1 Q; \<turnstile>(P \<inter> {s. get_stack s \<in> - b}) c\<^sub>2 Q\<rbrakk>
         \<Longrightarrow>
         \<turnstile> P (IF b c\<^sub>1 c\<^sub>2) Q"

| While: "\<turnstile> (P \<inter> {s. get_stack s \<in> b}) c\<^sub>1 P
          \<Longrightarrow>
          \<turnstile> P (While b c\<^sub>1) (P \<inter> {s. get_stack s \<in> - b})"

| QAlloc:"not_access_v v q \<Longrightarrow> not_access_v (\<SS> R) q \<Longrightarrow> q \<in> nat_vars \<Longrightarrow>   
          \<forall>\<sigma>. length (v \<sigma>) > 1 \<and> vec_norm (vec_of_list (v \<sigma>)) = 1 \<Longrightarrow>
          \<turnstile> R q:=alloc v ((q\<cdot>f \<mapsto>\<^sub>v v) \<and>\<^sup>* R)"


\<comment>\<open>In QDispose we set that Qs does not depend on the stack to avoid that 
   the n in the postcondition may also depend on the stack and gives unsound results
  in later modifications to the stack that may not affect the vector\<close>

| QDispose: " \<turnstile> (q\<cdot>i \<mapsto>\<^sub>v |0>) (Dispose q i) ( |>a) "

|(* QMeasure: "st = (\<lambda>s. get_stack s)  \<Longrightarrow> 
             not_access_v q v \<Longrightarrow>  not_access_v vl v \<Longrightarrow>                            
             \<Psi> = (\<lambda>i. {\<sigma>. \<sigma> \<in> ((q \<cdot> (\<lambda>s. {}) \<mapsto> (unit_vecl s q i)) \<and>\<^sup>* 
                          (qr \<cdot> (\<lambda>s. {}) \<mapsto> (vector_i \<sigma> q vl i)))}) \<Longrightarrow>               
               \<turnstile> ((q \<cdot> qr \<mapsto> vl) \<inter> 
                 ({s. \<exists>i\<in> {q}\<^sub>s. \<Phi> (set_stack s (set_value (st s) v (from_nat i)))}))
                    (Measure v q)   
                  ({s. s \<in> (\<Union>i\<in>{q}\<^sub>s. \<Psi> i)} \<inter> {s. \<Phi> s})" *)

QMeasure: " v \<in> nat_vars \<Longrightarrow>
           not_access_v q v \<Longrightarrow>  not_access_v vl v \<Longrightarrow> not_access_v qr v \<Longrightarrow>                                            
           \<turnstile> (q \<cdot> qr \<mapsto> vl)
                (Measure v q)   
              {s. s \<in> (\<Union>i\<in>{q}\<^sub>s. (v\<down>\<^sub>(from_nat i)) \<inter> (((q \<mapsto> (unit_vecl s q i)) \<and>\<^sup>* 
                                  (qr  \<mapsto> (vector_i s q vl i)))\<smile>(\<rho> q vl i s)))}" 
                                             

(*| Frame: "\<turnstile> P c Q \<Longrightarrow> not_access_v_set (\<lambda>s. s\<in>{b. \<exists>a c. (a,b,c)\<in>A}) (modify_locals c) \<Longrightarrow> {v. (\<exists>p q. access_v  (\<lambda>s. (p, (s,q)) \<in> A) v = True)} \<inter> 
                      modify_locals c = {} \<Longrightarrow> \<turnstile> (P \<and>\<^sup>* A) c (Q \<and>\<^sup>* A)" *)

| Frame: "\<turnstile> P c Q \<Longrightarrow> not_access_v_set (\<lambda>s. \<lambda>a c. s\<in>{b. (a,b,c)\<in>A}) (modify_locals c) \<Longrightarrow>
          \<turnstile> (P \<and>\<^sup>* A) c (Q \<and>\<^sup>* A)"

| Conseq: "\<forall>s \<in> P. \<exists>P' Q'. \<turnstile> P' c Q' \<and> s \<in> P' \<and> Q' \<subseteq> Q 
           \<Longrightarrow> \<turnstile> P c Q"

lemma prob_assert_intro:"x\<noteq>0 \<Longrightarrow> (a,b,c) \<in> P \<Longrightarrow>(a*x,b,c) \<in> P \<smile> x"
  unfolding prob_assert_def 
  by force

lemma prob_assert_dest1:"s \<in> P \<smile> x \<Longrightarrow> x\<noteq>0 \<Longrightarrow> (\<exists>p. get_prob s = x*p \<and> (p,snd s) \<in> P)"
  unfolding prob_assert_def get_prob_def by auto

lemma prob_assert_dest2:"s \<in> P \<smile> x \<Longrightarrow> x=0 \<Longrightarrow> get_prob s = 0 \<and> snd s\<in>UNIV"
  unfolding prob_assert_def get_prob_def by auto

lemma map_assnv_prob:
   "QState_wf (q'_addr, v \<sigma>) \<Longrightarrow> QStateM_wf ((\<lambda>i. {})(q' := q'_addr), QState (q'_addr, v \<sigma>)) \<Longrightarrow> 
       QStateM_map (QStateM ((\<lambda>i. {})(q' := q'_addr), QState (q'_addr, v \<sigma>))) = (\<lambda>i. {})(q' := q'_addr) \<Longrightarrow>
        q \<in> nat_vars  \<Longrightarrow>  q \<in> variables \<Longrightarrow> length (v \<sigma>) > 1 \<Longrightarrow>       
     v \<sigma> = v (set_value \<sigma> q (from_nat q')) \<Longrightarrow> 
      (1, set_value \<sigma> q (from_nat q'),
         QStateM ((\<lambda>i. {})(q' := q'_addr), QState (q'_addr, v \<sigma>)))
           \<in> (q\<cdot>f \<mapsto>\<^sub>v v)"
  unfolding prob_assert_def map_assnv_def Let_def get_qstate_def get_stack_def 
            Q_domain_var_def set_value_def var_set_def 
  by (auto simp add: QState_var_idem  QState_wf_def QStateM_wf_qstate QState_list_idem less_not_refl2 get_set rep_nat set_value_def)             
            

lemma alloc_sound:
  assumes a1:"not_access_v v q" and 
          a2':"not_access_v (\<SS> R) q" and 
          a4:"q \<in> nat_vars"  and 
          a5:"\<forall>\<sigma>. length (v \<sigma>) > 1 \<and> vec_norm (vec_of_list (v \<sigma>)) = 1"
  shows "\<Turnstile> R q:=alloc v (( (q\<cdot>f \<mapsto>\<^sub>v v))  \<and>\<^sup>* R)"  
proof-
  { fix s s'
    let ?st = "(\<lambda>s. get_stack s) "
     assume a00:"\<turnstile> \<langle>q:=alloc v,s\<rangle> \<Rightarrow> s'" and
            a01:"s \<in> Normal ` R"             
     then obtain sn where a01:"s = Normal sn" and         
         a01a:"sn \<in> R"  
       by auto           
     from QExec_Normal_elim_cases(9)[OF a00[simplified a01]] a5
      obtain q' \<Q> q'_addr \<sigma> \<delta>  where 
      sn: "sn = (\<delta>, \<sigma>, \<Q>)" and 
      s':"s' = Normal (\<delta>, set_value \<sigma> q (from_nat q'),
                         \<Q> + QStateM ((\<lambda>i. {})(q' := q'_addr), QState (q'_addr, v \<sigma>)))" and
      q':"q' \<notin> dom_q_vars (QStateM_map \<Q>)"  and lv:"length (v \<sigma>) > 1" and vnz:"vec_norm (vec_of_list (v \<sigma>)) = 1" and
      q'_addr_in_new: "q'_addr \<in> new_q_addr v \<sigma> (QStateM_map \<Q>)"       
        by (metis One_nat_def le_Suc_eq le_zero_eq less_numeral_extra(4) not_less_zero)    
    then obtain sn' where 
       sn':"s' = Normal sn' \<and> 
        sn' = (\<delta>, set_value \<sigma> q (from_nat q'), \<Q> + QStateM ((\<lambda>i. {})(q' := q'_addr), QState (q'_addr, v \<sigma>)))" 
       by auto              
     let ?\<Q> = "\<Q> + QStateM ((\<lambda>i. {})(q' := q'_addr), QState (q'_addr, v \<sigma>))" 
     have \<sigma>:"\<sigma> = ?st sn" and Q:"QStateM_unfold \<Q> = get_qstate sn" and 
          Q':"QStateM_unfold ?\<Q> = get_qstate sn'"
       using sn  sn' unfolding get_qstate_def get_stack_def   by auto
     let ?\<sigma>' = "set_value \<sigma> q (from_nat q')" 
     let ?\<Q>' = "QStateM ((\<lambda>i. {})(q' := q'_addr), QState (q'_addr, v \<sigma>))"   
     
     have st':"?st sn' = ?\<sigma>'" using sn' unfolding get_stack_def   
       by auto     
     have v_eq:"v \<sigma> = v ?\<sigma>'" 
       by (metis local.a1 not_access_v_f_q_eq_set st')    
     have sn_mod_\<sigma>'_in_R:"(\<delta>, ?\<sigma>', \<Q>) \<in> R" using a01a st' unfolding get_stack_def
       using a2' allocate_preserves_R sn by blast
     have new_state_in_assr:"(1, ?\<sigma>', ?\<Q>') \<in> (q\<cdot>f \<mapsto>\<^sub>v v)"
         
       using map_assnv_prob[OF _ _ _ , of q'_addr v \<sigma> q' q]    v_eq a4 lv
       allocate_wf1[of ?\<Q>' _ _ v \<sigma>, OF _ lv vnz _ q'_addr_in_new, of "{}\<^sub>q(q' := q'_addr)" q' , simplified]             
       unfolding  QState_wf_def  by force
       
     have "sn' \<in> ((q\<cdot>f \<mapsto>\<^sub>v v)  \<and>\<^sup>* R)"       
     proof-    
       let ?A = "(q\<cdot>f \<mapsto>\<^sub>v v)" and ?B = R
       let ?A' = "eq_stack_S ?A (eq_stack ?A ?B)"
       let ?B' = "eq_stack_S ?B (eq_stack ?A ?B)"       
       have "get_prob sn' \<in> (comb_set (*) (prob\<^sub>s  ?A') (prob\<^sub>s  ?B'))"
         using  comb_set_prob\<^sub>s_intro[OF new_state_in_assr sn_mod_\<sigma>'_in_R] sn'              
         unfolding get_prob_def by auto
       moreover have "get_stack sn' \<in> eq_stack ?A ?B"
         using stack_set_intro[OF new_state_in_assr sn_mod_\<sigma>'_in_R]
         by (simp add: st')
       moreover have h:"QStateM ((\<lambda>i. {})(q' := q'_addr), QState (q'_addr, v \<sigma>)) ## \<Q>"
         using disjoint_allocate[of ?\<Q>' "{}\<^sub>q(q' := q'_addr)" q'_addr v \<sigma>, OF _ lv q' vnz,simplified, OF q'_addr_in_new]          
         using sep_disj_commuteI by blast 
       then have "((\<lambda>s. s \<in> (QState\<^sub>s ?A')) \<and>* (\<lambda>s. s \<in> (QState\<^sub>s  ?B'))) (get_QStateM sn')"
         using quantu_set_QState\<^sub>s_intro[OF new_state_in_assr sn_mod_\<sigma>'_in_R] sn' 
         unfolding get_QStateM_def
         by (simp add: sep_add_commute)
       show ?thesis 
         using Q_sep_dis_set_intro[OF new_state_in_assr sn_mod_\<sigma>'_in_R h]         
         unfolding get_prob_def comb_set_def get_stack_def
         by (simp add: local.h sep_add_commute sn')
     qed
    then have "s' \<in> Normal ` ((q\<cdot>f \<mapsto>\<^sub>v v) \<and>\<^sup>* R)" using sn' by auto  
   } thus ?thesis unfolding valid_def by auto
 qed

lemma  Q_domain_Q:
  assumes
       a0':"\<Q> = \<Q>' + \<Q>''" and a0'':"\<Q>' ## \<Q>''" and
       a0:"QStateM_vars \<Q> = Q_domain_var vs (QStateM_map \<Q>)" and
       a2:"QStateM_vars \<Q>' = Q_domain_var vs (QStateM_map \<Q>')" and
       a3:"\<forall>e\<in>vs. QStateM_map \<Q>' e \<noteq> {}"
     shows "Q_domain (QStateM_map \<Q>') =  Q_domain (QStateM_map \<Q>)"
proof-  
  have "QStateM_vars \<Q> = Q_domain (QStateM_map \<Q>)"
    by (simp add: QStateM_rel1 QStateM_vars.rep_eq qstate_def)
  moreover have "QStateM_vars \<Q>' = Q_domain (QStateM_map \<Q>')"
    by (simp add: QStateM_rel1 QStateM_vars.rep_eq qstate_def)
  moreover have "QStateM_map \<Q> = QStateM_map \<Q>' + QStateM_map \<Q>''"
    unfolding plus_QStateM
    by (metis QStateM_wf_map a0' a0'' plus_QStateM plus_wf sep_disj_QStateM)
  moreover have "QStateM_map \<Q>' ## QStateM_map \<Q>''"
    using a0'' sep_disj_QStateM by blast
  ultimately show ?thesis 
    using a0  a2 a3  unfolding Q_domain_var_def Q_domain_def 
    by (metis (no_types, lifting) SUP_cong Sep_Prod_Instance.none_def  plus_fun_def sep_add_commute)
qed


lemma dispose_sounda:
  shows "\<Turnstile> (q\<cdot>i \<mapsto>\<^sub>v |0>) (Dispose q i) ( |>a)" 
proof-
  { fix s s'
    let ?st = "(\<lambda>s. get_stack s) "
    assume a00:"\<turnstile> \<langle>Dispose q i,s\<rangle> \<Rightarrow> s'" and
            a01:"s \<in> Normal ` ((q\<cdot>i \<mapsto>\<^sub>v |0>))"  
    then obtain \<sigma> \<rho> \<Q> where a01:"s = Normal (\<rho>,\<sigma>,\<Q>)" and
         a01a:"(\<rho>,\<sigma>,\<Q>) \<in>  (q\<cdot>i \<mapsto>\<^sub>v |0>)"               
      by auto
    note dest_assign = map_assn_zero_dest[OF a01a]
    moreover obtain \<Q>' \<Q>''  where 
        step:"\<Q> =  \<Q>' + \<Q>'' \<and> Zero \<Q>' \<and>
          s' = Normal (\<rho>, \<sigma>, \<Q>'') \<and>
          \<Q>' ## \<Q>'' \<and>  Q_domain_var (the (var_set q i \<sigma>)) (QStateM_map \<Q>') \<noteq> {} \<and>
          QStateM_vars \<Q>' = Q_domain_var (the (var_set q i \<sigma>)) (QStateM_map \<Q>') \<and>
          (\<forall>e \<in> (the (var_set q i \<sigma>)). (QStateM_map \<Q>') e \<noteq> {})"                 
      apply (rule  QExec_Normal_elim_cases(10)[OF a00[simplified a01]])
       apply blast 
      apply auto  
      using calculation apply auto 
      unfolding Q_domain_def Q_domain_var_def       
      apply (drule spec[of _ \<Q>], auto simp add: ZeroQ_vector_Zero_eq)  
      apply (frule spec[of _ 0])
      by auto         
    moreover have q_domain:"Q_domain (QStateM_map \<Q>') =  Q_domain (QStateM_map \<Q>)"
      using calculation 
      by (simp add: Q_domain_Q)  
    ultimately have eq_Q_Q':"\<Q> = \<Q>'"
      by (smt (verit, ccfv_SIG) QStateM_eq_intro QStateM_map_plus ZeroQ_vector_Zero_eq h 
               list_of_vec_QStateM_vec sep_Q_eq_Q'_Q''_empty sep_disj_zero)
    then have "\<Q>'' = 0" using Q2_is_zero
      using local.step by blast
    moreover obtain sn where 
       s':"s' = Normal sn \<and> sn = (\<rho>, \<sigma>, \<Q>'')"
      using step by auto
    ultimately have  "sn \<in> ( |>a) "
      using dest_assign eq_Q_Q'
      unfolding  empty_qstatem_ass_def get_QStateM_def get_stack_def
      by (simp add: s') 
     then have "s' \<in> Normal ` (( |>a))" using s' by auto
   }
   thus ?thesis  unfolding valid_def by auto
 qed


definition \<pi>::"real \<Rightarrow> ('s state) set"
  where "\<pi> x \<equiv> {s. fst s = x}"

lemma " x\<in> (\<pi> u) \<and> fst x = n \<Longrightarrow> fst x = fst y \<Longrightarrow> y \<in> \<pi> u"
  unfolding \<pi>_def by auto


lemma domain_Q: assumes 
      a1:"(\<forall>e\<in>q. QStateM_map \<Q> e \<noteq> {})" and
      a2:"(k::nat) < 2 ^ card (\<Union> (QStateM_map \<Q> ` q))" and
      a3:"QStateM_vars \<Q> = Q_domain_var (q \<union> qr ) (QStateM_map \<Q>)" and
      a4:"QStateM_list \<Q> = vl" and      
      a6:"q  \<inter> qr   = {}" and a7:"q  \<noteq> {}"                    
    shows "finite (Q_domain_var  q (QStateM_map \<Q>))" and 
          "finite (Q_domain_var qr (QStateM_map \<Q>))" and
          "Q_domain (QStateM_map \<Q>) = QStateM_vars \<Q>" and
          "dim_vec (vec_of_list vl) =
             2 ^ card (Q_domain_var q (QStateM_map \<Q>)) *
             2 ^ card (Q_domain_var qr (QStateM_map \<Q>))" and
          "k < 2 ^ card (Q_domain_var q (QStateM_map \<Q>))" and
          "Q_domain_var q (QStateM_map \<Q>) \<inter> Q_domain_var qr (QStateM_map \<Q>) = {}" and
          "Q_domain_var q (QStateM_map \<Q>) \<noteq> {}" and
          "Q_domain_var qr (QStateM_map \<Q>) = Q_domain (QStateM_map \<Q>) - Q_domain_var q (QStateM_map \<Q>)"    
proof-
  let ?v = "vec_of_list vl" and       
      ?v1 = "Q_domain_var q (QStateM_map \<Q>)" and ?v2 = "Q_domain_var qr (QStateM_map \<Q>)"
  let ?M = "(1\<^sub>k (2 ^ card (\<Union> (QStateM_map \<Q> ` q ))))"
  have "finite (QStateM_vars \<Q>)"
    using a3 finite_Q_domain_var by presburger
  moreover have h1:"QStateM_vars \<Q> = Q_domain_var q (QStateM_map \<Q>) \<union> Q_domain_var qr (QStateM_map \<Q>)"
    using a3 a6 unfolding Q_domain_var_def
    by simp 
  ultimately show f1:"finite ?v1" and f2:"finite ?v2" 
    by auto

  show Q_domain:"Q_domain (QStateM_map \<Q>) = QStateM_vars \<Q>"
    by (simp add: QStateM_rel1 QStateM_vars.rep_eq qstate_def)

  show k:"k < 2 ^ card ?v1"
    using a2 unfolding Q_domain_var_def by auto  

  show inter_12:"?v1 \<inter> ?v2 = {}"
    using q_var_inter_empty
    using a3 a6 domain_qr by auto
  
  show dim_vec:"dim_vec ?v = 2 ^ card ?v1 * 2 ^ card ?v2"
    using a4 QStateM_list_dim_union_vars[OF h1 inter_12] 
    by auto
  show v1_not_empty:"?v1\<noteq>{}"
    by (simp add: Q_domain_var_def a7 local.a1)
  show "?v2 = Q_domain (QStateM_map \<Q>) - ?v1"
    using domain_qr  a3 a6 by blast
qed

lemma \<delta>k:
  assumes a0:"(\<delta>k, \<Q>') = measure_vars k q \<Q>"
  shows "\<delta>k =  Re ((vec_norm
             (matrix_sep q \<Q> 1\<^sub>k (2 ^ card (\<Union> (QStateM_map \<Q> ` q)))))\<^sup>2)" 
  using measure_vars_dest a0 QState_rel3' 
  by (auto simp add: Let_def)

lemma Qv_ptensor:
  assumes a0:"(\<delta>k, \<Q>') = measure_vars k q \<Q>" and
      a1:"(\<forall>e\<in>q. QStateM_map \<Q> e \<noteq> {})" and
      a2:"k < 2 ^ card (\<Union> (QStateM_map \<Q> ` q))" and
      a3:"QStateM_vars \<Q> = Q_domain_var (q \<union> qr) (QStateM_map \<Q>)" and
      a4:"QStateM_list \<Q> = vl" and
      a6:"q  \<inter> qr   = {}" and a7:"q  \<noteq> {}" and a8:"0 < \<delta>k" and
      a9:"M = 1\<^sub>k (2 ^ card (\<Union> (QStateM_map \<Q> ` q)))" and 
      a10:"v1 = Q_domain_var q (QStateM_map \<Q>)" and a11:"v2 = Q_domain_var qr (QStateM_map \<Q>)"
  shows "matrix_sep q \<Q> M = 
            (ptensor_mat v1 v2 M  (1\<^sub>m (2^(card v2))) *\<^sub>v QStateM_vector \<Q>)"
proof-
  let ?v = "vec_of_list vl" and
       ?v1 = "Q_domain_var q (QStateM_map \<Q>)" and ?v2 = "Q_domain_var qr (QStateM_map \<Q>)"
  let ?M = "(1\<^sub>k (2 ^ card (\<Union> (QStateM_map \<Q> ` q))))"

  have f1:"finite ?v1" and f2:"finite ?v2" and
       Q_domain:"Q_domain (QStateM_map \<Q>) = QStateM_vars \<Q>" and
       dim_vec:"dim_vec ?v = 2 ^ card ?v1 * 2 ^ card ?v2" and k:"k < 2 ^ card ?v1" and
       inter_12:"?v1 \<inter> ?v2 = {}" and v1_not_empty:"?v1 \<noteq> {}" and
       v2:"?v2 = Q_domain (QStateM_map \<Q>) - ?v1"
    using domain_Q[of q  \<Q> k qr vl, OF a1 a2 a3 a4 a6 a7] by auto           
  then show ?thesis
    by (simp add: Q_domain_var_def a10 a11 a9 projection1_def matrix_sep_def)  
qed

lemma vec_norm_unit_vec_1:
  assumes a0: "k < n"
  shows "vec_norm (unit_vec n k) = 1" 
  using a0 vec_norm_dest unfolding vec_norm_def by auto

lemma sound_prob_semant_proof_rho:
  assumes a0:"(\<delta>k, \<Q>') = measure_vars k (q \<sigma>) \<Q>" and 
      a1:"(\<forall>e\<in>q \<sigma>. QStateM_map \<Q> e \<noteq> {})" and
      a2:"k < 2 ^ card (\<Union> (QStateM_map \<Q> ` q \<sigma>))" and
      a3:"QStateM_vars \<Q> = Q_domain_var (q \<sigma> \<union> qr \<sigma>) (QStateM_map \<Q>)" and
      a4:"QStateM_list \<Q> = vl \<sigma>" and
      a6:"q \<sigma> \<inter> qr \<sigma>  = {}" and a7:"q \<sigma> \<noteq> {}" and 
      a8:"ns' = (p * \<delta>k, \<sigma>', \<Q>')" and 
      a9:"q \<sigma>' = q \<sigma> " and a10:"qr \<sigma>' = qr \<sigma>" and a11:"vl \<sigma>' = vl \<sigma>" and
      a12:"QStateM_map \<Q>' = QStateM_map \<Q>" 
    shows "\<delta>k = \<rho> q vl k ns'" 
proof-
  let ?q = "q \<sigma>" and ?qr = "qr \<sigma>" and ?v = "vec_of_list (vl \<sigma>)" and
      ?q' = "q \<sigma>'" and ?qr' = "qr \<sigma>'" and ?v' = "vl \<sigma>'" 
  let ?v1 = "Q_domain_var ?q (QStateM_map \<Q>)" and ?v2 = "Q_domain_var ?qr (QStateM_map \<Q>)"
  let ?M = "(1\<^sub>k (2 ^ card (\<Union> (QStateM_map \<Q> ` q \<sigma>))))"

  have f1:"finite ?v1" and f2:"finite ?v2" and
       Q_domain:"Q_domain (QStateM_map \<Q>) = QStateM_vars \<Q>" and
       dim_vec:"dim_vec ?v = 2 ^ card ?v1 * 2 ^ card ?v2" and k:"k < 2 ^ card ?v1" and
       inter_12:"?v1 \<inter> ?v2 = {}" and v1_not_empty:"?v1 \<noteq> {}" and
       v2:"?v2 = Q_domain (QStateM_map \<Q>) - ?v1"
    using domain_Q [OF a1 a2 a3 a4 a6 a7] by auto
  
  note vec_norm_ptensor_eq_sum_norm_k[OF f1 f2 inter_12 k dim_vec]
  moreover have \<delta>k:"\<delta>k =  Re ((vec_norm
             (matrix_sep ?q \<Q> 1\<^sub>k (2 ^ card (\<Union> (QStateM_map \<Q> ` ?q)))))\<^sup>2)"
    using measure_vars_dest measure_vars_dest a0
          QStateM_list.rep_eq QState_wf QState_wf_def vec_of_list_QStateM_list by auto
  moreover have h:"(matrix_sep (q \<sigma>) \<Q> ?M) = 
                 (ptensor_mat ?v1 ?v2
                               (?M::complex mat) (1\<^sub>m (2^(card ?v2))) *\<^sub>v 
                      QStateM_vector \<Q>)"
    using v2
    unfolding matrix_sep_def
    by (simp add: Q_domain Q_domain_var_def projection1_def)
  then have "Re ((vec_norm
                  (ptensor_mat ?v1 ?v2 (1\<^sub>k (2 ^ card ?v1)) (1\<^sub>m (2 ^ card ?v2)) *\<^sub>v
                    vec_of_list (vl \<sigma>)))\<^sup>2) = 
             Re ((vec_norm
                ((matrix_sep (q \<sigma>) \<Q> (1\<^sub>k (2 ^ card ?v1)))))\<^sup>2)"
    using QStateM_list.rep_eq QStateM_vector.rep_eq QState_list.rep_eq 
          QState_vector.rep_eq Q_domain_var_def a4 v2 by auto  
  ultimately have "\<delta>k = (\<Sum>j = 0..<2^(card ?v2). norm (partial_state2.aijv ?v1 ?v2 ?v k j )^2) "
    by (metis Q_domain_var_def Re_complex_of_real)
  
  moreover have "\<rho> q vl k ns' = Re (vec_norm (Matrix.vec (2 ^ card ?v2 ) (local.aij ns' q vl k) )^2)"
    using \<rho>_def vector_s_def get_qstate_def get_stack_def
    by (metis a12 a8 a9 fst_conv snd_conv v2)

  moreover have " Re (vec_norm (Matrix.vec (2 ^ card ?v2 ) (local.aij ns' q vl k) )^2) = 
                 (\<Sum>j = 0..<2^(card ?v2). norm (partial_state2.aijv ?v1 ?v2 ?v k j )^2) "
    unfolding aij_def Let_def using vec_norm_square 
    by (simp add: a11 a12 a8 a9 get_qstate_def get_stack_def v2)

  ultimately show "\<delta>k = \<rho> q vl k ns'" by auto
qed


    
lemma sound_prob_semant_proof:
  assumes a0:"(\<delta>k, \<Q>') = measure_vars k (q \<sigma>) \<Q>" and 
      a1:"(\<forall>e\<in>q \<sigma>. QStateM_map \<Q> e \<noteq> {})" and
      a2:"k < 2 ^ card (\<Union> (QStateM_map \<Q> ` q \<sigma>))" and
      a3:"QStateM_vars \<Q> = Q_domain_var (q \<sigma> \<union> qr \<sigma>) (QStateM_map \<Q>)" and
      a4:"QStateM_list \<Q> = vl \<sigma>" and
      a5:" QStateM_vars \<Q> \<noteq> {}" and
      a6:"q \<sigma> \<inter> qr \<sigma>  = {}" and a7:"q \<sigma> \<noteq> {}" and 
      a8:"ns' = (p * \<delta>k, \<sigma>', \<Q>')" and 
      a9:"q \<sigma>' = q \<sigma> " and a10:"qr \<sigma>' = qr \<sigma>" and a11:"vl \<sigma>' = vl \<sigma>" and
      a12:"QStateM_map \<Q>' = QStateM_map \<Q>" and
      a13:"0 < \<delta>k"        
    shows "\<delta>k = \<rho> q vl k ns'" and 
      "QStateM_vars \<Q>' = Q_domain_var (q \<sigma>) (QStateM_map \<Q>) \<union> 
                         (Q_domain_var (qr \<sigma>) (QStateM_map \<Q>))" and
      "QStateM_vector \<Q>' = 
         (1 / sqrt(\<rho> q vl k ns')) \<cdot>\<^sub>v (ptensor_vec 
          (Q_domain_var (q \<sigma>) (QStateM_map \<Q>))
          (Q_domain_var (qr \<sigma>) (QStateM_map \<Q>))
          (unit_vec (2 ^ card (Q_domain_var (q \<sigma>) (QStateM_map \<Q>))) k)
          (partial_state2.vector_aij (Q_domain_var (q \<sigma>) (QStateM_map \<Q>))
          (Q_domain_var (qr \<sigma>) (QStateM_map \<Q>)) (QStateM_vector \<Q>) k))"    
proof-
  let ?q = "q \<sigma>" and ?qr = "qr \<sigma>" and ?v = "vec_of_list (vl \<sigma>)" and
      ?q' = "q \<sigma>'" and ?qr' = "qr \<sigma>'" and ?v' = "vl \<sigma>'" 
  let ?v1 = "Q_domain_var ?q (QStateM_map \<Q>)" and ?v2 = "Q_domain_var ?qr (QStateM_map \<Q>)"
  let ?M = "(1\<^sub>k (2 ^ card (\<Union> (QStateM_map \<Q> ` q \<sigma>))))"

  note Qv_ptensor = Qv_ptensor[OF a0 a1 a2 a3 a4 a6 a7 a13]
  show "\<delta>k = \<rho> q vl k ns'" 
    using sound_prob_semant_proof_rho[of \<delta>k \<Q>' k q \<sigma> \<Q> qr vl, OF a0 a1 a2 a3 a4 a6 a7 a8 a9 a10 a11 a12]
    by auto
  have f1:"finite ?v1" and f2:"finite ?v2" and
       Q_domain:"Q_domain (QStateM_map \<Q>) = QStateM_vars \<Q>" and
       dim_vec:"dim_vec ?v = 2 ^ card ?v1 * 2 ^ card ?v2" and k:"k < 2 ^ card ?v1" and
       inter_12:"?v1 \<inter> ?v2 = {}" and v1_not_empty:"?v1 \<noteq> {}" and
       v2:"?v2 = Q_domain (QStateM_map \<Q>) - ?v1"
    using domain_Q[OF a1 a2 a3 a4 a6 a7] by auto   
   
    
  show "QStateM_vars \<Q>' = ?v1 \<union> ?v2"
    by (metis QStateM_rel1 QStateM_vars.rep_eq Q_domain_var_def UN_Un a12 a3 qstate_def)
  have "Re (vec_norm (matrix_sep (q \<sigma>) \<Q> (1\<^sub>k (2 ^ card ?v1))))^2 = \<rho> q vl k ns'"
    using Q_domain_var_def \<delta>k \<open>\<delta>k = \<rho> q vl k ns'\<close> a0 vec_norm_Re_0 by force 
  moreover have "\<Q>' = QStateM(QStateM_map \<Q>, QState(QStateM_vars \<Q>, list_of_vec ((1 / sqrt \<delta>k) \<cdot>\<^sub>v  matrix_sep (q \<sigma>) \<Q> (1\<^sub>k ((2::nat) ^ card (\<Union> (QStateM_map \<Q> ` (q \<sigma>))))))))"
    using  measure_vars_dest[of \<delta>k _ _ _ _ , OF  \<delta>k] a0 a8 Qv_ptensor
    apply auto
    by (metis prod.sel(2)) 
  ultimately have "QStateM_vector \<Q>' = (1 /  sqrt(\<rho> q vl k ns')) \<cdot>\<^sub>v (ptensor_mat ?v1 ?v2
                               (?M::complex mat) (1\<^sub>m (2^(card ?v2))) *\<^sub>v QStateM_vector \<Q>)"  
    using a13 \<delta>k[OF a0] Qv_ptensor 
    using a5   sca_mult_q_statem_qstate_vector v1_not_empty
    by (metis Q_domain_var_def \<open>\<delta>k = \<rho> q vl k ns'\<close> a0  measure_vars_dest_QStateM prod.sel(2))  
  moreover have "(1 /sqrt(\<rho> q vl k ns')) \<cdot>\<^sub>v ((ptensor_mat ?v1 ?v2 (?M::complex mat) (1\<^sub>m (2^(card ?v2))) *\<^sub>v QStateM_vector \<Q>)) = 
                 (1 / sqrt(\<rho> q vl k ns')) \<cdot>\<^sub>v ptensor_vec ?v1 ?v2 (unit_vec (2^(card ?v1)) k) (partial_state2.vector_aij ?v1 ?v2 (QStateM_vector \<Q>) k)"
    using v_scalar_mat_product_eq_ptensor[OF f1 f2 inter_12 k dim_vec]
    by (simp add: Q_domain_var_def a4 vec_of_list_QStateM_list)
  ultimately show  "QStateM_vector \<Q>' = (1 / sqrt (\<rho> q vl k ns')) \<cdot>\<^sub>v ptensor_vec ?v1 ?v2 (unit_vec (2^(card ?v1)) k) (partial_state2.vector_aij ?v1 ?v2 (QStateM_vector \<Q>) k)"
    using measure_vars_dest[of \<delta>k] a0  by auto
qed


lemma assest_unit:
  assumes 
      a0:"QStateM_vars \<Q> = Q_domain_var (q \<sigma> \<union> qr \<sigma>) (QStateM_map \<Q>)" and       
      a1:"ns' = (p * \<delta>k, \<sigma>', \<Q>')" and 
      a2:"q \<sigma>' = q \<sigma> " and a3:"finite v1" and a4:"v1 \<noteq> {}" and
      a5:"QStateM_map \<Q>' = QStateM_map \<Q>" and
      a6: "map_q = fst (split_map (QStateM_map \<Q>) (q \<sigma>))" and
      a7:"v1 = Q_domain_var (q \<sigma>) (QStateM_map \<Q>)" and 
      a8: "Q1 = QStateM(map_q, QState(v1, list_of_vec (unit_vec (2^(card v1)) k)))" and
      a9:"k < 2 ^ card v1"
shows "(1, \<sigma>', Q1) \<in> (q \<mapsto> local.unit_vecl ns' q k)"   
proof-
  have "QStateM_wf (QStateM_unfold \<Q>)"
    using QStateM_wf by blast
  then have QStateM_wf1:"(\<forall>x y. x\<noteq>y \<and> x\<in> domain (QStateM_map \<Q>) \<and> y \<in> domain (QStateM_map \<Q>) \<longrightarrow> 
              QStateM_map \<Q> x \<inter> QStateM_map \<Q> y = {})"
    by auto
  have a01:"Q_domain_var (q \<sigma>) (QStateM_map \<Q>) =
           Q_domain_var (q \<sigma>') (fst (split_map (QStateM_map \<Q>) (q \<sigma>)))"
    unfolding _Q_domain_var_def split_map_def constrain_map_def
    by (auto simp add: a0 a2)
  moreover have a02:"list_of_vec (unit_vec (2 ^ card (Q_domain_var (q \<sigma>) (QStateM_map \<Q>))) k) =
          local.unit_vecl ns' q k \<sigma>'" using a1
    unfolding unit_vecl_def Let_def Q_domain_def 
                Q_domain_set_def Q_domain_var_def get_qstate_def get_stack_def 
    using a2 a5 by auto
  moreover have a03:"QState_wf(v1,list_of_vec (unit_vec (2^(card v1)) k))"
    using vec_norm_unit_vec_1
    unfolding  QState_wf_def
    using a3 a4 a9 apply simp
    by (simp add: vec_list)
  moreover have a04:"QStateM_wf (map_q, QState(v1, list_of_vec (unit_vec (2^(card v1)) k)))"  
      using a6 a7
      apply auto
      using QState_var_idem Q_domain_def Q_domain_var_def a03 constrain_map_def split_map_def apply auto[1]
      using QState_var_idem Q_domain_def Q_domain_var_def a03 a01 apply auto[1]
      unfolding  domain_def none_def split_map_def constrain_map_def 
      apply auto 
      subgoal for x y xa xb xc apply (cases "x \<in> q \<sigma>"; cases "y \<in> q \<sigma>"; auto)
      using QStateM_wf1 unfolding domain_def by auto done
  show ?thesis  using a01 a02 a03 a04 a8 a3 a6 a7
    apply (clarify, intro map_assn_intro) by fast+          
qed

lemma assest_vectori1:
  assumes 
      a0:"QStateM_vars \<Q> = Q_domain_var (q \<sigma> \<union> qr \<sigma>) (QStateM_map \<Q>)" and       
      a1:"ns' = (p * \<delta>k, \<sigma>', \<Q>')" and 
      a2:"q \<sigma>' = q \<sigma>" and a2':"qr \<sigma>' = qr \<sigma> " and a2'':"vl \<sigma>' = vl \<sigma>" and
      a3:"QStateM_map \<Q>' = QStateM_map \<Q>" and      
      a4:"v1 = Q_domain_var (q \<sigma>) (QStateM_map \<Q>)" and  
      a6:"v2 = Q_domain_var (qr \<sigma>) (QStateM_map \<Q>)" and      
      a7:"q \<sigma> \<inter> qr \<sigma> = {}" and a8:"\<delta>k = \<rho> q vl k ns'" and a9:"QStateM_list \<Q> = vl \<sigma> "
    shows "list_of_vec (complex_of_real (1 /  sqrt(\<rho> q vl k ns')) \<cdot>\<^sub>v
                       partial_state2.vector_aij (Q_domain_var (q \<sigma>) (QStateM_map \<Q>))
                       (Q_domain_var (qr \<sigma>) (QStateM_map \<Q>)) (QStateM_vector \<Q>) k) =
           local.vector_i ns' q vl k \<sigma>'"
proof-  
  interpret ps2:partial_state2 "list_dims (v1 \<union> v2)" v1 "v2"
    apply standard
    apply (auto simp add: list_dims_def finite_Q_domain_var a4 a6)
    using a0 a7 domain_qr by auto
  
 
  let ?v = "list_of_vec (complex_of_real (1 / sqrt(\<rho>  q vl k ns')) \<cdot>\<^sub>v
             ps2.vector_aij (QStateM_vector \<Q>) k)" 

  have Qstatem_wf_Q:"QStateM_wf (QStateM_unfold \<Q>)"
     using QStateM_wf by blast
  then have QStateM_wf1:"(\<forall>x y. x\<noteq>y \<and> x\<in> domain (QStateM_map \<Q>) \<and> y \<in> domain (QStateM_map \<Q>) \<longrightarrow> 
              QStateM_map \<Q> x \<inter> QStateM_map \<Q> y = {})"
    by auto
  
  have v2:"v2 = QStateM_vars \<Q> - v1"
    using q_vars_q2[of "q \<sigma>" "qr \<sigma>" "QStateM_map \<Q>" "QStateM_vars \<Q>" ] 
          a7  a6 Qstatem_wf_Q a0 a4 eq_QStateM_vars 
    by auto
  have len:"length ?v = length (vector_i ns' q vl k \<sigma>') "
    using v2 a3 a4 a6 a1 a2 QStateM_rel1
    unfolding vector_i_def Let_def  get_qstate_def vector_s_def get_stack_def Q_domain_set_def 
    unfolding ps2.vector_aij_def ps2.aijv_def ps2.d2_def aij_def Let_def
    apply auto
    using QStateM_vars.rep_eq ps2.dims2_def qstate_def by fastforce  
  moreover have  "\<forall>i<length ?v. ?v!i = vector_i ns' q vl k \<sigma>' !i" using 
    assest_vectors_aij[of \<Q> q \<sigma> qr ns' p \<delta>k  \<sigma>' \<Q>' vl,OF a0 a1 a2 a2' a2'' a3 a4 a6 a7 a8 a9]
    unfolding vector_i_def \<rho>_def
    using QSemanticsBig.vec_norm_square  a4 a6  vec_norm_dest by fastforce
  ultimately show ?thesis
    using nth_equalityI a4 a6 by blast 
qed

lemma assest_vectori:
  assumes 
      a0:"QStateM_vars \<Q> = Q_domain_var (q \<sigma> \<union> qr \<sigma>) (QStateM_map \<Q>)" and       
      a1:"ns' = (p * \<delta>k, \<sigma>', \<Q>')" and 
      a2:"q \<sigma>' = q \<sigma>" and a2':"qr \<sigma>' = qr \<sigma> " and a2'':"vl \<sigma>' = vl \<sigma>" and
      a4:"v1 \<noteq> {}" and a3':"finite v2" and
      a5:"QStateM_map \<Q>' = QStateM_map \<Q>" and
      a6: "map_q = fst (split_map (QStateM_map \<Q>) (q \<sigma>))" and
      a6':"map_qr = snd (split_map (QStateM_map \<Q>) (q \<sigma>))" and a6'':"map_qr = constrain_map (QStateM_map \<Q>) (qr \<sigma>)" and
      a7:"v1 = Q_domain_var (q \<sigma>) (QStateM_map \<Q>)" and  
      a7':"v2 = Q_domain_var (qr \<sigma>) (QStateM_map \<Q>)" and a7'':"0 < \<delta>k " and
      a8:"Q2  = QStateM(map_qr, QState(v2, list_of_vec ((1 / sqrt(\<rho> q vl k ns'))\<cdot>\<^sub>v(partial_state2.vector_aij v1 v2 (QStateM_vector \<Q>) k))))" and
      a11:"q \<sigma> \<inter> qr \<sigma> = {}" and a12:"\<delta>k = \<rho> q vl k ns'" and a13:"QStateM_list \<Q> = vl \<sigma> " and
      a14:"QState_wf(v2,list_of_vec ((1 / sqrt(\<rho> q vl k ns'))\<cdot>\<^sub>v(partial_state2.vector_aij v1 v2 (QStateM_vector \<Q>) k)))" and
      a15:"QStateM_wf (map_qr, QState(v2, list_of_vec ((1 / sqrt(\<rho> q vl k ns'))\<cdot>\<^sub>v(partial_state2.vector_aij v1 v2 (QStateM_vector \<Q>) k))))"
shows "(p, \<sigma>', Q2) \<in>  (qr \<mapsto> vector_i ns' q vl k)"   
proof
  have "QStateM_wf (QStateM_unfold \<Q>)"
    using QStateM_wf by blast
  then have QStateM_wf1:"(\<forall>x y. x\<noteq>y \<and> x\<in> domain (QStateM_map \<Q>) \<and> y \<in> domain (QStateM_map \<Q>) \<longrightarrow> 
              QStateM_map \<Q> x \<inter> QStateM_map \<Q> y = {})"
    by auto
  have a01:"Q_domain_var (qr \<sigma>) (QStateM_map \<Q>) =
           Q_domain_var (qr \<sigma>') (snd (split_map (QStateM_map \<Q>) (q \<sigma>)))"
    using a6'' a6' unfolding _Q_domain_var_def split_map_def constrain_map_def none_def
    by (auto simp add: a0 a2')    
  moreover have a02:"list_of_vec (complex_of_real (1 / sqrt(\<rho> q vl k ns')) \<cdot>\<^sub>v
                       partial_state2.vector_aij (Q_domain_var (q \<sigma>) (QStateM_map \<Q>))
                       (Q_domain_var (qr \<sigma>) (QStateM_map \<Q>)) (QStateM_vector \<Q>) k) =
                     local.vector_i ns' q vl k \<sigma>'" 
    using assest_vectori1[of \<Q> q \<sigma> qr, OF a0 a1 a2 a2' a2'' a5 a7  a7' a11 a12 a13] by auto
  moreover have a03:"QState_wf(v2,list_of_vec ((1 / sqrt(\<rho> q vl k ns'))\<cdot>\<^sub>v(partial_state2.vector_aij v1 v2 (QStateM_vector \<Q>) k)))"
    using a14 by auto     
  moreover have a04:"QStateM_wf (map_qr, QState(v2, list_of_vec ((1 / sqrt(\<rho> q vl k ns'))\<cdot>\<^sub>v(partial_state2.vector_aij v1 v2 (QStateM_vector \<Q>) k))))" 
    using a15 by auto     
   have "(p, \<sigma>', QStateM(map_qr, QState(v2, list_of_vec ((1 / sqrt(\<rho> q vl k ns'))\<cdot>\<^sub>v(partial_state2.vector_aij v1 v2 (QStateM_vector \<Q>) k))))) \<in>  (qr \<mapsto> vector_i ns' q vl k)"   
      apply (rule map_assn_intro)
      using a7' a01
      apply (simp add: a6')
      using a02 a7 a7' apply blast
      using a04 apply blast
      using a03 by blast
    thus ?thesis
      using a8  by blast   
    show "(qr \<mapsto> local.vector_i ns' q vl k) \<subseteq> (qr \<mapsto> local.vector_i ns' q vl k)"
      by auto
qed

lemma V1_V2_not_zero_tensor_not_zero:   
     assumes a0:"finite v1" and a1:"finite v2" and a2:"v1 \<inter> v2 = {}" and
              a3:"dim_vec (V1::'a::field vec)  = 2^card v1" and a4:"dim_vec V2 = 2^card v2" and 
              a5:"V1 \<noteq> 0\<^sub>v (2^card v1)" and a6:"V2 \<noteq> 0\<^sub>v (2^card v2)"
      shows "partial_state2.ptensor_vec v1 v2 V1 V2  \<noteq> 0\<^sub>v (2 ^ card (v1 \<union> v2))"
proof-
  interpret ps2:partial_state2 "list_dims (v1 \<union> v2)" v1 v2
    apply standard using a0 a1 a2 a2 a3 a4 by (auto simp add: list_dims_def)
  obtain i j where V1_i_not0:"V1$i \<noteq> 0" and i_less_dim_v1:"i < ps2.d1" and 
                   V2_i_not0:"V2$j \<noteq> 0" and j_less_dim_v2:"j < ps2.d2"
    using a5 a6 a3 a4 not_zero_vector_index
    by (metis a0 a1 a2 length_replicate nth_replicate partial_state2.dims1_def 
         partial_state2.intro prod_list_replicate ps2.d1_def ps2.d2_def ps2.dims2_def) 
  moreover have "ps2.ptensor_vec  V1 V2 $ (ps2.pencode12 (i,j))\<noteq> 0"
    using i_less_dim_v1 j_less_dim_v2 calculation
    unfolding ps2.pencode12_def ps2.ptensor_vec_def partial_state.tensor_vec_def
    by (simp add: partial_state.d1_def partial_state.d2_def 
                  partial_state.dims1_def partial_state.dims2_def 
                  partial_state.encode12_inv1 partial_state.encode12_inv2 partial_state.encode12_lt 
                  ps2.d1_def ps2.d2_def ps2.nths_vars1' ps2.nths_vars2')
  ultimately show ?thesis unfolding ps2.ptensor_vec_def zero_vec_def partial_state.tensor_vec_def 
    apply auto
    by (metis (no_types, lifting) dim_vec index_vec partial_state.d1_def partial_state.d2_def 
              partial_state.dims1_def partial_state.dims2_def partial_state.encode12_lt 
             ps2.d1_def ps2.d2_def ps2.nths_vars1' ps2.nths_vars2' ps2.pencode12_def)
qed

lemma s_product_not_zero_v_not_zero:
  assumes a0:"(a::complex) \<cdot>\<^sub>v v \<noteq> 0\<^sub>v (dim_vec v)" 
  shows"v \<noteq> 0\<^sub>v (dim_vec v)"
proof-
  { assume "v=0\<^sub>v (dim_vec v)"
    then have "\<forall>i<(dim_vec v). v$i = 0"
      by (metis index_zero_vec(1))
    then have "\<forall>i<(dim_vec v). a*v$i = 0"
      by auto
    then have False using a0 unfolding smult_vec_def by auto
  } thus ?thesis by auto
qed

lemma  Q_in_disjunction_conj_unit_vector1:
  assumes a0:"(\<delta>k, \<Q>') = measure_vars k (q \<sigma>) \<Q>" and 
      a1:"(\<forall>e\<in>q \<sigma>. QStateM_map \<Q> e \<noteq> {})" and
      a2:"k < 2 ^ card (\<Union> (QStateM_map \<Q> ` q \<sigma>))" and
      a3:"QStateM_vars \<Q> = Q_domain_var (q \<sigma> \<union> qr \<sigma>) (QStateM_map \<Q>)" and
      a4:"QStateM_list \<Q> = vl \<sigma>" and
      a5:" QStateM_vars \<Q> \<noteq> {}" and
      a6:"q \<sigma> \<inter> qr \<sigma>  = {}" and a7:"q \<sigma> \<noteq> {}" and 
      a8:"ns' = (p * \<delta>k, \<sigma>', \<Q>')" and 
      a9:"q \<sigma>' = q \<sigma> " and a10:"qr \<sigma>' = qr \<sigma>" and a11:"vl \<sigma>' = vl \<sigma>" and
      a12:"QStateM_map \<Q>' = QStateM_map \<Q>" and
      a13:"0 < \<delta>k" and a14:"\<delta>k = \<rho> q vl k ns'" 
    shows "(p, \<sigma>', \<Q>') \<in> (q \<mapsto> local.unit_vecl ns' q k \<and>\<^sup>* qr \<mapsto> vector_i ns' q vl k)"
proof-
  let ?q = "q \<sigma>" and ?qr = "qr \<sigma>" and ?v = "vec_of_list (vl \<sigma>)" and
      ?q' = "q \<sigma>'" and ?qr' = "qr \<sigma>'" and ?v' = "vl \<sigma>'" 
  let ?v1 = "Q_domain_var ?q (QStateM_map \<Q>)" and ?v2 = "Q_domain_var ?qr (QStateM_map \<Q>)"
  let ?M = "(1\<^sub>k (2 ^ card (\<Union> (QStateM_map \<Q> ` q \<sigma>))))"
  let ?n = "Re ((vec_norm
             (QStateM_vector
               (matrix_sep_QStateM ?q \<Q> 1\<^sub>k (2 ^ card (\<Union> (QStateM_map \<Q> ` ?q))))))\<^sup>2 /
             (vec_norm (QStateM_vector \<Q>))\<^sup>2)"
  have "QStateM_wf (QStateM_unfold \<Q>)"
    using QStateM_wf by blast
  then have QStateM_wf1:"(\<forall>x y. x\<noteq>y \<and> x\<in> domain (QStateM_map \<Q>) \<and> y \<in> domain (QStateM_map \<Q>) \<longrightarrow> 
              QStateM_map \<Q> x \<inter> QStateM_map \<Q> y = {})"
    by auto
  have f1:"finite ?v1" and f2:"finite ?v2" and
       Q_domain:"Q_domain (QStateM_map \<Q>) = QStateM_vars \<Q>" and
       dim_vec:"dim_vec ?v = 2 ^ card ?v1 * 2 ^ card ?v2" and k:"k < 2 ^ card ?v1" and
       inter_12:"?v1 \<inter> ?v2 = {}" and v1_not_empty:"?v1 \<noteq> {}" and
       v2:"?v2 = Q_domain (QStateM_map \<Q>) - ?v1"
    using domain_Q [OF a1 a2 a3 a4 a6 a7] by auto 
  
  interpret ps2:partial_state2 "list_dims (?v1 \<union> ?v2)" ?v1 ?v2
    apply standard by (auto simp add: v2 list_dims_def f1 f2 Q_domain a3 finite_Q_domain_var)
    
  let ?L1 = "unit_vec (2^(card ?v1)) k" and
      ?L2 = "ps2.vector_aij  (QStateM_vector \<Q>) k"

  have delta:"\<delta>k = \<rho> q vl k ns'" and q'_vars:"QStateM_vars \<Q>' = ?v1 \<union> ?v2" and
       q'_vector:"QStateM_vector \<Q>' = (1 / sqrt(\<rho> q vl k ns')) \<cdot>\<^sub>v ptensor_vec ?v1 ?v2 ?L1 ?L2"
    using sound_prob_semant_proof[OF assms(1-14)] by auto

  have conj_domain_vars_empty:"Q_domain_var (q \<sigma>) (QStateM_map \<Q>) \<inter> Q_domain_var (qr \<sigma>) (QStateM_map \<Q>) = {}"
    using inter_12 by blast 
  
  have prob_not_zero: "1 / sqrt(\<rho> q vl k ns')\<noteq>0"
    using   a13 vec_norm_ptensor_eq_sum_norm_k[OF f1 f2 conj_domain_vars_empty k]  
    unfolding Let_def
    by (smt (verit, ccfv_SIG) \<rho>_def delta divide_eq_0_iff real_sqrt_eq_zero_cancel_iff sum.cong)  
  
  let ?V1 = "unit_vec (2 ^ card (Q_domain_var (q \<sigma>) (QStateM_map \<Q>))) k"
  let ?V2 = "ps2.vector_aij (QStateM_vector \<Q>) k"
 
  have "QStateM_vector \<Q>'\<noteq> 0\<^sub>v (2^card(?v1 \<union> ?v2))"
    apply transfer
    by (metis QState_rel3' one_neq_zero vec_norm_zero zero_carrier_vec)
  then have  ptensor_not_zero:"complex_of_real (1 / sqrt(\<rho> q vl k ns')) \<cdot>\<^sub>v ps2.ptensor_vec (unit_vec (2 ^ card (Q_domain_var (q \<sigma>) (QStateM_map \<Q>))) k) (ps2.vector_aij (QStateM_vector \<Q>) k) \<noteq>
       0\<^sub>v (2 ^ card (Q_domain_var (q \<sigma>) (QStateM_map \<Q>) \<union> Q_domain_var (qr \<sigma>) (QStateM_map \<Q>)))"
    using q'_vector prob_not_zero by auto
  then have ptensor_not_zeroa:"ps2.ptensor_vec (unit_vec (2 ^ card (Q_domain_var (q \<sigma>) (QStateM_map \<Q>))) k) (ps2.vector_aij (QStateM_vector \<Q>) k) \<noteq>
       0\<^sub>v (2 ^ card (Q_domain_var (q \<sigma>) (QStateM_map \<Q>) \<union> Q_domain_var (qr \<sigma>) (QStateM_map \<Q>)))"
    using s_product_not_zero_v_not_zero by auto
  then have "?V1 \<noteq> 0\<^sub>v (2 ^ card (?v1))" and "?V2 \<noteq> 0\<^sub>v (2 ^ card (?v2))" using k
    using unit_vec_nonzero apply blast  
    using not_zero_tensor_product_comp_vectors
    by (metis ptensor_not_zeroa f1 f2 index_unit_vec(3) index_zero_vec(2) inter_12)
    
 
  have QM_wf:"QStateM_wf (QStateM_unfold \<Q>')" and Q_wf:"QState_wf (QState_unfold (qstate \<Q>'))"
    apply (simp add: QStateM_rel1 QStateM_rel2)
    using QState_wf by blast
  then have  "\<exists>i<length (QStateM_list \<Q>'). (QStateM_list \<Q>')!i\<noteq>0"
    unfolding  QState_wf_def
    unfolding qstate_def apply transfer'
    using QState_rel4' by blast 
  then have len_L2:"\<exists>i< dim_vec ?L2. list_of_vec ?L2 ! i \<noteq> 0"  
    using q'_vector not_zero_tensor_product_comp_index[of ?v1 ?v2 ?L1 ?L2, OF conj_domain_vars_empty f1 f2 ptensor_not_zeroa] 
    using q'_vars list_of_vec_QStateM_vec prob_not_zero
    by (metis Matrix.dim_vec list_of_vec_index partial_state2.d2_def prod_list_replicate ps2.dims2_def ps2.partial_state2_axioms ps2.vector_aij_def) 

  let ?map_q = "fst (split_map (QStateM_map \<Q>) (q \<sigma>))" and
      ?map_qr = "snd (split_map (QStateM_map \<Q>) (q \<sigma>))" and 
       ?V1 = "list_of_vec (unit_vec (2^(card ?v1)) k)" and 
       ?V2 = "list_of_vec ((1 / sqrt(\<rho> q vl k ns'))\<cdot>\<^sub>v(partial_state2.vector_aij ?v1 ?v2 (QStateM_vector \<Q>) k))"
  let ?Q1 = "QStateM(?map_q, QState(?v1, ?V1))"
  let ?Q2 = "QStateM(?map_qr, QState(?v2, ?V2))"
  have map_qr_cons:"?map_qr = constrain_map (QStateM_map \<Q>) (qr \<sigma>)" 
    using split_q1_constrain_q2
    by (simp add: QStateM_wf1 Q_domain a3 a6)
  
  have v1_q_wf:"QState_wf (?v1, ?V1)"
    apply (simp add: f1 v1_not_empty  QState_wf_def)
    using a2 unfolding Q_domain_var_def
    by (metis vec_list vec_norm_unit_vec_1)
  then have v1_qm_wf:"QStateM_wf (?map_q, QState(?v1, ?V1))"
    using QStateM_wf1 QState_var_idem constrain_map_wf1 
      q_domain_split_eq_q_domain_var split_map_def by auto             
  have v2_q_wf:"QState_wf (?v2, ?V2)" 
    using f2  a3 a13 len_L2 prob_not_zero 
    unfolding 
     QState_wf_def Q_domain_var_def
    by (metis (no_types, lifting) Matrix.dim_vec QStateM_vector.rep_eq QState_rel3' Q_domain_var_def a2 dim_vec_of_list f1 
         fst_conv index_smult_vec(2) index_unit_vec(3) inter_12 mult_1 
         partial_state2.vector_aij_def prod_list_replicate ps2.d2_def ps2.dims2_def 
       ps2.partial_state2_axioms pscalar_ptensor_2 q'_vector snd_conv 
    tensor_norm vec_list vec_norm_unit_vec_1) 
        
  then have v2_qm_wf:"QStateM_wf (?map_qr, QState(?v2, ?V2))"
    using QStateM_wf1 QState_var_idem constrain_map_wf1 
      map_qr_cons q_domain_constrain_eq_q_domain_var
    by simp    
 
  have a00:"(1, \<sigma>', ?Q1) \<in> (q \<mapsto> local.unit_vecl ns' q k)" 
    using assest_unit[of \<Q> q \<sigma> qr, OF a3 a8 a9 f1 v1_not_empty a12] k
    by blast       
  moreover have a01:"(p, \<sigma>', ?Q2) \<in> (qr \<mapsto> vector_i ns' q vl k)"
    using assest_vectori[of \<Q> q \<sigma> qr, OF a3 a8 a9 a10 a11 v1_not_empty f2 a12 _ _ map_qr_cons _  _ a13 _ a6 a14 a4 v2_q_wf v2_qm_wf]
    by auto
  moreover have a03:"?Q1 ## ?Q2" 
  proof-    
     have "?map_q ## ?map_qr" and "QState(?v1, ?V1) ## QState(?v2, ?V2)"
      using local.a1 q_map_int apply blast 
      unfolding sep_disj_QState disj_QState_def 
      using v2_q_wf v1_q_wf inter_12 QState_var_idem
      by blast         
    then show ?thesis using v2_qm_wf v1_qm_wf
      by (simp add: QStateM_wf_map QStateM_wf_qstate sep_disj_QStateM)      
  qed    
  ultimately have "(1*p, \<sigma>', ?Q1 + ?Q2) \<in> (q \<mapsto> local.unit_vecl ns' q k \<and>\<^sup>* qr \<mapsto> vector_i ns' q vl k)"
    by (fast intro: Q_sep_dis_set_intro)     
  moreover have "?Q1 + ?Q2 = \<Q>'"
  proof-
    have "?map_q + ?map_qr = QStateM_map \<Q>'"
      using a12 local.a1 q_map_split by auto    
    moreover have "QState(?v1, ?V1) + QState(?v2, ?V2) = qstate \<Q>'"           
    proof-      
      have a01:"QStateM_vars \<Q>' = Q_domain_var (q \<sigma>) (QStateM_map \<Q>) + Q_domain_var (qr \<sigma>) (QStateM_map \<Q>)"         
        by (simp add: q'_vars plus_set_def)
      have a02:"QStateM_vector \<Q>' = ptensor_vec ?v1 ?v2 (vec_of_list ?V1) (vec_of_list ?V2) " 
        using q'_vector f1 pscalar_ptensor_2[OF inter_12 f1 f2] 
        unfolding ps2.vector_aij_def ps2.d2_def ps2.dims2_def
        by (smt (verit, best) Matrix.dim_vec index_unit_vec(3) prod_list_replicate  vec_list)
      show ?thesis 
        using QState_plus_intro[OF inter_12 v1_q_wf v2_q_wf] a01 a02 
        unfolding qstate_def apply transfer' by auto
    qed
    ultimately show ?thesis
      using QStateM_wf_map QStateM_wf_qstate idem_QState 
      plus_QStateM v1_qm_wf v2_qm_wf by auto
  qed 
  ultimately show ?thesis by auto
qed  


lemma meassure_sound: 
  assumes a0:"v \<in> nat_vars" and a1:"not_access_v q v" and 
          a2:"not_access_v vl v" and a3:"not_access_v qr v"
  shows "\<Turnstile> (q\<cdot>qr \<mapsto> vl) v:=meassure q
            {s. s \<in> (\<Union>i\<in>{q}\<^sub>s. 
                       (v\<down>\<^sub>(from_nat i)) \<inter>
                       ((q \<mapsto> local.unit_vecl s q i \<and>\<^sup>* qr \<mapsto> vector_i s q vl i) \<smile>
                        \<rho> q vl i s))}"
proof-
  { fix s s'
    let ?st = "(\<lambda>s. get_stack s) "
    assume a00:"\<turnstile> \<langle>v:=meassure q,s\<rangle> \<Rightarrow> s'" and
            a01:"s \<in> Normal ` (q\<cdot>qr \<mapsto> vl)"
    then obtain \<sigma> p \<Q> where a01:"s = Normal (p,\<sigma>,\<Q>)" and
         a01a:"(p,\<sigma>,\<Q>) \<in>  (q\<cdot>qr \<mapsto> vl)"               
      by auto
    note dest_assign = map_assn'_dest[OF a01a]    
    obtain  k \<delta>k \<Q>' ns'
         where step:"s' = Normal ns' \<and> ns' = (p * \<delta>k, set_value \<sigma> v (from_nat k), \<Q>') \<and>
                 (\<forall>e\<in>q \<sigma>. QStateM_map \<Q> e \<noteq> {}) \<and> 
                 k < 2 ^ card (\<Union> (QStateM_map \<Q> ` q \<sigma>)) \<and>
                (\<delta>k, \<Q>') = measure_vars k (q \<sigma>) \<Q> \<and> 0 < \<delta>k"
      by (rule QExec_Normal_elim_cases(8)[OF a00[simplified a01]], 
             auto intro: simp add: dest_assign)
    let ?\<sigma>' = "set_value \<sigma> v (from_nat k)"
    have q:"q \<sigma> = q ?\<sigma>'" using a0 a1 step
      using  from_nat_in_vdomain not_access_v_f_q_eq_set by blast
    have qr:"qr \<sigma> = qr ?\<sigma>'" using a0 a3 step
      using  from_nat_in_vdomain not_access_v_f_q_eq_set by blast
    have vl:"vl \<sigma> = vl ?\<sigma>'"
      using a0 a2 step 
      using from_nat_in_vdomain not_access_v_f_q_eq_set by blast
    have q_state_q_q':"QStateM_map \<Q> = QStateM_map \<Q>'"
      by (metis (no_types) local.step measure_vars_QStateM_map)
    have "\<delta>k = \<rho> q vl k ns'" 
      using step dest_assign q_state_q_q' q qr vl sound_prob_semant_proof_rho
      by (force intro:sound_prob_semant_proof_rho)
    have "ns' \<in> ((v\<down>\<^sub>(from_nat k)) \<inter>
                 ((q \<mapsto> local.unit_vecl ns' q k \<and>\<^sup>* qr \<mapsto> vector_i ns' q vl k) \<smile>
                 \<rho> q vl k ns'))" 
    proof-
      obtain a b c where a00:"ns' = (a,b,c)"
        using local.step by blast
   
      have "(p, set_value \<sigma> v (from_nat k), \<Q>') \<in> (q \<mapsto> local.unit_vecl ns' q k \<and>\<^sup>* qr \<mapsto> vector_i ns' q vl k)"         
        apply (rule Q_in_disjunction_conj_unit_vector1[of \<delta>k \<Q>' k q \<sigma> \<Q> qr vl ns' p ?\<sigma>'])
        using local.step dest_assign q qr vl q_state_q_q' \<open>\<delta>k = \<rho> q vl k ns'\<close>
        by auto

      moreover have "\<delta>k = \<rho> q vl k ns'" 
        using step dest_assign q_state_q_q' q qr vl sound_prob_semant_proof_rho      
        by (force intro:sound_prob_semant_proof_rho)
      
      ultimately have "ns' \<in> (q \<mapsto> local.unit_vecl ns' q k \<and>\<^sup>* qr \<mapsto> vector_i ns' q vl k) \<smile>
                        \<rho> q vl k ns'" 
        using prob_assert_intro[of \<delta>k] step a00   by fastforce               
      moreover have "ns' \<in> (v\<down>\<^sub>(from_nat k))"
        by (simp add:  get_set get_stack_def local.step set_value_def val_var_def)      
      ultimately show ?thesis by auto
    qed            
    moreover have "fst (QStateM_unfold (snd (snd ns'))) = QStateM_map \<Q>'"
      using step by auto    
    then have "k\<in>{q}\<^sub>ns'"
      unfolding card_set_q_def Let_def Q_domain_set_def get_stack_def get_qstate_def  
      using step q_state_q_q' dest_assign[simplified q qr vl] q
      by auto
    ultimately have "ns' \<in> {s. s \<in> (\<Union>i\<in>{q}\<^sub>s.
                 (v\<down>\<^sub>(from_nat i)) \<inter>
                 ((q \<mapsto> local.unit_vecl s q i \<and>\<^sup>* qr \<mapsto> vector_i s q vl i) \<smile>
                 \<rho> q vl i s))}" 
      unfolding card_set_q_def Let_def Q_domain_set_def  by fast
    then have "s' \<in> Normal ` {s. s \<in> (\<Union>i\<in>{q}\<^sub>s.
                           (v\<down>\<^sub>(from_nat i)) \<inter>
                           ((q \<mapsto> local.unit_vecl s q i \<and>\<^sup>* qr \<mapsto> vector_i s q vl i) \<smile>
                           \<rho> q vl i s))}"
      using step by auto
  } thus ?thesis unfolding valid_def by auto
qed


(* 


Frame Rule

*)




inductive_cases QExec_Normal_Fault_elim_cases [cases set]:  
  "\<turnstile>\<langle>Seq c1 c2,Normal s\<rangle> \<Rightarrow>  Fault"

lemma assumes a0:"\<turnstile> \<langle>Seq c1 c2,Normal s\<rangle> \<Rightarrow> t"
  shows "\<exists>s'. \<turnstile> \<langle>c1,Normal s\<rangle> \<Rightarrow> s' \<and> \<turnstile> \<langle>c2,s'\<rangle> \<Rightarrow> t"
using QExec_Normal_elim_cases(5)[OF a0]
  by metis

lemma seq_normal:assumes a0:"\<turnstile> \<langle>Seq c1 c2,Normal s\<rangle> \<Rightarrow> Normal t"
  shows "\<exists>s'. \<turnstile> \<langle>c1,Normal s\<rangle> \<Rightarrow> Normal s' \<and> \<turnstile> \<langle>c2,Normal s'\<rangle> \<Rightarrow> Normal t"
  apply (rule QExec_Normal_elim_cases(5)[OF a0])
  subgoal for \<sigma>'    
    by (cases \<sigma>', auto intro: QExec_elim_cases(1))    
  done

lemma  QState_map_not_empty_plus:
  assumes a0:"QM1 ## QM2" and a1:"\<exists>x\<in>q. QM1 x \<noteq> {}"
  shows "\<exists>x\<in>q. (QM1 + QM2) x \<noteq> {}"
proof-
  show ?thesis unfolding plus_fun_def none_def using a1 by auto
qed

lemma  QState_map_all_not_empty_plus:
  assumes a0:"QM1 ## QM2" and a1:"\<forall>x\<in>q. QM1 x \<noteq> {}"
  shows "\<forall>x\<in>q. (QM1 + QM2) x \<noteq> {}"
proof-
  show ?thesis unfolding plus_fun_def none_def using a1 by auto
qed

lemma eq_domain_var_plus:
  assumes a0:"Q1 ## Q2" and a1:"\<forall>x\<in>q.  (QStateM_map Q1) x \<noteq> {}"
  shows " Q_domain_var q (QStateM_map Q1) = Q_domain_var q (QStateM_map (Q1 + Q2))"
proof-
  
  have "(\<forall>x y. x\<noteq>y \<and> x\<in> domain (QStateM_map (Q1+Q2)) \<and> y \<in> domain (QStateM_map (Q1+Q2)) \<longrightarrow> (QStateM_map (Q1+Q2)) x \<inter> (QStateM_map (Q1+Q2)) y = {})"
    by (simp add: QStateM_rel2)
   moreover have "(\<forall>x y. x\<noteq>y \<and> x\<in> domain (QStateM_map Q1) \<and> y \<in> domain (QStateM_map Q1) \<longrightarrow> (QStateM_map Q1) x \<inter> (QStateM_map Q1) y = {})"
    by (simp add: QStateM_rel2)
  ultimately show ?thesis using a0 unfolding   plus_fun_def Q_domain_var_def sep_disj_fun_def opt_class.domain_def 
    apply auto
    by (metis QStateM_map_plus Sep_Prod_Instance.none_def local.a1 plus_fun_def sep_add_commute sep_disj_commuteI)+
    
  qed




lemma tensor_product_1ma:
  assumes a0:"q \<subseteq> Q" and a2:"finite Q"
  shows "1\<^sub>m (2^ card Q) =  
         ptensor_mat q (Q - q) (1\<^sub>m (2^ card q)) (1\<^sub>m (2^ card (Q - q)))"
proof-
  interpret ps2:partial_state2 "list_dims Q" q "Q - q"    
    apply standard  
    unfolding list_dims_def using a0 a2 
    by (auto simp add:finite_subset sup.absorb1 sup_commute)

  interpret ps_1:partial_state ps2.dims0 ps2.vars1' .
  have "dim_row (1\<^sub>m (2 ^ card Q)) =
        dim_row (ps2.ptensor_mat (1\<^sub>m (2 ^ card q)) (1\<^sub>m (2 ^ card (Q - q))))"
    by (simp add: a0 sup.absorb2 ps2.d0_def ps2.dims0_def ps2.vars0_def)    
  moreover have "dim_col (1\<^sub>m (2 ^ card Q)) =
         dim_col (ps2.ptensor_mat (1\<^sub>m (2 ^ card q)) (1\<^sub>m (2 ^ card (Q - q))))"
    by (simp add: a0 sup.absorb2 ps2.d0_def ps2.dims0_def ps2.vars0_def)
  moreover have 
   "\<And>i j. \<lbrakk>i < dim_row (ps2.ptensor_mat (1\<^sub>m (2 ^ card q)) (1\<^sub>m (2 ^ card (Q - q))));
           j < dim_col (ps2.ptensor_mat (1\<^sub>m (2 ^ card q)) (1\<^sub>m (2 ^ card (Q - q))))\<rbrakk>
           \<Longrightarrow> 1\<^sub>m (2 ^ card Q) $$ (i, j) =
                ps2.ptensor_mat (1\<^sub>m (2 ^ card q)) (1\<^sub>m (2 ^ card (Q - q))) $$ (i, j)"
    apply auto using calculation(2) ps2.partial_state2_axioms ps2.ptensor_mat_id
    unfolding partial_state2.d1_def partial_state2.d2_def 
              partial_state2.dims1_def partial_state2.dims2_def apply auto
    by (smt (z3) one_mat_one one_mat_zero partial_state2.d1_def partial_state2.d2_def 
                 partial_state2.dims1_def partial_state2.dims2_def prod_list_replicate 
                 ps2.pmat_extension_def ps2.pmat_extension_id)+    
  ultimately show ?thesis by fast
qed

lemma tensor_product_1m:
  assumes a0:"Q1 \<inter> Q2 = {}"  and a1:"finite Q1" and a2:"finite Q2"
  shows "1\<^sub>m (2^(card (Q1 \<union> Q2))) =  
         ptensor_mat Q1 Q2 (1\<^sub>m (2^(card Q1))) (1\<^sub>m (2^(card Q2)))"
  using tensor_product_1ma[of Q1 "Q1 \<union> Q2"] a0 a1 a2
    by (simp add: Diff_triv Int_commute Un_Diff)

abbreviation matrix_M_unit :: "nat set \<Rightarrow> nat set \<Rightarrow> complex mat \<Rightarrow>  complex mat" 
  where "matrix_M_unit q_vars_m q_vars_q M \<equiv>
         ptensor_mat q_vars_m (q_vars_q - q_vars_m)
                               (M::complex mat) (1\<^sub>m (2^(card (q_vars_q - q_vars_m))))"

lemma ptensor_unit_assoc:
    assumes a0:"finite q_vars_q" and 
              a1:"q_vars_m \<subseteq> q_vars_q1" and
              a2:"q_vars_q1 \<subseteq> q_vars_q"
       shows "ptensor_mat q_vars_m (q_vars_q - q_vars_m) M (1\<^sub>m (2^(card (q_vars_q - q_vars_m)))) = 
              ptensor_mat q_vars_q1 (q_vars_q - q_vars_q1)
              (ptensor_mat q_vars_m (q_vars_q1 - q_vars_m) M (1\<^sub>m (2^(card (q_vars_q1 - q_vars_m)))))
              (1\<^sub>m (2^(card (q_vars_q - q_vars_q1))))" 
proof-
  let ?rest = "q_vars_q1 - q_vars_m" and ?q2 = "q_vars_q - q_vars_q1"
  let ?uni_rest = "(1\<^sub>m (2 ^ card ?rest))" and ?uni_q2 = "1\<^sub>m (2 ^ card ?q2)"

  have eq1[simp]:"q_vars_q - q_vars_m - ?rest = ?q2"
    using a1 a2 by auto 
  have eq2[simp]:"q_vars_m \<union> ?rest = q_vars_q1" using a1 a2 by auto
  have eq3[simp]:"q_vars_m \<union> q_vars_q1 = q_vars_q1" using a1 a2 by auto
  have eq4[simp]:"q_vars_q1 - q_vars_m \<union> (q_vars_q - q_vars_q1) = q_vars_q - q_vars_m"
    using a1 a2 by auto
  interpret ps2_m_q:partial_state2 "list_dims q_vars_q" q_vars_m  "q_vars_q - q_vars_m"
    apply standard apply (auto simp add: list_dims_def) using a0 a1 a2 apply auto
     by (auto simp add: finite_subset sup.absorb2 sup_commute)          
  interpret ps_m_q:partial_state ps2_m_q.dims0 ps2_m_q.vars1' . 

  interpret ps2_q1_q:partial_state2 "list_dims q_vars_q" q_vars_q1 "q_vars_q - q_vars_q1"
    apply standard apply (auto simp add: list_dims_def) using a0 a1 a2
     by (auto simp add: finite_subset  sup_absorb2)

  interpret ps_q1_q:partial_state ps2_q1_q.dims0 ps2_q1_q.vars1' .  

  interpret ps2_m_q1:partial_state2 "list_dims q_vars_q1" q_vars_m "?rest"
    apply standard apply (auto simp add: list_dims_def) using a0 a1 a2
    by (auto simp add: finite_subset)

  interpret ps_m_q1: partial_state ps2_m_q1.dims0 ps2_m_q1.vars1' .

  interpret ps2_q1_qa:partial_state2 "list_dims (?rest \<union> ?q2)" "?rest" "?q2"   
    apply standard apply (auto simp add: list_dims_def) using a0 a1 a2 apply auto 
    by (auto simp add: finite_subset  sup_absorb1)
  interpret ps_q1_qa:partial_state ps2_q1_q.dims0 ps2_q1_q.vars1' . 
 
  have f1:"?rest \<subseteq> q_vars_q - q_vars_m"
    using a1 a2 by auto
  have f2:"finite (q_vars_q - q_vars_m)" using a1 a2 a0 by auto
  
  have "ps2_m_q.ptensor_mat M (1\<^sub>m (2 ^ card (q_vars_q - q_vars_m))) =
        ps2_m_q.ptensor_mat M (ps2_q1_qa.ptensor_mat (1\<^sub>m (2 ^ card ?rest))
              (1\<^sub>m (2 ^ card ?q2)))"
    by (auto simp add: tensor_product_1ma[OF f1 f2])
  then show ?thesis      
    using a0 a1 a2  ps2_q1_q.finite_v1  ps2_m_q1.finite_v1 ps2_q1_q.finite_v1 ps2_m_q1.disjoint
    by (auto dest: ptensor_mat_assoc[of q_vars_m ?rest ?q2 M ?uni_rest ?uni_q2, simplified])       
qed

lemma mat_sep_G:
  assumes a0:"Q1 ## Q2" and a1:"\<forall>e \<in> q. QStateM_map Q1 e \<noteq> {}" and 
          a3:"unitary M" and 
          a4:"M \<in> carrier_mat (2^(card ( \<Union> (QStateM_map Q1 ` q)))) (2^(card (\<Union> (QStateM_map Q1 ` q))))"       
  shows "matrix_sep_QStateM q (Q1 + Q2) M = (matrix_sep_QStateM q Q1 M) + Q2"
proof-
  let ?sep_vars = "Q_domain_var q (QStateM_map Q1)" and
      ?var_d = "QStateM_vars Q1" and ?var_d2 = "QStateM_vars Q2" 
  let ?var_r = "?var_d - ?sep_vars"

  let ?sep_vars' = "Q_domain_var q (QStateM_map (Q1 + Q2))" and
      ?var_d' = "QStateM_vars (Q1 + Q2)" 
  let ?var_r' = "?var_d' - ?sep_vars'"  
  let ?ptensor_mat = "(ptensor_mat ?sep_vars ?var_r (M::complex mat) (1\<^sub>m (2^(card ?var_r))))"
  let ?mat_sep_v = "?ptensor_mat *\<^sub>v QStateM_vector Q1"
  let ?vec_mat_sep_plus_q2 = "partial_state2.ptensor_vec 
                       (QStateM_vars Q1) (QStateM_vars Q2) ?mat_sep_v (QStateM_vector Q2)"
  let ?vec_mat_sep_q1_plus_q2 = "ptensor_mat ?sep_vars' ?var_r'
                                   (M::complex mat) (1\<^sub>m (2^(card ?var_r'))) *\<^sub>v 
                                   QStateM_vector  (Q1 + Q2)"
  

  have qvars_empty:"QStateM_vars Q1 \<inter> QStateM_vars Q2 = {}" using a0
    by (simp add: QStateM_vars.rep_eq disj_QState_def qstate_def sep_disj_QState sep_disj_QStateM)

  have q_vars_in_Q_vars:"?sep_vars \<subseteq> ?var_d"
    by (simp add: Q_domain_var_in_vars)

  have q_vars_map_q1q2_eq_map_q1 [simp]: 
    "Q_domain_var q (QStateM_map (Q1 + Q2)) = Q_domain_var q (QStateM_map Q1)"
    using a0 eq_domain_var_plus local.a1 by fastforce 

  have QStateM_vars_eq_q_U_r:"Q_domain_var q (QStateM_map (Q1 + Q2)) \<union>
     (QStateM_vars Q1 - Q_domain_var q (QStateM_map Q1)) = QStateM_vars Q1"
    using q_vars_in_Q_vars
    by auto
  
  have QVars_Q1_Q2[simp]:
  "QStateM_vars (Q1 + Q2) = QStateM_vars Q1 \<union>  QStateM_vars Q2"
    by (simp add: QStateM_vars_plus a0)

  have var_r'_eq_union_r_d2:"?var_r' = (?var_r \<union>  ?var_d2)"
    by (metis Diff_Int_distrib Diff_cancel Diff_eq_empty_iff Diff_triv 
         QStateM_vars_eq_q_U_r QVars_Q1_Q2 Un_Diff Un_upper1 inf_commute 
        inf_right_idem q_vars_map_q1q2_eq_map_q1 qvars_empty) 
 
  then have 
    QStateM_map_Q1:"QStateM_map (matrix_sep_QStateM q Q1 M) = QStateM_map Q1" and 
    QStateM_vars_Q1:"QStateM_vars (matrix_sep_QStateM q Q1 M) = QStateM_vars Q1" and
    QStateM_list_Q1:"QStateM_list (matrix_sep_QStateM q Q1 M) = 
         list_of_vec (ptensor_mat ?sep_vars ?var_r
                               (M::complex mat) (1\<^sub>m (2^(card ?var_r))) *\<^sub>v 
                      QStateM_vector Q1)"
    using matrix_sep_dest[OF a3 a4] unfolding matrix_sep_def Let_def Q_domain_var_def
    apply auto
    by (meson a4 carrier_matD(1))
  then have QStateM_list_Q1_plus_Q2:"QStateM_list ((matrix_sep_QStateM q Q1 M) + Q2) = 
                                     list_of_vec ?vec_mat_sep_plus_q2"
    using QStateM_list_plus QStateM_vars_Q1
    by (metis QStateM_rel1 a0 disj_QState_def sep_disj_QState sep_disj_QStateM 
            vec_list vec_of_list_QStateM_list) 

 
  then have   
     QStateM_map_Q12:"QStateM_map (matrix_sep_QStateM q  (Q1 + Q2) M) = QStateM_map  (Q1 + Q2)" and
     QStateM_vars_Q12:"QStateM_vars (matrix_sep_QStateM q  (Q1 + Q2) M) = QStateM_vars  (Q1 + Q2)" and
     QStateM_list_Q12:"QStateM_list (matrix_sep_QStateM q  (Q1 + Q2) M) = 
         list_of_vec (ptensor_mat ?sep_vars' ?var_r'
                               (M::complex mat) (1\<^sub>m (2^(card ?var_r'))) *\<^sub>v 
                      QStateM_vector  (Q1 + Q2))"
    using  matrix_sep_dest a3 a4   q_vars_map_q1q2_eq_map_q1 
    unfolding matrix_sep_def Let_def Q_domain_var_def 
    by auto
                                             

  interpret ps21:partial_state2 "list_dims(?var_r \<union> (QStateM_vars Q2))" ?var_r  "QStateM_vars Q2"
    apply standard apply (auto simp add: list_dims_def)
    apply (simp add: QStateM_vars.rep_eq QState_rel3')
    using QStateM_vars.rep_eq qvars_empty apply auto[1]
    by (auto simp add: QStateM_vars.rep_eq QState_rel2')    
  interpret ps_1:partial_state ps21.dims0 ps21.vars1' . 

  interpret ps2:partial_state2 "list_dims (?var_d \<union> ?var_d2)" ?var_d ?var_d2
    apply standard
    apply (simp add: qvars_empty)
    apply (simp add: list_dims_def)
    using list_dims_def apply blast
    apply (simp add: QStateM_vars.rep_eq QState_rel2')
    using ps21.finite_v2  by (auto simp add: qvars_empty list_dims_def QStateM_vars.rep_eq QState_rel3' )
  interpret ps:partial_state ps2.dims0 ps2.vars1' .  

  interpret ps22:partial_state2 "list_dims (?sep_vars \<union> ?var_r)" "?sep_vars" "?var_r"
    apply standard
    apply (auto simp: list_dims_def)
    using finite_subset ps2.finite_v1 q_vars_in_Q_vars apply blast
    using ps21.finite_v1 by blast
  interpret ps2a: partial_state ps22.dims0 ps2.vars1' .
  thm  ps2.ptensor_mat_mult_vec
  have QStateM_vector[simp]:"QStateM_vector (Q1 + Q2) = ps2.ptensor_vec (QStateM_vector Q1) (QStateM_vector Q2)"
    by (simp add: QStateM_list_plus a0 vec_list vec_of_list_QStateM_list)
  
  have "ptensor_vec ?var_d  ?var_d2 ?mat_sep_v (1\<^sub>m (2^(card ?var_d2)) *\<^sub>v QStateM_vector Q2) =
        ptensor_mat ?var_d  ?var_d2
                     (ptensor_mat ?sep_vars ?var_r (M::complex mat) (1\<^sub>m (2^(card ?var_r))))
                     (1\<^sub>m (2^(card ?var_d2))) *\<^sub>v ps2.ptensor_vec (QStateM_vector Q1) (QStateM_vector Q2)"
    apply (rule ps2.ptensor_mat_mult_vec[of ?ptensor_mat "QStateM_vector Q1" "1\<^sub>m (2^(card ?var_d2))" "QStateM_vector Q2"])
    using QStateM_vars_eq_q_U_r ps2.d1_def ps2.dims1_def ps22.d0_def ps22.dims0_def ps22.vars0_def apply auto
      apply (metis (full_types) QStateM_vars.rep_eq 
           QStateM_vector.rep_eq QState_list.rep_eq QState_rel1' 
           QState_vector.rep_eq carrier_vec_def 
           dim_vec_of_list mem_Collect_eq)
    apply (simp add: ps21.d2_def ps21.dims2_def)
    by (metis (mono_tags) QStateM_vars.rep_eq QStateM_vector.rep_eq 
         QState_list.rep_eq QState_rel1' QState_vector.rep_eq 
         carrier_vec_def dim_vec_of_list 
         mem_Collect_eq prod_list_replicate ps21.d2_def ps21.dims2_def)
  also have "\<dots> = ptensor_mat ?sep_vars ?var_r'
                     (M::complex mat) 
                 (ptensor_mat ?var_r ?var_d2
                  (1\<^sub>m (2^(card ?var_r))) (1\<^sub>m (2^(card ?var_d2))))*\<^sub>v  ps2.ptensor_vec (QStateM_vector Q1) (QStateM_vector Q2)"
    apply auto
    by (metis QStateM_vars_eq_q_U_r QVars_Q1_Q2 ps21.finite_v2 ps22.disjoint ps22.finite_v1 
              ps22.finite_v2 ptensor_mat_assoc q_vars_map_q1q2_eq_map_q1 
              qvars_empty var_r'_eq_union_r_d2) 
  also have "\<dots> = ptensor_mat ?sep_vars ?var_r'
                     (M::complex mat) (1\<^sub>m (2^(card ?var_r'))) *\<^sub>v  ps2.ptensor_vec (QStateM_vector Q1) (QStateM_vector Q2)"
    by (metis ps21.disjoint ps21.finite_v2 ps22.finite_v2 tensor_product_1m var_r'_eq_union_r_d2)          
  finally have "?vec_mat_sep_plus_q2 = 
                 ?vec_mat_sep_q1_plus_q2" 
    using carrier_dim_vec
    by (metis QStateM_list_dim QStateM_vector one_mult_mat_vec 
              q_vars_map_q1q2_eq_map_q1 vec_of_list_QStateM_list)
  moreover have "QStateM_map (matrix_sep_QStateM q Q1 M + Q2) = QStateM_map Q1 + QStateM_map Q2"
    using QStateM_map_Q1 QStateM_map_plus QStateM_vars.rep_eq 
          QStateM_vars_Q1 a0 disj_QState_def qstate_def 
            sep_disj_QState sep_disj_QStateM by auto
  then have " QStateM_map Q1 + QStateM_map Q2 = QStateM_map (matrix_sep_QStateM q (Q1 + Q2) M)" and
            "QStateM_map (matrix_sep_QStateM q (Q1 + Q2) M) = QStateM_map (matrix_sep_QStateM q Q1 M + Q2)"       
    by (auto simp add: QStateM_map_Q12 QStateM_map_plus a0)             
  ultimately show ?thesis
    apply -  
    by (auto simp add: QStateM_list_Q12 QStateM_list_Q1 QStateM_list_Q1_plus_Q2)
qed



lemma 
  QStateM_map_plus_int:
  assumes a0:"Q1##Q2" and a1:"\<forall>e \<in> (i \<sigma>). QStateM_map Q1 e \<noteq> {}"
  shows "\<forall>e \<in> (i \<sigma>). QStateM_map (Q1 + Q2) e \<noteq> {}"
proof-  
  have "QStateM_map (Q1 + Q2) = QStateM_map Q1 + QStateM_map Q2"
    using QStateM_map_plus[OF a0] by auto
  moreover have "QStateM_map Q1 + QStateM_map Q2 = 
                 QStateM_map Q2 + QStateM_map Q1"
    using  sep_add_commute QStateM_disj_dest(1)[OF a0]  by auto
  ultimately show ?thesis using  a1   
    unfolding Sep_Prod_Instance.none_def  plus_fun_def
    by auto        
qed

lemma Q_upd_Q1_dom_sep_Q2_dom:
  assumes 
   a0:"Q1##Q2" and 
   a3:"unitary M" and 
   a4: "M \<in> carrier_mat (2^(card ( \<Union> (QStateM_map Q1 ` q)))) (2^(card (\<Union> (QStateM_map Q1 ` q))))"
 shows "(matrix_sep_QStateM q Q1 M) ## Q2"
proof-
   let ?sep_vars = "Q_domain_var q (QStateM_map Q1)" and
      ?var_d = "QStateM_vars Q1" 
  let ?var_r = "?var_d - ?sep_vars"

  let ?sep_vars' = "Q_domain_var q (QStateM_map (Q1 + Q2))" and
      ?var_d' = "QStateM_vars (Q1 + Q2)" 
  let ?var_r' = "?var_d' - ?sep_vars'"
  let ?mat_sep_v = "ptensor_mat ?sep_vars ?var_r
                               (M::complex mat) (1\<^sub>m (2^(card ?var_r))) *\<^sub>v 
                      QStateM_vector Q1"
  let ?vec_mat_sep_plus_q2 = "partial_state2.ptensor_vec 
                       (QStateM_vars Q1) (QStateM_vars Q2) ?mat_sep_v (QStateM_vector Q2)"
  let ?vec_mat_sep_q1_plus_q2 = "ptensor_mat ?sep_vars' ?var_r'
                                   (M::complex mat) (1\<^sub>m (2^(card ?var_r'))) *\<^sub>v 
                                   QStateM_vector  (Q1 + Q2)"

  have 
    QStateM_map_Q1:"QStateM_map (matrix_sep_QStateM q Q1 M) = QStateM_map Q1" and 
    QStateM_vars_Q1:"QStateM_vars (matrix_sep_QStateM q Q1 M) = QStateM_vars Q1" and
    QStateM_list_Q1:"QStateM_list (matrix_sep_QStateM q Q1 M) = 
         list_of_vec (ptensor_mat ?sep_vars ?var_r
                               (M::complex mat) (1\<^sub>m (2^(card ?var_r))) *\<^sub>v 
                      QStateM_vector Q1)"
    using matrix_sep_dest a3
    using a4 apply blast
    using a3 a4 matrix_sep_dest apply blast
    using Q_domain_var_def a3 a4 matrix_sep_def matrix_sep_dest by force
  thus ?thesis
    by (metis QStateM_rel1 a0 disj_QState_def sep_disj_QState sep_disj_QStateM)
qed

lemma not_fault_while:
  "\<not> \<turnstile>\<langle>While b c,Normal ( \<rho>1, \<sigma>, Q1)\<rangle> \<Rightarrow> Fault \<Longrightarrow> \<sigma> \<in> b \<Longrightarrow>
         \<not> \<turnstile>\<langle>c,Normal ( \<rho>1, \<sigma>, Q1)\<rangle> \<Rightarrow> Fault"
  using QExec.Fault_Prop QExec.WhileTrue by force

lemma step_not_to_fault:assumes a0:"\<not> \<turnstile> \<langle>While b c,Normal (p,s,q)\<rangle> \<Rightarrow> Fault" and
              a1:"\<turnstile> \<langle>c,Normal (p,s,q)\<rangle> \<Rightarrow> Normal s'" and a2:"s\<in>b"
            shows "\<not> \<turnstile> \<langle>While b c,Normal s'\<rangle> \<Rightarrow> Fault"
proof-
  { assume "\<turnstile> \<langle>While b c,Normal s'\<rangle> \<Rightarrow> Fault"
    then have "\<turnstile> \<langle>While b c,Normal (p,s,q)\<rangle> \<Rightarrow> Fault"
      using QExec.WhileTrue[OF a2 a1] by auto
    then have False using a0 by auto
  } thus ?thesis by auto
qed

lemma dom_q_vars_Q_Q1:
  assumes a0:"q' \<notin> dom_q_vars (QStateM_map (Q1 + Q2))" and
          a1:"Q1 ## Q2"
  shows "q' \<notin> dom_q_vars (QStateM_map Q1)"
    using a0 a1
    unfolding dom_q_vars_def    
    by (cases "QStateM_map Q2 q' = {}", 
      auto simp add: QStateM_map_plus plus_fun_def) 

lemma disj_QStateM_sep_Q_domain:"Q1 ## Q2 \<Longrightarrow> 
       Q_domain (QStateM_map Q1) \<inter> Q_domain (QStateM_map Q2) = {}"
  by (simp add: QStateM_rel1 disj_QState_def sep_disj_QState sep_disj_QStateM)

lemma union_Q_domain:
  "Q1 ## Q2 \<Longrightarrow> 
    Q_domain (QStateM_map (Q1 + Q2)) = 
    Q_domain (QStateM_map Q1) \<union> Q_domain (QStateM_map Q2)"
  apply (subst QStateM_map_plus, simp)  
  by (simp add: QStateM_rel1 QState_vars_plus 
     disjoint_x_y_wf1_x_plus_y plus_set_def sep_disj_QStateM)
  
lemma new_q_addr_Q_Q1:
  assumes a0:"q'_addr \<in> new_q_addr v \<sigma> (QStateM_map (Q1 + Q2))" and
          a1:"Q1 ## Q2"                        
        shows "q'_addr \<in> new_q_addr v \<sigma> (QStateM_map Q1)"
proof-
  have "QStateM_map (Q1 + Q2) = QStateM_map Q1 + QStateM_map Q2"
    by (simp add: QStateM_map_plus local.a1)  
  moreover have "finite q'_addr \<and>
         2 ^ card q'_addr = length (v \<sigma>) \<and>
         Q_domain (QStateM_map (Q1 + Q2)) \<inter> q'_addr ={}"
    using a0 unfolding new_q_addr_def by auto
  moreover have "Q_domain (QStateM_map Q1) \<inter> q'_addr ={} "
    using calculation
    using local.a1 union_Q_domain by fastforce    
  ultimately show ?thesis unfolding new_q_addr_def by auto
qed



lemma vars_map_int:
    assumes 
      a0:"\<forall>e\<in>vs. QStateM_map Q1' e \<noteq> {}"   and        
      a1:"Q1' ## (Q1'' + Q2)" and
      a2:"Q1'' ## Q2"
    shows "\<forall>e\<in>vs. QStateM_map Q2 e = {}"  
proof-
  have "QStateM_map Q1' ## QStateM_map (Q1'' + Q2)"
    using a1 sep_disj_QStateM by force
  moreover have "\<forall>e\<in>vs. QStateM_map (Q1'' + Q2) e = {}"
  proof -
  { fix nn :: nat
    have "{n. QStateM_map Q1' n \<noteq> none} \<inter> {n. QStateM_map (Q1'' + Q2) n \<noteq> none} = {}"
      by (metis \<open>QStateM_map Q1' ## QStateM_map (Q1'' + Q2)\<close> opt_class.domain_def sep_disj_fun_def)
  then have "nn \<notin> vs \<or> QStateM_map (Q1'' + Q2) nn = {}"
    using a0 by fastforce }
    then show ?thesis
      by blast
  qed
  ultimately show ?thesis using a2
    by (metis QStateM_map_plus Sep_Prod_Instance.none_def plus_fun_def)  
qed


lemma same_qstate_map:
  assumes 
     a0':"Q1 + (Q2 + Q3) = Q1' + Q2'" and a0'':"Q1 ## (Q2 + Q3)" and a0''':"Q1' ## Q2'" and
     a0:"Q_domain_var vs (QStateM_map Q1) \<noteq> {}" and
     a1:"QStateM_vars Q1 = Q_domain_var vs (QStateM_map Q1)" and
     a2:"\<forall>e\<in> vs. QStateM_map Q1 e \<noteq> {}" and
     a3:"Q_domain_var vs (QStateM_map Q1') \<noteq> {}" and
     a4:"QStateM_vars Q1' = Q_domain_var vs (QStateM_map Q1')" and
     a5:"\<forall>e\<in> vs. QStateM_map Q1' e \<noteq> {}" 
   shows "QStateM_map Q1 = QStateM_map Q1'"
proof-
  have a0':"QStateM_map (Q1 + (Q2 + Q3)) = QStateM_map (Q1' + Q2')"
    using a0' by auto
  have q1:"QStateM_map (Q1 + (Q2 + Q3)) = QStateM_map Q1 + QStateM_map (Q2 + Q3)" and
       q1':"QStateM_map (Q1' + Q2') = QStateM_map Q1' + QStateM_map Q2'"
    using QStateM_map_plus a0'' a0''' a0
    by auto  
  have not_xs_q1:"\<forall>x. x\<notin>vs \<longrightarrow>  (QStateM_map Q1) x = {}"
    apply auto
    by (metis (no_types) QStateM_rel1 QStateM_vars.rep_eq Un_empty_right 
          empty_iff local.a1 q_var_in_q_qr qstate_def)
  have "\<forall>x. x \<in> vs \<longrightarrow> (QStateM_map (Q2 + Q3)) x = {}"
    apply auto
    by (smt (z3) IntI Sep_Prod_Instance.none_def a0'' equals0D local.a2 
            mem_Collect_eq opt_class.domain_def sep_disj_QStateM sep_disj_fun_def)    
  then have xs_q1:"\<forall>x. x \<in> vs \<longrightarrow> (QStateM_map Q1) x = (QStateM_map (Q1 + (Q2 + Q3))) x"
    by (auto simp add:plus_fun_def q1)

  have not_xs_q1':"\<forall>x. x\<notin>vs \<longrightarrow>  (QStateM_map Q1') x = {}"
    apply auto 
    by (metis (no_types) QStateM_rel1 QStateM_vars.rep_eq Un_empty_right empty_iff local.a4 q_var_in_q_qr qstate_def)
  have "\<forall>x. x \<in> vs \<longrightarrow> (QStateM_map Q2') x = {}"
    apply auto
    by (smt (z3) IntI Sep_Prod_Instance.none_def a0''' equals0D local.a5
            mem_Collect_eq opt_class.domain_def sep_disj_QStateM sep_disj_fun_def)
  then have xs_q1':"\<forall>x. x \<in> vs \<longrightarrow> (QStateM_map Q1') x = (QStateM_map (Q1' + Q2')) x"
    by (auto simp add:plus_fun_def q1')
  { fix  x 
    { assume "x \<notin> vs"
      then have "(QStateM_map Q1) x  = (QStateM_map Q1') x"
        using not_xs_q1 not_xs_q1' by presburger
    }
    moreover { assume "x \<in> vs"
      then have "(QStateM_map Q1) x  = (QStateM_map Q1') x"
        using a0' xs_q1 xs_q1' by auto
    }
    ultimately have "QStateM_map Q1 x = QStateM_map Q1' x"
      by auto
  }
  thus ?thesis by auto
qed
          

lemma same_qstate_map':
  assumes a0:"Q1 + (Q2 + Q3) = Q1' + Q2'" and 
              a1:"Q1 ## (Q2 + Q3)" and a2:"Q1' ## Q2'" and
              a3:"QStateM_map Q1 = QStateM_map Q1'"
  shows "QStateM_map (Q2 + Q3) = QStateM_map Q2'"
  using a0 a1 a2 a3
proof-
   have a0':"QStateM_map (Q1 + (Q2 + Q3)) = QStateM_map (Q1' + Q2')"
    using a0 by auto
  have q1:"QStateM_map (Q1 + (Q2 + Q3)) = QStateM_map Q1 + QStateM_map (Q2 + Q3)" and
       q1':"QStateM_map (Q1' + Q2') = QStateM_map Q1' + QStateM_map Q2'"
    using QStateM_map_plus a1 a2 a0'
    by auto
  { fix x
    { assume "x \<notin> domain (QStateM_map (Q2 + Q3))"
      moreover have "x\<notin>domain (QStateM_map Q2')" using calculation
        by (smt (z3) QStateM_disj_dest(1) QStateM_map_plus a0 a3 disjoint_iff 
        local.a2 mem_Collect_eq opt_class.domain_def plus_fun_def q1 sep_disj_fun_def)
      ultimately have "QStateM_map (Q2 + Q3) x = QStateM_map Q2' x"
        by (simp add: opt_class.domain_def)        
    }
    moreover {
      assume "x \<in> domain (QStateM_map (Q2 + Q3))"
      moreover have "x \<in> domain (QStateM_map Q2')" using calculation       
        by (smt (verit, best) QStateM_disj_dest(1) a0 a3 disjoint_iff 
             local.a1 mem_Collect_eq 
             opt_class.domain_def plus_fun_def q1 q1' sep_disj_fun_def)
      ultimately have "QStateM_map (Q2 + Q3) x = QStateM_map Q2' x"        
        by (metis (mono_tags) a0 mem_Collect_eq opt_class.domain_def 
             plus_fun_def q1 q1')
    }
    ultimately have "QStateM_map (Q2 + Q3) x = QStateM_map Q2' x"  
      by auto
  } thus ?thesis by auto
qed

lemma idem_sca_mult_qstate_1:"1 \<cdot>\<^sub>q Q = Q"
  unfolding sca_mult_qstatem_def sca_mult_qstate_def apply auto
  by (metis QState_list.rep_eq QState_refl QState_vector.rep_eq list_vec)


lemma idem_sca_mult_qstatem_1:"1 \<cdot>\<^sub>Q Q = Q"
  unfolding sca_mult_qstatem_def using idem_sca_mult_qstate_1
  using idem_QState by presburger


lemma QStateM_map_0_QStateM_vars_0':
  assumes a0:"QStateM_map Q = 0" 
  shows "QStateM_vars Q = {}"
  using a0 range_0_none  
  apply transfer  
  by(auto simp add: Q_domain_def) 

lemma QStateM_map_0_QStateM_vars_0'':
  assumes a0:"QStateM_vars Q = {}" 
  shows "QStateM_map Q = 0"
  using a0  
  apply transfer
  unfolding Q_domain_def zero_fun_def by fastforce  

lemma QStateM_map_0_QStateM_vars_0:
  shows "QStateM_vars Q = {} = (QStateM_map Q = 0)"
  using QStateM_map_0_QStateM_vars_0' QStateM_map_0_QStateM_vars_0''
  by auto

lemma QStateM_zero_QStateM_vars_plus_empty:
  assumes a0:"QStateM_map Q1 = 0" and a1:"QStateM_map Q2 = 0"
  shows "QStateM_vars (Q1 + Q2) = {}"
proof-
  have "QStateM_map Q1  ## QStateM_map Q2" 
    using a0 a1 by auto
  moreover have "QStateM_vars Q1 = {}" and "QStateM_vars Q2 = {}"
    using a0 a1 QStateM_map_0_QStateM_vars_0 by auto
  then show ?thesis
    using QStateM_map_0_QStateM_vars_0' QStateM_map_plus 
          QStateM_vars.rep_eq a0 a1 disj_QState_def qstate_def 
          sep_disj_QState sep_disj_QStateM by auto
qed


lemma measure_prob_q_in_tensor_Q1_plus_Q2_eq_measure_prob_Q1:
   assumes  a0':"Q1 ## Q2" and
            a1:"k < 2 ^ card (\<Union> (QStateM_map Q1 ` q))" and 
            a2: "0< fst (measure_vars k q (Q1 + Q2))" and a3:"\<forall>e\<in>q. QStateM_map Q1 e \<noteq> {}"
          shows "fst (measure_vars k q (Q1 + Q2)) = fst (measure_vars k q Q1)" and 
                "snd (measure_vars k q (Q1 + Q2)) =  snd (measure_vars k q Q1) + Q2"
proof-
  let ?sep_vars = " \<Union>((QStateM_map (Q1+Q2)) ` q)" 
  let ?sep_vars' = " \<Union>((QStateM_map Q1) ` q)" 
  let ?Q' =  "matrix_sep q (Q1+Q2) (1\<^sub>k (2^(card ?sep_vars)))"
  let ?Q1' = "matrix_sep q Q1 (1\<^sub>k (2^(card ?sep_vars)))"
  let ?\<delta>kQ = "Re ((vec_norm ?Q')^2)"
  let ?\<delta>kQ1 = "Re ((vec_norm ?Q1')^2)"
  let ?QF' = "1/sqrt ?\<delta>kQ \<cdot>\<^sub>v ?Q'"
  let ?Q1F' = "1/sqrt ?\<delta>kQ1 \<cdot>\<^sub>v ?Q1'"
  let ?M = "1\<^sub>k (2^(card ?sep_vars))"

  have eq_sep_vars:"?sep_vars = ?sep_vars'"
    using Q_domain_var_def a0' a3 eq_domain_var_plus by presburger

  have eq_matrix_sep:"matrix_sep q (Q1+Q2) ?M = ptensor_vec (QStateM_vars Q1) (QStateM_vars Q2) (matrix_sep q Q1 ?M) (QStateM_vector Q2)"
    
    by (smt (verit) QStateM_list_plus Q_domain_var_def Q_domain_var_in_vars a0' a3 
           eq_sep_vars matrix_sep_def matrix_sep_tensor_product_1 vec_list vec_of_list_QStateM_list)
    
  then have eq_\<delta>1:"?\<delta>kQ = ?\<delta>kQ1"
    by (smt (verit, ccfv_threshold) QStateM_disj_dest(2) QStateM_list_dim 
            QStateM_vector.rep_eq QState_rel3' QState_wf QState_wf_def 
            \<open>\<Union> (QStateM_map (Q1 + Q2) ` q) = \<Union> (QStateM_map Q1 ` q)\<close> 
             a0' disj_QState_def eq_QStateM_vars mat_carrier 
            matrix_sep_eq_len mult.right_neutral prod.sel(1) 
            prod.sel(2) projection1_def sep_disj_QState tensor_norm vec_of_list_QStateM_list)
  then show eq_\<delta>:"fst (measure_vars k q (Q1 + Q2)) = fst (measure_vars k q Q1)"
    by (metis \<open>\<Union> (QStateM_map (Q1 + Q2) ` q) = \<Union> (QStateM_map Q1 ` q)\<close> fst_conv measure_vars_dest) 
  
  show "snd (measure_vars k q (Q1 + Q2)) =  snd (measure_vars k q Q1) + Q2"
    by (smt (verit, ccfv_threshold) QStateM_disj_dest(2) QStateM_list.rep_eq QStateM_list_dim 
        QStateM_map_plus QStateM_map_qstate QStateM_rel1 QStateM_vars.rep_eq 
         QStateM_vector.rep_eq QState_plus_intro QState_qstate_eq QState_rel2' 
         QState_vars_plus QState_wf Q_domain_var_def \<delta>k a0' a2 disj_QStateM_sep_Q_domain eq_\<delta>1 
         eq_matrix_sep eq_sep_vars idem_QState mat_carrier matrix_sep_eq_len measure_vars_dest_QStateM 
        plus_QStateM prod.collapse projection1_def pscalar_ptensor_1 qstate_def vec_of_list_QStateM_list)
qed

lemma measure_prob_q_in_tensor_Q1_eq_measure_prob_Q1:
   assumes a0: "(\<delta>k, \<Q>') = measure_vars k q (Q1 + Q2)" and a0':"Q1 ## Q2" and
              a1:"k < 2 ^ card (\<Union> (QStateM_map Q1 ` q))" and
              a2: "0<\<delta>k" and a3:"\<forall>e\<in>q. QStateM_map Q1 e \<noteq> {}" 
            shows "fst (measure_vars k q Q1) = \<delta>k"
  by (metis a0 a0' a1 a2 a3 fst_conv measure_prob_q_in_tensor_Q1_plus_Q2_eq_measure_prob_Q1(1))

lemma measure_vector_q_in_tensor_Q1_eq_tensor_measure_vector_q_in_Q1_Q2:
  assumes a0: "(\<delta>k, \<Q>') = measure_vars k q (Q1+Q2)" and  a0':"Q1 ## Q2" and
              a1:"k < 2 ^ card (\<Union> (QStateM_map Q1 ` q))" and
              a2: "0<\<delta>k" and a3:"\<forall>e\<in>q. QStateM_map Q1 e \<noteq> {}" 
            shows "\<exists>\<Q>1'. (\<delta>k, \<Q>1') =  measure_vars k q Q1 \<and> \<Q>' = \<Q>1' + Q2 \<and> \<Q>1' ## Q2"
 
proof-
  let ?sep_vars = "\<Union> (QStateM_map Q1 ` q)"
  let ?sep_vars' = "\<Union> (QStateM_map (Q1 + Q2) ` q)"
  let ?\<delta>k = "Re ((vec_norm (matrix_sep q Q1 1\<^sub>k (2 ^ card ?sep_vars)))\<^sup>2)"
  let ?Q' = "matrix_sep q Q1 1\<^sub>k (2 ^ card ?sep_vars)"

  have "\<Union> (QStateM_map Q1 ` q) = \<Union> (QStateM_map (Q1 + Q2) ` q)"
    using Q_domain_var_def a0' a3 eq_domain_var_plus by presburger

  have zero_less_delta:"0 < fst (measure_vars k q (Q1 + Q2))" using a0 a2
    by (metis fst_conv)
  have dest_measure_vars:"measure_vars k q Q1 =
        (?\<delta>k, QStateM (QStateM_map Q1, 
                        QState (QStateM_vars Q1, 
                                 list_of_vec (complex_of_real (1 / sqrt ?\<delta>k) \<cdot>\<^sub>v ?Q'))))"
    using measure_vars_dest by blast
  have "fst (measure_vars k q Q1) = \<delta>k" 
    using measure_prob_q_in_tensor_Q1_eq_measure_prob_Q1[OF a0 a0' a1 a2 a3] by auto
   
  moreover have "fst (measure_vars k q (Q1+Q2)) = \<delta>k" and 
             "snd (measure_vars k q (Q1 + Q2)) =  snd (measure_vars k q Q1) + Q2"
    using measure_prob_q_in_tensor_Q1_plus_Q2_eq_measure_prob_Q1[OF a0' a1 zero_less_delta a3] calculation 
    by auto
  ultimately show ?thesis
    by (metis QStateM_rel1 a0 a0' a2 disj_QState_def measure_vars_QStateM_map prod.collapse sep_disj_QState sep_disj_QStateM snd_conv)
qed 


lemma Frame_execution:
  assumes           
    a0:"\<turnstile> \<langle>c,Normal (\<delta>1*\<delta>2,\<sigma>,Q1+Q2)\<rangle> \<Rightarrow> Normal (\<delta>',\<sigma>',Q')" and 
    a1:"Q1##Q2"
  shows "(\<exists>\<delta>1' Q1'. \<turnstile> \<langle>c,Normal (\<delta>1,\<sigma>,Q1)\<rangle> \<Rightarrow> Normal (\<delta>1',\<sigma>',Q1') \<and>
                    \<delta>' = \<delta>1'*\<delta>2 \<and> Q' = Q1'+Q2  \<and> Q1'##Q2) \<or> \<turnstile> \<langle>c,Normal (\<delta>1,\<sigma>,Q1)\<rangle> \<Rightarrow> Fault"  
  using a0 a1
proof(induct c arbitrary: \<delta>1 \<sigma> Q1 \<delta>' \<sigma>' Q' \<delta>2 Q2)
  case Skip  
  then show ?case using QExec.Skip Skip
    by (fast intro: QExec_Normal_elim_cases(2))    
next
  case (SMod f)   
  then have "\<turnstile> \<langle>SMod f,Normal (\<delta>1,\<sigma>,Q1)\<rangle> \<Rightarrow>  Normal (\<delta>1, f \<sigma>, Q1)"
    using QExec.StackMod by auto
  moreover have "\<delta>' = \<delta>1*\<delta>2 \<and> \<sigma>' =  f \<sigma> \<and> Q' = Q1 + Q2"
    by (auto intro: QExec_Normal_elim_cases(3)[OF SMod(1)] )    
  ultimately show ?case using SMod(2) by auto
next
  case (QMod M q)   
  obtain m where  a00:"\<delta>' = \<delta>1*\<delta>2" and a01:"\<sigma> = \<sigma>'" and a02:"Q' = matrix_sep_QStateM (q \<sigma>) (Q1 + Q2) M" and
            a03:"\<forall>e \<in> q \<sigma>. (QStateM_map (Q1 + Q2) e) \<noteq> {}" and 
            a05:"unitary M" and 
            a06:"M \<in> carrier_mat m m"
    by (auto intro: QExec_Normal_elim_cases(4)[OF QMod(1)])
  { assume e:"\<forall>e \<in> q \<sigma>. (QStateM_map Q1 e) \<noteq> {}"
    moreover have step:"\<turnstile> \<langle>QMod M q,Normal (\<delta>1, \<sigma>, Q1)\<rangle> \<Rightarrow> Normal (\<delta>1, \<sigma>, matrix_sep_QStateM (q \<sigma>) Q1 M)"
      using QExec.QMod a05 a06 calculation by blast 
    ultimately have ?case
    proof-
      { assume a000:"m = 2^(card ( \<Union> (QStateM_map Q1 ` (q \<sigma>))))"  
        then have ?case using Q_upd_Q1_dom_sep_Q2_dom[OF QMod(2) a05 a06[simplified a000]] 
             step mat_sep_G[OF QMod.prems(2) e a05 a06[simplified a000]] 
             a0 step a00 a01 a02 a03 a05 a06
           by blast
      }
      moreover { 
        assume "m \<noteq> 2^(card ( \<Union> (QStateM_map Q1 ` (q \<sigma>))))"  
        moreover have "\<turnstile> \<langle>QMod M q,Normal (\<delta>1, \<sigma>, Q1)\<rangle> \<Rightarrow> Normal (\<delta>1, \<sigma>, Q1)" 
          using step dest_var_a_2 calculation
          by (metis a06 carrier_matD(1) idem_QState1 list_of_vec_QStateM_vec)
        ultimately have ?case using a00 a01 a02 a03 a05 a06
          by (metis QMod.prems(2) Q_domain_var_def carrier_matD(1) dest_var_a_2 e 
                  idem_QState1 list_of_vec_QStateM_vec vars.eq_domain_var_plus vars_axioms)
      } 
      ultimately show ?case by auto
    qed
  }
  moreover { 
    assume e:"\<not> (\<forall>e \<in> q \<sigma>. (QStateM_map Q1 e) \<noteq> {})"
    then have ?case
      by (meson QExec.QMod_F) 
  }
  ultimately show ?case by auto
next
  case (IF b c1 c2) thm IF(3)
  then show ?case using QExec.CondTrue QExec.CondFalse
    apply-
    apply (rule QExec_Normal_elim_cases(7)[OF IF(3) _ ], auto)
    by metis+  
next
  case (While b c)
  { assume "\<sigma> \<notin> b" then have ?case using QExec.WhileFalse While(3) While.prems(1)
      apply -
      apply(rule QExec_Normal_elim_cases(6)[OF While(2)], auto) 
      by metis
  }
  moreover {
    assume a00:"\<sigma> \<in> b"     
    {  fix d::"('v,'s) com" fix s s'
       assume exec: "\<turnstile>\<langle>d,s\<rangle> \<Rightarrow> s'"
       assume d: "d=While b c" and s:"s = Normal (\<delta>1 * \<delta>2, \<sigma>, Q1 + Q2)" and 
              s':"s' = Normal (\<delta>', \<sigma>', Q')" and 
              not_fault:"\<not> \<turnstile> \<langle>QSyntax.com.While b c,Normal (\<delta>1, \<sigma>, Q1)\<rangle> \<Rightarrow> Fault"
       from exec d s s' a00 not_fault
       have "\<lbrakk>Q1 ## Q2\<rbrakk> \<Longrightarrow>  
             \<exists>\<delta>1' Q1' . \<turnstile> \<langle>While b c,Normal (\<delta>1,\<sigma>,Q1)\<rangle> \<Rightarrow> Normal (\<delta>1',\<sigma>',Q1') \<and>
                    \<delta>' = \<delta>1'*\<delta>2 \<and> Q' = Q1'+Q2  \<and> Q1'##Q2 "
       proof (induct arbitrary: \<delta>1 \<sigma> Q1 \<delta>2 Q2)              
         case  (WhileTrue \<sigma>a ba ca \<rho>a Q1a sa' s1'')          
         then have b:"ba = b" and c:"ca = c" and "\<rho>a = \<delta>1 * \<delta>2" and 
                   \<sigma>:"\<sigma>a = \<sigma>" and Q1:"Q1 + Q2 = Q1a" by auto
         moreover obtain sa\<delta> sa_\<sigma> sa_Q where sa':"sa' = Normal (sa\<delta>,sa_\<sigma>,sa_Q)" 
           using s' WhileTrue(4,9)
           by (metis XQState.exhaust exec_Fault_end prod_cases3)
         moreover 
         have step:"\<turnstile>\<langle>c,Normal ( \<delta>1 * \<delta>2, \<sigma>, Q1 + Q2)\<rangle> \<Rightarrow> Normal (sa\<delta>,sa_\<sigma>,sa_Q)" and
              sa1:"\<turnstile>\<langle>While b c,sa'\<rangle> \<Rightarrow>  s1''"
           using calculation WhileTrue.hyps(2) WhileTrue.hyps(4) 
                   WhileTrue.prems(2) WhileTrue.prems(3) by auto
         obtain \<delta>1' Q1' where 
            step_i:"\<turnstile>\<langle>c,Normal ( \<delta>1, \<sigma>, Q1)\<rangle> \<Rightarrow> Normal (\<delta>1',sa_\<sigma>,Q1')" and
            sap:"sa\<delta> = \<delta>1'*\<delta>2" and saq:"sa_Q = Q1' + Q2" and dis_q1':"Q1' ## Q2" thm While(1)
           using While.hyps WhileTrue.prems(1) WhileTrue.prems(5) 
                 WhileTrue.prems(6) local.step not_fault_while by blast  
         thm While(1)
         { assume a00:"sa_\<sigma> \<in> b" 
           have "\<not> \<turnstile> \<langle>While b c,Normal (\<delta>1',sa_\<sigma>,Q1')\<rangle> \<Rightarrow> Fault"
             using step_not_to_fault[OF  WhileTrue(11) step_i WhileTrue(10)]  by auto
           then have ?case 
             using WhileTrue(5)[simplified b c, OF dis_q1' _  sa'[simplified sap saq] WhileTrue(9) a00]                           
             using QExec.WhileTrue[OF  WhileTrue.prems(5) step_i]
             by auto             
         }
         moreover { assume a00:"sa_\<sigma> \<notin> b"
           then have "sa' = s1''" using sa1 sa' 
             using QExec_Normal_elim_cases(6)[OF sa1[simplified sa']] by fastforce
           then have ?case
             using QExec.WhileTrue[OF WhileTrue.prems(5) step_i] WhileTrue.prems(4) 
                   dis_q1' sa' sap saq QExec.WhileFalse[OF a00, of c \<delta>1' Q1'] 
             by fastforce
         } ultimately show ?case by auto
         qed(auto)
     } with While have ?case by auto
   } ultimately show ?case by auto    
next
  case (Seq c1 c2)  
  then obtain \<delta>'' \<sigma>'' Q'' where
  step_c1_comp:"\<turnstile> \<langle>c1, Normal (\<delta>1 * \<delta>2, \<sigma>, Q1 + Q2)\<rangle> \<Rightarrow> Normal (\<delta>'', \<sigma>'', Q'')" and 
  step_c2_comp:"\<turnstile> \<langle>c2, Normal (\<delta>'', \<sigma>'', Q'')\<rangle> \<Rightarrow> Normal (\<delta>', \<sigma>', Q')"    
    using seq_normal[OF Seq(3)] by auto
  { assume a00:"\<not> \<turnstile> \<langle>c1,Normal (\<delta>1, \<sigma>, Q1)\<rangle> \<Rightarrow> Fault"
  
    then obtain \<delta>1'' Q1'' where 
      step_c1:"\<turnstile> \<langle>c1,Normal (\<delta>1, \<sigma>, Q1)\<rangle> \<Rightarrow> Normal (\<delta>1'', \<sigma>'', Q1'')" and
      eq_\<rho>'':"\<delta>'' = \<delta>1''*\<delta>2" and eq_Q'':"Q'' = Q1'' + Q2" and disj_Q1''_Q2:"Q1''##Q2"
      using Seq(1)[OF step_c1_comp Seq(4)] by auto 
    { assume a000:"\<not> \<turnstile> \<langle>c2,Normal (\<delta>1'', \<sigma>'', Q1'')\<rangle> \<Rightarrow> Fault"
      then have ?case 
        using step_c1 a00 Seq(2)[OF step_c2_comp[simplified eq_\<rho>'' eq_Q''] disj_Q1''_Q2] QExec.Seq
        by blast 
    }
    moreover { assume a000:"\<turnstile> \<langle>c2,Normal (\<delta>1'', \<sigma>'', Q1'')\<rangle> \<Rightarrow> Fault"
      then have ?case
        using QExec.Seq step_c1 by blast
    }
    ultimately have ?case by auto
  }
  moreover { 
    assume a00:"\<turnstile> \<langle>c1,Normal (\<delta>1, \<sigma>, Q1)\<rangle> \<Rightarrow> Fault"
    then have ?case
      using QExec.Fault_Prop QExec.Seq by blast
  }
  ultimately show ?case by auto
next
  case (Alloc v  vec)  
  obtain q' \<Q> q'_addr \<delta> where
  eq_tuple:"(\<delta>1 * \<delta>2, \<sigma>, Q1 + Q2) = (\<delta>, \<sigma>, \<Q>)" and 
    eq_end_state:"Normal (\<delta>', \<sigma>', Q') =
     Normal
      (\<delta>, set_value \<sigma> v (from_nat q'),
       \<Q> + QStateM ({}\<^sub>q(q' := q'_addr), QState (q'_addr, vec \<sigma>)))" and 
   not_q'_in_Q:"q' \<notin> dom_q_vars (QStateM_map \<Q>)" and wf_vec:"1 < length (vec \<sigma>)" and
    q_addr_new:"q'_addr \<in> new_q_addr vec \<sigma> (QStateM_map \<Q>)" and 
    not_zero:" vec_norm (vec_of_list (vec \<sigma>)) = 1"
    by (auto intro: QExec_Normal_elim_cases(9)[OF Alloc(1)])
  moreover have not_q'_in_Q1:"q' \<notin> dom_q_vars (QStateM_map Q1)" 
    using dom_q_vars_Q_Q1 calculation Alloc(2) by fast
  moreover obtain "q'_addr \<in> new_q_addr vec \<sigma> (QStateM_map Q1)"
     using new_q_addr_Q_Q1[OF _ Alloc(2)] calculation by fastforce
  ultimately have
    "\<turnstile> \<langle>v:=alloc vec,Normal (\<delta>1, \<sigma>, Q1)\<rangle> \<Rightarrow> 
         Normal (\<delta>1, set_value \<sigma> v (from_nat q'), Q1 + QStateM((\<lambda>i. {})(q' := q'_addr), QState (q'_addr,(vec \<sigma>)) ))"
    using QExec.Alloc[of q' Q1 vec \<sigma> "(\<lambda>i. {})(q' := q'_addr)" q'_addr "set_value \<sigma> v (from_nat q')" v, OF _ wf_vec ]    by auto  
  moreover have h1:"\<Q> ## QStateM ({}\<^sub>q(q' := q'_addr), QState (q'_addr, vec \<sigma>))"
    using disjoint_allocate not_q'_in_Q q_addr_new wf_vec not_zero by fastforce
  ultimately show ?case 
    using  Alloc.prems(2)  eq_end_state eq_tuple sep_add_assoc sep_add_commute sep_add_disjD sep_add_disjI1
    apply auto   
    by (smt sep_add_assoc sep_add_commute sep_add_disjD sep_add_disjI1)            
next
  case (Dispose v expr)
  { fix Q1' Q1''
    assume 
      f0'':"Q1 = Q1' + Q1''" and
      f2':"Q1' ## Q1''" and f3':"Q_domain_var (the (var_set v expr \<sigma>)) (QStateM_map Q1') \<noteq> {}" and
      f4':"QStateM_vars Q1' = Q_domain_var (the (var_set v expr \<sigma>)) (QStateM_map Q1')" and
      f5':"\<forall>e\<in>the (var_set v expr \<sigma>). QStateM_map Q1' e \<noteq> {}"   and f6':"Zero Q1'"
    then have step_s:"\<turnstile> \<langle>Dispose v expr,Normal (\<delta>1, \<sigma>, Q1)\<rangle> \<Rightarrow> Normal (\<delta>1, \<sigma>, Q1'')"
      using QExec.Dispose by blast
    then have q1_q2:"Q1 + Q2 = Q1' + (Q1'' + Q2)" and q1_dis_q2:"Q1' ## (Q1'' + Q2)"
      using Dispose.prems(2)  sep_add_assoc sep_add_disjD
      using f0'' f2' apply blast 
      using Dispose.prems(2) f0'' f2' sep_disj_addI3 by blast 
     
    have Q1_zero:"QStateM_vector Q1' =  |0>\<^sub>(card (QStateM_vars Q1'))"
      using ZeroQ_vector_Zero_eq f6' by presburger 

    obtain Qa Qb  where 
      f0:"(\<delta>1*\<delta>2, \<sigma>, Q1 + Q2) = (\<delta>1*\<delta>2, \<sigma>,  Qa + Qb)" and
      f1:"Normal (\<delta>', \<sigma>', Q') = Normal (\<delta>1*\<delta>2, \<sigma>, Qb)" and 
      f2:"Qa ## Qb" and
      f3:"Q_domain_var (the (var_set v expr \<sigma>)) (QStateM_map Qa) \<noteq> {}" and
      f4:"QStateM_vars Qa = Q_domain_var (the (var_set v expr \<sigma>)) (QStateM_map Qa)" and
      f5:"\<forall>e\<in>the (var_set v expr \<sigma>). QStateM_map Qa e \<noteq> {}"  and f6:"Zero Qa"
        by (auto intro:QExec_Normal_elim_cases(10)[OF Dispose(1)])    
    have "Q1' = Qa"
      by (metis Q1_zero QStateM_eq_intro ZeroQ_vector_Zero_dic f0 f2 f3 f3' f4 f4' f5 f5' f6 
      list_of_vec_QStateM_vec q1_dis_q2 q1_q2 same_qstate_map snd_conv)
    moreover have q1q2eqqaqb:"Q1 + Q2 = Qa + Qb"
      using f0 by force 
    then have "Qb =  Q1'' + Q2"
      by (metis calculation f2 q1_dis_q2 q1_q2 sep_add_cancelD sep_add_commute sep_disj_commuteI)
    then have ?case
      by (metis Dispose.prems(2) XQState.inject f0'' f1  f2' 
              fst_conv prod.sel(2) sep_disj_addD sep_disj_commuteI step_s)
  }
  moreover{
    assume "\<nexists>Q1' Q1''.  Q1 = Q1' + Q1'' \<and> Q1' ## Q1'' \<and> QStateM_vars Q1' \<noteq> {} \<and> Zero Q1' \<and> 
               QStateM_vars Q1' = (Q_domain_var (the (var_set v expr \<sigma>)) (QStateM_map Q1')) \<and>
               (\<forall>e \<in> (the (var_set v expr \<sigma>)). (QStateM_map Q1') e \<noteq> {})"
    then have ?case
      using QExec.Dispose_F by presburger
  }
  ultimately show ?case
    by blast
next
  case (Measure v q) 
  obtain \<delta> \<Q> \<delta>k k \<Q>' where  
    init_tuple:"(\<delta>1 * \<delta>2, \<sigma>, Q1 + Q2) = (\<delta>, \<sigma>, \<Q>)" and
    step_tuple:"Normal (\<delta>', \<sigma>', Q') = Normal (\<delta> * \<delta>k, set_value \<sigma> v (from_nat k), \<Q>')" and
    qbits_not_empty:"\<forall>e\<in>q \<sigma>. QStateM_map \<Q> e \<noteq> {}" and
    valid_k:"k < 2 ^ card (\<Union> (QStateM_map \<Q> ` q \<sigma>))" and
    measure:"(\<delta>k, \<Q>') = measure_vars k (q \<sigma>) (Q1 + Q2)" and valid_prob:"0 < \<delta>k" and 
    sigma':"\<sigma>' = set_value \<sigma> v (from_nat k)"
    apply (rule  QExec_Normal_elim_cases(8)[OF Measure(1)])
    by fast+
  let ?addr = "\<Union>((QStateM_map Q1) ` (q \<sigma>))"
  let ?\<delta>k = "fst (measure_vars k (q \<sigma>) Q1)"
  let ?Q' = "snd (measure_vars k (q \<sigma>) Q1)"

  { assume e_Q1:"\<forall>e \<in> (q \<sigma>). (QStateM_map Q1) e \<noteq> {}"
    moreover have "\<forall>e \<in> (q \<sigma>). (QStateM_map Q2) e = {}" using calculation
      by (metis Measure.prems(2) sep_add_zero_sym sep_disj_commuteI sep_disj_zero vars_map_int)
    ultimately have eq_set:"\<Union> (QStateM_map Q1 ` q \<sigma>) = \<Union> (QStateM_map \<Q> ` q \<sigma>)"
      by (metis Measure.prems(2) Pair_inject Q_domain_var_def eq_domain_var_plus init_tuple)
    then have k:"k < 2 ^ card(\<Union> (QStateM_map Q1 ` q \<sigma>))"
      using valid_k by presburger
  
    have prob_measure_Q1_eq_\<delta>k:"\<delta>k = ?\<delta>k" 
      using measure_vector_q_in_tensor_Q1_eq_tensor_measure_vector_q_in_Q1_Q2[OF measure Measure.prems(2) k valid_prob e_Q1]
      by (metis fst_conv)
    have step:"\<turnstile> \<langle>Measure v q, Normal (\<delta>1,\<sigma>,Q1)\<rangle> \<Rightarrow> Normal (\<delta>1*?\<delta>k,\<sigma>', ?Q')"
      apply (rule QExec.Measure[of ?addr Q1 q \<sigma> k ?\<delta>k ?Q' _ \<delta>1 \<sigma>', OF _ e_Q1], 
                   auto simp add: eq_set valid_k sigma') 
      using prob_measure_Q1_eq_\<delta>k valid_prob by auto
    moreover have "\<delta>' = \<delta>1 * ?\<delta>k *\<delta>2" 
      using  init_tuple step_tuple measure  prob_measure_Q1_eq_\<delta>k by force
    moreover have " Q' = ?Q' + Q2 "
      using measure_vector_q_in_tensor_Q1_eq_tensor_measure_vector_q_in_Q1_Q2[OF measure Measure.prems(2) k valid_prob e_Q1]
      by (metis XQState.simps(1) snd_conv step_tuple)
    moreover have "?Q' ## Q2"
      by (metis Measure.prems(2) QStateM_rel1 disj_QState_def fst_conv measure_vars_dest 
              measure_vars_dest_QStateM prob_measure_Q1_eq_\<delta>k sep_disj_QState 
              sep_disj_QStateM valid_prob)
    ultimately have ?case by auto
  }
  moreover {
    assume e_Q1:"\<not> (\<forall>e \<in> (q \<sigma>). (QStateM_map Q1) e \<noteq> {})"
    then have ?case
      using QExec.Measure_F by blast
  }
  ultimately show ?case by auto
qed

lemma Frame_execution_not_fault:
  assumes           
    a0:"\<turnstile> \<langle>c,Normal (\<delta>1*\<delta>2,\<sigma>,Q1+Q2)\<rangle> \<Rightarrow> Normal (\<delta>',\<sigma>',Q')" and 
    a1:"Q1##Q2" and a2:"\<not> (\<turnstile> \<langle>c,Normal (\<delta>1,\<sigma>,Q1)\<rangle> \<Rightarrow> Fault)"
  shows "\<exists>\<delta>1' Q1'. \<turnstile> \<langle>c,Normal (\<delta>1,\<sigma>,Q1)\<rangle> \<Rightarrow> Normal (\<delta>1',\<sigma>',Q1') \<and>
                    \<delta>' = \<delta>1'*\<delta>2 \<and> Q' = Q1'+Q2  \<and> Q1'##Q2 "
  using Frame_execution a0 a1 a2 by blast  
  

lemma
  assumes a0: "Q1'' + Q2 = k \<cdot>\<^sub>Q Qb" and a1:"Q1'' ## Q2" and
             "k \<cdot>\<^sub>Q Qb = Qb' + Qb''" and 
             "QStateM_wf (QStateM_map Q1'', k' \<cdot>\<^sub>q (qstate Qb')) \<and>
             QStateM_wf (QStateM_map Q2, (inverse k') \<cdot>\<^sub>q (qstate Qb''))" and
             "Q1'' = k' \<cdot>\<^sub>Q Qb' \<and> Q2 = inverse k' \<cdot>\<^sub>Q (Qb'')" and 
             "Q1'' + Q2 = k \<cdot>\<^sub>Q Qb"
           shows "k \<cdot>\<^sub>Q Qb = k' \<cdot>\<^sub>Q Qb' +  inverse k' \<cdot>\<^sub>Q (Qb'')"
  using assms 
  by auto

lemma valid_is_safe: 
  assumes a0:"\<Turnstile>P c Q"
  shows "\<forall>s\<in>P. \<not> \<turnstile> \<langle>c,Normal s\<rangle> \<Rightarrow> Fault"
proof-
  { fix s
    assume a00:"s \<in>  P"
    { assume "\<forall>s'. \<not> \<turnstile> \<langle>c,Normal s\<rangle> \<Rightarrow> s'"
      then have ?thesis using a0 valid_def by auto
    }
    moreover { 
      assume "\<not> (\<forall>s'. \<not> \<turnstile> \<langle>c,Normal s\<rangle> \<Rightarrow> s')"
      then have "\<exists>s'. \<turnstile> \<langle>c,Normal s\<rangle> \<Rightarrow> s'" by auto
      then have ?thesis using  a00 a0 unfolding valid_def by auto
    } 
    ultimately have ?thesis by auto
  } thus ?thesis by auto
qed

thm step.induct
thm converse_rtranclp_induct [case_names Refl Trans]


lemma fault_to_fault:assumes a0:"\<turnstile>\<langle>c, s\<rangle> \<Rightarrow> s'" and a1:"Q1##Q2"
  shows "s = Normal (\<rho>1*\<rho>2,\<sigma>,Q1+Q2) \<Longrightarrow> s' = Fault \<Longrightarrow>  \<turnstile>\<langle>c,Normal (\<rho>1,\<sigma>,Q1)\<rangle> \<Rightarrow> Fault" 
  using a0 a1
proof(induct arbitrary: Q1 Q2 \<sigma> \<rho>1 \<rho>2)
  case (Skip \<sigma> Q1 Q2 \<sigma>' \<rho>1 \<rho>2 )
  then show ?case by auto
next
  case (StackMod f \<delta> \<sigma> \<Q>)
  then show ?case by auto
next
  case (QMod q \<sigma> \<Q> M \<Q>' \<delta>)
  then show ?case by auto
next
  case (QMod_F q \<sigma> \<Q> M  \<delta> Q1 Q2 \<sigma>' \<rho>1 \<rho>2)

  moreover { assume "\<exists>e. e \<in> q \<sigma> \<and> QStateM_map \<Q> e = {}"
    have ?case
      by (metis QStateM_disj_dest(1) QStateM_map_plus QState_map_all_not_empty_plus XQState.inject \<open>\<exists>e. e \<in> q \<sigma> \<and> QStateM_map \<Q> e = {}\<close> calculation(2) calculation(4) fst_conv snd_conv vars.QExec.QMod_F vars_axioms) 
  }
  moreover {
    assume "\<not> unitary M"
    then have ?case using QMod_F QExec.QMod_F  by presburger 
  }
  moreover {
    assume "\<forall>m. M \<notin> carrier_mat m m"
    then have ?case using QMod_F QExec.QMod_F
      by blast 
  }
  ultimately show ?case by auto
next
  case (Alloc q' \<Q> v \<sigma> \<vv>' q'_addr \<sigma>' q \<delta>)
  then show ?case
    by fastforce 
next
  case (Alloc_F v \<sigma> q \<delta> \<Q>)
  then show ?case
    using QExec.Alloc_F by blast 
next
  case (CondTrue \<sigma> b c1 \<delta> \<Q> \<sigma>' c2)
  then show ?case
    using QExec.CondTrue by blast 
next
  case (CondFalse \<sigma> b c2 \<delta> \<Q> \<sigma>' c1)
  then show ?case
    using QExec.CondFalse by blast 
next
  case (WhileTrue \<sigma> b c \<delta> \<Q> \<sigma>' \<sigma>'' Q1 Q2 \<sigma>''' \<rho>1 \<rho>2)
  then show ?case using QExec_elim_cases(6)[OF WhileTrue(4)] QExec.WhileTrue 
    by (smt (verit) Frame_execution_not_fault Pair_inject XQState.inject not_fault_while)
next
  case (WhileFalse \<sigma> b c \<delta> \<Q> Q1 Q2 \<sigma>' \<rho>1 \<rho>2)
  then show ?case by blast 
next
  case (Seq C1 \<alpha> \<alpha>' C2 \<alpha>'' Q1 Q2 \<sigma> \<delta>1 \<delta>2)
  { assume "\<alpha>' = Fault"
    then have ?case using Seq
      by (meson QExec.Seq)
  }
  moreover { 
    assume "\<not> \<alpha>' = Fault"
    then obtain \<delta>' \<sigma>' Q' where 
      stepc1:"\<turnstile> \<langle>C1,Normal \<alpha>\<rangle> \<Rightarrow> Normal (\<delta>',\<sigma>',Q')" and 
      \<alpha>':"\<alpha>' = Normal (\<delta>',\<sigma>',Q')"
        by (metis Seq.hyps(1) XQState.exhaust prod_cases3) 
    then have "(\<exists>\<delta>1' Q1'. \<turnstile> \<langle>C1,Normal (\<delta>1,\<sigma>,Q1)\<rangle> \<Rightarrow> Normal (\<delta>1',\<sigma>',Q1') \<and>
                    \<delta>' = \<delta>1'*\<delta>2 \<and> Q' = Q1'+Q2  \<and> Q1'##Q2) \<or> \<turnstile> \<langle>C1,Normal (\<delta>1,\<sigma>,Q1)\<rangle> \<Rightarrow> Fault"
      using Frame_execution Seq.prems(1) Seq.prems(3) by auto
    moreover { 
      assume "\<exists>\<delta>1' Q1'. \<turnstile> \<langle>C1,Normal (\<delta>1,\<sigma>,Q1)\<rangle> \<Rightarrow> Normal (\<delta>1',\<sigma>',Q1') \<and>
                    \<delta>' = \<delta>1'*\<delta>2 \<and> Q' = Q1'+Q2  \<and> Q1'##Q2"
      then obtain \<delta>1' Q1' where 
        "\<turnstile> \<langle>C1,Normal (\<delta>1,\<sigma>,Q1)\<rangle> \<Rightarrow> Normal (\<delta>1',\<sigma>',Q1')" and
        "\<delta>' = \<delta>1'*\<delta>2" and "Q' = Q1'+Q2" and "Q1'##Q2" by auto
      then have ?case
        using QExec.Seq Seq.hyps(4) Seq.prems(2) \<alpha>' by presburger 
    }
    moreover { assume "\<turnstile> \<langle>C1,Normal (\<delta>1,\<sigma>,Q1)\<rangle> \<Rightarrow> Fault"
      then have ?case
        using QExec.Fault_Prop QExec.Seq by blast 
    }
    ultimately have ?case by auto
  }
  ultimately show ?case by auto
next
  case (Dispose \<Q>' \<Q>'' \<Q> q i \<sigma> \<delta>)
  then show ?case
    by fastforce 
next
  case (Dispose_F \<Q> q i \<sigma> \<delta> Q1 Q2 \<sigma>' \<rho>1 \<rho>2)
  then show ?case using QExec.Dispose_F apply auto
    by (metis sep_add_assoc sep_add_disjD sep_disj_addI3)
next
  case (Measure addr1 \<Q> q \<sigma> k \<delta>k \<Q>' \<delta>' \<delta> \<sigma>' v)
  then show ?case by auto
next
  case (Measure_F q \<sigma> \<Q> v \<delta>)
  then show ?case
    by (metis Pair_inject QExec.Measure_F QStateM_map_plus Sep_Prod_Instance.none_def XQState.inject plus_fun_def)
next
  case (Fault_Prop C)
  then show ?case
    by blast 
qed

lemma not_fault_conjunction_dis:
  assumes a0:"Q1##Q2" and 
          a1:"\<not> \<turnstile> \<langle>c,Normal (\<rho>1,\<sigma>,Q1)\<rangle> \<Rightarrow> Fault"
  shows"\<not> \<turnstile> \<langle>c,Normal (\<rho>1*\<rho>2,\<sigma>,Q1 + Q2)\<rangle> \<Rightarrow> Fault" using fault_to_fault
  using a0 a1 by blast
  
definition set_a::"('a\<times>'b\<times>'c) set \<Rightarrow> 'b set"
  where "set_a s \<equiv> {b. \<exists>a c. (a,b,c)\<in>s}" 

lemma normal_normal:"\<turnstile> \<langle>C2,s'\<rangle> \<Rightarrow> Normal s \<Longrightarrow> \<exists>a' b' c'. s' = Normal (a',b',c')"
  by (metis XQState.exhaust exec_Fault_end prod_cases3)

lemma disjoint_modified_c_accessed_A:
  assumes a0:"\<turnstile> \<langle>c,s\<rangle> \<Rightarrow> s'"
  shows "s = Normal  (\<delta>, \<sigma>, \<Q>) \<Longrightarrow> s' = Normal (\<delta>', \<sigma>', \<Q>') \<Longrightarrow> 
         \<delta> = \<delta>1 * \<delta>2 \<Longrightarrow> \<Q> =  Q1 + Q2 \<Longrightarrow> Q1 ## Q2 \<Longrightarrow>  \<delta>' = \<delta>1'*\<delta>2 \<Longrightarrow> \<Q>' = Q1'+Q2 \<Longrightarrow>
        (\<delta>2, \<sigma>, Q2) \<in> A \<Longrightarrow> 
        not_access_v_set (\<lambda>s. \<lambda>a c. s\<in>{b. (a,b,c)\<in>A}) (modify_locals c) \<Longrightarrow>
        \<not> \<turnstile> \<langle>c,Normal (\<delta>1, \<sigma>, Q1)\<rangle> \<Rightarrow>  Fault \<Longrightarrow>
        (\<delta>2, \<sigma>', Q2) \<in> A"
  using a0 
proof(induct arbitrary:\<sigma> \<sigma>' \<delta> \<delta>1 \<delta>2 \<Q> Q1 Q2 \<delta>' \<delta>1' \<Q>' Q1' )
  case (Skip \<sigma>)
  then show ?case
    by blast 
next
  case (StackMod f \<delta> \<sigma> \<Q> \<sigma>' \<sigma>'' \<delta>' \<delta>1 \<delta>2 \<Q>' Q1 Q2 \<delta>'' \<delta>1' \<Q>'' Q1')
  moreover have "modify_locals (SMod f) = {v. modify_v f v}"
    by simp
  moreover have "\<sigma>'' = f \<sigma>'"
    using QExec_Normal_elim_cases(3) calculation(2) calculation(1) by force  
  moreover have "finite {v. modify_v f v}"
    by (metis UNIV_def finite_Un finite_vars sup_top_right)
  ultimately show ?case 
    by (metis (no_types, lifting) mem_Collect_eq not_access_v_set_modify) 
next
  case (Alloc q' \<Q> v \<sigma> \<vv>' q'_addr \<sigma>' q \<delta> \<sigma>'' \<sigma>''' \<delta>' \<delta>1 \<delta>2 \<Q>' Q1 Q2 \<delta>'' \<delta>1' \<Q>'' Q1')
  moreover have "modify_locals (Alloc q v) = {q}"
    by simp
  moreover obtain q'' where "\<sigma>' = set_value \<sigma> q (from_nat q'')"
    using QExec_elim_cases(9) using calculation(3) by blast 
  ultimately show ?case using not_access_v_set_f_q_eq_set[OF Alloc(14)] apply auto
    by meson+
next
  case (CondTrue \<sigma> b c1 \<delta> \<Q> \<sigma>' c2 \<sigma>'' \<sigma>''' \<delta>' \<delta>1 \<delta>2 \<Q>' Q1 Q2 \<delta>'' \<delta>1' \<Q>'' Q1')
  then have "\<not> \<turnstile> \<langle>c1,Normal (\<delta>1,\<sigma>'', Q1)\<rangle> \<Rightarrow> Fault" using QExec.CondTrue[OF CondTrue(1)] by auto
  moreover have "not_access_v_set (\<lambda>s. \<lambda>a c. s\<in>{b. (a,b,c)\<in>A}) (modify_locals c1)"
    using CondTrue.prems not_access_v_set_included by auto  
  ultimately show ?case 
    using  CondTrue.prems CondTrue.hyps(3) by blast 
next
  case (CondFalse \<sigma> b c2 \<delta> \<Q> \<sigma>' c1 \<sigma>'' \<sigma>''' \<delta>' \<delta>1 \<delta>2 \<Q>' Q1 Q2 \<delta>'' \<delta>1' \<Q>'' Q1')
  then have "\<not> \<turnstile> \<langle>c2,Normal (\<delta>1,\<sigma>'', Q1)\<rangle> \<Rightarrow> Fault" using QExec.CondFalse by auto
  moreover have "not_access_v_set (\<lambda>s. \<lambda>a c. s\<in>{b. (a,b,c)\<in>A}) (modify_locals c2)"
    using CondFalse.prems not_access_v_set_included by auto  
  ultimately show ?case 
    using  CondFalse.prems CondFalse.hyps(3) by blast 
next
  case (WhileTrue \<sigma> b c \<delta> \<Q> s' s'' \<sigma>a \<sigma>'' \<delta>a \<delta>1 \<delta>2 \<Q>a \<Q>1 \<Q>2 \<delta>'' \<delta>1'' \<Q>'' \<Q>1'')
  have not_access_C1:"not_access_v_set (\<lambda>s a c. s \<in> {b. (a, b, c) \<in> A}) (modify_locals (c))" 
    using not_access_v_set_included
    using WhileTrue.prems(9) by force 

  obtain  \<delta>' \<sigma>' \<Q>' where s':"s' = Normal(\<delta>',\<sigma>',\<Q>')" using WhileTrue
    by (meson normal_normal)

  obtain \<Q>1'  \<delta>1'  where
     \<delta>':"\<turnstile> \<langle>c,Normal (\<delta>1, \<sigma>a, \<Q>1)\<rangle> \<Rightarrow> Normal (\<delta>1', \<sigma>', \<Q>1') \<and> \<delta>' = \<delta>1'*\<delta>2 \<and> \<Q>' = \<Q>1' + \<Q>2 \<and> \<Q>1' ## \<Q>2  \<or>
         \<turnstile> \<langle>c,Normal (\<delta>1, \<sigma>a, \<Q>1)\<rangle> \<Rightarrow> Fault"
    using Frame_execution[OF  WhileTrue(2)[simplified WhileTrue(6,7,8,9) s'] WhileTrue(10)] by blast
  then have A:"(\<delta>2, \<sigma>', \<Q>2) \<in> A"
    by (metis (mono_tags, lifting) Pair_inject WhileTrue.hyps(1) WhileTrue.hyps(3) 
         WhileTrue.prems(1) WhileTrue.prems(10) WhileTrue.prems(3) WhileTrue.prems(4) 
        WhileTrue.prems(5) WhileTrue.prems(8) XQState.inject not_access_C1 not_fault_while s')  
  then show ?case
    by (metis (mono_tags, lifting) WhileTrue.hyps(1) WhileTrue.hyps(5) WhileTrue.prems(1) 
           WhileTrue.prems(10) WhileTrue.prems(2) WhileTrue.prems(6) WhileTrue.prems(7) 
           XQState.inject \<delta>' fst_conv local.WhileTrue(14) 
            not_fault_while s' snd_conv vars.step_not_to_fault vars_axioms) 
next
  case (Seq C1 s s' C2 s'' \<sigma> \<sigma>'' \<delta> \<delta>1 \<delta>2 \<Q> \<Q>1 \<Q>2 \<delta>'' \<delta>1'' \<Q>'' \<Q>1'')
  have not_access_C1:"not_access_v_set (\<lambda>s a c. s \<in> {b. (a, b, c) \<in> A}) (modify_locals (C1))" and
       not_access_C2:"not_access_v_set (\<lambda>s a c. s \<in> {b. (a, b, c) \<in> A}) (modify_locals (C2))"
    using Seq.prems(9) not_access_v_set_included by auto
  obtain \<delta>' \<sigma>'  \<Q>' where 
    s':"s' = Normal (\<delta>',\<sigma>', \<Q>')"
    using Seq(3)[simplified Seq(6)] normal_normal by blast 
   
  obtain \<Q>1'  \<delta>1'  where
     \<delta>':"\<turnstile> \<langle>C1,Normal (\<delta>1, \<sigma>, \<Q>1)\<rangle> \<Rightarrow> Normal (\<delta>1', \<sigma>', \<Q>1') \<and> \<delta>' = \<delta>1'*\<delta>2 \<and> \<Q>' = \<Q>1' + \<Q>2 \<and> \<Q>1' ## \<Q>2  \<or>
         \<turnstile> \<langle>C1,Normal (\<delta>1, \<sigma>, \<Q>1)\<rangle> \<Rightarrow> Fault"
    using Frame_execution[OF Seq(1)[simplified Seq(5,7,8) s'] Seq(9)] Seq.prems(10)
    by blast
  then have A:"(\<delta>2, \<sigma>', \<Q>2) \<in> A"  
    using  Seq.hyps(2)[OF Seq.prems(1) s' Seq(7) Seq(8) Seq(9) _ _ Seq(12) not_access_C1]
    using QExec.Fault_Prop QExec.Seq Seq.prems(10) by blast

  have "\<not>\<turnstile> \<langle>C1,Normal (\<delta>1, \<sigma>, \<Q>1)\<rangle> \<Rightarrow> Fault"
    using QExec.Fault_Prop QExec.Seq Seq.prems(10) by blast 
  moreover have "\<not>\<turnstile> \<langle>C2,Normal (\<delta>1', \<sigma>', \<Q>1')\<rangle> \<Rightarrow> Fault"
    using QExec.Seq Seq.prems(10) \<delta>' calculation by force 
  ultimately show ?case 
    using local.Seq(4)[OF s' Seq.prems(2) _ _ _  Seq.prems(6) Seq.prems(7) A not_access_C2] \<delta>'   by blast  
next
  case (Measure addr1 \<Q> q \<sigma> k \<delta>k \<Q>' \<delta>' \<delta> \<sigma>' v \<sigma>'' \<sigma>''' \<delta>'' \<delta>1 \<delta>2 \<Q>'' Q1 Q2 \<delta>''' \<delta>1' \<Q>''' Q1')
  then show ?case using not_access_v_set_f_q_eq_set[OF Measure(16)] apply auto
    by meson+ 
qed(auto)
  
lemma frame_sound: 
  assumes a0:"\<Turnstile>P c Q" and
    a1:"not_access_v_set (\<lambda>s. \<lambda>a c. s\<in>{b. (a,b,c)\<in>A}) (modify_locals c)"
  shows "\<Turnstile>(P \<and>\<^sup>* A) c (Q \<and>\<^sup>* A)"
proof-
  { fix s s'
    assume step:"\<turnstile> \<langle>c,s\<rangle> \<Rightarrow> s'" and 
           "s \<in> Normal ` (P \<and>\<^sup>* A)"
    then obtain sn \<delta> \<sigma> \<Q> where 
      s_normal:"s = Normal sn" and 
      "sn \<in>  (P \<and>\<^sup>* A)" and
      sn:"sn = (\<delta>, \<sigma>, \<Q>)" by auto
    then obtain \<delta>1 \<delta>2 Q1 Q2 where
       delta:"\<delta> = \<delta>1 * \<delta>2" and P:"(\<delta>1, \<sigma>, Q1) \<in> P" and 
       A:"(\<delta>2, \<sigma>, Q2) \<in> A" and Q_eq_Q1_plus_Q2:" \<Q> =  Q1 + Q2" and Q1_disj_Q2:"Q1 ## Q2"
      using Q_sep_dis_set_dest
      by fastforce
    have not_fault:"\<not> \<turnstile> \<langle>c,Normal (\<delta>1, \<sigma>, Q1)\<rangle> \<Rightarrow> Fault"
      using valid_is_safe[OF a0] P
      by blast 
    then have "\<not> \<turnstile> \<langle>c,Normal (\<delta>, \<sigma>, \<Q>)\<rangle> \<Rightarrow> Fault" using not_fault_conjunction_dis
      using Q1_disj_Q2 Q_eq_Q1_plus_Q2 delta by blast 
    then obtain \<delta>' \<sigma>' Q' where s':"s' = Normal (\<delta>',\<sigma>',Q')" using step s_normal sn
      by (cases s', auto)
    then obtain \<delta>1' Q1' where cond:"\<turnstile> \<langle>c,Normal (\<delta>1, \<sigma>, Q1)\<rangle> \<Rightarrow>  Normal (\<delta>1',\<sigma>',Q1') \<and>
                    \<delta>' = \<delta>1'*\<delta>2 \<and> Q' = Q1'+Q2  \<and> Q1'##Q2 " and 
                    step:"\<turnstile> \<langle>c,Normal (\<delta>, \<sigma>, \<Q>)\<rangle> \<Rightarrow> Normal (\<delta>', \<sigma>', Q')"
      using Frame_execution
      using Q1_disj_Q2 Q_eq_Q1_plus_Q2 delta not_fault step s_normal sn by blast      
    then have   Q:"(\<delta>1', \<sigma>', Q1') \<in> Q"
      using a0 unfolding valid_def
      using \<open>(\<delta>1, \<sigma>, Q1) \<in> P\<close>  by auto  
    have  A: "(\<delta>2, \<sigma>', Q2) \<in> A"
      using disjoint_modified_c_accessed_A[OF step _ _ delta Q_eq_Q1_plus_Q2 Q1_disj_Q2 _ _ A a1 not_fault]
      using cond by blast
    have "s' \<in> Normal ` (Q \<and>\<^sup>* A) " 
      using Q_sep_dis_set_intro[OF Q A] cond s'
      by blast
  }
  thus  ?thesis unfolding valid_def by auto 
qed



lemma quantum_separation_logic_sound:
 "\<turnstile> P c Q \<Longrightarrow> \<Turnstile> P c Q"
proof(induct rule:hoarep.induct)
case (Skip Q)
  then show ?case unfolding valid_def
    by (auto elim: QExec_Normal_elim_cases)
next
  case (SMod f Q) 
  then show ?case unfolding valid_def 
    unfolding get_stack_def set_stack_def get_prob_def get_qstate_def get_QStateM_def
    using QExec_Normal_elim_cases(3) QExec_elim_cases(1) XQState.distinct(1)
    apply auto
    by blast
next
  case (QMod M q_v st \<Q> qs Q) 
  thm QExec_Normal_elim_cases(4)[of M]
  then show ?case unfolding valid_def   
    unfolding get_stack_def get_QStateM_def set_qstate_def get_prob_def get_qstate_def Q_domain_set_def 
    apply clarsimp 
    by  (rule  QExec_Normal_elim_cases(4)[of M], auto)     
next
  case (Seq P c\<^sub>1 R c\<^sub>2 Q)
  have valid_c1:"\<Turnstile>P c\<^sub>1 R" by fact
  have valid_c2:"\<Turnstile>R c\<^sub>2 Q" by fact
  show ?case 
  proof-
  { fix \<sigma> \<sigma>'
    assume exec:" \<turnstile> \<langle>c\<^sub>1;; c\<^sub>2,Normal \<sigma>\<rangle> \<Rightarrow> \<sigma>'"    
    assume P:"\<sigma> \<in> P"
    from exec P obtain r where
      exec_c1: "\<turnstile>\<langle>c\<^sub>1,Normal \<sigma>\<rangle> \<Rightarrow> r" and exec_c2:  "\<turnstile>\<langle>c\<^sub>2,r\<rangle> \<Rightarrow> \<sigma>'"
      by cases auto   
    with valid_c1 exec_c1 P 
    have r: "r\<in>Normal ` R"        
      unfolding valid_def by auto
    have "\<sigma>' \<in> Normal ` Q"     
    proof(cases r)
      case (Normal r')
      with exec_c2 r show ?thesis 
        using valid_c2  unfolding valid_def by auto
    next
      case Fault
      then show ?thesis
        using r by blast
    qed
  } thus ?case unfolding valid_def by auto
qed
next
  case (Cond P b c\<^sub>1 Q c\<^sub>2)
  have valid_c1:"\<Turnstile>(P \<inter> {s. get_stack s \<in> b}) c\<^sub>1 Q" by fact
  have valid_c2:"\<Turnstile>(P \<inter> {s. get_stack s \<in> - b}) c\<^sub>2 Q" by fact
  show "\<Turnstile>P IF b c\<^sub>1 c\<^sub>2 Q"
  proof-
    { fix \<sigma> \<sigma>'
      assume exec: "\<turnstile>\<langle>IF b c\<^sub>1 c\<^sub>2,Normal \<sigma>\<rangle> \<Rightarrow> \<sigma>'"
      assume P: "\<sigma> \<in> P"      
      have "\<sigma>' \<in> Normal ` Q"
      proof(cases "get_stack \<sigma> \<in> b")
        case True
        with exec have "\<turnstile>\<langle>c\<^sub>1,Normal \<sigma>\<rangle> \<Rightarrow> \<sigma>'"
          by cases (auto simp add: get_stack_def)
        with P True show ?thesis 
          using valid_c1  
          unfolding valid_def get_stack_def by auto      
      next
        case False        
        with exec have "\<turnstile>\<langle>c\<^sub>2,Normal \<sigma>\<rangle> \<Rightarrow> \<sigma>'"
          by cases (auto simp add: get_stack_def)
        with P False show ?thesis 
          using valid_c2  
          unfolding valid_def get_stack_def by auto
      qed
    } thus ?case unfolding valid_def by auto
  qed  
next
  case (While P b c)
  have valid_c: "\<Turnstile>(P \<inter> {s. get_stack s \<in> b}) c P" by fact
  show ?case
  proof-
  { fix \<sigma> \<sigma>'
    assume exec: "\<turnstile>\<langle>While b c,Normal \<sigma>\<rangle> \<Rightarrow> \<sigma>'"
    assume P: "\<sigma> \<in> P"
    have "\<sigma>' \<in> Normal ` (P \<inter> {s. get_stack s \<in> - b})" 
    proof (cases "\<sigma> \<in> {s. get_stack s \<in> b}")
      case True
      {  fix d::"('v,'s) com" fix \<sigma> \<sigma>'
         assume exec: "\<turnstile>\<langle>d,\<sigma>\<rangle> \<Rightarrow> \<sigma>'"
         assume d: "d=While b c"
         from exec d 
         have "\<lbrakk>\<sigma> \<in> Normal ` P \<rbrakk>
               \<Longrightarrow> \<sigma>' \<in> Normal ` (P \<inter> {s. get_stack s \<in> - b})"
         proof (induct)       
           case (WhileTrue \<sigma> b' c' \<delta> \<Q> \<sigma>' \<sigma>'')
           have eqs: "While b' c' = While b c" by fact
           note valid_c
           moreover from WhileTrue
           obtain "\<turnstile>\<langle>c,Normal (\<delta>, \<sigma>, \<Q>)\<rangle> \<Rightarrow> \<sigma>'" and
              "\<turnstile>\<langle>While b c,\<sigma>'\<rangle> \<Rightarrow> \<sigma>''" and
            "Normal (\<delta>, \<sigma>, \<Q>) \<in> Normal `(P \<inter> {s. get_stack s \<in> b})" 
             unfolding get_stack_def by auto   
           ultimately
           have r: "\<sigma>' \<in> Normal ` P" unfolding valid_def
             by- auto
           from this _
           show ?case
           proof(cases \<sigma>')
             case (Normal \<sigma>1')
             then show ?thesis
               using r  eqs              
               by - (rule WhileTrue.hyps,auto)
           next
             case Fault with r show ?thesis by blast
           qed
         qed (auto simp add: get_stack_def)
       } with exec P  show ?thesis by auto
    next
      case False with exec P have "\<sigma>' = Normal \<sigma>"
        unfolding get_stack_def
        by cases auto
      with P False show ?thesis by auto
    qed
  } thus ?case unfolding valid_def by auto
  qed  
next
  case (QAlloc v q e)
  then show ?case using alloc_sound by auto 
next
  case (QDispose q i)
  then show ?case using dispose_sounda by auto
next
  case (QMeasure v q vl qr)
  then show ?case using meassure_sound by auto
next
  case (Frame P c Q A)
  then show ?case using frame_sound by auto
next
case (Conseq P c Q)
  hence adapt: "\<forall>s \<in> P. (\<exists>P' Q' A'. \<Turnstile> P' c Q'  \<and>
                          s \<in> P' \<and> Q' \<subseteq> Q )"
    by blast
  then show "\<Turnstile> P c Q" 
  proof-
  {
    fix s t
    assume exec: "\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow> t"
    assume P: "s \<in> P"    
    have "t \<in> Normal ` Q"
    proof-
      from P adapt obtain P' Q' Z where
         spec:"\<Turnstile> P' c Q'"  and
        P': "s \<in> P'"  and  strengthen: "Q' \<subseteq> Q "
        by auto
      from spec [rule_format]  exec P' 
      have "t \<in> Normal ` Q'" unfolding valid_def by auto
      with strengthen show ?thesis by blast
    qed
  } thus ?thesis unfolding valid_def by auto qed
qed


end
end
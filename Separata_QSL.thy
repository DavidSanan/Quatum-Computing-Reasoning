theory Separata_QSL
  imports QSemanticsBig 
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
end

(* The two definitions below are moved out of the vars context.*)

definition empty_qstatem_ass::" (('s state) set)"
("/|>a")
where "empty_qstatem_ass \<equiv> {s. fst s = 1 \<and> get_QStateM s = 0}"

definition prob_assert::" (('s state) set) \<Rightarrow>  real \<Rightarrow> (('s state) set)"
(infixr "\<smile>" 60)
where "prob_assert q p \<equiv> if p \<noteq> 0 then (\<lambda>s. (fst s * p, snd s)) ` q 
                          else (\<lambda>s. (fst s * p, snd s)) ` UNIV"

(* NOTE: The above are taken from Quantum_separataion_logicDef.thy
   Should separate the above definitions in a new file...*)

(* BEGIN development of this file. *)

text \<open>The following lemmas show the soundness of the inference rules in the labelled sequent 
calculus for quantum separation logic. 
  We also show the invertibility of those rules when possible.\<close>

definition tern_rel_qsl:: "QStateM \<Rightarrow> QStateM \<Rightarrow> QStateM \<Rightarrow> bool" ("(_\<circ>_\<triangleright>_)" 25) where
  "tern_rel_qsl a b c \<equiv> a ## b \<and> a + b = c"

text \<open>The definition of magic wand, though is not widely used in this application.\<close>

definition Q_sep_magic_set1::"(('s state) set) \<Rightarrow> (('s state) set) \<Rightarrow>  (('s state) set)" 
(infixr "--*1" 35)
where "Q_sep_magic_set1 A B \<equiv>           
         {(\<rho>,\<sigma>,Q). \<forall>\<rho>1 \<rho>2 Q1 Q2. ((\<rho>1,\<sigma>,Q1) \<in> A \<and> \<rho>2 = \<rho>1 * \<rho> \<and> Q1 ## Q \<and> Q2 = Q1 + Q)
          \<longrightarrow> (\<rho>2,\<sigma>,Q2) \<in> B}"

text \<open>Soundness of empL.\<close>

lemma empl_qsl: 
  "Gamma \<and> ((snd (snd s)) = 0) \<and> ((fst s) = 1) \<longrightarrow> Delta \<Longrightarrow> 
  Gamma \<and> (s \<in> empty_qstatem_ass) \<longrightarrow> Delta"
  unfolding empty_qstatem_ass_def get_QStateM_def by auto

lemma empl_qsl_inv:
  "Gamma \<and> (s \<in> empty_qstatem_ass) \<longrightarrow> Delta \<Longrightarrow>  
  Gamma \<and> ((snd (snd s)) = 0) \<and> ((fst s) = 1) \<longrightarrow> Delta"
  unfolding empty_qstatem_ass_def get_QStateM_def by auto

lemma empl_qsl_der: "(s \<in> empty_qstatem_ass) \<Longrightarrow> (((snd (snd s)) = 0) \<and> ((fst s) = 1))"
  using empl_qsl by blast

lemma empl_qsl_eq: "(s \<in> empty_qstatem_ass) = (((snd (snd s)) = 0) \<and> ((fst s) = 1))"
  unfolding empty_qstatem_ass_def get_QStateM_def by auto

text \<open>Soundness of empR.\<close>

lemma empr_qsl: 
  "Gamma \<longrightarrow> ((1,stk,0) \<in> empty_qstatem_ass) \<or> Delta"
  unfolding empty_qstatem_ass_def get_QStateM_def by auto

lemma empr_qsl_der: "(1,stk,0) \<in> empty_qstatem_ass"
  using empr_qsl
  by metis 

text \<open>Soundness of the $*L$ rule.\<close>
lemma starl_qsl_sub:
  "(\<exists>p1 p2 q1 q2. ((fst s) = p1 * p2 \<and> (q1\<circ>q2\<triangleright>(snd (snd s))) \<and>
  ((p1,(fst (snd s)),q1) \<in> A) \<and> ((p2,(fst (snd s)),q2) \<in> B))) \<Longrightarrow>
  s \<in> (A \<and>\<^sup>*1 B)"
  unfolding Q_sep_dis_set1_def tern_rel_qsl_def apply auto
  by auto

lemma starl_qsl_der:     
  "s \<in> (A \<and>\<^sup>*1 B) \<Longrightarrow> 
  (\<exists>p1 p2 q1 q2. ((fst s) = p1 * p2 \<and> (q1\<circ>q2\<triangleright>(snd (snd s))) \<and>
  ((p1,(fst (snd s)),q1) \<in> A) \<and> ((p2,(fst (snd s)),q2) \<in> B)))"
  unfolding Q_sep_dis_set1_def tern_rel_qsl_def apply auto
  by blast

lemma starl_qsl_eq:     
  "s \<in> (A \<and>\<^sup>*1 B) = 
  (\<exists>p1 p2 q1 q2. ((fst s) = p1 * p2 \<and> (q1\<circ>q2\<triangleright>(snd (snd s))) \<and>
  ((p1,(fst (snd s)),q1) \<in> A) \<and> ((p2,(fst (snd s)),q2) \<in> B)))"
  using starl_qsl_sub starl_qsl_der by blast

lemma starl_qsl:
  "(\<exists>p1 p2 q1 q2. ((fst s) = p1 * p2 \<and> (q1\<circ>q2\<triangleright>(snd (snd s))) \<and>
  Gamma \<and> ((p1,(fst (snd s)),q1) \<in> A) \<and> ((p2,(fst (snd s)),q2) \<in> B))) \<longrightarrow> Delta \<Longrightarrow>
  Gamma \<and> s \<in> (A \<and>\<^sup>*1 B) \<longrightarrow> Delta"
  using starl_qsl_der by blast

lemma starl_qsl_inv:
  "Gamma \<and> s \<in> (A \<and>\<^sup>*1 B) \<longrightarrow> Delta \<Longrightarrow>
  (\<exists>p1 p2 q1 q2. ((fst s) = p1 * p2 \<and> (q1\<circ>q2\<triangleright>(snd (snd s))) \<and>
  Gamma \<and> ((p1,(fst (snd s)),q1) \<in> A) \<and> ((p2,(fst (snd s)),q2) \<in> B))) \<longrightarrow> Delta"
  using starl_qsl_sub by blast

text \<open>Soundness of the $*R$ rule.\<close>
lemma starr_qsl:
  "\<lbrakk>Gamma \<and> (fst s) = p1 * p2 \<and> (q1\<circ>q2\<triangleright>(snd (snd s))) \<longrightarrow> 
      ((p1,(fst (snd s)),q1) \<in> A) \<or> s \<in> (A \<and>\<^sup>*1 B) \<or> Delta; 
    Gamma \<and> (fst s) = p1 * p2 \<and> (q1\<circ>q2\<triangleright>(snd (snd s))) \<longrightarrow> 
      ((p2,(fst (snd s)),q2) \<in> B) \<or> s \<in> (A \<and>\<^sup>*1 B) \<or> Delta\<rbrakk> \<Longrightarrow>
  Gamma \<and> (fst s) = p1 * p2 \<and> (q1\<circ>q2\<triangleright>(snd (snd s))) \<longrightarrow> s \<in> (A \<and>\<^sup>*1 B) \<or> Delta"
  using starl_qsl_sub by blast

lemma starr_qsl_inv:
  "Gamma \<and> (fst s) = p1 * p2 \<and> (q1\<circ>q2\<triangleright>(snd (snd s))) \<longrightarrow> s \<in> (A \<and>\<^sup>*1 B) \<or> Delta \<Longrightarrow>
  (Gamma \<and> (fst s) = p1 * p2 \<and> (q1\<circ>q2\<triangleright>(snd (snd s))) \<longrightarrow> 
      ((p1,(fst (snd s)),q1) \<in> A) \<or> s \<in> (A \<and>\<^sup>*1 B) \<or> Delta) \<and> 
  (Gamma \<and> (fst s) = p1 * p2 \<and> (q1\<circ>q2\<triangleright>(snd (snd s))) \<longrightarrow> 
      ((p2,(fst (snd s)),q2) \<in> B) \<or> s \<in> (A \<and>\<^sup>*1 B) \<or> Delta)"
  by simp

text \<open>For efficiency we only apply *R on a pair of a ternary relational atom
  and a formula ONCE. To achieve this, we create a special predicate to indicate that
  a pair of a ternary relational atom and a formula has already been used in
  a *R application. 
  Note that the predicate is true even if the *R rule hasn't been applied. 
  We will not infer the truth of this predicate in proof search, but only
  check its syntactical appearance, which is only generated by the lemma lspasl\_starr\_der. 
  We need to ensure that this predicate is not generated elsewhere
  in the proof search.
  This part is similar to the treatment in separata\<close>

definition starr_applied_qsl:: "QStateM \<Rightarrow> QStateM \<Rightarrow> QStateM \<Rightarrow> (('s state) set) \<Rightarrow> bool" where
  "starr_applied_qsl q1 q2 q0 F \<equiv> \<exists>p s. ((q1\<circ>q2\<triangleright>q0) \<and> \<not>((p,s,q0) \<in> F))"

lemma starr_qsl_der:
  "(fst s) = p1 * p2 \<Longrightarrow> (q1\<circ>q2\<triangleright>(snd (snd s))) \<Longrightarrow> s \<notin> (A \<and>\<^sup>*1 B) \<Longrightarrow> 
  ((fst s) = p1 * p2 \<and> (q1\<circ>q2\<triangleright>(snd (snd s))) \<and> \<not> (((p1,(fst (snd s)),q1) \<in> A) \<or> s \<in> (A \<and>\<^sup>*1 B)) \<and> 
    (starr_applied_qsl q1 q2 (snd (snd s)) (A \<and>\<^sup>*1 B))) \<or> 
  ((fst s) = p1 * p2 \<and> (q1\<circ>q2\<triangleright>(snd (snd s))) \<and> \<not> (((p2,(fst (snd s)),q2) \<in> B) \<or> s \<in> (A \<and>\<^sup>*1 B)) \<and> 
    (starr_applied_qsl q1 q2 (snd (snd s)) (A \<and>\<^sup>*1 B)))"
  by (metis prod.exhaust_sel starr_applied_qsl_def starr_qsl)

lemma starr_qsl_der2:
  "(fst s) = p1 * p2 \<Longrightarrow> (q1\<circ>q2\<triangleright>q) \<Longrightarrow> s \<notin> (A \<and>\<^sup>*1 B) \<Longrightarrow> (snd (snd s)) = q \<Longrightarrow>
  ((fst s) = p1 * p2 \<and> (q1\<circ>q2\<triangleright>(snd (snd s))) \<and> \<not> (((p1,(fst (snd s)),q1) \<in> A) \<or> s \<in> (A \<and>\<^sup>*1 B)) \<and> 
    (starr_applied_qsl q1 q2 (snd (snd s)) (A \<and>\<^sup>*1 B))) \<or> 
  ((fst s) = p1 * p2 \<and> (q1\<circ>q2\<triangleright>(snd (snd s))) \<and> \<not> (((p2,(fst (snd s)),q2) \<in> B) \<or> s \<in> (A \<and>\<^sup>*1 B)) \<and> 
    (starr_applied_qsl q1 q2 (snd (snd s)) (A \<and>\<^sup>*1 B)))"
  using starr_qsl_der
  by blast 

lemma starr_qsl_der3:
  "(fst s) = 1 \<Longrightarrow> (q1\<circ>q2\<triangleright>q) \<Longrightarrow> s \<notin> (A \<and>\<^sup>*1 B) \<Longrightarrow> (snd (snd s)) = q \<Longrightarrow>
  ((fst s) = 1 \<and> (q1\<circ>q2\<triangleright>(snd (snd s))) \<and> \<not> (((1,(fst (snd s)),q1) \<in> A) \<or> s \<in> (A \<and>\<^sup>*1 B)) \<and> 
    (starr_applied_qsl q1 q2 (snd (snd s)) (A \<and>\<^sup>*1 B))) \<or> 
  ((fst s) = 1 \<and> (q1\<circ>q2\<triangleright>(snd (snd s))) \<and> \<not> (((1,(fst (snd s)),q2) \<in> B) \<or> s \<in> (A \<and>\<^sup>*1 B)) \<and> 
    (starr_applied_qsl q1 q2 (snd (snd s)) (A \<and>\<^sup>*1 B)))"
  using starr_qsl_der
  by (metis mult_1)

lemma starr_qsl_der4:
  "((snd (snd s))\<circ>0\<triangleright>(snd (snd s))) \<Longrightarrow> s \<notin> (A \<and>\<^sup>*1 B) \<Longrightarrow> 
  (((snd (snd s))\<circ>0\<triangleright>(snd (snd s))) \<and> \<not> ((((fst s),(fst (snd s)),(snd (snd s))) \<in> A) \<or> 
    s \<in> (A \<and>\<^sup>*1 B)) \<and> 
    (starr_applied_qsl (snd (snd s)) 0 (snd (snd s)) (A \<and>\<^sup>*1 B))) \<or> 
  (((snd (snd s))\<circ>0\<triangleright>(snd (snd s))) \<and> \<not> (((1,(fst (snd s)),0) \<in> B) \<or> s \<in> (A \<and>\<^sup>*1 B)) \<and> 
    (starr_applied_qsl (snd (snd s)) 0 (snd (snd s)) (A \<and>\<^sup>*1 B)))"
  using starr_qsl_der mult_cancel_left1 by blast

lemma starr_qsl_der5:
  "(0\<circ>(snd (snd s))\<triangleright>(snd (snd s))) \<Longrightarrow> s \<notin> (A \<and>\<^sup>*1 B) \<Longrightarrow> 
  ((0\<circ>(snd (snd s))\<triangleright>(snd (snd s))) \<and> \<not> (((1,(fst (snd s)),0) \<in> A) \<or> s \<in> (A \<and>\<^sup>*1 B)) \<and> 
    (starr_applied_qsl 0 (snd (snd s)) (snd (snd s)) (A \<and>\<^sup>*1 B))) \<or> 
  (((snd (snd s))\<circ>0\<triangleright>(snd (snd s))) \<and> \<not> ((((fst s),(fst (snd s)),(snd (snd s))) \<in> B) \<or> 
    s \<in> (A \<and>\<^sup>*1 B)) \<and> 
    (starr_applied_qsl 0 (snd (snd s)) (snd (snd s)) (A \<and>\<^sup>*1 B)))"
  using starr_qsl_der
  by (metis (no_types, lifting) mult_cancel_right1 sep_add_commute sep_disj_commuteI 
      tern_rel_qsl_def)  

lemma starr_qsl_der6:
  "(q\<circ>0\<triangleright>q) \<Longrightarrow> s \<notin> (A \<and>\<^sup>*1 B) \<Longrightarrow> (snd (snd s)) = q \<Longrightarrow>
  ((q\<circ>0\<triangleright>q) \<and> \<not> ((((fst s),(fst (snd s)),(snd (snd s))) \<in> A) \<or> 
    s \<in> (A \<and>\<^sup>*1 B)) \<and> (starr_applied_qsl q 0 q (A \<and>\<^sup>*1 B))) \<or> 
  ((q\<circ>0\<triangleright>q) \<and> \<not> (((1,(fst (snd s)),0) \<in> B) \<or> s \<in> (A \<and>\<^sup>*1 B)) \<and> 
    (starr_applied_qsl q 0 q (A \<and>\<^sup>*1 B)))"
  using starr_qsl_der4 by blast

lemma starr_qsl_der7:
  "(0\<circ>q\<triangleright>q) \<Longrightarrow> s \<notin> (A \<and>\<^sup>*1 B) \<Longrightarrow> (snd (snd s)) = q \<Longrightarrow>
  ((0\<circ>q\<triangleright>q) \<and> \<not> (((1,(fst (snd s)),0) \<in> A) \<or> s \<in> (A \<and>\<^sup>*1 B)) \<and> 
    (starr_applied_qsl 0 q q (A \<and>\<^sup>*1 B))) \<or> 
  ((q\<circ>0\<triangleright>q) \<and> \<not> ((((fst s),(fst (snd s)),(snd (snd s))) \<in> B) \<or> 
    s \<in> (A \<and>\<^sup>*1 B)) \<and> 
    (starr_applied_qsl 0 q q (A \<and>\<^sup>*1 B)))"
  using starr_qsl_der5 by blast  

lemma starr_qsl_eq: 
  "((fst s) = p1 * p2 \<and> (q1\<circ>q2\<triangleright>(snd (snd s))) \<and> s \<notin> (A \<and>\<^sup>*1 B)) = 
  (((fst s) = p1 * p2 \<and> (q1\<circ>q2\<triangleright>(snd (snd s))) \<and> \<not> (((p1,(fst (snd s)),q1) \<in> A) \<or> s \<in> (A \<and>\<^sup>*1 B))) \<or> 
   ((fst s) = p1 * p2 \<and> (q1\<circ>q2\<triangleright>(snd (snd s))) \<and> \<not> (((p2,(fst (snd s)),q2) \<in> B) \<or> s \<in> (A \<and>\<^sup>*1 B))))"
  using starl_qsl_sub by blast

text \<open>Soundness of the $-*L$ rule.\<close>
lemma magicl_qsl_sub:
  "(\<forall>p1 p2 q1 q2. (p2 = p1 * (fst s) \<and> (q1\<circ>(snd (snd s))\<triangleright>q2) \<and>
  ((p1,(fst (snd s)),q1) \<in> A)) \<longrightarrow> ((p2,(fst (snd s)),q2) \<in> B)) \<Longrightarrow>
  s \<in> (A --*1 B)"
  unfolding tern_rel_qsl_def using Q_sep_magic_set1_def by force 

lemma magicl_qsl:
  "\<lbrakk>Gamma \<and> p2 = p1 * (fst s) \<and> (q1\<circ>(snd (snd s))\<triangleright>q2) \<and> s \<in> (A --*1 B) \<longrightarrow> 
      ((p1,(fst (snd s)),q1) \<in> A) \<or> Delta; 
    Gamma \<and> p2 = p1 * (fst s) \<and> (q1\<circ>(snd (snd s))\<triangleright>q2) \<and> s \<in> (A --*1 B) \<and> 
      ((p2,(fst (snd s)),q2) \<in> B) \<longrightarrow> Delta\<rbrakk> \<Longrightarrow>
  Gamma \<and> p2 = p1 * (fst s) \<and> (q1\<circ>(snd (snd s))\<triangleright>q2) \<and> s \<in> (A --*1 B) \<longrightarrow> Delta"
  using magicl_qsl_sub Q_sep_magic_set1_def tern_rel_qsl_def by fastforce 
  
lemma magicl_qsl_inv:
  "Gamma \<and> p2 = p1 * (fst s) \<and> (q1\<circ>(snd (snd s))\<triangleright>q2) \<and> s \<in> (A --*1 B) \<longrightarrow> Delta \<Longrightarrow>
  (Gamma \<and> p2 = p1 * (fst s) \<and> (q1\<circ>(snd (snd s))\<triangleright>q2) \<and> s \<in> (A --*1 B) \<longrightarrow> 
      ((p1,(fst (snd s)),q1) \<in> A) \<or> Delta) \<and> 
  (Gamma \<and> p2 = p1 * (fst s) \<and> (q1\<circ>(snd (snd s))\<triangleright>q2) \<and> s \<in> (A --*1 B) \<and> 
      ((p2,(fst (snd s)),q2) \<in> B) \<longrightarrow> Delta)"
  by simp

text \<open>Soundness of the $-*R$ rule.\<close>
lemma magic_qsl_der:     
  "s \<in> (A --*1 B) \<Longrightarrow> 
  (\<forall>p1 p2 q1 q2. (p2 = p1 * (fst s) \<and> (q1\<circ>(snd (snd s))\<triangleright>q2) \<and>
  ((p1,(fst (snd s)),q1) \<in> A)) \<longrightarrow> ((p2,(fst (snd s)),q2) \<in> B))"
  unfolding Q_sep_magic_set1_def tern_rel_qsl_def by auto

lemma magic_qsl_eq:     
  "s \<in> (A --*1 B) = 
  (\<forall>p1 p2 q1 q2. (p2 = p1 * (fst s) \<and> (q1\<circ>(snd (snd s))\<triangleright>q2) \<and>
  ((p1,(fst (snd s)),q1) \<in> A)) \<longrightarrow> ((p2,(fst (snd s)),q2) \<in> B))"
  using magicl_qsl_sub magic_qsl_der
  by metis 

lemma magicr_qsl:
  "(\<exists>p1 p2 q1 q2. (p2 = p1 * (fst s) \<and> (q1\<circ>(snd (snd s))\<triangleright>q2) \<and>
  Gamma \<and> ((p1,(fst (snd s)),q1) \<in> A) \<and> ((p2,(fst (snd s)),q2) \<notin> B))) \<longrightarrow> Delta \<Longrightarrow>
  Gamma \<longrightarrow> s \<in> (A --*1 B) \<or> Delta"
  by (metis magicl_qsl_sub)

lemma magicr_qsl_inv:
  "Gamma \<longrightarrow> s \<in> (A --*1 B) \<or> Delta \<Longrightarrow>
  (\<exists>p1 p2 q1 q2. (p2 = p1 * (fst s) \<and> (q1\<circ>(snd (snd s))\<triangleright>q2) \<and>
  Gamma \<and> ((p1,(fst (snd s)),q1) \<in> A) \<and> ((p2,(fst (snd s)),q2) \<notin> B))) \<longrightarrow> Delta"
  using magicl_qsl_sub
  by (meson magic_qsl_eq) 

lemma magicr_qsl_der:
  "s \<notin> (A --*1 B) \<Longrightarrow> 
  (\<exists>p1 p2 q1 q2. (p2 = p1 * (fst s) \<and> (q1\<circ>(snd (snd s))\<triangleright>q2) \<and> ((p1,(fst (snd s)),q1) \<in> A) \<and> 
    ((p2,(fst (snd s)),q2) \<notin> B)))"
  by (metis magicl_qsl_sub)
  
lemma magicr_qsl_eq:
  "s \<notin> (A --*1 B) = 
  (\<exists>p1 p2 q1 q2. (p2 = p1 * (fst s) \<and> (q1\<circ>(snd (snd s))\<triangleright>q2) \<and> ((p1,(fst (snd s)),q1) \<in> A) \<and> 
    ((p2,(fst (snd s)),q2) \<notin> B)))"
  by (metis magicl_qsl magicl_qsl_sub)

text \<open>Soundness of the probability rules dot L and dot R. 
Added assumptions that probabilities must be between (0,1] and (fst s) \<le> e.\<close>

lemma dotl_qsl:
  "0 < e \<and> e \<le> 1 \<Longrightarrow> 0 < (fst s) \<and> (fst s) \<le> 1 \<Longrightarrow> (fst s) \<le> e \<Longrightarrow>
  Gamma \<and> ((fst s) / e,snd s) \<in> A \<longrightarrow> Delta \<Longrightarrow>
  Gamma \<and> s \<in> (A\<smile>e) \<longrightarrow> Delta"
  unfolding prob_assert_def by auto

lemma dotl_qsl_inv: 
  "0 < e \<and> e \<le> 1 \<Longrightarrow> 0 < (fst s) \<and> (fst s) \<le> 1 \<Longrightarrow> (fst s) \<le> e \<Longrightarrow>  
  Gamma \<and> s \<in> (A\<smile>e) \<longrightarrow> Delta \<Longrightarrow>
  Gamma \<and> ((fst s) / e,snd s) \<in> A \<longrightarrow> Delta"
  unfolding prob_assert_def apply auto
  proof -
    assume a1: "0 < fst s"
    assume a2: "fst s \<le> e"
    assume a3: "(fst s / e, snd s) \<in> A"
    have "e \<noteq> 0"
      using a2 a1 by fastforce
    then show "s \<in> (\<lambda>p. (fst p * e, snd p)) ` A"
      using a3 by (simp add: rev_image_eqI)
  qed

lemma dotl_qsl_der:
  "0 < e \<and> e \<le> 1 \<Longrightarrow> 0 < (fst s) \<and> (fst s) \<le> 1 \<Longrightarrow> (fst s) \<le> e \<Longrightarrow>  
   s \<in> (A\<smile>e) \<Longrightarrow> (e \<le> 1) \<and> ((fst s) / e,snd s) \<in> A"
  using dotl_qsl by blast

lemma dotr_qsl:
  "0 < e \<and> e \<le> 1 \<Longrightarrow> 0 < (fst s) \<and> (fst s) \<le> 1 \<Longrightarrow> (fst s) \<le> e \<Longrightarrow>
  Gamma \<longrightarrow> ((fst s) / e,snd s) \<in> A \<or> Delta \<Longrightarrow>
  Gamma \<longrightarrow> s \<in> (A\<smile>e) \<or> Delta"
  unfolding prob_assert_def apply auto
  by (smt (verit, best) fst_conv image_iff nonzero_divide_eq_eq prod.collapse snd_conv)
  
lemma dotr_qsl_inv:
  "0 < e \<and> e \<le> 1 \<Longrightarrow> 0 < (fst s) \<and> (fst s) \<le> 1 \<Longrightarrow> (fst s) \<le> e \<Longrightarrow>  
  Gamma \<longrightarrow> s \<in> (A\<smile>e) \<or> Delta \<Longrightarrow>
  Gamma \<longrightarrow> ((fst s) / e,snd s) \<in> A \<or> Delta"
  unfolding prob_assert_def by auto

lemma dotr_qsl_der:
  "0 < e \<and> e \<le> 1 \<Longrightarrow> 0 < (fst s) \<and> (fst s) \<le> 1 \<Longrightarrow> (fst s) \<le> e \<Longrightarrow>  
  s \<notin> (A\<smile>e) \<Longrightarrow> ((fst s) / e,snd s) \<notin> A"
  using dotr_qsl by blast
  

text \<open>Soundness of the structural rules. Directly follows from separata, but reproved 
using the definitions for QSL.\<close>

text \<open>Soundness of $Eq_1$ and $Eq_2$.\<close>
lemma eq_qsl: 
  "Gamma \<and> (0\<circ>h2\<triangleright>h2) \<and> h1 = h2 \<longrightarrow> Delta \<Longrightarrow>
  Gamma \<and> (0\<circ>h1\<triangleright>h2) \<longrightarrow> Delta"
  unfolding tern_rel_qsl_def by auto

lemma eq_qsl_inv:
  "Gamma \<and> (0\<circ>h1\<triangleright>h2) \<longrightarrow> Delta \<Longrightarrow>
  Gamma \<and> (0\<circ>h2\<triangleright>h2) \<and> h1 = h2 \<longrightarrow> Delta"
  unfolding tern_rel_qsl_def by auto
  
lemma eq_qsl_der: "(0\<circ>h1\<triangleright>h2) \<Longrightarrow> ((0\<circ>h1\<triangleright>h1) \<and> h1 = h2)"
  using tern_rel_qsl_def by auto
  
lemma eq_qsl_eq: "(0\<circ>h1\<triangleright>h2) = ((0\<circ>h1\<triangleright>h1) \<and> (h1 = h2))"
  using eq_qsl_der by blast

text \<open>Soundness of $U$.\<close>
lemma u_qsl:
  "Gamma \<and> (h1\<circ>0\<triangleright>h1) \<longrightarrow> Delta \<Longrightarrow>
  Gamma \<longrightarrow> Delta"
  using tern_rel_qsl_def by auto

lemma u_qsl_inv:
  "Gamma \<longrightarrow> Delta \<Longrightarrow>
  Gamma \<and> (h1\<circ>0\<triangleright>h1) \<longrightarrow> Delta"
  by auto

lemma u_qsl_der: "(h1\<circ>0\<triangleright>h1)"
  using u_qsl by auto

lemma mu_qsl_der: "(p::real) = p * 1"
  by auto

text \<open>Soundness of $E$.\<close>
lemma e_qsl:
  "Gamma \<and> (h1\<circ>h2\<triangleright>h0) \<and> (h2\<circ>h1\<triangleright>h0) \<longrightarrow> Delta \<Longrightarrow>
  Gamma \<and> (h1\<circ>h2\<triangleright>h0) \<longrightarrow> Delta"
  using tern_rel_qsl_def
  by (simp add: sep_add_commute sep_disj_commute) 
  
lemma e_qsl_inv:
  "Gamma \<and> (h1\<circ>h2\<triangleright>h0) \<longrightarrow> Delta \<Longrightarrow>
  Gamma \<and> (h1\<circ>h2\<triangleright>h0) \<and> (h2\<circ>h1\<triangleright>h0) \<longrightarrow> Delta"
  by auto

lemma e_qsl_der: "(h1\<circ>h2\<triangleright>h0) \<Longrightarrow> (h1\<circ>h2\<triangleright>h0) \<and> (h2\<circ>h1\<triangleright>h0)"
  using e_qsl by blast 

lemma mc_qsl_der: "((p::real) = p1 * p2) \<Longrightarrow> (p = p1 * p2) \<and> (p = p2 * p1)"
  by auto

lemma e_qsl_eq: "(h1\<circ>h2\<triangleright>h0) = ((h1\<circ>h2\<triangleright>h0) \<and> (h2\<circ>h1\<triangleright>h0))"
  using e_qsl_der by blast
  
lemma a_qsl_der: 
  assumes a1: "(h1\<circ>h2\<triangleright>h0)"
    and a2: "(h3\<circ>h4\<triangleright>h1)"
  shows "(\<exists>h5. (h3\<circ>h5\<triangleright>h0) \<and> (h2\<circ>h4\<triangleright>h5) \<and> (h1\<circ>h2\<triangleright>h0) \<and> (h3\<circ>h4\<triangleright>h1))"
proof -
  have f1: "h1 ## h2"
    using a1 by (simp add: tern_rel_qsl_def)    
  have f2: "h3 ## h4"
    using a2 by (simp add: tern_rel_qsl_def)    
  have f3: "h3 + h4 = h1"
    using a2 by (simp add: tern_rel_qsl_def)    
  then have "h3 ## h2"
    using f2 f1 sep_add_disjD by blast 
  then have f4: "h2 ## h3"
    by (simp add: sep_disj_commute)
  then have f5: "h2 + h4 ## h3"
    using f3 f2 f1
    by (simp add: sep_add_disjI2) 
  have "h4 ## h2"
    using f3 f2 f1
    using sep_add_disjD by blast 
  then show ?thesis
    using f5 f4
    by (metis a1 a2 sep_add_assoc sep_add_commute sep_disj_commute tern_rel_qsl_def) 
qed

text \<open>Soundness of $A$.\<close>
lemma a_qsl:
  "(\<exists>h5. Gamma \<and> (h3\<circ>h5\<triangleright>h0) \<and> (h2\<circ>h4\<triangleright>h5) \<and> (h1\<circ>h2\<triangleright>h0) \<and> (h3\<circ>h4\<triangleright>h1)) \<longrightarrow> Delta \<Longrightarrow>
  Gamma \<and> (h1\<circ>h2\<triangleright>h0) \<and> (h3\<circ>h4\<triangleright>h1) \<longrightarrow> Delta"
  using a_qsl_der by auto

lemma a_qsl_inv:
  "Gamma \<and> (h1\<circ>h2\<triangleright>h0) \<and> (h3\<circ>h4\<triangleright>h1) \<longrightarrow> Delta \<Longrightarrow>
  (\<exists>h5. Gamma \<and> (h3\<circ>h5\<triangleright>h0) \<and> (h2\<circ>h4\<triangleright>h5) \<and> (h1\<circ>h2\<triangleright>h0) \<and> (h3\<circ>h4\<triangleright>h1)) \<longrightarrow> Delta"
  by auto

lemma a_qsl_eq: 
  "((h1\<circ>h2\<triangleright>h0) \<and> (h3\<circ>h4\<triangleright>h1)) = 
  (\<exists>h5. (h3\<circ>h5\<triangleright>h0) \<and> (h2\<circ>h4\<triangleright>h5) \<and> (h1\<circ>h2\<triangleright>h0) \<and> (h3\<circ>h4\<triangleright>h1))"
  using a_qsl_der by fastforce
 
text \<open>Soundness of $P$.\<close>
lemma p_qsl:
  "Gamma \<and> (h1\<circ>h2\<triangleright>h0) \<and> h0 = h3 \<longrightarrow> Delta \<Longrightarrow>
  Gamma \<and> (h1\<circ>h2\<triangleright>h0) \<and> (h1\<circ>h2\<triangleright>h3) \<longrightarrow> Delta"
  using tern_rel_qsl_def by force
  
lemma p_qsl_inv:
  "Gamma \<and> (h1\<circ>h2\<triangleright>h0) \<and> (h1\<circ>h2\<triangleright>h3) \<longrightarrow> Delta \<Longrightarrow>
  Gamma \<and> (h1\<circ>h2\<triangleright>h0) \<and> h0 = h3 \<longrightarrow> Delta"
  by fastforce

lemma p_qsl_der:
  "(h1\<circ>h2\<triangleright>h0) \<Longrightarrow> (h1\<circ>h2\<triangleright>h3) \<Longrightarrow> (h1\<circ>h2\<triangleright>h0) \<and> h0 = h3"
  using tern_rel_qsl_def by auto
  
lemma p_qsl_eq: 
  "((h1\<circ>h2\<triangleright>h0) \<and> (h1\<circ>h2\<triangleright>h3)) = ((h1\<circ>h2\<triangleright>h0) \<and> h0 = h3)"
  using p_qsl_der by blast
  
lemma c_qsl:
  "Gamma \<and> (h1\<circ>h2\<triangleright>h0) \<and> h2 = h3 \<longrightarrow> Delta \<Longrightarrow>
  Gamma \<and> (h1\<circ>h2\<triangleright>h0) \<and> (h1\<circ>h3\<triangleright>h0) \<longrightarrow> Delta"
  unfolding tern_rel_qsl_def apply auto
  using sep_add_cancelD
  by (metis sep_add_commute sep_disj_commute) 

lemma c_qsl_inv:
  "Gamma \<and> (h1\<circ>h2\<triangleright>h0) \<and> (h1\<circ>h3\<triangleright>h0) \<longrightarrow> Delta \<Longrightarrow>
  Gamma \<and> (h1\<circ>h2\<triangleright>h0) \<and> h2 = h3 \<longrightarrow> Delta"
  by auto

lemma c_qsl_der:
  "(h1\<circ>h2\<triangleright>h0) \<Longrightarrow> (h1\<circ>h3\<triangleright>h0) \<Longrightarrow> (h1\<circ>h2\<triangleright>h0) \<and> h2 = h3"
  using c_qsl by blast

lemma c_qsl_eq:
  "((h1\<circ>h2\<triangleright>h0) \<and> (h1\<circ>h3\<triangleright>h0)) = ((h1\<circ>h2\<triangleright>h0) \<and> h2 = h3)"
  using c_qsl_der by auto

section \<open>Integrate the inference rules in proof search.\<close>

method try_empl_qsl = (
    match premises in P[thin]:"?s \<in> empty_qstatem_ass" \<Rightarrow> 
    \<open>insert empl_qsl_der[OF P]\<close>,
    simp?
    )

method try_empr_qsl = (
    match premises in P:"(1,stk,0) \<notin> empty_qstatem_ass" for stk \<Rightarrow> 
    \<open>insert empr_qsl_der[of stk]\<close>,
    simp?
    )

method try_starl_qsl = (
    match premises in P[thin]:"?s \<in> (?A \<and>\<^sup>*1 ?B)" \<Rightarrow> 
    \<open>insert starl_qsl_der[OF P], auto\<close>,
    simp?
    )

text \<open>Only apply the rule Eq on (0,h1,h2) where h1 and h2
  are not syntactically the same.\<close>

method try_eq_qsl = (
    match premises in P[thin]:"(0\<circ>?h1\<triangleright>?h2)" \<Rightarrow> 
    \<open>match P in 
    "(0\<circ>h\<triangleright>h)" for h \<Rightarrow> \<open>fail\<close>     
    \<bar>_ \<Rightarrow> \<open>insert eq_qsl_der[OF P], auto\<close>\<close>,
    simp?
    )

text \<open>We restrict that the rule P can't be applied to
  two syntactically identical ternary relational atoms.\<close>

method try_p_qsl = (
    match premises in P[thin]:"(h1\<circ>h2\<triangleright>h0)" for h0 h1 h2 \<Rightarrow> 
    \<open>match premises in "(h1\<circ>h2\<triangleright>h0)" \<Rightarrow> \<open>fail\<close>
    \<bar>P'[thin]:"(h1\<circ>h2\<triangleright>?h3)" \<Rightarrow> \<open>insert p_qsl_der[OF P P'], auto\<close>\<close>,
    simp?
    )

text \<open>We restrict that the rule C can't be applied to
  two syntactically identical ternary relational atoms.\<close>

method try_c_qsl = (
    match premises in P[thin]:"(h1\<circ>h2\<triangleright>h0)" for h0 h1 h2 \<Rightarrow> 
    \<open>match premises in "(h1\<circ>h2\<triangleright>h0)" \<Rightarrow> \<open>fail\<close>
    \<bar>P'[thin]:"(h1\<circ>?h3\<triangleright>h0)" \<Rightarrow> \<open>insert c_qsl_der[OF P P'], auto\<close>\<close>,
    simp?
    )

text \<open>We restrict that *R only applies to a pair of 
  a ternary relational and a formula once. 
  Here, we need to first try simp to unify heaps. 
  In the end, we try simp\_all to simplify all branches. 
  A similar strategy is used in -*L.\<close>

method try_starr_qsl0 = (
    simp?, 
    match premises in P:"(h1\<circ>h2\<triangleright>h)" and P':"(p,s,h) \<notin> (A \<and>\<^sup>*1 B)" for h1 h2 h A B p s \<Rightarrow> 
    \<open>match premises in "starr_applied_qsl h1 h2 h (A \<and>\<^sup>*1 B)" \<Rightarrow> \<open>fail\<close> 
    \<bar>_ \<Rightarrow> \<open>insert starr_qsl_der[OF P P'], auto\<close>\<close>, 
    simp_all?                                        
    )

method try_starr_qsl1 = (
    simp?, 
    match premises in P:"(h1\<circ>h2\<triangleright>(snd (snd s)))" 
      and P':"s \<notin> (A \<and>\<^sup>*1 B)" and P'':"fst s = p1 * p2" for h1 h2 A B s p1 p2 \<Rightarrow>  
      \<open>match premises in "starr_applied_qsl h1 h2 (snd (snd s)) (A \<and>\<^sup>*1 B)" \<Rightarrow> \<open>fail\<close> 
      \<bar>_ \<Rightarrow> \<open>insert starr_qsl_der[OF P'' P P'], auto\<close>\<close>,  
    simp_all?                                        
    )

method try_starr_qsl2 = (
    simp?,
    match premises in P:"((snd (snd s))\<circ>0\<triangleright>(snd (snd s)))" and P':"s \<notin> (A \<and>\<^sup>*1 B)" for A B s \<Rightarrow> 
      \<open>match premises in "starr_applied_qsl (snd (snd s)) 0 (snd (snd s)) (A \<and>\<^sup>*1 B)" \<Rightarrow> \<open>fail\<close> 
        \<bar>_ \<Rightarrow> \<open>insert starr_qsl_der4[OF P P'], auto\<close>\<close>,
    simp_all?
    )

method try_starr_qsl3 = (
    simp?,
    match premises in P:"(0\<circ>(snd (snd s))\<triangleright>(snd (snd s)))" and P':"s \<notin> (A \<and>\<^sup>*1 B)" for A B s \<Rightarrow> 
      \<open>match premises in "starr_applied_qsl 0 (snd (snd s)) (snd (snd s)) (A \<and>\<^sup>*1 B)" \<Rightarrow> \<open>fail\<close> 
        \<bar>_ \<Rightarrow> \<open>insert starr_qsl_der5[OF P P'], auto\<close>\<close>,
    simp_all?
    )

method try_starr_qsl4 = (
    simp?, 
    match premises in P:"(h1\<circ>h2\<triangleright>h)" and P''': "(snd (snd s)) = h"
      and P':"s \<notin> (A \<and>\<^sup>*1 B)" and P'':"fst s = p1 * p2" for h1 h2 h A B s p1 p2 \<Rightarrow>  
      \<open>match premises in "starr_applied_qsl h1 h2 h (A \<and>\<^sup>*1 B)" \<Rightarrow> \<open>fail\<close> 
      \<bar>_ \<Rightarrow> \<open>insert starr_qsl_der2[OF P'' P P' P'''], auto\<close>\<close>,  
    simp_all?                                        
    )

method try_starr_qsl5 = (
    simp?, 
    match premises in P:"(h1\<circ>h2\<triangleright>h)" and P''': "(snd (snd s)) = h"
      and P':"s \<notin> (A \<and>\<^sup>*1 B)" and P'':"fst s = 1" for h1 h2 h A B s \<Rightarrow>  
      \<open>match premises in "starr_applied_qsl h1 h2 h (A \<and>\<^sup>*1 B)" \<Rightarrow> \<open>fail\<close> 
      \<bar>_ \<Rightarrow> \<open>insert starr_qsl_der3[OF P'' P P' P'''], auto\<close>\<close>,  
    simp_all?                                        
    )

method try_starr_qsl6 = (
    simp?,
    match premises in P:"(h\<circ>0\<triangleright>h)" and 
      P':"s \<notin> (A \<and>\<^sup>*1 B)" and P'': "(snd (snd s)) = h" for A B s h \<Rightarrow> 
      \<open>match premises in "starr_applied_qsl h 0 h (A \<and>\<^sup>*1 B)" \<Rightarrow> \<open>fail\<close> 
        \<bar>_ \<Rightarrow> \<open>insert starr_qsl_der6[OF P P' P''], auto\<close>\<close>,
    simp_all?
    )

method try_starr_qsl7 = (
    simp?,
    match premises in P:"(0\<circ>q\<triangleright>q)" and 
      P':"s \<notin> (A \<and>\<^sup>*1 B)" and P'': "(snd (snd s)) = q" for A B s q \<Rightarrow> 
      \<open>match premises in "starr_applied_qsl 0 q q (A \<and>\<^sup>*1 B)" \<Rightarrow> \<open>fail\<close> 
        \<bar>_ \<Rightarrow> \<open>insert starr_qsl_der7[OF P P' P''], auto\<close>\<close>,
    simp_all?
    )

text \<open>We restrict that the U rule is only applicable to a world h
  when (h,0,h) is not in the premises. There are two cases:
  (1) We pick a ternary relational atom (h1,h2,h0),
  and check if (h1,0,h1) occurs in the premises, if not, 
  apply U on h1. Otherwise, check other ternary relational atoms.
  (2) We pick a labelled formula (A h), 
  and check if (h,0,h) occurs in the premises, if not,
  apply U on h. Otherwise, check other labelled formulae.\<close>

method try_u_qsl_tern = (
    match premises in 
    P:"(h1\<circ>h2\<triangleright>h0)" for h1 h2 h0 \<Rightarrow>
    \<open>match premises in 
    "(h1\<circ>0\<triangleright>h1)" \<Rightarrow> \<open>match premises in 
    "(h2\<circ>0\<triangleright>h2)" \<Rightarrow> \<open>match premises in 
    I1:"(h0\<circ>0\<triangleright>h0)" \<Rightarrow> \<open>fail\<close>
    \<bar>_ \<Rightarrow> \<open>insert u_qsl_der[of h0]\<close>\<close>
    \<bar>_ \<Rightarrow> \<open>insert u_qsl_der[of h2]\<close>\<close>
    \<bar>_ \<Rightarrow> \<open>insert u_qsl_der[of h1]\<close>\<close>,
    simp?
    )

method try_u_qsl_form = (
    match premises in 
    P':"(_,_,(h::QStateM)) \<in> _" for h \<Rightarrow>
      \<open>match premises in "(h\<circ>0\<triangleright>h)" \<Rightarrow> \<open>fail\<close>
      \<bar>"(0\<circ>0\<triangleright>0)" and "h = 0" \<Rightarrow> \<open>fail\<close>
      \<bar>"(0\<circ>0\<triangleright>0)" and "0 = h" \<Rightarrow> \<open>fail\<close>
      \<bar>_ \<Rightarrow> \<open>insert u_qsl_der[of h]\<close>\<close>
    \<bar>P'':"(s::('s state)) \<in> _" for s \<Rightarrow>
      \<open>match premises in "((snd (snd s))\<circ>0\<triangleright>(snd (snd s)))" \<Rightarrow> \<open>fail\<close>
      \<bar>"(0\<circ>0\<triangleright>0)" and "(snd (snd s)) = 0" \<Rightarrow> \<open>fail\<close>
      \<bar>"(0\<circ>0\<triangleright>0)" and "0 = (snd (snd s))" \<Rightarrow> \<open>fail\<close>
      \<bar>_ \<Rightarrow> \<open>insert u_qsl_der[of "(snd (snd s))"]\<close>\<close>,
    simp?
    )

text \<open>We restrict that the E rule is only applicable to
  (h1,h2,h0) when (h2,h1,h0) is not in the premises.\<close>

method try_e_qsl = (
    match premises in P:"(h1\<circ>h2\<triangleright>h0)" for h1 h2 h0 \<Rightarrow> 
    \<open>match premises in "(h2\<circ>h1\<triangleright>h0)" \<Rightarrow> \<open>fail\<close>
    \<bar>_ \<Rightarrow> \<open>insert e_qsl_der[OF P], auto\<close>\<close>,
    simp?
    )

text \<open>This rule is made just for QSL. 
  We restrict that the MC rule is only applicable to
  p = p1 * p2 when p = p2 * p1 is not in the premises.\<close>

method try_mc_qsl = (
    match premises in P:"p = p1 * p2" for p p1 p2 \<Rightarrow> 
    \<open>match premises in "p = p2 * p1" \<Rightarrow> \<open>fail\<close>
    \<bar>_ \<Rightarrow> \<open>insert mc_qsl_der[OF P]\<close>\<close>,
    simp?
    )

text \<open>We restrict that the A rule is only applicable to 
  (h1,h2,h0) and (h3,h4,h1) when (h3,h,h0) and (h2,h4,h) 
  or any commutative variants of the two 
  do not occur in the premises, for some h. 
  Additionally, we do not allow A to be applied to two identical 
  ternary relational atoms. 
  We further restrict that the leaves must not be 0, 
  because otherwise this application does not gain anything.\<close>

method try_a_qsl = (
    match premises in "(h1\<circ>h2\<triangleright>h0)" for h0 h1 h2 \<Rightarrow> 
    \<open>match premises in 
    "(0\<circ>h2\<triangleright>h0)" \<Rightarrow> \<open>fail\<close>
    \<bar>"(h1\<circ>0\<triangleright>h0)" \<Rightarrow> \<open>fail\<close>
    \<bar>"(h1\<circ>h2\<triangleright>0)" \<Rightarrow> \<open>fail\<close>
    \<bar>P[thin]:"(h1\<circ>h2\<triangleright>h0)" \<Rightarrow> 
    \<open>match premises in
    P':"(h3\<circ>h4\<triangleright>h1)" for h3 h4 \<Rightarrow> \<open>match premises in
    "(0\<circ>h4\<triangleright>h1)" \<Rightarrow> \<open>fail\<close>
    \<bar>"(h3\<circ>0\<triangleright>h1)" \<Rightarrow> \<open>fail\<close>
    \<bar>"(_\<circ>h3\<triangleright>h0)" \<Rightarrow> \<open>fail\<close>
    \<bar>"(h3\<circ>_\<triangleright>h0)" \<Rightarrow> \<open>fail\<close>
    \<bar>"(h2\<circ>h4\<triangleright>_)" \<Rightarrow> \<open>fail\<close>
    \<bar>"(h4\<circ>h2\<triangleright>_)" \<Rightarrow> \<open>fail\<close>       
    \<bar>_ \<Rightarrow> \<open>insert P P', drule a_qsl_der, auto\<close>\<close>\<close>\<close>,
    simp?
    )

text \<open>A smarter but restricted heuristic to apply *R.\<close>

method try_starr_qsl_guided0 = (
    simp?,
    match premises in P:"(h1\<circ>h2\<triangleright>h)" and P':"(p,s,h) \<notin> (A \<and>\<^sup>*1 B)" for h1 h2 h A B p s \<Rightarrow> 
    \<open>match premises in "starr_applied_qsl h1 h2 h (A \<and>\<^sup>*1 B)" \<Rightarrow> \<open>fail\<close> 
    \<bar>"(_,_,h1) \<in> A" \<Rightarrow> \<open>insert starr_qsl_der[OF P P'], auto\<close>
    \<bar>"(_,_,h2) \<in> B" \<Rightarrow> \<open>insert starr_qsl_der[OF P P'], auto\<close>\<close>,
    simp_all?
    )

method try_starr_qsl_guided1 = (
    simp?,
    match premises in P:"(h1\<circ>h2\<triangleright>(snd (snd s)))" 
      and P':"s \<notin> (A \<and>\<^sup>*1 B)" and P'':"fst s = p1 * p2" for h1 h2 A B s p1 p2 \<Rightarrow> 
      \<open>match premises in "starr_applied_qsl h1 h2 (snd (snd s)) (A \<and>\<^sup>*1 B)" \<Rightarrow> \<open>fail\<close> 
        \<bar>"(_,_,h1) \<in> A" \<Rightarrow> \<open>insert starr_qsl_der[OF P'' P P'], auto\<close>
        \<bar>"(_,_,h2) \<in> B" \<Rightarrow> \<open>insert starr_qsl_der[OF P'' P P'], auto\<close>\<close>,
    simp_all?
    )

method try_starr_qsl_guided2 = (
    simp?,
    match premises in P:"((snd (snd s))\<circ>0\<triangleright>(snd (snd s)))" and P':"s \<notin> (A \<and>\<^sup>*1 B)" for A B s \<Rightarrow> 
      \<open>match premises in "starr_applied_qsl (snd (snd s)) 0 (snd (snd s)) (A \<and>\<^sup>*1 B)" \<Rightarrow> \<open>fail\<close> 
        \<bar>"(_,_,(snd (snd s))) \<in> A" \<Rightarrow> \<open>insert starr_qsl_der4[OF P P'], auto\<close>
        \<bar>"s \<in> A" \<Rightarrow> \<open>insert starr_qsl_der4[OF P P'], auto\<close>
        \<bar>"(_,_,0) \<in> B" \<Rightarrow> \<open>insert starr_qsl_der4[OF P P'], auto\<close>\<close>,
    simp_all?
    )

method try_starr_qsl_guided3 = (
    simp?,
    match premises in P:"(0\<circ>(snd (snd s))\<triangleright>(snd (snd s)))" and P':"s \<notin> (A \<and>\<^sup>*1 B)" for A B s \<Rightarrow> 
      \<open>match premises in "starr_applied_qsl 0 (snd (snd s)) (snd (snd s)) (A \<and>\<^sup>*1 B)" \<Rightarrow> \<open>fail\<close> 
        \<bar>"(_,_,0) \<in> A" \<Rightarrow> \<open>insert starr_qsl_der5[OF P P'], auto\<close>
        \<bar>"(_,_,(snd (snd s))) \<in> B" \<Rightarrow> \<open>insert starr_qsl_der5[OF P P'], auto\<close>
        \<bar>"s \<in> B" \<Rightarrow> \<open>insert starr_qsl_der5[OF P P'], auto\<close>\<close>,
    simp_all?
    )

method try_starr_qsl_guided4 = (
    simp?,
    match premises in P:"(h1\<circ>h2\<triangleright>h)" and P''': "(snd (snd s)) = h"
      and P':"s \<notin> (A \<and>\<^sup>*1 B)" and P'':"fst s = p1 * p2" for h1 h2 h A B s p1 p2 \<Rightarrow>  
      \<open>match premises in "starr_applied_qsl h1 h2 h (A \<and>\<^sup>*1 B)" \<Rightarrow> \<open>fail\<close> 
        \<bar>"(_,_,h1) \<in> A" \<Rightarrow> \<open>insert starr_qsl_der2[OF P'' P P' P'''], auto\<close>
        \<bar>"(_,_,h2) \<in> B" \<Rightarrow> \<open>insert starr_qsl_der2[OF P'' P P' P'''], auto\<close>\<close>,
    simp_all?
    )

method try_starr_qsl_guided5 = (
    simp?,
    match premises in P:"(h1\<circ>h2\<triangleright>h)" and P''': "(snd (snd s)) = h"
      and P':"s \<notin> (A \<and>\<^sup>*1 B)" and P'':"fst s = 1" for h1 h2 h A B s \<Rightarrow>  
      \<open>match premises in "starr_applied_qsl h1 h2 h (A \<and>\<^sup>*1 B)" \<Rightarrow> \<open>fail\<close>
        \<bar>"(_,_,h1) \<in> A" \<Rightarrow> \<open>insert starr_qsl_der3[OF P'' P P' P'''], auto\<close>
        \<bar>"(_,_,h2) \<in> B" \<Rightarrow> \<open>insert starr_qsl_der3[OF P'' P P' P'''], auto\<close>\<close>,
    simp_all?
    )

method try_starr_qsl_guided6 = (
    simp?,
    match premises in P:"(h\<circ>0\<triangleright>h)" and 
      P':"s \<notin> (A \<and>\<^sup>*1 B)" and P'': "(snd (snd s)) = h" for A B s h \<Rightarrow> 
      \<open>match premises in "starr_applied_qsl h 0 h (A \<and>\<^sup>*1 B)" \<Rightarrow> \<open>fail\<close> 
        \<bar>"(_,_,(snd (snd s))) \<in> A" \<Rightarrow> \<open>insert starr_qsl_der6[OF P P' P''], auto\<close>
        \<bar>"s \<in> A" \<Rightarrow> \<open>insert starr_qsl_der6[OF P P' P''], auto\<close>
        \<bar>"(_,_,0) \<in> B" \<Rightarrow> \<open>insert starr_qsl_der6[OF P P' P''], auto\<close>\<close>,
    simp_all?
    )

method try_starr_qsl_guided7 = (
    simp?,
    match premises in P:"(0\<circ>q\<triangleright>q)" and 
      P':"s \<notin> (A \<and>\<^sup>*1 B)" and P'': "(snd (snd s)) = q" for A B s q \<Rightarrow> 
      \<open>match premises in "starr_applied_qsl 0 q q (A \<and>\<^sup>*1 B)" \<Rightarrow> \<open>fail\<close> 
        \<bar>"(_,_,0) \<in> A" \<Rightarrow> \<open>insert starr_qsl_der7[OF P P' P''], auto\<close>
        \<bar>"(_,_,(snd (snd s))) \<in> B" \<Rightarrow> \<open>insert starr_qsl_der7[OF P P' P''], auto\<close>
        \<bar>"s \<in> B" \<Rightarrow> \<open>insert starr_qsl_der7[OF P P' P''], auto\<close>\<close>,
    simp_all?
    )

text \<open>In case the conclusion is not False, we normalise the goal as below.\<close>

method norm_goal = (
    match conclusion in "False" \<Rightarrow> \<open>fail\<close>
    \<bar>_ \<Rightarrow> \<open>rule ccontr\<close>,
    simp?
    )

text \<open>The tactic for separata for QSL (called qsep). We first try to simplify the problem
  with auto simp add: sep\_conj\_ac, which ought to solve many problems.
  Then we apply the "true" invertible rules and structural rules 
  which unify worlds as much as possible, followed by auto to simplify the goals. 
  Then we apply *R and other structural rules.\<close>

method qsep_invertible = 
  ((try_empr_qsl
    |try_empl_qsl (* This section contains invertible rules. Apply as often as possible. *)
    |try_starl_qsl
    (*|try_magicr_qsl N/A *)
    (*|try_iu_qsl N/A *)
    (*|try_d_qsl N/A *)
    |try_eq_qsl     
    |try_p_qsl
    |try_c_qsl
    |try_starr_qsl_guided0,(metis prod.collapse)?
    |try_starr_qsl_guided1,(metis prod.collapse)?
    |try_starr_qsl_guided2,(metis prod.collapse)?
    |try_starr_qsl_guided3,(metis prod.collapse)?
    |try_starr_qsl_guided4,(metis prod.collapse)?
    |try_starr_qsl_guided5,(metis prod.collapse)?
    |try_starr_qsl_guided6,(metis prod.collapse)?
    |try_starr_qsl_guided7,(metis prod.collapse)?
    (*|try_magicl_qsl_guided N/A *)
   )+,auto?)

method qsep_struct = 
  (try_u_qsl_tern (* This section contains structural rules. *)
   |try_e_qsl
   |try_mc_qsl
   |try_a_qsl)+

method qsep_non_term =
  try_starr_qsl0,(metis prod.collapse)? (* This section contains *R. *)
  |try_starr_qsl1,(metis prod.collapse)?
  |try_starr_qsl2,(metis prod.collapse)?
  |try_starr_qsl3,(metis prod.collapse)?
  |try_starr_qsl4,(metis prod.collapse)?
  |try_starr_qsl5,(metis prod.collapse)?
  |try_starr_qsl6,(metis prod.collapse)?
  |try_starr_qsl7,(metis prod.collapse)?
  (*|try_magicl_qsl*)
          
method qsep_init = norm_goal?,auto?

method qsep_term = qsep_init,(qsep_invertible|qsep_struct|try_u_qsl_form)+

method qsep = qsep_init,                                
  (qsep_term, (* This part applies the terminating rules as much as possible. *)
    (smt (verit, ccfv_threshold) Q_sep_dis_set_intro eq_Qsep_dis_sets mult.assoc mult.commute 
        starl_qsl_sub tern_rel_qsl_def a_qsl_der ab_semigroup_mult_class.mult_ac(1) 
        prod.exhaust_sel mult.left_commute)?
  |qsep_non_term (* This part applies the non-terminating rules. *)
  )+ (* This tactic may not terminate! *)

method qsep2 = qsep_init,                                
  (qsep_term, (* This part applies the terminating rules as much as possible. *)
    (smt (verit, ccfv_threshold) Q_sep_dis_set_intro eq_Qsep_dis_sets mult.assoc mult.commute 
        starl_qsl_sub tern_rel_qsl_def a_qsl_der ab_semigroup_mult_class.mult_ac(1) 
        prod.exhaust_sel)?
  |qsep_non_term (* This part applies the non-terminating rules. *)
  )+ (* This tactic may not terminate! *)

method qsep3 = qsep_init,                                
  (qsep_term, (* This part applies the terminating rules as much as possible. *)
    (smt Q_sep_dis_set_intro eq_Qsep_dis_sets mult.assoc mult.commute 
        starl_qsl_sub tern_rel_qsl_def a_qsl_der ab_semigroup_mult_class.mult_ac(1) 
        prod.exhaust_sel mult.left_commute)?
  |qsep_non_term (* This part applies the non-terminating rules. *)
  )+ (* This tactic may not terminate! *)

text \<open>In what follows, we prove (some of) the inference rules in Figure 8 of Le at al.'s paper.\<close>

text \<open>We begin with the trivial ones in Figure 8(d), which may not even need qsep.\<close>

lemma "s \<in> A \<longrightarrow> True"
  by simp

lemma "False \<longrightarrow> s \<in> A"
  by simp

text \<open>We do not have the notion of substitution in formula, so the rule $\overset{S}{=}$
is skipped.\<close>

text \<open>The rule $*E$ in Figure 8 of Le at al.'s paper.
Sledgehammer can prove the first direction quickly but can't prove the second direction.\<close>

lemma "(s \<in> (empty_qstatem_ass \<and>\<^sup>*1 A)) \<longrightarrow> (s \<in> A)"
  by qsep

lemma "(s \<in> A) \<longrightarrow> (s \<in> (empty_qstatem_ass \<and>\<^sup>*1 A))"
  by qsep

text \<open>The rule $*C$ in Figure 8 of Le at al.'s paper.
Sledgehammer can prove this one quickly\<close>

lemma "(s \<in> (A \<and>\<^sup>*1 B) \<longrightarrow> s \<in> (B \<and>\<^sup>*1 A))"
  by qsep

text \<open>The rule $*A$ in Figure 8 of Le at al.'s paper. The reasoning involves arithmetics over
  probabilities, which is not a part of the sequent calculus, and that's why reasoning
  using Isabelle/HOL is required.

However, Sledgehammer could not directly find a proof, but after applying qsep_term, 
Sledgehammer can find a proof. This illustrates that the tactics helps.\<close>

lemma "s \<in> ((A \<and>\<^sup>*1 B) \<and>\<^sup>*1 C) \<longrightarrow> s \<in> (A \<and>\<^sup>*1 (B \<and>\<^sup>*1 C))"
  by qsep

text \<open>The rule $*^{\vdash}$ in Figure 8 of Le at al.'s paper.
Sledgehammer can easily find a proof using a1.\<close>

lemma assumes a1: "\<forall>s.(s::'s state) \<in> A \<longrightarrow> s \<in> B"
  shows "s' \<in> (A \<and>\<^sup>*1 C) \<longrightarrow> s' \<in> (B \<and>\<^sup>*1 C)"
proof -
  show ?thesis
    apply qsep_term
    using a1 by auto
qed

text \<open>We define a pure formula as one that is independent of the probability and the quantum heap.\<close>
definition pure:: "(('s state) set) \<Rightarrow> bool" where
"pure A \<equiv> \<forall>p s q p' q'. ((p,s,q) \<in> A) = ((p',s,q') \<in> A)"

text \<open>The rule $\overset{-}{*}$ is proven below.\<close> 
lemma "pure A \<and> pure B \<and> s \<in> (A \<and>\<^sup>*1 B) \<longrightarrow> s \<in> (A \<inter> B)"
  unfolding pure_def
  by qsep

lemma "pure A \<and> pure B \<and> s \<in> (A \<inter> B) \<longrightarrow> s \<in> (A \<and>\<^sup>*1 B)"
  unfolding pure_def
  by qsep


text \<open>The rule $\overset{-}{*^{\land}}$ is proven below.\<close>
lemma "pure A \<and> s \<in> (A \<inter> (B \<and>\<^sup>*1 C)) \<longrightarrow> s \<in> ((A \<inter> B) \<and>\<^sup>*1 C)"
  unfolding pure_def
  by qsep

lemma "pure A \<and> s \<in> ((A \<inter> B) \<and>\<^sup>*1 C) \<longrightarrow> s \<in> (A \<inter> (B \<and>\<^sup>*1 C))"
  unfolding pure_def
  by qsep            

text \<open>The rule $*^{\land}$ in Figure 8 of Le at al.'s paper. 
Note that this rule is one-direction.

Note: we use intersection to encode and and use union to encode or.

Sledgehammer takes a while to find a proof.\<close>

lemma "s \<in> (A \<and>\<^sup>*1 (B \<inter> C)) \<longrightarrow> s \<in> ((A \<and>\<^sup>*1 B) \<inter> (A \<and>\<^sup>*1 C))"
  by qsep

text \<open>The rule $*^{\land}$ in Figure 8 of Le at al.'s paper.
Note that this rule is bidirectional. Sledgehammer needs a long time to prove the second 
direction.\<close>

lemma "s \<in> (A \<and>\<^sup>*1 (B \<union> C)) \<longrightarrow> s \<in> ((A \<and>\<^sup>*1 B) \<union> (A \<and>\<^sup>*1 C))"
  by qsep

lemma "s \<in> ((A \<and>\<^sup>*1 B) \<union> (A \<and>\<^sup>*1 C)) \<longrightarrow> s \<in> (A \<and>\<^sup>*1 (B \<union> C))"
  by qsep

text \<open>The rule P\vdash in Figure 8 of Le at al.'s paper.
The first lemma is without constraints. The second lemma has constraints. \<close>

lemma "\<forall>s.(s::'s state) \<in> A \<longrightarrow> s \<in> B \<Longrightarrow> s' \<in> A\<smile>p \<longrightarrow> s' \<in> B\<smile>p" 
  by (smt (verit, best) image_iff prob_assert_def) 

lemma "0 < p \<and> p \<le> 1 \<Longrightarrow> 0 < fst s' \<and> fst s' \<le> 1 \<Longrightarrow> fst s' \<le> p \<Longrightarrow> 
  \<forall>s.(s::'s state) \<in> A \<longrightarrow> s \<in> B \<Longrightarrow> s' \<in> A\<smile>p \<longrightarrow> s' \<in> B\<smile>p" 
  using dotl_qsl_der dotr_qsl_der by blast 

text \<open>The rule P^I in Figure 8 of Le at al.'s paper.
The first two lemmas don't have constraints, the last two lemmas have.\<close>

lemma "s \<in> A\<smile>1 \<longrightarrow> s \<in> A"
  by (simp add: prob_assert_def)

lemma "s \<in> A \<longrightarrow> s \<in> A\<smile>1"
  by (simp add: prob_assert_def)

lemma "0 < fst s \<and> fst s \<le> 1 \<Longrightarrow> 
  s \<in> A\<smile>1 \<longrightarrow> s \<in> A"
  using dotl_qsl_der 
  by (metis div_by_1 le_numeral_extra(4) less_numeral_extra(1) surjective_pairing) 

lemma "0 < fst s \<and> fst s \<le> 1 \<Longrightarrow> 
  s \<in> A \<longrightarrow> s \<in> A\<smile>1"
  using dotl_qsl_der dotr_qsl_der
  by (smt (verit, del_insts) div_by_1 prod.collapse)

text \<open>The rule P\bot in Figure 8 of Le at al.'s paper.\<close>

lemma "(p \<le> 0 \<or> p > 1) \<and> s \<in> A\<smile>p \<longrightarrow> False"
  sorry (* With constraints it's trivial though. *)

lemma "0 < p \<and> p \<le> 1 \<Longrightarrow> 0 < fst s \<and> fst s \<le> 1 \<Longrightarrow> fst s \<le> p \<Longrightarrow> 
  (p \<le> 0 \<or> p > 1) \<and> s \<in> A\<smile>p \<longrightarrow> False"
  by auto

text \<open>The rule P^bar in Figure 8 of Le at al.'s paper.
The first lemma is an auxiliary lemma.
The second and the third lemmas are proven using definitions, which means the rule in the POPL paper
is sound.
The last two lemmas are proven using labelled sequent calculus rules.\<close>

lemma "0 < p \<and> p \<le> 1 \<Longrightarrow> 0 < fst s \<and> fst s \<le> 1 \<Longrightarrow> fst s \<le> p \<Longrightarrow> 
  pure A \<Longrightarrow> s \<in> A\<smile>p \<longrightarrow> s \<in> A"
  unfolding pure_def prob_assert_def apply auto
  by blast   

lemma "0 < p \<and> p \<le> 1 \<Longrightarrow> 0 < fst s \<and> fst s \<le> 1 \<Longrightarrow> fst s \<le> p \<Longrightarrow> 
  pure A \<Longrightarrow> s \<in> (A \<inter> B)\<smile>p \<longrightarrow> s \<in> (A \<inter> (B\<smile>p))"
  unfolding pure_def prob_assert_def apply auto
  by blast

lemma "0 < p \<and> p \<le> 1 \<Longrightarrow> 0 < fst s \<and> fst s \<le> 1 \<Longrightarrow> fst s \<le> p \<Longrightarrow> 
  pure A \<Longrightarrow> s \<in> (A \<inter> (B\<smile>p)) \<longrightarrow> s \<in> (A \<inter> B)\<smile>p"
  unfolding pure_def prob_assert_def apply auto
proof -
  fix a :: real and aa :: 'a and b :: QStateM
  assume a1: "\<forall>p s q p' q'. ((p, s, q) \<in> A) = ((p', s, q') \<in> A)"
  assume a2: "(a * p, aa, b) \<in> A"
  assume a3: "(a, aa, b) \<in> B"
  have "(a, aa, b) \<in> A"
    using a2 a1 by blast
  then have f4: "(a, aa, b) \<in> A \<inter> B"
    using a3 by blast
  have "(a * p, aa, b) = (fst (a, aa, b) * p, snd (a, aa, b))"
    by simp
  then show "(a * p, aa, b) \<in> (\<lambda>pa. (fst pa * p, snd pa)) ` (A \<inter> B)"
    using f4 by blast
qed

lemma "0 < p \<and> p \<le> 1 \<Longrightarrow> 0 < fst s \<and> fst s \<le> 1 \<Longrightarrow> fst s \<le> p \<Longrightarrow> 
  pure A \<Longrightarrow> s \<in> (A \<inter> B)\<smile>p \<longrightarrow> s \<in> (A \<inter> (B\<smile>p))"
  unfolding pure_def using dotl_qsl_der dotr_qsl_der
  by (metis Int_iff prod.collapse)
  
lemma "0 < p \<and> p \<le> 1 \<Longrightarrow> 0 < fst s \<and> fst s \<le> 1 \<Longrightarrow> fst s \<le> p \<Longrightarrow> 
  pure A \<Longrightarrow> s \<in> (A \<inter> (B\<smile>p)) \<longrightarrow> s \<in> (A \<inter> B)\<smile>p"
  unfolding pure_def using dotl_qsl_der dotr_qsl_der
  by (metis Int_iff prod.collapse)
  
text \<open>The rule P^J in Figure 8 of Le at al.'s paper.
The first two lemmas are proven using definitions, which means the rule in the POPL paper
is sound.
The last two lemmas are proven using labelled sequent calculus rules.\<close>

lemma "0 < p \<and> p \<le> 1 \<Longrightarrow> 0 < p' \<and> p' \<le> 1 \<Longrightarrow> 0 < fst s \<and> fst s \<le> 1 \<Longrightarrow> fst s \<le> p \<Longrightarrow> fst s \<le> p*p' \<Longrightarrow> 
  s \<in> (A\<smile>p')\<smile>p \<longrightarrow> s \<in> (A\<smile>(p*p')) \<and> 0 < p \<and> p \<le> 1 \<and> 0 < p' \<and> p' \<le> 1"
  unfolding pure_def prob_assert_def apply auto
  by (smt (verit) fst_conv image_iff mc_qsl_der mult.left_commute snd_conv)
  
lemma "0 < p \<and> p \<le> 1 \<Longrightarrow> 0 < p' \<and> p' \<le> 1 \<Longrightarrow> 0 < fst s \<and> fst s \<le> 1 \<Longrightarrow> fst s \<le> p \<Longrightarrow> fst s \<le> p*p' \<Longrightarrow> 
  s \<in> (A\<smile>(p*p')) \<and> 0 < p \<and> p \<le> 1 \<and> 0 < p' \<and> p' \<le> 1 \<longrightarrow> s \<in> (A\<smile>p')\<smile>p"
  unfolding pure_def prob_assert_def apply auto
proof -
  fix a :: real and aa :: 'a and b :: QStateM
  assume a1: "(a, aa, b) \<in> A"
  assume a2: "s = (a * (p * p'), aa, b)"
  obtain pp :: "(real \<times> 'a \<times> QStateM) set \<Rightarrow> (real \<times> 'a \<times> QStateM \<Rightarrow> real \<times> 'a \<times> QStateM) \<Rightarrow> real \<times> 'a \<times> QStateM \<Rightarrow> real \<times> 'a \<times> QStateM" where
    f3: "\<forall>p f P. (p \<in> f ` P \<or> (\<forall>pa. f pa \<noteq> p \<or> pa \<notin> P)) \<and> (f (pp P f p) = p \<and> pp P f p \<in> P \<or> p \<notin> f ` P)"
    by (metis (no_types) image_iff)
  have f4: "(aa, b) = snd s"
    using a2 by simp
  have f5: "\<forall>r ra rb. (rb::real) * (r * ra) = ra * (rb * r)"
    by force
  have f6: "\<forall>r p. (fst (r, p::'a \<times> QStateM) * p', snd (r, p)) = (p' * r, p)"
    by auto
  have f7: "\<forall>r pa. (fst (r, pa::'a \<times> QStateM) * p, snd (r, pa)) = (p * r, pa)"
    by force
  have "(p' * a, snd s) \<in> (\<lambda>p. (fst p * p', snd p)) ` A"
    using f6 f4 f3 a1 by (metis (lifting))
  then show "(a * (p * p'), aa, b) \<in> (\<lambda>pa. (fst pa * p, snd pa)) ` (\<lambda>p. (fst p * p', snd p)) ` A"
    using f7 f5 f4 f3 by (smt (z3))
qed

lemma "0 < p \<and> p \<le> 1 \<Longrightarrow> 0 < p' \<and> p' \<le> 1 \<Longrightarrow> 0 < fst s \<and> fst s \<le> 1 \<Longrightarrow> fst s \<le> p \<Longrightarrow> fst s \<le> p*p' \<Longrightarrow> 
  s \<in> (A\<smile>p')\<smile>p \<longrightarrow> s \<in> (A\<smile>(p*p')) \<and> 0 < p \<and> p \<le> 1 \<and> 0 < p' \<and> p' \<le> 1"
  unfolding pure_def using dotl_qsl_der dotr_qsl_der
  by (smt (verit, del_insts) divide_divide_eq_left divide_le_eq_1_pos divide_pos_pos fst_conv snd_conv)

lemma "0 < p \<and> p \<le> 1 \<Longrightarrow> 0 < p' \<and> p' \<le> 1 \<Longrightarrow> 0 < fst s \<and> fst s \<le> 1 \<Longrightarrow> fst s \<le> p \<Longrightarrow> fst s \<le> p*p' \<Longrightarrow> 
  s \<in> (A\<smile>(p*p')) \<and> 0 < p \<and> p \<le> 1 \<and> 0 < p' \<and> p' \<le> 1 \<longrightarrow> s \<in> (A\<smile>p')\<smile>p"
  unfolding pure_def using dotl_qsl_der dotr_qsl_der
  by (smt (verit) divide_divide_eq_left fst_conv image_iff nonzero_divide_eq_eq prob_assert_def snd_conv)

text \<open>The rule P^\land in Figure 8 of Le at al.'s paper.
The first two lemmas are proven using definitions (without assumptions), 
which means the rule in the POPL paper is sound.
The last two lemmas are proven using labelled sequent calculus rules (with assumptions).\<close>

lemma "s \<in> (A \<inter> B)\<smile>p \<longrightarrow> s \<in> ((A\<smile>p) \<inter> (B\<smile>p))"
  unfolding prob_assert_def by auto

lemma "s \<in> ((A\<smile>p) \<inter> (B\<smile>p)) \<longrightarrow> s \<in> (A \<inter> B)\<smile>p"
  unfolding prob_assert_def by auto

lemma "0 < p \<and> p \<le> 1 \<Longrightarrow> 0 < fst s \<and> fst s \<le> 1 \<Longrightarrow> fst s \<le> p \<Longrightarrow> 
  s \<in> (A \<inter> B)\<smile>p \<longrightarrow> s \<in> ((A\<smile>p) \<inter> (B\<smile>p))"
  using dotl_qsl_der dotr_qsl_der by blast

lemma "0 < p \<and> p \<le> 1 \<Longrightarrow> 0 < fst s \<and> fst s \<le> 1 \<Longrightarrow> fst s \<le> p \<Longrightarrow> 
  s \<in> ((A\<smile>p) \<inter> (B\<smile>p)) \<longrightarrow> s \<in> (A \<inter> B)\<smile>p"
  using dotl_qsl_der dotr_qsl_der by blast

text \<open>The rule P^\lor in Figure 8 of Le at al.'s paper.
The first two lemmas are proven using definitions (without assumptions), 
which means the rule in the POPL paper is sound.
The last two lemmas are proven using labelled sequent calculus rules (with assumptions).\<close>

lemma "s \<in> (A \<union> B)\<smile>p \<longrightarrow> s \<in> ((A\<smile>p) \<union> (B\<smile>p))"
  unfolding prob_assert_def by auto

lemma "s \<in> ((A\<smile>p) \<union> (B\<smile>p)) \<longrightarrow> s \<in> (A \<union> B)\<smile>p"
  unfolding prob_assert_def by auto

lemma "0 < p \<and> p \<le> 1 \<Longrightarrow> 0 < fst s \<and> fst s \<le> 1 \<Longrightarrow> fst s \<le> p \<Longrightarrow> 
  s \<in> (A \<union> B)\<smile>p \<longrightarrow> s \<in> ((A\<smile>p) \<union> (B\<smile>p))"
  using dotl_qsl_der dotr_qsl_der by blast

lemma "0 < p \<and> p \<le> 1 \<Longrightarrow> 0 < fst s \<and> fst s \<le> 1 \<Longrightarrow> fst s \<le> p \<Longrightarrow> 
  s \<in> ((A\<smile>p) \<union> (B\<smile>p)) \<longrightarrow> s \<in> (A \<union> B)\<smile>p"
  using dotl_qsl_der dotr_qsl_der by blast

text \<open>Some other examples.\<close>

text \<open>Sledgehammer can't prove this one.\<close>
lemma "(s \<in> empty_qstatem_ass \<and> s \<in> A) \<longrightarrow> (s \<in> (A \<and>\<^sup>*1 A))"
  by qsep

text \<open>Sledgehammer can't prove this one.\<close>
lemma "(s \<in> A) \<longrightarrow> (\<not> ((s \<notin> (A \<and>\<^sup>*1 B)) \<and> (s \<notin> (A \<and>\<^sup>*1 (- B)))))"
  by qsep

lemma "s \<in> ((A \<and>\<^sup>*1 B) \<and>\<^sup>*1 C) \<longrightarrow> s \<in> (A \<and>\<^sup>*1 (C \<and>\<^sup>*1 B))"
  by qsep

end
theory Quantum_Separation_LogicDef
  imports QSemanticsBig 
begin

type_synonym ('s,'p) triplet = "('s state) assn \<times> 'p \<times> ('s state) assn"


definition comb_set::"('a \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'b set"
  where "comb_set f A B \<equiv> \<Union>a\<in>A. f a ` B " 


lemma "a \<in> A \<Longrightarrow> b \<in> B \<Longrightarrow> f a b \<in> comb_set f A B"  
  unfolding comb_set_def by auto

lemma "x \<in> comb_set f A B \<Longrightarrow> \<exists>a b. a \<in> A \<and> b \<in> B \<and> x = f a b"  
  unfolding comb_set_def by auto


definition Q_sep_dis::"(('s state) \<Rightarrow> bool) \<Rightarrow> (('s state) \<Rightarrow> bool) \<Rightarrow>  (('s state) \<Rightarrow> bool)" 
(infixr "\<and>*\<^sub>q" 35)
where "Q_sep_dis A B \<equiv>  let setAB = fst ` (snd ` {s. A s}) \<inter>  fst ` (snd ` {s. B s});
                              setA = {s. A s \<and> fst (snd s) \<in> setAB}; 
                              setB = {s. B s \<and> fst (snd s) \<in> setAB} in
                           (\<lambda>s. fst s \<in> (comb_set (*) (fst ` setA) (fst ` setB)) \<and>  
                                 fst (snd s) \<in> setAB \<and>      
                            ((\<lambda>s. s \<in> (snd ` (snd ` setA))) \<and>* 
                             (\<lambda>s. s \<in> (snd ` (snd ` setB)))) (snd (snd s)))"

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
    by (simp add: QState_var_idem)
  have f2:"QState_list ?Q = v" using a3
    by (simp add: QState_list_idem)
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


lemma map_assnv_dest:
  "(\<rho>,\<sigma>,Q) \<in> q\<cdot>f \<mapsto>\<^sub>v v \<Longrightarrow> 
      QStateM_vars Q = Q_domain_var (the (var_set q f \<sigma>)) (QStateM_map Q) \<and> 
      QStateM_list Q = v \<sigma> \<and> QStateM_vars Q \<noteq> {} \<and> 
      (\<forall>e \<in> (the (var_set q f \<sigma>)). (QStateM_map Q) e \<noteq> {}) \<and> \<rho> = 1"
  unfolding map_assnv_def Let_def get_qstate_def get_stack_def qstate_def 
  by (auto simp add: QStateM_vars.rep_eq  QStateM_list.rep_eq)

(* definition prob_assert::" (('s state) set) \<Rightarrow>  real \<Rightarrow> (('s state) set)"
(infixr "\<smile>" 60)
where "prob_assert q p \<equiv> {s. fst s = p \<and> snd s \<in> {(x,y). \<exists>p. (p,(x,y)) \<in> q}} "
*)

definition prob_assert::" (('s state) set) \<Rightarrow>  real \<Rightarrow> (('s state) set)"
(infixr "\<smile>" 60)
where "prob_assert q p \<equiv> if p \<noteq> 0 then (\<lambda>s. (fst s * p, snd s)) ` q 
                          else (\<lambda>s. (fst s * p, snd s)) ` UNIV"

definition int_stack_ass::"('s,'a set) expr \<Rightarrow> ('s, 'a set) expr \<Rightarrow> (('s state) set)"
(infixr "\<inter>\<^sub>{\<^sub>}" 35)
  where "int_stack_ass q1 q2 \<equiv> let st = (\<lambda>s. get_stack s) in   
                 {s. q1 (st s) \<inter> q2 (st s) = {}}"

(* definition empty_state_norm_expr::"('s, complex) expr \<Rightarrow> ('s , complex QState) expr"
("|>\<^sub>_" 50)
where "empty_state_norm_expr n \<equiv> (\<lambda>s. (n s) \<cdot>\<^sub>q |>)" *)

definition empty_qstatem_norm_expr::"('s, complex) expr \<Rightarrow> ('s ,  QStateM) expr"
("|>\<^sub>_" 50)
where "empty_qstatem_norm_expr n \<equiv> (\<lambda>s. (n s) \<cdot>\<^sub>Q 0)"


definition empty_qstatem_norm_ass::"('s, complex) expr \<Rightarrow> (('s state) set)"
("/|>a\<^sub>_" 50)
where "empty_qstatem_norm_ass n \<equiv> let h = |>\<^sub>n in 
                                 {s. fst s = 1 \<and> get_QStateM s = (h (get_stack s))}"


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



(* definition map_assnl::"('s,nat set) expr \<Rightarrow> ('s state, (complex) QState) expr \<Rightarrow> (('s state) set)"  (infixr "\<mapsto>\<^sub>l" 35)
  where "map_assnl f v \<equiv> let qv = (\<lambda>s. fst (get_qstate s)); 
                            qs = (\<lambda>s. snd (get_qstate s));
                            st = (\<lambda>s. get_stack s) in   
                 {s. \<Union>((qv s) ` (f (st s))) \<noteq> {} \<and> Q_domain_set f s = QState_vars (v s) \<and>
                     (\<exists>\<qq>' \<qq>''. (qs s) =  \<qq>' + \<qq>'' \<and> (v s) = \<qq>''  \<and> \<qq>' ## \<qq>'' )}" *)

(* definition map_assnl'::"('s,nat set) expr \<Rightarrow> ('s,nat set) expr \<Rightarrow> ('s state, (complex) QState) expr \<Rightarrow> (('s state) set)" 
("_\<cdot>_ \<mapsto>\<^sub>l _"  [1000, 20, 1000] 60)
where "map_assnl' f f' v \<equiv> let qv = (\<lambda>s. fst (get_qstate s)); 
                               qs = (\<lambda>s. snd (get_qstate s));
                               st = (\<lambda>s. get_stack s) in   
                 {s. Q_domain_set f (qv s) (st s) \<noteq> {} \<and> Q_domain_set f (qv s) (st s) = QState_vars (v s) \<and>
                     (\<exists>\<qq>' \<qq>''. (qs s) =  \<qq>' + \<qq>'' \<and> (v s) = \<qq>''  \<and> \<qq>' ## \<qq>'' \<and> 
                                 Q_domain_set f' (qv s) (st s) = QState_vars \<qq>'')}"*)

(* definition aij::"'s expr_q \<Rightarrow> ('s, (complex) QState) expr \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>'s state \<Rightarrow>  complex"
  where "aij f v i j\<equiv>   let st =(\<lambda>s. get_stack s) in
                 (\<lambda>s. vector_element_12 (v (st s)) (Q_domain_set f s) (i,j))" *)


(* definition aijv::"nat set \<Rightarrow> nat set \<Rightarrow> complex list  \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>  complex"
  where "aijv d1 d2 v i j\<equiv>  (vec_of_list v)$(partial_state2.pencode12 d1 d2 (i,j))" *)

definition aij ::"'s state \<Rightarrow> 's expr_q  \<Rightarrow> ('s, complex list) expr \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>complex" 
  where "aij s q v i j \<equiv> let st = get_stack s ; qv = fst (get_qstate s); 
                             vars = Q_domain qv; d1 = Q_domain_var (q st) qv; d2 = vars - d1 ;
                             vec = v st in 
                             aijv d1 d2 (vec_of_list vec) i j"




(* definition aij::"'s expr_q \<Rightarrow> ('s state, (complex) QState) expr \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>'s state \<Rightarrow>  complex"
  where "aij v f i j\<equiv>  let qv = (\<lambda>s. fst (get_qstate s)); 
                            st = (\<lambda>s. get_stack s) in 
                 (\<lambda>s. vector_element_12 (f s) (v (st s, qv s)) (i,j))" *)

(* definition v_f::"'s expr_q \<Rightarrow>( nat \<Rightarrow>'s state \<Rightarrow>  complex) \<Rightarrow> ('s state, (complex) QState) expr"
  where "v_f q f \<equiv> let vars = Q_domain_set q in 
                     (\<lambda>s. QState(vars s, 
                          map (\<lambda>e. f e s) [0..<2^card (vars s)]))" *)

definition v_f::"'s expr_q \<Rightarrow> q_vars \<Rightarrow> ( nat \<Rightarrow>'s  \<Rightarrow>  complex) \<Rightarrow> ('s,  QState) expr"
  where "v_f q qvars f \<equiv> let vars = Q_domain_set q qvars in 
                     (\<lambda>s. QState(vars s, map (\<lambda>e. f e s) [0..<2^card (vars s)]))"


definition var_exp::"'v \<Rightarrow> 's \<Rightarrow> nat set"
("\<llangle>_\<rrangle>"  [] 1000)
where "var_exp q  \<equiv> \<lambda>\<sigma>. {to_nat (get_value \<sigma> q)}"



definition valid::"[('s state) assn,('v, 's) com,('s state) assn] \<Rightarrow> bool"
    ("\<Turnstile>_ _ _"  [1000, 20, 1000] 60)
    where "\<Turnstile> P c Q \<equiv> \<forall>\<sigma> \<sigma>'. \<turnstile> \<langle>c,\<sigma>\<rangle> \<Rightarrow> \<sigma>' \<longrightarrow> \<sigma> \<in> Normal ` P \<longrightarrow> \<sigma>' \<in> Normal ` Q"

definition \<SS>::"('s state) set \<Rightarrow> ('s \<Rightarrow> real \<Rightarrow>  QStateM \<Rightarrow> bool)"
  where "\<SS> s \<equiv> (\<lambda>u p q. (p,u,q) \<in> s)"


lemma \<SS>_equiv:"s \<in> R \<longleftrightarrow> (\<SS> R) (get_stack s)  (get_prob s) (get_QStateM s)" 
  unfolding  \<SS>_def get_stack_def get_prob_def get_QStateM_def by auto

lemma allocate_preserves_R:
  assumes a2':"\<sigma>' = set_value \<sigma> q (from_nat q')" and       
       a6:"not_access_v (\<SS> R) q" and a7:"q \<in> variables" and  a8:"q \<in> nat_vars" and
       a9:"(p,\<sigma>,\<Q>) \<in> R"
     shows "(p,\<sigma>',\<Q>) \<in> R"   
  using not_access_v_f_q_eq_set[OF a7 from_nat_in_vdomain[OF a7 a8] a2' a6] assms 
  unfolding \<SS>_equiv get_stack_def get_prob_def get_QStateM_def
  by auto

definition \<rho> ::"'s expr_q  \<Rightarrow> ('s, complex list) expr \<Rightarrow> nat \<Rightarrow>  's state \<Rightarrow> real" 
  where "\<rho> q v i s \<equiv> let st = get_stack s ; qv = fst (get_qstate s); 
                         vars = Q_domain qv; d1 = Q_domain_var (q st) qv; d2 = vars - d1 in 
                     (\<Sum>j = 0..<2^(card d2). norm (aijv d1 d2 (vec_of_list (v st)) i j )^2) / 
                        (\<Sum>i = 0 ..<2^(card d1). 
                            \<Sum>j = 0 ..<2^(card d2). norm (aijv d1 d2 (vec_of_list (v st)) i j )^2 )"

definition vector_i::"'s state \<Rightarrow> 's expr_q  \<Rightarrow>  ('s, complex list) expr \<Rightarrow> nat \<Rightarrow> ('s, complex list) expr"
  where "vector_i s q v i \<equiv> 
     let st = get_stack s ; qv = fst (get_qstate s); 
        vars = Q_domain qv; d1 = Q_domain_var (q st) qv; d2 = vars - d1;
        elem_ij  = (\<lambda>j. (aij s q v i j) / sqrt (\<rho> q v i s)) in
     (\<lambda>st. map (\<lambda>e. elem_ij e) [0..<2^card d2])"

definition vector_i'::"'s state \<Rightarrow> 's expr_q  \<Rightarrow>  ('s, complex list) expr \<Rightarrow> nat \<Rightarrow> ('s, complex list) expr"
  where "vector_i' s q v i \<equiv> 
     let st = get_stack s ; qv = fst (get_qstate s); 
        vars = Q_domain qv; d1 = Q_domain_var (q st) qv; d2 = vars - d1;
        elem_ij  = if d2 \<noteq> {} then (\<lambda>j. (aij s q v i j) / sqrt (\<rho> q v i s))
                   else (\<lambda>j. 1) in
     (\<lambda>st. map (\<lambda>e. elem_ij e) [0..<2^card d2])"

lemma eq_vector_i:
  assumes a0:"(Q_domain (fst (get_qstate s))) - 
                  (Q_domain_var (q (get_stack s)) (fst (get_qstate s))) \<noteq>{}" 
  shows "vector_i s q v i = vector_i' s q v i"
  using a0
  unfolding vector_i_def vector_i'_def Let_def Q_domain_set_def
  by auto

lemma vector_i_d2_empty:
  assumes a0:"(Q_domain (fst (get_qstate s))) - 
                  (Q_domain_var (q (get_stack s)) (fst (get_qstate s))) = {}" 
  shows "vector_i' s q v i = (\<lambda>st. [1])"
proof-
  
  have "2^card ((Q_domain (fst (get_qstate s))) - 
                  (Q_domain_var (q (get_stack s)) (fst (get_qstate s)))) = 1"    
    by (simp add: assms) 
  then have "[0..<
                 2 ^
                 card
                  (Q_domain (fst (get_qstate s)) -
                   (Q_domain_var (q (get_stack s)) (fst (get_qstate s))))] = [0]" 
    by (simp add: assms)
  then show ?thesis unfolding vector_i'_def Let_def apply auto using a0 by auto
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

inductive "hoarep"::"[('s state) assn,('v,'s) com, ('s state) assn] => bool"
    ("\<turnstile>(_/ (_)/ _)" [1000,20,1000]60)
where
  Skip: "\<turnstile> Q Skip Q"

| SMod: "\<turnstile>{s.  set_stack s (f (get_stack s)) \<in> Q} (SMod f) Q"
         
| QMod: " \<turnstile> {s. q_v = fst (get_qstate s) \<and>  st = get_stack s \<and>
                Q_domain_set qs q_v  st \<noteq> {} \<and>
                set_qstate s (matrix_sep (qs st) (get_QStateM s) M) \<in> Q} 
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

| QAlloc:"not_access_v v q \<Longrightarrow> not_access_v (\<SS> R) q \<Longrightarrow>         
          q \<in> variables \<Longrightarrow> q \<in> nat_vars \<Longrightarrow> \<forall>\<sigma>. length (v \<sigma>) > 1 \<Longrightarrow>
          \<turnstile> R q:=alloc[e] v ((q\<cdot>f \<mapsto>\<^sub>v v) \<and>\<^sup>* R)"


\<comment>\<open>In QDispose we set that Qs does not depend on the stack to avoid that 
   the n in the postcondition may also depend on the stack and gives unsound results
  in later modifications to the stack that may not affect the vector\<close>

| QDispose: " n = (\<lambda>s. vec_norm (vec_of_list (v s))) \<Longrightarrow>                  
              \<turnstile> (q\<cdot>i \<mapsto>\<^sub>v v) (Dispose q i) ( |>a\<^sub>n) "

|(* QMeasure: "st = (\<lambda>s. get_stack s)  \<Longrightarrow> 
             not_access_v q v \<Longrightarrow>  not_access_v vl v \<Longrightarrow>                            
             \<Psi> = (\<lambda>i. {\<sigma>. \<sigma> \<in> ((q \<cdot> (\<lambda>s. {}) \<mapsto> (unit_vecl s q i)) \<and>\<^sup>* 
                          (qr \<cdot> (\<lambda>s. {}) \<mapsto> (vector_i \<sigma> q vl i)))}) \<Longrightarrow>               
               \<turnstile> ((q \<cdot> qr \<mapsto> vl) \<inter> 
                 ({s. \<exists>i\<in> {q}\<^sub>s. \<Phi> (set_stack s (set_value (st s) v (from_nat i)))}))
                    (Measure v q)   
                  ({s. s \<in> (\<Union>i\<in>{q}\<^sub>s. \<Psi> i)} \<inter> {s. \<Phi> s})" *)

QMeasure: " v \<in> nat_vars \<Longrightarrow> v \<in> variables \<Longrightarrow>
           not_access_v q v \<Longrightarrow>  not_access_v vl v \<Longrightarrow> not_access_v qr v \<Longrightarrow>                                            
           \<turnstile> (q \<cdot> qr \<mapsto> vl)
                (Measure v q)   
              {s. s \<in> (\<Union>i\<in>{q}\<^sub>s. (v\<down>\<^sub>(from_nat i)) \<inter> (((q \<mapsto> (unit_vecl s q i)) \<and>\<^sup>* 
                                  (qr  \<mapsto> (vector_i' s q vl i)))\<smile>(\<rho> q vl i s)))}" 


| Frame: "\<turnstile> P c Q \<Longrightarrow> {v. (\<exists>p q. access_v  (\<lambda>s. (p, (s,q)) \<in> A) v = True)} \<inter> 
                      modify_locals c = {} \<Longrightarrow> \<turnstile> (P \<and>\<^sup>* A) c (Q \<and>\<^sup>* A)"

| Conseq: "\<forall>s \<in> P. \<exists>P' Q'. \<turnstile> P' c Q' \<and> s \<in> P' \<and> Q' \<subseteq> Q 
           \<Longrightarrow> \<turnstile> P c Q"


lemma prob_assert_intro:"x\<noteq>0 \<Longrightarrow> (a,b,c) \<in> P \<Longrightarrow>(a*x,b,c) \<in> P \<smile> x"
  unfolding prob_assert_def 
  by force

lemma prob_assert_dest1:"s \<in> P \<smile> x \<Longrightarrow> x\<noteq>0 \<Longrightarrow> (\<exists>p. get_prob s = x*p \<and> (p,snd s) \<in> P)"
  unfolding prob_assert_def get_prob_def by auto

lemma prob_assert_dest2:"s \<in> P \<smile> x \<Longrightarrow> x=0 \<Longrightarrow> get_prob s = 0 \<and> snd s\<in>UNIV"
  unfolding prob_assert_def get_prob_def by auto


(* lemma map_assnv_prob:
   "QState_wf (q'_addr, v \<sigma>) \<Longrightarrow> QStateM_wf ((\<lambda>i. {})(q' := q'_addr), QState (q'_addr, v \<sigma>)) \<Longrightarrow> 
       QStateM_map (QStateM ((\<lambda>i. {})(q' := q'_addr), QState (q'_addr, v \<sigma>))) = (\<lambda>i. {})(q' := q'_addr) \<Longrightarrow>
        length (v \<sigma>) = 2^e \<sigma> \<Longrightarrow>  
      length (v (set_value \<sigma> q (from_nat q'))) = 2^e \<sigma> \<Longrightarrow> q \<in> variables \<Longrightarrow>
     v \<sigma> = v (set_value \<sigma> q (from_nat q')) \<Longrightarrow>
      (1, set_value \<sigma> q (from_nat q'),
         QStateM ((\<lambda>i. {})(q' := q'_addr), QState (q'_addr, v \<sigma>)))
           \<in> (q \<mapsto>\<^sub>v v) \<smile> 1"
 unfolding prob_assert_def map_assnv_def Let_def get_qstate_def get_stack_def Q_domain_var_def set_value_def
  apply auto        
     apply (metis QStateM_rel1 QState_var_idem  fst_conv snd_conv)
  using QStateM_rel1 QState_var_idem  apply fastforce 
    apply (metis QStateM_rel2 QStateM_wf_qstate QState_list_idem  fst_conv snd_conv )      
  apply (simp add:  get_set rep_nat set_value_def)
  by (simp add:  get_set rep_nat) *)


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
  by (auto simp add: QState_var_idem QStateM_wf_qstate QState_list_idem less_not_refl2 get_set rep_nat set_value_def)             
            

lemma alloc_sound:
  assumes (* a0: "st =(\<lambda>s. get_stack s) " and *) a1:"not_access_v v q" and 
          a2':"not_access_v (\<SS> R) q" and 
          a3:"q \<in> variables" and  a4:"q \<in> nat_vars"  and a5:"\<forall>\<sigma>. length (v \<sigma>) > 1"
  shows "\<Turnstile> R q:=alloc[e] v (( (q\<cdot>f \<mapsto>\<^sub>v v))  \<and>\<^sup>* R)"  
proof-
  { fix s s'
    let ?st = "(\<lambda>s. get_stack s) "
     assume a00:"\<turnstile> \<langle>q:=alloc[e] v,s\<rangle> \<Rightarrow> s'" and
            a01:"s \<in> Normal ` R"             
     then obtain sn where a01:"s = Normal sn" and         
         a01a:"sn \<in> R"  
       by auto           
     from QExec_Normal_elim_cases(9)[OF a00[simplified a01]] a5
      obtain q' \<Q> q'_addr \<sigma> \<delta> where 
      sn: "sn = (\<delta>, \<sigma>, \<Q>)" and 
      s':"s' = Normal (\<delta>, set_value \<sigma> q (from_nat q'),
                         \<Q> + QStateM ((\<lambda>i. {})(q' := q'_addr), QState (q'_addr, v \<sigma>)))" and
      q':"q' \<notin> dom_q_vars (QStateM_map \<Q>)"  and lv:"length (v \<sigma>) > 1" and
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
       by (metis a3 a4 from_nat_in_vdomain local.a1 not_access_v_f_q_eq_set st')    
     have sn_mod_\<sigma>'_in_R:"(\<delta>, ?\<sigma>', \<Q>) \<in> R" using a01a st' unfolding get_stack_def
       using a2' a3 a4 allocate_preserves_R sn by blast
     have new_state_in_assr:"(1, ?\<sigma>', ?\<Q>') \<in> (q\<cdot>f \<mapsto>\<^sub>v v)"
       using map_assnv_prob[OF _ _ _ , of q'_addr v \<sigma> q' q]    v_eq a4 a3  lv
(*          allocate_wf1[of ?\<Q>', OF _  _ _ q'_addr_in_new , of  "(\<lambda>i. {})(q' := q'_addr)" v q' ?\<sigma>' set_value q, simplified] *)
       allocate_wf1[of ?\<Q>', OF _ lv    _ q'_addr_in_new, of "{}\<^sub>q(q' := q'_addr)" q' , simplified]              
       by force
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
         using disjoint_allocate[of ?\<Q>', OF _ lv q' _  q'_addr_in_new, simplified]         
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

(* lemma Q_domain_Q:"QStateM_vars \<Q> = Q_domain_var vs (QStateM_map \<Q>) \<Longrightarrow> 
       \<Q> =  \<Q>' + \<Q>'' \<Longrightarrow> \<Q>' ## \<Q>'' \<Longrightarrow>
       Q_domain (QStateM_map \<Q>') = Q_domain_var vs (QStateM_map \<Q>') \<Longrightarrow>
       Q_domain (QStateM_map \<Q>') =  Q_domain (QStateM_map \<Q>)"
  unfolding Q_domain_var_def 
  sorry
*)

lemma  Q_domain_Q:
  assumes
       a0':"\<Q> = \<Q>' + \<Q>''" and a0'':"\<Q>' ## \<Q>''" and
       a0:"QStateM_vars \<Q> = Q_domain_var vs (QStateM_map \<Q>)" and
       a1:"\<forall>e\<in>vs. QStateM_map \<Q> e \<noteq> {}" and
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
    using a0 a1 a2 a3  unfolding Q_domain_var_def Q_domain_def 
    by (metis (no_types, lifting) SUP_cong Sep_Prod_Instance.none_def  plus_fun_def sep_add_commute)
qed

  

lemma dispose_sound:
  assumes  
    a0:"n = (\<lambda>s. vec_norm (vec_of_list (v s)))" 
  shows "\<Turnstile> (q\<cdot>i \<mapsto>\<^sub>v v) (Dispose q i) ( |>a\<^sub>n)" 
proof-
  { fix s s'
    let ?st = "(\<lambda>s. get_stack s) "
    assume a00:"\<turnstile> \<langle>Dispose q i,s\<rangle> \<Rightarrow> s'" and
            a01:"s \<in> Normal ` ((q\<cdot>i \<mapsto>\<^sub>v v))"                  
    then obtain \<sigma> \<rho> \<Q> where a01:"s = Normal (\<rho>,\<sigma>,\<Q>)" and
         a01a:"(\<rho>,\<sigma>,\<Q>) \<in>  (q\<cdot>i \<mapsto>\<^sub>v v)"               
      by auto
    note dest_assign = map_assnv_dest[OF a01a]
    moreover obtain \<Q>' \<Q>''  where 
        step:"\<Q> =  \<Q>' + \<Q>'' \<and>
          s' = Normal (\<rho>, \<sigma>, vec_norm (QStateM_vector \<Q>') \<cdot>\<^sub>Q \<Q>'') \<and>
          \<Q>' ## \<Q>'' \<and>  Q_domain_var (the (var_set q i \<sigma>)) (QStateM_map \<Q>') \<noteq> {} \<and>
          QStateM_vars \<Q>' = Q_domain_var (the (var_set q i \<sigma>)) (QStateM_map \<Q>') \<and>
          (\<forall>e \<in> (the (var_set q i \<sigma>)). (QStateM_map \<Q>') e \<noteq> {})"                 
      apply (rule  QExec_Normal_elim_cases(10)[OF a00[simplified a01]])
       apply blast 
      apply auto  
      using calculation apply auto 
      unfolding Q_domain_def Q_domain_var_def       
      apply (drule spec[of _ \<Q>], auto)               
      apply (frule spec[of _ 0])
      by auto         
    moreover have q_domain:"Q_domain (QStateM_map \<Q>') =  Q_domain (QStateM_map \<Q>)"
      using calculation Q_domain_Q
      by (simp add: Q_domain_Q)   
    ultimately have Q:"\<Q> = ((QStateM_list \<Q>'' ! 0)) \<cdot>\<^sub>Q \<Q>' \<and> (inverse(QStateM_list \<Q>'' ! 0)) \<cdot>\<^sub>Q \<Q>'' = 0"
      using sep_eq by auto     
    
    have map:"(QStateM_map \<Q>'') = {}\<^sub>q"
      using sep_Q_eq_Q'_Q''_empty step q_domain by auto
    then have len:"length (QStateM_list \<Q>'') = 1"
      using QStateM_rel1  QState_rel1 unfolding Q_domain_def qstate_def apply auto
      by (metis QStateM_list.rep_eq QState_list.rep_eq QState_vars.rep_eq 
           SUP_bot_conv(2) card_empty nat_power_eq_Suc_0_iff)

    have "QStateM_list \<Q> = v \<sigma> "
      using dest_assign by blast
    then have "vec_norm (vec_of_list (v \<sigma>)) \<cdot>\<^sub>Q 0 = 
               vec_norm (QStateM_vector \<Q>) \<cdot>\<^sub>Q 0" 
      apply transfer'
      by (simp add: QState_vector.rep_eq uqstate_snd)
    also have "vec_norm (QStateM_vector \<Q>) \<cdot>\<^sub>Q 0  = 
               vec_norm (QStateM_vector \<Q>) \<cdot>\<^sub>Q ((inverse(QStateM_list \<Q>'' ! 0)) \<cdot>\<^sub>Q \<Q>'')"
      using Q by simp 
    also have "vec_norm (QStateM_vector \<Q>) \<cdot>\<^sub>Q ((inverse(QStateM_list \<Q>'' ! 0)) \<cdot>\<^sub>Q \<Q>'') = 
               vec_norm (QStateM_vector (((QStateM_list \<Q>'' ! 0)) \<cdot>\<^sub>Q \<Q>')) \<cdot>\<^sub>Q ((inverse(QStateM_list \<Q>'' ! 0)) \<cdot>\<^sub>Q \<Q>'')"
      using Q by simp    
    finally have 
       "vec_norm (QStateM_vector \<Q>') \<cdot>\<^sub>Q \<Q>'' = vec_norm (vec_of_list (v \<sigma>)) \<cdot>\<^sub>Q 0 "      
      using  eq_vec_norm_q_empty[of \<Q>'' \<Q>', OF len]
      by simp
    moreover obtain sn where 
       s':"s' = Normal sn \<and> sn = (\<rho>, \<sigma>, vec_norm (QStateM_vector \<Q>') \<cdot>\<^sub>Q \<Q>'')"
      using step by auto
    ultimately have  "sn \<in> ( |>a\<^sub>n) "
      using a0 dest_assign
      unfolding  empty_qstatem_norm_ass_def empty_qstatem_norm_expr_def get_QStateM_def get_stack_def
      by auto      
     then have "s' \<in> Normal ` (( |>a\<^sub>n))" using s' by auto
   }
   thus ?thesis  unfolding valid_def by auto
 qed

definition \<pi>::"real \<Rightarrow> ('s state) set"
  where "\<pi> x \<equiv> {s. fst s = x}"

lemma " x\<in> (\<pi> u) \<and> fst x = n \<Longrightarrow> fst x = fst y \<Longrightarrow> y \<in> \<pi> u"
  unfolding \<pi>_def by auto


lemma domain_Q: assumes 
      a1:"(\<forall>e\<in>q \<sigma>. QStateM_map \<Q> e \<noteq> {})" and
      a2:"(k::nat) < 2 ^ card (\<Union> (QStateM_map \<Q> ` q \<sigma>))" and
      a3:"QStateM_vars \<Q> = Q_domain_var (q \<sigma> \<union> qr \<sigma>) (QStateM_map \<Q>)" and
      a4:"QStateM_list \<Q> = vl \<sigma>" and      
      a6:"q \<sigma> \<inter> qr \<sigma>  = {}" and a7:"q \<sigma> \<noteq> {}"                    
    shows "finite (Q_domain_var (q \<sigma>) (QStateM_map \<Q>))" and 
          "finite (Q_domain_var (qr \<sigma>) (QStateM_map \<Q>))" and
          "Q_domain (QStateM_map \<Q>) = QStateM_vars \<Q>" and
          "dim_vec (vec_of_list (vl \<sigma>)) =
             2 ^ card (Q_domain_var (q \<sigma>) (QStateM_map \<Q>)) *
             2 ^ card (Q_domain_var (qr \<sigma>) (QStateM_map \<Q>))" and
          "k < 2 ^ card (Q_domain_var (q \<sigma>) (QStateM_map \<Q>))" and
          "Q_domain_var (q \<sigma>) (QStateM_map \<Q>) \<inter> Q_domain_var (qr \<sigma>) (QStateM_map \<Q>) = {}" and
          "Q_domain_var (q \<sigma>) (QStateM_map \<Q>) \<noteq> {}" and
          "Q_domain_var (qr \<sigma>) (QStateM_map \<Q>) = Q_domain (QStateM_map \<Q>) - Q_domain_var (q \<sigma>) (QStateM_map \<Q>)"    
proof-
  let ?q = "q \<sigma>" and ?qr = "qr \<sigma>" and ?v = "vec_of_list (vl \<sigma>)"       
  let ?v1 = "Q_domain_var ?q (QStateM_map \<Q>)" and ?v2 = "Q_domain_var ?qr (QStateM_map \<Q>)"
  let ?M = "(1\<^sub>k (2 ^ card (\<Union> (QStateM_map \<Q> ` q \<sigma>))))"
  have "finite (QStateM_vars \<Q>)"
    by (simp add: QStateM_vars.rep_eq QState_rel3')
  moreover have h1:"QStateM_vars \<Q> = Q_domain_var ?q (QStateM_map \<Q>) \<union> Q_domain_var ?qr (QStateM_map \<Q>)"
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

lemma sound_prob_semant_proof_rho:
  assumes a0:"(\<delta>k, \<Q>') = measure_vars' k (q \<sigma>) \<Q>" and 
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
    using domain_Q[of q \<sigma> \<Q> k qr vl, OF a1 a2 a3 a4 a6 a7] by auto
  
  note eq_norm[OF f1 f2 inter_12 k dim_vec]
  moreover have \<delta>k:"\<delta>k =  Re ((vec_norm
             (QStateM_vector
               (matrix_sep ?q \<Q> 1\<^sub>k (2 ^ card (\<Union> (QStateM_map \<Q> ` ?q))))))\<^sup>2 /
             (vec_norm (QStateM_vector \<Q>))\<^sup>2)"
    using measure_vars'_dest measure_vars_dest a0
    by (metis fst_conv measure_vars'_neq)
  moreover have "QStateM_vector (matrix_sep (q \<sigma>) \<Q> ?M) = 
                 (ptensor_mat ?v1 ?v2
                               (?M::complex mat) (1\<^sub>m (2^(card ?v2))) *\<^sub>v 
                      QStateM_vector \<Q>)"
    using matrix_sep_dest[OF v1_not_empty _ Q_domain  v2, of "q \<sigma>"  ?M] v2 
    by (auto simp add: list_of_vec_QStateM_vec Q_domain list_of_vec_elim)
  then have "Re ((vec_norm
                  (ptensor_mat ?v1 ?v2 (1\<^sub>k (2 ^ card ?v1)) (1\<^sub>m (2 ^ card ?v2)) *\<^sub>v
                    vec_of_list (vl \<sigma>)))\<^sup>2 /
                (vec_norm (vec_of_list (vl \<sigma>)))\<^sup>2) = 
             Re ((vec_norm
                (QStateM_vector (matrix_sep (q \<sigma>) \<Q> (1\<^sub>k (2 ^ card ?v1)))))\<^sup>2 /
                (vec_norm (QStateM_vector \<Q>))\<^sup>2)"
    using QStateM_list.rep_eq QStateM_vector.rep_eq QState_list.rep_eq 
          QState_vector.rep_eq Q_domain_var_def a4 v2 by auto
  
  ultimately show "\<delta>k = \<rho> q vl k ns'" using v2
    unfolding \<rho>_def aij_def Q_domain_var_def Let_def get_stack_def get_qstate_def     
    by (force simp add: a8 a12 a9 a10 a11) 
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
         (1 / sqrt \<delta>k) \<cdot>\<^sub>v (ptensor_vec 
          (Q_domain_var (q \<sigma>) (QStateM_map \<Q>))
          (Q_domain_var (qr \<sigma>) (QStateM_map \<Q>))
          (unit_vec (2 ^ card (Q_domain_var (q \<sigma>) (QStateM_map \<Q>))) k)
          (vector_aij (Q_domain_var (q \<sigma>) (QStateM_map \<Q>))
          (Q_domain_var (qr \<sigma>) (QStateM_map \<Q>)) (QStateM_vector \<Q>) k))"
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
    using domain_Q[of q \<sigma> \<Q> k qr vl, OF a1 a2 a3 a4 a6 a7] by auto
  
  note eq_norm[OF f1 f2 inter_12 k dim_vec]
  moreover have \<delta>k:"\<delta>k =  Re ((vec_norm
             (QStateM_vector
               (matrix_sep ?q \<Q> 1\<^sub>k (2 ^ card (\<Union> (QStateM_map \<Q> ` ?q))))))\<^sup>2 /
             (vec_norm (QStateM_vector \<Q>))\<^sup>2)"
    using measure_vars_dest a0
    by auto     
  moreover have "QStateM_vector (matrix_sep (q \<sigma>) \<Q> ?M) = 
                 (ptensor_mat ?v1 ?v2
                               (?M::complex mat) (1\<^sub>m (2^(card ?v2))) *\<^sub>v 
                      QStateM_vector \<Q>)"
    using matrix_sep_dest[OF v1_not_empty _ Q_domain  v2, of "q \<sigma>"  ?M] v2 
    by (auto simp add: list_of_vec_QStateM_vec Q_domain list_of_vec_elim)
  then have "Re ((vec_norm
                  (ptensor_mat ?v1 ?v2 (1\<^sub>k (2 ^ card ?v1)) (1\<^sub>m (2 ^ card ?v2)) *\<^sub>v
                    vec_of_list (vl \<sigma>)))\<^sup>2 /
                (vec_norm (vec_of_list (vl \<sigma>)))\<^sup>2) = 
             Re ((vec_norm
                (QStateM_vector (matrix_sep (q \<sigma>) \<Q> (1\<^sub>k (2 ^ card ?v1)))))\<^sup>2 /
                (vec_norm (QStateM_vector \<Q>))\<^sup>2)"
    using QStateM_list.rep_eq QStateM_vector.rep_eq QState_list.rep_eq 
          QState_vector.rep_eq Q_domain_var_def a4 v2 by auto
  
  ultimately show "\<delta>k = \<rho> q vl k ns'" using v2
    unfolding \<rho>_def aij_def Q_domain_var_def Let_def get_stack_def get_qstate_def     
    by (force simp add: a8 a12 a9 a10 a11)  
  show "QStateM_vars \<Q>' = ?v1 \<union> ?v2"
    by (metis QStateM_rel1 QStateM_vars.rep_eq Q_domain_var_def UN_Un a12 a3 qstate_def)
  have "QStateM_vector (matrix_sep (q \<sigma>) \<Q> ?M) = 
                 (ptensor_mat ?v1 ?v2
                               (?M::complex mat) (1\<^sub>m (2^(card ?v2))) *\<^sub>v 
                      QStateM_vector \<Q>)"
    using matrix_sep_dest[OF v1_not_empty _ Q_domain  v2, of "q \<sigma>"  ?M] v2 
    by (auto simp add: list_of_vec_QStateM_vec Q_domain list_of_vec_elim)
  moreover have "\<Q>' = (1 / sqrt (\<delta>k)) \<cdot>\<^sub>Q matrix_sep (q \<sigma>) \<Q> (1\<^sub>k ((2::nat) ^ card (\<Union> (QStateM_map \<Q> ` (q \<sigma>)))))"
    using measure_vars_dest[of \<delta>k] a0
    by (simp add: \<delta>k) 
  ultimately have "QStateM_vector \<Q>' = (1 / sqrt \<delta>k) \<cdot>\<^sub>v (ptensor_mat ?v1 ?v2
                               (?M::complex mat) (1\<^sub>m (2^(card ?v2))) *\<^sub>v QStateM_vector \<Q>)"  
    using a13  
    by (metis Im_complex_of_real Re_complex_of_real real_sqrt_gt_0_iff 
              sca_mult_q_statem_qstate_vector zero_less_divide_1_iff)
  moreover have "(1 / sqrt \<delta>k) \<cdot>\<^sub>v ((ptensor_mat ?v1 ?v2 (?M::complex mat) (1\<^sub>m (2^(card ?v2))) *\<^sub>v QStateM_vector \<Q>)) = 
                 (1 / sqrt \<delta>k) \<cdot>\<^sub>v ptensor_vec ?v1 ?v2 (unit_vec (2^(card ?v1)) k) (vector_aij ?v1 ?v2 (QStateM_vector \<Q>) k)"
    using v_scalar_mat_product_eq_ptensor[OF f1 f2 inter_12 k dim_vec]
    by (simp add: Q_domain_var_def a4 vec_of_list_QStateM_list)
  ultimately show  "QStateM_vector \<Q>' = (1 / sqrt \<delta>k) \<cdot>\<^sub>v ptensor_vec ?v1 ?v2 (unit_vec (2^(card ?v1)) k) (vector_aij ?v1 ?v2 (QStateM_vector \<Q>) k)"
    using measure_vars_dest[of \<delta>k] a0  by auto
qed

lemma sound_prob_semant_proof2:
  assumes a0:"(\<delta>k, \<Q>') = measure_vars' k (q \<sigma>) \<Q>" and 
      a1:"(\<forall>e\<in>q \<sigma>. QStateM_map \<Q> e \<noteq> {})" and
      a2:"k < 2 ^ card (\<Union> (QStateM_map \<Q> ` q \<sigma>))" and
      a3:"QStateM_vars \<Q> = Q_domain_var (q \<sigma> \<union> qr \<sigma>) (QStateM_map \<Q>)" and
      a4:"QStateM_list \<Q> = vl \<sigma>" and
      a5:" QStateM_vars \<Q> \<noteq> {}" and
      a6:"q \<sigma> \<inter> qr \<sigma>  = {}" and a7:"q \<sigma> \<noteq> {}" and 
      a8:"ns' = (p * \<delta>k, \<sigma>', \<Q>')" and 
      a9:"q \<sigma>' = q \<sigma> " and a10:"qr \<sigma>' = qr \<sigma>" and a11:"vl \<sigma>' = vl \<sigma>" and
      a12:"QStateM_map \<Q>' = QStateM_map \<Q>" and
      a13:"0 < \<delta>k" and a14:"QStateM_vars \<Q> = \<Union>((QStateM_map \<Q>) ` q \<sigma>)"      
    shows "\<delta>k = \<rho> q vl k ns'" and 
      "QStateM_vars \<Q>' = Q_domain_var (q \<sigma>) (QStateM_map \<Q>) \<union> 
                         (Q_domain_var (qr \<sigma>) (QStateM_map \<Q>))" and
      "QStateM_vector \<Q>' = 
         unit_vec (2 ^ card (Q_domain_var (q \<sigma>) (QStateM_map \<Q>))) k"
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
    using domain_Q[of q \<sigma> \<Q> k qr vl, OF a1 a2 a3 a4 a6 a7] by auto
  
  note eq_norm[OF f1 f2 inter_12 k dim_vec]
  moreover have \<delta>k:"\<delta>k =  Re ((vec_norm
             (QStateM_vector
               (matrix_sep ?q \<Q> 1\<^sub>k (2 ^ card (\<Union> (QStateM_map \<Q> ` ?q))))))\<^sup>2 /
             (vec_norm (QStateM_vector \<Q>))\<^sup>2)"
    using measure_vars'_dest a0 a14
    by auto     
  moreover have "QStateM_vector (matrix_sep (q \<sigma>) \<Q> ?M) = 
                 (ptensor_mat ?v1 ?v2
                               (?M::complex mat) (1\<^sub>m (2^(card ?v2))) *\<^sub>v 
                      QStateM_vector \<Q>)"
    using matrix_sep_dest[OF v1_not_empty _ Q_domain  v2, of "q \<sigma>"  ?M] v2 
    by (auto simp add: list_of_vec_QStateM_vec Q_domain list_of_vec_elim)
  then have "Re ((vec_norm
                  (ptensor_mat ?v1 ?v2 (1\<^sub>k (2 ^ card ?v1)) (1\<^sub>m (2 ^ card ?v2)) *\<^sub>v
                    vec_of_list (vl \<sigma>)))\<^sup>2 /
                (vec_norm (vec_of_list (vl \<sigma>)))\<^sup>2) = 
             Re ((vec_norm
                (QStateM_vector (matrix_sep (q \<sigma>) \<Q> (1\<^sub>k (2 ^ card ?v1)))))\<^sup>2 /
                (vec_norm (QStateM_vector \<Q>))\<^sup>2)"
    using QStateM_list.rep_eq QStateM_vector.rep_eq QState_list.rep_eq 
          QState_vector.rep_eq Q_domain_var_def a4 v2 by auto
  
  ultimately show "\<delta>k = \<rho> q vl k ns'" using v2
    unfolding \<rho>_def aij_def Q_domain_var_def Let_def get_stack_def get_qstate_def     
    by (force simp add: a8 a12 a9 a10 a11)  
  show "QStateM_vars \<Q>' = ?v1 \<union> ?v2"
    by (metis QStateM_rel1 QStateM_vars.rep_eq Q_domain_var_def UN_Un a12 a3 qstate_def)
  have "QStateM_vector (matrix_sep (q \<sigma>) \<Q> ?M) = 
                 (ptensor_mat ?v1 ?v2
                               (?M::complex mat) (1\<^sub>m (2^(card ?v2))) *\<^sub>v 
                      QStateM_vector \<Q>)"
    using matrix_sep_dest[OF v1_not_empty _ Q_domain  v2, of "q \<sigma>"  ?M] v2 
    by (auto simp add: list_of_vec_QStateM_vec Q_domain list_of_vec_elim)
  moreover have "\<Q>' =  QStateM (QStateM_map \<Q>, QState(QStateM_vars \<Q>, 
           list_of_vec (unit_vec (2^(card (\<Union> (QStateM_map \<Q> ` (q \<sigma>))))) k)))"
    using measure_vars'_dest[of \<Q> "q \<sigma>" \<delta>k] a0 a14
    by (simp add: \<delta>k) 
  ultimately show "QStateM_vector \<Q>' = unit_vec (2 ^ card (Q_domain_var (q \<sigma>) (QStateM_map \<Q>))) k"  
    unfolding Q_domain_var_def
    using a13 a14
    by (metis \<delta>k a0 a7 local.a1 measure_vars'_dest_QStateM snd_conv)
qed

lemma assest_unit:
  assumes 
      a0:"QStateM_vars \<Q> = Q_domain_var (q \<sigma> \<union> qr \<sigma>) (QStateM_map \<Q>)" and       
      a1:"ns' = (p * \<delta>k, \<sigma>', \<Q>')" and 
      a2:"q \<sigma>' = q \<sigma> " and a3:"finite v1" and a4:"v1 \<noteq> {}" and
      a5:"QStateM_map \<Q>' = QStateM_map \<Q>" and
      a6: "map_q = fst (split_map (QStateM_map \<Q>) (q \<sigma>))" and
      a7:"v1 = Q_domain_var (q \<sigma>) (QStateM_map \<Q>)" and 
      a8: "Q1 = QStateM(map_q, QState(v1, list_of_vec (unit_vec (2^(card v1)) k)))"        
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
    using a3 a4 by auto      
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
      a5:"QStateM_vars \<Q> \<noteq> \<Union>((QStateM_map \<Q>) ` q \<sigma>)" and
      a6:"v2 = Q_domain_var (qr \<sigma>) (QStateM_map \<Q>)" and      
      a7:"q \<sigma> \<inter> qr \<sigma> = {}" and a8:"\<delta>k = \<rho> q vl k ns'" and a9:"QStateM_list \<Q> = vl \<sigma> "
    shows "list_of_vec (complex_of_real (1 / sqrt \<delta>k) \<cdot>\<^sub>v
                       vector_aij (Q_domain_var (q \<sigma>) (QStateM_map \<Q>))
                       (Q_domain_var (qr \<sigma>) (QStateM_map \<Q>)) (QStateM_vector \<Q>) k) =
           local.vector_i ns' q vl k \<sigma>'"
proof-             
  let ?v = "list_of_vec (complex_of_real (1 / sqrt \<delta>k) \<cdot>\<^sub>v
             vector_aij (Q_domain_var (q \<sigma>) (QStateM_map \<Q>))
             (Q_domain_var (qr \<sigma>) (QStateM_map \<Q>)) (QStateM_vector \<Q>) k)" 
  have Qstatem_wf_Q:"QStateM_wf (QStateM_unfold \<Q>)"
     using QStateM_wf by blast
  then have QStateM_wf1:"(\<forall>x y. x\<noteq>y \<and> x\<in> domain (QStateM_map \<Q>) \<and> y \<in> domain (QStateM_map \<Q>) \<longrightarrow> 
              QStateM_map \<Q> x \<inter> QStateM_map \<Q> y = {})"
    by auto
  
  have v2:"v2 = QStateM_vars \<Q> - v1"
    using q_vars_q2[of "q \<sigma>" "qr \<sigma>" "QStateM_map \<Q>" "QStateM_vars \<Q>" ] 
          a7 a5 a6 Qstatem_wf_Q a0 a4 eq_QStateM_vars 
    by auto
  have len:"length ?v = length (vector_i ns' q vl k \<sigma>') "
    using v2 a3 a4 a6 a1 a2 QStateM_rel1
    unfolding vector_i_def Let_def vector_aij_def get_qstate_def get_stack_def Q_domain_set_def
    apply auto     
    using QStateM_vars.rep_eq Q_domain_var_def qstate_def by presburger     
  moreover have  "\<forall>i<length ?v. ?v!i = vector_i ns' q vl k \<sigma>' !i"
  proof-
    { fix i 
      assume a00:"i<length ?v"
      moreover have "i<length (vector_i ns' q vl k \<sigma>')" 
        using len calculation by auto
      moreover have 
      "aijv (Q_domain_var (q \<sigma>) (QStateM_map \<Q>)) (Q_domain_var (qr \<sigma>) (QStateM_map \<Q>))
        (QStateM_vector \<Q>) k i =
      aijv (Q_domain_var (q (fst (snd ns'))) (QStateM_map (snd (snd ns'))))
        (Q_domain (QStateM_map (snd (snd ns'))) -
         Q_domain_var (q (fst (snd ns'))) (QStateM_map (snd (snd ns'))))
        (vec_of_list (vl (fst (snd ns')))) k i" 
        using a1 a2 a2' a2'' a3 v2 a4 a6 QStateM_rel1 
              QStateM_vars.rep_eq a9 qstate_def vec_of_list_QStateM_list by auto
      ultimately have "?v!i = vector_i ns' q vl k \<sigma>' ! i" using  a8
        unfolding get_qstate_def get_stack_def vector_aij_def vector_i_def Let_def aij_def 
        by auto
    } thus ?thesis by auto
  qed
  ultimately show ?thesis
    using nth_equalityI by blast  
qed

lemma assest_vectori_v2_empty:
  assumes 
      a0:"QStateM_vars \<Q> = Q_domain_var (q \<sigma> \<union> qr \<sigma>) (QStateM_map \<Q>)" and       
      a1:"ns' = (p * \<delta>k, \<sigma>', \<Q>')" and 
      a2:"q \<sigma>' = q \<sigma>" and a2':"qr \<sigma>' = qr \<sigma> " and       
      a5:"QStateM_map \<Q>' = QStateM_map \<Q>" and     
      a6':"map_qr = snd (split_map (QStateM_map \<Q>) (q \<sigma>))" and      
      a7':"v2 = Q_domain_var (qr \<sigma>) (QStateM_map \<Q>)" and
      a9: "Q2  = QStateM(map_qr, QState(v2, [1]))" and       
      a11:"\<forall>e\<in>q \<sigma>. QStateM_map \<Q> e \<noteq> {}" and a12:"q \<sigma> \<inter> qr \<sigma> = {}" and
      a10:"QStateM_vars \<Q> = \<Union>((QStateM_map \<Q>) ` q \<sigma>)" 
shows "(p, \<sigma>', Q2) \<in>  (qr \<mapsto> vector_i' ns' q vl k)"   
proof-
  have "QStateM_wf (QStateM_unfold \<Q>)"
    using QStateM_wf by blast
  then have QStateM_wf1:"(\<forall>x y. x\<noteq>y \<and> x\<in> domain (QStateM_map \<Q>) \<and> y \<in> domain (QStateM_map \<Q>) \<longrightarrow> 
              QStateM_map \<Q> x \<inter> QStateM_map \<Q> y = {})"
    by auto
  then have "v2 = {}" using a10 a7' a12 unfolding Q_domain_var_def
    by (metis Diff_disjoint Q_domain_var_def SUP_union a0 domain_qr 
              inf_commute inf_sup_absorb sup_commute)
  moreover have "map_qr = (\<lambda>x. {})" using q_map_int[OF a11] a12 a6' a10
    by (metis Compl_iff QStateM_rel1 QStateM_vars.rep_eq Q_domain_var_def 
             Sep_Prod_Instance.none_def 
              UN_iff a0 a7' all_not_in_conv calculation constrain_map_def 
               q_var_in_q_qr qstate_def snd_conv split_map_def) 
  moreover have "vector_i' ns' q vl k = (\<lambda>x. [1])"
    using  vector_i_d2_empty unfolding get_qstate_def get_stack_def apply auto 
    by (metis (full_types) Diff_eq_empty_iff Q_domain_set_def Q_domain_var_def 
          a0 a12 a5 a7' calculation(1) domain_qr local.a1 local.a2)
  ultimately have "(p, \<sigma>', QStateM(map_qr, QState(v2, [1]))) \<in>  (qr \<mapsto> vector_i' ns' q vl k)"
    apply clarify
    apply (rule map_assn_intro)    
    using \<open>vector_i' ns' q vl k = (\<lambda>x. [1])\<close> 
    by (auto simp add: QState_vars_empty Q_domain_def Q_domain_var_def)
  thus ?thesis using a9  by auto
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
      a7:"v1 = Q_domain_var (q \<sigma>) (QStateM_map \<Q>)" and  a10:"QStateM_vars \<Q> \<noteq> \<Union>((QStateM_map \<Q>) ` q \<sigma>)" and
      a7':"v2 = Q_domain_var (qr \<sigma>) (QStateM_map \<Q>)" and a7'':"0 < \<delta>k " and
      a8:"Q2  = QStateM(map_qr, QState(v2, list_of_vec ((1 / sqrt \<delta>k)\<cdot>\<^sub>v(vector_aij v1 v2 (QStateM_vector \<Q>) k))))" and
      a11:"q \<sigma> \<inter> qr \<sigma> = {}" and a12:"\<delta>k = \<rho> q vl k ns'" and a13:"QStateM_list \<Q> = vl \<sigma> "
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
  then have v2_not_empty:"v2\<noteq>{}" using a10
    using Q_domain_var_def a0 a7' by auto
  moreover have a02:"list_of_vec (complex_of_real (1 / sqrt \<delta>k) \<cdot>\<^sub>v
                       vector_aij (Q_domain_var (q \<sigma>) (QStateM_map \<Q>))
                       (Q_domain_var (qr \<sigma>) (QStateM_map \<Q>)) (QStateM_vector \<Q>) k) =
                     local.vector_i ns' q vl k \<sigma>'" 
    using assest_vectori1[of \<Q> q \<sigma> qr, OF a0 a1 a2 a2' a2'' a5 a7 a10 a7' a11 a12 a13] by auto
  moreover have a03:"QState_wf(v2,list_of_vec ((1 / sqrt \<delta>k)\<cdot>\<^sub>v(vector_aij v1 v2 (QStateM_vector \<Q>) k)))"
    using a3' a4 v2_not_empty unfolding vector_aij_def by auto     
  moreover have a04:"QStateM_wf (map_qr, QState(v2, list_of_vec ((1 / sqrt \<delta>k)\<cdot>\<^sub>v(vector_aij v1 v2 (QStateM_vector \<Q>) k))))"  
      using a6 a6' a7 a8 
      apply auto
      using QState_var_idem Q_domain_def Q_domain_var_def a03 constrain_map_def split_map_def apply auto[1]
      using QState_var_idem Q_domain_def Q_domain_var_def a03 a01
      apply (metis (no_types, lifting) Sep_Prod_Instance.none_def UN_I a6'' a7' empty_iff)
      unfolding  domain_def none_def split_map_def constrain_map_def 
      using v2_not_empty
      apply auto
      apply (metis (no_types, lifting) QStateM_rel1 QStateM_vars.rep_eq UN_I a0 a7' q_var_in_q_qr qstate_def) 
      using v2_not_empty apply auto 
       apply (smt QState.rep_eq QState_vars.rep_eq Q_domain_def Q_domain_var_def UNIV_I UN_iff a01 a6' a7' equals0D fstI)
      using QStateM_wf1 unfolding domain_def apply auto
      by (metis (no_types, lifting) IntI equals0D)
   have "(p, \<sigma>', QStateM(map_qr, QState(v2, list_of_vec ((1 / sqrt \<delta>k)\<cdot>\<^sub>v(vector_aij v1 v2 (QStateM_vector \<Q>) k))))) \<in>  (qr \<mapsto> vector_i ns' q vl k)"   
      apply (rule map_assn_intro)
      using a7' a01
      apply (simp add: a6')
      using a02 a7 a7' apply blast
      using a04 apply blast
      using a03 by blast
    thus ?thesis
      using a8 by blast   
    show "(qr \<mapsto> local.vector_i ns' q vl k) \<subseteq> (qr \<mapsto> local.vector_i ns' q vl k)"
      by auto
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
      a13:"0 < \<delta>k" and a14:"\<delta>k = \<rho> q vl k ns'" and a15:"QStateM_list \<Q> = vl \<sigma> " and
      a16:"QStateM_vars \<Q> \<noteq> \<Union>((QStateM_map \<Q>) ` q \<sigma>)" 
    shows "(p, \<sigma>', \<Q>') \<in> (q \<mapsto> local.unit_vecl ns' q k \<and>\<^sup>* qr \<mapsto> vector_i ns' q vl k)"
proof-
  let ?q = "q \<sigma>" and ?qr = "qr \<sigma>" and ?v = "vec_of_list (vl \<sigma>)" and
      ?q' = "q \<sigma>'" and ?qr' = "qr \<sigma>'" and ?v' = "vl \<sigma>'" 
  let ?v1 = "Q_domain_var ?q (QStateM_map \<Q>)" and ?v2 = "Q_domain_var ?qr (QStateM_map \<Q>)"
  let ?M = "(1\<^sub>k (2 ^ card (\<Union> (QStateM_map \<Q> ` q \<sigma>))))"
  let ?n = "Re ((vec_norm
             (QStateM_vector
               (matrix_sep ?q \<Q> 1\<^sub>k (2 ^ card (\<Union> (QStateM_map \<Q> ` ?q))))))\<^sup>2 /
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
    using domain_Q[of q \<sigma> \<Q> k qr vl, OF a1 a2 a3 a4 a6 a7] by auto 
  have delta:"\<delta>k = \<rho> q vl k ns'" and q'_vars:"QStateM_vars \<Q>' = ?v1 \<union> ?v2" and
       q'_vector:"QStateM_vector \<Q>' = (1 / sqrt \<delta>k) \<cdot>\<^sub>v ptensor_vec ?v1 ?v2 (unit_vec (2^(card ?v1)) k) (vector_aij ?v1 ?v2 (QStateM_vector \<Q>) k)"
    using sound_prob_semant_proof[OF assms(1-14)] by auto
  
  let ?map_q = "fst (split_map (QStateM_map \<Q>) (q \<sigma>))" and
      ?map_qr = "snd (split_map (QStateM_map \<Q>) (q \<sigma>))" and 
       ?V1 = "list_of_vec (unit_vec (2^(card ?v1)) k)" and 
       ?V2 = "list_of_vec ((1 / sqrt \<delta>k)\<cdot>\<^sub>v(vector_aij ?v1 ?v2 (QStateM_vector \<Q>) k))"
  let ?Q1 = "QStateM(?map_q, QState(?v1, ?V1))"
  let ?Q2 = "QStateM(?map_qr, QState(?v2, ?V2))"
  have map_qr_cons:"?map_qr = constrain_map (QStateM_map \<Q>) (qr \<sigma>)" 
    using split_q1_constrain_q2
    by (simp add: QStateM_wf1 Q_domain a3 a6)
  
  have v1_q_wf:"QState_wf (?v1, ?V1)"
    by (simp add: f1 v1_not_empty)
  then have v1_qm_wf:"QStateM_wf (?map_q, QState(?v1, ?V1))"
    using QStateM_wf1 QState_var_idem constrain_map_wf1 
      q_domain_split_eq_q_domain_var split_map_def by auto             
  have v2_q_wf:"QState_wf (?v2, ?V2)" 
    using f2 a16 a3 unfolding vector_aij_def Q_domain_var_def by auto             
  then have v2_qm_wf:"QStateM_wf (?map_qr, QState(?v2, ?V2))"
    using QStateM_wf1 QState_var_idem constrain_map_wf1 
      map_qr_cons q_domain_constrain_eq_q_domain_var by force
 
  have a00:"(1, \<sigma>', ?Q1) \<in> (q \<mapsto> local.unit_vecl ns' q k)" 
    using assest_unit[of \<Q> q \<sigma> qr, OF a3 a8 a9 f1 v1_not_empty a12]
    by blast   
  moreover have a01:"(p, \<sigma>', ?Q2) \<in> (qr \<mapsto> vector_i ns' q vl k)"
    using assest_vectori[of \<Q> q \<sigma> qr, OF a3 a8 a9 a10 a11 v1_not_empty f2 a12 _ _ map_qr_cons _ a16 _ a13 _ a6 a14 a15]
    by auto
  moreover have a03:"?Q1 ## ?Q2" 
  proof-    
     have "?map_q ## ?map_qr" and "QState(?v1, ?V1) ## QState(?v2, ?V2)"
      using local.a1 q_map_int apply blast 
      unfolding sep_disj_QState disj_QState_def 
      using v2_q_wf v1_q_wf inter_12 QState_var_idem  
      by presburger       
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
        using q'_vector f1
        by (simp add: pscalar_ptensor_2[OF inter_12 f1 f2] vec_list vector_aij_def) 
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


lemma  Q_in_disjunction_conj_unit_vector2:
  assumes a0:"(\<delta>k, \<Q>') = measure_vars' k (q \<sigma>) \<Q>" and 
      a1:"(\<forall>e\<in>q \<sigma>. QStateM_map \<Q> e \<noteq> {})" and
      a2:"k < 2 ^ card (\<Union> (QStateM_map \<Q> ` q \<sigma>))" and
      a3:"QStateM_vars \<Q> = Q_domain_var (q \<sigma> \<union> qr \<sigma>) (QStateM_map \<Q>)" and
      a4:"QStateM_list \<Q> = vl \<sigma>" and
      a5:" QStateM_vars \<Q> \<noteq> {}" and
      a6:"q \<sigma> \<inter> qr \<sigma>  = {}" and a7:"q \<sigma> \<noteq> {}" and 
      a8:"ns' = (p * \<delta>k, \<sigma>', \<Q>')" and 
      a9:"q \<sigma>' = q \<sigma> " and a10:"qr \<sigma>' = qr \<sigma>" and a11:"vl \<sigma>' = vl \<sigma>" and
      a12:"QStateM_map \<Q>' = QStateM_map \<Q>" and
      a13:"0 < \<delta>k" and a14:"\<delta>k = \<rho> q vl k ns'" and a15:"QStateM_list \<Q> = vl \<sigma> " and
      a16:"QStateM_vars \<Q> = \<Union>((QStateM_map \<Q>) ` q \<sigma>)" 
    shows "(p, \<sigma>', \<Q>') \<in> (q \<mapsto> local.unit_vecl ns' q k \<and>\<^sup>* qr \<mapsto> vector_i' ns' q vl k)"
proof-
  have vector_i':"vector_i' ns' q vl k = (\<lambda>st. [1])"
    using vector_i_d2_empty a3 a16
      unfolding get_stack_def get_qstate_def Q_domain_var_def apply auto
      using domain_Q[of q \<sigma> \<Q> k qr vl, OF a1 a2 a3 a4 a6 a7]
      by (simp add: a12 a8 a9)
  let ?q = "q \<sigma>" and ?qr = "qr \<sigma>" and ?v = "vec_of_list (vl \<sigma>)" and
      ?q' = "q \<sigma>'" and ?qr' = "qr \<sigma>'" and ?v' = "vl \<sigma>'" 
  let ?v1 = "Q_domain_var ?q (QStateM_map \<Q>)" and ?v2 = "Q_domain_var ?qr (QStateM_map \<Q>)"
  let ?M = "(1\<^sub>k (2 ^ card (\<Union> (QStateM_map \<Q> ` q \<sigma>))))"
  let ?n = "Re ((vec_norm
             (QStateM_vector
               (matrix_sep ?q \<Q> 1\<^sub>k (2 ^ card (\<Union> (QStateM_map \<Q> ` ?q))))))\<^sup>2 /
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
       v2:"?v2 = {}"
    using domain_Q[of q \<sigma> \<Q> k qr vl, OF a1 a2 a3 a4 a6 a7] a16        
    by (auto simp add: Q_domain_var_def) 
  have delta:"\<delta>k = \<rho> q vl k ns'" and q'_vars:"QStateM_vars \<Q>' = ?v1 \<union> ?v2" and
       q'_vector:"QStateM_vector \<Q>' = unit_vec (2 ^ card (Q_domain_var (q \<sigma>) (QStateM_map \<Q>))) k"
    using sound_prob_semant_proof2[OF assms(1-14) assms(17)] by auto
  
  let ?map_q = "fst (split_map (QStateM_map \<Q>) (q \<sigma>))" and
      ?map_qr = "snd (split_map (QStateM_map \<Q>) (q \<sigma>))" and 
       ?V1 = "list_of_vec (unit_vec (2^(card ?v1)) k)" and 
       ?V2 = "[1]"
  let ?Q1 = "QStateM(?map_q, QState(?v1, ?V1))"
  let ?Q2 = "QStateM(?map_qr, QState(?v2, ?V2))"
  have map_qr_cons:"?map_qr = constrain_map (QStateM_map \<Q>) (qr \<sigma>)" 
    using split_q1_constrain_q2
    by (simp add: QStateM_wf1 Q_domain a3 a6)
  
  have v1_q_wf:"QState_wf (?v1, ?V1)"
    by (simp add: f1 v1_not_empty)
  then have v1_qm_wf:"QStateM_wf (?map_q, QState(?v1, ?V1))"
    using QStateM_wf1 QState_var_idem constrain_map_wf1 
      q_domain_split_eq_q_domain_var split_map_def by auto             
  have v2_q_wf:"QState_wf (?v2, ?V2)" 
    using  a3 QStateM_wf1 v2   by auto         
  then have v2_qm_wf:"QStateM_wf (?map_qr, QState(?v2, ?V2))"
    using QStateM_wf1 QState_var_idem constrain_map_wf1 
      map_qr_cons q_domain_constrain_eq_q_domain_var by force
 
  have a00:"(1, \<sigma>', ?Q1) \<in> (q \<mapsto> local.unit_vecl ns' q k)" 
    using assest_unit[of \<Q> q \<sigma> qr, OF a3 a8 a9 f1 v1_not_empty a12]
    by blast   
  moreover have a01:"(p, \<sigma>', ?Q2) \<in> (qr \<mapsto> vector_i' ns' q vl k)"
    using assest_vectori_v2_empty[of \<Q> q \<sigma> qr, OF a3 a8 a9 a10 a12 _ _ _ a1 a6 a16]
    by auto
  moreover have a03:"?Q1 ## ?Q2" 
  proof-    
     have "?map_q ## ?map_qr" and "QState(?v1, ?V1) ## QState(?v2, ?V2)"
      using local.a1 q_map_int apply blast 
      unfolding sep_disj_QState disj_QState_def 
      using v2_q_wf v1_q_wf inter_12 QState_var_idem  
      by presburger       
    then show ?thesis using v2_qm_wf v1_qm_wf
      by (simp add: QStateM_wf_map QStateM_wf_qstate sep_disj_QStateM)      
  qed    
  ultimately have "(1*p, \<sigma>', ?Q1 + ?Q2) \<in> (q \<mapsto> local.unit_vecl ns' q k \<and>\<^sup>* qr \<mapsto> vector_i' ns' q vl k)"
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
        using q'_vector f1 apply auto
        by (simp add: idempoten_qstate v2 vec_list) 
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

lemma  Q_in_disjunction_conj_unit_vectori':
  assumes a0:"(\<delta>k, \<Q>') = measure_vars' k (q \<sigma>) \<Q>" and 
      a1:"(\<forall>e\<in>q \<sigma>. QStateM_map \<Q> e \<noteq> {})" and
      a2:"k < 2 ^ card (\<Union> (QStateM_map \<Q> ` q \<sigma>))" and
      a3:"QStateM_vars \<Q> = Q_domain_var (q \<sigma> \<union> qr \<sigma>) (QStateM_map \<Q>)" and
      a4:"QStateM_list \<Q> = vl \<sigma>" and
      a5:" QStateM_vars \<Q> \<noteq> {}" and
      a6:"q \<sigma> \<inter> qr \<sigma>  = {}" and a7:"q \<sigma> \<noteq> {}" and 
      a8:"ns' = (p * \<delta>k, \<sigma>', \<Q>')" and 
      a9:"q \<sigma>' = q \<sigma> " and a10:"qr \<sigma>' = qr \<sigma>" and a11:"vl \<sigma>' = vl \<sigma>" and
      a12:"QStateM_map \<Q>' = QStateM_map \<Q>" and
      a13:"0 < \<delta>k" and a14:"\<delta>k = \<rho> q vl k ns'" and a15:"QStateM_list \<Q> = vl \<sigma> "      
    shows "(p, \<sigma>', \<Q>') \<in> (q \<mapsto> local.unit_vecl ns' q k \<and>\<^sup>* qr \<mapsto> vector_i' ns' q vl k)"
  
proof-
  { assume a00:"QStateM_vars \<Q> \<noteq> \<Union>((QStateM_map \<Q>) ` q \<sigma>)"
    moreover have "vector_i' ns' q vl k = vector_i ns' q vl k" 
      using eq_vector_i a3 calculation
      unfolding get_stack_def get_qstate_def Q_domain_var_def apply auto
      using domain_Q[of q \<sigma> \<Q> k qr vl, OF a1 a2 a3 a4 a6 a7]
      by (metis Diff_eq_empty_iff Q_domain_var_def UN_I a12 a8 a9 equals0D)
    moreover have "measure_vars k (q \<sigma>) \<Q> = measure_vars' k (q \<sigma>) \<Q>"
      using a00 measure_vars'_neq by presburger
    ultimately have ?thesis  
      using Q_in_disjunction_conj_unit_vector1[of \<delta>k \<Q>' k q \<sigma> \<Q> qr vl, OF _ assms(2-16)] a00 
      by (simp add: a0)
  }                                  
  moreover {
    assume a00:"QStateM_vars \<Q> = \<Union>((QStateM_map \<Q>) ` q \<sigma>)"
    then have "vector_i' ns' q vl k = (\<lambda>st. [1])"
    using vector_i_d2_empty a3 calculation
      unfolding get_stack_def get_qstate_def Q_domain_var_def apply auto
      using domain_Q[of q \<sigma> \<Q> k qr vl, OF a1 a2 a3 a4 a6 a7]
      by (simp add: a12 a8 a9)
    then have ?thesis using Q_in_disjunction_conj_unit_vector2[OF _ assms(2-16)]
      using a0 a00 by linarith
  }
  ultimately show ?thesis by auto
qed  

lemma meassure_sound: 
  assumes a0:"v \<in> nat_vars" and a1:"not_access_v q v" and 
          a2:"not_access_v vl v" and a3:"not_access_v qr v" and a4:"v\<in> variables"
  shows "\<Turnstile> (q\<cdot>qr \<mapsto> vl) v:=meassure q
            {s. s \<in> (\<Union>i\<in>{q}\<^sub>s. 
                       (v\<down>\<^sub>(from_nat i)) \<inter>
                       ((q \<mapsto> local.unit_vecl s q i \<and>\<^sup>* qr \<mapsto> vector_i' s q vl i) \<smile>
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
                (\<delta>k, \<Q>') = measure_vars' k (q \<sigma>) \<Q> \<and> 0 < \<delta>k"
      by (rule QExec_Normal_elim_cases(8)[OF a00[simplified a01]], 
             auto intro: simp add: dest_assign)
    let ?\<sigma>' = "set_value \<sigma> v (from_nat k)"
    have q:"q \<sigma> = q ?\<sigma>'" using a0 a1 step
      using a4 from_nat_in_vdomain not_access_v_f_q_eq_set by blast
    have qr:"qr \<sigma> = qr ?\<sigma>'" using a0 a3 step
      using a4 from_nat_in_vdomain not_access_v_f_q_eq_set by blast
    have vl:"vl \<sigma> = vl ?\<sigma>'"
      using a0 a2 step a4
      using from_nat_in_vdomain not_access_v_f_q_eq_set by blast
    have q_state_q_q':"QStateM_map \<Q> = QStateM_map \<Q>'"
      using q qr vl  dest_assign[simplified q qr vl]
      measure_vars'_QStateM_map[of "q \<sigma>" \<Q>  \<delta>k \<Q>' k, simplified q qr vl] step  
      by auto    
    have "\<delta>k = \<rho> q vl k ns'" 
      using step dest_assign q_state_q_q' q qr vl sound_prob_semant_proof_rho
      by (force intro:sound_prob_semant_proof_rho)
    have "ns' \<in> ((v\<down>\<^sub>(from_nat k)) \<inter>
                 ((q \<mapsto> local.unit_vecl ns' q k \<and>\<^sup>* qr \<mapsto> vector_i' ns' q vl k) \<smile>
                 \<rho> q vl k ns'))" 
    proof-
      obtain a b c where "ns' = (a,b,c)"
        using local.step by blast
      have "(p, set_value \<sigma> v (from_nat k), \<Q>') \<in> (q \<mapsto> local.unit_vecl ns' q k \<and>\<^sup>* qr \<mapsto> vector_i' ns' q vl k)"         
        apply (rule Q_in_disjunction_conj_unit_vectori'[of \<delta>k \<Q>' k q \<sigma> \<Q> qr vl ns' p ?\<sigma>'])
        using local.step dest_assign q qr vl q_state_q_q' \<open>\<delta>k = \<rho> q vl k ns'\<close> 
        by (auto intro: Q_in_disjunction_conj_unit_vectori'[of \<delta>k \<Q>' k q \<sigma> \<Q> qr vl ns' p ?\<sigma>'])
      moreover have "\<delta>k = \<rho> q vl k ns'" 
        using step dest_assign q_state_q_q' q qr vl sound_prob_semant_proof_rho      
        by (force intro:sound_prob_semant_proof_rho)
      
      ultimately have "ns' \<in> (q \<mapsto> local.unit_vecl ns' q k \<and>\<^sup>* qr \<mapsto> vector_i' ns' q vl k) \<smile>
                        \<rho> q vl k ns'"
        using prob_assert_intro[of \<delta>k] step by fastforce               
      moreover have "ns' \<in> (v\<down>\<^sub>(from_nat k))"
        by (simp add: a4 get_set get_stack_def local.step set_value_def val_var_def)      
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
                 ((q \<mapsto> local.unit_vecl s q i \<and>\<^sup>* qr \<mapsto> vector_i' s q vl i) \<smile>
                 \<rho> q vl i s))}" 
      unfolding card_set_q_def Let_def Q_domain_set_def  by fast
    then have "s' \<in> Normal ` {s. s \<in> (\<Union>i\<in>{q}\<^sub>s.
                           (v\<down>\<^sub>(from_nat i)) \<inter>
                           ((q \<mapsto> local.unit_vecl s q i \<and>\<^sup>* qr \<mapsto> vector_i' s q vl i) \<smile>
                           \<rho> q vl i s))}"
      using step by auto
  } thus ?thesis unfolding valid_def by auto
qed

(* lemma dispose_sound:
  assumes a0:"qv = (\<lambda>s. fst (get_qstate s))" and a1:"st = get_stack" and
    a2:"not_access_v n q" and
    a3:"n = (\<lambda>s. vec_norm (vec_of_list (v1 s)))" and
    a4:"P =
    (\<llangle>q\<rrangle> 1\<mapsto>\<^sub>l v1) \<inter> (q1 1\<mapsto>\<^sub>l v2) \<inter> (\<llangle>q\<rrangle> \<inter>\<^sub>s q1) \<inter>
    {s. get_qstate s = s1 + s2 \<and>
        Q_domain (fst s1) = Q_domain_set \<llangle>q\<rrangle> (qv s) (st s) \<and>
        Q_domain (fst s2) = Q_domain_set q1 (qv s) (st s) \<and>
        set_qstate s (QStateM (fst s2, snd s2 + n (st s) \<cdot>\<^sub>q |>)) \<in> Q}"
  shows "\<Turnstile>P Dispose q Q"
  sorry
*)

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
    by (fastforce intro: QExec_Normal_elim_cases(3))
next
  case (QMod q_v st qs M Q) 
  then show ?case unfolding valid_def   
    unfolding get_stack_def get_QStateM_def set_qstate_def get_prob_def get_qstate_def Q_domain_set_def    
    apply clarsimp
    by (rule  QExec_Normal_elim_cases(4)[of M], auto)    
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
             by - auto
           from this _
           show "\<sigma>'' \<in> Normal ` (P \<inter> {s. get_stack s \<in> - b})"
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
  case (QDispose q n v i)
  then show ?case using dispose_sound by auto
next
  case (QMeasure v q vl qr)
  then show ?case using meassure_sound by auto
next
  case (Frame P c Q A)
  then show ?case sorry
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


lemma QDispose':
  assumes a0:"q \<in> variables" and a1:"q \<in> nat_vars \<or> q \<in> nat_list_vars" and 
          a2:"n = (\<lambda>s. vec_norm (vec_of_list (v s)))"
        shows "\<turnstile> ((q\<cdot>i \<mapsto>\<^sub>v v) \<and>\<^sup>* R) (Dispose q i) (( |>a\<^sub>n) \<and>\<^sup>* R)"
  using QDispose[OF a0 a1, of _ "(q\<cdot>i \<mapsto>\<^sub>v v)" i "( |>a\<^sub>n)" R]
  apply auto

end
end
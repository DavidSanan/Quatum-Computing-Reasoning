theory Quantum_Separation_LogicDef
  imports QSemanticsBig 
begin

type_synonym ('s,'p) triplet = "('s state) assn \<times> 'p \<times> ('s state) assn"




definition Q_domain_set::"'s expr_q \<Rightarrow> q_vars \<Rightarrow> 's expr_q "
  where "Q_domain_set q qvars \<equiv> (\<lambda>s. \<Union> (qvars ` q s))"




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

definition QState\<^sub>s :: "('s state) set \<Rightarrow> (complex) QStateM set"
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

definition map_assn'::"'s expr_q \<Rightarrow> 's expr_q \<Rightarrow> ('s, (complex) QState) expr \<Rightarrow> (('s state) set)"  
 ("_\<cdot>_ \<mapsto> _"  [1000, 20, 1000] 60)
  where "map_assn' q1 q2 v \<equiv> let qs = (\<lambda>s. snd (get_qstate s));
                                  st = (\<lambda>s. get_stack s) in   
                 {s. fst s = 1 \<and>(q1 (st s) \<union> q2 (st s)) \<noteq> {} \<and> (qs s) = (v (st s)) \<and>
                      (\<exists>\<qq>' \<qq>''. (get_QStateM s) = \<qq>' +  \<qq>'' \<and> \<qq>' ## \<qq>'' \<and> 
                                (q1 (st s)) = QStateM_vars \<qq>' \<and>
                                (q1 (st s)) = QStateM_vars \<qq>')}"

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
                 {s. QState_vars (qs s)  = Q_domain_var (set_v (st s)) (qv s) \<and>
                     QState_list (qs s) = (q (st s))}"

definition prob_assert::" (('s state) set) \<Rightarrow>  real \<Rightarrow> (('s state) set)"
(infixr "\<smile>" 60)
  where "prob_assert q p \<equiv> {s. fst s = p \<and> snd s \<in> {(x,y). \<exists>p. (p,(x,y)) \<in> q}} "

definition int_stack_ass::"('s,'a set) expr \<Rightarrow> ('s, 'a set) expr \<Rightarrow> (('s state) set)"
(infixr "\<inter>\<^sub>{\<^sub>}" 35)
  where "int_stack_ass q1 q2 \<equiv> let st = (\<lambda>s. get_stack s) in   
                 {s. q1 (st s) \<inter> q2 (st s) = {}}"

(* definition empty_state_norm_expr::"('s, complex) expr \<Rightarrow> ('s , complex QState) expr"
("|>\<^sub>_" 50)
where "empty_state_norm_expr n \<equiv> (\<lambda>s. (n s) \<cdot>\<^sub>q |>)" *)

definition empty_qstatem_norm_expr::"('s, complex) expr \<Rightarrow> ('s , complex QStateM) expr"
("|>\<^sub>_" 50)
where "empty_qstatem_norm_expr n \<equiv> (\<lambda>s. QStateM ({}\<^sub>q, (n s) \<cdot>\<^sub>q |>))"


definition empty_qstatem_norm_ass::"('s, complex) expr \<Rightarrow> (('s state) set)"
("/|>a\<^sub>_" 50)
where "empty_qstatem_norm_ass n \<equiv> let h = |>\<^sub>n in 
                                 {s. get_QStateM s = (h (get_stack s))}"


definition Q_sep_dis_q::"(('s state) set) \<Rightarrow> (('s state) set) \<Rightarrow>  (('s state) set)" 
(infixr "\<and>\<^sub>q" 35)
where "Q_sep_dis_q q1 q2 \<equiv> {s. ((\<lambda>s. s \<in> (snd ` (snd ` q1))) \<and>* 
                                (\<lambda>s. s \<in> (snd ` (snd ` q2)))) (snd (snd s))}"

definition QState_expr::"('s , nat set) expr \<Rightarrow> ('s, complex list) expr \<Rightarrow> ('s,complex QState) expr"
  where "QState_expr v l \<equiv>  (\<lambda>s. QState (v s, l s))"

definition QState_plus_expr::"('s,complex QState) expr \<Rightarrow> ('s,complex QState) expr \<Rightarrow> ('s,complex QState) expr"
(infixr "+\<^sub>e" 50)
  where "QState_plus_expr q1 q2 \<equiv> (\<lambda>s. (q1 s) + (q2 s))"

definition QStateM_expr::"('s,complex QState) expr \<Rightarrow> ('s state, complex QStateM) expr"
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

definition aij::"'s expr_q \<Rightarrow> q_vars \<Rightarrow> ('s, (complex) QState) expr \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>'s  \<Rightarrow>  complex"
  where "aij f qvars v i j\<equiv>  
                 (\<lambda>s. vector_element_12 (v s) (Q_domain_set f qvars s) (i,j))"


(* definition aij::"'s expr_q \<Rightarrow> ('s state, (complex) QState) expr \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>'s state \<Rightarrow>  complex"
  where "aij v f i j\<equiv>  let qv = (\<lambda>s. fst (get_qstate s)); 
                            st = (\<lambda>s. get_stack s) in 
                 (\<lambda>s. vector_element_12 (f s) (v (st s, qv s)) (i,j))" *)

(* definition v_f::"'s expr_q \<Rightarrow>( nat \<Rightarrow>'s state \<Rightarrow>  complex) \<Rightarrow> ('s state, (complex) QState) expr"
  where "v_f q f \<equiv> let vars = Q_domain_set q in 
                     (\<lambda>s. QState(vars s, 
                          map (\<lambda>e. f e s) [0..<2^card (vars s)]))" *)

definition v_f::"'s expr_q \<Rightarrow> q_vars \<Rightarrow> ( nat \<Rightarrow>'s  \<Rightarrow>  complex) \<Rightarrow> ('s, (complex) QState) expr"
  where "v_f q qvars f \<equiv> let vars = Q_domain_set q qvars in 
                     (\<lambda>s. QState(vars s, map (\<lambda>e. f e s) [0..<2^card (vars s)]))"


definition var_exp::"'v \<Rightarrow> 's \<Rightarrow> nat set"
("\<llangle>_\<rrangle>"  [] 1000)
where "var_exp q  \<equiv> \<lambda>\<sigma>. {to_nat (get_value \<sigma> q)}"



definition valid::"[('s state) assn,('v, 's) com,('s state) assn] \<Rightarrow> bool"
    ("\<Turnstile>_ _ _"  [1000, 20, 1000] 60)
    where "\<Turnstile> P c Q \<equiv> \<forall>\<sigma> \<sigma>'. \<turnstile> \<langle>c,\<sigma>\<rangle> \<Rightarrow> \<sigma>' \<longrightarrow> \<sigma> \<in> Normal ` P \<longrightarrow> \<sigma>' \<in> Normal ` Q"

definition \<SS>::"('s state) set \<Rightarrow> ('s \<Rightarrow> real \<Rightarrow> complex QStateM \<Rightarrow> bool)"
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

inductive "hoarep"::"[('s state) assn,('v,'s) com, ('s state) assn] => bool"
    ("\<turnstile>(_/ (_)/ _)" [1000,20,1000]60)
where
  Skip: "\<turnstile> Q Skip Q"

| SMod: "\<turnstile>{s.  set_stack s (f (get_stack s)) \<in> Q} (SMod f) Q"
         
| QMod: " \<turnstile> {s. q_v = fst (get_qstate s) \<and> q_s = snd (get_qstate s) \<and> st = get_stack s \<and>
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

(* | QAlloc: " \<turnstile> {s. qv = fst (get_qstate s) \<and> qs = snd (get_qstate s) \<and> st = get_stack s \<and>
                  length (v st) = (e st) \<and> e st \<noteq> 0 \<and>
                  vs = (SOME x. x \<in>new_q_addr e s) \<and> q' = (SOME q. q \<notin> (dom_q_vars qv)) \<and>                  
                  set_stack
                      (set_qstate s (qv (q':=vs) , qs + QState (vs ,(v st)) ) ) 
                      (set_value st q (from_nat q'))
                    \<in> Q} 
              (Alloc q e v) Q" *)
(* | QAlloc:"qv = (\<lambda>s. fst (get_qstate s)) \<and> st =(\<lambda>s. get_stack s) \<Longrightarrow> not_access_v v q \<Longrightarrow> not_access_v e q \<Longrightarrow>         
          q \<in> variables \<Longrightarrow> 
          \<turnstile> {s. ((qv s)(the_elem ((\<llangle>q\<rrangle>) (st s))) = {}) \<and> is_singleton ((\<llangle>q\<rrangle>) (st s)) \<and>
                 length (v (st s)) = (e (st s)) \<and> (from_nat (the_elem ((\<llangle>q\<rrangle>) (st s)))) \<in> v_domain q \<and>
                 QState_list (Qs (st s)) = (v (st s)) \<and> s' = set_stack s (set_value (st s) q (from_nat (the_elem ((\<llangle>q\<rrangle>) (st s))))) \<and>                 
                 (set_stack s (set_value (st s) q (from_nat (the_elem ((\<llangle>q\<rrangle>) (st s)))))) \<in> ((\<llangle>q\<rrangle>) \<mapsto>\<^sub>l Qs)}
              (Alloc q e v) (\<llangle>q\<rrangle> \<mapsto>\<^sub>l Qs)"
*)
| QAlloc:"not_access_v v q \<Longrightarrow> not_access_v (\<SS> R) q \<Longrightarrow>         
          q \<in> variables \<Longrightarrow> q \<in> nat_vars \<Longrightarrow> \<forall>\<sigma>. length (v \<sigma>) > 1 \<Longrightarrow>
          \<turnstile> R q:=alloc v ((q\<cdot>f \<mapsto>\<^sub>v v) \<smile> 1 \<and>\<^sup>* R)"


\<comment>\<open>In QDispose we set that Qs does not depend on the stack to avoid that 
   the n in the postcondition may also depend on the stack and gives unsound results
  in later modifications to the stack that may not affect the vector\<close>
(* | QDispose: "not_access_v n q \<Longrightarrow>               
             n = (\<lambda>s. vec_norm (vec_of_list (v1 s))) \<Longrightarrow>
             P = (\<llangle>q\<rrangle> \<mapsto>\<^sub>l v1) \<inter> (q1 \<mapsto>\<^sub>l v2) \<inter> (\<llangle>q\<rrangle> \<inter>\<^sub>{\<^sub>} q1) \<inter>
             {s. set_qstate s 
                 ((QStateM_expr ((QState_expr q1 v2) +\<^sub>e |>\<^sub>n)) s) \<in> Q} \<Longrightarrow> 
              \<turnstile> P (Dispose q) Q"  *)

 | QDispose: "q \<in> variables \<Longrightarrow> q \<in> nat_vars \<or> q \<in> nat_list_vars  \<Longrightarrow>            
               n = (\<lambda>s. vec_norm (vec_of_list (v s))) \<Longrightarrow>                  
              \<turnstile> ((q\<cdot>i \<mapsto>\<^sub>v v) \<and>\<^sup>* R) (Dispose q i) (( |>a\<^sub>n) \<and>\<^sup>* R)"  

(* | QMeasure1: " \<turnstile> {s.  \<exists>k. pr = get_prob s \<and> qv = fst (get_qstate s) \<and> qs = snd (get_qstate s) \<and> st = get_stack s \<and> 
                 q (st, qv) \<subseteq> (QState_vars qs) \<and> 
                 (\<delta>k, q') = measure_vars k (q (st, qv)) (qv,qs) \<and> 
                 st' = set_value st v (from_nat (pr * \<delta>k)) \<and>               
                set_prob (set_stack (set_qstate s q') st') (pr * \<delta>k) \<in> Q} 
               (Measure v q) Q"  *)

(* | QMeasure: "st = (\<lambda>s. get_stack s)  \<Longrightarrow>
             (\<forall>s1 s2. (st s1)\<noteq>(st s2) \<longrightarrow> Qs s1 = Qs s2) \<Longrightarrow>
             \<rho> = (\<lambda>i s. (\<Sum>j\<in> (QState_vars (Qs s) - Q_domain_set q s). norm (aij q Qs i j s )^2) / 
                        (\<Sum>i\<in>Q_domain_set q s. 
                            \<Sum>j\<in> (QState_vars (Qs s) - Q_domain_set q s). norm (aij q Qs i j s )^2 )) \<Longrightarrow>               
             \<Psi> = (\<lambda>i. ((q \<cdot> (\<lambda>s. {}) \<mapsto>  (\<lambda>s. QState (Q_domain_set q s, unit_vecl (2^card (Q_domain_set q s)) i))) \<and>\<^sup>* 
                        (qr \<cdot> (\<lambda>s. {}) \<mapsto> (v_f qr (\<lambda>j s. (aij q Qs i j s) / sqrt (\<rho> i s)) )))) \<Longrightarrow>
               \<turnstile> ((q \<cdot> qr \<mapsto> Qs) \<inter> ({s. \<exists>i\<in>Q_domain_set q s. \<Phi> (set_stack s (set_value (st s) v (from_nat i)))}))
                    (Measure v q) 
                  ((\<Union>i\<in>A. \<Psi> i) \<inter> {s. \<Phi> s})" *)

| QMeasure: "st = (\<lambda>s. get_stack s) \<and> qv = (\<lambda>s. fst (get_qstate s)) \<Longrightarrow> \<Q> = (\<lambda>\<sigma>. Q_domain_set q (qv \<sigma>) (st \<sigma>)) \<Longrightarrow>
             not_access_v q v \<Longrightarrow>  not_access_v Qs v \<Longrightarrow>
             \<rho> = (\<lambda>i qv s. (\<Sum>j\<in> (QState_vars (Qs (st s)) - \<Q> s). norm (aij q (qv s) Qs i j (st s) )^2) / 
                        (\<Sum>i\<in>\<Q> s. 
                            \<Sum>j\<in> (QState_vars (Qs (st s)) - \<Q> s). norm (aij q (qv s) Qs i j (st s) )^2 )) \<Longrightarrow>               
             \<Psi> = (\<lambda>i. {\<sigma>. \<sigma> \<in> ((q \<cdot> (\<lambda>s. {}) \<mapsto>  (\<lambda>s. QState (\<Q> \<sigma>, unit_vecl (2^card (\<Q> \<sigma>)) i))) \<and>\<^sup>* 
                        (qr \<cdot> (\<lambda>s. {}) \<mapsto> (v_f qr (qv \<sigma>) (\<lambda>j s. (aij q (qv \<sigma>) Qs i j s) / sqrt (\<rho> i qv \<sigma>)) )))}) \<Longrightarrow>
               \<turnstile> ((q \<cdot> qr \<mapsto> Qs) \<inter> ({s. \<exists>i\<in> \<Q> s. \<Phi> (set_stack s (set_value (st s) v (from_nat i)))}))
                    (Measure v q)   
                  ((\<Union>i\<in>A. \<Psi> i) \<inter> {s. \<Phi> s})" 

| Frame: "\<turnstile> P c Q \<Longrightarrow> {v. (\<exists>p q. access_v  (\<lambda>s. (p, (s,q)) \<in> A) v = True)} \<inter> 
                      modify_locals c = {} \<Longrightarrow> \<turnstile> (P \<and>\<^sup>* A) c (Q \<and>\<^sup>* A)"

| Conseq: "\<forall>s \<in> P. \<exists>P' Q'. \<turnstile> P' c Q' \<and> s \<in> P' \<and> Q' \<subseteq> Q 
           \<Longrightarrow> \<turnstile> P c Q"


  
lemma prob_assert_dest:"s \<in> P \<smile> 1 \<Longrightarrow> get_prob s = 1 \<and> (\<exists>s'. (s',snd s) \<in> P)"
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
       q \<in> nat_vars  \<Longrightarrow> q \<in> variables \<Longrightarrow> length (v \<sigma>) > 1 \<Longrightarrow>
     v \<sigma> = v (set_value \<sigma> q (from_nat q')) \<Longrightarrow>
      (1, set_value \<sigma> q (from_nat q'),
         QStateM ((\<lambda>i. {})(q' := q'_addr), QState (q'_addr, v \<sigma>)))
           \<in> (q\<cdot>f \<mapsto>\<^sub>v v) \<smile> 1"
  unfolding prob_assert_def map_assnv_def Let_def get_qstate_def get_stack_def 
            Q_domain_var_def set_value_def var_set_def
  apply auto
  apply (simp add: get_set rep_nat)
  apply (metis (no_types, lifting) QState.rep_eq QStateM_rel1 QState_vars.rep_eq equals0D fst_conv)
          apply (metis One_nat_def QState.rep_eq QStateM_rel1 QState_vars.rep_eq card_0_eq fst_conv n_not_Suc_n nat_power_eq_Suc_0_iff numeral_2_eq_2 snd_conv)
  apply (metis One_nat_def QStateM_rel2 QStateM_wf_qstate QState_list_idem card_0_eq equals0D fst_conv n_not_Suc_n nat_power_eq_Suc_0_iff numeral_2_eq_2 snd_conv)
  apply (simp add: get_set rep_nat)
  by (simp add: get_set rep_nat)


lemma alloc_sound:
  assumes (* a0: "st =(\<lambda>s. get_stack s) " and *) a1:"not_access_v v q" and 
          a2':"not_access_v (\<SS> R) q" and 
          a3:"q \<in> variables" and  a4:"q \<in> nat_vars" and a5:"\<forall>\<sigma>. length (v \<sigma>) > 1"
  shows "\<Turnstile> R q:=alloc v (( (q\<cdot>f \<mapsto>\<^sub>v v)) \<smile> 1 \<and>\<^sup>* R)"  
proof-
  { fix s s'
    let ?st = "(\<lambda>s. get_stack s) "
     assume a00:"\<turnstile> \<langle>q:=alloc v,s\<rangle> \<Rightarrow> s'" and
            a01:"s \<in> Normal ` R"       
     then obtain sn where a01:"s = Normal sn" and         
         a01a:"sn \<in> R"  using a00 a01
       by auto               
     then obtain q' \<Q> q'_addr \<sigma> \<delta> where 
      sn: "sn = (\<delta>, \<sigma>, \<Q>)" and 
      s':"s' = Normal (\<delta>, set_value \<sigma> q (from_nat q'),
                         \<Q> + QStateM ((\<lambda>i. {})(q' := q'_addr), QState (q'_addr, v \<sigma>)))" and
      q':"q' \<notin> dom_q_vars (QStateM_map \<Q>)" and
      q'_addr_in_new: "q'_addr \<in> new_q_addr v \<sigma> (QStateM_map \<Q>)"         
       by (auto intro: QExec_Normal_elim_cases(9)[OF a00[simplified a01]])    
    then obtain sn' where 
       sn':"s' = Normal sn' \<and> 
        sn' = (\<delta>, set_value \<sigma> q (from_nat q'), \<Q> + QStateM ((\<lambda>i. {})(q' := q'_addr), QState (q'_addr, v \<sigma>)))" 
       by auto              
     let ?\<Q> = "\<Q> + QStateM ((\<lambda>i. {})(q' := q'_addr), QState (q'_addr, v \<sigma>))" 
     have h1:"length (v \<sigma>) > 1" using a5
       by blast
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
     have new_state_in_assr:"(1, ?\<sigma>', ?\<Q>') \<in> (q\<cdot>f \<mapsto>\<^sub>v v) \<smile> 1"
       using map_assnv_prob[OF _ _ _ ]    v_eq a4 a3  h1
(*          allocate_wf1[of ?\<Q>', OF _  _ _ q'_addr_in_new , of  "(\<lambda>i. {})(q' := q'_addr)" v q' ?\<sigma>' set_value q, simplified] *)
       allocate_wf1[of ?\<Q>', OF _ _  _ _ q'_addr_in_new, of "{}\<^sub>q(q' := q'_addr)" q' ?\<sigma>', simplified]

       by fastforce
     have "sn' \<in> ((q\<cdot>f \<mapsto>\<^sub>v v) \<smile> 1 \<and>\<^sup>* R)"       
     proof-    
       let ?A = "(q\<cdot>f \<mapsto>\<^sub>v v) \<smile> 1" and ?B = R
       let ?A' = "eq_stack_S ?A (eq_stack ?A ?B)"
       let ?B' = "eq_stack_S ?B (eq_stack ?A ?B)"       
       have "get_prob sn' \<in> (comb_set (*) (prob\<^sub>s  ?A') (prob\<^sub>s  ?B'))"
         using prob_assert_dest comb_set_prob\<^sub>s_intro[OF new_state_in_assr sn_mod_\<sigma>'_in_R] sn'              
         unfolding get_prob_def by auto
       moreover have "get_stack sn' \<in> eq_stack ?A ?B"
         using stack_set_intro[OF new_state_in_assr sn_mod_\<sigma>'_in_R]
         by (simp add: st')
       moreover have h:"QStateM ((\<lambda>i. {})(q' := q'_addr), QState (q'_addr, v \<sigma>)) ## \<Q>"
         using disjoint_allocate[of ?\<Q>', OF _ q' _ _ q'_addr_in_new, of "{}\<^sub>q(q' := q'_addr)" ?\<sigma>' set_value, simplified]         
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
    then have "s' \<in> Normal ` ((q\<cdot>f \<mapsto>\<^sub>v v) \<smile> 1 \<and>\<^sup>* R)" using sn' by auto  
   } thus ?thesis unfolding valid_def by auto
 qed

lemma dispose_sound:
  assumes a0:"q \<in> variables" and  a1:"q \<in> nat_vars \<or> q \<in> nat_list_vars" and
    a4:"n = (\<lambda>s. vec_norm (vec_of_list (v s)))" 
  shows "\<Turnstile> ((q\<cdot>i \<mapsto>\<^sub>v v) \<and>\<^sup>* R) (Dispose q i) (( |>a\<^sub>n) \<and>\<^sup>* R)" 
proof-
  { fix s s'
    let ?st = "(\<lambda>s. get_stack s) "
    assume a00:"\<turnstile> \<langle>Dispose q i,s\<rangle> \<Rightarrow> s'" and
            a01:"s \<in> Normal ` ((q\<cdot>i \<mapsto>\<^sub>v v) \<and>\<^sup>* R)" and
            a02:"s' \<noteq> Fault"
     then obtain sn where a01:"s = Normal sn" and         
         a01a:"sn \<in>  ((q\<cdot>i \<mapsto>\<^sub>v v) \<and>\<^sup>* R)"        
       by auto 
     then obtain \<rho>1 \<rho>2 Q1 Q2 where 
       "(\<rho>1, get_stack sn, Q1) \<in> (q\<cdot>i \<mapsto>\<^sub>v v)" and
       "(\<rho>2, get_stack sn, Q2) \<in> R" and "get_prob sn = \<rho>1 * \<rho>2 " and 
       "get_QStateM sn =  Q1 + Q2"
       using Q_sep_dis_set_dest unfolding get_prob_def get_QStateM_def get_stack_def
       using prod.exhaust_sel by metis       
     have "\<exists> \<Q>' \<Q>'' \<sigma> \<delta> . sn = (\<delta>, \<sigma>, \<Q>' + \<Q>'') \<and>
          s' = Normal (\<delta>, \<sigma>, QStateM (QStateM_map \<Q>', vec_norm (QStateM_vector \<Q>'') \<cdot>\<^sub>q qstate \<Q>')) \<and>
          \<Q>' ## \<Q>'' \<and>  Q_domain_var (var_set q i \<sigma>) (QStateM_map \<Q>'') \<noteq> {} \<and>
          Q_domain (QStateM_map \<Q>'') = Q_domain_var (var_set q i \<sigma>) (QStateM_map \<Q>'')"      
       apply (rule  QExec_Normal_elim_cases(10)[OF a00[simplified a01]])
       using a02 by fast+    
     then obtain \<Q>' \<Q>'' \<sigma> \<delta>  where
      f1:"sn = (\<delta>, \<sigma>, \<Q>' + \<Q>'')" and
      f2:"s' = Normal (\<delta>, \<sigma>, QStateM (QStateM_map \<Q>', vec_norm (QStateM_vector \<Q>'') \<cdot>\<^sub>q qstate \<Q>'))" and
      f3:"\<Q>' ## \<Q>''" and f4:"Q_domain_var (var_set q i \<sigma>) (QStateM_map \<Q>'') \<noteq> {}" and
      f5:"Q_domain (QStateM_map \<Q>'') = Q_domain_var (var_set q i \<sigma>) (QStateM_map \<Q>'')"       
       by fast
     have "(\<rho>1, get_stack sn, QStateM ({}\<^sub>q, (n \<sigma>) \<cdot>\<^sub>q |>)) \<in> ( |>a\<^sub>n)" sorry
     moreover have "(\<rho>1, get_stack sn, \<Q>') \<in> R" sorry
     moreover have "QStateM ({}\<^sub>q, (n \<sigma>) \<cdot>\<^sub>q |>) ## \<Q>'" sorry
     moreover have "QStateM (QStateM_map \<Q>', vec_norm (QStateM_vector \<Q>'') \<cdot>\<^sub>q qstate \<Q>') = 
                      QStateM ({}\<^sub>q, (n \<sigma>) \<cdot>\<^sub>q |>) + \<Q>'" sorry
    
     ultimately have "(\<delta>, \<sigma>, QStateM (QStateM_map \<Q>', vec_norm (QStateM_vector \<Q>'') \<cdot>\<^sub>q qstate \<Q>')) \<in> (( |>a\<^sub>n) \<and>\<^sup>* R)"
       using Q_sep_dis_set_intro unfolding get_stack_def
       sorry
     then have "s' \<in> Normal ` (( |>a\<^sub>n) \<and>\<^sup>* R)" using f2 by auto
   }
   thus ?thesis  unfolding valid_def by auto
qed

(* lemma dispose_sound1:
  assumes a0:"qv = (\<lambda>s. fst (get_qstate s))" and a1:"st = get_stack" and
    a2:"not_access_v n q" and
    a3:"n = (\<lambda>s. vec_norm (vec_of_list (v1 s)))" and
    a4:"P =
    (\<llangle>q\<rrangle> 1\<mapsto>\<^sub>l v1) \<inter> (q1 1\<mapsto>\<^sub>l v2) \<inter> (\<llangle>q\<rrangle> \<inter>\<^sub>{\<^sub>} q1) \<inter>
    {s. set_qstate s ((QStateM_expr ((QState_expr q1 v2) +\<^sub>e |>\<^sub>n)) s) \<in> Q}"
  shows "\<Turnstile>P Dispose q {s. get_QStateM s = ((QStateM_expr ((QState_expr q1 v2) +\<^sub>e |>\<^sub>n)) s)}"
  sorry *)


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
  case (QMod q_v q_s st qs M Q) 
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
  case (QDispose q n v i R)
  then show ?case using dispose_sound by auto
next
  case (QMeasure qv st Qs \<rho> q \<Psi> qr \<Phi> v A)
  then show ?case sorry
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



end
end
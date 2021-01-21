theory Quantum_Separation_LogicDef
  imports QSemanticsBig Sep_Prod_Instance
begin

type_synonym ('s,'p) triplet = "('s state) assn \<times> 'p \<times> ('s state) assn"

context vars
begin

definition Q_sep_dis::"(('s state) \<Rightarrow> bool) \<Rightarrow> (('s state) \<Rightarrow> bool) \<Rightarrow>  (('s state) \<Rightarrow> bool)" 
(infixr "\<and>*\<^sub>q" 35)
where "Q_sep_dis A B \<equiv> (\<lambda>s. fst s \<in> (fst ` {s. A s \<and> B s}) \<and>  
                            (fst (snd s) \<in> (fst ` (snd ` {s. A s \<and> B s}))) \<and>
                            ((\<lambda>s. s \<in> (snd ` (snd ` {s. A s}))) \<and>* 
                             (\<lambda>s. s \<in> (snd ` (snd ` {s. B s})))) (snd (snd s)))"

definition Q_sep_dis_set::"(('s state) set) \<Rightarrow> (('s state) set) \<Rightarrow>  (('s state) set)" 
(infixr "\<and>\<^sup>*" 35)
where "Q_sep_dis_set A B \<equiv> let eq_stack = (fst ` (snd ` A)) \<inter> (fst ` (snd ` B));
                               eq_stack_S = (\<lambda>S. {s. s \<in> S \<and> fst (snd s) \<in> eq_stack})  in
                            {s. \<forall>s1 s2. s1 \<in> eq_stack_S A \<and> s2 \<in> eq_stack_S B \<and> 
                                   fst (snd s1) = fst (snd s2) \<longrightarrow> 
                                fst s = fst s1 * fst s2 \<and> fst (snd s) = fst (snd s1) \<and>
                               ((\<lambda>s. s \<in> (snd ` (snd ` {s. s = s1}))) \<and>* 
                               (\<lambda>s. s \<in> (snd ` (snd ` {s. s = s2})))) (snd (snd s))}"

definition map_assn'::"'s expr_q \<Rightarrow> 's expr_q \<Rightarrow> ('s state, (complex) QState) expr \<Rightarrow> (('s state) set)"  
 ("_\<cdot>_ \<mapsto> _"  [1000, 20, 1000] 60)
  where "map_assn' q1 q2 v \<equiv> let qv = (\<lambda>s. fst (get_qstate s)); 
                            qs = (\<lambda>s. snd (get_qstate s));
                            st = (\<lambda>s. get_stack s) in   
                 {s. fst s = 1 \<and>(q1 (st s, qv s) \<union> q2 (st s, qv s)) \<noteq> {} \<and> 
                      (\<exists>\<qq>' \<qq>''. (qs s) = (v s) \<and> (v s) = \<qq>' +  \<qq>'' \<and> \<qq>' ## \<qq>'' \<and> 
                                (q1 (st s, qv s)) = QState_vars \<qq>' \<and>
                                (q1 (st s, qv s)) = QState_vars \<qq>')}"


definition map_assn::"'s expr_q \<Rightarrow> ('s state, (complex) QState) expr \<Rightarrow> (('s state) set)"  (infixr "\<mapsto>\<^sub>q" 35)
  where "map_assn f v \<equiv> let qv = (\<lambda>s. fst (get_qstate s)); 
                            qs = (\<lambda>s. snd (get_qstate s));
                            st = (\<lambda>s. get_stack s) in   
                 {s. (f (st s, qv s)) \<noteq> {} \<and> (\<exists>\<qq>' \<qq>''. (qs s) = (v s) \<and> (v s) = \<qq>' +  \<qq>'' \<and> \<qq>' ## \<qq>'' \<and> (f (st s, qv s)) = QState_vars \<qq>')}"

definition map_assnl::"('s,nat) expr \<Rightarrow> ('s state, (complex) QState) expr \<Rightarrow> (('s state) set)"  (infixr "\<mapsto>\<^sub>l" 35)
  where "map_assnl f v \<equiv> let qv = (\<lambda>s. fst (get_qstate s)); 
                            qs = (\<lambda>s. snd (get_qstate s));
                            st = (\<lambda>s. get_stack s) in   
                 {s. (qv s) (f (st s)) \<noteq> {} \<and> (\<exists>\<qq>'. (qs s) =  \<qq>' +  (v s) \<and> \<qq>' ## (v s) \<and> (qv s) (f (st s)) = QState_vars (v s))}"

definition aij::"'s expr_q \<Rightarrow> ('s state, (complex) QState) expr \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>'s state \<Rightarrow>  complex"
  where "aij v f i j\<equiv>  let qv = (\<lambda>s. fst (get_qstate s)); 
                            st = (\<lambda>s. get_stack s) in 
                 (\<lambda>s. vector_element_12 (f s) (v (st s, qv s)) (i,j))"

definition v_f::"'s expr_q \<Rightarrow>( nat \<Rightarrow>'s state \<Rightarrow>  complex) \<Rightarrow> ('s state, (complex) QState) expr"
  where "v_f q f \<equiv> let qv = (\<lambda>s. fst (get_qstate s)); 
                            st = (\<lambda>s. get_stack s) in 
                     (\<lambda>s. QState(q (st s, qv s), map (\<lambda>e. f e s) [0..<2^card (q (st s, qv s))]))"

definition valid::"[('s state) assn,('v, 's) com,('s state) assn] \<Rightarrow> bool"
    ("\<Turnstile>_ _ _"  [1000, 20, 1000] 60)
    where "\<Turnstile> P c Q \<equiv> \<forall>\<sigma> \<sigma>'. \<turnstile> \<langle>c,\<sigma>\<rangle> \<Rightarrow> \<sigma>' \<longrightarrow> \<sigma> \<in> Normal ` P \<longrightarrow> \<sigma>' \<noteq> Fault \<longrightarrow>
                            \<sigma>' \<in> Normal ` Q"


inductive "hoarep"::"[('s state) assn,('v,'s) com, ('s state) assn] => bool"
    ("\<turnstile>(_/ (_)/ _)" [1000,20,1000]60)
where
  Skip: "\<turnstile> Q Skip Q"

| SMod: "\<turnstile>{s.  set_stack s (f (get_stack s)) \<in> Q} (SMod f) Q"
         
| QMod: " \<turnstile> {s. q_v = fst (get_qstate s) \<and> q_s = snd (get_qstate s) \<and> st = get_stack s \<and>
                (qs (st,q_v)) \<subseteq> QState_vars q_s \<and>
                set_qstate s (matrix_sep (qs (st,q_v)) (get_qstate s) M) \<in> Q} (QMod M qs) 
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

|QAlloc:"qv = (\<lambda>s. fst (get_qstate s)) \<and> st =(\<lambda>s. get_stack s) \<Longrightarrow> 
         (qa \<mapsto>\<^sub>l Qs) \<subseteq> Q \<Longrightarrow> not_access_locals v \<Longrightarrow>
          \<turnstile> {s. ((qv s)(qa (st s)) = {}) \<and> 
                   length (v (st s)) = (e (st s)) \<and> 
                   QState_list (Qs s) = (v (st s)) \<and> 
                 (set_stack s (set_value (st s) q (from_nat (qa (st s)))))\<in>Q}
              (Alloc q e v) Q"


| QDispose: "qv = (\<lambda>s. fst (get_qstate s)) \<and> st =(\<lambda>s. get_stack s) \<Longrightarrow> 
              \<exists>Q n. P = ((q \<mapsto>\<^sub>l Qs) \<inter> {s. n = vec_norm (QState_vector (Qs s)) } \<inter> 
                    {s. set_qstate s ((qv s) ((q (st s)):={}),\<qq>' + n \<cdot>\<^sub>q |>) \<in>Q}) \<Longrightarrow> 
              \<turnstile> P (Dispose q) Q"

(* | QMeasure1: " \<turnstile> {s.  \<exists>k. pr = get_prob s \<and> qv = fst (get_qstate s) \<and> qs = snd (get_qstate s) \<and> st = get_stack s \<and> 
                 q (st, qv) \<subseteq> (QState_vars qs) \<and> 
                 (\<delta>k, q') = measure_vars k (q (st, qv)) (qv,qs) \<and> 
                 st' = set_value st v (from_nat (pr * \<delta>k)) \<and>               
                set_prob (set_stack (set_qstate s q') st') (pr * \<delta>k) \<in> Q} 
               (Measure v q) Q"  *)

| QMeasure: "qv = (\<lambda>s. fst (get_qstate s)) \<and> st = (\<lambda>s. get_stack s)  \<Longrightarrow>
             \<rho> = (\<lambda>i s. (\<Sum>j\<in> (QState_vars (Qs s) - (q (st s, qv s))). norm (aij q Qs i j s )^2) / 
                        (\<Sum>i\<in>q (st s, qv s). \<Sum>j\<in> (QState_vars (Qs s) - (q (st s, qv s))). norm (aij q Qs i j s )^2 )) \<Longrightarrow>               
             \<Psi> = (\<lambda>i. ((q \<cdot> (\<lambda>s. {}) \<mapsto>  (\<lambda>s. QState (q (st s, qv s), unit_vecl (2^card (q (st s, qv s))) i))) \<and>\<^sup>* 
                        (qr \<cdot> (\<lambda>s. {}) \<mapsto> (v_f qr (\<lambda>j s. (aij q Qs i j s) / sqrt (\<rho> i s)) )))) \<Longrightarrow>
               \<turnstile> ((q \<cdot> qr \<mapsto> Qs) \<inter> ({s. \<exists>i\<in>q (st s, qv s). \<Phi> (set_stack s (set_value (st s) v (from_nat i)))}))
               (Measure v q) ((\<Union>i\<in>A. \<Psi> i) \<inter> {s. \<Phi> s})"

| Frame: "\<turnstile> P c Q \<Longrightarrow>  {v. access_v  (\<lambda>s. (p, (s,q)) \<in> A) v = True} \<inter> 
                       modify_locals c = {} \<Longrightarrow> \<turnstile> (P \<and>\<^sup>* A) c (Q \<and>\<^sup>* A)"

| Conseq: "\<forall>s \<in> P. \<exists>P' Q'. \<turnstile> P' c Q' \<and> s \<in> P' \<and> Q' \<subseteq> Q 
           \<Longrightarrow> \<turnstile> P c Q"





end
end
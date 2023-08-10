(* Title:     Quantum-Semantics/vars.thy
   Author:    David Sanan, Nanyang Technological University 
   Copyright   2020
   License:     BSD
*)


theory vars
  imports HOL.Complex
begin

subsection \<open>Syntax\<close>

text \<open>Datatype for quantum programs\<close>

class nat_abs=
  fixes from_nat ::"nat \<Rightarrow> 'a"
  fixes to_nat ::"'a \<Rightarrow> nat"
  fixes subset_nat :: "'a set"

  assumes nat_bij:"bij_betw to_nat subset_nat UNIV"
  assumes abs_nat:"a \<in> subset_nat \<Longrightarrow> from_nat (to_nat a) = a "
  assumes rep_nat:"to_nat (from_nat b) = b"

class nat_list_abs= nat_abs +
  fixes from_nat_list ::"nat list \<Rightarrow> 'a"
  fixes to_nat_list ::"'a \<Rightarrow> nat list"
  fixes subset_nat_list :: "'a set"

  assumes nat_list_bij:"bij_betw to_nat_list subset_nat_list UNIV"
  assumes abs_nat_list:"a \<in> subset_nat_list \<Longrightarrow> from_nat_list (to_nat_list a) = a "
  assumes rep_nat_list:"to_nat_list (from_nat_list b) = b" 

class real_abs= nat_list_abs+
  fixes from_real ::"real \<Rightarrow> 'a"
  fixes to_real ::"'a \<Rightarrow> real"
  fixes subset_real :: "'a set"

  assumes real_bij:"bij_betw to_real subset_real UNIV"
  assumes "a \<in> subset_real \<Longrightarrow> from_real (to_real a) = a "
  assumes "to_real (from_real b) = b"


locale vars =  
  fixes types::"'t set"
  fixes v_domain :: "'v \<Rightarrow> ('m::real_abs) set"
  fixes get_value :: "'s \<Rightarrow> 'v  \<Rightarrow> 'm"
  (* fixes set_value ::"'s \<Rightarrow> 'v \<Rightarrow> 'b \<Rightarrow> 's"  *)
  fixes conv::"('v \<Rightarrow> 'm) \<Rightarrow>  's"  
\<comment>\<open> I can add a function from 'v to a string noting the type of 'v and a set of possible 
    values, the assumes must specify that the range is in a set of types\<close>
  fixes var_types::"'v \<Rightarrow> nat"
  fixes nat_vars::"'v set"
  fixes nat_list_vars::"'v set" 

  assumes finite_vars:"finite {v::'v. True}"
  assumes domain_nat:"v \<in> nat_vars \<Longrightarrow> v_domain v = subset_nat"
  assumes domain_nat_list:"v \<in> nat_list_vars \<Longrightarrow> v_domain v = subset_nat_list"     
  assumes "(get_value s v) \<in> v_domain v"
(*  assumes eq_get_set:"v \<in> variables \<Longrightarrow> x \<in> (v_domain v) \<Longrightarrow> get_value (set_value s v x) v = x" *)
  assumes abs_elem: "s = conv (get_value s)"
 
  assumes get_set:"get_value (conv (m(v := val))) v = val"
  assumes get_set_id:"\<forall>v'. v\<noteq>v' \<longrightarrow> get_value (conv (m(v := val))) v' = m v'"
  assumes int_domains:"nat_vars \<inter> nat_list_vars = {}"
  (* assumes get_value: "v\<in>variables \<Longrightarrow> 
                       (get_value (m (v:= x))) = x" *)
(*  assumes set_value_eq:"set_value s v val = conv (get_value (set_value s v val)) variables" *)
 (* for dynamic types *)
  assumes type_vars:"var_types v = 0 \<or> var_types v = 1"
  assumes domain_nat1:"var_types v = 0 \<Longrightarrow> v_domain v = subset_nat"
  assumes domain_nat_list1:"var_types v = 1 \<Longrightarrow> v_domain v = subset_nat_list"

  
begin

definition set_value:: "'s \<Rightarrow> 'v \<Rightarrow> 'm \<Rightarrow> 's"
  where "set_value s v val = conv ((get_value s)(v:=val))"

lemma set_value_id:"get_value (set_value s v val) v = val"
  unfolding set_value_def using get_set by auto

    
lemma set_value_id_v':"\<forall>v. v\<noteq>q \<longrightarrow> get_value (set_value \<sigma> q val) v = get_value \<sigma> v"
  unfolding set_value_def apply auto
  by (simp add: get_set_id) 

lemma con_elem: "get_value (conv m) = m"
proof -
  have "\<forall>f v. get_value (conv f) v = f v"
    by (metis (full_types) fun_upd_triv get_set)
  then show ?thesis
    by blast
qed

lemma v_only_one_domain:"v \<in> nat_vars \<and> v \<in> nat_list_vars \<Longrightarrow> False"
  using int_domains by auto

definition not_access_v::"('s \<Rightarrow> 'n) \<Rightarrow> 'v \<Rightarrow> bool"
where "not_access_v f v \<equiv>     
  \<forall>s f1 f2. f1 \<in> v_domain v \<and> f2 \<in> v_domain v \<longrightarrow>
    f (set_value s v f1) = 
    f (set_value s v f2)" 

definition not_access_v_set::"('s \<Rightarrow> 'n) \<Rightarrow> 'v set \<Rightarrow> bool"
where "not_access_v_set f V \<equiv>  \<forall>v. v \<in> V \<longrightarrow> not_access_v f v" 

definition access_v::"('s \<Rightarrow> 'n) \<Rightarrow> 'v \<Rightarrow> bool"
where "access_v f v \<equiv>     
  \<exists>s f1 f2. f1 \<in> v_domain v \<and> f2 \<in> v_domain v \<and>
    f (set_value s v f1) \<noteq> 
    f (set_value s v f2)"

definition not_access_locals::"('s \<Rightarrow> 'n) \<Rightarrow> bool"
where "not_access_locals f \<equiv> \<forall>v\<in>{x::'v. True}. not_access_v f v"

lemma access_neg:"access_v f v = (\<not> (not_access_v f v))"
  unfolding access_v_def not_access_v_def set_value_def by auto

definition modify_v:: "('s \<Rightarrow> 's) \<Rightarrow> 'v \<Rightarrow> bool"
  where "modify_v f v \<equiv> \<exists>s. get_value (f s) v \<noteq> get_value s v"
                               
definition not_modify_v::"('s \<Rightarrow> 's) \<Rightarrow> 'v \<Rightarrow> bool"
  where "not_modify_v f v \<equiv> \<forall>s. get_value (f s) v = get_value s v"

lemma modify_neg:"modify_v f v =  ( \<not> (not_modify_v f v))" 
  unfolding modify_v_def not_modify_v_def by auto

lemma modify_v_conv:"modify_v f v \<Longrightarrow> \<exists>\<sigma> \<sigma>' val. \<sigma>' = conv ((get_value \<sigma>)(v:=val))"
  unfolding modify_v_def
  by auto

lemma modify_v_set_value:"modify_v f v \<Longrightarrow> \<exists>\<sigma> \<sigma>' val. \<sigma>' = set_value \<sigma> v val"
  unfolding modify_v_def set_value_def
  by auto


lemma set_value_modify_v':"\<sigma>' = set_value \<sigma> v val \<and> \<sigma> \<noteq> \<sigma>'  \<Longrightarrow> \<exists>f. modify_v f v"
  unfolding modify_v_def set_value_def
  by (metis (full_types) abs_elem fun_upd_same fun_upd_triv get_set)

lemma set_value_modify_v:"\<sigma>' = set_value \<sigma> v val \<and> \<sigma> \<noteq> \<sigma>'  \<Longrightarrow>  modify_v (\<lambda>\<sigma>. set_value \<sigma> v val) v"
  unfolding modify_v_def set_value_def
  by (metis (full_types) abs_elem fun_upd_triv get_set)

lemma empty_set_modified_eq_f:"{} = {a. modify_v f a} \<Longrightarrow> \<sigma> = f \<sigma>" 
  unfolding modify_v_def apply auto
  by (metis abs_elem ext)

lemma
  f_updates_only_x_with_x:
  assumes a0:"\<forall>y. x\<noteq>y \<longrightarrow> get_value (f \<sigma>) y = get_value \<sigma> y"
  shows "set_value \<sigma> x (get_value (f \<sigma>) x) = f \<sigma>"
proof -
  fix y
  have f1: "\<forall>m f v. (f(v::'v := m::'m)) v = m"
    by auto
  have f2: "\<forall>v va f m. (va::'v) = v \<or> (f(v := m::'m)) va = f va"
    by (meson fun_upd_other)
  have "y = x \<longrightarrow> (\<exists>s. get_value s = (get_value \<sigma>)(x := get_value (f \<sigma>) x) \<and> s = f \<sigma>)"
    using f1 assms by auto
  moreover
  { assume "y \<noteq> x"
    then have "get_value (f \<sigma>) y = get_value \<sigma> y \<and> y \<noteq> x"
      using assms by presburger
    then have "\<exists>s. get_value s = (get_value \<sigma>)(x := get_value (f \<sigma>) x) \<and> s = f \<sigma>"
      using f2 assms by auto}
  ultimately show ?thesis
    by (metis abs_elem set_value_def)
qed


lemma not_access_v_f_q_eq_set:
      "\<sigma>' = set_value \<sigma> q v \<Longrightarrow> 
       not_access_v A q \<Longrightarrow> A \<sigma> = A \<sigma>'"
  unfolding not_access_v_def set_value_def 
  using fun_upd_triv vars_axioms unfolding vars_def
  by metis

lemma not_access_v_f_modifie_v_q_eq_set:
      "modify_v (\<lambda>\<sigma>. set_value \<sigma> q v) q \<Longrightarrow> 
       not_access_v A q \<Longrightarrow> A \<sigma> = A (set_value \<sigma> q v)"
  unfolding not_access_v_def set_value_def
  using fun_upd_triv vars_axioms unfolding vars_def
  by metis
 

lemma not_access_v_set_f_q_eq_set:
   "not_access_v_set A Q  \<Longrightarrow> 
    \<forall>\<sigma>' \<sigma> q v. q \<in>Q \<and> \<sigma>' = set_value \<sigma> q v \<longrightarrow> A \<sigma> = A \<sigma>'"
  by (meson not_access_v_f_q_eq_set not_access_v_set_def subsetD)

lemma not_access_v_set_included:
"not_access_v_set f Q  \<Longrightarrow> Q1\<subseteq>Q \<Longrightarrow> not_access_v_set f Q1"
  by (simp add: not_access_v_set_def subsetD)

lemma from_nat_in_vdomain:
  assumes a1:"q \<in> nat_vars"
  shows "from_nat q' \<in> v_domain q"
proof- 
  have "v_domain q = subset_nat" using domain_nat[OF a1]
    by auto
  thus ?thesis using nat_bij abs_nat 
    by (metis UNIV_I bij_betw_def imageE)
qed

lemma from_nat_list_in_vdomain:
  assumes  a1:"q \<in> nat_list_vars"
  shows "from_nat_list q' \<in> v_domain q"
proof- 
  have "v_domain q = subset_nat_list" using domain_nat_list[OF  a1]
    by auto
  thus ?thesis using nat_list_bij abs_nat_list
    by (metis UNIV_I bij_betw_def imageE)
qed


definition set_values::"'s \<Rightarrow> ('v\<times>'m) list  \<Rightarrow> 's"
  where "set_values s vs \<equiv>
   let vars = map fst vs in 
   if (distinct vars) then
      conv (foldr (\<lambda>v f. f(fst v := snd v)) vs (get_value s))
   else s"

definition set_values_alt::"'s \<Rightarrow> ('v\<times>'m) list  \<Rightarrow> 's"
  where "set_values_alt s vs \<equiv>
   let vars = map fst vs in 
   if (distinct vars) then
      foldr (\<lambda>v \<sigma>. set_value \<sigma> (fst v) (snd v)) vs s
   else s"

lemma not_var_i_before_i: 
  assumes a0:"distinct (map fst vs)" and a2:"i < length vs"  
  shows "\<forall>j<i. fst (vs!j) \<noteq> fst (vs!i)"
  using a0 a2 nth_eq_iff_index_eq by fastforce 

lemma not_var_i_after_i: 
  assumes a0:"distinct (map fst vs)" and a2:"i < length vs"  
  shows "\<forall>j>i. j < length vs \<longrightarrow> fst (vs!j) \<noteq> fst (vs!i)"
  using a0 a2 
  by (metis not_var_i_before_i) 

lemma ls_not_v_eq_val:
  assumes a0:"ls\<noteq>[]" and a1:"\<forall>i<length ls. fst(ls!i) \<noteq> v"
  shows "(foldr (\<lambda>v f. f(fst v := snd v)) ls s) v = s v"
  using a0 a1
proof(induct ls rule:list_nonempty_induct)
  case (single x)
  then show ?case
    by simp 
next
  case (cons x xs)
  then have "foldr (\<lambda>v f. f(fst v := snd v)) xs s v = s v"
    by (metis (no_types, lifting) dual_order.strict_iff_not le_simps(2) length_Cons linorder_neqE_nat nth_Cons_Suc) 
  then show ?case
    by (metis (no_types, lifting) cons.prems foldr.simps(2) fun_upd_other length_greater_0_conv list.discI nth_Cons_0 o_apply) 
qed

lemma set_values_less_i:
  assumes a0:"distinct (map fst vs)" and a1:"i < length vs" 
  shows "foldr (\<lambda>v f. f(fst v := snd v)) (take i vs) s (fst (vs!i)) = s (fst (vs!i))"
  using a0 a1
proof(cases "i=0")
  case True
  then show ?thesis by auto
next
  case False
  then have "take i vs \<noteq> []" using a1 by auto
  moreover have "\<forall>j<length (take i vs).  fst((take i vs)!j) \<noteq> fst (vs!i)"
    by (simp add: a0 a1 not_var_i_before_i)
  ultimately show ?thesis
    by (simp add: a0 a1 ls_not_v_eq_val)
qed

lemma set_values_greater_i:
  assumes a0:"distinct (map fst vs)" and a1:"i < length vs" 
  shows "foldr (\<lambda>v f. f(fst v := snd v)) (drop (i+1) vs) s (fst (vs!i)) = s (fst (vs!i))"
  using a0 a1
proof(cases "i=length vs")
  case True
  then show ?thesis by auto
next
  case False
  then have "drop i vs \<noteq> []" using a1 by auto
  moreover have "\<forall>j<length (drop (i+1) vs).  fst((drop (i+1) vs)!j) \<noteq> fst (vs!i)"
    using a0 less_diff_conv nth_eq_iff_index_eq by fastforce
  ultimately show ?thesis
    by (smt (verit) foldr.simps(1) id_apply ls_not_v_eq_val)
qed


lemma foldr_split:
  assumes a0:"i < length vs" 
        shows "foldr f vs s = foldr f (take i vs) (f (vs!i) (foldr f (drop (i+1) vs) s))"
proof-
  let ?xs = "take i vs" and ?ys = "vs!i # (drop (i+1) vs)" 
  have "vs = ?xs @ ?ys"
    by (simp add: Cons_nth_drop_Suc a0)
  moreover have "\<And>s. foldr f ?ys s = foldr f [(vs!i)] (foldr f (drop (i+1) vs) s)"
    by auto
  then have "foldr f ?ys s = foldr f [(vs!i)] (foldr f (drop (i+1) vs) s)"  by auto
  ultimately show ?thesis
    by (metis foldr.simps(1) foldr.simps(2) foldr_append o_id) 
qed

lemma reduce_get_value_conv:"conv ((get_value (conv s))(fst a := snd a)) =
             conv (s(fst a:= snd a))"
  by (simp add: con_elem)   

lemma foldr_split_assingment:
  assumes a0:"i < length vs"  
        shows "foldr (\<lambda>v f. f(fst v := snd v)) vs s = 
               foldr (\<lambda>v f. f(fst v := snd v)) (take i vs) 
                    ((foldr (\<lambda>v f. f(fst v := snd v)) (drop (i+1) vs) s)(fst(vs!i):=snd(vs!i)))"
  by (meson assms foldr_split)
  
lemma conf_fold:
   "conv (foldr (\<lambda>v f. f(fst v := snd v)) vs (get_value s)) = 
   foldr (\<lambda>v f. conv ((get_value f)(fst v := snd v))) vs s"
proof(induct vs arbitrary: s)
  case Nil
  then show ?case
    using abs_elem by fastforce 
next
  case (Cons a vs)
  then show ?case
    by (metis (no_types, lifting) con_elem foldr.simps(2) o_apply)
qed


lemma set_values_refl:
  assumes a0:"distinct (map fst vs)" and a1:"i < length vs"  
  shows "get_value (set_values s vs) (fst(vs!i)) = snd (vs!i)"

proof-
  have "foldr (\<lambda>v f. f(fst v := snd v)) vs (get_value s) = 
        foldr (\<lambda>v f. f(fst v := snd v)) (take i vs) 
           ((foldr (\<lambda>v f. f(fst v := snd v)) (drop (i+1) vs) (get_value s))(fst(vs!i):=snd(vs!i)))"
    using a1 foldr_split_assingment by blast
  then show ?thesis
    by (simp add: a0 a1 con_elem set_values_def set_values_less_i)
qed

lemma not_in_set_values:
assumes a0:"v \<notin> set (map fst vs)" and a1:"i < length vs"  
shows "get_value (set_values s vs) v = get_value s v"
  by (smt (verit) a0 a1 con_elem in_set_conv_nth length_0_conv length_map 
       ls_not_v_eq_val not_less_zero nth_map set_values_def)

lemma fold_set_value_conv:"foldr (\<lambda>v \<sigma>. set_value \<sigma> (fst v) (snd v)) vs s = 
       foldr (\<lambda>v f. conv ((get_value f)(fst v := snd v))) vs s"
  using set_value_def by auto

lemma eq_set_values:"set_values = set_values_alt"
  unfolding set_values_def set_values_alt_def 
  using fold_set_value_conv conf_fold by presburger

lemma f_modify_1_set_value':"F = {a. modify_v f a} \<Longrightarrow> F = {v} \<Longrightarrow> \<sigma>' =  f \<sigma> \<Longrightarrow> 
      f \<sigma> = set_value \<sigma> v (get_value \<sigma>' v)"
 by (metis (full_types) f_updates_only_x_with_x mem_Collect_eq modify_v_def singletonD)

lemma f_modify_1_set_value:"F = {a. modify_v f a} \<Longrightarrow> F = {v} \<Longrightarrow>
      f = (\<lambda>\<sigma>. set_value \<sigma> v (get_value (f \<sigma>) v))"
  using f_modify_1_set_value' by auto

lemma f_modify_1_set_value'':"{a. modify_v f a} = {v} \<Longrightarrow>
      f = (\<lambda>\<sigma>. set_value \<sigma> v (get_value (f \<sigma>) v))"
  using f_modify_1_set_value' by auto

lemma eq_f':assumes a0:"\<forall>x. get_value (f \<sigma>) x =  get_value (f' \<sigma>) x"
  shows "f \<sigma> = f' \<sigma>"
proof -
  have "f' \<sigma> = conv (get_value (f \<sigma>))"
    using abs_elem a0 by presburger
  then show ?thesis
    using abs_elem by presburger
qed

lemma eq_f[intro]:assumes a0:"\<forall>x \<sigma>. get_value (f \<sigma>) x =  get_value (f' \<sigma>) x"
  shows "f = f' " 
proof -
  have "\<forall>a. f' a = conv (get_value (f a))"
    using abs_elem a0 by presburger
  then show ?thesis
    using abs_elem by presburger
qed
  
lemma list_from_single_F:"F = {x} \<Longrightarrow> set l = F \<Longrightarrow> distinct l \<Longrightarrow> l = [x]"
  by (metis distinct_length_2_or_more empty_iff empty_set insert_iff list.exhaust list.simps(15))

lemma split_f:
  assumes a0:"f' =  (\<lambda>\<sigma>. conv (\<lambda>y. if x \<noteq> y then (get_value (f \<sigma>) y) else get_value \<sigma> x )) " 
  shows "f = (\<lambda>\<sigma>. set_value (f' \<sigma>) x (get_value (f \<sigma>) x))"
  apply rule
  by (smt (verit, ccfv_threshold) assms con_elem set_value_id set_value_id_v')
  
 
lemma x_not_in_f':"x \<notin> {a. modify_v (\<lambda>\<sigma>. conv (\<lambda>y. if x \<noteq> y then (get_value (f \<sigma>) y) else get_value \<sigma> x )) a}"
  by (simp add: con_elem modify_v_def)
  
lemma modify_f: 
  assumes a0:"f = (\<lambda>\<sigma>. set_value (f' \<sigma>) x (get_value (f \<sigma>) x))" and
     a1:"F = {a. modify_v f a}" and a1':"x \<in> F" and
     a2:"f' = (\<lambda>\<sigma>. conv (\<lambda>y. if x \<noteq> y then (get_value (f \<sigma>) y) else get_value \<sigma> x ))"
   shows "F - {x}  = {a. modify_v f' a}" 
proof-
  have "x\<notin>{a. modify_v f' a}" using a2
    by (simp add: con_elem modify_v_def) 
  moreover have "\<forall>\<sigma> y. y\<noteq>x \<longrightarrow> get_value (f \<sigma>) y = get_value (f' \<sigma>) y"
    by (metis a0 set_value_id_v')
  then have "\<forall>y. x \<noteq> y \<longrightarrow> modify_v f y = modify_v f' y"
    using modify_v_def by presburger
  moreover have "modify_v f x" using a1 a1' by auto
  ultimately show ?thesis using  a1 a1' by fastforce
qed


lemma f_map_f': assumes 
  a0':"xs\<noteq>[]" and
  a0:"f' =  (\<lambda>\<sigma>. conv (\<lambda>y. if x \<noteq> y then (get_value (f \<sigma>) y) else get_value \<sigma> x ))" and 
  a1:"x \<notin> set xs" 
shows"map (\<lambda>x. (x, \<lambda>\<sigma>. get_value (f' \<sigma>) x)) xs = map (\<lambda>x. (x, \<lambda>\<sigma>. get_value (f \<sigma>) x)) (xs)"
  using a0' a0 a1
proof(induct xs rule: list_nonempty_induct)
  case (single u)
  then show ?case using con_elem by auto 
next
  case (cons u xs)
  then have "map (\<lambda>x. (x, \<lambda>\<sigma>. get_value (f' \<sigma>) x)) xs = map (\<lambda>x. (x, \<lambda>\<sigma>. get_value (f \<sigma>) x)) xs" by auto
  moreover have "(u, \<lambda>\<sigma>. get_value (f' \<sigma>) u) = (u, \<lambda>\<sigma>. get_value (f \<sigma>) u)" using cons con_elem by auto
  ultimately show ?case
    by auto
qed

lemma f_map_f'': assumes 
  a0':"xs\<noteq>[]" and
  a0:"f' =  (\<lambda>\<sigma>. conv (\<lambda>y. if x \<noteq> y then (get_value (f \<sigma>) y) else get_value \<sigma> x ))" and 
  a1:"x \<notin> set xs" 
shows"map (\<lambda>x. (x, get_value (f' \<sigma>) x)) xs = map (\<lambda>x. (x, get_value (f \<sigma>) x)) xs"
  using a0' a0 a1
proof(induct xs rule: list_nonempty_induct)
  case (single u)
  then show ?case using con_elem by auto 
next
  case (cons u xs)
  then have "map (\<lambda>x. (x, get_value (f' \<sigma>) x)) xs = map (\<lambda>x. (x, get_value (f \<sigma>) x)) xs" by auto
  moreover have "(u, get_value (f' \<sigma>) u) = (u, get_value (f \<sigma>) u)" using cons con_elem by auto
  ultimately show ?case
    by auto
qed

lemma f_fold': assumes 
  a0:"f' =  (\<lambda>\<sigma>. conv (\<lambda>y. if x \<noteq> y then (get_value (f \<sigma>) y) else get_value \<sigma> x ))" and
  a1:"f' \<sigma> = foldr (\<lambda>v \<sigma>. set_value \<sigma> (fst v) (snd v)) (map (\<lambda>x. (x, get_value (f' \<sigma>) x)) xs) \<sigma>" and 
  a2:"f = (\<lambda>\<sigma>. set_value (f' \<sigma>) x (get_value (f \<sigma>) x))" and a3:"x \<notin> set xs" and a4:"xs\<noteq>[]"
shows"f \<sigma> = foldr (\<lambda>v \<sigma>. set_value \<sigma> (fst v) (snd v)) (map (\<lambda>x. (x, get_value (f \<sigma>) x)) (x # xs)) \<sigma> "
proof-
  let ?f' ="foldr (\<lambda>v \<sigma>. set_value \<sigma> (fst v) (snd v \<sigma>)) (map (\<lambda>x. (x, \<lambda>\<sigma>. get_value (f \<sigma>) x)) xs)"
  have "map (\<lambda>x. (x, get_value (f' \<sigma>) x)) xs = map (\<lambda>x. (x, get_value (f \<sigma>) x)) xs"
    using f_map_f''[OF a4 a0 a3] by auto
  then have "f' \<sigma>= foldr (\<lambda>v \<sigma>. set_value \<sigma> (fst v) (snd v)) (map (\<lambda>x. (x,  get_value (f \<sigma>) x)) xs) \<sigma>"
    using a1 by presburger
  then have "foldr (\<lambda>v \<sigma>. set_value \<sigma> (fst v) (snd v)) (map (\<lambda>x. (x, get_value (f \<sigma>) x)) (x # xs)) \<sigma> = 
             set_value (f' \<sigma>) x (get_value (f \<sigma>) x)" by auto  
  then show ?thesis using a2  by metis 
qed

lemma induct_modify_set':
  assumes a0:"l\<noteq>[]" 
  shows "set l = F \<Longrightarrow> distinct l \<Longrightarrow> F = {a. modify_v f a} \<Longrightarrow> 
         f \<sigma> = foldr (\<lambda>v \<sigma>. set_value \<sigma> (fst v) (snd v)) (map (\<lambda>x. (x,(get_value (f \<sigma>) x))) l) \<sigma>"
  using a0 
proof(induct l arbitrary: f F rule:list_nonempty_induct )
  case (single x)
  then have "f = (\<lambda>\<sigma>. set_value \<sigma> x ((get_value (f \<sigma>)) x))" 
    using f_modify_1_set_value''  by auto
  moreover have "modify_v f x"
    using single.prems(1) single.prems(3) by auto 
  then have "foldr (\<lambda>v \<sigma>. set_value \<sigma> (fst v) (snd v)) (map (\<lambda>x. (x,(get_value (f \<sigma>) x))) [x]) \<sigma>  = 
             set_value \<sigma> x ((get_value (f \<sigma>)) x)" by auto
  ultimately show ?case by metis
next
  case (cons x xs)
  let ?f' = "(\<lambda>\<sigma>. conv (\<lambda>y. if x \<noteq> y then (get_value (f \<sigma>) y) else get_value \<sigma> x ))"
  from cons have "set xs = F - {x}" and "distinct xs" 
    by auto
  moreover have f:"f = (\<lambda>\<sigma>. set_value (?f' \<sigma>) x (get_value (f \<sigma>) x))" and "x \<in> F"
    using split_f
    apply auto[1]
    using cons.prems(1) by auto 
  then have "F - {x} = {a. modify_v ?f' a} "
    by (simp add: cons.prems(3) modify_f)  
  ultimately have f':"?f' \<sigma> = foldr (\<lambda>v \<sigma>. set_value \<sigma> (fst v) (snd v)) (map (\<lambda>x. (x, get_value (?f' \<sigma>) x)) xs) \<sigma>" 
    using cons by auto
  show ?case using f_fold'[OF _ f' f _ cons(1)]
    using cons.prems(2)  by auto 
qed


lemma induct_modify_set:
  assumes a0:"finite F" and a1:"F\<noteq>{}" 
  shows "set l = F \<Longrightarrow> distinct l \<Longrightarrow> F = {a. modify_v f a} \<Longrightarrow> 
         f \<sigma> = foldr (\<lambda>v \<sigma>. set_value \<sigma> (fst v) (snd v)) (map (\<lambda>x. (x,(get_value (f \<sigma>) x))) l) \<sigma>"
  using induct_modify_set'
  using a0 a1 by fastforce

lemma f_set_values_holds_A:
  assumes a0:"vs\<noteq>[]" and a1:"\<sigma>' = foldr (\<lambda>v \<sigma>. set_value \<sigma> (fst v) (snd v)) vs \<sigma>" and
          a2:"not_access_v_set A (set (map (\<lambda>s. fst s) vs))"
        shows "A \<sigma> = A \<sigma>'"
  using a0 a1 a2 
proof(induct vs  arbitrary: \<sigma> \<sigma>' rule: list_nonempty_induct)
  case (single x)
  then show ?case
    using not_access_v_set_f_q_eq_set by fastforce 
next
  case (cons x xs)
  then show ?case
    using not_access_v_set_f_q_eq_set not_access_v_set_included by fastforce 
qed
  

lemma not_access_v_set_modify:
  assumes a0:"finite V" and a1:"V = {v. modify_v f v}" and 
          a2:"not_access_v_set A V " and a3:"\<sigma>' = f \<sigma>" 
        shows " A \<sigma> = A \<sigma>'" 
proof-
  {
    assume "V = {}"
    then have "f \<sigma> = \<sigma>"  by (metis empty_set_modified_eq_f a1)
    then have ?thesis using a3 by simp 
  }
  moreover {
    assume a00:"V \<noteq> {}"
    obtain l where "set l = V" and "l\<noteq>[]" and "distinct l"
      using assms 
      by (metis a00 empty_set finite_distinct_list)
    moreover have f:"f \<sigma> = foldr (\<lambda>v \<sigma>. set_value \<sigma> (fst v) (snd v)) (map (\<lambda>x. (x,(get_value (f \<sigma>) x))) l) \<sigma>"
      using a00 a1 a3 vars.induct_modify_set vars_axioms calculation  by fastforce 
    ultimately have ?thesis using f_set_values_holds_A 
      by (smt (verit) Nil_is_map_conv a2 a3 fst_conv in_set_conv_nth length_map not_access_v_set_def nth_map)
  } ultimately show ?thesis by auto
qed


definition in_list::"nat set \<Rightarrow> nat list \<Rightarrow> bool"
  where "in_list vs list \<equiv> \<forall>i\<in>vs. i<length list"

definition var_set::"'v \<Rightarrow> ('s \<Rightarrow> nat set) \<Rightarrow> 's \<Rightarrow> (nat set) option"
  where "var_set v f \<sigma> \<equiv> (if (v \<in> nat_vars) then Some {to_nat (get_value \<sigma> v )} 
                          else 
                             let list_state = (to_nat_list (get_value \<sigma> v )) in
                               (if (v \<in> nat_list_vars \<and> in_list (f \<sigma>) list_state) then 
                                   Some (set (nths list_state (f \<sigma>)))
                               else None))" 


end

(* locale vars_plus = vars +
  fixes from_real ::"real \<Rightarrow> 'c"
  fixes to_real ::"'c \<Rightarrow> real"
  fixes subset_real :: "'c set"

  assumes "a \<in> subset_real \<Longrightarrow> from_real (to_real a) = a "
  assumes "to_real (from_real b) = b" 

  assumes type_vars:"v \<in> variables \<Longrightarrow> var_types v = 0 \<or> var_types v = 1 \<or> var_types v = 2"
  assumes domain_real:"v\<in>variables \<Longrightarrow> var_types v = 2 \<Longrightarrow> v_domain v = subset_real "
begin
  definition real_set::"'a set"
    where "real_set \<equiv> {v. var_types v = 2}"
end
*)
end


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
  fixes variables :: "'v set"
  fixes types::"'t set"
  fixes v_domain :: "'v \<Rightarrow> ('m::nat_list_abs) set"
  fixes get_value :: "'s \<Rightarrow> 'v  \<Rightarrow> 'm"
  (* fixes set_value ::"'s \<Rightarrow> 'v \<Rightarrow> 'b \<Rightarrow> 's"  *)
  fixes conv::"('v \<Rightarrow> 'm) \<Rightarrow> 'v set \<Rightarrow> 's"  
\<comment>\<open> I can add a function from 'v to a string noting the type of 'v and a set of possible 
    values, the assumes must specify that the range is in a set of types\<close>
  fixes var_types::"'v \<Rightarrow> nat"
  fixes nat_vars::"'v set"
  fixes nat_list_vars::"'v set" 
  
  assumes domain_nat:"v \<in> variables \<Longrightarrow> v \<in> nat_vars \<Longrightarrow> v_domain v = subset_nat"
  assumes domain_nat_list:"v\<in>variables \<Longrightarrow> v \<in> nat_list_vars \<Longrightarrow> v_domain v = subset_nat_list"     
  assumes "finite variables" 
  assumes "v \<in> variables \<Longrightarrow> (get_value s v) \<in> v_domain v"
(*  assumes eq_get_set:"v \<in> variables \<Longrightarrow> x \<in> (v_domain v) \<Longrightarrow> get_value (set_value s v x) v = x" *)
  assumes abs_elem: "s = conv (get_value s) variables"
  assumes get_set:"v \<in> variables \<Longrightarrow> get_value (conv ((get_value s)(v := val)) variables) v = val"
  assumes int_domains:"nat_vars \<inter> nat_list_vars = {}"
  (* assumes get_value: "v\<in>variables \<Longrightarrow> 
                       (get_value (m (v:= x))) = x" *)
(*  assumes set_value_eq:"set_value s v val = conv (get_value (set_value s v val)) variables" *)
 (* for dynamic types *)
  assumes type_vars:"v \<in> variables \<Longrightarrow> var_types v = 0 \<or> var_types v = 1"
  assumes domain_nat1:"v \<in> variables \<Longrightarrow> var_types v = 0 \<Longrightarrow> v_domain v = subset_nat"
  assumes domain_nat_list1:"v\<in>variables \<Longrightarrow> var_types v = 1 \<Longrightarrow> v_domain v = subset_nat_list"

  
begin

definition set_value:: "'s \<Rightarrow> 'v \<Rightarrow> 'm \<Rightarrow> 's"
  where "set_value s v val = conv ((get_value s)(v:=val)) variables"

lemma v_only_one_domain:"v \<in> nat_vars \<and> v \<in> nat_list_vars \<Longrightarrow> False"
  using int_domains by auto

definition not_access_v::"('s \<Rightarrow> 'n) \<Rightarrow> 'v \<Rightarrow> bool"
where "not_access_v f v \<equiv>     
  \<forall>s f1 f2. f1 \<in> v_domain v \<and> f2 \<in> v_domain v \<longrightarrow>
    f (set_value s v f1) = 
    f (set_value s v f2)" 

definition access_v::"('s \<Rightarrow> 'n) \<Rightarrow> 'v \<Rightarrow> bool"
where "access_v f v \<equiv>     
  \<exists>s f1 f2. f1 \<in> v_domain v \<and> f2 \<in> v_domain v \<and>
    f (conv ((get_value s)(v:=f1)) variables) \<noteq> 
    f (conv ((get_value s)(v:=f2)) variables)"

definition not_access_locals::"('s \<Rightarrow> 'n) \<Rightarrow> bool"
where "not_access_locals f \<equiv> \<forall>v\<in>variables. not_access_v f v"

lemma access_neg:"access_v f v = (\<not> (not_access_v f v))"
  unfolding access_v_def not_access_v_def set_value_def by auto

definition modify_v:: "('s \<Rightarrow> 's) \<Rightarrow> 'v \<Rightarrow> bool"
  where "modify_v f v \<equiv> \<exists>s. get_value (f s) v \<noteq> get_value s v"

definition not_modify_v::"('s \<Rightarrow> 's) \<Rightarrow> 'v \<Rightarrow> bool"
  where "not_modify_v f v \<equiv> \<forall>s. get_value (f s) v = get_value s v"

lemma modify_neg:"modify_v f v =  ( \<not> (not_modify_v f v))" 
  unfolding modify_v_def not_modify_v_def by auto

lemma not_access_v_f_q_eq_set:
      "q \<in> variables  \<Longrightarrow> 
       v \<in> v_domain q \<Longrightarrow> 
       \<sigma>' = set_value \<sigma> q v \<Longrightarrow> 
       not_access_v f q \<Longrightarrow> f \<sigma> = f \<sigma>'"
  unfolding not_access_v_def set_value_def 
  using fun_upd_triv vars_axioms unfolding vars_def
  by metis

lemma from_nat_in_vdomain:
  assumes a0:"q \<in> variables" and a1:"q \<in> nat_vars"
  shows "from_nat q' \<in> v_domain q"
proof- 
  have "v_domain q = subset_nat" using domain_nat[OF a0 a1]
    by auto
  thus ?thesis using nat_bij abs_nat 
    by (metis UNIV_I bij_betw_def imageE)
qed

lemma from_nat_list_in_vdomain:
  assumes a0:"q \<in> variables" and a1:"q \<in> nat_list_vars"
  shows "from_nat_list q' \<in> v_domain q"
proof- 
  have "v_domain q = subset_nat_list" using domain_nat_list[OF a0 a1]
    by auto
  thus ?thesis using nat_list_bij abs_nat_list
    by (metis UNIV_I bij_betw_def imageE)
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


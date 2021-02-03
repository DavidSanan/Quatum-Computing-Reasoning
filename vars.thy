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

class real_abs= nat_abs+
  fixes from_real ::"real \<Rightarrow> 'a"
  fixes to_real ::"'a \<Rightarrow> real"
  fixes subset_real :: "'a set"

  assumes "a \<in> subset_real \<Longrightarrow> from_real (to_real a) = a "
  assumes "to_real (from_real b) = b"

locale vars =  
  fixes variables :: "'v set"
  fixes types::"'t set"
  fixes v_domain :: "'v \<Rightarrow> ('b::nat_abs) set"
  fixes get_value :: "'s \<Rightarrow> 'v  \<Rightarrow> 'b"
  (* fixes set_value ::"'s \<Rightarrow> 'v \<Rightarrow> 'b \<Rightarrow> 's"  *)
  fixes conv::"('v \<Rightarrow> 'b) \<Rightarrow> 'v set \<Rightarrow> 's"  
  fixes is_nat::"'v \<Rightarrow> bool"

  assumes domain_nat:"v \<in> variables \<Longrightarrow> is_nat v \<Longrightarrow> v_domain v = subset_nat"
  assumes "finite variables" 
  assumes "v \<in> variables \<Longrightarrow> (get_value s v) \<in> v_domain v"
(*  assumes eq_get_set:"v \<in> variables \<Longrightarrow> x \<in> (v_domain v) \<Longrightarrow> get_value (set_value s v x) v = x" *)
  assumes abs_elem: "s = conv (get_value s) variables"
  assumes get_set:"v \<in> variables \<Longrightarrow> get_value (conv ((get_value s)(v := val)) variables) v = val"
  (* assumes get_value: "v\<in>variables \<Longrightarrow> 
                       (get_value (m (v:= x))) = x" *)
(*  assumes set_value_eq:"set_value s v val = conv (get_value (set_value s v val)) variables" *)

  
begin

definition set_value:: "'s \<Rightarrow> 'v \<Rightarrow> 'b \<Rightarrow> 's"
  where "set_value s v val = conv ((get_value s)(v:=val)) variables"



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
  using fun_upd_triv vars_axioms vars_def
  by metis

lemma from_nat_in_vdomain:
  assumes a0:"q \<in> variables" and a1:"is_nat q"
  shows "from_nat q' \<in> v_domain q"
proof- 
  have "v_domain q = subset_nat" using domain_nat[OF a0 a1]
    by auto
  thus ?thesis using nat_bij abs_nat 
    by (metis UNIV_I bij_betw_def imageE)
qed

end




end


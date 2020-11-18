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

locale vars =  
  fixes variables :: "'v set"
  fixes domain :: "'v \<Rightarrow> 'b set"
  fixes get_value :: "'s \<Rightarrow> 'v  \<Rightarrow> 'b"
  fixes set_value ::"'s \<Rightarrow> 'v \<Rightarrow> 'b \<Rightarrow> 's"
  fixes nat_to_typ ::"nat \<Rightarrow> 'b"
  fixes typ_to_nat ::"'b \<Rightarrow> nat"
  fixes conv::"('v \<Rightarrow> 'b) \<Rightarrow> 'v set \<Rightarrow> 's"
                 
  assumes "finite variables"
  assumes "v \<in> variables \<Longrightarrow> (get_value s v) \<in> domain v"
  assumes eq_get_set:"x \<in> names \<Longrightarrow> get_value (set_value s v x) v = x"
  assumes abs_elem: "s = conv ((get_value s)) variables"

begin

definition not_access_v::"('s \<Rightarrow> 'n) \<Rightarrow> 'v \<Rightarrow> bool"
where "not_access_v f v \<equiv>     
  \<forall>s f1 f2. f1\<in>domain v \<and> f2\<in> domain v \<longrightarrow>
    f (conv ((get_value s)(v:=f1)) variables) = 
    f (conv ((get_value s)(v:=f2)) variables)" 

definition access_v::"('s \<Rightarrow> 'n) \<Rightarrow> 'v \<Rightarrow> bool"
where "access_v f v \<equiv>     
  \<exists>s f1 f2. f1\<in>domain v \<and> f2\<in> domain v \<and>
    f (conv ((get_value s)(v:=f1)) variables) \<noteq> 
    f (conv ((get_value s)(v:=f2)) variables)"

lemma access_neg:"access_v f v = (\<not> (not_access_v f v))"
  unfolding access_v_def not_access_v_def by auto

definition modify_v:: "('s \<Rightarrow> 's) \<Rightarrow> 'v \<Rightarrow> bool"
  where "modify_v f v \<equiv> \<exists>s. get_value (f s) v \<noteq> get_value s v"

definition not_modify_v::"('s \<Rightarrow> 's) \<Rightarrow> 'v \<Rightarrow> bool"
  where "not_modify_v f v \<equiv> \<forall>s. get_value (f s) v = get_value s v"

lemma modify_neg:"modify_v f v =  ( \<not> (not_modify_v f v))" 
  unfolding modify_v_def not_modify_v_def by auto

end

end


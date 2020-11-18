theory Tensor_Permutation
  imports "HOL-Library.Permutations" "Jordan_Normal_Form.Matrix" "HOL-Word.Word"
begin

definition list_permutation_functions::"'a list \<Rightarrow> (nat \<Rightarrow> nat) set"
  where "list_permutation_functions ls \<equiv> {p. p permutes {..<length ls}}"

definition list_permutations :: "'a list \<Rightarrow> 'a list set"
  where "list_permutations ls \<equiv> (\<lambda>p. permute_list p ls) ` list_permutation_functions ls"

definition permutes_lists::"'a list \<Rightarrow> 'a list \<Rightarrow> (nat \<Rightarrow> nat) set"
  where "permutes_lists ls ls' \<equiv> {p. p permutes {..<length ls} \<and> ls' = permute_list p ls}"

definition list_permutations'::"'a list \<Rightarrow> 'a list set" where
  "list_permutations' ls = {ls'. \<exists>p. p permutes {..<length ls} \<and> ls' = permute_list p ls}"

lemma eq_list_permutations_def:"list_permutations ls = list_permutations' ls"
  unfolding list_permutations_def list_permutations'_def list_permutation_functions_def
  by auto

definition vector_permutations::"'a vec \<Rightarrow> 'a vec set" where
   "vector_permutations v = vec_of_list ` (list_permutations (list_of_vec v))"

lemma diff_permutations:
    "ls'\<in> list_permutations ls \<Longrightarrow> 
     ls'' \<in> list_permutations ls \<Longrightarrow> ls'\<noteq> ls'' \<Longrightarrow> 
      (\<exists>p1 p2.  ls' = permute_list p1 ls \<and> ls'' = permute_list p2 ls \<and> p1\<noteq>p2 \<and> 
                p1 permutes {..<length ls} \<and> p2 permutes {..<length ls})"
  unfolding list_permutations_def list_permutation_functions_def
  by force

definition permute_number :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow>  nat"
  where "permute_number l p n \<equiv> nat (bl_to_bin (permute_list p (bin_to_bl l n)))"

definition vector_permutation::"nat \<Rightarrow> 'a vec \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> 'a vec"
  where "vector_permutation n v p \<equiv>                                   
    vec_of_list (permute_list (permute_number n p)  (list_of_vec v))"

definition Normal_Tensor::"'q::linorder set \<Rightarrow> 'q set \<Rightarrow> 'a vec \<Rightarrow> 'a vec"
  where "Normal_Tensor q s v \<equiv> let l' = sorted_list_of_set (s-q)@(sorted_list_of_set q);
                                p = SOME p. p \<in> permutes_lists (sorted_list_of_set s) l' in 
                             vector_permutation (length l') v p"


end
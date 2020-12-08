(* Title:     Quantum-Semantics/Tensor_permutation.thy
   Author:    David Sanan, Nanyang Technological University 
   Copyright   2020
   License:     BSD
*)


theory Tensor_Permutation
  imports "HOL-Library.Permutations" "Jordan_Normal_Form.Matrix" "HOL-Word.Word"
begin

definition list_permutation_functions::"'a list \<Rightarrow> (nat \<Rightarrow> nat) set"
  where "list_permutation_functions ls \<equiv> {p. p permutes {..<length ls}}"

definition list_permutations :: "'a list \<Rightarrow> 'a list set"
  where "list_permutations ls \<equiv> (\<lambda>p. permute_list p ls) ` list_permutation_functions ls"

definition permutes_lists::"'a list \<Rightarrow> 'a list \<Rightarrow> (nat \<Rightarrow> nat) set"
  where "permutes_lists ls ls' \<equiv> {p. p permutes {..<length ls} \<and> ls' = permute_list p ls}"

lemma not_eq_length_no_permutation:
  "length ls \<noteq> length ls' \<Longrightarrow> permutes_lists ls ls' = {}"
  unfolding permutes_lists_def by auto

lemma eq_length_there_is_perm:
  "length ls = length ls' \<Longrightarrow> set ls = set ls' \<Longrightarrow> distinct ls \<Longrightarrow> 
   permutes_lists ls ls' \<noteq> {}"
  unfolding permutes_lists_def apply auto
  by (metis card_distinct distinct_card mset_eq_permutation mset_set_set)

lemma eq_perm_function: 
  assumes    
   a1:"p1 \<in> permutes_lists ls ls'" and
   a2:"p2 \<in> permutes_lists ls ls'" and
   a4:"distinct ls" 
 shows "\<forall>n<length ls. p1 n = p2 n" 
proof-
  { fix n assume a00:"n < length ls"
    have "ls' ! n = ls ! p1 n"
      using a1 unfolding permutes_lists_def  
      apply auto
      by (metis (no_types)  a00 permute_list_nth)    
    moreover have "ls' ! n = ls ! p2 n" 
      using a2 unfolding permutes_lists_def  
      apply auto
      by (metis (no_types) a00 permute_list_nth)
    ultimately have "ls ! p1 n = ls ! p2 n" by auto 
    moreover have "p1 n < length ls"
      using a1 a00  permutes_in_image permutes_lists_def 
      by fastforce
    moreover have "p2 n < length ls"
      using a2 a00 permutes_in_image permutes_lists_def 
      by fastforce
    ultimately have "p1 n = p2 n" using a4 nth_eq_iff_index_eq by auto
  }then show ?thesis by auto
qed  

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

lemma "length (bin_to_bl l n) = l"
  using Bits_Int.len_bin_to_bl by auto

value "bl_to_bin (bin_to_bl 3 4)"

definition permute_number :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow>  nat"
  where "permute_number l p n \<equiv> nat (bl_to_bin (permute_list p (bin_to_bl l n)))"

(* lemma permute_number_0:"permute_number 0 f = (\<lambda>n. 0)"
  unfolding permute_number_def by auto *)

lemma eq_bin_to_bl:
  assumes a0:"\<forall>i<l. p i = i" 
  shows "permute_list p (bin_to_bl l j) = (bin_to_bl l j)"
    using a0 unfolding permute_list_def 
    by (metis lessThan_atLeast0 lessThan_iff map_cong map_nth set_upt size_bin_to_bl) 

lemma bl_to_bin_n_n:assumes a0:"(n::nat) < 2 ^ l" 
  shows "bl_to_bin (bin_to_bl l n) = n"
proof-
  have "bl_to_bin (bin_to_bl l n) = bintrunc l n" 
    using bin_bl_bin by auto
  moreover have "bintrunc l n = n" using bintrunc_mod2p a0  by auto
  ultimately show ?thesis  by auto 
qed

lemma permute_number_id: assumes a0:"\<forall>i<l. p i = i" and a1:"j < 2 ^ l" 
    shows "(permute_number l p) j = j"
proof-
  have "permute_list p (bin_to_bl l j) = (bin_to_bl l j)"
    using a0 eq_bin_to_bl by auto
  moreover have  "bl_to_bin (bin_to_bl l j) = j" using bl_to_bin_n_n[OF a1] by auto    
  ultimately show ?thesis unfolding permute_number_def 
    by auto
qed
  
  

lemma eq_perm_func_eq_perm_list:
  assumes a0:"\<forall>i<length l. p1 i = p2 i" and
       a1:"p1 permutes {0..<length l}" and
       a2:"p2 permutes {0..<length l}" 
     shows "permute_list p1 l = permute_list p2 l"
  using a0 a1 a2
  by (metis length_permute_list lessThan_atLeast0 list_eq_iff_nth_eq permute_list_nth)

lemma eq_permute_number:
  assumes a0:"\<forall>i<l. p1 i = p2 i" and a1:"p1 permutes {0..<l}" and 
          a2:"p2 permutes {0..<l}"  
        shows "permute_number l p1 n = permute_number l p2 n"
proof-
  have "length (bin_to_bl l n) = l" 
    using  Bits_Int.len_bin_to_bl by auto
  then have "permute_list p1  (bin_to_bl l n) = permute_list p2  (bin_to_bl l n)"
    using eq_perm_func_eq_perm_list a0 a1 a2 
    by (auto intro:eq_perm_func_eq_perm_list)
  thus ?thesis unfolding permute_number_def by auto
qed

lemma eq_permute_number2:
  assumes a0:"\<forall>i<l. p1 i = p2 i" and a1:"p1 permutes {0..<l}" and 
          a2:"p2 permutes {0..<l}"  
        shows "(\<lambda>n. permute_number l p1 n) = (\<lambda>n. permute_number l p2 n)"
  using a0 a1 a2 eq_permute_number by auto

definition vector_permutation::"nat \<Rightarrow> 'a vec \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> 'a vec"
  where "vector_permutation n v p \<equiv>                                   
    vec_of_list (permute_list (permute_number n p)  (list_of_vec v))"

lemma eq_length:"l' = permute_list p l \<Longrightarrow> length l' = length l"
  by auto

lemma eq_vector_permutation: 
  assumes a0:"distinct l" and  a1:"length l = length l'" and
          a3:"p1 \<in>(permutes_lists l l')" and
          a4:"p2 \<in>(permutes_lists l l')"
  shows "vector_permutation (length l) v p1 = 
         vector_permutation (length l) v p2"
proof-
  have "\<forall>n<length l. p1 n = p2 n" using eq_perm_function[OF a3 a4 a0] by auto
  moreover have "length l = length l'"
    using a3 not_eq_length_no_permutation by auto
  ultimately have "permute_number (length l) p1 = permute_number (length l) p2"
    using eq_permute_number  a3 a4 unfolding permutes_lists_def
     by (metis (no_types, lifting) eq_permute_number2 lessThan_atLeast0 mem_Collect_eq)     
  then show ?thesis
    unfolding vector_permutation_def
    by (simp add:  a1)
qed

lemma eq_vector_permutation_image_permutes:
  assumes a0:"distinct l" and
          a1:"x \<in> (vector_permutation (length l) v) ` (permutes_lists l l')" and
          a2:"y \<in> (vector_permutation (length l) v) ` (permutes_lists l l')" 
  shows "x = y"
  using a0 a1 a2  
  apply auto
  apply (rule eq_vector_permutation[OF a0], auto)
  using not_eq_length_no_permutation by blast

definition change_orientation_set::"'q::linorder list \<Rightarrow> 'a vec \<Rightarrow> 'q list \<Rightarrow> 'a vec set"
  where "change_orientation_set l v l' \<equiv>  
     (vector_permutation (length l) v) ` (permutes_lists l l')"


definition change_orientation::" 'a vec \<Rightarrow> 'q::linorder list \<Rightarrow> 'q list \<Rightarrow> 'a vec" ("_ . \<^sub>_ \<^sub>\<leadsto>  \<^sub>_" [80,80, 80] 80) 
  where "change_orientation v l l' \<equiv>  
     THE e. e \<in> change_orientation_set l v l'"

lemma change_base_set_same_element:
  assumes a0:"distinct l" and
              a1:"x \<in> (change_orientation_set l v l')" and
              a2:"y \<in> (change_orientation_set l v l')" 
  shows "x = y"
  using a0 a1 a2  unfolding change_orientation_set_def 
  by (auto intro: eq_vector_permutation_image_permutes)

lemma change_base_set_has_element:
  assumes a0:"distinct l" and  a2:"length l = length l'" and 
          a3:"set l = set l'"
  shows "change_orientation_set l v l' \<noteq> {}"
  using eq_length_there_is_perm[OF a2 a3 a0]  
  unfolding change_orientation_set_def by auto

lemma change_base_set_card_1:
  assumes a0:"distinct l" and  a1:"length l = length l'" and 
          a2:"set l = set l'"
        shows "card (change_orientation_set l v l') = 1"
  using change_base_set_same_element[OF a0] change_base_set_has_element[OF a0 a1 a2]  
  by (metis is_singletonI' is_singleton_altdef)

lemma change_base_alt_def: 
  assumes a0:"distinct l" and  a1:"length l = length l'" and 
          a2:"set l = set l'"
  shows "(v.\<^sub>l\<^sub>\<leadsto>\<^sub>l') = 
    vector_permutation (length l) v (SOME p. p \<in>(permutes_lists l l'))"  
proof-
  have "\<exists>p. p \<in>(permutes_lists l l')"
    by (meson a0 a1 a2 all_not_in_conv eq_length_there_is_perm)
  then show ?thesis unfolding change_orientation_set_def change_orientation_def
    apply clarify
    apply (rule the_equality)
     apply (metis emptyE imageI some_in_eq)    
    apply (erule imageE)             
    using eq_vector_permutation[OF a0 a1] 
          some_eq_ex[of "\<lambda>p. p \<in> permutes_lists l l'"]
    by auto
qed

lemma change_orientation_length:
  assumes a0:"distinct l" and  a1:"length l = length l'" and 
          a2:"set l = set l'"
        shows "dim_vec v  = dim_vec  (v.\<^sub>l\<^sub>\<leadsto>\<^sub>l')"  
    unfolding change_base_alt_def[OF a0 a1 a2]
              vector_permutation_def permute_list_def 
    by auto

lemma assumes a0:"i < length l" and 
              a1:"p permutes {..<length l}" and 
              a2:"l = map (\<lambda>i. l ! p i) [0..<length l]" and 
              a3:"distinct l"
            shows "p i = i"
  using a0 a1 a2 a3
  by (metis distinct_Ex1 lessThan_iff nth_mem permute_list_def permute_list_nth permutes_in_image)


lemma eq_vector_same_permutation: 
  assumes a0:"distinct l" and a1:"dim_vec v  = 2 ^ length l"
  shows "v.\<^sub>l\<^sub>\<leadsto>\<^sub>l = v"
proof-
  have "\<forall>p \<in> permutes_lists l l. \<forall>i. i<(length l) \<longrightarrow> p i = i"
    unfolding permutes_lists_def   using a0
    apply auto     
    by (metis distinct_Ex1 lessThan_iff nth_mem permute_list_nth permutes_in_image)
  moreover have  "permutes_lists l l \<noteq> {}" using eq_length_there_is_perm a0 by auto  
  ultimately obtain p where permutes:"p \<in> permutes_lists l l \<and> (\<forall>i. i<length l \<longrightarrow> p i = i)" by auto     
  then   
  have "dim_vec v = dim_vec (v.\<^sub>l\<^sub>\<leadsto>\<^sub>l)"    
    by (metis a0 change_orientation_length)
  moreover have  "(v.\<^sub>l\<^sub>\<leadsto>\<^sub>l)  = vector_permutation (length l) v p"  
    using change_base_alt_def[OF a0] permutes eq_vector_permutation[OF a0]
    by (smt someI_ex)
  moreover have "\<forall>j< 2 ^ (length l). permute_number (length l) p j = j" 
    using permutes permute_number_id by auto
  then have "\<forall>i<dim_vec (v.\<^sub>l\<^sub>\<leadsto>\<^sub>l). v $ i = (v.\<^sub>l\<^sub>\<leadsto>\<^sub>l) $ i" using calculation
    apply (auto simp add: vector_permutation_def)
    by (simp add: a1 permute_list_def vec_of_list_index)    
  ultimately show ?thesis by auto
qed
 

definition Normal_Tensor::"'q::linorder set \<Rightarrow> 'q set \<Rightarrow> 'a vec \<Rightarrow> 'a vec"
  where "Normal_Tensor q s v \<equiv> 
      let l' = sorted_list_of_set (s-q)@(sorted_list_of_set q);
          p = SOME p. p \<in> permutes_lists (sorted_list_of_set s) l' in 
        vector_permutation (length l') v p"

end
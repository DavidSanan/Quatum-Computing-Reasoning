(* Title:     Quantum-Semantics/Tensor_permutation.thy
   Author:    David Sanan, Nanyang Technological University 
   Copyright   2020
   License:     BSD
*)


theory Tensor_Permutation
  imports "HOL-Library.Permutations" "Jordan_Normal_Form.Matrix" "HOL-Word.Word" Jordan_Normal_Form.Missing_Permutations
begin

fun find_index_i ::"'a \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow>  nat option"
  where "find_index_i _ [] _  = None"
    |   "find_index_i a (x#xs) n  = (if x = a then Some n else find_index_i a xs (n+1))"


definition find_index ::"'a \<Rightarrow> 'a list \<Rightarrow> nat option"
  where "find_index a l = find_index_i a l 0"

value "the (find_index (0::nat) [1,0,2])"
lemma find_index_i_pos:"find_index_i a xs n = Some i \<Longrightarrow> xs ! (i - n) = a"
proof(induction xs arbitrary: i n)
  case Nil
  then show ?case by auto
next
  case (Cons x xs)
  { assume "a = x"
    then have ?case using Cons
      by simp
  }
  moreover { assume "a\<noteq>x"
    then have "find_index_i a xs (n+1) = Some i" using Cons
      by auto
    moreover have "xs ! (i - (n + 1)) = a" using Cons calculation by auto
    ultimately have ?case apply clarify apply (erule find_index_i.elims) apply auto 
      by (metis (no_types) Suc_eq_plus1 diff_diff_left 
          lessI not_less_zero nth_Cons' option.inject zero_diff zero_less_diff)
  } ultimately show ?case by auto
qed

lemma find_index_i_equiv1:"find_index_i a xs n = Some i \<Longrightarrow> 
                        xs ! (i - n) = a \<and> n \<le> i \<and> i - n < length xs \<and> (\<forall>j<i - n. xs!j \<noteq> a)"
proof(induction xs arbitrary: i n)
  case Nil
  then show ?case by auto
next
  case (Cons x xs)
  { assume "a = x"
    then have ?case using Cons
      by simp
  }
  moreover { assume a00:"a\<noteq>x"
    then have "find_index_i a xs (n+1) = Some i" using Cons
      by auto
    moreover have f0:"xs ! (i - (n + 1)) = a \<and> (n+1 \<le>i) \<and> (i - (n + 1) < length xs) \<and> 
                  (\<forall>j<i - (n + 1). xs!j \<noteq> a)" 
      using Cons calculation by auto
    ultimately have ?case apply clarify apply (erule find_index_i.elims) apply auto
      by (metis One_nat_def Suc_diff_Suc Suc_eq_plus1 Suc_le_eq a00 f0 
               diff_zero not_less_eq nth_non_equal_first_eq) 
  } ultimately show ?case by auto
qed

lemma find_index_i_equiv2:
  "xs ! (i - n) = a \<Longrightarrow> n \<le> i \<Longrightarrow> i - n < length xs \<Longrightarrow> 
   \<forall>j<i - n. xs!j \<noteq> a \<Longrightarrow>  find_index_i a xs n = Some i"
proof(induction xs arbitrary: i n)
  case Nil
  then show ?case by auto
next
  case (Cons x xs)
  { 
    assume "xs = []" then have ?case using Cons by auto
  }
  moreover { assume "xs\<noteq>[]"
    { assume "a = x" and "i - n = 0"
      then have ?case using Cons by auto      
    }
    moreover { assume "a = x" and "i - n \<noteq> 0"
      then have ?case using Cons
        by (meson neq0_conv nth_Cons_0) 
    }
    moreover { 
      assume "a\<noteq>x" and "i - n = 0"
      then have ?thesis using Cons by auto
    }
    moreover {
      assume "a\<noteq>x" and "i - n \<noteq> 0"     
      moreover have "n+1 \<le> i" using calculation by auto
      moreover have "xs ! (i - (n+1)) = a" using Cons calculation by auto
      moreover have "(i - (n+1)) < length xs" using Cons calculation by auto
      moreover have "\<forall>j< i -(n+1). xs ! j \<noteq> a" using Cons calculation
        by (metis Suc_diff_Suc Suc_eq_plus1 Suc_less_eq neq0_conv nth_Cons_Suc zero_less_diff)
      ultimately have "find_index_i a xs (n+1) = Some i" using Cons(1)[of "i" "n+1"] by auto       
      then have ?case
        using \<open>a \<noteq> x\<close> by auto
    }
    ultimately have ?case using Cons.prems(1) nth_Cons_0 by metis   
  } ultimately show ?case by fast
qed

lemma find_index_i_equiv:"find_index_i a xs n = Some i  \<longleftrightarrow> 
                          xs ! (i - n) = a \<and> n \<le> i \<and> i - n < length xs \<and> 
                          (\<forall>j<i - n. xs!j \<noteq> a)"  
  by (meson find_index_i_equiv1 find_index_i_equiv2)


lemma find_index_i_lenght:"find_index_i a xs n = Some i \<Longrightarrow> (i - n) < length xs"
  apply (induction xs arbitrary: i n, fastforce)
  subgoal for x xs i n
    apply (cases "a = x", fastforce+) .
  done

lemma find_index_i_first_index:"find_index_i a xs n = Some i \<Longrightarrow> (\<nexists>m. m < (i-n) \<and> xs ! m = a)"
proof(induction xs arbitrary: i n)
  case Nil
  then show ?case by auto
next
  case (Cons x xs)
  { assume "a = x"
    then have ?case using Cons
      by simp
  }
  moreover { assume a00:"a\<noteq>x"
    then have "find_index_i a xs (n+1) = Some i" using Cons
      by auto
    moreover have "\<not> (\<exists>m<i - (n + 1). xs ! m = a)" using Cons calculation by auto
    ultimately have ?case apply clarify apply (erule find_index_i.elims) apply auto
      by (metis One_nat_def Suc_diff_Suc a00 add.commute less_diff_conv 
                less_imp_diff_less not_less_eq nth_non_equal_first_eq)
  } ultimately show ?case by auto
qed

lemma find_index_i_none:"find_index_i a xs n = None \<Longrightarrow> \<forall>i<length xs. xs !i \<noteq> a"
proof(induction xs arbitrary: n)
  case Nil
  then show ?case by auto
next
  case (Cons x xs)
  { assume "a = x"
    then have ?case using Cons
      by simp
  }
  moreover { assume a00:"a\<noteq>x"
    then have "\<forall>i<length xs. xs !i \<noteq> a" using Cons
      by auto
    then have ?case using a00
      by (metis One_nat_def Suc_diff_Suc Suc_less_eq diff_zero length_Cons neq0_conv nth_Cons')
  } ultimately show ?case by auto
qed

lemma find_index_i_distinct:
  assumes a0:"distinct xs" and
    a1:"find_index_i a xs n = Some i"
  shows "\<nexists>m. m<length xs \<and> m \<noteq> (i-n) \<and> xs ! m = a"
proof-
  have "xs!(i-n) = a \<and> (i-n) < length xs" 
    using find_index_i_pos[OF a1] find_index_i_lenght[OF a1] by auto
  thus ?thesis using a0 nth_eq_iff_index_eq by fast
qed

lemma find_index_pos:"find_index a l = Some i \<Longrightarrow> l ! i = a"
  unfolding find_index_def using find_index_i_pos by fastforce

lemma find_index_first_index:"find_index a l = Some i \<Longrightarrow> (\<nexists>m. m < i \<and> l ! m = a)"
  unfolding find_index_def using find_index_i_first_index by fastforce

lemma find_index_none:"find_index a xs = None \<Longrightarrow> \<forall>i<length xs. xs !i \<noteq> a"
  unfolding find_index_def using find_index_i_none by fastforce

lemma find_index_i:"find_index a xs = Some i \<Longrightarrow> i < length xs"
  unfolding find_index_def using find_index_i_lenght by fastforce

lemma find_index_distinct:
  "distinct xs \<Longrightarrow> find_index a xs = Some i \<Longrightarrow> 
    \<nexists>m. m<length xs \<and> m \<noteq> i \<and> xs ! m = a"
  unfolding find_index_def using find_index_i_distinct by fastforce

lemma find_index_equiv_less_i:"find_index a xs = Some i  \<longleftrightarrow> 
                          xs ! i = a \<and>  i  < length xs \<and> 
                          (\<forall>j<i. xs!j \<noteq> a)"
  unfolding find_index_def 
  by (simp add: find_index_i_equiv)

lemma find_index_equiv: "distinct xs \<Longrightarrow> find_index a xs = Some i  \<longleftrightarrow> 
                          xs ! i = a \<and>  i  < length xs \<and> 
                          (\<forall>j\<noteq>i. j<length xs \<longrightarrow> xs!j \<noteq> a)"
  unfolding find_index_def
  by (metis find_index_def find_index_distinct find_index_equiv_less_i 
             find_index_i_none not_Some_eq) 


lemma distinct_xs_index_a: 
  "distinct xs \<Longrightarrow> a \<in> set xs \<Longrightarrow> \<exists>!i. find_index a xs = Some i \<and> i < length xs"
  by (metis find_index_def find_index_distinct find_index_i_none in_set_conv_nth option.exhaust)
 
lemma distinct_xs_index_b: 
  "distinct xs \<Longrightarrow> a \<in> set xs \<Longrightarrow> (\<exists>!i. find_index a xs = Some i) \<and> the (find_index a xs) < length xs"
  using distinct_xs_index_a by fastforce


definition list_permutation_functions::"'a list \<Rightarrow> (nat \<Rightarrow> nat) set"
  where "list_permutation_functions ls \<equiv> {p. p permutes {..<length ls}}"

definition list_permutations :: "'a list \<Rightarrow> 'a list set"
  where "list_permutations ls \<equiv> (\<lambda>p. permute_list p ls) ` list_permutation_functions ls"
  

definition get_permutation_list::"'a list \<Rightarrow> 'a list \<Rightarrow> (nat \<Rightarrow> nat)"
  where "get_permutation_list l l' \<equiv> 
    foldl (\<lambda>f e. f(e:= the (find_index (l'!e) l))) id [0..<length l]"   


abbreviation p_inv where "p_inv \<equiv> Hilbert_Choice.inv"


lemma h1:"i<length as \<Longrightarrow> as \<noteq>[]"
  by auto

lemma distinct_remove:
  assumes a0:"length as = length bs" and
      a1:"set as = set bs" and a2:"distinct bs" and
      a5:"bs!j = as!i"
  shows  "distinct (remove1 (bs!j) bs) \<and> distinct (remove1 (as!i) as) \<and> 
             set (remove1 (as!i) as) = set (remove1 (bs!j) bs)"
  by (simp add: a0 a1 a2 a5 card_distinct distinct_card)

lemma i_not_in_index_f:
  assumes 
  a0:"length as = length bs" and
  a1:"set as = set bs" and
  a2:"i\<ge> length as" and a4:"m\<le>length as" and a5:"n\<le>m"
shows "(foldl (\<lambda>f e. f(e:= the (find_index (bs!e) as))) f [n..<m]) i =  (f i)"
  using a0 a1 a2 a4 a5
proof(induct "m-n" arbitrary: as n bs f )
  case 0
  then show ?case by auto
next
  case (Suc l)    
  let ?i = "the (find_index (bs ! n) as)"
  let ?f = "(\<lambda>f e. f(e := the (find_index (bs ! e) as)))"        
  have step:"foldl (\<lambda>f e. f(e := the (find_index (bs ! e) as))) (f(n := the (find_index (bs ! n) as)))
        [Suc n..<m] i = f i" 
    using Suc(1)[of  "Suc n" as bs  "(?f f n)", simplified] Suc(2) Suc(3,4,5,6,7) by auto  
  moreover have "[n..<m] = n#[Suc n..<m]"
    using Suc.hyps(2) upt_conv_Cons by auto 
  then have "foldl ?f f [n..<m] = foldl ?f (?f f n) [Suc n..<m]" by auto
  ultimately show ?case
    by simp
qed

lemma i_not_in_n_m_f:
  assumes 
  a0:"length as = length bs" and
  a1:"set as = set bs" and
  a2:"i\<ge> m \<or> i<n" and a4:"m\<le>length as" and a5:"n\<le>m"
shows "(foldl (\<lambda>f e. f(e:= the (find_index (bs!e) as))) f [n..<m]) i =  (f i)"
  using a0 a1 a2 a4 a5
proof(induct "m-n" arbitrary: as n bs f )
  case 0
  then show ?case by auto
next
  case (Suc l)    
  let ?i = "the (find_index (bs ! n) as)"
  let ?f = "(\<lambda>f e. f(e := the (find_index (bs ! e) as)))"        
  have step:"foldl (\<lambda>f e. f(e := the (find_index (bs ! e) as))) (f(n := the (find_index (bs ! n) as)))
        [Suc n..<m] i = f i" 
    using Suc(1)[of  "Suc n" as bs  "(?f f n)", simplified] Suc(2) Suc(3,4,5,6,7) by auto  
  moreover have "[n..<m] = n#[Suc n..<m]"
    using Suc.hyps(2) upt_conv_Cons by auto 
  then have "foldl ?f f [n..<m] = foldl ?f (?f f n) [Suc n..<m]" by auto
  ultimately show ?case
    by simp
qed


lemma  get_permutation_list_not_index_id:
  "length a = length b \<Longrightarrow> set a = set b \<Longrightarrow> i \<ge> length a \<Longrightarrow> 
   get_permutation_list a b i = i \<and> i \<ge> length a"
  unfolding get_permutation_list_def using i_not_in_index_f[of a b i "length a" 0 "id"]
  by auto


lemma i_in_n_m_index_f:
  assumes 
  a0:"length as = length bs" and
  a1:"set as = set bs" and
  a2:"i < m" and a3:"i\<ge>n" and a4:"m\<le>length as" and a5:"n\<le>m"
shows "(foldl (\<lambda>f e. f(e:= the (find_index (bs!e) as))) f [n..<m]) i =  the (find_index (bs!i) as)"
  using a0 a1 a2 a3 a4 a5
proof(induct "m-n" arbitrary: as n bs f i)
  case 0
  then show ?case by auto
next
  case (Suc l)    
  let ?i = "the (find_index (bs ! n) as)"
  let ?f = "(\<lambda>f e. f(e := the (find_index (bs ! e) as)))"        
  have step:"foldl (\<lambda>f e. f(e := the (find_index (bs ! e) as))) (f(n := the (find_index (bs ! n) as)))
        [Suc n..<m] i = the (find_index (bs!i) as)" 
  proof-
    { assume a00:"i=n"
      have "Suc i \<le> m \<and> i < Suc i \<and> m \<le> length as \<and> 
            (f(i := the (find_index (bs ! i) as))) i = the (find_index (bs ! i) as)"
        by (simp add: Suc.prems(3) Suc.prems(5) Suc_le_eq)
      then have ?thesis
        by (simp add: Suc.prems(1) Suc.prems(2) a00 i_not_in_n_m_f)              
    }
    moreover { 
      assume a00:"i>n"
      then have ?thesis 
        using Suc(1)[of  "Suc n" as bs  i "(?f f n)", simplified] Suc(2) Suc(3,4,5,6,7)
        by auto
    } ultimately show ?thesis
      using Suc.prems(4) le_neq_implies_less by blast
  qed
  moreover have "[n..<m] = n#[Suc n..<m]"
    using Suc.hyps(2) upt_conv_Cons by auto 
  then have "foldl ?f f [n..<m] = foldl ?f (?f f n) [Suc n..<m]" by auto
  ultimately show ?case
    by simp
qed

lemma  get_permutation_list_index_id:
  "length a = length b \<Longrightarrow> set a = set b \<Longrightarrow> i < length a \<Longrightarrow>
     get_permutation_list a b i = the (find_index (b!i) a) \<and> i<length a"
  unfolding get_permutation_list_def using i_in_n_m_index_f[of a b i "length a" 0 "id"]
  by auto

lemma get_permutation_list:"length a = length b \<Longrightarrow> set a = set b \<Longrightarrow> 
       (get_permutation_list a b i = the (find_index (b!i) a) \<and> i<length a) \<or>
       (get_permutation_list a b i = i \<and> i\<ge>length a)"
  using  get_permutation_list_not_index_id get_permutation_list_index_id 
  by (metis  not_less)
 

lemma get_permutation_list_bijective1:
  assumes 
  a0:"length as = length bs" and 
  a1:"set as = set bs" and a2:"distinct as" and  a3:"y<length as"
shows "\<exists>i. get_permutation_list as bs i = y \<and> i <length as"
proof-
  have a00:"\<forall>i<length as. get_permutation_list as bs i = the (find_index (bs!i) as)"
    using get_permutation_list[OF a0 a1] by fastforce
  obtain i where "i<length bs \<and> as ! y = bs !i " using a0 a1 a2
    by (metis a3 in_set_conv_nth)
  moreover have "\<forall>j. j \<noteq> y \<longrightarrow> j < length as \<longrightarrow> as ! j \<noteq> bs ! i"
    using a0 a1 a2  calculation
    by (metis a3  nth_eq_iff_index_eq) 
  ultimately show ?thesis using find_index_equiv[OF a2, of "bs !i" y] a00
    using a0 a3 by force
qed 
  

lemma foldl_find_index_bij2:
  assumes 
  a0:"length as = length bs" and
  a1:"set as = set bs" and a2:"distinct as" and 
  a5:"get_permutation_list as bs i = get_permutation_list as bs j"
shows "i = j"
proof-
  { assume a00:"i\<ge> length as" and a01:"j\<ge> length as"        
    then have ?thesis
      using a5 a0 a1 get_permutation_list_not_index_id by fastforce
  }
  moreover { assume a00:"i<length as" and a01:"j\<ge> length as"
    have "get_permutation_list as bs j = j"
      using a0 a1 a00 a01 get_permutation_list_not_index_id by fastforce
    moreover have "get_permutation_list as bs i = the (find_index (bs!i) as) \<and> i < length as"
      using get_permutation_list[OF a0 a1]
          a00   a0 a1 a2 get_permutation_list_index_id by blast
    ultimately have ?thesis
      by (metis a0 a01 a1 a2 a5 distinct_Ex1 find_index_equiv 
                find_index_none leD nth_mem option.exhaust_sel)
  }
  moreover { assume a00:"j<length as" and a01:"i\<ge> length as"
    have "get_permutation_list as bs i = i"
      using a0 a1 a00 a01 get_permutation_list_not_index_id by fastforce
    moreover have "get_permutation_list as bs j = the (find_index (bs!j) as) \<and> j < length as"
      using get_permutation_list[OF a0 a1]
          a00   a0 a1 a2 get_permutation_list_index_id by blast
    ultimately have ?thesis
      by (metis a0 a01 a1 a2 a5 distinct_Ex1 find_index_equiv 
                find_index_none leD nth_mem option.exhaust_sel)
  }
  moreover { assume a00:"i< length as" and a01:"j<length as"  
    have "get_permutation_list as bs i = the (find_index (bs!i) as)"
      using get_permutation_list[OF a0 a1]
            a0 a1 a2 get_permutation_list_index_id a00 by blast      
    moreover have "get_permutation_list as bs j = the (find_index (bs!j) as)"
      using get_permutation_list[OF a0 a1] a0 a01 leD by auto
    moreover have "\<exists>!k. find_index (bs!j) as = Some k \<and> k < length as"
      using a0 a1 a01  distinct_xs_index_a[OF a2] by auto 
    moreover have "\<exists>!k. find_index (bs!i) as = Some k \<and> k < length as"
      using a0 a1 a00  distinct_xs_index_a[OF a2] by auto    
    ultimately have ?thesis
      by (metis a0 a00 a01 a1 a2 a5 card_distinct 
           distinct_card find_index_pos nth_eq_iff_index_eq option.sel)
  }
  ultimately show ?thesis by fastforce
qed 

lemma  get_permutation_list_bijective:
  "length a = length b \<Longrightarrow> set a = set b \<Longrightarrow> distinct a \<Longrightarrow>
   \<exists>!x. get_permutation_list a b x = y"
  using get_permutation_list_bijective1 foldl_find_index_bij2
  by (metis get_permutation_list)
  
lemma get_permutation_list_permutes:
  "length a = length b \<Longrightarrow> set a = set b \<Longrightarrow> distinct a \<Longrightarrow>
         (get_permutation_list a b) permutes  {..<length a}" 
  using get_permutation_list_not_index_id get_permutation_list_bijective
  unfolding permutes_def
  by (simp add: get_permutation_list_bijective get_permutation_list_not_index_id)  

lemma get_permutation_list_permute_list:
  assumes a0:"length a = length b" and a1:"set a = set b" and a2:"distinct a"
  shows "permute_list (get_permutation_list a b) a = b"
proof-
  let ?p = "map (\<lambda>i. a ! get_permutation_list a b i) [0..<length a]"
  have  "length ?p = length b" using a0 by auto
  moreover have  "\<forall>i<length ?p. ?p!i = b!i"
  proof-
    { fix i
      assume a00:"i<length ?p"
      then have "?p!i =  a ! get_permutation_list a b i" by auto
      then have "?p!i = b!i" 
        using get_permutation_list_index_id[OF a0 a1 a00[simplified]]
              find_index_equiv[OF a2] find_index_none[of "b!i"] a0 a1 a2
        by (metis a0 a1 a2 distinct_Ex1  nth_mem option.exhaust_sel)
    } then show ?thesis by auto
  qed
  ultimately show ?thesis unfolding  permute_list_def
  using nth_equalityI by blast
qed

lemma get_permutation_list_tran:
  assumes a0:"length a = length b" and a1:"set a = set b" and a2:"distinct a" and 
              a3:"length b = length c" and a4:"set b = set c"
  shows "get_permutation_list a b o get_permutation_list b c = get_permutation_list a c"  
proof
  fix i 
  { assume a00:"i < length a"
    then have "(get_permutation_list a b \<circ> get_permutation_list b c) i = get_permutation_list a c i"

    using a0 a1 a2 a3 a4 a00
    by (smt card_distinct comp_apply distinct_card 
             get_permutation_list_index_id get_permutation_list_permute_list 
             get_permutation_list_permutes lessThan_atLeast0 permute_list_nth permutes_less(1))      
  }
  moreover {
    assume a00:"i\<ge> length a"
    then have "(get_permutation_list a b \<circ> get_permutation_list b c) i = get_permutation_list a c i"
      by (simp add: a0 a1 a3 a4 get_permutation_list_not_index_id)      
  }
  ultimately 
    show "(get_permutation_list a b \<circ> get_permutation_list b c) i = get_permutation_list a c i"
      by fastforce
qed

lemma ref_get_perm_list_l:assumes a0:"distinct l" 
  shows "\<forall>i. i<(length l) \<longrightarrow> get_permutation_list l l i = i"
  apply auto 
  by (metis a0 find_index_def find_index_distinct 
              find_index_i_none get_permutation_list option.exhaust_sel)


lemma inv_permutation: 
  assumes a0:"length a = length b" and a1:"set a = set b" and a2:"distinct a"
  shows "get_permutation_list a b   = p_inv (get_permutation_list b a)"
proof
  fix i
  have "(get_permutation_list a b i = the (find_index (b!i) a) \<and> i<length a) \<or>
       (get_permutation_list a b i = i \<and> i\<ge>length a)"
    using get_permutation_list[OF a0 a1] by auto
  then show "get_permutation_list a b i = p_inv (get_permutation_list b a) i" 
    by (smt a0 a1 a2 card_distinct distinct_card 
               get_permutation_list get_permutation_list_index_id 
                 get_permutation_list_permute_list 
                 get_permutation_list_permutes permute_list_nth permutes_inverses(1)) 
   
qed
(* 
definition permutes_lists::"'a list \<Rightarrow> 'a list \<Rightarrow> (nat \<Rightarrow> nat) set"
  where "permutes_lists ls ls' \<equiv> {p. p permutes {..<length ls} \<and> ls' = permute_list p ls}"

definition the_permutes_lists::"'a list \<Rightarrow> 'a list \<Rightarrow> (nat \<Rightarrow> nat)"
  where "the_permutes_lists ls ls' \<equiv> THE p. p permutes {..<length ls} \<and> ls' = permute_list p ls"
*)

(* lemma only_one_permute_distinct_list:
  assumes a0:"distinct l" and a1:"set l = set l'" and a2:"length l = length l'"
  shows "\<exists>!p. p permutes {..<length l} \<and> l' = permute_list p l"
proof-
  have "\<exists>p. p permutes {..<length l} \<and> l' = permute_list p l" using assms
    by (metis card_distinct distinct_card mset_eq_permutation mset_set_set)
  moreover have  "\<forall>p1 p2. (p1 permutes {..<length l}) \<and> l' = permute_list p1 l \<and> 
                          (p2 permutes {..<length l}) \<and>  l' = permute_list p2 l \<longrightarrow> p1 = p2"
  proof-
    { fix p1 p2
      assume a00:"p1 permutes {..<length l} \<and> l' = permute_list p1 l \<and> 
                  p2 permutes {..<length l} \<and> l' = permute_list p2 l"
      then have  "p1 = p2"
      proof-
        { assume a000:"p1 \<noteq> p2" 
          then obtain i where  "p1 i \<noteq> p2 i"
            by auto
          moreover have "i<length l"
            using a00 a000 calculation
            by (metis lessThan_iff permutes_not_in)
          moreover have "l' ! i = l ! (p1 i) \<and> l' ! i  = l ! (p2 i)"
            using calculation
            using a00 permute_list_nth by auto
          ultimately have False using a00 a0 a1 a2
            by (metis (mono_tags, lifting) distinct_conv_nth lessThan_iff permutes_in_image)
        }
        thus ?thesis by auto
      qed       
    } thus ?thesis by auto
  qed
  ultimately show ?thesis by auto
qed



lemma permute_lists_card_1: 
  assumes a0:"distinct ls" and a1:"set ls = set ls'" and a2:"length ls = length ls'"
  shows "card (permutes_lists ls ls') = 1" 
proof-
  { assume a00:"card (permutes_lists ls ls') \<noteq> 1"
    have "finite (permutes_lists ls ls')"
      unfolding permutes_lists_def 
      using only_one_permute_distinct_list[OF a0 a1 a2]
      by (simp add: finite_permutations)
    then have  "card (permutes_lists ls ls') \<noteq> 0"
      unfolding permutes_lists_def 
      using only_one_permute_distinct_list[OF a0 a1 a2]
      by auto    
    then obtain x1 x2 where 
      "x1\<in>(permutes_lists ls ls') \<and>  x2\<in>(permutes_lists ls ls') \<and> x1\<noteq>x2"
      by (metis (full_types) a00 card_eq_0_iff is_singletonI' is_singleton_altdef)
    then have False 
      using only_one_permute_distinct_list[OF a0 a1 a2] unfolding permutes_lists_def
      by auto
  } thus ?thesis by auto
qed
*)
(* lemma not_eq_length_no_permutation:
  "length ls \<noteq> length ls' \<Longrightarrow> permutes_lists ls ls' = {}"
  unfolding permutes_lists_def by auto
*)
(* lemma eq_length_there_is_perm:
  "length ls = length ls' \<Longrightarrow> set ls = set ls' \<Longrightarrow> distinct ls \<Longrightarrow> 
   permutes_lists ls ls' \<noteq> {}"
  unfolding permutes_lists_def apply auto
  by (metis card_distinct distinct_card mset_eq_permutation mset_set_set)
*)
(* lemma eq_perm_function: 
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
*)
(* definition vector_permutations::"'a vec \<Rightarrow> 'a vec set" where
   "vector_permutations v = vec_of_list ` (list_permutations (list_of_vec v))"
*)
lemma diff_permutations:
    "ls'\<in> list_permutations ls \<Longrightarrow> 
     ls'' \<in> list_permutations ls \<Longrightarrow> ls'\<noteq> ls'' \<Longrightarrow> 
      (\<exists>p1 p2.  ls' = permute_list p1 ls \<and> ls'' = permute_list p2 ls \<and> p1\<noteq>p2 \<and> 
                p1 permutes {..<length ls} \<and> p2 permutes {..<length ls})"
  unfolding list_permutations_def list_permutation_functions_def
  by force

definition permute_number :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow>  nat"
  where "permute_number l p n \<equiv> if n < 2 ^ l then nat (bl_to_bin (permute_list p (bin_to_bl l n)))
                                else n"

lemma permute_big_n:"n \<ge> 2 ^ l \<Longrightarrow> permute_number l p n = n"
  unfolding permute_number_def by auto


lemma permute_list_comp:"p permutes {..< length l} \<Longrightarrow> permute_list p (permute_list (p_inv p) l) = l"
  by (metis (no_types) permute_list_compose permute_list_id permutes_inv_o(2))

lemma id_permute_number_inverse: 
  assumes a0:"y < 2 ^ l" and a1:"p permutes {..<l}" and 
          a2:"x = nat (bl_to_bin (permute_list (p_inv p) (bin_to_bl l (int y))))"
  shows "nat (bl_to_bin (permute_list p (bin_to_bl l (int x)))) = y"
proof-
  let ?y = "nat (bl_to_bin (permute_list (p_inv p) (bin_to_bl l (int y))))"
  have "?y < 2 ^ l" using a0
    by (metis bl_to_bin_lt2p length_permute_list nat_less_numeral_power_cancel_iff size_bin_to_bl)
  moreover have  "bin_to_bl l (int ?y) = permute_list (p_inv p) (bin_to_bl l (int y))"        
    by (metis bl_bin_bl bl_to_bin_ge0 int_nat_eq length_permute_list size_bin_to_bl)             
  ultimately have "nat (bl_to_bin (permute_list p (bin_to_bl l (int ?y)))) = y"
    using a0 bin_bl_bin bintrunc_mod2p permute_list_comp 
    by (metis a1 int_mod_eq' nat_int of_nat_0_le_iff 
              of_nat_less_numeral_power_cancel_iff size_bin_to_bl)        
  then show ?thesis using a2
    by blast 
qed

lemma assumes a1:"p permutes {..<l}"
  shows "permute_number l p (permute_number l (p_inv p) y) = y"
proof-
  { assume a00:"y < 2 ^ l"
    then have ?thesis
      unfolding permute_number_def using id_permute_number_inverse[OF a00 a1]
      by (smt bl_to_bin_ge0 bl_to_bin_lt2p int_nat_eq length_permute_list not_numeral_le_zero 
            numeral_less_iff of_nat_less_imp_less of_nat_numeral of_nat_power 
            power_less_imp_less_base semiring_norm(76) size_bin_to_bl)
  }
  moreover {
    assume a00:"y \<ge> 2 ^ l"
    then have ?thesis unfolding permute_number_def by auto
  }
  ultimately show ?thesis by fastforce
qed
 
lemma permute_number_permutes_2_pow_l:
  assumes a0:"p permutes {..<l}"
  shows "permute_number l p permutes {..< 2^l}"  
proof-
  have "(\<forall>y. \<exists>!x. (if x < 2 ^ l then nat (bl_to_bin (permute_list p (bin_to_bl l (int x)))) else x) = y)"
  proof{       
    fix y    
    have "\<exists>x. (if x < 2 ^ l then nat (bl_to_bin (permute_list p (bin_to_bl l (int x)))) else x) = y"
    proof(cases "y < 2 ^ l")
      case True  
      then show ?thesis using id_permute_number_inverse a0       
        by (metis bl_to_bin_lt2p length_permute_list 
               nat_less_numeral_power_cancel_iff size_bin_to_bl)      
    next
      case False
      then show ?thesis by auto
    qed     
    moreover have "\<forall>x z. (if x < 2 ^ l then nat (bl_to_bin (permute_list p (bin_to_bl l (int x)))) else x) = y \<and> 
                (if z < 2 ^ l then nat (bl_to_bin (permute_list p (bin_to_bl l (int z)))) else z) = y \<longrightarrow>
                x = z" 
    proof-
      { fix x z
        assume  a0:"(if x < 2 ^ l then nat (bl_to_bin (permute_list p (bin_to_bl l (int x)))) else x) = y" and
                a1:"(if z < 2 ^ l then nat (bl_to_bin (permute_list p (bin_to_bl l (int z)))) else z) = y"
        { assume a00:"y < 2 ^ l" 
          moreover have "x < 2 ^ l \<and> z < 2 ^ l" 
            using a0 a1 calculation
            by presburger
          moreover have  "nat (bl_to_bin (permute_list p (bin_to_bl l (int x)))) = 
                          nat (bl_to_bin (permute_list p (bin_to_bl l (int z))))" 
            using a0 a1 a00 calculation by auto 
          ultimately have "x=z" using id_permute_number_inverse
            by (metis assms permutes_inv permutes_inv_inv)
        }
        moreover { 
          assume a00:"y \<ge> 2 ^ l" 
          then have "x \<ge> 2 ^ l \<and> z \<ge> 2 ^ l" using a0 a1
            by (metis a0 a00 bl_to_bin_lt2p length_permute_list nat_less_numeral_power_cancel_iff 
                      not_le size_bin_to_bl)          
          then have "x=z" using a0 a1 by auto
        }
        ultimately have "x = z"
          using not_le by blast     
      } thus ?thesis by blast
    qed
    ultimately show " \<exists>!x. (if x < 2 ^ l then nat (bl_to_bin (permute_list p (bin_to_bl l (int x)))) else x) = y"
      by blast      
  } qed
  then show ?thesis unfolding permute_number_def permutes_def by auto
qed

lemma permutes_number_def_comp:
  assumes a0:"p permutes {..<l}" and a1:"p' permutes {..< l}" and a2:"n < 2 ^ l"
  shows "nat (bl_to_bin (permute_list (p \<circ> p') (bin_to_bl l (int n)))) = 
               ((\<lambda>n. nat (bl_to_bin (permute_list p' (bin_to_bl l (int n))))) o
               (\<lambda>n. nat (bl_to_bin (permute_list p (bin_to_bl l (int n)))))) n"
proof-
  let ?n = "nat (bl_to_bin (permute_list p (bin_to_bl l (int n))))"
  have "bin_to_bl l (int (?n)) = permute_list p (bin_to_bl l (int n))"
    using a1 a2
    by (metis bl_bin_bl bl_to_bin_ge0 int_nat_eq length_permute_list size_bin_to_bl)
  moreover have "nat (bl_to_bin (permute_list (p \<circ> p') (bin_to_bl l (int n)))) = 
       nat (bl_to_bin (permute_list p' (permute_list p (bin_to_bl l (int n)))))"
    by (metis a1 permute_list_compose size_bin_to_bl)
  ultimately have "nat (bl_to_bin (permute_list (p \<circ> p') (bin_to_bl l (int n)))) = 
        nat (bl_to_bin (permute_list p' (bin_to_bl l (int (?n)))))" by auto
  thus ?thesis by auto
qed


  

lemma permutes_number_comp:
  assumes a0:"p permutes {..<l}" and a1:"p' permutes {..< l}" 
  shows "permute_number l (p \<circ> p') n = 
         ((permute_number l p') \<circ> (permute_number l p)) n"
proof-
  { assume a00:"n < 2 ^ l" 
    then have "nat (bl_to_bin (permute_list (p \<circ> p') (bin_to_bl l (int n)))) = 
               ((\<lambda>n. nat (bl_to_bin (permute_list p' (bin_to_bl l (int n))))) o 
                (\<lambda>n. nat (bl_to_bin (permute_list p (bin_to_bl l (int n)))))) n" 
      using permutes_number_def_comp[OF a0 a1]
      by blast
    moreover have "(\<lambda>n. nat (bl_to_bin (permute_list p (bin_to_bl l (int n))))) n < 2 ^ l" using a00 a1
      by (metis bl_to_bin_ge0 bl_to_bin_lt2p int_nat_eq length_permute_list  
                  of_nat_less_numeral_power_cancel_iff size_bin_to_bl)
    ultimately have ?thesis using a00 unfolding permute_number_def by clarsimp
  }
  moreover { 
    assume "n \<ge> 2 ^ l"
    then have ?thesis unfolding permute_number_def by auto
  } ultimately show ?thesis by fastforce
qed
  
lemma permutes_number_comp':
  assumes a0:"p permutes {..<l}" and a1:"p' permutes {..< l}" 
  shows "permute_number l (p \<circ> p') n = 
         ((permute_number l p')  (permute_number l p n))"
proof-
  { assume a00:"n < 2 ^ l" 
    then have "nat (bl_to_bin (permute_list (p \<circ> p') (bin_to_bl l (int n)))) = 
               ((\<lambda>n. nat (bl_to_bin (permute_list p' (bin_to_bl l (int n))))) o 
                (\<lambda>n. nat (bl_to_bin (permute_list p (bin_to_bl l (int n)))))) n" 
      using permutes_number_def_comp[OF a0 a1]
      by blast
    moreover have "(\<lambda>n. nat (bl_to_bin (permute_list p (bin_to_bl l (int n))))) n < 2 ^ l" using a00 a1
      by (metis bl_to_bin_ge0 bl_to_bin_lt2p int_nat_eq length_permute_list  
                  of_nat_less_numeral_power_cancel_iff size_bin_to_bl)
    ultimately have ?thesis using a00 unfolding permute_number_def by clarsimp
  }
  moreover { 
    assume "n \<ge> 2 ^ l"
    then have ?thesis unfolding permute_number_def by auto
  } ultimately show ?thesis by fastforce
qed

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

definition vector_permutation1::"nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> 'a vec \<Rightarrow>  'a vec"
  where "vector_permutation1 n p v \<equiv>                                   
    vec_of_list (permute_list (permute_number n p)  (list_of_vec v))"

definition vector_permutation::"nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow>  'a list"
  where "vector_permutation n p v \<equiv>                                   
          permute_list (permute_number n (p_inv p)) v"

definition vector_permutation_inv::"nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow>  'a list"
  where "vector_permutation_inv n p v \<equiv>                                   
          permute_list (permute_number n p) v"

lemma eq_length:"l' = permute_list p l \<Longrightarrow> length l' = length l"
  by auto

(* lemma eq_vector_permutation: 
  assumes a0:"distinct l" and  a1:"length l = length l'" and
          a3:"p1 \<in>(permutes_lists l l')" and
          a4:"p2 \<in>(permutes_lists l l')"
  shows "vector_permutation (length l) p1 v  = 
         vector_permutation (length l) p2 v "
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
*)
(* lemma eq_vector_permutation_image_permutes:
  assumes a0:"distinct l" and
          a1:"x \<in> (\<lambda>p. vector_permutation (length l) p v) ` (permutes_lists l l')" and
          a2:"y \<in> (\<lambda>p. vector_permutation (length l) p  v) ` (permutes_lists l l')" 
  shows "x = y"
  using a0 a1 a2  
  apply auto
  apply (rule eq_vector_permutation[OF a0], auto)
  using not_eq_length_no_permutation by blast
*)

(* definition change_orientation_set::"'q::linorder list \<Rightarrow> 'a list \<Rightarrow> 'q list \<Rightarrow> 'a list set"
  where "change_orientation_set l v l' \<equiv>  
     (\<lambda>p. vector_permutation (length l) p v) ` (permutes_lists l l')"
*)

(* lemma eq_permutes_lists_get_permutation_list:
  assumes a0:"length l = length l'" and a1:"set l = set l'" and a2:"distinct l'" 
  shows "permutes_lists l l' = {get_permutation_list l l'}"
  unfolding permutes_lists_def apply auto
    apply (metis a0 a1 a2 distinct_permute_list get_permutation_list_permute_list get_permutation_list_permutes only_one_permute_distinct_list)
  apply (metis a0 a1 a2 card_distinct distinct_card get_permutation_list_permutes)
  by (simp add: a0 a1 a2 card_distinct distinct_card get_permutation_list_permute_list)               
*)

definition change_orientation::" 'a list \<Rightarrow> 'q::linorder list \<Rightarrow> 'q list \<Rightarrow> 'a list" ("_ . \<^sub>_ \<^sub>\<leadsto>  \<^sub>_" [80,80, 80] 80) 
  where "change_orientation v l l' \<equiv>  
     vector_permutation (length l) (get_permutation_list l l') v"

definition change_orientation_inv::" 'a list \<Rightarrow> 'q::linorder list \<Rightarrow> 'q list \<Rightarrow> 'a list" ("_ . \<^sub>_ \<^sub>\<leadsto>\<^sub>i  \<^sub>_" [80,80, 80] 80) 
  where "change_orientation_inv v l l' \<equiv>  
     vector_permutation_inv (length l) (get_permutation_list l' l) v"

lemma eq_change_orientation:"length l = length l' \<Longrightarrow> set l = set l' \<Longrightarrow> distinct l \<Longrightarrow>
      change_orientation v l l' = change_orientation_inv v l l'"
  unfolding change_orientation_def change_orientation_inv_def vector_permutation_def
vector_permutation_inv_def
  by (metis card_distinct distinct_card inv_permutation)

(* lemma eq_change_orientation_set:
  assumes a0:"length l = length l'" and a1:"set l = set l'" and a2:"distinct l'" 
  shows "change_orientation_set l v l' = {v.\<^sub>l\<^sub>\<leadsto>\<^sub>l'}"
  unfolding change_orientation_set_def change_orientation_def 
  using eq_permutes_lists_get_permutation_list[OF a0 a1 a2] by auto

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




lemma assumes a0:"i < length l" and 
              a1:"p permutes {..<length l}" and 
              a2:"l = map (\<lambda>i. l ! p i) [0..<length l]" and 
              a3:"distinct l"
            shows "p i = i"
  using a0 a1 a2 a3
  by (metis distinct_Ex1 lessThan_iff nth_mem permute_list_def permute_list_nth permutes_in_image)
*)

lemma change_orientation_length:
  assumes a0:"distinct l" and  a1:"length l = length l'" and 
          a2:"set l = set l'"
        shows "length v  = length  (v.\<^sub>l\<^sub>\<leadsto>\<^sub>l')"  
    unfolding change_orientation_def
              vector_permutation_def permute_list_def 
    by auto

lemma eq_vector_same_permutation: 
  assumes a0:"distinct l" and a1:"length v  = 2 ^ length l"
  shows "v.\<^sub>l\<^sub>\<leadsto>\<^sub>l = v"
proof-
  let ?p = "get_permutation_list l l"
  have permute:"\<forall>i. i<(length l) \<longrightarrow> ?p i = i"
    using a0 ref_get_perm_list_l 
    by auto     
  have "length v = length (v.\<^sub>l\<^sub>\<leadsto>\<^sub>l)"
    by (simp add: change_orientation_def vector_permutation_def)    
   (* by (metis a0 change_orientation_length) *)
  moreover have  "(v.\<^sub>l\<^sub>\<leadsto>\<^sub>l)  = vector_permutation (length l) ?p v"  
    unfolding change_orientation_def by blast    
  moreover have "\<forall>j< 2 ^ (length l). permute_number (length l) ?p j = j" 
    using  permute_number_id permute by auto
  then have "\<forall>i<length (v.\<^sub>l\<^sub>\<leadsto>\<^sub>l). v ! i = (v.\<^sub>l\<^sub>\<leadsto>\<^sub>l) ! i" using calculation
    apply (auto simp add: vector_permutation_def)
    by (metis a0 a1 get_permutation_list_permutes 
              inv_permutation permute_list_nth permute_number_permutes_2_pow_l)
  ultimately show ?thesis
    by (simp add: nth_equalityI)
qed

lemma l_permutes_l':"distinct l \<Longrightarrow> length l = length l' \<Longrightarrow> set l = set l' \<Longrightarrow> \<exists>p. p permutes {..<length l}  \<and> l' = permute_list p l"
  by (metis card_distinct distinct_card mset_eq_permutation mset_set_set)


lemma "mset l = mset l' \<Longrightarrow> \<exists>p. l' = permute_list p l \<and> p permutes {..<length l}"
  by (metis mset_eq_permutation)

lemma permute_list_tran:"p permutes {..<length l} \<Longrightarrow> p' permutes {..<length l} \<Longrightarrow>
      l' = permute_list p l \<Longrightarrow> l'' = permute_list p' l \<Longrightarrow> 
  \<exists>p''. l'' = permute_list p'' l' \<and> p'' permutes {..<length l'}"
  by (metis  mset_eq_permutation mset_permute_list)

lemma vector_perm_tran:
  assumes a0:"p permutes {..<length l}" and a1:"l' = permute_list p l" and
          a2:"p' permutes {..<length l'}" and a3:"permute_list (p o p') l = permute_list p' l'" and          
          a4:"length v  = 2 ^ length l" and a5:"length l = length l'"
     shows "vector_permutation (length l)  (p o p') v =  
            vector_permutation (length l') p' (vector_permutation (length l) p v)" 
  unfolding vector_permutation_def
proof- 
  have a00:"p_inv (p \<circ> p') = 
       p_inv (p') o p_inv (p)" 
    using a0 a2 by (metis bij_def  inj_iff o_inv_distrib 
        permutes_inv_o(2) permutes_surj)
  have a0':"(p_inv p) permutes {..<length l}" using a0
    by (simp add: permutes_inv)
  have a2':"(p_inv p') permutes {..<length l}" using a2
    by (simp add: a5 permutes_inv)
  have  "permute_number (length l) (p_inv(p \<circ> p')) = 
         (permute_number (length l) (p_inv p)) \<circ> (permute_number (length l) (p_inv p'))"
    using permutes_number_comp[OF  a2' a0'] a00 by auto           
  moreover  have "permute_number (length l) p' permutes {..<length  v}"
    using permute_number_permutes_2_pow_l[OF a2]
    by (simp add: a4 a5)
  ultimately have "permute_list (permute_number (length l) (p_inv(p \<circ> p'))) v = 
        permute_list (permute_number (length l') (p_inv p')) 
        (permute_list (permute_number (length l) (p_inv p)) v)"
    using a5 permute_list_compose
    by (simp add: permute_list_compose a2 a4 permute_number_permutes_2_pow_l permutes_inv)    
  thus "
     permute_list (permute_number (length l) (p_inv(p \<circ> p'))) v =    
     permute_list (permute_number (length l') (p_inv p'))     
           (permute_list (permute_number (length l) (p_inv p)) v)"
    by (simp add: list_vec)
qed 

lemma ordering_permutation_eq_orientation:
  assumes a0:"distinct l" and a1:"length l = length l'" and a2:"set l = set l'" and 
             a3:"length l = length s" and a4:"set l = set s" and
             a5:"v' = v.\<^sub>l\<^sub>\<leadsto>\<^sub>l'" and a6:"vs = v.\<^sub>l\<^sub>\<leadsto>\<^sub>s" and a7:"length v  = 2 ^ length l"
           shows "vs = v'.\<^sub>l'\<^sub>\<leadsto>\<^sub>s"
proof-
  let ?p_l_l' = "(get_permutation_list l l')"
  let ?p_l_s = "(get_permutation_list l s)"
  let ?p_l'_s = "(get_permutation_list l' s)"    
  have v11:"v' = vector_permutation (length l) ?p_l_l'  v" and 
         v12:"?p_l_l' permutes {..<length l}" and v13:"l' = permute_list  ?p_l_l' l"
    using a5 unfolding change_orientation_def
    apply blast
    using a0 a1 a2 get_permutation_list_permutes apply blast
    by (simp add: a0 a1 a2 get_permutation_list_permute_list)
  have "vs = vector_permutation (length l) ?p_l_s  v" and 
         v12:"?p_l_s permutes {..<length l}" and v13:"s = permute_list  ?p_l_s l"
    using a6 unfolding change_orientation_def
    apply blast
    using a0 a1 a2 get_permutation_list_permutes
    using a3 a4 apply blast
    by (simp add: a0 a3 a4 get_permutation_list_permute_list)  
  moreover have "distinct l'" using a0 
    using distinct_permute_list v12 v13
    using a1 a2 card_distinct distinct_card by fastforce 
  moreover have  "length l' = length s" using a1 a3 by auto
  moreover have "set l' = set s" using a2 a4 by auto
  ultimately have v31:"v'.\<^sub>l'\<^sub>\<leadsto>\<^sub>s = vector_permutation (length l') ?p_l'_s v'" and 
          v32:"?p_l'_s permutes {..<length l'}" and v33:"s = permute_list ?p_l'_s l'" 
    unfolding change_orientation_def  apply blast
    using \<open>distinct l'\<close> \<open>length l' = length s\<close> \<open>set l' = set s\<close> 
      get_permutation_list_permutes apply blast
    by (simp add: \<open>distinct l'\<close> \<open>length l' = length s\<close> \<open>set l' = set s\<close> get_permutation_list_permute_list)    
  then have v22:"s = permute_list (?p_l_l' o ?p_l'_s) l" and v23:"(?p_l_l' o ?p_l'_s) permutes {..<length l}"
    using v32 v33 v12 a1 v13 permute_list_compose
    apply (metis a0 a2 get_permutation_list_permute_list)              
    using a1 permutes_compose v12 v32
    by (simp add: \<open>length l' = length s\<close> \<open>set l' = set s\<close> a0 a2 get_permutation_list_tran)
  (* moreover have "{p. p permutes {..<length l} \<and> s = permute_list p l} \<noteq> {}"
    unfolding permutes_lists_def using l_permutes_l'[OF a0 a3 a4] by auto *)
   have v21:"vs = vector_permutation (length l)  (?p_l_l' o ?p_l'_s) v"  
     using a6 a0 a3 
     by (metis (no_types, hide_lams) a1 a2 a4 change_orientation_def get_permutation_list_tran)
   then show ?thesis 
     unfolding change_orientation_def using vector_perm_tran[of ?p_l_l' l l' ?p_l'_s v]
     by (metis a0 a1 a2 a7 get_permutation_list_permute_list get_permutation_list_permutes v11 v22 v32 v33) 
qed

(* definition Normal_Tensor::"'q::linorder set \<Rightarrow> 'q set \<Rightarrow> 'a vec \<Rightarrow> 'a vec"
  where "Normal_Tensor q s v \<equiv> 
      let l' = sorted_list_of_set (s-q)@(sorted_list_of_set q);
          p = SOME p. p \<in> permutes_lists (sorted_list_of_set s) l' in 
        vector_permutation (length l') v p" *)

end
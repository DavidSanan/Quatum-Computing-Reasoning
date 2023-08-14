theory perm_test
  imports  Q_State

begin

locale mytest =
   fixes s1::"nat set"
   fixes l1::"nat list"
   assumes not_empty:"s1\<noteq>{}" 
 begin
 
 definition add::"nat \<Rightarrow> nat set"
   where "add v \<equiv> insert v s1"
 
 definition addl::"nat \<Rightarrow> nat list"
   where "addl v \<equiv> v#l1"
end

declare mytest.add_def[code]

interpretation v:mytest "{1}" "[]"
  apply unfold_locales by auto 



value "v.add 2"



definition pex::"nat \<Rightarrow> nat"
  where "pex i = (((((id((0::nat):=0))(1:=2))(2:=3)))(3:=1)) i"

definition pex1::"nat \<Rightarrow> nat"
  where "pex1 i = (((((id((0::nat):=0))(1:=3))(2:=1)))(3:=2)) i"

definition dims :: "nat list \<Rightarrow> nat set \<Rightarrow> nat list" where
  "dims tv vs = nths tv vs"
                                                            
definition encode::"nat list \<Rightarrow> nat set \<Rightarrow> nat \<Rightarrow> nat" 
  where "encode tv vs i \<equiv> digit_decode (dims tv vs) (nths (digit_encode tv i) vs)"

definition list_dims::"nat set \<Rightarrow> nat list"
  where "list_dims qvars \<equiv> replicate (card qvars) 2"

definition tensor_vec :: "nat set \<Rightarrow> nat set \<Rightarrow> 'a::times vec \<Rightarrow> 'a vec \<Rightarrow> 'a vec" where
  "tensor_vec s1 s2 v1 v2 \<equiv> 
    let tv = list_dims (s1 \<union> s2) in 
     Matrix.vec (prod_list tv) (\<lambda>i. (v1 $ (encode tv s1 i)) * (v2 $ (encode tv (-s1) i)))"

definition tensor_vec_vars :: "nat set \<Rightarrow> nat set \<Rightarrow> 'a::times vec \<Rightarrow> 'a vec \<Rightarrow> 'a vec" where
  "tensor_vec_vars s1 s2 v1 v2 \<equiv>  
     let vars0 = s1 \<union> s2; 
         dims0 = list_dims vars0;
         s1' = (ind_in_set vars0) ` s1 in   
     Matrix.vec (prod_list dims0) (\<lambda>i. (v1 $ (encode dims0 s1' i)) * (v2 $ (encode dims0 (-s1') i)))"

definition tensor_mat :: "nat set \<Rightarrow> nat set \<Rightarrow> complex mat \<Rightarrow> complex mat \<Rightarrow> complex mat" where
  "tensor_mat s1 s2 m1 m2 \<equiv> 
    let vars0 = s1 \<union> s2; 
        dims0 = list_dims vars0;
        s1' = (ind_in_set vars0) ` s1 in  
    Matrix.mat (prod_list dims0) (prod_list dims0) 
    (\<lambda>(i,j).
       m1 $$ (encode dims0 s1' i, encode dims0 s1' j) * m2 $$ (encode dims0 (-s1') i, encode dims0 (-s1') j))"

definition encode1::"nat set \<Rightarrow> nat set \<Rightarrow> nat \<Rightarrow> nat"
  where "encode1 s1 s2 i \<equiv>
        let vars0 = s1 \<union> s2; 
        dims0 = list_dims vars0;
        s1' = (ind_in_set vars0) ` s1 in encode dims0 s1' i"

definition encode2::"nat set \<Rightarrow> nat set \<Rightarrow> nat \<Rightarrow> nat"
  where "encode2 s1 s2 i \<equiv>
        let vars0 = s1 \<union> s2; 
        dims0 = list_dims vars0;
        s1' = (ind_in_set vars0) ` s1 in encode dims0 (-s1') i"

definition encode12 :: "nat set \<Rightarrow> nat set \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "encode12 s1 s2 i j \<equiv> 
   (let vars0 = s1 \<union> s2; 
     dims0 = list_dims vars0;      
     s1' = (ind_in_set vars0) ` s1;
     dims1 = dims dims0 s1';
     dims2 = dims dims0 (-s1') in
     digit_decode dims0 (weave s1' (digit_encode dims1 i) (digit_encode dims2 j)))"




interpretation v:partial_state2 "list_dims {0,Suc 0,Suc (Suc 0),Suc (Suc (Suc 0))}" "{0,Suc 0}" "{Suc (Suc 0),Suc(Suc(Suc 0))}"
  apply unfold_locales unfolding list_dims_def apply auto
  by (metis Suc_lessI neq0_conv not_less_eq nth_Cons_0 nth_Cons_Suc numeral_2_eq_2)
declare v.vars0_def[code]
declare v.dims0_def[code]
declare v.dims1_def[code]

value "v.vars0"

value "encode12 {0,1} {2,3} 0 0"
value "encode1 {0,1} {2,3} 0"
value "encode2 {0,1} {2,3} 0"
value "encode1 {0,1} {2,3} 1"
value "encode2 {0,1} {2,3} 1"
value "encode2 {0,1} {2,3} 5"

value "encode (list_dims {0,1,2,3}) ((ind_in_set {0::nat,1,2,3}) ` {0,1}) 1"
value "encode (list_dims {0,1,2,3}) (-((ind_in_set {0::nat,1,2,3}) ` {0,1})) 1"
value "encode (list_dims {0,1,2,3}) (-((ind_in_set {0::nat,1,2,3}) ` {0,1})) 0"
(* definition tensor_vec_vars::"nat set \<Rightarrow> nat set \<Rightarrow> 'a::times vec \<Rightarrow> 'a vec \<Rightarrow> 'a vec" where
  "tensor_vec_vars s1 s2 v1 v2 \<equiv>           
     tensor_vec_qp s1 s2 v1 v2" *)

definition plus_QState_vector::" QState \<Rightarrow> QState \<Rightarrow>nat set \<times> complex list"
  where "plus_QState_vector q1 q2 \<equiv> 
     let d1 = (QState_vars q1); 
         d2 = (QState_vars q2); 
          l1 = QState_vector q1; l2 = QState_vector q2 in
          (d1 \<union> d2, list_of_vec(tensor_vec_vars  d1 d2 l1 l2))"

value "plus_QState_vector (QState({2},[1::int,2])) (QState({0,1},[1::int,2,3,4]))"

value "plus_QState_vector (QState({0,1},[1::int,2,3,4])) (QState({2},[1::int,2]))"

value "plus_QState_vector (QState({3},[1::int,2])) 
                          (QState(plus_QState_vector (QState({2},[5::int,7])) (QState({0,1},[11::int,12,29,37]))))"

value "plus_QState_vector (QState(plus_QState_vector (QState ({3},[1::int,2])) (QState({2},[5::int,7])))) 
                          (QState({0,1},[11::int,12,29,37]))"



definition projection1::"nat \<Rightarrow> nat \<Rightarrow> complex mat" ("1\<^sub>_ _") where
  "projection1 k n \<equiv> mat n n (\<lambda> (i,j). if i = k \<and> j = k then 1 else 0)"


value "tensor_mat {0,1} {2,3} (projection1 (0::nat) (2^(card {0::nat,1}))) (1\<^sub>m (2^(card {2::nat,3}))) $$ (4,4)"
value "mat_to_list (projection1 (0::nat) (2^(card {0::nat,1})))"
value "mat_to_list ((1\<^sub>m (2^(card {2::nat,3})))::complex mat)"
value "mat_to_list (tensor_mat {0,1} {2,3} (projection1 (0::nat) (2^(card {0::nat,1}))) (1\<^sub>m (2^(card {2::nat,3}))))"

value "encode1 {0} {1,2} ` {0..<8}"
value "encode2 {0} {1,2} ` {0..<8}"

value "encode1 {1} {0,2} ` {0..<8}"
value "encode2 {1} {0,2} ` {0..<8}"

value "encode1 {0,1} {2} ` {0..<8}"
value "encode2 {0,1} {2} ` {0..<8}"

value "encode1 {0,2} {1} ` {0..<8}"
value "encode2 {0,2} {1} ` {0..<8}"

value "encode1 {0} {1} ` {0..<4}"
value "encode2 {0} {1} ` {0..<4}"

value "encode1 {0} {} ` {0..<2}"
value "encode2 {0} {} ` {0..<2}"


value "encode1 {1} {} ` {0..<2}"
value "encode2 {1} {} ` {0..<2}"


value "mat_to_list (tensor_mat {0} {1} (projection1 (0::nat) (2^(card {0::nat}))) (1\<^sub>m (2^(card {1::nat}))))"

value "mat_to_list (tensor_mat {0,1} {2,3} (projection1 (0::nat) (2^(card {0::nat,1}))) (1\<^sub>m (2^(card {2::nat,3})))) = 
       mat_to_list (tensor_mat {2,3} {0,1} (1\<^sub>m (2^(card {2::nat,3}))) (projection1 (0::nat) (2^(card {0::nat,1}))))"

value "(nths [2::nat,2,2,2] {0::nat,3,2})"
value "list_of_vec (tensor_vec_vars {} {} (vec_of_list [1::complex]) (vec_of_list [1]))"
value "list_of_vec (tensor_vec_vars  {0} {2,3,1} (vec_of_list [0::nat, 1])  (vec_of_list [0::nat, 1, 2,3,4,5,6,7]))"
value "(ind_in_set  {0::nat,1,2}) `  {0,1,2}"
value "list_of_vec (tensor_vec_vars  {0,1,2} {} (vec_of_list [0::nat, 1, 2,3,4,5,6,7]) (vCons 1 vNil))"


value "mat_to_list (mat_of_rows_list 2 [[1::nat,2],[1,1]])"
value "mat_to_list (mat_of_rows_list 2 [[1::nat,2],[2,2]])"

value "mat_to_list (tensor_mat {0,1} {2,3} 
          (mat_of_rows_list 4 [[1::nat,3,4,5],[6,7,8,9],[10,11,12,13],[14,15,16,17]])  
          (mat_of_rows_list 4 [[2::nat,20,21,22],[24,25,27,28],[40,41,44,45],[50,100,9,17]]))"

value "mat_to_list (tensor_mat {2,3} {0,1} 
          (mat_of_rows_list 4 [[2::nat,20,21,22],[24,25,27,28],[40,41,44,45],[50,100,9,17]])  
          (mat_of_rows_list 4 [[1::nat,3,4,5],[6,7,8,9],[10,11,12,13],[14,15,16,17]] ))"

value "let a = [[a0::nat,a1,a2,a3],[b1,b2,b3,b4],[c1,c2,c3,c4],[d1,d2,d3,d4]] in a"

value "(tensor_mat {0,1} {2,3} 
          (mat_of_rows_list 4 [[a0::nat,a1,a2,a3],[b1,b2,b3,b4],[c1,c2,c3,c4],[d1,d2,d3,d4]])  
          (mat_of_rows_list 4 [[e1::nat,e2,e3,e4],[f1,f2,f3,f4],[g1,g2,g3,g4],[h1,h2,h3,h4]]))"
value "list_of_vec (tensor_vec {0,1} {2,3} (vec_of_list [a0::nat,a1,a2,a3]) (vec_of_list [b0,b1,b2,b3])) "

value "permute_list pex [0::nat,3,1,2]"

value "list_of_vec (tensor_vec {0} {1} (vec_of_list [a0::nat,a1]) (vec_of_list [b0,b1])) "
value "list_of_vec (tensor_vec {1} {0} (vec_of_list [b0::nat,b1]) (vec_of_list [a0,a1])) "
value "list_of_vec (tensor_vec {0} {1} (vec_of_list [b0::nat,b1]) (vec_of_list [a0,a1])) "
\<comment>\<open> a * b * c \<close>
value "list_of_vec (tensor_vec {0,1} {2} (vec_of_list [(a0::nat) * b0, a1 * b0, a0 * b1, a1 * b1]) (vec_of_list [c0,c1]))"
value "[a0 * b0 * c0, a1 * b0 * c0, a0 * b1 * c0, a1 * b1 * c0, a0 * b0 * c1, a1 * b0 * c1, a0 * b1 * c1, a1 * b1 * c1]. 
        \<^sub>[0::nat,1,2] \<^sub>\<leadsto>\<^sub>i \<^sub>[1,0,2]"
\<comment>\<open> b * a * c\<close>
value "list_of_vec (tensor_vec {0,1} {2} 
       (vec_of_list [b0 * a0, b1 * a0, b0 * a1, b1 * a1]) 
        (vec_of_list [c0,c1]))"

value "list_of_vec (tensor_vec {0,1} {2,3} 
            (vec_of_list [a00::nat,a01,a30,a31]) (vec_of_list [b10,b11,b20,b21])) "


value "((permute_number)) 3 (get_permutation_list  [0::nat,1,2][1,2,0]) 0"
value "permute_number 3 (get_permutation_list [0::nat,1,2][1,2,0]) 1"
value "permute_number 3 (get_permutation_list [0::nat,1,2] [1,2,0]) 2"
value "permute_number 3 (get_permutation_list  [0::nat,1,2][1,2,0]) 3"
value "permute_number 3 (get_permutation_list  [0::nat,1,2][1,2,0]) 4"
value "permute_number 3 (get_permutation_list [0::nat,1,2][1,2,0]) 5"
value "permute_number 3 (get_permutation_list  [0::nat,1,2][1,2,0]) 6"
value "permute_number 3 (get_permutation_list  [0::nat,1,2][1,2,0]) 7"
value "permute_number 3 (get_permutation_list  [0::nat,1,2][1,2,0]) 8"
lemma "a o f = -a"

value "permute_number 3 (get_permutation_list  [0::nat,1,2][1,2,0]) 0"
value "permute_number 3 (get_permutation_list [0::nat,1,2][1,2,0]) 1"
value "permute_number 3 (get_permutation_list [0::nat,1,2] [1,2,0]) 2"
value "permute_number 3 (get_permutation_list  [0::nat,1,2][1,2,0]) 3"
value "permute_number 3 (get_permutation_list  [0::nat,1,2][1,2,0]) 4"
value "permute_number 3 (get_permutation_list [0::nat,1,2][1,2,0]) 5"
value "permute_number 3 (get_permutation_list  [0::nat,1,2][1,2,0]) 6"
value "permute_number 3 (get_permutation_list  [0::nat,1,2][1,2,0]) 7"
value "permute_number 3 (get_permutation_list  [0::nat,1,2][1,2,0]) 8"

value "permute_number 3 (get_permutation_list  [1::nat,2,0][1,2,0]) 0"
value "permute_number 3 (get_permutation_list [1::nat,2,0][1,2,0]) 1"
value "permute_number 3 (get_permutation_list [1::nat,2,0] [1,2,0]) 2"
value "permute_number 3 (get_permutation_list  [1::nat,2,0][1,2,0]) 3"
value "permute_number 3 (get_permutation_list  [1::nat,2,0][1,2,0]) 4"
value "permute_number 3 (get_permutation_list [1::nat,2,0][1,2,0]) 5"
value "permute_number 3 (get_permutation_list  [1::nat,2,0][1,2,0]) 6"
value "permute_number 3 (get_permutation_list  [1::nat,2,0][1,2,0]) 7"
value "permute_number 3 (get_permutation_list  [1::nat,2,0][1,2,0]) 8"


value "permute_number 4 (get_permutation_list  [0,3,1,2][3::nat,0,2,1]) 0"
value "permute_number 4 (get_permutation_list [0,3,1,2][3::nat,0,2,1]) 1"
value "permute_number 4 (get_permutation_list [0,3,1,2] [3::nat,0,2,1]) 2"
value "permute_number 4 (get_permutation_list  [0,3,1,2][3::nat,0,2,1]) 3"
value "permute_number 4 (get_permutation_list  [0,3,1,2][3::nat,0,2,1]) 4"
value "permute_number 4 (get_permutation_list [0,3,1,2][3::nat,0,2,1]) 5"
value "permute_number 4 (get_permutation_list  [0,3,1,2][3::nat,0,2,1]) 6"
value "permute_number 4 (get_permutation_list  [0,3,1,2][3::nat,0,2,1]) 7"
value "permute_number 4 (get_permutation_list  [0,3,1,2][3::nat,0,2,1]) 8"
value "permute_number 4 (get_permutation_list  [0,3,1,2][3::nat,0,2,1]) 9"
value "permute_number 4 (get_permutation_list  [0,3,1,2][3::nat,0,2,1]) 10"
value "permute_number 4 (get_permutation_list  [0,3,1,2][3::nat,0,2,1]) 11"
value "permute_number 4 (get_permutation_list  [0,3,1,2][3::nat,0,2,1]) 12"
value "permute_number 4 (get_permutation_list  [0,3,1,2][3::nat,0,2,1] ) 13"
value "permute_number 4 (get_permutation_list  [0,3,1,2] [3::nat,0,2,1]) 14"
value "permute_number 4 (get_permutation_list [0,3,1,2] [3::nat,0,2,1]) 15"


value "get_permutation_list [0::nat, 3, 1, 2] [3,0,2,1] 0"
value "get_permutation_list [0::nat, 3, 1, 2] [3,0,2,1] 1"
value "get_permutation_list [0::nat, 3, 1, 2] [3,0,2,1] 2"
value "get_permutation_list [0::nat, 3, 1, 2] [3,0,2,1] 3"

value "permute_number 4 (get_permutation_list  [0,3,1,2][3::nat,0,2,1]) 0"
value "permute_number 4 (get_permutation_list [0,3,1,2][3::nat,0,2,1]) 1"
value "permute_number 4 (get_permutation_list [0,3,1,2] [3::nat,0,2,1]) 2"
value "permute_number 4 (get_permutation_list  [0,3,1,2][3::nat,0,2,1]) 3"
value "permute_number 4 (get_permutation_list  [0,3,1,2][3::nat,0,2,1]) 4"
value "permute_number 4 (get_permutation_list [0,3,1,2][3::nat,0,2,1]) 5"
value "permute_number 4 (get_permutation_list  [0,3,1,2][3::nat,0,2,1]) 6"
value "permute_number 4 (get_permutation_list  [0,3,1,2][3::nat,0,2,1]) 7"
value "permute_number 4 (get_permutation_list  [0,3,1,2][3::nat,0,2,1]) 8"
value "permute_number 4 (get_permutation_list  [0,3,1,2][3::nat,0,2,1]) 9"
value "permute_number 4 (get_permutation_list  [0,3,1,2][3::nat,0,2,1]) 10"
value "permute_number 4 (get_permutation_list  [0,3,1,2][3::nat,0,2,1]) 11"
value "permute_number 4 (get_permutation_list  [0,3,1,2][3::nat,0,2,1]) 12"
value "permute_number 4 (get_permutation_list  [0,3,1,2][3::nat,0,2,1] ) 13"
value "permute_number 4 (get_permutation_list  [0,3,1,2] [3::nat,0,2,1]) 14"
value "permute_number 4 (get_permutation_list [0,3,1,2] [3::nat,0,2,1]) 15"

value "get_permutation_list [3::nat, 0, 2,1] [0,1,2,3] 0"
value "get_permutation_list [3::nat, 0, 2,1] [0,1,2,3] 1"
value "get_permutation_list [3::nat, 0, 2,1] [0,1,2,3] 2"
value "get_permutation_list [3::nat, 0, 2,1] [0,1,2,3] 3"

value "permute_number 4 (get_permutation_list  [3,0,2,1][0::nat,1,2,3]) 0"
value "permute_number 4 (get_permutation_list [3,0,2,1][0::nat,1,2,3]) 1"
value "permute_number 4 (get_permutation_list [3,0,2,1] [0::nat,1,2,3]) 2"
value "permute_number 4 (get_permutation_list  [3,0,2,1][0::nat,1,2,3]) 3"
value "permute_number 4 (get_permutation_list  [3,0,2,1][0::nat,1,2,3]) 4"
value "permute_number 4 (get_permutation_list [3,0,2,1][0::nat,1,2,3]) 5"
value "permute_number 4 (get_permutation_list  [3,0,2,1][0::nat,1,2,3]) 6"
value "permute_number 4 (get_permutation_list  [3,0,2,1][0::nat,1,2,3]) 7"
value "permute_number 4 (get_permutation_list  [3,0,2,1][0::nat,1,2,3]) 8"
value "permute_number 4 (get_permutation_list  [3,0,2,1][0::nat,1,2,3]) 9"
value "permute_number 4 (get_permutation_list  [3,0,2,1][0::nat,1,2,3]) 10"
value "permute_number 4 (get_permutation_list  [3,0,2,1][0::nat,1,2,3]) 11"
value "permute_number 4 (get_permutation_list  [3,0,2,1][0::nat,1,2,3]) 12"
value "permute_number 4 (get_permutation_list  [3,0,2,1][0::nat,1,2,3] ) 13"
value "permute_number 4 (get_permutation_list  [3,0,2,1] [0::nat,1,2,3]) 14"
value "permute_number 4 (get_permutation_list [3,0,2,1] [0::nat,1,2,3]) 15"

value "let v = [a00::nat, a01, a02, a03, a04,a05, a06, a07,a08,a09,a10,a11,a12,a13,a14,a15] in
           change_orientation v [0::nat,3,1,2] [3,0,2,1]
          "

value "let v = [a00::nat, a02, a01, a03, a08, a10, a09, a11, a04, a06, a05, a07, a12, a14, a13, a15] in
           change_orientation v [3::nat,0,2,1] [0,1,2,3]
          "

value "let v = [a00::nat, a01, a02, a03, a04,a05, a06, a07,a08,a09,a10,a11,a12,a13,a14,a15] in
           change_orientation (change_orientation v [0::nat,3,1,2] [3,0,2,1] ) [3::nat,0,2,1] [0,1,2,3]
          "
value "get_permutation_list  [0::nat,3,1,2] [0,1,2,3] 0"
value "get_permutation_list  [0::nat,3,1,2] [0,1,2,3] 1"
value "get_permutation_list  [0::nat,3,1,2] [0,1,2,3] 2"
value "get_permutation_list  [0::nat,3,1,2] [0,1,2,3] 3"

value "permute_number 4 (get_permutation_list  [3,0,2,1][0::nat,1,2,3]) 0"
value "permute_number 4 (get_permutation_list [3,0,2,1][0::nat,1,2,3]) 1"
value "permute_number 4 (get_permutation_list [3,0,2,1] [0::nat,1,2,3]) 2"
value "permute_number 4 (get_permutation_list  [3,0,2,1][0::nat,1,2,3]) 3"
value "permute_number 4 (get_permutation_list  [3,0,2,1][0::nat,1,2,3]) 4"
value "permute_number 4 (get_permutation_list [3,0,2,1][0::nat,1,2,3]) 5"
value "permute_number 4 (get_permutation_list  [3,0,2,1][0::nat,1,2,3]) 6"
value "permute_number 4 (get_permutation_list  [3,0,2,1][0::nat,1,2,3]) 7"
value "permute_number 4 (get_permutation_list  [3,0,2,1][0::nat,1,2,3]) 8"
value "permute_number 4 (get_permutation_list  [3,0,2,1][0::nat,1,2,3]) 9"
value "permute_number 4 (get_permutation_list  [3,0,2,1][0::nat,1,2,3]) 10"
value "permute_number 4 (get_permutation_list  [3,0,2,1][0::nat,1,2,3]) 11"
value "permute_number 4 (get_permutation_list  [3,0,2,1][0::nat,1,2,3]) 12"
value "permute_number 4 (get_permutation_list  [3,0,2,1][0::nat,1,2,3] ) 13"
value "permute_number 4 (get_permutation_list  [3,0,2,1] [0::nat,1,2,3]) 14"
value "permute_number 4 (get_permutation_list [3,0,2,1] [0::nat,1,2,3]) 15"
value "let v = [a00, a01, a02, a03, a04,a05, a06, a07,a08,a09,a10,a11,a12,a13,a14,a15] in
           change_orientation v [0::nat,3,1,2] [0,1,2,3]
          "


(* --------------------------------- *)
value "let v = [a00, a01, a02, a03, a04,a05, a06, a07,a08,a09,a10,a11,a12,a13,a14,a15] in
           change_orientation v [0::nat,3,1,2] [3,0,2,1]
          "

value "permute_number 4 (get_permutation_list   [0::nat,3,2,1] [3,0,2,1]) 0"
value "permute_number 4 (get_permutation_list [0::nat,3,2,1] [3,0,2,1]) 1"
value "permute_number 4 (get_permutation_list [0::nat,3,2,1] [3,0,2,1]) 2"
value "permute_number 4 (get_permutation_list   [0::nat,3,2,1] [3,0,2,1]) 3"
value "permute_number 4 (get_permutation_list    [0::nat,3,2,1] [3,0,2,1] ) 4"
value "permute_number 4 (get_permutation_list   [0::nat,3,2,1] [3,0,2,1]) 5"
value "permute_number 4 (get_permutation_list    [0::nat,3,2,1] [3,0,2,1]) 6"
value "permute_number 4 (get_permutation_list    [0::nat,3,2,1] [3,0,2,1]) 7"
value "permute_number 4 (get_permutation_list    [0::nat,3,2,1] [3,0,2,1]) 8"
value "permute_number 4 (get_permutation_list    [0::nat,3,2,1] [3,0,2,1]) 9"
value "permute_number 4 (get_permutation_list    [0::nat,3,2,1] [3,0,2,1]) 10"
value "permute_number 4 (get_permutation_list    [0::nat,3,2,1] [3,0,2,1]) 11"
value "permute_number 4 (get_permutation_list    [0::nat,3,2,1] [3,0,2,1]) 12"
value "permute_number 4 (get_permutation_list    [0::nat,3,2,1]  [3,0,2,1]) 13"
value "permute_number 4 (get_permutation_list     [0::nat,3,2,1] [3,0,2,1]) 14"
value "permute_number 4 (get_permutation_list    [0::nat,3,2,1] [3,0,2,1]) 15"

value "let v = [a00, a02, a01, a03, a08, a10, a09, a11, a04, a06, a05, a07, a12, a14, a13, a15] in
           change_orientation v [3::nat,0,2,1] [0,1,2,3]
          "
value "(get_permutation_list [0::nat,3,2,1] [0::nat,1,2,3])"
value "permute_number 4 (get_permutation_list  [3,0,2,1] [0::nat,1,2,3]) 0"
value "permute_number 4 (get_permutation_list [3,0,2,1] [0::nat,1,2,3]) 1"
value "permute_number 4 (get_permutation_list [3,0,2,1]  [0::nat,1,2,3] ) 2"
value "permute_number 4 (get_permutation_list  [3,0,2,1] [0::nat,1,2,3]) 3"
value "permute_number 4 (get_permutation_list  [3,0,2,1] [0::nat,1,2,3] ) 4"
value "permute_number 4 (get_permutation_list [3,0,2,1] [0::nat,1,2,3] ) 5"
value "permute_number 4 (get_permutation_list  [3,0,2,1] [0::nat,1,2,3] ) 6"
value "permute_number 4 (get_permutation_list  [3,0,2,1] [0::nat,1,2,3] ) 7"
value "permute_number 4 (get_permutation_list  [3,0,2,1] [0::nat,1,2,3] ) 8"
value "permute_number 4 (get_permutation_list  [3,0,2,1] [0::nat,1,2,3] ) 9"
value "permute_number 4 (get_permutation_list  [3,0,2,1] [0::nat,1,2,3] ) 10"
value "permute_number 4 (get_permutation_list  [3,0,2,1] [0::nat,1,2,3] ) 11"
value "permute_number 4 (get_permutation_list  [3,0,2,1] [0::nat,1,2,3]) 12"
value "permute_number 4 (get_permutation_list  [3,0,2,1] [0::nat,1,2,3]  ) 13"
value "permute_number 4 (get_permutation_list  [3,0,2,1]  [0::nat,1,2,3] ) 14"
value "permute_number 4 (get_permutation_list [3,0,2,1]  [0::nat,1,2,3] ) 15"

value "let v = [a00, a01, a02, a03, a04,a05, a06, a07,a08,a09,a10,a11,a12,a13,a14,a15] in
           change_orientation (change_orientation v [0::nat,3,1,2] [3,0,2,1]) [3::nat,0,2,1] [0,1,2,3]
          "

value "let v = [a00, a01, a02, a03, a04,a05, a06, a07,a08,a09,a10,a11,a12,a13,a14,a15] in
           change_orientation v [0::nat,3,1,2] [0,1,2,3]
          "

value "let v = [a00, a01, a02, a03, a04,a05, a06, a07,a08,a09,a10,a11,a12,a13,a14,a15] in
           change_orientation (change_orientation v   [3::nat,0,2,1] [0,1,2,3]) [3::nat,0,2,1] [0::nat,3,1,2] 
          "

value "permute_number 4 (get_permutation_list   [0::nat,3,2,1] [0,1,2,3]) 0"
value "permute_number 4 (get_permutation_list [0::nat,3,2,1] [0,1,2,3]) 1"
value "permute_number 4 (get_permutation_list [0::nat,3,2,1] [0,1,2,3]) 2"
value "permute_number 4 (get_permutation_list   [0::nat,3,2,1] [0,1,2,3]) 3"
value "permute_number 4 (get_permutation_list    [0::nat,3,2,1] [0,1,2,3] ) 4"
value "permute_number 4 (get_permutation_list   [0::nat,3,2,1] [0,1,2,3]) 5"
value "permute_number 4 (get_permutation_list    [0::nat,3,2,1] [0,1,2,3]) 6"
value "permute_number 4 (get_permutation_list    [0::nat,3,2,1] [0,1,2,3]) 7"
value "permute_number 4 (get_permutation_list    [0::nat,3,2,1] [0,1,2,3]) 8"
value "permute_number 4 (get_permutation_list    [0::nat,3,2,1] [0,1,2,3]) 9"
value "permute_number 4 (get_permutation_list    [0::nat,3,2,1] [0,1,2,3]) 10"
value "permute_number 4 (get_permutation_list    [0::nat,3,2,1] [0,1,2,3]) 11"
value "permute_number 4 (get_permutation_list    [0::nat,3,2,1] [0,1,2,3]) 12"
value "permute_number 4 (get_permutation_list    [0::nat,3,2,1]  [0,1,2,3]) 13"
value "permute_number 4 (get_permutation_list     [0::nat,3,2,1] [0,1,2,3]) 14"
value "permute_number 4 (get_permutation_list    [0::nat,3,2,1] [0,1,2,3]) 15"


value "permute_list pex1 [0::nat,3,1,2]"

value "permute_list pex [0::nat,0,0,0]"
value "permute_list pex [0::nat,0,0,1]"
value "permute_list pex [0::nat,0,1,0]"
value "permute_list pex [0::nat,0,1,1]"
value "permute_list pex [0::nat,1,0,0]"
value "permute_list pex [0::nat,1,0,1]"
value "permute_list pex [0::nat,1,1,0]"
value "permute_list pex [0::nat,1,1,1]"
value "permute_list pex [1::nat,0,0,0]"
value "permute_list pex [1::nat,0,0,1]"
value "permute_list pex [1::nat,0,1,0]"
value "permute_list pex [1::nat,0,1,1]"
value "permute_list pex [1::nat,1,0,0]"
value "permute_list pex [1::nat,1,0,1]"
value "permute_list pex [1::nat,1,1,0]"
value "permute_list pex [1::nat,1,1,1]"

value "permute_list pex1 [0::nat,0,0,0]"
value "permute_list pex1 [0::nat,0,0,1]"
value "permute_list pex1 [0::nat,0,1,0]"
value "permute_list pex1 [0::nat,0,1,1]"
value "permute_list pex1 [0::nat,1,0,0]"
value "permute_list pex1 [0::nat,1,0,1]"
value "permute_list pex1 [0::nat,1,1,0]"
value "permute_list pex1 [0::nat,1,1,1]"
value "permute_list pex1 [1::nat,0,0,0]"
value "permute_list pex1 [1::nat,0,0,1]"
value "permute_list pex1 [1::nat,0,1,0]"
value "permute_list pex1 [1::nat,0,1,1]"
value "permute_list pex1 [1::nat,1,0,0]"
value "permute_list pex1 [1::nat,1,0,1]"
value "permute_list pex1 [1::nat,1,1,0]"
value "permute_list pex1 [1::nat,1,1,1]"

value "permute_number 4 pex "

lemma "(p_inv pex) = pex1"
  unfolding pex_def pex1_def inv_def  
  apply rule by auto

lemma  " (p o p') =  p_inv (p' o p)"
  unfolding inv_def apply auto apply rule apply auto nitpick
  sorry

definition p1::"nat \<Rightarrow> nat"
  where "p1 i \<equiv> ((((id((0::nat):=2))(1:=0))(2:=1))) i"

definition p'::"nat \<Rightarrow> nat"
  where "p' i \<equiv> ((((id((0::nat):=1))(1:=2))(2:=0))) i"

definition p::"nat \<Rightarrow> nat"
  where "p i \<equiv> ((((id((0::nat):=0))(1:=2))(2:=1))) i"

definition "p'' \<equiv> p o p'"

value "permute_list p [3::nat,1,2]" (* l \<rightarrow> l' *)
value "permute_list p' [3::nat,2,1]" (* l' \<rightarrow> s *)


value "(p o p') 0"
value "(p o p') 1"
value "(p o p') 2"

value "(p' o p) 0"
value "(p' o p) 1"
value "(p' o p) 2"

lemma "p_inv (p o p') = (p' o p)"
  unfolding p_def p'_def inv_def
  apply rule
  apply auto
  oops


lemma "p_inv p = p'"
  unfolding p_def p'_def inv_def
  apply rule
  apply auto
  oops

value "permute_list (p o p') [3::nat,1,2]"
value "permute_list (p' o p) [3::nat,1,2]"
value "permute_list p' (permute_list p  [3::nat,1,2])"


value "vector_permutation 3 p ([0::nat,1,2,3,4,5,6,7]) " (* v' = v.l \<rightarrow> l' *)

value "vector_permutation 3 p' [0::nat, 2, 1, 3, 4, 6, 5, 7]" (* vs = v'. l' \<rightarrow> s *)

value "vector_permutation 3 (p o p') ([0::nat,1,2,3,4,5,6,7]) " (* vs = v.l \<rightarrow> s *)

value "vector_permutation 3 (p' o p) ([0::nat,1,2,3,4,5,6,7]) " (* vs = v.l \<rightarrow> s *)

value "vector_permutation 3 p' (vector_permutation 3 p ([0::nat,1,2,3,4,5,6,7]))"

end

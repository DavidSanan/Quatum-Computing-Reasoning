theory Tensor_Product
  imports Deep_Learning.Tensor_Matricization QHLProver.Complex_Matrix

begin


definition tensor_prod_vec :: "'a::times vec \<Rightarrow> 'a vec \<Rightarrow> 'a vec" where
  "tensor_prod_vec v1 v2 = Matrix.vec (dim_vec v1 * dim_vec v2) (\<lambda>i. v1 $ encode1 i * v2 $ encode2 i)"

end

theory Sep_Algebra_Vector
imports  QHLProver.Partial_State Actions.Sep_Prod_Instance QHLProver.Partial_State
begin                                      
instantiation vec :: (comm_ring_1) sep_algebra
begin
definition zero_vec_def: "0 \<equiv> dim_vec "
end


end
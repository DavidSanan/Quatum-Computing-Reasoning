theory Sep_Algebra_QState
  imports  Separation_Algebra.Separation_Algebra
begin                                      
instantiation prod :: (zero,zero) sep_algebra
begin
definition zero_vec_def: "0 \<equiv> (0,0)"
end


end
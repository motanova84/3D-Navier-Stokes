/-
  Tests for PsiNSE Complete Lemmas
  
  Validates the structure and compilation of the new modules
-/

import NavierStokes.PsiNSE_CompleteLemmas_WithInfrastructure

set_option autoImplicit false

namespace NavierStokesTests

-- Test that f₀ constant is defined correctly
example : f₀ = 141.7001 := by rfl

-- Test that theorem statements are available
#check sobolev_embedding_l_infty
#check banach_fixed_point_complete
#check integration_by_parts_divergence_free
#check poincare_inequality_expander
#check agmon_inequality_3d
#check local_existence_kato_complete
#check phi_tensor_treewidth_connection
#check qcal_coherence_implies_regularity

-- Test f₀ derivation theorem
#check f0_from_primes

-- Test that modules are properly imported
#check PNP.CNF_Formula
#check QCAL.FrequencyValidation.validated_f0

-- Test advanced spaces
open NavierStokes
#check SobolevSpace
#check Graph
#check ExpanderGraph

end NavierStokesTests

import LSSecondDiagonalAlgebra
import LSFiberRankProof

noncomputable section
set_option autoImplicit false
open scoped TensorProduct

namespace LeBrunSalamon.Step3CDNativeAudit

theorem tensorSecond_eq_actual {A : Type*} [CommRing A] [Algebra ℂ A]
    (D E : Derivation ℂ A A) :
    Core.ExternalTensorCoordinates.tensorSecond D E = SecondDiagonalAlgebra.second D E := rfl

theorem projectDetector {A : Type*} [CommRing A] [Algebra ℂ A]
    [Algebra.Smooth ℂ A] (t : A ⊗[ℂ] A)
    (ht : t ∈ (KaehlerDifferential.ideal ℂ A) ^ 2)
    (h : ∀ D E : Derivation ℂ A A, Core.ExternalTensorCoordinates.tensorSecond D E t = 0) :
    t ∈ (KaehlerDifferential.ideal ℂ A) ^ 3 := by
  exact SecondDiagonalAlgebra.smooth_second_derivatives_detect t ht h

end LeBrunSalamon.Step3CDNativeAudit

#print axioms LeBrunSalamon.SecondDiagonalAlgebra.smooth_second_derivatives_detect
#print axioms LeBrunSalamon.Step3CDNativeAudit.tensorSecond_eq_actual
#print axioms LeBrunSalamon.Step3CDNativeAudit.projectDetector
#print axioms LeBrunSalamon.FiberRankProof.fiber_rank_and_finite

end

import LSQuadraticLinearTransport
import LSComplexQuadraticMatrix
import LSRelativeVeroneseModel
import LSPolarizedOverIso

/-! Compose the actual GL coordinate changes with the actual relative
Veronese model, retaining the line and base at every step. The matrix
identity, standard conic, and projective action are the precise inputs;
no formal-trait classification is assumed. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight

namespace LeBrunSalamon.QuadraticPolarizedModels

variable (R : Type) [CommRing R]

def line (q : PlaneQuadratic.Coefficients R) : LineBundle (PlaneQuadratic.ZeroScheme R q) :=
  pullbackLine (PlaneQuadratic.inclusion R q) (StandardTautological.line R 2)

def linear (q q' : PlaneQuadratic.Coefficients R) (M : (Matrix (Fin 3) (Fin 3) R)ˣ)
    (h : PlaneQuadratic.transformed R q M = PlaneQuadratic.polynomial R q') :
    PolarizedOverIso (PlaneQuadratic.projection R q') (PlaneQuadratic.projection R q)
      (line R q') (line R q) where
  iso := QuadraticLinearTransport.iso R q q' M h
  over_base := QuadraticLinearTransport.over_base R q q' M h
  lineIso := (QuadraticLinearTransport.lineIso R q q' M h).symm

theorem veronese (φ : ℂ →+* R) :
    Nonempty (PolarizedOverIso (RelativeVeroneseModel.projection φ)
      (PlaneQuadratic.projection R (QuadraticVeronese.equation R))
      (RelativeVeroneseModel.line φ) (line R (QuadraticVeronese.equation R))) := by
  obtain ⟨e, he, ⟨eL⟩⟩ := RelativeVeroneseModel.polarized_iso φ
  exact ⟨⟨e, he, eL⟩⟩

/-- The explicit constant P1 model maps to the actual quadratic whose
chosen normalizing matrix gives the sum of three squares. -/
theorem smooth_model_to_quadratic [Algebra ℂ R]
    (q : PlaneQuadratic.Coefficients R) (M : (Matrix (Fin 3) (Fin 3) R)ˣ)
    (hM : PlaneQuadratic.transformed R q M =
      PlaneQuadratic.polynomial R (PlaneQuadratic.diagonal R 1)) :
    Nonempty (PolarizedOverIso (RelativeVeroneseModel.projection (algebraMap ℂ R))
      (PlaneQuadratic.projection R q)
      (RelativeVeroneseModel.line (algebraMap ℂ R)) (line R q)) := by
  obtain ⟨v⟩ := veronese R (algebraMap ℂ R)
  have hV : PlaneQuadratic.transformed R (PlaneQuadratic.diagonal R 1)
      (ComplexQuadraticMatrix.veroneseUnit R) =
      PlaneQuadratic.polynomial R (QuadraticVeronese.equation R) :=
    ComplexQuadraticMatrix.transformed_veronese R
  let w := linear R (PlaneQuadratic.diagonal R 1) (QuadraticVeronese.equation R)
    (ComplexQuadraticMatrix.veroneseUnit R) hV
  let u := linear R q (PlaneQuadratic.diagonal R 1) M hM
  exact ⟨(v.trans w).trans u⟩

end LeBrunSalamon.QuadraticPolarizedModels
end

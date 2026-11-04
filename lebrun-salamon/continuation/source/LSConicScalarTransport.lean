import LSConicCotangentExt
import LSCotangentScalarAlgebra
import LSConicOverlapCoordinates

/-! Reciprocal-coordinate comparison with both cotangent functionals
kept abstract.  The chart-specific choices are inserted only in short
wrappers, after this generic proof has been kernel checked. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.PhaseThirty LeBrunSalamon.Skeleton
open LeBrunSalamon.Construction.Smoothing
open LeBrunSalamon.Construction.Smoothing.SourceAffineCharts
open LeBrunSalamon.Construction.Smoothing.CoordinateCharts
open LeBrunSalamon.ConicOverlapCoordinates LeBrunSalamon.CotangentScalarAlgebra

namespace LeBrunSalamon.ConicScalarTransport

theorem hom_ext_two {B T : Scheme} (f : T ⟶ Plane) [IsOpenImmersion f]
    (s : Plane ⟶ B) (sB : B ⟶ ComplexBase) (hs : s ≫ sB = planeBase)
    (t : T ⟶ B) (ht : f ≫ s = t)
    (q r : cotangentSheaf t ⟶ structureModule T)
    (h₀ : derivative q (value f 0) = derivative r (value f 0))
    (h₁ : derivative q (value f 1) = derivative r (value f 1)) : q = r := by
  apply ConicCotangentExt.hom_ext f s sB hs t ht q r
  intro i
  fin_cases i
  · exact h₀
  · exact h₁

theorem of_scaled_coordinates {B T : Scheme} (f : T ⟶ Plane) [IsOpenImmersion f]
    (s : Plane ⟶ B) (sB : B ⟶ ComplexBase) (hs : s ≫ sB = planeBase)
    (t : T ⟶ B) (ht : f ≫ s = t)
    (q r : cotangentSheaf t ⟶ structureModule T) (w : RingSections T ⊤)
    (hq₀ : derivative q (value f 0) = value f 0)
    (hq₁ : derivative q (value f 1) = -value f 1)
    (hr₀ : w * derivative r (value f 0) = value f 0)
    (hr₁ : w * derivative r (value f 1) = -value f 1) :
    q = r ≫ scalarSection w := by
  apply hom_ext_two f s sB hs t ht q (r ≫ scalarSection w)
  · exact (hq₀.trans hr₀.symm).trans (derivative_scalar r w (value f 0)).symm
  · exact (hq₁.trans hr₁.symm).trans (derivative_scalar r w (value f 1)).symm

theorem left_form {B T : Scheme} (f : T ⟶ Plane) [IsOpenImmersion f]
    (s : Plane ⟶ B) (sB : B ⟶ ComplexBase) (hs : s ≫ sB = planeBase)
    (t : T ⟶ B) (ht : f ≫ s = t)
    (q r : cotangentSheaf t ⟶ structureModule T) (w z : RingSections T ⊤)
    (hq₀ : derivative q (value f 0) = value f 0)
    (hq₁ : derivative q (value f 1) = -value f 1)
    (huw : value f 0 * w = 1) (huv : value f 0 * value f 1 = z)
    (hz : derivative r z = 0) (hw : derivative r w = -1) :
    q = r ≫ scalarSection w := by
  have hc := left_coefficients r (value f 0) (value f 1) w z huw huv hz hw
  exact of_scaled_coordinates f s sB hs t ht q r w hq₀ hq₁ hc.1 hc.2

theorem right_form {B T : Scheme} (f : T ⟶ Plane) [IsOpenImmersion f]
    (s : Plane ⟶ B) (sB : B ⟶ ComplexBase) (hs : s ≫ sB = planeBase)
    (t : T ⟶ B) (ht : f ≫ s = t)
    (q r : cotangentSheaf t ⟶ structureModule T) (w z : RingSections T ⊤)
    (hq₀ : derivative q (value f 0) = value f 0)
    (hq₁ : derivative q (value f 1) = -value f 1)
    (hvw : value f 1 * w = 1) (huv : value f 0 * value f 1 = z)
    (hz : derivative r z = 0) (hw : derivative r w = 1) :
    q = r ≫ scalarSection w := by
  have hc := right_coefficients r (value f 0) (value f 1) w z hvw huv hz hw
  exact of_scaled_coordinates f s sB hs t ht q r w hq₀ hq₁ hc.1 hc.2

end LeBrunSalamon.ConicScalarTransport
end

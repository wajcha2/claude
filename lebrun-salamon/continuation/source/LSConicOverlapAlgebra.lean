import RecompileExtensionsPart04Geometry

/-! The reciprocal-coordinate and Leibniz identities used on actual conic
chart intersections. These statements concern regular functions and the
original quotient-coordinate maps; no gluing conclusion is assumed. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.Construction.Smoothing
open LeBrunSalamon.Construction.Smoothing.CoordinateCharts

open LeBrunSalamon.Skeleton
open SourceAffineCharts

namespace LeBrunSalamon.ConicOverlapAlgebra

/-- Equal actual projective points in the two ratio charts have inverse
regular ratios, even on nonreduced test schemes. -/
theorem reciprocal_of_equal_ratios {T : Scheme} (a b : T ⟶ AffineLine)
    (h : a ≫ (ratioPoint 0).val = b ≫ (ratioPoint 1).val) :
    a.appTop parameterFunction * b.appTop parameterFunction = 1 := by
  let H := (projectiveCoordinates 1).hyperplane.sheaf
  let e : pullbackModule (a ≫ (ratioPoint 0).val) H ≅ structureModule T :=
    (Scheme.Modules.pullbackCongr h).app H ≪≫ ratioPullFrame b 1
  let s₀ := pullSection (a ≫ (ratioPoint 0).val) ((projectiveCoordinates 1).coordinate 0)
  let s₁ := pullSection (a ≫ (ratioPoint 0).val) ((projectiveCoordinates 1).coordinate 1)
  have h₀ : s₀ ≫ (ratioPullFrame a 0).hom = 𝟙 _ := by
    exact (ratioPullFrame_coordinate a 0 0).trans (if_pos rfl)
  have h₁ : s₁ ≫ (ratioPullFrame a 0).hom = scalarSection (a.appTop parameterFunction) := by
    exact (ratioPullFrame_coordinate a 0 1).trans (if_neg (by decide))
  have he₀ : s₀ ≫ e.hom = scalarSection (b.appTop parameterFunction) := by
    dsimp only [s₀, e, H]
    rw [Iso.trans_hom, Iso.app_hom, ← Category.assoc, ExternalExchangeCoherenceProof.pullSection_congr,
      ratioPullFrame_coordinate, if_neg (by decide)]
  have he₁ : s₁ ≫ e.hom = 𝟙 _ := by
    dsimp only [s₁, e, H]
    rw [Iso.trans_hom, Iso.app_hom, ← Category.assoc, ExternalExchangeCoherenceProof.pullSection_congr,
      ratioPullFrame_coordinate, if_pos rfl]
  have hs₀ : s₀ = (ratioPullFrame a 0).inv := by
    apply (cancel_mono (ratioPullFrame a 0).hom).mp
    rw [h₀, Iso.inv_hom_id]
  have hprod : scalarSection (a.appTop parameterFunction * b.appTop parameterFunction) =
      (𝟙 (structureModule T)) := by
    rw [scalarSection_mul, ← h₁, ← he₀, hs₀]
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using he₁
  have hv := congrArg sectionValue hprod
  have hid : sectionValue (𝟙 (structureModule T)) = (1 : RingSections T ⊤) := rfl
  simpa only [scalarSection, sectionFromValue_spec, hid] using hv

section Leibniz

variable {A : Type*} [CommRing A]

/-- On the left overlap the frame multiplier is w=u⁻¹. The prescribed
outer derivative D(w)=-1 gives exactly the two node coefficients. -/
theorem node_coefficients_from_left (D : A → A)
    (hD : ∀ a b, D (a * b) = a * D b + b * D a)
    (h1 : D 1 = 0) (u v w t : A)
    (huw : u * w = 1) (ht : u * v = t) (hDt : D t = 0)
    (hDw : D w = -1) : w * D u = u ∧ w * D v = -v := by
  have hu : w * D u = u := by
    have h := hD u w
    rw [huw, h1, hDw, mul_neg, mul_one] at h
    linear_combination -h
  have huv : u * D v + v * D u = 0 := by rw [← hD, ht, hDt]
  refine ⟨hu, ?_⟩
  calc
    w * D v = w * (u * w) * D v := by rw [huw, mul_one]
    _ = w * w * (u * D v + v * D u) - v * w * (w * D u) := by ring
    _ = -v := by rw [huv, hu, mul_zero, zero_sub]; rw [mul_assoc v w u, mul_comm w u, huw, mul_one]

/-- The symmetric right overlap has D(w)=1 and the same node vector
(u,-v), with no cancellation or reducedness assumption. -/
theorem node_coefficients_from_right (D : A → A)
    (hD : ∀ a b, D (a * b) = a * D b + b * D a)
    (h1 : D 1 = 0) (u v w t : A)
    (hvw : v * w = 1) (ht : u * v = t) (hDt : D t = 0)
    (hDw : D w = 1) : w * D u = u ∧ w * D v = -v := by
  have hneg : ∀ a b, -D (a * b) = a * (-D b) + b * (-D a) := by
    intro a b
    rw [hD]
    ring
  have h := node_coefficients_from_left (fun a => -D a) hneg
    (by rw [h1, neg_zero]) v u w t hvw (by simpa [mul_comm] using ht)
    (by rw [hDt, neg_zero]) (by rw [hDw])
  constructor
  · have hh := h.2
    simpa only [mul_neg, neg_inj] using hh
  · have hh := congrArg Neg.neg h.1
    simpa only [mul_neg, neg_neg] using hh

end Leibniz
end LeBrunSalamon.ConicOverlapAlgebra
end

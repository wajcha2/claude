import Mathlib

/-! Properness over a local ring promotes coverage of the actual closed
fibre to coverage of the whole source. No admitted theorem is used. -/

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace LeBrunSalamon.ProperLocalTopology

theorem open_eq_top_of_closed_point_fibre
    (R : Type) [CommRing R] [IsLocalRing R]
    {X : Scheme} (pi : X ⟶ Spec (CommRingCat.of R)) [IsProper pi]
    (U : X.Opens)
    (h : ∀ x : X, pi x = IsLocalRing.closedPoint R → x ∈ U) : U = ⊤ := by
  let W : (Spec (CommRingCat.of R)).Opens :=
    ⟨(pi '' (U : Set X)ᶜ)ᶜ,
      (pi.isClosedMap _ U.isOpen.isClosed_compl).isOpen_compl⟩
  have hclosed : IsLocalRing.closedPoint R ∈ W := by
    rintro ⟨x, hx, he⟩
    exact hx (h x he)
  have hW : W = ⊤ := (IsLocalRing.closedPoint_mem_iff W).mp hclosed
  apply top_unique
  intro x hx
  by_contra hxU
  have hxW : pi x ∈ W := by rw [hW]; trivial
  exact hxW ⟨x, hxU, rfl⟩

/-- The fibre is the actual categorical pullback, not merely a chosen
collection of closed points. Existence of pullback points is supplied
by the scheme pullback theorem. -/
theorem open_eq_top_of_closed_fibre
    (R : Type) [CommRing R] [IsLocalRing R]
    {X T : Scheme} (pi : X ⟶ Spec (CommRingCat.of R)) [IsProper pi]
    (s : T ⟶ Spec (CommRingCat.of R))
    (t : T) (ht : s t = IsLocalRing.closedPoint R)
    (U : X.Opens) (h : Set.range (pullback.fst pi s) ⊆ U) : U = ⊤ := by
  apply open_eq_top_of_closed_point_fibre R pi U
  intro x hx
  obtain ⟨z, hz, _⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := pi) (g := s) x t (hx.trans ht.symm)
  exact h ⟨z, hz⟩

end LeBrunSalamon.ProperLocalTopology

end

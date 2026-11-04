import Mathlib

/-!
Global sections and the closed-point stalk on a local affine base.
The sole topological fact is that every open neighbourhood of the closed
point is the whole spectrum. Germ representatives then give the actual
global-to-stalk bijection. This records the local affine normalization
used when reading a cohomology/base-change statement in stalk notation.

There is no admission in this file. Off-graph native candidate.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace LeBrunSalamon.LocalBaseSections

/-- If the only neighbourhood of a point is the whole space, the actual
germ map from global sections of an additive presheaf is bijective. -/
theorem global_germ_bijective {X : TopCat} (F : X.Presheaf AddCommGrpCat)
    (x : X) (hx : ∀ U : TopologicalSpace.Opens X, x ∈ U → U = ⊤) :
    Function.Bijective (F.Γgerm x) := by
  constructor
  · intro a b hab
    obtain ⟨U, hU, i, j, h⟩ := F.germ_eq x trivial trivial a b hab
    have htop : U = ⊤ := hx U hU
    subst U
    have hi : i = 𝟙 (⊤ : TopologicalSpace.Opens X) := Subsingleton.elim _ _
    have hj : j = 𝟙 (⊤ : TopologicalSpace.Opens X) := Subsingleton.elim _ _
    simpa [hi, hj] using h
  · intro a
    obtain ⟨U, hU, b, hb⟩ := F.exists_germ_eq a
    have htop : U = ⊤ := hx U hU
    subst U
    exact ⟨b, hb⟩

/-- The actual ring-valued global germ map has the same normalization. -/
theorem global_ring_germ_bijective {X : TopCat} (F : X.Presheaf CommRingCat)
    (x : X) (hx : ∀ U : TopologicalSpace.Opens X, x ∈ U → U = ⊤) :
    Function.Bijective (F.Γgerm x) := by
  constructor
  · intro a b hab
    obtain ⟨U, hU, i, j, h⟩ := F.germ_eq x trivial trivial a b hab
    have htop : U = ⊤ := hx U hU
    subst U
    have hi : i = 𝟙 (⊤ : TopologicalSpace.Opens X) := Subsingleton.elim _ _
    have hj : j = 𝟙 (⊤ : TopologicalSpace.Opens X) := Subsingleton.elim _ _
    simpa [hi, hj] using h
  · intro a
    obtain ⟨U, hU, b, hb⟩ := F.exists_germ_eq a
    have htop : U = ⊤ := hx U hU
    subst U
    exact ⟨b, hb⟩

/-- On a literal local affine base, the additive global-to-stalk map is
bijective, without a quasi-coherence assumption or a new source input. -/
theorem closedPoint_global_germ_bijective (R : Type) [CommRing R] [IsLocalRing R]
    (F : (Spec (CommRingCat.of R)).carrier.Presheaf AddCommGrpCat) :
    Function.Bijective (F.Γgerm (IsLocalRing.closedPoint R)) :=
  global_germ_bijective F (IsLocalRing.closedPoint R)
    (fun U hU => (IsLocalRing.closedPoint_mem_iff U).mp hU)

/-- The actual closed-point ring germ is likewise bijective. -/
theorem closedPoint_global_ring_germ_bijective (R : Type)
    [CommRing R] [IsLocalRing R] :
    Function.Bijective
      ((Spec (CommRingCat.of R)).presheaf.Γgerm (IsLocalRing.closedPoint R)) :=
  global_ring_germ_bijective (Spec (CommRingCat.of R)).presheaf
    (IsLocalRing.closedPoint R)
    (fun U hU => (IsLocalRing.closedPoint_mem_iff U).mp hU)

end LeBrunSalamon.LocalBaseSections

end

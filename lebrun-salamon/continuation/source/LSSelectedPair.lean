import LSSuitableLinear

/-!
## From spanning actual directions to nonorthogonal actual line maps

SOURCE: the opening selection step of `lines:suitable-pair`.

The spanning hypothesis is imposed on the union of the selected directions.
The resulting witnesses are the original free curves and their canonical
node differentials. This gives a nonempty nonorthogonality locus, not yet a
point where the derivative of addition is surjective. The latter must be
obtained by the manuscript's cone dominance and generic-smoothness steps.

STATUS: new source; compilation deferred by the 35,000-line gate.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySeven
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.Skeleton

namespace LeBrunSalamon.Construction.Lines.SelectedPair

open DirectionCones SuitablePairAlgebra

/-- The original Levi test, named once so generated record declarations
refer to a small application instead of duplicating its dependent fiber terms.
This predicate is definitionally the same test used by `SuitablePair`. -/
def nodePairNonorthogonal {n : ℕ} {X : ContactFanoManifold n}
    (x : ComplexPoint X.variety) (f g : FreeLine X)
    (hf : marking.map ≫ f.curve.map = x.map)
    (hg : marking.map ≫ g.curve.map = x.map)
    (p q : Fiber (tangentSheaf P.structureMap) marking.map) : Prop :=
  NonzeroLeviPair X x (nodeDifferential (X := X) f x hf p)
    (nodeDifferential (X := X) g x hg q)

set_option genInjectivity false in
set_option genSizeOf false in
/-- A witnessed pair in the nonorthogonal locus of the selected family.
This is deliberately weaker than `SuitablePair`: complementarity of its
positive spaces is a theorem still to be established at a suitable point. -/
structure NonorthogonalPairAt {n : ℕ} (X : ContactFanoManifold n)
    (H : FreeLine X → Prop) (x : ComplexPoint X.variety) where
  first : FreeLine X
  second : FreeLine X
  first_selected : H first
  second_selected : H second
  first_at : marking.map ≫ first.curve.map = x.map
  second_at : marking.map ≫ second.curve.map = x.map
  first_parameter : Fiber (tangentSheaf P.structureMap) marking.map
  second_parameter : Fiber (tangentSheaf P.structureMap) marking.map
  nonorthogonal : nodePairNonorthogonal x first second first_at second_at
    first_parameter second_parameter

theorem NonorthogonalPairAt.first_parameter_ne_zero {n : ℕ}
    {X : ContactFanoManifold n} {H : FreeLine X → Prop} {x : ComplexPoint X.variety}
    (D : NonorthogonalPairAt X H x) : D.first_parameter ≠ 0 := by
  intro h
  apply nonzeroLeviPair_left_ne_zero X x D.nonorthogonal
  rw [h, map_zero]

theorem NonorthogonalPairAt.second_parameter_ne_zero {n : ℕ}
    {X : ContactFanoManifold n} {H : FreeLine X → Prop} {x : ComplexPoint X.variety}
    (D : NonorthogonalPairAt X H x) : D.second_parameter ≠ 0 := by
  intro h
  apply nonzeroLeviPair_right_ne_zero X x D.nonorthogonal
  rw [h, map_zero]

/-- The linear-span argument actually returns two curve maps. Nonzero
directions are lifted using their defining canonical differential values. -/
theorem nonorthogonalPair_exists_of_selected_spanning {n : ℕ}
    (X : ContactFanoManifold n) (H : FreeLine X → Prop) (x : ComplexPoint X.variety)
    (hlevi : contactLevi X x ≠ 0)
    (hspan : Submodule.span ℂ (projectiveCone (selectedDirections H x)) = ⊤) :
    Nonempty (NonorthogonalPairAt X H x) := by
  obtain ⟨a, ha, b, hb, hab⟩ := exists_nonorthogonal_generators
    (contactLevi X x) hlevi (projectiveCone (selectedDirections H x))
    (projectiveCone (selectedDirections H x)) hspan hspan
  have ha0 := nonorthogonal_left_ne_zero (contactLevi X x) hab
  have hb0 := nonorthogonal_right_ne_zero (contactLevi X x) hab
  obtain ⟨f, hf, hfx, p, hp⟩ := (selectedCone_nonzero_iff H x a ha0).mp ha
  obtain ⟨g, hg, hgx, q, hq⟩ := (selectedCone_nonzero_iff H x b hb0).mp hb
  have htrans : NonzeroLeviPair X x
      (nodeDifferential f x hfx p) (nodeDifferential g x hgx q) := by
    rw [hp, hq]
    exact (nonzeroLeviPair_iff_contactLevi X x a b).mpr hab
  exact ⟨{
    first := f
    second := g
    first_selected := hf
    second_selected := hg
    first_at := hfx
    second_at := hgx
    first_parameter := p
    second_parameter := q
    nonorthogonal := htrans }⟩

/-- For a genuine projective realization, spanning the union of component
cones suffices. No claim about the span of any one component is introduced. -/
theorem selected_spanning_of_component_union {n : ℕ}
    (X : ContactFanoManifold n) (H : FreeLine X → Prop) (x : ComplexPoint X.variety)
    {N : ℕ} (e : contactPlane X x ≃ₗ[ℂ] (Fin (N+1) → ℂ))
    (D : ReducedProjectiveDirections N) (hD : RealizesSelectedDirections H x e D)
    (hspan : Submodule.span ℂ
      (⋃ C : D.Component, projectiveCone (D.componentDirections e C)) = ⊤) :
    Submodule.span ℂ (projectiveCone (selectedDirections H x)) = ⊤ := by
  apply top_unique
  rw [← hspan]
  apply Submodule.span_mono
  intro v hv
  obtain ⟨C, hC⟩ := Set.mem_iUnion.mp hv
  apply projectiveCone_mono (fun d hd => ?_) hC
  rw [← hD]
  exact D.componentDirections_subset e C hd

theorem nonorthogonalPair_exists_of_component_union {n : ℕ}
    (X : ContactFanoManifold n) (H : FreeLine X → Prop) (x : ComplexPoint X.variety)
    {N : ℕ} (e : contactPlane X x ≃ₗ[ℂ] (Fin (N+1) → ℂ))
    (D : ReducedProjectiveDirections N) (hD : RealizesSelectedDirections H x e D)
    (hlevi : contactLevi X x ≠ 0)
    (hspan : Submodule.span ℂ
      (⋃ C : D.Component, projectiveCone (D.componentDirections e C)) = ⊤) :
    Nonempty (NonorthogonalPairAt X H x) :=
  nonorthogonalPair_exists_of_selected_spanning X H x hlevi
    (selected_spanning_of_component_union X H x e D hD hspan)

/-- At a point where the actual derivative-sum comparison is available,
the same witnessed curves and parameters give the original suitable pair.
This does not assert that an arbitrary nonorthogonal pair is such a point. -/
def NonorthogonalPairAt.toSuitablePair {n : ℕ}
    {X : ContactFanoManifold n} {H : FreeLine X → Prop} {x : ComplexPoint X.variety}
    (D : NonorthogonalPairAt X H x)
    {A B : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    (d₁ : A →ₗ[ℂ] contactPlane X x) (d₂ : B →ₗ[ℂ] contactPlane X x)
    (h₁ : ∀ a, (d₁ a : TangentFiber X.variety x) ∈ positiveNodeSpace D.first x D.first_at)
    (h₂ : ∀ b, (d₂ b : TangentFiber X.variety x) ∈ positiveNodeSpace D.second x D.second_at)
    (hsurj : Function.Surjective (d₁.coprod d₂)) : SuitablePair X :=
  suitablePair_of_surjective_variation x D.first D.second D.first_at D.second_at
    D.first_parameter D.second_parameter D.nonorthogonal d₁ d₂ h₁ h₂ hsurj

end LeBrunSalamon.Construction.Lines.SelectedPair

end

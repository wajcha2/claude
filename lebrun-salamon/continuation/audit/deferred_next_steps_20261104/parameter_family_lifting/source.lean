import LSRelativeHomFunctorTranslationProbe

/-! The lifting condition of an actual represented relative Hom functor.
This is a categorical comparison on all test schemes; it assumes no
smoothness, Artinian, cohomology, or representability existence theorem. -/

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.RelativeMorphismsFunctorPrototype

namespace LeBrunSalamon.Next3i.RelativeHomLifting

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Parameter lifts are exactly lifts of the actual associated source family.
The compatibility equation uses the literal source base-change morphism. -/
theorem lift_iff_family {S Y Z : Scheme} (pi : Y ⟶ S) (q : Z ⟶ S)
    (H : Over S) (R : (morphismFunctor pi q).RepresentableBy H)
    {T₀ T : Over S} (i : T₀ ⟶ T) (f₀ : T₀ ⟶ H) :
    (∃ f : T ⟶ H, i ≫ f = f₀) ↔
      ∃ g : sourceOver pi T ⟶ Over.mk q,
        sourceMapOver pi i ≫ g = R.homEquiv f₀ := by
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨R.homEquiv f, ?_⟩
    have h := R.homEquiv_comp i f
    change R.homEquiv (i ≫ f) = sourceMapOver pi i ≫ R.homEquiv f at h
    rw [hf] at h
    exact h.symm
  · rintro ⟨g, hg⟩
    refine ⟨R.homEquiv.symm g, ?_⟩
    apply R.homEquiv.injective
    rw [R.homEquiv_comp]
    change sourceMapOver pi i ≫ R.homEquiv (R.homEquiv.symm g) = R.homEquiv f₀
    rw [R.homEquiv.apply_symm_apply]
    exact hg

end LeBrunSalamon.Next3i.RelativeHomLifting

#print axioms LeBrunSalamon.Next3i.RelativeHomLifting.lift_iff_family

end

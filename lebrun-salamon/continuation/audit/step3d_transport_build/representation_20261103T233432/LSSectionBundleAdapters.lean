import LSSectionRepresentability
import RecompileExtensionsPart04Geometry

/-! Exact historical public-type adapters for the generic section functor.
These checks use the frozen project interface; full current replay is separate. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.Skeleton
open LeBrunSalamon.Construction

namespace LeBrunSalamon.SectionBundleAdapters

theorem totalLine_exists {Z : Scheme} (L : LineBundle Z) :
    Nonempty (Descent.TotalLine L) := by
  obtain ⟨V, p, τ, hV⟩ :=
    SectionRepresentability.represented_section_data L.locallyFree
  exact ⟨{ space := V, projection := p, tautological := τ, universal := hV }⟩

theorem totalBundle_representation {Z : Scheme} {r : ℕ} (E : AlgebraicVectorBundle Z r) :
    ∃ (V : Scheme) (bundleProjection : V ⟶ Z)
      (τ : AlgebraicSection (pullbackModule bundleProjection E.sheaf)),
      ∀ (T : Scheme) (f : T ⟶ Z),
        Function.Bijective (fun h : {h : T ⟶ V // h ≫ bundleProjection = f} =>
          pullSection h.val τ ≫
            (compositionPullback h.val bundleProjection f h.property E.sheaf).hom) :=
  SectionRepresentability.represented_section_data E.locallyFree

theorem totalBundle_exists {Z : Scheme} {r : ℕ} (E : AlgebraicVectorBundle Z r) :
    Nonempty (Normalization.TotalBundle E) := by
  obtain ⟨V, p, τ, hV⟩ := totalBundle_representation E
  exact ⟨{ space := V, projection := p, tautological := τ, universal := hV }⟩

end LeBrunSalamon.SectionBundleAdapters

end

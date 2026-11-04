import LSConicCotangentTools

/-! Coordinate extensionality after an actual open affine-plane chart.
The generic lemma removes repeated large scheme-level transport expressions
from the two conic overlap calculations. No admission. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.PhaseThirty LeBrunSalamon.Skeleton
open LeBrunSalamon.Construction.Smoothing
open LeBrunSalamon.Construction.Smoothing.SourceAffineCharts

namespace LeBrunSalamon.ConicCotangentExt

/-- The original two coordinate differentials determine a morphism out of
the relative cotangent sheaf on any open subscheme of the affine plane. -/
theorem hom_ext {B T : Scheme} (f : T ⟶ Plane) [IsOpenImmersion f]
    (s : Plane ⟶ B) (sB : B ⟶ ComplexBase) (hs : s ≫ sB = planeBase)
    (t : T ⟶ B) (ht : f ≫ s = t) {E : OModule T}
    (q r : cotangentSheaf t ⟶ E)
    (h : ∀ i : Fin 2,
      q.app ⊤ ((cotangentPresentation t).differential.apply ⊤
        (f.appTop (planeFunction (MvPolynomial.X i)))) =
      r.app ⊤ ((cotangentPresentation t).differential.apply ⊤
        (f.appTop (planeFunction (MvPolynomial.X i))))) : q = r := by
  subst t
  letI := openImmersion_cotangentMap_isIso f s
  apply (cancel_epi (cotangentMap f s)).mp
  apply Construction.ConicModelSections.plane_pulledCotangent_hom_ext s sB hs f
  intro i
  change q.app (f ⁻¹ᵁ ⊤)
      ((cotangentMap f s).app (f ⁻¹ᵁ ⊤)
        (pullLocalSection f (cotangentSheaf s) ⊤
          ((cotangentPresentation s).differential.apply ⊤
            (planeFunction (MvPolynomial.X i))))) =
    r.app (f ⁻¹ᵁ ⊤)
      ((cotangentMap f s).app (f ⁻¹ᵁ ⊤)
        (pullLocalSection f (cotangentSheaf s) ⊤
          ((cotangentPresentation s).differential.apply ⊤
            (planeFunction (MvPolynomial.X i)))))
  rw [ContactDerivativeIsoProof.cotangentMap_differential]
  exact h i

end LeBrunSalamon.ConicCotangentExt
end

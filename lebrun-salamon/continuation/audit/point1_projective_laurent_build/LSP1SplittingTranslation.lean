import RecompileExtensionCore

/-! Generic splitting into invertible sheaves, followed by the proved
translation into the project's marked-point integer-twist convention.
The Picard-classification prerequisite is audited separately.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseEighteen
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseThirtyTwo

namespace LeBrunSalamon.PublishedInputs.ProjectiveLine

/-- Birkhoff--Grothendieck, in its algebraic direct-sum-of-invertible-sheaves
form. Primary reference: Hazewinkel--Martin, Journal of Pure and Applied
Algebra 25 (1982), 207--211, Theorem 4.1 on p.211.
The theorem is over an arbitrary field; it does not use the project's
marked point, splitting profile, or O(d) construction.
-/
theorem splitsIntoInvertibleSheaves (k : Type) [Field k]
    (r : ℕ) (E : (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).Modules)
    (hE : IsLocallyFreeOfRank E r) :
    ∃ L : Fin r → (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).Modules,
      (∀ i, IsLocallyFreeOfRank (L i) 1) ∧ Nonempty (E ≅ ∐ L) := by
  sorry

end LeBrunSalamon.PublishedInputs.ProjectiveLine

namespace LeBrunSalamon.P1SplittingTranslation

/-- Choose the degree of each actual invertible summand, then transport the
finite coproduct through the component isomorphisms. No realization of the
project splitting profile is assumed by the generic published theorem.
-/
theorem birkhoffGrothendieck (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) {r : ℕ}
    (E : AlgebraicVectorBundle ProjectiveLine r) :
    ∃ a : TangentSplittingProfile r, RealizesSplitting P p E a := by
  obtain ⟨L, hL, ⟨e⟩⟩ :=
    PublishedInputs.ProjectiveLine.splitsIntoInvertibleSheaves ℂ r E.sheaf E.locallyFree
  have hi (i : Fin r) :
      ∃ d : ℤ, Nonempty (L i ≅ (projectiveTwist P p d).sheaf) :=
    (projectiveLineBundle_classification P p ⟨L i, hL i⟩).exists
  choose d hd using hi
  refine ⟨⟨d⟩, ?_⟩
  exact ⟨e ≪≫ Sigma.mapIso (fun i => Classical.choice (hd i))⟩

end LeBrunSalamon.P1SplittingTranslation

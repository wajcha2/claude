import LSPolarizedEmbeddingLift
import LSStandardProjectiveSmooth
import LSRelativeCartier
import LSResidueFieldPresentation

/-! Supply the geometric hypotheses of the relative Cartier criterion
for the actual lifted plane embedding.  Flatness, finite presentation,
properness and the literal residue-field square are all instantiated
here.  No additional family hypothesis or admission is introduced. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight

namespace LeBrunSalamon.PlaneEmbeddingCartier

theorem of_closed_fibre
    (R K : Type) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [Field K]
    (φ : R →+* K) [IsLocalHom φ] (hφ : Function.Surjective φ)
    {X : Scheme.{0}} (pi : X ⟶ Spec (CommRingCat.of R)) [Flat pi]
    (L : LineBundle X) (f : PolarizedProjectiveEmbedding R 2 X pi L)
    (j : PolarizedProjectiveEmbedding K 2
      (pullback pi (StandardProjectiveBaseChange.base φ))
      (pullback.snd pi (StandardProjectiveBaseChange.base φ))
      (pullbackLine (pullback.fst pi (StandardProjectiveBaseChange.base φ)) L))
    (hcompare : j.hom ≫ StandardProjectiveBaseChange.map φ 2 =
      pullback.fst pi (StandardProjectiveBaseChange.base φ) ≫ f.hom)
    (h0 : IsLocallyFreeOfRank (EffectiveCartier.ideal j.hom) 1) :
    IsLocallyFreeOfRank (EffectiveCartier.ideal f.hom) 1 := by
  let p := StandardTautological.toSpec R 2
  let b := StandardProjectiveBaseChange.map φ 2
  let q := StandardTautological.toSpec K 2
  let a := pullback.fst pi (StandardProjectiveBaseChange.base φ)
  letI : IsProper p := StandardProjectiveProper.proper R 2
  letI : Flat p := StandardProjectiveSmooth.flat R 2
  letI : LocallyOfFinitePresentation p := StandardProjectiveSmooth.locallyOfFinitePresentation R 2
  letI : IsLocallyNoetherian (StandardTautological.space R 2) :=
    LocallyOfFiniteType.isLocallyNoetherian p
  letI : IsClosedImmersion f.hom := f.closed
  letI : LocallyOfFinitePresentation f.hom := inferInstance
  letI : Flat (f.hom ≫ p) := by rw [f.over_base]; infer_instance
  have hsq := PolarizedEmbeddingLift.cartesian_of_comparison R K φ pi 2 L f j hcompare
  have hres := ResidueFieldPresentation.pullback_residue p b q φ hφ
    (StandardProjectiveBaseChange.isPullback φ 2)
  exact RelativeCartier.of_closed_fibre R p f.hom b
    (q ≫ (ResidueFieldPresentation.specIso φ hφ).hom) hres a j.hom hsq h0

end LeBrunSalamon.PlaneEmbeddingCartier
end

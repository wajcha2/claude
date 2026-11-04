import RecompileExtensionsPart01

/-!
# Independent projectivity and formal-trait definitions

These three declarations are extracted verbatim from LSStableMapFamily.
They use only the accepted early projective-scheme vocabulary and the
complex power-series trait, with no stable-map family construction.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseSeven LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentySix LeBrunSalamon.PhaseTwentySeven
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseTwentyNine
open LeBrunSalamon.PhaseThirty LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.PhaseThirtyFour LeBrunSalamon.Skeleton

namespace LeBrunSalamon.Construction.StableMaps

/-- Relative projectivity expressed by actual closed embeddings after
every affine base restriction. This is sufficient in particular after
pullback to any trait whose closed point lies in the chosen affine. -/
def IsProjectiveOver {C B : Scheme} (pi : C ⟶ B)
    (sB : B ⟶ ComplexBase) : Prop :=
  ∀ U : B.Opens, IsAffineOpen U →
    ∃ N : ℕ,
      ∃ j : pullback pi U.ι ⟶ pullback (projectiveBaseMap N) (U.ι ≫ sB),
        IsClosedImmersion j ∧
          j ≫ pullback.snd (projectiveBaseMap N) (U.ι ≫ sB) = pullback.snd pi U.ι

namespace FormalArcs

/-- A complete trait with actual complex coefficient and residue maps. -/
abbrev Trait : Scheme := Spec (CommRingCat.of (PowerSeries ℂ))

def toC : Trait ⟶ ComplexBase :=
  Spec.map (CommRingCat.ofHom (PowerSeries.C : ℂ →+* PowerSeries ℂ))

end FormalArcs

end LeBrunSalamon.Construction.StableMaps

end

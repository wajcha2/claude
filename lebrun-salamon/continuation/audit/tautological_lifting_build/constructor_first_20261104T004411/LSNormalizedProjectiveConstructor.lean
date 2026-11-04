import RecompileExtensionsPart01
import LSStandardTautological

/-!
Candidate project-facing constructor, retaining the public record type but
selecting its line, sections and frames from the same normalized generic
tautological data.  After native checking, this constructor body can replace
the current public choice, and these accessors can be transferred verbatim.
This file introduces no admitted theorem and remains outside source/.
-/

noncomputable section
set_option autoImplicit false
set_option maxErrors 1
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.Core LeBrunSalamon.Skeleton

namespace LeBrunSalamon.NormalizedProjectiveCoordinates

/-- Generic projection: the old unnormalized universal statement follows
from the standard construction, so its old admission can be removed. -/
theorem universalInvertibleQuotient (R : Type) [CommRing R] (N : ℕ) :
    ∃ (L : (ProjectiveQuotient.space R N).Modules), IsLocallyFreeOfRank L 1 ∧
      ∃ a : Fin (N + 1) → (structureModule (ProjectiveQuotient.space R N) ⟶ L),
        Epi (Sigma.desc a) ∧
        ∀ (T : Scheme) (s : T ⟶ Spec (CommRingCat.of R))
          (F : T.Modules), IsLocallyFreeOfRank F 1 →
          ∀ b : Fin (N + 1) → (structureModule T ⟶ F),
            Epi (Sigma.desc b) →
            ∃! f : {f : T ⟶ ProjectiveQuotient.space R N //
                f ≫ ProjectiveQuotient.toSpec R N = s},
              ∃ e : pullbackModule f.val L ≅ F,
                ∀ i, pullSection f.val (a i) ≫ e.hom = b i := by
  let d := StandardTautological.chosen R N
  refine ⟨d.sheaf, d.locallyFree, d.coordinate, d.generates, ?_⟩
  exact d.universal

/-- Explicit normalized constructor; this replaces the public choice of an
arbitrary inhabitant, not merely the proof that an inhabitant exists. -/
def coordinates (N : ℕ) : ProjectiveCoordinates N where
  hyperplane := StandardTautological.line ℂ N
  coordinate := StandardTautological.coordinate ℂ N
  generates := StandardTautological.generates ℂ N
  universal := by
    intro T s F b hb
    have hmap := (StandardTautological.chosen ℂ N).universal T s F.sheaf F.locallyFree b hb
    simpa only [PointsOver, StandardTautological.toSpec, StandardTautological.constants,
      StandardTautological.space, StandardTautological.grading, projectiveBaseMap,
      constantsToDegreeZero] using hmap

def coordinateFrame (N : ℕ) (i : Fin (N + 1)) :
    LocalFrames.OverFrame (coordinates N).hyperplane.sheaf
      (StandardTautological.chart ℂ N i) :=
  StandardTautological.frame ℂ N i

theorem coordinateFrame_coefficient (N : ℕ) (i j : Fin (N + 1)) :
    LocalFrames.coordinates (coordinateFrame N i)
      (Scheme.Modules.Hom.app ((coordinates N).coordinate j)
        (StandardTautological.chart ℂ N i)
        (1 : RingSections (ComplexProjectiveSpace N)
          (StandardTautological.chart ℂ N i))) =
      StandardTautological.ratioSection ℂ N i j :=
  StandardTautological.section_coordinates ℂ N i j

end LeBrunSalamon.NormalizedProjectiveCoordinates

end

import LSStableMapFamily
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# Reduction of the whole member-comparison cover

The reduction is the actual closed subscheme cut out by the nilradical.
Its inclusion is surjective on points, finite, and proper.  In particular,
reducing a member-comparison cover retains every point of the entire
source square, including its diagonal.  No smooth-locus restriction is
made in this construction.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.Skeleton

namespace LeBrunSalamon.Construction.SchemeReduction

/-- The actual scheme defined by the nilradical ideal sheaf. -/
abbrev obj (Y : Scheme) : Scheme := Y.nilradical.subscheme

/-- The canonical closed immersion from the reduction. -/
abbrev ι (Y : Scheme) : obj Y ⟶ Y := Y.nilradical.subschemeι

instance isReduced (Y : Scheme) : IsReduced (obj Y) := by
  letI (U : Y.affineOpens) :
      _root_.IsReduced (Γ(Y, U) ⧸ Y.nilradical.ideal U) :=
    (Ideal.isRadical_iff_quotient_reduced _).mp (by
      change (⊥ : Ideal Γ(Y, U)).radical.IsRadical
      exact Ideal.radical_isRadical _)
  letI (U : Y.affineOpens) :
      IsReduced (Y.nilradical.subschemeCover.openCover.X U) := by
    change IsReduced (Spec (CommRingCat.of (Γ(Y, U) ⧸ Y.nilradical.ideal U)))
    infer_instance
  exact IsReduced.of_openCover _ Y.nilradical.subschemeCover.openCover

instance inclusion_isClosedImmersion (Y : Scheme) : IsClosedImmersion (ι Y) := by
  change IsClosedImmersion Y.nilradical.subschemeι
  infer_instance

instance inclusion_surjective (Y : Scheme) : Surjective (ι Y) := by
  constructor
  apply Set.range_eq_univ.mp
  change Set.range Y.nilradical.subschemeι = Set.univ
  rw [Y.nilradical.range_subschemeι, Scheme.support_nilradical]
  rfl

instance inclusion_isFinite (Y : Scheme) : IsFinite (ι Y) := by
  infer_instance

instance inclusion_isProper (Y : Scheme) : IsProper (ι Y) := by
  infer_instance

theorem inclusion_function_surjective (Y : Scheme) : Function.Surjective (ι Y) :=
  (ι Y).surjective

/-- Finite type is inherited by passing to the reduction of the source. -/
theorem locallyOfFiniteType_toBase {Y S : Scheme} (s : Y ⟶ S)
    [LocallyOfFiniteType s] : LocallyOfFiniteType (ι Y ≫ s) := by
  infer_instance

theorem proper_toBase {Y S : Scheme} (s : Y ⟶ S)
    [IsProper s] : IsProper (ι Y ≫ s) := by
  infer_instance

end LeBrunSalamon.Construction.SchemeReduction

namespace LeBrunSalamon.Construction.StableMaps.FullHomComparison

variable {P : ProjectiveLineOverC} {p : ProjectiveLinePoint P}
variable {d : ℕ} {X : SmoothProperComplexVariety d}
variable {H : HomSpacePresentation P X} {U : H.parameter.Opens}
variable {L : LineBundle X.scheme} {degree : ℕ}
variable {F : ProjectiveNodalFamily P p X L degree}
variable (Q : FullHomComparison P p X H U L degree F)
variable (t : PointsOver ComplexBase (𝟙 ComplexBase) U.toScheme (U.ι ≫ H.toC))

/-- A reduced comparison cover of the entire source square of `t`. -/
abbrev ReducedMemberCover : Scheme := SchemeReduction.obj (Q.MemberCover t)

abbrev reducedMemberInclusion : Q.ReducedMemberCover t ⟶ Q.MemberCover t :=
  SchemeReduction.ι (Q.MemberCover t)

def reducedMemberToSquare : Q.ReducedMemberCover t ⟶ SelfProduct P.structureMap :=
  Q.reducedMemberInclusion t ≫ Q.memberToSquare t

def reducedMemberToC : Q.ReducedMemberCover t ⟶ ComplexBase :=
  Q.reducedMemberToSquare t ≫ firstProjection P.structureMap ≫ P.structureMap

theorem reducedMemberCover_reduced : IsReduced (Q.ReducedMemberCover t) := by
  infer_instance

theorem reducedMemberInclusion_closed : IsClosedImmersion (Q.reducedMemberInclusion t) := by
  infer_instance

theorem reducedMemberInclusion_proper : IsProper (Q.reducedMemberInclusion t) := by
  infer_instance

theorem reducedMemberInclusion_surjective :
    Function.Surjective (Q.reducedMemberInclusion t) :=
  (Q.reducedMemberInclusion t).surjective

theorem reducedMemberToSquare_finite : IsFinite (Q.reducedMemberToSquare t) := by
  letI : IsFinite (Q.memberToSquare t) := Q.memberToSquare_finite t
  dsimp only [reducedMemberToSquare]
  infer_instance

theorem reducedMemberToSquare_proper : IsProper (Q.reducedMemberToSquare t) := by
  letI : IsFinite (Q.reducedMemberToSquare t) := Q.reducedMemberToSquare_finite t
  infer_instance

theorem reducedMemberToSquare_surjective :
    Function.Surjective (Q.reducedMemberToSquare t) := by
  letI : Surjective (Q.memberToSquare t) := ⟨Q.memberToSquare_surjective t⟩
  change Function.Surjective (Q.reducedMemberInclusion t ≫ Q.memberToSquare t)
  exact (Q.reducedMemberInclusion t ≫ Q.memberToSquare t).surjective

theorem reducedMemberToC_proper : IsProper (Q.reducedMemberToC t) := by
  letI : IsProper P.structureMap := ProjectiveLineProof.structureMap_proper P
  letI : IsProper (Q.reducedMemberToSquare t) := Q.reducedMemberToSquare_proper t
  dsimp only [reducedMemberToC, firstProjection]
  infer_instance

theorem reducedMemberToC_locallyOfFiniteType :
    LocallyOfFiniteType (Q.reducedMemberToC t) := by
  letI : IsProper (Q.reducedMemberToC t) := Q.reducedMemberToC_proper t
  infer_instance

end LeBrunSalamon.Construction.StableMaps.FullHomComparison

end

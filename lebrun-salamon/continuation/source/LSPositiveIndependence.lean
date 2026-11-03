import LSPositiveHom
import LSPositiveSplit

/-!
## Independence of the actual positive subbundle

SOURCE: `lines:positive`, the mutual-containment argument for two
nonnegative splittings. The composites into the opposite zero quotients
vanish by the already proved degree obstruction. The constructed
retractions then give inverse comparisons commuting with the actual
inclusions in the original sheaf. Thus the statement concerns the same
subbundle of that sheaf, not just an abstract isomorphism of bundles.

The comparison is unique over the ambient sheaf and satisfies the
cocycle identity. Different marked points defining the twists and
different profile lengths are allowed. No new admission is introduced.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseEighteen LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentySix LeBrunSalamon.PhaseTwentySeven
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction

namespace LeBrunSalamon.Construction.Lines.PositivePart

/-- The positive part of one splitting has zero image in the degree-zero
quotient of any other splitting of the same actual sheaf. -/
theorem positiveInclusion_otherZeroProjection
    (P : ProjectiveLineOverC) (p q : ProjectiveLinePoint P)
    {r s : ℕ} (a : TangentSplittingProfile r) (b : TangentSplittingProfile s)
    {E : OModule ProjectiveLine}
    (e : E ≅ splitSheaf P p a) (f : E ≅ splitSheaf P q b) :
    positiveInclusion P p a e ≫ zeroProjection P q b f = 0 := by
  classical
  exact PositiveHom.hom_positiveCoproduct_eq_zero_of_trivialization P p q
    (fun j : PositiveIndex a => a.degree j.val) (fun j => j.property)
    (zeroTrivialization P q b) _

/-- The comparison is the original inclusion followed by the other
splitting's retraction. Its construction uses no choice of factorization. -/
def positiveComparison
    (P : ProjectiveLineOverC) (p q : ProjectiveLinePoint P)
    {r s : ℕ} (a : TangentSplittingProfile r) (b : TangentSplittingProfile s)
    {E : OModule ProjectiveLine}
    (e : E ≅ splitSheaf P p a) (f : E ≅ splitSheaf P q b) :
    positiveSheaf P p a ⟶ positiveSheaf P q b :=
  positiveInclusion P p a e ≫ positiveRetraction P q b f

/-- Mutual containment, with the actual inclusion in E as its equality. -/
theorem positiveComparison_inclusion
    (P : ProjectiveLineOverC) (p q : ProjectiveLinePoint P)
    {r s : ℕ} (a : TangentSplittingProfile r) (b : TangentSplittingProfile s)
    {E : OModule ProjectiveLine}
    (e : E ≅ splitSheaf P p a) (f : E ≅ splitSheaf P q b) (hb : b.IsFree) :
    positiveComparison P p q a b e f ≫ positiveInclusion P q b f =
      positiveInclusion P p a e := by
  exact PositiveHom.factor_through_split_inclusion
    (positiveInclusion P p a e) (positiveInclusion P q b f)
    (positiveRetraction P q b f) (zeroProjection P q b f) (zeroSection P q b f)
    (split_total P q b f hb) (positiveInclusion_otherZeroProjection P p q a b e f)

/-- A comparison commuting with the original inclusions is uniquely
determined. This is stronger than merely choosing an abstract iso. -/
theorem positiveComparison_unique
    (P : ProjectiveLineOverC) (p q : ProjectiveLinePoint P)
    {r s : ℕ} (a : TangentSplittingProfile r) (b : TangentSplittingProfile s)
    {E : OModule ProjectiveLine}
    (e : E ≅ splitSheaf P p a) (f : E ≅ splitSheaf P q b)
    (g : positiveSheaf P p a ⟶ positiveSheaf P q b)
    (hg : g ≫ positiveInclusion P q b f = positiveInclusion P p a e) :
    g = positiveComparison P p q a b e f := by
  exact PositiveHom.factor_through_split_inclusion_unique
    (positiveInclusion P p a e) (positiveInclusion P q b f)
    (positiveRetraction P q b f) (positive_retraction P q b f) g hg

/-- The identity comparison is the identity on the actual positive sheaf. -/
theorem positiveComparison_self
    (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {r : ℕ} (a : TangentSplittingProfile r)
    {E : OModule ProjectiveLine} (e : E ≅ splitSheaf P p a) :
    positiveComparison P p p a a e e = 𝟙 (positiveSheaf P p a) :=
  positive_retraction P p a e

/-- Comparisons through a third splitting agree with the direct one;
the inclusion-over-E characterization is coherent. -/
theorem positiveComparison_comp
    (P : ProjectiveLineOverC) (p q z : ProjectiveLinePoint P)
    {r s t : ℕ} (a : TangentSplittingProfile r) (b : TangentSplittingProfile s)
    (c : TangentSplittingProfile t) {E : OModule ProjectiveLine}
    (e : E ≅ splitSheaf P p a) (f : E ≅ splitSheaf P q b)
    (g : E ≅ splitSheaf P z c) (hb : b.IsFree) :
    positiveComparison P p q a b e f ≫ positiveComparison P q z b c f g =
      positiveComparison P p z a c e g := by
  change positiveComparison P p q a b e f ≫
      (positiveInclusion P q b f ≫ positiveRetraction P z c g) =
    positiveInclusion P p a e ≫ positiveRetraction P z c g
  rw [← Category.assoc, positiveComparison_inclusion P p q a b e f hb]

/-- The canonical isomorphism of positive parts of two nonnegative
splittings. Both directions commute with the actual inclusions in E. -/
def positivePartIso
    (P : ProjectiveLineOverC) (p q : ProjectiveLinePoint P)
    {r s : ℕ} (a : TangentSplittingProfile r) (b : TangentSplittingProfile s)
    {E : OModule ProjectiveLine}
    (e : E ≅ splitSheaf P p a) (f : E ≅ splitSheaf P q b)
    (ha : a.IsFree) (hb : b.IsFree) : positiveSheaf P p a ≅ positiveSheaf P q b :=
  PositiveHom.splitInclusionIso
    (positiveInclusion P p a e) (positiveRetraction P p a e)
    (positiveInclusion P q b f) (positiveRetraction P q b f)
    (positive_retraction P p a e) (positive_retraction P q b f)
    (positiveComparison_inclusion P p q a b e f hb)
    (positiveComparison_inclusion P q p b a f e ha)

theorem positivePartIso_hom_inclusion
    (P : ProjectiveLineOverC) (p q : ProjectiveLinePoint P)
    {r s : ℕ} (a : TangentSplittingProfile r) (b : TangentSplittingProfile s)
    {E : OModule ProjectiveLine}
    (e : E ≅ splitSheaf P p a) (f : E ≅ splitSheaf P q b)
    (ha : a.IsFree) (hb : b.IsFree) :
    (positivePartIso P p q a b e f ha hb).hom ≫ positiveInclusion P q b f =
      positiveInclusion P p a e :=
  positiveComparison_inclusion P p q a b e f hb

theorem positivePartIso_inv_inclusion
    (P : ProjectiveLineOverC) (p q : ProjectiveLinePoint P)
    {r s : ℕ} (a : TangentSplittingProfile r) (b : TangentSplittingProfile s)
    {E : OModule ProjectiveLine}
    (e : E ≅ splitSheaf P p a) (f : E ≅ splitSheaf P q b)
    (ha : a.IsFree) (hb : b.IsFree) :
    (positivePartIso P p q a b e f ha hb).inv ≫ positiveInclusion P p a e =
      positiveInclusion P q b f :=
  positiveComparison_inclusion P q p b a f e ha

end LeBrunSalamon.Construction.Lines.PositivePart

end

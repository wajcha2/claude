import LSHomDegree
import LSHomPresentationComparisonProfile

/-! Transport of a supplied fixed-degree stratum through the actual
canonical Hom-presentation isomorphism. The comparison import is the exact
completed local diagnostic artifact, not a relabeled production module. -/

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseSeven LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseThirtyTwo LeBrunSalamon.Skeleton
open LeBrunSalamon.Construction.Lines
open LeBrunSalamon.HomPresentationComparison

namespace LeBrunSalamon.HomDegreeStratumTransport

/-! ## Restriction along an isomorphism over the same base -/

theorem restriction_over {S T B : Scheme} (e : S ≅ T)
    (sS : S ⟶ B) (sT : T ⟶ B) (he : e.hom ≫ sT = sS)
    (U : T.Opens) :
    (e.hom ∣_ U) ≫ (U.ι ≫ sT) = (e.hom ⁻¹ᵁ U).ι ≫ sS := by
  calc
    (e.hom ∣_ U) ≫ (U.ι ≫ sT) =
        (e.hom ⁻¹ᵁ U).ι ≫ (e.hom ≫ sT) :=
      morphismRestrict_ι_assoc e.hom U sT
    _ = (e.hom ⁻¹ᵁ U).ι ≫ sS := by rw [he]

theorem preimage_locallyOfFiniteType {S T B : Scheme} (e : S ≅ T)
    (sS : S ⟶ B) (sT : T ⟶ B) (he : e.hom ≫ sT = sS)
    (U : T.Opens) (hU : LocallyOfFiniteType (U.ι ≫ sT)) :
    LocallyOfFiniteType ((e.hom ⁻¹ᵁ U).ι ≫ sS) := by
  letI : LocallyOfFiniteType (U.ι ≫ sT) := hU
  rw [← restriction_over e sS sT he U]
  infer_instance

theorem preimage_quasiCompact {S T B : Scheme} (e : S ≅ T)
    (sS : S ⟶ B) (sT : T ⟶ B) (he : e.hom ≫ sT = sS)
    (U : T.Opens) (hU : QuasiCompact (U.ι ≫ sT)) :
    QuasiCompact ((e.hom ⁻¹ᵁ U).ι ≫ sS) := by
  letI : QuasiCompact (U.ι ≫ sT) := hU
  rw [← restriction_over e sS sT he U]
  infer_instance

/-! ## The original degree-stratum contract on an arbitrary presentation -/

def transport (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {d : ℕ} (X : SmoothProperComplexVariety d)
    (H K : HomSpacePresentation P X) (L : LineBundle X.scheme) (e : ℤ)
    (D : HomDegree.Open P p X K L e) : HomDegree.Open P p X H L e where
  openSet := (canonicalIso P H K).hom ⁻¹ᵁ D.openSet
  closed := D.closed.preimage (canonicalIso P H K).hom.continuous
  finiteType := preimage_locallyOfFiniteType (canonicalIso P H K) H.toC K.toC
    (canonicalIso_toC P H K) D.openSet D.finiteType
  quasiCompact := preimage_quasiCompact (canonicalIso P H K) H.toC K.toC
    (canonicalIso_toC P H K) D.openSet D.quasiCompact
  membership t := by
    have ht := D.membership (composePoint t (comparison P H K))
    rw [comparison_mapAt P H K t] at ht
    let z : ComplexBase := IsLocalRing.closedPoint ℂ
    change ((t.val ≫ (comparison P H K).val) z ∈ D.openSet) ↔ _ at ht
    change ((comparison P H K).val (t.val z) ∈ D.openSet) ↔ _
    rw [Scheme.Hom.comp_apply t.val (comparison P H K).val z] at ht
    exact ht

theorem nonempty_transport (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {d : ℕ} (X : SmoothProperComplexVariety d)
    (H K : HomSpacePresentation P X) (L : LineBundle X.scheme) (e : ℤ)
    (hK : Nonempty (HomDegree.Open P p X K L e)) :
    Nonempty (HomDegree.Open P p X H L e) := by
  obtain ⟨D⟩ := hK
  exact ⟨transport P p X H K L e D⟩

end LeBrunSalamon.HomDegreeStratumTransport

end

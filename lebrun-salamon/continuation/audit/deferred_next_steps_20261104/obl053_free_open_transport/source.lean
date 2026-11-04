import RecompileExtensionsPart04Geometry
import LSHomPresentationComparisonProfile

/-! Transport of a supplied free-curve neighbourhood between supplied
all-test Hom presentations. No neighbourhood-existence theorem is used.
The comparison import is the exact completed local diagnostic artifact. -/

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseSeven LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentySix LeBrunSalamon.PhaseTwentySeven
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirty
open LeBrunSalamon.PhaseThirtyTwo LeBrunSalamon.Skeleton
open LeBrunSalamon.HomPresentationComparison
open LeBrunSalamon.Construction

namespace LeBrunSalamon.HomFreeOpenTransport

theorem inverse_over {S T B : Scheme} (e : S ≅ T)
    (sS : S ⟶ B) (sT : T ⟶ B) (he : e.hom ≫ sT = sS) :
    e.inv ≫ sS = sT := by
  rw [← he, Iso.inv_hom_id_assoc]

theorem restriction_over {S T B : Scheme} (e : S ≅ T)
    (sS : S ⟶ B) (sT : T ⟶ B) (he : e.hom ≫ sT = sS)
    (U : T.Opens) :
    (e.hom ∣_ U) ≫ (U.ι ≫ sT) = (e.hom ⁻¹ᵁ U).ι ≫ sS := by
  calc
    (e.hom ∣_ U) ≫ (U.ι ≫ sT) =
        (e.hom ⁻¹ᵁ U).ι ≫ (e.hom ≫ sT) :=
      morphismRestrict_ι_assoc e.hom U sT
    _ = (e.hom ⁻¹ᵁ U).ι ≫ sS := by rw [he]

def pointForward {S T : Scheme} (e : S ≅ T)
    (sS : S ⟶ ComplexBase) (sT : T ⟶ ComplexBase)
    (he : e.hom ≫ sT = sS)
    (t : PointsOver ComplexBase (𝟙 ComplexBase) S sS) :
    PointsOver ComplexBase (𝟙 ComplexBase) T sT :=
  ⟨t.val ≫ e.hom, by rw [Category.assoc, he, t.property]⟩

def pointBackward {S T : Scheme} (e : S ≅ T)
    (sS : S ⟶ ComplexBase) (sT : T ⟶ ComplexBase)
    (he : e.hom ≫ sT = sS)
    (t : PointsOver ComplexBase (𝟙 ComplexBase) T sT) :
    PointsOver ComplexBase (𝟙 ComplexBase) S sS :=
  pointForward e.symm sT sS (inverse_over e sS sT he) t

theorem pointForward_backward {S T : Scheme} (e : S ≅ T)
    (sS : S ⟶ ComplexBase) (sT : T ⟶ ComplexBase)
    (he : e.hom ≫ sT = sS)
    (t : PointsOver ComplexBase (𝟙 ComplexBase) T sT) :
    pointForward e sS sT he (pointBackward e sS sT he t) = t := by
  apply Subtype.ext
  simp only [pointForward, pointBackward, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

def sourceIso (P : ProjectiveLineOverC) {S T : Scheme} (e : S ≅ T)
    (sS : S ⟶ ComplexBase) (sT : T ⟶ ComplexBase)
    (he : e.hom ≫ sT = sS) :
    RationalSourceOver P S sS ≅ RationalSourceOver P T sT where
  hom := rationalSourceMap P ⟨e.hom, he⟩
  inv := rationalSourceMap P ⟨e.inv, inverse_over e sS sT he⟩
  hom_inv_id := by
    apply pullback.hom_ext <;> simp [rationalSourceMap, Category.assoc]
  inv_hom_id := by
    apply pullback.hom_ext <;> simp [rationalSourceMap, Category.assoc]

theorem denseRange_iso_comp {S T Y : Scheme} (e : S ≅ T) (g : T ⟶ Y)
    (hg : DenseRange (fun z => g z)) :
    DenseRange (fun z => (e.hom ≫ g) z) := by
  have hsubset : Set.range (fun y => g y) ⊆ Set.range (fun x => (e.hom ≫ g) x) := by
    rintro _ ⟨y, rfl⟩
    refine ⟨e.inv y, ?_⟩
    change (e.hom ≫ g) (e.inv y) = g y
    have hback : e.hom (e.inv y) = y := by
      calc
        e.hom (e.inv y) = (e.inv ≫ e.hom) y :=
          (Scheme.Hom.comp_apply e.inv e.hom y).symm
        _ = (𝟙 T) y := congrArg (fun k : T ⟶ T => k y) e.inv_hom_id
        _ = y := rfl
    rw [Scheme.Hom.comp_apply, hback]
  intro z
  exact closure_mono hsubset (hg z)

def openPoint {T : Scheme} (sT : T ⟶ ComplexBase) (U : T.Opens)
    (t : PointsOver ComplexBase (𝟙 ComplexBase) U.toScheme (U.ι ≫ sT)) :
    PointsOver ComplexBase (𝟙 ComplexBase) T sT :=
  ⟨t.val ≫ U.ι, by simpa only [Category.assoc] using t.property⟩

section SuppliedPresentations

variable (P : ProjectiveLineOverC) {d : ℕ} {X : SmoothProperComplexVariety d}
variable (H K : HomSpacePresentation P X)

def restrictedIso (U : K.parameter.Opens) :
    ((canonicalIso P H K).hom ⁻¹ᵁ U).toScheme ≅ U.toScheme :=
  asIso ((canonicalIso P H K).hom ∣_ U)

theorem restrictedIso_over (U : K.parameter.Opens) :
    (restrictedIso P H K U).hom ≫ (U.ι ≫ K.toC) =
      ((canonicalIso P H K).hom ⁻¹ᵁ U).ι ≫ H.toC :=
  restriction_over (canonicalIso P H K) H.toC K.toC (canonicalIso_toC P H K) U

def forwardPoint (U : K.parameter.Opens)
    (t : PointsOver ComplexBase (𝟙 ComplexBase)
      ((canonicalIso P H K).hom ⁻¹ᵁ U).toScheme
      (((canonicalIso P H K).hom ⁻¹ᵁ U).ι ≫ H.toC)) :
    PointsOver ComplexBase (𝟙 ComplexBase) U.toScheme (U.ι ≫ K.toC) :=
  pointForward (restrictedIso P H K U)
    (((canonicalIso P H K).hom ⁻¹ᵁ U).ι ≫ H.toC) (U.ι ≫ K.toC)
    (restrictedIso_over P H K U) t

def backwardPoint (U : K.parameter.Opens)
    (t : PointsOver ComplexBase (𝟙 ComplexBase) U.toScheme (U.ι ≫ K.toC)) :
    PointsOver ComplexBase (𝟙 ComplexBase)
      ((canonicalIso P H K).hom ⁻¹ᵁ U).toScheme
      (((canonicalIso P H K).hom ⁻¹ᵁ U).ι ≫ H.toC) :=
  pointBackward (restrictedIso P H K U)
    (((canonicalIso P H K).hom ⁻¹ᵁ U).ι ≫ H.toC) (U.ι ≫ K.toC)
    (restrictedIso_over P H K U) t

theorem forward_backward (U : K.parameter.Opens)
    (t : PointsOver ComplexBase (𝟙 ComplexBase) U.toScheme (U.ι ≫ K.toC)) :
    forwardPoint P H K U (backwardPoint P H K U t) = t :=
  pointForward_backward (restrictedIso P H K U)
    (((canonicalIso P H K).hom ⁻¹ᵁ U).ι ≫ H.toC) (U.ι ≫ K.toC)
    (restrictedIso_over P H K U) t

theorem mapAt_forward (U : K.parameter.Opens)
    (t : PointsOver ComplexBase (𝟙 ComplexBase)
      ((canonicalIso P H K).hom ⁻¹ᵁ U).toScheme
      (((canonicalIso P H K).hom ⁻¹ᵁ U).ι ≫ H.toC)) :
    K.mapAt P (openPoint K.toC U (forwardPoint P H K U t)) =
      H.mapAt P (openPoint H.toC ((canonicalIso P H K).hom ⁻¹ᵁ U) t) := by
  have hpoint : openPoint K.toC U (forwardPoint P H K U t) =
      composePoint (openPoint H.toC ((canonicalIso P H K).hom ⁻¹ᵁ U) t)
        (comparison P H K) := by
    apply Subtype.ext
    change (t.val ≫ ((canonicalIso P H K).hom ∣_ U)) ≫ U.ι =
      (t.val ≫ ((canonicalIso P H K).hom ⁻¹ᵁ U).ι) ≫ (canonicalIso P H K).hom
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc]
  exact (congrArg (K.mapAt P) hpoint).trans
    (comparison_mapAt P H K (openPoint H.toC ((canonicalIso P H K).hom ⁻¹ᵁ U) t))

theorem restriction_evaluation (U : K.parameter.Opens) :
    rationalSourceMap P
      ⟨(restrictedIso P H K U).hom, restrictedIso_over P H K U⟩ ≫
        (rationalSourceMap P (⟨U.ι, rfl⟩ :
          PointsOver U.toScheme (U.ι ≫ K.toC) K.parameter K.toC) ≫ K.evaluation) =
    rationalSourceMap P (⟨((canonicalIso P H K).hom ⁻¹ᵁ U).ι, rfl⟩ :
      PointsOver ((canonicalIso P H K).hom ⁻¹ᵁ U).toScheme
        (((canonicalIso P H K).hom ⁻¹ᵁ U).ι ≫ H.toC) H.parameter H.toC) ≫
      H.evaluation := by
  have hp : composePoint
      (⟨(restrictedIso P H K U).hom, restrictedIso_over P H K U⟩ :
        PointsOver ((canonicalIso P H K).hom ⁻¹ᵁ U).toScheme
          (((canonicalIso P H K).hom ⁻¹ᵁ U).ι ≫ H.toC)
          U.toScheme (U.ι ≫ K.toC))
      (⟨U.ι, rfl⟩ : PointsOver U.toScheme (U.ι ≫ K.toC) K.parameter K.toC) =
      composePoint
        (⟨((canonicalIso P H K).hom ⁻¹ᵁ U).ι, rfl⟩ :
          PointsOver ((canonicalIso P H K).hom ⁻¹ᵁ U).toScheme
            (((canonicalIso P H K).hom ⁻¹ᵁ U).ι ≫ H.toC) H.parameter H.toC)
        (comparison P H K) := by
    apply Subtype.ext
    exact morphismRestrict_ι (canonicalIso P H K).hom U
  rw [← Category.assoc, ← sourceMap_comp, hp, comparison_family]

theorem preimage_smooth (U : K.parameter.Opens)
    (hU : Smooth (U.ι ≫ K.toC)) :
    Smooth (((canonicalIso P H K).hom ⁻¹ᵁ U).ι ≫ H.toC) := by
  letI := hU
  rw [← restrictedIso_over P H K U]
  infer_instance

theorem preimage_irreducible (U : K.parameter.Opens)
    (hU : IrreducibleSpace U.toScheme) :
    IrreducibleSpace ((canonicalIso P H K).hom ⁻¹ᵁ U).toScheme := by
  letI := hU
  exact (restrictedIso P H K U).inv.homeomorph.surjective.irreducibleSpace
    (restrictedIso P H K U).inv.continuous

theorem preimage_smoothEvaluation (U : K.parameter.Opens)
    (hU : Smooth (rationalSourceMap P (⟨U.ι, rfl⟩ :
      PointsOver U.toScheme (U.ι ≫ K.toC) K.parameter K.toC) ≫ K.evaluation)) :
    Smooth (rationalSourceMap P (⟨((canonicalIso P H K).hom ⁻¹ᵁ U).ι, rfl⟩ :
      PointsOver ((canonicalIso P H K).hom ⁻¹ᵁ U).toScheme
        (((canonicalIso P H K).hom ⁻¹ᵁ U).ι ≫ H.toC) H.parameter H.toC) ≫
      H.evaluation) := by
  letI := hU
  let e := sourceIso P (restrictedIso P H K U)
    (((canonicalIso P H K).hom ⁻¹ᵁ U).ι ≫ H.toC) (U.ι ≫ K.toC)
    (restrictedIso_over P H K U)
  rw [← restriction_evaluation P H K U]
  change Smooth (e.hom ≫ _)
  infer_instance

theorem preimage_dominantEvaluation (U : K.parameter.Opens)
    (hU : DenseRange (fun z => (rationalSourceMap P (⟨U.ι, rfl⟩ :
      PointsOver U.toScheme (U.ι ≫ K.toC) K.parameter K.toC) ≫ K.evaluation) z)) :
    DenseRange (fun z => (rationalSourceMap P
      (⟨((canonicalIso P H K).hom ⁻¹ᵁ U).ι, rfl⟩ :
        PointsOver ((canonicalIso P H K).hom ⁻¹ᵁ U).toScheme
          (((canonicalIso P H K).hom ⁻¹ᵁ U).ι ≫ H.toC) H.parameter H.toC) ≫
      H.evaluation) z) := by
  let e := sourceIso P (restrictedIso P H K U)
    (((canonicalIso P H K).hom ⁻¹ᵁ U).ι ≫ H.toC) (U.ι ≫ K.toC)
    (restrictedIso_over P H K U)
  rw [← restriction_evaluation P H K U]
  change DenseRange (fun z => (e.hom ≫ _) z)
  exact denseRange_iso_comp e
    (rationalSourceMap P (⟨U.ι, rfl⟩ :
      PointsOver U.toScheme (U.ι ≫ K.toC) K.parameter K.toC) ≫ K.evaluation) hU

def transport (p : ProjectiveLinePoint P) (f : RationalCurve P X)
    (L : LineBundle X.scheme) (O : HomNeighborhood.FreeOpen P p X K f L) :
    HomNeighborhood.FreeOpen P p X H f L where
  neighborhood := (canonicalIso P H K).hom ⁻¹ᵁ O.neighborhood
  affine := O.affine.preimage_of_isIso (canonicalIso P H K).hom
  marked := backwardPoint P H K O.neighborhood O.marked
  center := by
    change H.mapAt P (openPoint H.toC ((canonicalIso P H K).hom ⁻¹ᵁ O.neighborhood)
      (backwardPoint P H K O.neighborhood O.marked)) = f.map
    rw [← mapAt_forward P H K O.neighborhood, forward_backward]
    exact O.center
  smooth := preimage_smooth P H K O.neighborhood O.smooth
  irreducible := preimage_irreducible P H K O.neighborhood O.irreducible
  smoothEvaluation := preimage_smoothEvaluation P H K O.neighborhood O.smoothEvaluation
  dominantEvaluation := preimage_dominantEvaluation P H K O.neighborhood O.dominantEvaluation
  curveAt t := O.curveAt (forwardPoint P H K O.neighborhood t)
  curveAt_spec t := (O.curveAt_spec (forwardPoint P H K O.neighborhood t)).trans
    (mapAt_forward P H K O.neighborhood t)
  free t := O.free (forwardPoint P H K O.neighborhood t)
  degree t := O.degree (forwardPoint P H K O.neighborhood t)
  preservesVeryFree hf t := O.preservesVeryFree hf (forwardPoint P H K O.neighborhood t)

theorem nonempty_transport (p : ProjectiveLinePoint P) (f : RationalCurve P X)
    (L : LineBundle X.scheme) (hK : Nonempty (HomNeighborhood.FreeOpen P p X K f L)) :
    Nonempty (HomNeighborhood.FreeOpen P p X H f L) := by
  obtain ⟨O⟩ := hK
  exact ⟨transport P H K p f L O⟩

end SuppliedPresentations

end LeBrunSalamon.HomFreeOpenTransport

end

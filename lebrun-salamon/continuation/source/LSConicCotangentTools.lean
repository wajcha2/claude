import LSTangentComparison

/-! Evaluation-normalized dual frames and coordinate extensionality for the
actual relative cotangent sheaf on the affine plane. Extracted unchanged
from the later conic-node proof so the source fundamental class can use them. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.PhaseThirty LeBrunSalamon.Skeleton
namespace LeBrunSalamon.Construction.ConicModelSections
open Smoothing Smoothing.SourceAffineCharts ContactDerivativeIsoProof

namespace DualFrame

/-- Dualizing an actual frame, using the evaluation-normalized dual map. -/
def dualIso {Y : Scheme} {E G : OModule Y} (e : E ≅ G) :
    dualSheaf E ≅ dualSheaf G where
  hom := dualMap e.inv
  inv := dualMap e.hom
  hom_inv_id := by rw [← dualMap_comp, e.hom_inv_id, dualMap_id]
  inv_hom_id := by rw [← dualMap_comp, e.inv_hom_id, dualMap_id]

def unitIso (Y : Scheme) : dualSheaf (structureModule Y) ≅ structureModule Y :=
  InternalHomPresentation.unitSourceIso
    (internalHomPresentation (structureModule Y) (structureModule Y))

/-- The unit comparison reads a functional on the unit section. -/
theorem unitIso_apply {Y : Scheme} (U : Y.Opens)
    (v : SectionsOn (dualSheaf (structureModule Y)) U) :
    (unitIso Y).hom.app U v =
      (dualEvaluation (structureModule Y)).apply U v (1 : RingSections Y U) := by
  have h := congrArg
    (fun q : tensorSheaf (dualSheaf (structureModule Y)) (structureModule Y) ⟶
      structureModule Y => q.app U
        ((tensorPresentation (dualSheaf (structureModule Y))
          (structureModule Y)).pair.apply U v (1 : RingSections Y U)))
    ((internalHomPresentation (structureModule Y) (structureModule Y)).uniqueIso_evaluate
      (InternalHomPresentation.unitSource (structureModule Y)))
  change (TensorConstruction.rightUnitIso (structureModule Y)).hom.app U
      ((tensorMap (unitIso Y).hom (𝟙 (structureModule Y))).app U
        ((tensorPresentation (dualSheaf (structureModule Y))
          (structureModule Y)).pair.apply U v (1 : RingSections Y U))) =
    (dualEvaluation (structureModule Y)).apply U v (1 : RingSections Y U) at h
  rw [tensorMap_apply, TensorConstruction.rightUnitIso_hom_pair] at h
  change (1 : RingSections Y U) • (unitIso Y).hom.app U v = _ at h
  simpa only [one_smul] using h

/-- The dual frame evaluates on the generator of the given original frame. -/
def ofFrame {Y : Scheme} {E : OModule Y} (e : E ≅ structureModule Y) :
    dualSheaf E ≅ structureModule Y := dualIso e ≪≫ unitIso Y

theorem ofFrame_apply {Y : Scheme} {E : OModule Y}
    (e : E ≅ structureModule Y) (U : Y.Opens)
    (v : SectionsOn (dualSheaf E) U) :
    (ofFrame e).hom.app U v =
      (dualEvaluation E).apply U v (e.inv.app U (1 : RingSections Y U)) := by
  change (unitIso Y).hom.app U ((dualMap e.inv).app U v) = _
  rw [unitIso_apply, dualMap_evaluate]

end DualFrame

/-- Two affine-plane coordinate differentials determine a map out of
the actual pulled relative cotangent sheaf.  The base map need only
factor the complex structure; the relative source can be singular. -/
theorem plane_pulledCotangent_hom_ext {B T : Scheme}
    (pi : Plane ⟶ B) (sB : B ⟶ ComplexBase) (hpi : pi ≫ sB = planeBase)
    (f : T ⟶ Plane) {E : OModule T}
    (q r : pullbackModule f (cotangentSheaf pi) ⟶ E)
    (h : ∀ i : Fin 2,
      q.app (f ⁻¹ᵁ ⊤) (pullLocalSection f (cotangentSheaf pi) ⊤
        ((cotangentPresentation pi).differential.apply ⊤
          (planeFunction (MvPolynomial.X i)))) =
      r.app (f ⁻¹ᵁ ⊤) (pullLocalSection f (cotangentSheaf pi) ⊤
        ((cotangentPresentation pi).differential.apply ⊤
          (planeFunction (MvPolynomial.X i))))) : q = r := by
  let A := (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv
    (cotangentSheaf pi) E
  apply A.injective
  apply ((cotangentPresentation pi).universal
    ((Scheme.Modules.pushforward f).obj E)).injective
  let Dq := (cotangentPresentation pi).differential.postcompose (A q)
  let Dr := (cotangentPresentation pi).differential.postcompose (A r)
  change Dq = Dr
  have hconstant (D : RelativeSheafDerivation pi
      ((Scheme.Modules.pushforward f).obj E)) (c : ℂ) :
      D.apply ⊤ (planeFunction (MvPolynomial.C c)) = 0 := by
    rw [planeFunction_constant, complexConstants_apply_top, ← hpi,
      Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    exact D.killsBase ⊤
      (sB.appTop ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c))
  have hX (i : Fin 2) :
      Dq.apply ⊤ (planeFunction (MvPolynomial.X i)) =
        Dr.apply ⊤ (planeFunction (MvPolynomial.X i)) := h i
  apply Lines.AffineDerivationFaithfulness.eq_of_affine_global
  intro a
  obtain ⟨p, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of PlaneRing)).inv).surjective a
  change Dq.apply ⊤ (planeFunction p) = Dr.apply ⊤ (planeFunction p)
  induction p using MvPolynomial.induction_on with
  | C c => rw [hconstant Dq, hconstant Dr]
  | add p q hp hq =>
      have hsum : planeFunction (p + q) = planeFunction p + planeFunction q :=
        map_add (Scheme.ΓSpecIso (CommRingCat.of PlaneRing)).inv.hom p q
      rw [hsum, Dq.add, Dr.add, hp, hq]
  | mul_X p i hp =>
      have hprod : planeFunction (p * MvPolynomial.X i) =
          planeFunction p * planeFunction (MvPolynomial.X i) :=
        map_mul (Scheme.ΓSpecIso (CommRingCat.of PlaneRing)).inv.hom p (MvPolynomial.X i)
      rw [hprod, Dq.leibniz, Dr.leibniz, hp, hX i]


end LeBrunSalamon.Construction.ConicModelSections
end

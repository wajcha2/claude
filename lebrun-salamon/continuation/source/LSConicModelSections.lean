import LSTraitContact

/-!
# The actual node of the standard conic

The fundamental-class map vanishes after pullback to the node.  The
proof uses its two fixed chart coefficients and the universal property
of relative differentials.  Affine localization faithfulness extends
the calculation from the two polynomial generators to every open.
No local freeness of the relative cotangent sheaf at the node is used.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.PhaseThirty LeBrunSalamon.Skeleton
open LeBrunSalamon.Refinement

namespace LeBrunSalamon.Construction.ConicModelSections

open Smoothing Smoothing.SourceAffineCharts
open StandardConicDifferential ContactDerivativeIsoProof

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
      (dualEvaluation (structureModule Y)).apply U v 1 := by
  have h := congrArg
    (fun q : tensorSheaf (dualSheaf (structureModule Y)) (structureModule Y) ⟶
      structureModule Y => q.app U
        ((tensorPresentation (dualSheaf (structureModule Y))
          (structureModule Y)).pair.apply U v 1))
    ((internalHomPresentation (structureModule Y) (structureModule Y)).uniqueIso_evaluate
      (InternalHomPresentation.unitSource (structureModule Y)))
  change (TensorConstruction.rightUnitIso (structureModule Y)).hom.app U
      ((tensorMap (unitIso Y).hom (𝟙 (structureModule Y))).app U
        ((tensorPresentation (dualSheaf (structureModule Y))
          (structureModule Y)).pair.apply U v 1)) =
    (dualEvaluation (structureModule Y)).apply U v 1 at h
  rw [tensorMap_apply, TensorConstruction.rightUnitIso_hom_pair, one_smul] at h
  exact h

/-- The dual frame evaluates on the generator of the given original frame. -/
def ofFrame {Y : Scheme} {E : OModule Y} (e : E ≅ structureModule Y) :
    dualSheaf E ≅ structureModule Y := dualIso e ≪≫ unitIso Y

theorem ofFrame_apply {Y : Scheme} {E : OModule Y}
    (e : E ≅ structureModule Y) (U : Y.Opens)
    (v : SectionsOn (dualSheaf E) U) :
    (ofFrame e).hom.app U v =
      (dualEvaluation E).apply U v (e.inv.app U 1) := by
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
        map_add (Scheme.ΓSpecIso (CommRingCat.of PlaneRing)).inv p q
      rw [hsum, Dq.add, Dr.add, hp, hq]
  | mul_X p i hp =>
      have hprod : planeFunction (p * MvPolynomial.X i) =
          planeFunction p * planeFunction (MvPolynomial.X i) :=
        map_mul (Scheme.ΓSpecIso (CommRingCat.of PlaneRing)).inv p (MvPolynomial.X i)
      rw [hprod, Dq.leibniz, Dr.leibniz, hp, hX i]

/-- The literal point u=v=0 in the nodal affine chart. -/
def origin : ComplexBase ⟶ Plane := planeFromFunctions (𝟙 ComplexBase) 0 0

theorem origin_coordinate (i : Fin 2) :
    origin.appTop (planeFunction (MvPolynomial.X i)) = 0 := by
  rw [origin, planeFromFunctions_apply, MvPolynomial.eval₂_X]
  simp

variable (F : StandardSource)

def node : ComplexBase ⟶ F.source := origin ≫ modelMap F 0

@[reassoc] theorem node_parameter : node F ≫ F.parameter = scalarPoint 0 := by
  change Smoothing.FixedEndsProof.BranchCharts.nodeSource F (𝟙 ComplexBase) 0 0 ≫
    F.parameter = scalarPoint 0
  rw [Smoothing.FixedEndsProof.BranchCharts.nodeSource_parameter, zero_mul,
    Smoothing.FixedEndsProof.BranchCharts.fromFunction_zero, Category.id_comp]

/-- Express the actual chart form in its fixed dual O(1,1) frame. -/
def nodeChartScalar : cotangentSheaf (modelMap F 0 ≫ F.parameter) ⟶
    structureModule Plane :=
  chartForm F (fundamentalClass F) 0 ≫ (DualFrame.ofFrame (chartLineFrame F 0)).hom

theorem nodeChartScalar_differential (i : Fin 2) :
    (nodeChartScalar F).app ⊤
      ((cotangentPresentation (modelMap F 0 ≫ F.parameter)).differential.apply ⊤
        (planeFunction (MvPolynomial.X i))) = chartLogValue 0 i := by
  change (DualFrame.ofFrame (chartLineFrame F 0)).hom.app ⊤
    ((chartForm F (fundamentalClass F) 0).app ⊤
      ((cotangentPresentation (modelMap F 0 ≫ F.parameter)).differential.apply ⊤
        (planeFunction (MvPolynomial.X i)))) = _
  rw [DualFrame.ofFrame_apply]
  exact fundamentalClass_chartCoefficient F 0 i

theorem nodeChartScalar_pullback_zero :
    (Scheme.Modules.pullback origin).map (nodeChartScalar F) = 0 := by
  let pi := modelMap F 0 ≫ F.parameter
  have hpi : pi ≫ affineLineToC = planeBase := by
    rw [pi, (modelMap_spec F 0).1, polynomialLine_over]
  have h : (Scheme.Modules.pullback origin).map (nodeChartScalar F) ≫
      unitPullbackMap origin = 0 := by
    apply plane_pulledCotangent_hom_ext pi affineLineToC hpi origin
    intro i
    change (unitPullbackMap origin).app (origin ⁻¹ᵁ ⊤)
      (((Scheme.Modules.pullback origin).map (nodeChartScalar F)).app (origin ⁻¹ᵁ ⊤)
        (pullLocalSection origin (cotangentSheaf pi) ⊤
          ((cotangentPresentation pi).differential.apply ⊤
            (planeFunction (MvPolynomial.X i))))) = 0
    rw [ExternalExchangeCoherenceProof.pullLocalSection_map,
      nodeChartScalar_differential, unitPullbackMap_pullLocalSection]
    change origin.appTop (chartLogValue 0 i) = 0
    fin_cases i <;> simp [chartLogValue, origin_coordinate]
  apply (cancel_mono (unitPullbackIso origin).hom).mp
  simpa only [zero_comp] using h

/-- The original source fundamental class has zero fiber at the actual
node.  Both coordinate generators are killed, before base change to any
nonreduced thickened node. -/
theorem fundamentalClass_node_zero :
    (Scheme.Modules.pullback (node F)).map (fundamentalClass F) = 0 := by
  have hform : (Scheme.Modules.pullback origin).map
      (chartForm F (fundamentalClass F) 0) = 0 := by
    apply (cancel_mono
      ((Scheme.Modules.pullback origin).mapIso (DualFrame.ofFrame (chartLineFrame F 0))).hom).mp
    rw [zero_comp, ← Functor.map_comp]
    exact nodeChartScalar_pullback_zero F
  letI := dualBaseChange_isIso (modelMap F 0) (line F).locallyFree
  have hiter : (Scheme.Modules.pullback origin).map
      ((Scheme.Modules.pullback (modelMap F 0)).map (fundamentalClass F)) = 0 := by
    apply (cancel_epi
      ((Scheme.Modules.pullback origin).mapIso (chartCotangentIso F 0)).inv).mp
    apply (cancel_mono
      ((Scheme.Modules.pullback origin).map (dualBaseChange (modelMap F 0) (line F).sheaf))).mp
    simpa only [chartForm, Functor.map_comp, Category.assoc, comp_zero, zero_comp] using hform
  apply (cancel_epi (compositionPullback origin (modelMap F 0) (node F) rfl
    (cotangentSheaf F.parameter)).hom).mp
  rw [← Normalization.BundleGluing.compositionPullback_naturality,
    hiter, zero_comp, comp_zero]

end LeBrunSalamon.Construction.ConicModelSections

end

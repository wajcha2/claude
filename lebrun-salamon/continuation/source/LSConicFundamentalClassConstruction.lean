import LSStandardConicFrames
import LSConicChartDerivations
import LSConicCotangentTools
import LSModuleHomGluing
import LSOpenCotangentScalar
import LSConicOverlapAlgebra
import LSLineEvaluation
import LSOpenModuleCoherence
import LSConicScalarCompatibility

/-! Off-graph candidate: assemble the prescribed affine cotangent functionals
through the actual homogeneous O(1,1) frames. The explicit overlap calculation
and global gluing are supplied below without a new admission. Native checking
of this candidate and its new helpers is still pending; the source text alone
does not certify the completed fundamental-class obligation. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.PhaseThirty
open LeBrunSalamon.Skeleton
open LeBrunSalamon.ModuleHomGluing

namespace LeBrunSalamon.Construction.StandardConicConstruction

open Smoothing Smoothing.SourceAffineCharts Smoothing.CoordinateCharts StandardConicDifferential
open ConicModelSections
open OpenModuleCoherence

attribute [local instance] modelMap_isOpenImmersion

variable (F : StandardSource)

abbrev chart (k : Fin 3) : F.source.Opens :=
  chartOpen F (leftIndex k) (rightIndex k)

/-- The selected affine-plane presentation of each actual open. -/
def atlasHomEquiv (E G : OModule F.source) (k : Fin 3) :
    (E.over (chart F k) ⟶ G.over (chart F k)) ≃
      (pullbackModule (modelMap F k) E ⟶ pullbackModule (modelMap F k) G) :=
  chartHomAlongEquiv E G (chart F k) (chartIso F k).symm
    (modelMap F k) (modelToChart_inclusion F k)

theorem atlasHomEquiv_global (E G : OModule F.source) (k : Fin 3) (f : E ⟶ G) :
    atlasHomEquiv F E G k
        ((SheafOfModules.overFunctor F.source.ringCatSheaf (chart F k)).map f) =
      (Scheme.Modules.pullback (modelMap F k)).map f := by
  exact chartHomAlongEquiv_global E G (chart F k) (chartIso F k).symm
    (modelMap F k) (modelToChart_inclusion F k) f

/-- The normalized local functional as a map between pullbacks of the
original global sheaves. All comparisons retain their canonical orientation. -/
def localMap (k : Fin 3) :
    pullbackModule (modelMap F k) (cotangentSheaf F.parameter) ⟶
      pullbackModule (modelMap F k) (dualSheaf (line F).sheaf) := by
  letI := dualBaseChange_isIso (modelMap F k) (line F).locallyFree
  exact (chartCotangentIso F k).hom ≫ StandardConicLocal.chartMap F k ≫
    (DualFrame.ofFrame (chartLineFrame F k)).inv ≫
      (asIso (dualBaseChange (modelMap F k) (line F).sheaf)).inv

/-- Reading the constructed map back in the actual cotangent and line frames
recovers the original normalized affine functional, with no extra scalar. -/
theorem localMap_scalar (k : Fin 3) :
    (chartCotangentIso F k).inv ≫ localMap F k ≫
      dualBaseChange (modelMap F k) (line F).sheaf ≫
        (DualFrame.ofFrame (chartLineFrame F k)).hom =
          StandardConicLocal.chartMap F k := by
  letI := dualBaseChange_isIso (modelMap F k) (line F).locallyFree
  simp [localMap, Category.assoc]

/-- Evaluation on any of the original four homogeneous sections reads the
local functional times precisely that section's prescribed frame coordinate.
This permits comparison on an overlap using one common global section. -/
theorem localMap_evaluateCoordinate (k : Fin 3) (i j : Fin 2) :
    localMap F k ≫
        (Scheme.Modules.pullback (modelMap F k)).map
          (LineEvaluation.atSection (coordinate F i j)) ≫
        unitPullbackMap (modelMap F k) =
      (chartCotangentIso F k).hom ≫ StandardConicLocal.chartMap F k ≫
        scalarSection (coefficient (leftIndex k) i (planeFunction (leftPolynomial k)) *
          coefficient (rightIndex k) j (planeFunction (rightPolynomial k))) := by
  letI := dualBaseChange_isIso (modelMap F k) (line F).locallyFree
  rw [LineEvaluation.pullback]
  rw [LineEvaluation.atSection_frame (chartLineFrame F k)
    (pullSection (modelMap F k) (coordinate F i j)) _
    (chartLineFrame_coordinate F k i j)]
  simp [localMap, Category.assoc]

def localOverMap (k : Fin 3) :
    (cotangentSheaf F.parameter).over (chart F k) ⟶
      (dualSheaf (line F).sheaf).over (chart F k) :=
  (atlasHomEquiv F _ _ k).symm (localMap F k)

def toChart (W : F.source.Opens) (k : Fin 3) (h : W ≤ chart F k) :
    W.toScheme ⟶ Plane := F.source.homOfLE h ≫ (chartIso F k).hom

instance toChart_isOpenImmersion (W : F.source.Opens) (k : Fin 3)
    (h : W ≤ chart F k) : IsOpenImmersion (toChart F W k h) := by
  unfold toChart
  infer_instance

@[reassoc] theorem toChart_model (W : F.source.Opens) (k : Fin 3)
    (h : W ≤ chart F k) : toChart F W k h ≫ modelMap F k = W.ι := by
  change (F.source.homOfLE h ≫ chartToModel F k) ≫ modelMap F k = W.ι
  rw [Category.assoc, ConicOverlapCoordinates.chartToModel_modelMap]
  exact F.source.homOfLE_ι h

theorem toChart_toOpen (W : F.source.Opens) (k : Fin 3)
    (h : W ≤ chart F k) :
    toChart F W k h ≫ (chartIso F k).inv = F.source.homOfLE h := by
  simp [toChart, Category.assoc]

def restrictedMap (W : F.source.Opens) (k : Fin 3) (h : W ≤ chart F k) :
    pullbackModule W.ι (cotangentSheaf F.parameter) ⟶
      pullbackModule W.ι (dualSheaf (line F).sheaf) :=
  normalize W.ι (openHomEquiv _ _ W
    (restrictOverHom (homOfLE h) (localOverMap F k)))

/-- The selected chart map and literal restriction of the over-site map
have the same original pullback normalization. -/
theorem restrictedMap_spec (W : F.source.Opens) (k : Fin 3) (h : W ≤ chart F k) :
    restrictedMap F W k h =
      pullMapAlong (toChart F W k h) (modelMap F k) W.ι
        (toChart_model F W k h) (localMap F k) := by
  unfold restrictedMap
  rw [chartRestriction _ _ (chart F k) W h (chartIso F k).symm (modelMap F k)
    (modelToChart_inclusion F k) (toChart F W k h)
    (toChart_toOpen F W k h) (toChart_model F W k h)]
  change pullMapAlong _ _ _ _ (atlasHomEquiv F _ _ k (localOverMap F k)) = _
  rw [localOverMap, Equiv.apply_symm_apply]

/-- Read a transported local map against an original homogeneous section.
Its scalar is the affine functional times the actual coordinate ratio. -/
theorem transportedMap_evaluateCoordinate {T : Scheme} (k : Fin 3)
    (f : T ⟶ Plane) [IsOpenImmersion f] (v : T ⟶ F.source)
    (h : f ≫ modelMap F k = v) (i j : Fin 2) :
    pullMapAlong f (modelMap F k) v h (localMap F k) ≫
        (Scheme.Modules.pullback v).map (LineEvaluation.atSection (coordinate F i j)) ≫
        unitPullbackMap v =
      cotangentMap v F.parameter ≫
        ConicScalarCompatibility.scalarOn F k f (v ≫ F.parameter)
          (by rw [← Category.assoc, h]) ≫
        scalarSection (f.appTop
          (coefficient (leftIndex k) i (planeFunction (leftPolynomial k)) *
            coefficient (rightIndex k) j (planeFunction (rightPolynomial k)))) := by
  subst v
  rw [pullMapAlong_rfl, pullMap_evaluate, localMap_evaluateCoordinate]
  change (Scheme.Modules.pullbackComp f (modelMap F k)).inv.app
      (cotangentSheaf F.parameter) ≫
      (Scheme.Modules.pullback f).map
        (cotangentMap (modelMap F k) F.parameter ≫ StandardConicLocal.chartMap F k ≫
          scalarSection (coefficient (leftIndex k) i (planeFunction (leftPolynomial k)) *
            coefficient (rightIndex k) j (planeFunction (rightPolynomial k)))) ≫
      unitPullbackMap f = _
  exact ConicScalarCompatibility.composition_functional_scalar f (modelMap F k)
    F.parameter (StandardConicLocal.chartMap F k) _

/-- The common evaluation used to compare overlaps is invertible wherever
the map factors through the node chart. This follows from the original
homogeneous generator, with every pullback comparison retained. -/
theorem evaluateNode_isIso {T : Scheme} (a : T ⟶ Plane) (v : T ⟶ F.source)
    (h : a ≫ modelMap F 0 = v) :
    IsIso ((Scheme.Modules.pullback v).map
      (LineEvaluation.atSection (coordinate F 0 0)) ≫ unitPullbackMap v) := by
  letI := dualBaseChange_isIso v (line F).locallyFree
  have hg := chartLineFrame_generator F 0
  change pullSection (modelMap F 0) (coordinate F 0 0) = (chartLineFrame F 0).inv at hg
  have hs := compositionPullback_sections a (modelMap F 0) v h (coordinate F 0 0)
  rw [hg] at hs
  letI : IsIso (pullSection a (chartLineFrame F 0).inv) := by
    dsimp [pullSection, restrictSection]
    infer_instance
  letI : IsIso (pullSection v (coordinate F 0 0)) := by
    rw [← hs]
    infer_instance
  rw [LineEvaluation.pullback]
  infer_instance

theorem restricted_node_left (W : F.source.Opens)
    (h₀ : W ≤ chart F 0) (h₁ : W ≤ chart F 1) :
    restrictOverHom (homOfLE h₀) (localOverMap F 0) =
      restrictOverHom (homOfLE h₁) (localOverMap F 1) := by
  apply (openHomEquiv _ _ W).injective
  apply normalize_injective W.ι
  change restrictedMap F W 0 h₀ = restrictedMap F W 1 h₁
  rw [restrictedMap_spec, restrictedMap_spec]
  letI := evaluateNode_isIso F (toChart F W 0 h₀) W.ι (toChart_model F W 0 h₀)
  apply (cancel_mono ((Scheme.Modules.pullback W.ι).map
    (LineEvaluation.atSection (coordinate F 0 0)) ≫ unitPullbackMap W.ι)).mp
  rw [transportedMap_evaluateCoordinate, transportedMap_evaluateCoordinate]
  have hc := ConicScalarCompatibility.node_left_common F
    (toChart F W 0 h₀) (toChart F W 1 h₁)
    (by rw [toChart_model, toChart_model]) (W.ι ≫ F.parameter)
    (by rw [← Category.assoc, toChart_model])
    (by rw [← Category.assoc, toChart_model])
  simpa [leftIndex, rightIndex, coefficient, leftPolynomial, rightPolynomial,
    scalarSection_one, Category.assoc, ConicOverlapCoordinates.value] using
    congrArg (fun q => cotangentMap W.ι F.parameter ≫ q) hc

theorem restricted_node_right (W : F.source.Opens)
    (h₀ : W ≤ chart F 0) (h₂ : W ≤ chart F 2) :
    restrictOverHom (homOfLE h₀) (localOverMap F 0) =
      restrictOverHom (homOfLE h₂) (localOverMap F 2) := by
  apply (openHomEquiv _ _ W).injective
  apply normalize_injective W.ι
  change restrictedMap F W 0 h₀ = restrictedMap F W 2 h₂
  rw [restrictedMap_spec, restrictedMap_spec]
  letI := evaluateNode_isIso F (toChart F W 0 h₀) W.ι (toChart_model F W 0 h₀)
  apply (cancel_mono ((Scheme.Modules.pullback W.ι).map
    (LineEvaluation.atSection (coordinate F 0 0)) ≫ unitPullbackMap W.ι)).mp
  rw [transportedMap_evaluateCoordinate, transportedMap_evaluateCoordinate]
  have hc := ConicScalarCompatibility.node_right_common F
    (toChart F W 0 h₀) (toChart F W 2 h₂)
    (by rw [toChart_model, toChart_model]) (W.ι ≫ F.parameter)
    (by rw [← Category.assoc, toChart_model])
    (by rw [← Category.assoc, toChart_model])
  simpa [leftIndex, rightIndex, coefficient, leftPolynomial, rightPolynomial,
    scalarSection_one, Category.assoc, ConicOverlapCoordinates.value] using
    congrArg (fun q => cotangentMap W.ι F.parameter ≫ q) hc

/-- The precise gluing equation on the actual intersections of the three
homogeneous-coordinate opens. It is proved below; no compatibility is admitted. -/
def Compatible : Prop :=
  ∀ i j : Fin 3,
    restrictOverHom (homOfLE (inf_le_left : chart F i ⊓ chart F j ≤ chart F i))
      (localOverMap F i) =
    restrictOverHom (homOfLE (inf_le_right : chart F i ⊓ chart F j ≤ chart F j))
      (localOverMap F j)

theorem outer_intersection_le_node : chart F 1 ⊓ chart F 2 ≤ chart F 0 := by
  intro x hx
  change (F.left x ∈ Smoothing.CoordinateCharts.ratioOpen 1 ∧
      F.right x ∈ Smoothing.CoordinateCharts.ratioOpen 0) ∧
    (F.left x ∈ Smoothing.CoordinateCharts.ratioOpen 0 ∧
      F.right x ∈ Smoothing.CoordinateCharts.ratioOpen 1) at hx
  exact ⟨hx.2.1, hx.1.2⟩

/-- All nine restrictions agree. The two nontrivial node/outer calculations
are the actual cotangent identities above; the outer/outer overlap lies
inside the node chart, so their equality follows by transitivity there. -/
theorem compatible : Compatible F := by
  intro i j
  fin_cases i <;> fin_cases j
  · rfl
  · exact restricted_node_left F _ inf_le_left inf_le_right
  · exact restricted_node_right F _ inf_le_left inf_le_right
  · exact (restricted_node_left F _ inf_le_right inf_le_left).symm
  · rfl
  · exact (restricted_node_left F _ (outer_intersection_le_node F) inf_le_left).symm.trans
      (restricted_node_right F _ (outer_intersection_le_node F) inf_le_right)
  · exact (restricted_node_right F _ inf_le_right inf_le_left).symm
  · have hnode : chart F 2 ⊓ chart F 1 ≤ chart F 0 := by
      rw [inf_comm]
      exact outer_intersection_le_node F
    exact (restricted_node_right F _ hnode inf_le_left).symm.trans
      (restricted_node_left F _ hnode inf_le_right)
  · rfl

def glued (h : Compatible F) :
    cotangentSheaf F.parameter ⟶ dualSheaf (line F).sheaf :=
  glueOverHom (chart F) (threeCharts_cover F) (localOverMap F) h

theorem glued_pullback (h : Compatible F) (k : Fin 3) :
    (Scheme.Modules.pullback (modelMap F k)).map (glued F h) = localMap F k := by
  rw [← atlasHomEquiv_global]
  change atlasHomEquiv F _ _ k
    ((SheafOfModules.overFunctor F.source.ringCatSheaf (chart F k)).map
      (glueOverHom (chart F) (threeCharts_cover F) (localOverMap F) h)) = _
  rw [glueOverHom_local]
  exact (atlasHomEquiv F _ _ k).apply_symm_apply (localMap F k)

theorem glued_chartScalar (h : Compatible F) (k : Fin 3) :
    chartForm F (glued F h) k ≫ (DualFrame.ofFrame (chartLineFrame F k)).hom =
      StandardConicLocal.chartMap F k := by
  simp only [chartForm, Category.assoc, glued_pullback]
  exact localMap_scalar F k

/-- The literal three lists of polynomial coefficients agree with the
pre-existing requested chartLogValue, including the two outer signs. -/
theorem coefficient_eq_logValue (k : Fin 3) (i : Fin 2) :
    planeFunction (ConicLogAlgebra.coefficient ℂ k i) = chartLogValue k i := by
  fin_cases k <;> fin_cases i <;>
    simp [ConicLogAlgebra.coefficient, chartLogValue, planeFunction]

theorem glued_chartCoefficient (h : Compatible F) (k : Fin 3) (i : Fin 2) :
    chartCoefficient F (glued F h) k i = chartLogValue k i := by
  have hq := congrArg
    (fun q : cotangentSheaf (modelMap F k ≫ F.parameter) ⟶ structureModule Plane =>
      q.app ⊤ ((cotangentPresentation (modelMap F k ≫ F.parameter)).differential.apply ⊤
        (planeFunction (MvPolynomial.X i)))) (glued_chartScalar F h k)
  change (DualFrame.ofFrame (chartLineFrame F k)).hom.app ⊤
      ((chartForm F (glued F h) k).app ⊤
        ((cotangentPresentation (modelMap F k ≫ F.parameter)).differential.apply ⊤
          (planeFunction (MvPolynomial.X i)))) = _ at hq
  rw [DualFrame.ofFrame_apply, StandardConicLocal.chartMap_coordinate] at hq
  exact hq.trans (coefficient_eq_logValue k i)

/-- Assembly from an explicit compatibility proof, with exactly the original
requested maps, frames, variables and signs. -/
theorem fundamentalClass_of_compatibleCharts (h : Compatible F) :
    ∃ q : cotangentSheaf F.parameter ⟶ dualSheaf (line F).sheaf,
      ∀ (k : Fin 3) (i : Fin 2), chartCoefficient F q k i = chartLogValue k i :=
  ⟨glued F h, glued_chartCoefficient F h⟩

/-- An actual global fundamental-class morphism, normalized in all three
original charts and their fixed homogeneous O(1,1) generators. -/
theorem fundamentalClass_exists :
    ∃ q : cotangentSheaf F.parameter ⟶ dualSheaf (line F).sheaf,
      ∀ (k : Fin 3) (i : Fin 2), chartCoefficient F q k i = chartLogValue k i :=
  fundamentalClass_of_compatibleCharts F (compatible F)

end LeBrunSalamon.Construction.StandardConicConstruction
end

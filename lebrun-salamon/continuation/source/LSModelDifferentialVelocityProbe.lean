import LSModelBivector

/-!
# The actual logarithmic source differential in the node frame

Every comparison in this file uses the original cotangent differential,
its canonical pullback maps, and the fixed normalized source bivector.
-/

noncomputable section
set_option autoImplicit false

-- BEGIN MODEL_VELOCITY_PROBE_OPTIONS
set_option Elab.async false
set_option stderrAsMessages false
set_option profiler true
-- END MODEL_VELOCITY_PROBE_OPTIONS
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseSeven LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentySix LeBrunSalamon.PhaseTwentySeven
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirty LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.Core LeBrunSalamon.Skeleton LeBrunSalamon.Refinement
open LeBrunSalamon.Core.ExternalTensorCoordinates
open LeBrunSalamon.Refinement.Jets LeBrunSalamon.LocalFrames
open LeBrunSalamon.P1Charts LeBrunSalamon.P1TwistFrames
open scoped BigOperators

namespace LeBrunSalamon.Construction.SourceBivectorCoordinates

open Smoothing.CoordinateCharts Smoothing.SourceAffineCharts

theorem quadratic_second (q : Polynomial ℂ) (hq : q.natDegree ≤ 2) :
    q.derivative.derivative = Polynomial.C (2 * q.coeff 2) := by
  have he : q = Polynomial.C (q.coeff 0) + Polynomial.C (q.coeff 1) * Polynomial.X +
      Polynomial.C (q.coeff 2) * Polynomial.X^2 := by
    simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      pow_zero, mul_one, pow_one] using
      q.as_sum_range_C_mul_X_pow' (show q.natDegree < 3 by omega)
  conv_lhs => rw [he]
  simp only [Polynomial.derivative_add, Polynomial.derivative_C,
    Polynomial.derivative_C_mul_X, Polynomial.derivative_C_mul_X_sq,
    Polynomial.derivative_zero, zero_add, add_zero]
  congr 1
  ring

/-- The second diagonal symbol constructs an actual global tangent
section whose canonical affine coefficient is one. -/
theorem constant_combination :
    (∑ i, Polynomial.C ((right i).coeff 2) * left i) = 1 := by
  have h : (2 : Polynomial ℂ) *
      (∑ i, Polynomial.C ((right i).coeff 2) * left i) = 2 := by
    calc
      _ = ∑ i, left i * (right i).derivative.derivative := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [quadratic_second (right i) (polynomial_natDegree_le (expansion.right i))]
        simp only [map_mul, map_ofNat]
        ring
      _ = 2 := polynomial_second
  apply mul_left_cancel₀ (show (2 : Polynomial ℂ) ≠ 0 by norm_num)
  simpa only [mul_one] using h

def coordinateSection : AlgebraicSection TangentLine.sheaf :=
  ∑ i, expansion.left i ≫ GlobalScalars.scalarEnd TangentLine.sheaf
    (constants P.structureMap ⊤ ((right i).coeff 2))

theorem polynomial_scalar (s : AlgebraicSection TangentLine.sheaf) (c : ℂ) :
    polynomial (s ≫ GlobalScalars.scalarEnd TangentLine.sheaf
      (constants P.structureMap ⊤ c)) = Polynomial.C c * polynomial s := by
  let lc : SectionsOn TangentLine.sheaf U ≃ₗ[RingSections ProjectiveLine U]
      RingSections ProjectiveLine U := frame.coefficient
  change polynomialChartRingEquiv 0 (lc
    ((GlobalScalars.scalarEnd TangentLine.sheaf (constants P.structureMap ⊤ c)).app U
      (Scheme.Modules.Hom.app s U (1 : RingSections ProjectiveLine U)))) = _
  rw [GlobalScalars.scalarEnd_app, constants_restrict, map_smul, smul_eq_mul, map_mul]
  have hc : polynomialChartRingEquiv 0 (constants P.structureMap U c) = Polynomial.C c :=
    polynomialChartRingEquiv_canonical_constant 0 c
  exact congrArg (fun z : Polynomial ℂ => z * polynomial s) hc

theorem coordinateSection_polynomial : polynomial coordinateSection = 1 := by
  change chartAlgebraEquiv ((ScalarSections.coefficientAddHom frame)
    (∑ i, expansion.left i ≫ GlobalScalars.scalarEnd TangentLine.sheaf
      (constants P.structureMap ⊤ ((right i).coeff 2)))) = 1
  rw [map_sum, map_sum]
  change (∑ i, polynomial (expansion.left i ≫ GlobalScalars.scalarEnd TangentLine.sheaf
    (constants P.structureMap ⊤ ((right i).coeff 2)))) = 1
  simp_rw [polynomial_scalar]
  exact constant_combination

theorem coordinateSection_coefficient : frame.localCoefficient coordinateSection = 1 := by
  apply chartAlgebraEquiv.injective
  simpa only [polynomial, map_one] using coordinateSection_polynomial

namespace TestMaps

open PointFrame.LocalFrameJetProof

/-- The actual local differential dz, pulled and then restricted to
the whole affine test scheme. -/
def coordinateDifferential {T : Scheme} (f : T ⟶ ProjectiveLine)
    (hU : ⊤ ≤ f ⁻¹ᵁ U) :
    GlobalSections (pullbackModule f (cotangentSheaf P.structureMap)) :=
  (pullbackModule f (cotangentSheaf P.structureMap)).presheaf.map (homOfLE hU).op
    (pullLocalSection f (cotangentSheaf P.structureMap) U
      ((cotangentPresentation P.structureMap).differential.apply U coordinate))

/-- The pulled frame coefficient is exactly evaluation on the actual
pulled dz.  It is not an independent scalar normalization. -/
theorem pulledCoefficient_pairing {T : Scheme} (f : T ⟶ ProjectiveLine)
    (hU : ⊤ ≤ f ⁻¹ᵁ U)
    (v : GlobalSections (pullbackModule f TangentLine.sheaf)) :
    pulledCoefficient f hU v =
      (Lines.PositiveVelocityPairing.pulledEvaluation f P.structureMap).apply ⊤
        v (coordinateDifferential f hU) := by
  let v₀ : GlobalSections (pullbackModule f TangentLine.sheaf) :=
    (pullbackModule f TangentLine.sheaf).presheaf.map (homOfLE hU).op
      (pullLocalSection f TangentLine.sheaf U coordinateVector)
  have hv₀ : pulledCoefficient f hU v₀ = 1 := by
    have hlocal := coefficientOn_local frame f ⊤ hU (1 : RingSections ProjectiveLine U)
    change pulledCoefficient f hU v₀ =
      f.appLE U ⊤ hU (1 : RingSections ProjectiveLine U) at hlocal
    simpa only [map_one] using hlocal
  have hv : v = (pulledCoefficient f hU v) • v₀ := by
    apply (pulledCoefficient f hU).injective
    rw [map_smul, hv₀, smul_eq_mul, mul_one]
  let b := Lines.PositiveVelocityPairing.pulledEvaluation f P.structureMap
  have hp : b.apply (f ⁻¹ᵁ U)
      (pullLocalSection f TangentLine.sheaf U coordinateVector)
      (pullLocalSection f (cotangentSheaf P.structureMap) U
        ((cotangentPresentation P.structureMap).differential.apply U coordinate)) =
          (1 : RingSections T (f ⁻¹ᵁ U)) := by
    change (unitPullbackMap f).app (f ⁻¹ᵁ U)
      ((pullbackPair f (dualEvaluation (cotangentSheaf P.structureMap))).apply (f ⁻¹ᵁ U)
        (pullLocalSection f (dualSheaf (cotangentSheaf P.structureMap)) U coordinateVector)
        (pullLocalSection f (cotangentSheaf P.structureMap) U
          ((cotangentPresentation P.structureMap).differential.apply U coordinate))) =
            (1 : RingSections T (f ⁻¹ᵁ U))
    rw [pullbackPair_normalized, ContactDerivativeIsoProof.unitPullbackMap_pullLocalSection]
    change f.app U (frame.coefficient coordinateVector) = 1
    rw [coordinateVector_coefficient, map_one]
  have hn := b.naturality (homOfLE hU)
    (pullLocalSection f TangentLine.sheaf U coordinateVector)
    (pullLocalSection f (cotangentSheaf P.structureMap) U
      ((cotangentPresentation P.structureMap).differential.apply U coordinate))
  change T.presheaf.map (homOfLE hU).op
    (b.apply (f ⁻¹ᵁ U)
      (pullLocalSection f TangentLine.sheaf U coordinateVector)
      (pullLocalSection f (cotangentSheaf P.structureMap) U
        ((cotangentPresentation P.structureMap).differential.apply U coordinate))) =
      b.apply ⊤ v₀ (coordinateDifferential f hU) at hn
  rw [hp, map_one] at hn
  have hpair : b.apply ⊤ v₀ (coordinateDifferential f hU) =
      (1 : RingSections T ⊤) := hn.symm
  conv_rhs => rw [hv]
  change _ = b.apply ⊤ ((pulledCoefficient f hU v) • v₀) (coordinateDifferential f hU)
  rw [map_smul, LinearMap.smul_apply, hpair, smul_eq_mul, mul_one]

theorem frameIso_generator {T : Scheme} [IsAffine T] (f : T ⟶ ProjectiveLine)
    (hU : ⊤ ≤ f ⁻¹ᵁ U) : pullSection f coordinateSection = (frameIso f hU).inv := by
  apply (cancel_mono (frameIso f hU).hom).mp
  rw [frameIso_section, coordinateSection_coefficient, map_one,
    scalarSection_one, Iso.inv_hom_id]

end TestMaps

end LeBrunSalamon.Construction.SourceBivectorCoordinates

namespace LeBrunSalamon.Construction.LogVelocity

open StandardConicDifferential ContactDerivativeIsoProof
open Smoothing.CoordinateCharts Smoothing.SourceAffineCharts

/-- Differentiation into a smooth target, followed by an actual source
fundamental form and transposition. -/
def fromForm {S B : Scheme} (pi : S ⟶ B) (sB : B ⟶ ComplexBase)
    (M : OModule S) (q : cotangentSheaf pi ⟶ dualSheaf M)
    {d : ℕ} (X : SmoothProperComplexVariety d) (e : S ⟶ X.scheme)
    (he : e ≫ X.structureMap = pi ≫ sB) :
    M ⟶ pullbackModule e (tangentSheaf X.structureMap) := by
  letI := dualBaseChange_isIso e (smooth_cotangent_rank X.structureMap d X.smooth)
  exact transpose (RelativeDifferential.cotangent pi X.structureMap e sB he ≫ q) ≫
    inv (dualBaseChange e (cotangentSheaf X.structureMap))

@[reassoc]
theorem fromForm_normalized {S B : Scheme} (pi : S ⟶ B) (sB : B ⟶ ComplexBase)
    (M : OModule S) (q : cotangentSheaf pi ⟶ dualSheaf M)
    {d : ℕ} (X : SmoothProperComplexVariety d) (e : S ⟶ X.scheme)
    (he : e ≫ X.structureMap = pi ≫ sB) :
    fromForm pi sB M q X e he ≫ dualBaseChange e (cotangentSheaf X.structureMap) =
      transpose (RelativeDifferential.cotangent pi X.structureMap e sB he ≫ q) := by
  letI := dualBaseChange_isIso e (smooth_cotangent_rank X.structureMap d X.smooth)
  simp only [fromForm, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-- The relative chain rule also holds after restricting a local
function to any smaller test open. -/
theorem cotangent_differentialLE {S B Y A : Scheme}
    (pi : S ⟶ B) (sY : Y ⟶ A) (e : S ⟶ Y) (b : B ⟶ A)
    (he : e ≫ sY = pi ≫ b) (U : Y.Opens) (V : S.Opens)
    (hV : V ≤ e ⁻¹ᵁ U) (z : RingSections Y U) :
    (RelativeDifferential.cotangent pi sY e b he).app V
      ((pullbackModule e (cotangentSheaf sY)).presheaf.map (homOfLE hV).op
        (pullLocalSection e (cotangentSheaf sY) U
          ((cotangentPresentation sY).differential.apply U z))) =
      (cotangentPresentation pi).differential.apply V (e.appLE U V hV z) := by
  rw [← sheafHom_naturality, RelativeDifferential.cotangent_differential]
  exact (cotangentPresentation pi).differential.naturality (homOfLE hV) (e.app U z)

theorem fromForm_coefficient {S B : Scheme} [IsAffine S]
    (pi : S ⟶ B) (sB : B ⟶ ComplexBase)
    (M : OModule S) (q : cotangentSheaf pi ⟶ dualSheaf M)
    (e : S ⟶ ProjectiveLine) (he : e ≫ Lines.P.structureMap = pi ≫ sB)
    (hU : ⊤ ≤ e ⁻¹ᵁ SourceBivectorCoordinates.U) (m : AlgebraicSection M) :
    m ≫ fromForm pi sB M q (projectiveLineVariety Lines.P) e he ≫
      (SourceBivectorCoordinates.TestMaps.frameIso e hU).hom =
        scalarSection ((dualEvaluation M).apply ⊤
          (q.app ⊤ ((cotangentPresentation pi).differential.apply ⊤
            (e.appLE SourceBivectorCoordinates.U ⊤ hU SourceBivectorCoordinates.coordinate)))
          (sectionValue m)) := by
  apply (sectionValue_bijective (structureModule S)).injective
  simp only [sectionValue_comp, scalarSection, sectionFromValue_spec]
  change (SourceBivectorCoordinates.TestMaps.frameIso e hU).hom.app ⊤
    ((fromForm pi sB M q (projectiveLineVariety Lines.P) e he).app ⊤ (sectionValue m)) = _
  rw [SourceBivectorCoordinates.TestMaps.frameIso_apply,
    SourceBivectorCoordinates.TestMaps.pulledCoefficient_pairing]
  change (unitPullbackMap e).app ⊤
    ((pullbackPair e (dualEvaluation (cotangentSheaf Lines.P.structureMap))).apply ⊤
      ((fromForm pi sB M q (projectiveLineVariety Lines.P) e he).app ⊤ (sectionValue m))
      (SourceBivectorCoordinates.TestMaps.coordinateDifferential e hU)) = _
  rw [← dualBaseChange_evaluate]
  have hn := congrArg (fun k : M ⟶
      dualSheaf (pullbackModule e (cotangentSheaf Lines.P.structureMap)) =>
        k.app ⊤ (sectionValue m))
    (fromForm_normalized pi sB M q (projectiveLineVariety Lines.P) e he)
  change (dualBaseChange e (cotangentSheaf Lines.P.structureMap)).app ⊤
    ((fromForm pi sB M q (projectiveLineVariety Lines.P) e he).app ⊤ (sectionValue m)) =
      (transpose (RelativeDifferential.cotangent pi Lines.P.structureMap e sB he ≫ q)).app ⊤
        (sectionValue m) at hn
  change (dualEvaluation (pullbackModule e (cotangentSheaf Lines.P.structureMap))).apply ⊤
      ((dualBaseChange e (cotangentSheaf Lines.P.structureMap)).app ⊤
        ((fromForm pi sB M q (projectiveLineVariety Lines.P) e he).app ⊤ (sectionValue m)))
      (SourceBivectorCoordinates.TestMaps.coordinateDifferential e hU) = _
  rw [hn, transpose_evaluate]
  change (dualEvaluation M).apply ⊤
    (q.app ⊤ ((RelativeDifferential.cotangent pi Lines.P.structureMap e sB he).app ⊤
      (SourceBivectorCoordinates.TestMaps.coordinateDifferential e hU))) (sectionValue m) = _
  rw [SourceBivectorCoordinates.TestMaps.coordinateDifferential, cotangent_differentialLE]

/-- Pullback of an actual source form through specified cotangent and
line comparisons. -/
def pulledForm {S B S' B' : Scheme} (pi : S ⟶ B) (pi' : S' ⟶ B')
    (r : S' ⟶ S) (M : OModule S) (M' : OModule S')
    (C : pullbackModule r (cotangentSheaf pi) ≅ cotangentSheaf pi')
    (L : pullbackModule r M ≅ M') (q : cotangentSheaf pi ⟶ dualSheaf M) :
    cotangentSheaf pi' ⟶ dualSheaf M' :=
  C.inv ≫ (Scheme.Modules.pullback r).map q ≫ dualBaseChange r M ≫ dualMap L.inv

/-- Actual logarithmic velocities commute with base change.  The only
cotangent identification allowed here is the specified canonical
relative differential of the commuting source square. -/
theorem fromForm_baseChange {S B S' B' : Scheme}
    (pi : S ⟶ B) (pi' : S' ⟶ B') (sB : B ⟶ ComplexBase)
    (r : S' ⟶ S) (b : B' ⟶ B) (hr : r ≫ pi = pi' ≫ b)
    (M : OModule S) (M' : OModule S')
    (C : pullbackModule r (cotangentSheaf pi) ≅ cotangentSheaf pi')
    (hC : C.hom = RelativeDifferential.cotangent pi' pi r b hr)
    (L : pullbackModule r M ≅ M') (q : cotangentSheaf pi ⟶ dualSheaf M)
    {d : ℕ} (X : SmoothProperComplexVariety d) (e : S ⟶ X.scheme)
    (he : e ≫ X.structureMap = pi ≫ sB)
    (he' : (r ≫ e) ≫ X.structureMap = pi' ≫ (b ≫ sB)) :
    fromForm pi' (b ≫ sB) M' (pulledForm pi pi' r M M' C L q) X (r ≫ e) he' =
      L.inv ≫ (Scheme.Modules.pullback r).map (fromForm pi sB M q X e he) ≫
        (Scheme.Modules.pullbackComp r e).hom.app (tangentSheaf X.structureMap) := by
  let Ω := cotangentSheaf X.structureMap
  let K := RelativeDifferential.cotangent pi X.structureMap e sB he
  let K' := RelativeDifferential.cotangent pi' X.structureMap (r ≫ e) (b ≫ sB) he'
  let A := (Scheme.Modules.pullbackComp r e).app Ω
  have hk : K' ≫ C.inv = A.inv ≫ (Scheme.Modules.pullback r).map K := by
    have hc := congrArg (fun k => k ≫ C.inv)
      (RelativeDifferential.cotangent_comp pi' pi X.structureMap r b e sB hr he he')
    rw [← hC] at hc
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at hc
    change A.hom ≫ (K' ≫ C.inv) = (Scheme.Modules.pullback r).map K at hc
    apply (cancel_epi A.hom).mp
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hc
  have hq : K' ≫ pulledForm pi pi' r M M' C L q =
      (A.inv ≫ ((Scheme.Modules.pullback r).map (K ≫ q) ≫
        dualBaseChange r M)) ≫ dualMap L.inv := by
    unfold pulledForm
    rw [← Category.assoc K' C.inv, hk]
    simp only [Functor.map_comp, Category.assoc]
  letI := dualBaseChange_isIso e (smooth_cotangent_rank X.structureMap d X.smooth)
  letI := dualBaseChange_isIso (r ≫ e) (smooth_cotangent_rank X.structureMap d X.smooth)
  apply (cancel_mono (dualBaseChange (r ≫ e) Ω)).mp
  rw [fromForm_normalized]
  change transpose (K' ≫ pulledForm pi pi' r M M' C L q) = _
  rw [hq]
  calc
    _ = L.inv ≫
        ((Scheme.Modules.pullback r).map (transpose (K ≫ q)) ≫
          dualBaseChange r (pullbackModule e Ω)) ≫ dualMap A.inv := by
      rw [transpose_dualMap, transpose_comp, ← transpose_pullback]
    _ = (L.inv ≫ (Scheme.Modules.pullback r).map (fromForm pi sB M q X e he) ≫
        (Scheme.Modules.pullbackComp r e).hom.app (tangentSheaf X.structureMap)) ≫
          dualBaseChange (r ≫ e) Ω := by
      simp only [fromForm, Functor.map_comp, Functor.map_inv, Category.assoc]
      rw [dualBaseChange_comp]
      simp only [K, Ω, A, Iso.app_inv, Category.assoc, IsIso.inv_hom_id_assoc]

/-- The same-base relative differential is the ordinary cotangent map
of the source morphism, with the identity-base transports removed. -/
theorem cotangent_sameBase {S B T : Scheme} (pi : S ⟶ B) (r : T ⟶ S)
    (hr : r ≫ pi = (r ≫ pi) ≫ 𝟙 B) :
    RelativeDifferential.cotangent (r ≫ pi) pi r (𝟙 B) hr = cotangentMap r pi := by
  apply RelativeDifferential.pulledCotangent_hom_ext r pi
  intro U z
  rw [RelativeDifferential.cotangent_differential, cotangentMap_differential]

/-- Scalar multiplication of a section commutes with actual pullback,
using the same unit comparison as `scalarSection_pullback`. -/
theorem pullSection_scalar {Y T : Scheme} (p : T ⟶ Y)
    {E : OModule Y} (c : RingSections Y ⊤) (s : AlgebraicSection E) :
    pullSection p (scalarSection c ≫ s) =
      scalarSection (p.appTop c) ≫ pullSection p s := by
  rw [pullSection_naturality, ← scalarSection_pullback p c]
  simp only [pullSection, restrictSection, Category.assoc, Iso.hom_inv_id_assoc]

/-- Triple composition for actual pulled sections over an arbitrary
test scheme. -/
theorem section_comp {T Y Z W : Scheme}
    (p : T ⟶ Y) (f : Y ⟶ Z) (g : Z ⟶ W)
    (h : Y ⟶ W) (hh : f ≫ g = h)
    (q : T ⟶ Z) (hq : p ≫ f = q)
    (x : T ⟶ W) (hx : p ≫ h = x) (hx' : q ≫ g = x)
    {E : OModule W} (s : AlgebraicSection (pullbackModule g E)) :
    pullSection p (pullSection f s ≫ (compositionPullback f g h hh E).hom) ≫
      (compositionPullback p h x hx E).hom =
        pullSection q s ≫ (compositionPullback q g x hx' E).hom := by
  rw [pullSection_naturality, Category.assoc,
    Descent.TotalLine.compositionPullback_assoc p f g h hh q hq x hx hx' E,
    ← Category.assoc, compositionPullback_sections]

end LeBrunSalamon.Construction.LogVelocity

namespace LeBrunSalamon.Construction.SourceBivectorCoordinates.TestMaps

open Smoothing.CoordinateCharts Smoothing.SourceAffineCharts

/-- Exact coefficient transport through arbitrary base change of a
test map.  The canonical affine generator is the pullback of the actual
global section constructed from the normalized second symbol. -/
theorem coefficient_pullback {Y T : Scheme} [IsAffine Y] [IsAffine T]
    (p : T ⟶ Y) (f : Y ⟶ ProjectiveLine) (g : T ⟶ ProjectiveLine)
    (hg : p ≫ f = g) (hU : ⊤ ≤ f ⁻¹ᵁ U) (hV : ⊤ ≤ g ⁻¹ᵁ U)
    (s : AlgebraicSection (pullbackModule f TangentLine.sheaf))
    (c : RingSections Y ⊤) (hs : s ≫ (frameIso f hU).hom = scalarSection c) :
    pullSection p s ≫ (compositionPullback p f g hg TangentLine.sheaf).hom ≫
      (frameIso g hV).hom = scalarSection (p.appTop c) := by
  have hs' : s = scalarSection c ≫ pullSection f coordinateSection := by
    apply (cancel_mono (frameIso f hU).hom).mp
    rw [hs, frameIso_generator f hU, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hs', LogVelocity.pullSection_scalar]
  rw [Category.assoc, ← Category.assoc (pullSection p (pullSection f coordinateSection)),
    compositionPullback_sections, frameIso_generator g hV, Iso.inv_hom_id, Category.comp_id]

end LeBrunSalamon.Construction.SourceBivectorCoordinates.TestMaps

namespace LeBrunSalamon.Construction.TraitContact.ModelDifferential

local notation "Model" => LeBrunSalamon.Construction.StableMaps.FormalArcs.Model

open StableMaps.FormalArcs
open Smoothing.CoordinateCharts Smoothing.SourceAffineCharts
open StandardConicDifferential ContactDerivativeIsoProof

variable (F : Smoothing.StandardSource)

def universalPoint : F.source ⟶ ProjectiveLine := F.left ≫ P1CoordinateGauge.iso.inv

theorem universalPoint_over : universalPoint F ≫ Lines.P.structureMap =
    F.parameter ≫ Smoothing.affineLineToC := by
  rw [universalPoint, Category.assoc, P1CoordinateGauge.iso_inverse_over, F.left_over]

def universalVelocity : (StandardConicDifferential.line F).sheaf ⟶
    pullbackModule (universalPoint F) (tangentSheaf Lines.P.structureMap) :=
  LogVelocity.fromForm F.parameter Smoothing.affineLineToC
    (StandardConicDifferential.line F).sheaf (StandardConicDifferential.fundamentalClass F)
    (projectiveLineVariety Lines.P) (universalPoint F) (universalPoint_over F)

def universalSection : AlgebraicSection
    (pullbackModule (universalPoint F) (tangentSheaf Lines.P.structureMap)) :=
  StandardConicDifferential.coordinate F 0 0 ≫ universalVelocity F

abbrev chartPoint : Plane ⟶ ProjectiveLine := modelMap F 0 ≫ universalPoint F

theorem chartPoint_equation : chartPoint F =
    polynomialLine (MvPolynomial.X 0) ≫ polynomialChartInclusion 0 := by
  change modelMap F 0 ≫ (F.left ≫ P1CoordinateGauge.iso.inv) = _
  rw [← Category.assoc, (modelMap_spec F 0).2.1]
  simp only [leftPolynomial, leftIndex, if_pos rfl, show (0 : Fin 3) ≠ 1 by decide,
    if_neg, Category.assoc]
  exact congrArg (fun k => polynomialLine (MvPolynomial.X 0) ≫ k)
    (P1CoordinateGauge.quotient_backward 0)

theorem chartPoint_mem : ⊤ ≤ chartPoint F ⁻¹ᵁ SourceBivectorCoordinates.U := by
  rw [chartPoint_equation]
  exact ModelBivector.polynomialPoint_mem _

theorem chartPoint_coordinate :
    (chartPoint F).appLE SourceBivectorCoordinates.U ⊤ (chartPoint_mem F)
      SourceBivectorCoordinates.coordinate = planeFunction (MvPolynomial.X 0) := by
  let value : {g : Plane ⟶ ProjectiveLine //
      ⊤ ≤ g ⁻¹ᵁ SourceBivectorCoordinates.U} → RingSections Plane ⊤ :=
    fun g => g.val.appLE SourceBivectorCoordinates.U ⊤ g.property
      SourceBivectorCoordinates.coordinate
  have hvalue := congrArg value
    (Subtype.ext (chartPoint_equation F) :
      (⟨chartPoint F, chartPoint_mem F⟩ : {g : Plane ⟶ ProjectiveLine //
        ⊤ ≤ g ⁻¹ᵁ SourceBivectorCoordinates.U}) =
      ⟨polynomialLine (MvPolynomial.X 0) ≫ polynomialChartInclusion 0,
        ModelBivector.polynomialPoint_mem (polynomialLine (MvPolynomial.X 0))⟩)
  have hcoord := ModelBivector.polynomialPoint_coordinate
    (polynomialLine (MvPolynomial.X 0))
    (ModelBivector.polynomialPoint_mem (polynomialLine (MvPolynomial.X 0)))
  rw [polynomialLine_parameter] at hcoord
  exact hvalue.trans hcoord

theorem chartPoint_over : chartPoint F ≫ Lines.P.structureMap =
    (modelMap F 0 ≫ F.parameter) ≫ Smoothing.affineLineToC := by
  rw [chartPoint, Category.assoc, universalPoint_over, Category.assoc]

def chartVelocity : pullbackModule (modelMap F 0) (StandardConicDifferential.line F).sheaf ⟶
    pullbackModule (chartPoint F) (tangentSheaf Lines.P.structureMap) :=
  LogVelocity.fromForm (modelMap F 0 ≫ F.parameter) Smoothing.affineLineToC
    (pullbackModule (modelMap F 0) (StandardConicDifferential.line F).sheaf)
    (chartForm F (StandardConicDifferential.fundamentalClass F) 0)
    (projectiveLineVariety Lines.P) (chartPoint F) (chartPoint_over F)

theorem chartVelocity_baseChange : chartVelocity F =
    (Scheme.Modules.pullback (modelMap F 0)).map (universalVelocity F) ≫
      (compositionPullback (modelMap F 0) (universalPoint F) (chartPoint F) rfl
        (tangentSheaf Lines.P.structureMap)).hom := by
  have hC : (chartCotangentIso F 0).hom =
      RelativeDifferential.cotangent (modelMap F 0 ≫ F.parameter) F.parameter
        (modelMap F 0) (𝟙 Smoothing.AffineLine) (by simp) := by
    rw [LogVelocity.cotangent_sameBase]
    rfl
  have h := LogVelocity.fromForm_baseChange F.parameter (modelMap F 0 ≫ F.parameter)
    Smoothing.affineLineToC (modelMap F 0) (𝟙 Smoothing.AffineLine) (by simp)
    (StandardConicDifferential.line F).sheaf
    (pullbackModule (modelMap F 0) (StandardConicDifferential.line F).sheaf)
    (chartCotangentIso F 0) hC (Iso.refl _)
    (StandardConicDifferential.fundamentalClass F) (projectiveLineVariety Lines.P)
    (universalPoint F) (universalPoint_over F)
    (by
      change chartPoint F ≫ Lines.P.structureMap =
        (modelMap F 0 ≫ F.parameter) ≫ ((𝟙 Smoothing.AffineLine) ≫ Smoothing.affineLineToC)
      simpa only [Category.id_comp] using chartPoint_over F)
  simp only [chartVelocity, universalVelocity, LogVelocity.pulledForm,
    chartForm, Category.id_comp, Iso.refl_inv, dualMap_id, Category.comp_id,
    compositionPullback, Iso.trans_hom, Iso.app_hom, eqToIso_refl,
    Iso.refl_hom] at h
  change chartVelocity F =
    (Scheme.Modules.pullback (modelMap F 0)).map (universalVelocity F) ≫
      (Scheme.Modules.pullbackComp (modelMap F 0) (universalPoint F)).hom.app
        (tangentSheaf Lines.P.structureMap) at h
  exact h

/-- The actual chart velocity sends the chosen O(1,1) generator to
u times the canonical d/du frame. -/
theorem chartVelocity_coefficient :
    (chartLineFrame F 0).inv ≫ chartVelocity F ≫
      (SourceBivectorCoordinates.TestMaps.frameIso (chartPoint F) (chartPoint_mem F)).hom =
        scalarSection (planeFunction (MvPolynomial.X 0)) := by
  rw [chartVelocity, LogVelocity.fromForm_coefficient, chartPoint_coordinate]
  change scalarSection (chartCoefficient F (StandardConicDifferential.fundamentalClass F) 0 0) = _
  rw [fundamentalClass_chartCoefficient]
  simp only [chartLogValue, if_pos rfl, if_true, if_false]

def chartSection : AlgebraicSection
    (pullbackModule (chartPoint F) (tangentSheaf Lines.P.structureMap)) :=
  pullSection (modelMap F 0) (universalSection F) ≫
    (compositionPullback (modelMap F 0) (universalPoint F) (chartPoint F) rfl
      (tangentSheaf Lines.P.structureMap)).hom

theorem chartSection_coefficient :
    chartSection F ≫
      (SourceBivectorCoordinates.TestMaps.frameIso (chartPoint F) (chartPoint_mem F)).hom =
        scalarSection (planeFunction (MvPolynomial.X 0)) := by
  have hg : pullSection (modelMap F 0) (StandardConicDifferential.coordinate F 0 0) =
      (chartLineFrame F 0).inv := by
    simpa only [leftIndex, rightIndex, show (0 : Fin 3) ≠ 1 by decide,
      show (0 : Fin 3) ≠ 2 by decide, if_neg, if_true, if_false] using chartLineFrame_generator F 0
  have ht := congrArg (fun k => (chartLineFrame F 0).inv ≫ k ≫
    (SourceBivectorCoordinates.TestMaps.frameIso (chartPoint F) (chartPoint_mem F)).hom)
    (chartVelocity_baseChange F)
  simpa only [chartSection, universalSection, pullSection_naturality, hg,
    Category.assoc] using ht.symm.trans (chartVelocity_coefficient F)

variable (a : Coefficients)

def modelPoint : Model F a ⟶ ProjectiveLine :=
  LogarithmicSource.toUniversal F a ≫ universalPoint F

theorem modelPoint_over : modelPoint F a ≫ Lines.P.structureMap =
    modelProjection F a ≫ toC := by
  rw [modelPoint, Category.assoc, universalPoint_over, ← Category.assoc,
    show LogarithmicSource.toUniversal F a ≫ F.parameter =
      modelProjection F a ≫ parameterMap a from pullback.condition,
    Category.assoc, parameterMap_toC]

def modelVelocity : (modelLine F a).sheaf ⟶
    pullbackModule (modelPoint F a) (tangentSheaf Lines.P.structureMap) :=
  LogarithmicSource.velocity F a (projectiveLineVariety Lines.P)
    (modelPoint F a) (modelPoint_over F a)


-- BEGIN MODEL_VELOCITY_PROBE_MARKER ENTER_GENERIC
#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "MODEL_VELOCITY_PROBE ENTER_GENERIC"
  err.flush
-- END MODEL_VELOCITY_PROBE_MARKER ENTER_GENERIC

/-- Normalize the source comparisons with an arbitrary target, so the
concrete projective-line specialization keeps these module maps opaque. -/
private theorem logarithmicVelocity_baseChange_generic
    {d : ℕ} (X : SmoothProperComplexVariety d) (e : F.source ⟶ X.scheme)
    (he : e ≫ X.structureMap = F.parameter ≫ Smoothing.affineLineToC)
    (he' : (LogarithmicSource.toUniversal F a ≫ e) ≫ X.structureMap =
      modelProjection F a ≫ toC) :
    LogarithmicSource.velocity F a X (LogarithmicSource.toUniversal F a ≫ e) he' =
      (LogarithmicSource.lineComparison F a).inv ≫
        (Scheme.Modules.pullback (LogarithmicSource.toUniversal F a)).map
          (LogVelocity.fromForm F.parameter Smoothing.affineLineToC
            (StandardConicDifferential.line F).sheaf
            (StandardConicDifferential.fundamentalClass F) X e he) ≫
          (compositionPullback (LogarithmicSource.toUniversal F a) e
            (LogarithmicSource.toUniversal F a ≫ e) rfl
            (tangentSheaf X.structureMap)).hom := by
  have h := LogVelocity.fromForm_baseChange F.parameter (modelProjection F a)
    Smoothing.affineLineToC (LogarithmicSource.toUniversal F a) (parameterMap a)
    pullback.condition (StandardConicDifferential.line F).sheaf (modelLine F a).sheaf
    (LogarithmicSource.cotangentComparison F a) rfl (LogarithmicSource.lineComparison F a)
    (StandardConicDifferential.fundamentalClass F) X e he
    (by simpa only [parameterMap_toC] using he')
  simpa only [LogarithmicSource.velocity, LogarithmicSource.targetCotangent,
    LogarithmicSource.fundamentalClass, LogVelocity.fromForm,
    LogVelocity.pulledForm, parameterMap_toC, asIso_inv, compositionPullback,
    Iso.trans_hom, Iso.app_hom, eqToIso_refl, Iso.refl_hom, Category.comp_id] using h


-- BEGIN MODEL_VELOCITY_PROBE_MARKER ENTER_SPECIALIZATION
#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "MODEL_VELOCITY_PROBE ENTER_SPECIALIZATION"
  err.flush
-- END MODEL_VELOCITY_PROBE_MARKER ENTER_SPECIALIZATION

theorem modelVelocity_baseChange : modelVelocity F a =
    (LogarithmicSource.lineComparison F a).inv ≫
      (Scheme.Modules.pullback (LogarithmicSource.toUniversal F a)).map (universalVelocity F) ≫
        (compositionPullback (LogarithmicSource.toUniversal F a) (universalPoint F)
          (modelPoint F a) rfl (tangentSheaf Lines.P.structureMap)).hom := by
  exact logarithmicVelocity_baseChange_generic F a (projectiveLineVariety Lines.P)
    (universalPoint F) (universalPoint_over F) (modelPoint_over F a)


-- BEGIN MODEL_VELOCITY_PROBE_MARKER EXIT_SPECIALIZATION
#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "MODEL_VELOCITY_PROBE EXIT_SPECIALIZATION"
  err.flush
-- END MODEL_VELOCITY_PROBE_MARKER EXIT_SPECIALIZATION


end LeBrunSalamon.Construction.TraitContact.ModelDifferential

end

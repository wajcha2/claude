import LSNodalTangent
import LSHamiltonianJets
import LSAffineFiberDivisibility

/-!
# The fixed-end first-order smoothing and its actual source maps

The parameter and endpoint conditions are imposed on the original chart
derivations. Their normalized dual-number lifts give an actual map from
the source with parameter epsilon, with constant endpoint maps. The
following calculations retain these maps before any local jet argument.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.PhaseThirty LeBrunSalamon.PhaseThirtyFour
open LeBrunSalamon.Core LeBrunSalamon.Skeleton
open LeBrunSalamon.Construction LeBrunSalamon.Construction.Lines

/-- The affine-module divisibility argument is proved using the quotient
`M/XM` as a separating target. The actual sheaf maps are supplied by the
tilde/Gamma and pullback/pushforward adjunctions, so the polynomial coordinate
and the given zero-section restriction retain their original normalization. -/
theorem LeBrunSalamon.PublishedInputs.Step3f.affineLine_section_divisible
    (E : LeBrunSalamon.PhaseOne.OModule
      LeBrunSalamon.Construction.Smoothing.AffineLine)
    [E.IsQuasicoherent]
    (a : LeBrunSalamon.PhaseOne.GlobalSections E)
    (ha : LeBrunSalamon.PhaseTwentyEight.pullSection
      (LeBrunSalamon.Construction.Smoothing.scalarPoint 0)
      (LeBrunSalamon.PhaseTwentyEight.sectionFromValue a) = 0) :
    ∃ b : LeBrunSalamon.PhaseOne.GlobalSections E,
      a = LeBrunSalamon.Construction.Smoothing.parameterFunction • b := by
  exact LeBrunSalamon.AffineFiberDivisibility.affineLine_section_divisible E a ha

/-- Project-facing specialization of the affine module quotient theorem. -/
theorem LeBrunSalamon.StandardInputs.affineLine_section_divisible
    (E : LeBrunSalamon.PhaseOne.OModule
      LeBrunSalamon.Construction.Smoothing.AffineLine)
    [E.IsQuasicoherent]
    (a : LeBrunSalamon.PhaseOne.GlobalSections E)
    (ha : LeBrunSalamon.PhaseTwentyEight.pullSection
      (LeBrunSalamon.Construction.Smoothing.scalarPoint 0)
      (LeBrunSalamon.PhaseTwentyEight.sectionFromValue a) = 0) :
    ∃ b : LeBrunSalamon.PhaseOne.GlobalSections E,
      a = LeBrunSalamon.Construction.Smoothing.parameterFunction • b := by
  exact LeBrunSalamon.PublishedInputs.Step3f.affineLine_section_divisible E a ha

/-- Classical finite-locally-free corollary of the square-zero module
filtration in Stacks Project, Section 91.4 (Tags 08L3 and 08L5), together
with the closed-immersion module equivalence of Lemma 29.4.1 (Tag 01QY).
The Hom sheaf from the pulled bundle E to F has two epsilon-filtration
subquotients equal to its restriction Hom(E,i*F). Their global sections
vanish by h, so every actual morphism vanishes. This is a derived classical
corollary, not a verbatim published lemma; no contact object is used. -/
theorem LeBrunSalamon.PublishedInputs.Step3f.dualThickening_hom_vanishing
    {Y : AlgebraicGeometry.Scheme} (sY : Y ⟶ LeBrunSalamon.PhaseOne.ComplexBase)
    {r q : ℕ}
    (E : LeBrunSalamon.PhaseOne.AlgebraicVectorBundle Y r)
    (F : LeBrunSalamon.PhaseOne.AlgebraicVectorBundle
      (LeBrunSalamon.Construction.Lines.DualThickening.space sY) q)
    (h : ∀ m : E.sheaf ⟶
      LeBrunSalamon.PhaseTwo.pullbackModule
        (LeBrunSalamon.Construction.Lines.DualThickening.zeroSection sY) F.sheaf,
      m = 0) :
    ∀ m : LeBrunSalamon.PhaseTwo.pullbackModule
        (LeBrunSalamon.Construction.Lines.DualThickening.projection sY) E.sheaf ⟶ F.sheaf,
      m = 0 := by
  sorry

/-- Project-facing specialization of the square-zero Hom-filtration vanishing theorem. -/
theorem LeBrunSalamon.StandardInputs.dualThickening_hom_vanishing
    {Y : AlgebraicGeometry.Scheme} (sY : Y ⟶ LeBrunSalamon.PhaseOne.ComplexBase)
    {r q : ℕ}
    (E : LeBrunSalamon.PhaseOne.AlgebraicVectorBundle Y r)
    (F : LeBrunSalamon.PhaseOne.AlgebraicVectorBundle
      (LeBrunSalamon.Construction.Lines.DualThickening.space sY) q)
    (h : ∀ m : E.sheaf ⟶
      LeBrunSalamon.PhaseTwo.pullbackModule
        (LeBrunSalamon.Construction.Lines.DualThickening.zeroSection sY) F.sheaf,
      m = 0) :
    ∀ m : LeBrunSalamon.PhaseTwo.pullbackModule
        (LeBrunSalamon.Construction.Lines.DualThickening.projection sY) E.sheaf ⟶ F.sheaf,
      m = 0 := by
  exact LeBrunSalamon.PublishedInputs.Step3f.dualThickening_hom_vanishing sY E F h

namespace LeBrunSalamon.CotangentBaseChange

/-- The canonical cotangent map in the actual Cartesian square, formed
from the original universal differential and its relative quotient. -/
def canonicalMap {Y S T : Scheme} (f : Y ⟶ S) (g : T ⟶ S) :
    pullbackModule (pullback.fst f g) (cotangentSheaf f) ⟶
      cotangentSheaf (pullback.snd f g) :=
  cotangentMap (pullback.fst f g) f ≫
    eqToHom (congrArg cotangentSheaf (pullback.condition (f := f) (g := g))) ≫
      cotangentToRelative (pullback.snd f g) g

/-- The base-change map sends the actual pullback of da to d(p*a).
This pins the map independently of any later invertibility theorem. -/
theorem canonicalMap_differential {Y S T : Scheme} (f : Y ⟶ S) (g : T ⟶ S)
    (U : Y.Opens) (a : RingSections Y U) :
    (canonicalMap f g).app ((pullback.fst f g) ⁻¹ᵁ U)
      (pullLocalSection (pullback.fst f g) (cotangentSheaf f) U
        ((cotangentPresentation f).differential.apply U a)) =
      (cotangentPresentation (pullback.snd f g)).differential.apply
        ((pullback.fst f g) ⁻¹ᵁ U) ((pullback.fst f g).app U a) := by
  change (cotangentToRelative (pullback.snd f g) g).app _
    ((eqToHom (congrArg cotangentSheaf (pullback.condition (f := f) (g := g)))).app _
      ((cotangentMap (pullback.fst f g) f).app _
        (pullLocalSection (pullback.fst f g) (cotangentSheaf f) U
          ((cotangentPresentation f).differential.apply U a)))) = _
  rw [ContactDerivativeIsoProof.cotangentMap_differential,
    ContactDerivativeIsoProof.differential_transport,
    CotangentTransitivityRederivedV02.cotangentToRelative_differential]
  exact pullback.condition

end LeBrunSalamon.CotangentBaseChange

/-- **Published input (exact).** Relative Kähler differentials commute
with arbitrary base change, for the canonical map in the Cartesian square.
This is Stacks Project, Lemma 29.33.10 (Tag 01V0). -/
theorem LeBrunSalamon.PublishedInputs.BaseChangeFibers.cotangentPullback_isIso
    {Y S T : AlgebraicGeometry.Scheme} (f : Y ⟶ S) (g : T ⟶ S) :
    IsIso (LeBrunSalamon.CotangentBaseChange.canonicalMap f g) := by
  sorry

/-- Project API wrapper for cotangent base change. -/
theorem LeBrunSalamon.StandardInputs.cotangentPullback_isIso
    {Y S T : AlgebraicGeometry.Scheme} (f : Y ⟶ S) (g : T ⟶ S) :
    IsIso (LeBrunSalamon.CotangentBaseChange.canonicalMap f g) :=
  LeBrunSalamon.PublishedInputs.BaseChangeFibers.cotangentPullback_isIso f g

namespace LeBrunSalamon.Refinement.FiniteCovectorExpression

variable {A : Type*} [CommRing A] [Algebra ℂ A]

/-- A covector on derivations is a finite sum of function multiples of
actual differentials. Finite projective duality supplies the differential;
the universal Kähler generators supply its finite expression. -/
theorem exists_fin
    [Module.Finite A (KaehlerDifferential ℂ A)]
    [Module.Projective A (KaehlerDifferential ℂ A)]
    (θ : Derivation ℂ A A →ₗ[A] A) :
    ∃ (m : ℕ) (a b : Fin m → A),
      ∀ D : Derivation ℂ A A, θ D = ∑ i, a i * D (b i) := by
  classical
  let e : Module.Dual A (KaehlerDifferential ℂ A) ≃ₗ[A] Derivation ℂ A A :=
    KaehlerDifferential.linearMapEquivDerivation ℂ A
  let φ : Module.Dual A (Module.Dual A (KaehlerDifferential ℂ A)) :=
    θ.comp e.toLinearMap
  let ω : KaehlerDifferential ℂ A :=
    (Module.evalEquiv A (KaehlerDifferential ℂ A)).symm φ
  have hω : ω ∈ Submodule.span A (Set.range (KaehlerDifferential.D ℂ A)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  obtain ⟨m, a, g, hg⟩ := Submodule.mem_span_set'.1 hω
  choose b hb using fun i : Fin m => (g i).property
  refine ⟨m, a, b, ?_⟩
  intro D
  have he : e D.liftKaehlerDifferential = D := e.apply_symm_apply D
  have hD : D.liftKaehlerDifferential ω = θ D := by
    have h := Module.apply_evalEquiv_symm_apply A (KaehlerDifferential ℂ A)
      D.liftKaehlerDifferential φ
    change D.liftKaehlerDifferential ω = θ (e D.liftKaehlerDifferential) at h
    simpa only [he] using h
  rw [← hD, ← hg, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_smul, ← hb i, Derivation.liftKaehlerDifferential_comp_D]
  rfl

theorem exists_fin_of_smooth [Algebra.Smooth ℂ A]
    (θ : Derivation ℂ A A →ₗ[A] A) :
    ∃ (m : ℕ) (a b : Fin m → A),
      ∀ D : Derivation ℂ A A, θ D = ∑ i, a i * D (b i) := by
  exact exists_fin θ

end LeBrunSalamon.Refinement.FiniteCovectorExpression

namespace LeBrunSalamon.Construction.Smoothing.FixedEndsProof

open Charts.AffineTangentLift Normalization.NodalTangent

/-- The original unit tangent of the parameter line supplies the actual
map from the dual-number scheme; its epsilon coefficient is proved below. -/
def epsilonParameter : Infinitesimal.DualScheme ⟶ AffineLine :=
  (lift BaseDifferentialProof.baseChart BaseDifferentialProof.unitDirection).map

@[reassoc] theorem epsilonParameter_over :
    epsilonParameter ≫ affineLineToC = Infinitesimal.dualToC :=
  (lift BaseDifferentialProof.baseChart BaseDifferentialProof.unitDirection).overC

@[reassoc] theorem epsilonParameter_origin :
    Infinitesimal.origin ≫ epsilonParameter = scalarPoint 0 :=
  (lift BaseDifferentialProof.baseChart BaseDifferentialProof.unitDirection).reduces

/-- The chosen smoothing parameter is epsilon itself, not an unspecified
nonzero multiple or a replacement first-order coordinate. -/
theorem epsilonParameter_function :
    epsilonParameter.appTop parameterFunction =
      (Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).inv Infinitesimal.epsilon := by
  change (lift BaseDifferentialProof.baseChart BaseDifferentialProof.unitDirection).map.appTop
    (show RingSections BaseDifferentialProof.baseChart.scheme ⊤ from parameterFunction) = _
  rw [lift_normalized]
  congr 1
  have hz : BaseDifferentialProof.baseChart.evaluation parameterFunction = 0 := by
    change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
      ((scalarPoint 0).appTop parameterFunction) = 0
    rw [SourceMarksProof.scalarPoint_zero_parameter, map_zero]
  change algebraMap ℂ Infinitesimal.Dual
      (BaseDifferentialProof.baseChart.evaluation parameterFunction) +
    Infinitesimal.epsilon * algebraMap ℂ Infinitesimal.Dual
      (BaseDifferentialProof.unitDirection.val parameterFunction) = Infinitesimal.epsilon
  rw [hz, BaseDifferentialProof.unitDirection_parameter, map_zero, map_one,
    zero_add, mul_one]

theorem baseTangent_eq_unit (v : BaseDifferentialProof.baseChart.Tangent)
    (hv : v.val parameterFunction = 1) : v = BaseDifferentialProof.unitDirection := by
  apply sub_eq_zero.mp
  apply (baseTangent_zero_iff (v - BaseDifferentialProof.unitDirection)).mpr
  change v.val parameterFunction - BaseDifferentialProof.unitDirection.val parameterFunction = 0
  rw [hv, BaseDifferentialProof.unitDirection_parameter, sub_self]

variable {n : ℕ} {X : ContactFanoManifold n} {D : SuitablePair X} (G : Germ D)

/-- The nonreduced Hom parameter determined by the original affine
tangent vector. -/
def homLiftMap (z : G.chart.Tangent) : Infinitesimal.DualScheme ⟶ G.hom.parameter :=
  (lift G.chart z).map ≫ G.inclusion

@[reassoc] theorem homLiftMap_origin (z : G.chart.Tangent) :
    Infinitesimal.origin ≫ homLiftMap G z = G.chart.point.val ≫ G.inclusion := by
  rw [homLiftMap, ← Category.assoc, (lift G.chart z).reduces]

theorem homLiftMap_base (z : G.chart.Tangent) (hz : G.baseDifferential z = 1) :
    homLiftMap G z ≫ G.hom.toBase = epsilonParameter := by
  change (lift G.chart z).map ≫ (BaseDifferentialProof.smoothingChartMap G).map = _
  rw [lift_natural]
  have h : (BaseDifferentialProof.smoothingChartMap G).differential z =
      BaseDifferentialProof.unitDirection :=
    baseTangent_eq_unit _ hz
  rw [h]
  rfl

/-- The hypothetical smoothing is a map from the actual base change of
the supplied conic source, evaluated through the full relative Hom map. -/
def deformedMap (z : G.chart.Tangent) (hz : G.baseDifferential z = 1) :
    SourceOver G.source epsilonParameter ⟶ X.variety.scheme :=
  sourceBaseChangeMap G.source epsilonParameter G.hom.toBase
    (homLiftMap G z) (homLiftMap_base G z hz) ≫ G.hom.evaluation

@[reassoc] theorem deformedMap_over (z : G.chart.Tangent) (hz : G.baseDifferential z = 1) :
    deformedMap G z hz ≫ X.variety.structureMap =
      pullback.snd G.source.parameter epsilonParameter ≫ Infinitesimal.dualToC := by
  rw [deformedMap, Category.assoc, G.hom.overC]
  simp only [sourceBaseChangeMap, pullback.lift_snd_assoc]
  rw [Category.assoc]
  rw [← Category.assoc (homLiftMap G z) G.hom.toBase affineLineToC,
    homLiftMap_base G z hz, epsilonParameter_over]

def firstBranch : ProjectiveLine ⟶ SourceOver G.source epsilonParameter :=
  pullback.lift G.marks.branchLeft (P.structureMap ≫ Infinitesimal.origin)
    (by rw [Category.assoc, epsilonParameter_origin, G.marks.left_base])

def secondBranch : ProjectiveLine ⟶ SourceOver G.source epsilonParameter :=
  pullback.lift G.marks.branchRight (P.structureMap ≫ Infinitesimal.origin)
    (by rw [Category.assoc, epsilonParameter_origin, G.marks.right_base])

@[reassoc] theorem firstBranch_reduction (z : G.chart.Tangent)
    (hz : G.baseDifferential z = 1) :
    firstBranch G ≫ deformedMap G z hz = D.first.curve.map := by
  change (firstBranch G ≫ sourceBaseChangeMap G.source epsilonParameter G.hom.toBase
    (homLiftMap G z) (homLiftMap_base G z hz)) ≫ G.hom.evaluation = _
  have h : firstBranch G ≫ sourceBaseChangeMap G.source epsilonParameter G.hom.toBase
      (homLiftMap G z) (homLiftMap_base G z hz) =
      pullback.lift G.marks.branchLeft (P.structureMap ≫ G.chart.point.val ≫ G.inclusion)
        (by rw [G.marks.left_base]; simp [Category.assoc, G.centre_base]) := by
    apply pullback.hom_ext
    · simp only [Category.assoc, sourceBaseChangeMap, pullback.lift_fst,
        firstBranch, pullback.lift_fst_assoc]
    · simp only [Category.assoc, sourceBaseChangeMap, pullback.lift_snd_assoc,
        firstBranch, pullback.lift_snd]
      rw [homLiftMap_origin]
  rw [h]
  exact G.leftCentral

@[reassoc] theorem secondBranch_reduction (z : G.chart.Tangent)
    (hz : G.baseDifferential z = 1) :
    secondBranch G ≫ deformedMap G z hz = D.second.curve.map := by
  change (secondBranch G ≫ sourceBaseChangeMap G.source epsilonParameter G.hom.toBase
    (homLiftMap G z) (homLiftMap_base G z hz)) ≫ G.hom.evaluation = _
  have h : secondBranch G ≫ sourceBaseChangeMap G.source epsilonParameter G.hom.toBase
      (homLiftMap G z) (homLiftMap_base G z hz) =
      pullback.lift G.marks.branchRight (P.structureMap ≫ G.chart.point.val ≫ G.inclusion)
        (by rw [G.marks.right_base]; simp [Category.assoc, G.centre_base]) := by
    apply pullback.hom_ext
    · simp only [Category.assoc, sourceBaseChangeMap, pullback.lift_fst,
        secondBranch, pullback.lift_fst_assoc]
    · simp only [Category.assoc, sourceBaseChangeMap, pullback.lift_snd_assoc,
        secondBranch, pullback.lift_snd]
      rw [homLiftMap_origin]
  rw [h]
  exact G.rightCentral

/-- The two actual marked sections of the epsilon-source. -/
def markLift (F : StandardSource) (m : AffineLine ⟶ F.source)
    (hm : m ≫ F.parameter = 𝟙 AffineLine) :
    Infinitesimal.DualScheme ⟶ SourceOver F epsilonParameter :=
  pullback.lift (epsilonParameter ≫ m) (𝟙 Infinitesimal.DualScheme)
    (by rw [Category.assoc, hm, Category.comp_id, Category.id_comp])

@[reassoc] theorem markLift_deformedMap (z : G.chart.Tangent)
    (hz : G.baseDifferential z = 1) (m : AffineLine ⟶ G.source.source)
    (hm : m ≫ G.source.parameter = 𝟙 AffineLine) :
    markLift G.source m hm ≫ deformedMap G z hz =
      homLiftMap G z ≫ markedEvaluation G.hom m hm := by
  change (markLift G.source m hm ≫ sourceBaseChangeMap G.source epsilonParameter
      G.hom.toBase (homLiftMap G z) (homLiftMap_base G z hz)) ≫ G.hom.evaluation =
    (homLiftMap G z ≫ pullback.lift (G.hom.toBase ≫ m) (𝟙 G.hom.parameter)
      (by simp [Category.assoc, hm])) ≫ G.hom.evaluation
  congr 1
  apply pullback.hom_ext
  · simp only [Category.assoc, sourceBaseChangeMap, pullback.lift_fst_assoc,
      markLift, pullback.lift_fst]
    rw [← Category.assoc, homLiftMap_base G z hz]
  · simp only [Category.assoc, sourceBaseChangeMap, pullback.lift_snd_assoc,
      markLift, pullback.lift_snd, Category.id_comp, Category.comp_id]

theorem firstEndpoint_constant (z : G.chart.Tangent)
    (he : G.endpointDifferential z = 0) :
    homLiftMap G z ≫ markedEvaluation G.hom G.marks.first G.marks.first_base =
      Infinitesimal.dualToC ≫ infinity.map ≫ D.first.curve.map := by
  have hz : G.firstEval.differential z = 0 := congrArg Prod.fst he
  have h := (differential_zero_iff G.firstEval z).mp hz
  have hh := congrArg (fun f => f ≫ G.firstOpen) h
  simpa only [homLiftMap, Category.assoc, G.firstEval_spec, G.firstCentre] using hh

theorem secondEndpoint_constant (z : G.chart.Tangent)
    (he : G.endpointDifferential z = 0) :
    homLiftMap G z ≫ markedEvaluation G.hom G.marks.second G.marks.second_base =
      Infinitesimal.dualToC ≫ infinity.map ≫ D.second.curve.map := by
  have hz : G.secondEval.differential z = 0 := congrArg Prod.snd he
  have h := (differential_zero_iff G.secondEval z).mp hz
  have hh := congrArg (fun f => f ≫ G.secondOpen) h
  simpa only [homLiftMap, Category.assoc, G.secondEval_spec, G.secondCentre] using hh

theorem deformedMap_firstEndpoint (z : G.chart.Tangent)
    (hz : G.baseDifferential z = 1) (he : G.endpointDifferential z = 0) :
    markLift G.source G.marks.first G.marks.first_base ≫ deformedMap G z hz =
      Infinitesimal.dualToC ≫ infinity.map ≫ D.first.curve.map := by
  rw [markLift_deformedMap]
  exact firstEndpoint_constant G z he

theorem deformedMap_secondEndpoint (z : G.chart.Tangent)
    (hz : G.baseDifferential z = 1) (he : G.endpointDifferential z = 0) :
    markLift G.source G.marks.second G.marks.second_base ≫ deformedMap G z hz =
      Infinitesimal.dualToC ≫ infinity.map ≫ D.second.curve.map := by
  rw [markLift_deformedMap]
  exact secondEndpoint_constant G z he

namespace EpsilonNode

open SourceAffineCharts

abbrev Ring := FirstOrderSmoothingNode
abbrev Scheme : AlgebraicGeometry.Scheme := Spec (CommRingCat.of Ring)

def planeQuotient : CommRingCat.of PlaneRing ⟶ CommRingCat.of Ring :=
  CommRingCat.ofHom (Ideal.Quotient.mk nodeInfinitesimalIdeal)

def dualQuotient : CommRingCat.of (Polynomial ℂ) ⟶ CommRingCat.of Infinitesimal.Dual :=
  CommRingCat.ofHom (Ideal.Quotient.mk Infinitesimal.dualIdeal)

/-- The epsilon of the dual-number base is the actual product uv in
the first-order nodal ring. -/
def fromDual : Infinitesimal.Dual →ₐ[ℂ] Ring :=
  Ideal.Quotient.liftₐ Infinitesimal.dualIdeal
    (Polynomial.aeval firstOrderParameter) (by
      have h : Infinitesimal.dualIdeal ≤
          RingHom.ker (Polynomial.aeval firstOrderParameter).toRingHom := by
        rw [Infinitesimal.dualIdeal, Ideal.span_singleton_le_iff_mem]
        change Polynomial.aeval firstOrderParameter (Polynomial.X ^ 2) = 0
        rw [map_pow, Polynomial.aeval_X, firstOrderParameter_square]
      exact h)

theorem fromDual_epsilon : fromDual Infinitesimal.epsilon = firstOrderParameter := by
  change Polynomial.aeval firstOrderParameter Polynomial.X = _
  exact Polynomial.aeval_X _

def parameterMap : CommRingCat.of Infinitesimal.Dual ⟶ CommRingCat.of Ring :=
  CommRingCat.ofHom fromDual.toRingHom

theorem epsilonParameter_eq_Spec : epsilonParameter = Spec.map dualQuotient := by
  symm
  apply CoordinateCharts.functionMap_ext Infinitesimal.dualToC
  · change Spec.map dualQuotient ≫
      Spec.map (CommRingCat.ofHom (Polynomial.C : ℂ →+* Polynomial ℂ)) = _
    rw [← Spec.map_comp]
    rfl
  · exact epsilonParameter_over
  · rw [epsilonParameter_function]
    exact (congrArg
      (fun h : CommRingCat.of (Polynomial ℂ) ⟶
        Γ(Infinitesimal.DualScheme, ⊤) => h Polynomial.X)
      (AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality dualQuotient)).symm

/-- The affine square is the actual pushout of rings. The relation is
(uv)^2=0, and both quotient maps remain the prescribed ones. -/
theorem ringPushout :
    IsPushout AffineNode.nodeParameter dualQuotient planeQuotient parameterMap := by
  apply IsPushout.mk'
  · apply CommRingCat.hom_ext
    apply Polynomial.ringHom_ext
    · intro c
      change Ideal.Quotient.mk nodeInfinitesimalIdeal
        (Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 0 * MvPolynomial.X 1)
          (Polynomial.C c)) = fromDual
            (Ideal.Quotient.mk Infinitesimal.dualIdeal (Polynomial.C c))
      rw [Polynomial.eval₂_C]
      change algebraMap ℂ Ring c = fromDual (algebraMap ℂ Infinitesimal.Dual c)
      exact (fromDual.commutes c).symm
    · change Ideal.Quotient.mk nodeInfinitesimalIdeal
        (Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 0 * MvPolynomial.X 1)
          Polynomial.X) = fromDual Infinitesimal.epsilon
      rw [Polynomial.eval₂_X]
      exact fromDual_epsilon.symm
  · intro T f g h _
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact congrArg (fun h : CommRingCat.of PlaneRing ⟶ T => h p) h
  · intro T a b h
    have hxy : a (MvPolynomial.X 0 * MvPolynomial.X 1) =
        b Infinitesimal.epsilon := by
      have hx := congrArg (fun h : CommRingCat.of (Polynomial ℂ) ⟶ T =>
        h Polynomial.X) h
      simpa [AffineNode.nodeParameter, dualQuotient, Infinitesimal.epsilon] using hx
    have hC (c : ℂ) : a (MvPolynomial.C c) = b (algebraMap ℂ Infinitesimal.Dual c) := by
      have hc := congrArg (fun h : CommRingCat.of (Polynomial ℂ) ⟶ T =>
        h (Polynomial.C c)) h
      have hmk : Ideal.Quotient.mk Infinitesimal.dualIdeal (Polynomial.C c) =
          algebraMap ℂ Infinitesimal.Dual c :=
        Ideal.Quotient.mk_algebraMap ℂ Infinitesimal.dualIdeal c
      simpa [AffineNode.nodeParameter, dualQuotient, hmk] using hc
    have hk : nodeInfinitesimalIdeal ≤ RingHom.ker a.hom := by
      rw [nodeInfinitesimalIdeal, Ideal.span_singleton_le_iff_mem]
      change a ((MvPolynomial.X 0 * MvPolynomial.X 1) ^ 2) = 0
      rw [map_pow, hxy, ← map_pow, Infinitesimal.epsilon_square, map_zero]
    let l : CommRingCat.of Ring ⟶ T :=
      CommRingCat.ofHom (Ideal.Quotient.lift nodeInfinitesimalIdeal a.hom hk)
    refine ⟨l, ?_, ?_⟩
    · apply CommRingCat.hom_ext
      apply RingHom.ext
      intro p
      rfl
    · apply CommRingCat.hom_ext
      apply RingHom.ext
      intro x
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
      have he : (parameterMap ≫ l).hom.comp (Ideal.Quotient.mk Infinitesimal.dualIdeal) =
          b.hom.comp (Ideal.Quotient.mk Infinitesimal.dualIdeal) := by
        apply Polynomial.ringHom_ext
        · intro c
          change l (fromDual (algebraMap ℂ Infinitesimal.Dual c)) =
            b (algebraMap ℂ Infinitesimal.Dual c)
          rw [fromDual.commutes]
          exact hC c
        · change l (fromDual Infinitesimal.epsilon) = b Infinitesimal.epsilon
          rw [fromDual_epsilon]
          exact hxy
      exact congrArg (fun q : Polynomial ℂ →+* T => q p) he

theorem isPullback :
    IsPullback (Spec.map planeQuotient) (Spec.map parameterMap)
      (polynomialLine (parameterPolynomial 0)) epsilonParameter := by
  rw [epsilonParameter_eq_Spec]
  exact isPullback_SpecMap_of_isPushout AffineNode.nodeParameter dualQuotient
    planeQuotient parameterMap ringPushout

def fibreIso : Scheme ≅
    pullback (polynomialLine (parameterPolynomial 0)) epsilonParameter :=
  isPullback.isoPullback

@[reassoc] theorem fibreIso_plane :
    fibreIso.hom ≫ pullback.fst (polynomialLine (parameterPolynomial 0)) epsilonParameter =
      Spec.map planeQuotient := isPullback.isoPullback_hom_fst

@[reassoc] theorem fibreIso_parameter :
    fibreIso.hom ≫ pullback.snd (polynomialLine (parameterPolynomial 0)) epsilonParameter =
      Spec.map parameterMap := isPullback.isoPullback_hom_snd

end EpsilonNode

namespace EpsilonChart

open SourceAffineCharts

def inclusion (F : StandardSource) : SourceOver F epsilonParameter ⟶ F.source :=
  pullback.fst F.parameter epsilonParameter

def nodeOpen (F : StandardSource) : (SourceOver F epsilonParameter).Opens :=
  inclusion F ⁻¹ᵁ chartOpen F 0 0

def toSourceChart (F : StandardSource) :
    (nodeOpen F).toScheme ⟶ (chartOpen F 0 0).toScheme :=
  inclusion F ∣_ chartOpen F 0 0

def toPlane (F : StandardSource) : (nodeOpen F).toScheme ⟶ Plane :=
  toSourceChart F ≫ (chartIso F 0).hom

def toDual (F : StandardSource) : (nodeOpen F).toScheme ⟶ Infinitesimal.DualScheme :=
  (nodeOpen F).ι ≫ pullback.snd F.parameter epsilonParameter

/-- Restricting the actual epsilon-family to the prescribed node chart
is still the canonical pullback square. -/
theorem isPullback (F : StandardSource) :
    IsPullback (toPlane F) (toDual F)
      (polynomialLine (parameterPolynomial 0)) epsilonParameter := by
  have h := (AlgebraicGeometry.isPullback_morphismRestrict (inclusion F)
    (chartOpen F 0 0)).paste_vert
      (IsPullback.of_hasPullback F.parameter epsilonParameter)
  apply h.of_iso (Iso.refl _) (chartIso F 0) (Iso.refl _) (Iso.refl _)
  · simp only [Iso.refl_hom, Category.id_comp]
    rfl
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl
  · simp only [Iso.refl_hom, Category.comp_id]
    exact (chartToModel_parameter F 0).symm
  · simp

theorem toPlane_source (F : StandardSource) :
    toPlane F ≫ modelMap F 0 = (nodeOpen F).ι ≫ inclusion F := by
  have h : (chartIso F 0).hom ≫ modelMap F 0 = (chartOpen F 0 0).ι := by
    rw [← modelToChart_inclusion F 0, ← Category.assoc]
    change ((chartIso F 0).hom ≫ (chartIso F 0).inv) ≫ _ = _
    rw [Iso.hom_inv_id, Category.id_comp]
    rfl
  rw [toPlane, Category.assoc, h]
  exact AlgebraicGeometry.morphismRestrict_ι _ _

def openIso (F : StandardSource) : EpsilonNode.Scheme ≅ (nodeOpen F).toScheme :=
  EpsilonNode.isPullback.isoIsPullback _ _ (isPullback F)

@[reassoc] theorem openIso_plane (F : StandardSource) :
    (openIso F).hom ≫ toPlane F = Spec.map EpsilonNode.planeQuotient :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

@[reassoc] theorem openIso_parameter (F : StandardSource) :
    (openIso F).hom ≫ toDual F = Spec.map EpsilonNode.parameterMap :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

/-- The actual nodal affine chart of the nonreduced source. -/
def nodeMap (F : StandardSource) : EpsilonNode.Scheme ⟶ SourceOver F epsilonParameter :=
  (openIso F).hom ≫ (nodeOpen F).ι

instance nodeMap_open (F : StandardSource) : IsOpenImmersion (nodeMap F) := by
  dsimp [nodeMap]
  infer_instance

@[reassoc] theorem nodeMap_source (F : StandardSource) :
    nodeMap F ≫ pullback.fst F.parameter epsilonParameter =
      Spec.map EpsilonNode.planeQuotient ≫ modelMap F 0 := by
  change ((openIso F).hom ≫ (nodeOpen F).ι) ≫ inclusion F = _
  rw [Category.assoc, ← toPlane_source, ← Category.assoc, openIso_plane]

@[reassoc] theorem nodeMap_parameter (F : StandardSource) :
    nodeMap F ≫ pullback.snd F.parameter epsilonParameter =
      Spec.map EpsilonNode.parameterMap := openIso_parameter F

end EpsilonChart

namespace SquareZeroFunction

/-- A square-zero function determines the actual map to the dual-number
spectrum, through its defining quotient and the affine adjunction. -/
def functions {T : Scheme} (sT : T ⟶ ComplexBase)
    (a : RingSections T ⊤) (ha : a ^ 2 = 0) :
    CommRingCat.of Infinitesimal.Dual ⟶ Γ(T, ⊤) :=
  CommRingCat.ofHom (Ideal.Quotient.lift Infinitesimal.dualIdeal
    (Polynomial.eval₂RingHom (complexConstants sT) a) (by
      have hk : Infinitesimal.dualIdeal ≤
          RingHom.ker (Polynomial.eval₂RingHom (complexConstants sT) a) := by
        rw [Infinitesimal.dualIdeal, Ideal.span_singleton_le_iff_mem]
        change Polynomial.eval₂ (complexConstants sT) a (Polynomial.X ^ 2) = 0
        simpa only [Polynomial.eval₂_pow, Polynomial.eval₂_X] using ha
      exact hk))

def point {T : Scheme} (sT : T ⟶ ComplexBase)
    (a : RingSections T ⊤) (ha : a ^ 2 = 0) : T ⟶ Infinitesimal.DualScheme :=
  (ΓSpec.adjunction.homEquiv T (op (CommRingCat.of Infinitesimal.Dual)))
    (functions sT a ha).op

theorem point_apply {T : Scheme} (sT : T ⟶ ComplexBase)
    (a : RingSections T ⊤) (ha : a ^ 2 = 0) (r : Infinitesimal.Dual) :
    (point sT a ha).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).inv r) =
      functions sT a ha r := by
  exact congrArg (fun k : CommRingCat.of Infinitesimal.Dual ⟶ Γ(T, ⊤) => k r)
    (ΓSpecIso_inv_ΓSpec_adjunction_homEquiv (functions sT a ha))

theorem point_epsilon {T : Scheme} (sT : T ⟶ ComplexBase)
    (a : RingSections T ⊤) (ha : a ^ 2 = 0) :
    (point sT a ha).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).inv Infinitesimal.epsilon) = a := by
  rw [point_apply]
  change Polynomial.eval₂ (complexConstants sT) a Polynomial.X = a
  exact Polynomial.eval₂_X _ _

@[reassoc] theorem point_over {T : Scheme} (sT : T ⟶ ComplexBase)
    (a : RingSections T ⊤) (ha : a ^ 2 = 0) :
    point sT a ha ≫ Infinitesimal.dualToC = sT := by
  apply ext_to_Spec
  apply CommRingCat.hom_ext
  ext c
  change (point sT a ha).appTop
      (Infinitesimal.dualToC.appTop ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c)) =
    sT.appTop ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c)
  have hc := congrArg (fun k : CommRingCat.of ℂ ⟶
      Γ(Infinitesimal.DualScheme, ⊤) => k c)
    (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (algebraMap ℂ Infinitesimal.Dual)))
  change (Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).inv
    (algebraMap ℂ Infinitesimal.Dual c) =
    Infinitesimal.dualToC.appTop ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c) at hc
  rw [← hc, point_apply, ← complexConstants_apply_top]
  change Polynomial.eval₂ (complexConstants sT) a (Polynomial.C c) = _
  exact Polynomial.eval₂_C _ _

theorem point_parameter {T : Scheme} (sT : T ⟶ ComplexBase)
    (a : RingSections T ⊤) (ha : a ^ 2 = 0) :
    point sT a ha ≫ epsilonParameter = CoordinateCharts.fromFunction sT a := by
  apply CoordinateCharts.functionMap_ext sT
  · rw [Category.assoc, epsilonParameter_over, point_over]
  · exact CoordinateCharts.fromFunction_over _ _
  · rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      epsilonParameter_function, point_epsilon, CoordinateCharts.fromFunction_parameter]

theorem point_ext {T : Scheme} (sT : T ⟶ ComplexBase)
    {f g : T ⟶ Infinitesimal.DualScheme}
    (hf : f ≫ Infinitesimal.dualToC = sT)
    (hg : g ≫ Infinitesimal.dualToC = sT)
    (he : f.appTop ((Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).inv
        Infinitesimal.epsilon) =
      g.appTop ((Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).inv
        Infinitesimal.epsilon)) : f = g := by
  apply ext_to_Spec
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective r
  have hp : ((Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).inv ≫ f.appTop).hom.comp
        (Ideal.Quotient.mk Infinitesimal.dualIdeal) =
      ((Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).inv ≫ g.appTop).hom.comp
        (Ideal.Quotient.mk Infinitesimal.dualIdeal) := by
    apply Polynomial.ringHom_ext
    · intro c
      have hc := congrArg (fun k : CommRingCat.of ℂ ⟶
          Γ(Infinitesimal.DualScheme, ⊤) => k c)
        (Scheme.ΓSpecIso_inv_naturality
          (CommRingCat.ofHom (algebraMap ℂ Infinitesimal.Dual)))
      change (Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).inv
        (algebraMap ℂ Infinitesimal.Dual c) =
        Infinitesimal.dualToC.appTop ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c) at hc
      change f.appTop ((Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).inv
          (algebraMap ℂ Infinitesimal.Dual c)) =
        g.appTop ((Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).inv
          (algebraMap ℂ Infinitesimal.Dual c))
      rw [hc]
      have hfc := congrArg (fun k : T ⟶ ComplexBase =>
        k.appTop ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c)) hf
      have hgc := congrArg (fun k : T ⟶ ComplexBase =>
        k.appTop ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c)) hg
      simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at hfc hgc
      exact hfc.trans hgc.symm
    · exact he
  exact congrArg (fun q : Polynomial ℂ →+* RingSections T ⊤ => q p) hp

theorem point_natural {Y T : Scheme} (sY : Y ⟶ ComplexBase) (sT : T ⟶ ComplexBase)
    (f : T ⟶ Y) (hf : f ≫ sY = sT)
    (a : RingSections Y ⊤) (ha : a ^ 2 = 0) :
    f ≫ point sY a ha = point sT (f.appTop a) (by rw [← map_pow, ha, map_zero]) := by
  apply point_ext sT
  · rw [Category.assoc, point_over, hf]
  · exact point_over _ _ _
  · rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, point_epsilon, point_epsilon]

theorem point_zero {T : Scheme} (sT : T ⟶ ComplexBase) :
    point sT 0 (by simp) = sT ≫ Infinitesimal.origin := by
  apply point_ext sT
  · exact point_over _ _ _
  · rw [Category.assoc, DualThickening.origin_overC, Category.comp_id]
  · rw [point_epsilon, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      DualThickening.origin_epsilon, map_zero]

end SquareZeroFunction

namespace BranchCharts

open CoordinateCharts SourceAffineCharts DualThickening

theorem fromFunction_natural {T Y : Scheme} (sT : T ⟶ ComplexBase)
    (sY : Y ⟶ ComplexBase) (f : T ⟶ Y) (hf : f ≫ sY = sT)
    (a : RingSections Y ⊤) :
    f ≫ fromFunction sY a = fromFunction sT (f.appTop a) := by
  apply functionMap_ext sT
  · rw [Category.assoc, fromFunction_over, hf]
  · exact fromFunction_over _ _
  · rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      fromFunction_parameter, fromFunction_parameter]

theorem fromFunction_zero {T : Scheme} (sT : T ⟶ ComplexBase) :
    fromFunction sT 0 = sT ≫ scalarPoint 0 := by
  apply functionMap_ext sT
  · exact fromFunction_over _ _
  · rw [Category.assoc, scalarPoint_overC, Category.comp_id]
  · rw [fromFunction_parameter, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      SourceMarksProof.scalarPoint_zero_parameter, map_zero]

theorem planeFromFunctions_line {T : Scheme} (sT : T ⟶ ComplexBase)
    (a b : RingSections T ⊤) (p : PlaneRing) :
    planeFromFunctions sT a b ≫ polynomialLine p =
      fromFunction sT
        (MvPolynomial.eval₂ (complexConstants sT) (fun i : Fin 2 => if i = 0 then a else b) p) := by
  apply functionMap_ext sT
  · rw [Category.assoc, polynomialLine_over, planeFromFunctions_over]
  · exact fromFunction_over _ _
  · rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, polynomialLine_parameter,
      planeFromFunctions_apply, fromFunction_parameter]

/-- The actual map to the nodal chart with the prescribed two coordinate
functions. It exists on all test schemes, including double thickenings. -/
def nodeSource (F : StandardSource) {T : Scheme} (sT : T ⟶ ComplexBase)
    (a b : RingSections T ⊤) : T ⟶ F.source :=
  planeFromFunctions sT a b ≫ modelMap F 0

@[reassoc] theorem nodeSource_parameter (F : StandardSource) {T : Scheme}
    (sT : T ⟶ ComplexBase) (a b : RingSections T ⊤) :
    nodeSource F sT a b ≫ F.parameter = fromFunction sT (a*b) := by
  rw [nodeSource, Category.assoc, (modelMap_spec F 0).1,
    planeFromFunctions_line]
  simp [parameterPolynomial]

@[reassoc] theorem nodeSource_left (F : StandardSource) {T : Scheme}
    (sT : T ⟶ ComplexBase) (a b : RingSections T ⊤) :
    nodeSource F sT a b ≫ F.left = fromFunction sT a ≫ (ratioPoint 0).val := by
  rw [nodeSource, Category.assoc, (modelMap_spec F 0).2.1, ← Category.assoc,
    planeFromFunctions_line]
  simp [leftPolynomial, leftIndex]

@[reassoc] theorem nodeSource_right (F : StandardSource) {T : Scheme}
    (sT : T ⟶ ComplexBase) (a b : RingSections T ⊤) :
    nodeSource F sT a b ≫ F.right = fromFunction sT b ≫ (ratioPoint 0).val := by
  rw [nodeSource, Category.assoc, (modelMap_spec F 0).2.2, ← Category.assoc,
    planeFromFunctions_line]
  simp [rightPolynomial, rightIndex]

theorem nodeSource_natural (F : StandardSource) {T Y : Scheme}
    (sT : T ⟶ ComplexBase) (sY : Y ⟶ ComplexBase) (f : T ⟶ Y)
    (hf : f ≫ sY = sT) (a b : RingSections Y ⊤) :
    f ≫ nodeSource F sY a b = nodeSource F sT (f.appTop a) (f.appTop b) := by
  apply StandardSourceProof.coordinates_ext F
  · rw [Category.assoc, nodeSource_parameter, nodeSource_parameter,
      fromFunction_natural sT sY f hf, map_mul]
  · rw [Category.assoc, nodeSource_left, nodeSource_left, ← Category.assoc,
      fromFunction_natural sT sY f hf]
  · rw [Category.assoc, nodeSource_right, nodeSource_right, ← Category.assoc,
      fromFunction_natural sT sY f hf]

theorem nodeSource_zero_right (F : StandardSource) (m : SourceMarks F)
    {T : Scheme} (sT : T ⟶ ComplexBase) (a : RingSections T ⊤) :
    nodeSource F sT a 0 = fromFunction sT a ≫ (ratioPoint 0).val ≫ m.branchLeft := by
  apply StandardSourceProof.coordinates_ext F
  · rw [nodeSource_parameter, mul_zero, fromFunction_zero,
      Category.assoc, Category.assoc, m.left_base,
      ← Category.assoc (ratioPoint 0).val P.structureMap,
      (ratioPoint 0).property, ← Category.assoc, fromFunction_over]
  · rw [nodeSource_left, Category.assoc, Category.assoc, m.left_left,
      Category.comp_id]
  · rw [nodeSource_right, fromFunction_zero, Category.assoc,
      ratioPoint_zero_marking, Category.assoc, Category.assoc, m.left_right,
      ← Category.assoc (ratioPoint 0).val P.structureMap,
      (ratioPoint 0).property, ← Category.assoc, fromFunction_over]

theorem nodeSource_zero_left (F : StandardSource) (m : SourceMarks F)
    {T : Scheme} (sT : T ⟶ ComplexBase) (b : RingSections T ⊤) :
    nodeSource F sT 0 b = fromFunction sT b ≫ (ratioPoint 0).val ≫ m.branchRight := by
  apply StandardSourceProof.coordinates_ext F
  · rw [nodeSource_parameter, zero_mul, fromFunction_zero,
      Category.assoc, Category.assoc, m.right_base,
      ← Category.assoc (ratioPoint 0).val P.structureMap,
      (ratioPoint 0).property, ← Category.assoc, fromFunction_over]
  · rw [nodeSource_left, fromFunction_zero, Category.assoc,
      ratioPoint_zero_marking, Category.assoc, Category.assoc, m.right_left,
      ← Category.assoc (ratioPoint 0).val P.structureMap,
      (ratioPoint 0).property, ← Category.assoc, fromFunction_over]
  · rw [nodeSource_right, Category.assoc, Category.assoc, m.right_right,
      Category.comp_id]

/-- The source map retains the actual smoothing parameter ab. -/
def nodeFamily (F : StandardSource) {T : Scheme} (sT : T ⟶ ComplexBase)
    (a b : RingSections T ⊤) (hab : (a*b)^2 = 0) : T ⟶ SourceOver F epsilonParameter :=
  pullback.lift (nodeSource F sT a b) (SquareZeroFunction.point sT (a*b) hab)
    (by rw [nodeSource_parameter, SquareZeroFunction.point_parameter])

@[reassoc] theorem nodeFamily_source (F : StandardSource) {T : Scheme}
    (sT : T ⟶ ComplexBase) (a b : RingSections T ⊤) (hab : (a*b)^2 = 0) :
    nodeFamily F sT a b hab ≫ pullback.fst F.parameter epsilonParameter =
      nodeSource F sT a b := by
  simp [nodeFamily]

@[reassoc] theorem nodeFamily_parameter (F : StandardSource) {T : Scheme}
    (sT : T ⟶ ComplexBase) (a b : RingSections T ⊤) (hab : (a*b)^2 = 0) :
    nodeFamily F sT a b hab ≫ pullback.snd F.parameter epsilonParameter =
      SquareZeroFunction.point sT (a*b) hab := by
  simp [nodeFamily]

@[reassoc] theorem nodeFamily_over (F : StandardSource) {T : Scheme}
    (sT : T ⟶ ComplexBase) (a b : RingSections T ⊤) (hab : (a*b)^2 = 0) :
    nodeFamily F sT a b hab ≫ pullback.snd F.parameter epsilonParameter ≫
      Infinitesimal.dualToC = sT := by
  rw [nodeFamily_parameter_assoc, SquareZeroFunction.point_over]

theorem nodeFamily_natural (F : StandardSource) {T Y : Scheme}
    (sT : T ⟶ ComplexBase) (sY : Y ⟶ ComplexBase) (f : T ⟶ Y)
    (hf : f ≫ sY = sT) (a b : RingSections Y ⊤) (hab : (a*b)^2 = 0) :
    f ≫ nodeFamily F sY a b hab =
      nodeFamily F sT (f.appTop a) (f.appTop b)
        (by rw [← map_mul, ← map_pow, hab, map_zero]) := by
  apply pullback.hom_ext
  · rw [Category.assoc, nodeFamily_source, nodeFamily_source,
      nodeSource_natural F sT sY f hf]
  · simp only [Category.assoc, nodeFamily_parameter,
      SquareZeroFunction.point_natural sY sT f hf, map_mul]

abbrev AffineDual : Scheme := space affineLineToC

def coordinate : RingSections AffineDual ⊤ :=
  (projection affineLineToC).appTop parameterFunction

def epsilon : RingSections AffineDual ⊤ :=
  (parameter affineLineToC).appTop
    ((Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).inv Infinitesimal.epsilon)

theorem epsilon_square : epsilon ^ 2 = 0 := by
  rw [epsilon, ← map_pow, ← map_pow, Infinitesimal.epsilon_square, map_zero, map_zero]

theorem zero_coordinate : (zeroSection affineLineToC).appTop coordinate = parameterFunction := by
  rw [coordinate, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
    zeroSection_projection]
  rfl

theorem zero_epsilon : (zeroSection affineLineToC).appTop epsilon = 0 := by
  rw [epsilon, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
    zeroSection_parameter, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    origin_epsilon, map_zero]

theorem coordinate_fromFunction :
    fromFunction (toC affineLineToC) coordinate = projection affineLineToC := by
  symm
  exact fromFunction_unique (toC affineLineToC) coordinate (projection affineLineToC) rfl rfl

theorem parameter_fromFunction : fromFunction affineLineToC parameterFunction = 𝟙 AffineLine := by
  symm
  exact fromFunction_unique affineLineToC parameterFunction (𝟙 AffineLine)
    (Category.id_comp _) rfl

theorem ratioPoint_zero_infinity : scalarPoint 0 ≫ (ratioPoint 1).val = infinity.map := by
  let v : Fin 2 → ℂ := Pi.single 1 1
  have hv : v ≠ 0 := by
    intro h
    have h1 := congrFun h 1
    simpa [v] using h1
  let x := Classical.choose
    (projectiveCoordinates_pointOfVector (projectiveCoordinates 1) v hv)
  let q : PointsOver ComplexBase (𝟙 ComplexBase) ProjectiveLine P.structureMap :=
    ⟨scalarPoint 0 ≫ (ratioPoint 1).val, by
      rw [Category.assoc, (ratioPoint 1).property, scalarPoint_overC]⟩
  have hq : (projectiveCoordinates 1).Represents q v := by
    refine ⟨hv, ratioPullFrame (scalarPoint 0) 1, ?_⟩
    intro i
    rw [ratioPullFrame_coordinate, SourceMarksProof.scalarPoint_zero_parameter]
    fin_cases i
    · simp [v, scalarUnitSection, scalarSection]
    · simpa [v, scalarUnitSection, scalarSection] using
        (scalarSection_one ComplexBase).symm
  change q.val = x.val
  exact congrArg Subtype.val ((Classical.choose_spec
    (projectiveCoordinates_pointOfVector (projectiveCoordinates 1) v hv)).2 q hq)

theorem planeFromFunctions_natural {T Y : Scheme} (sT : T ⟶ ComplexBase)
    (sY : Y ⟶ ComplexBase) (f : T ⟶ Y) (hf : f ≫ sY = sT)
    (a b : RingSections Y ⊤) :
    f ≫ planeFromFunctions sY a b = planeFromFunctions sT (f.appTop a) (f.appTop b) := by
  apply plane_hom_ext sT
  · rw [Category.assoc, planeFromFunctions_over, hf]
  · exact planeFromFunctions_over _ _ _
  · intro i
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      planeFromFunctions_apply, planeFromFunctions_apply]
    fin_cases i <;> simp

/-- The two outer affine charts use s=e and the reciprocal branch
coordinate w. Their other branch coordinate is the actual product ew. -/
def outerSource (F : StandardSource) (k : Fin 3) {T : Scheme}
    (sT : T ⟶ ComplexBase) (e w : RingSections T ⊤) : T ⟶ F.source :=
  planeFromFunctions sT e w ≫ modelMap F k

@[reassoc] theorem outerSource_parameter (F : StandardSource) (k : Fin 3) (hk : k ≠ 0)
    {T : Scheme} (sT : T ⟶ ComplexBase) (e w : RingSections T ⊤) :
    outerSource F k sT e w ≫ F.parameter = fromFunction sT e := by
  rw [outerSource, Category.assoc, (modelMap_spec F k).1, planeFromFunctions_line]
  simp [parameterPolynomial, hk]

@[reassoc] theorem firstOuterSource_left (F : StandardSource) {T : Scheme}
    (sT : T ⟶ ComplexBase) (e w : RingSections T ⊤) :
    outerSource F 1 sT e w ≫ F.left = fromFunction sT w ≫ (ratioPoint 1).val := by
  rw [outerSource, Category.assoc, (modelMap_spec F 1).2.1, ← Category.assoc,
    planeFromFunctions_line]
  simp [leftPolynomial, leftIndex]

@[reassoc] theorem firstOuterSource_right (F : StandardSource) {T : Scheme}
    (sT : T ⟶ ComplexBase) (e w : RingSections T ⊤) :
    outerSource F 1 sT e w ≫ F.right = fromFunction sT (e*w) ≫ (ratioPoint 0).val := by
  rw [outerSource, Category.assoc, (modelMap_spec F 1).2.2, ← Category.assoc,
    planeFromFunctions_line]
  simp [rightPolynomial, rightIndex]

@[reassoc] theorem secondOuterSource_left (F : StandardSource) {T : Scheme}
    (sT : T ⟶ ComplexBase) (e w : RingSections T ⊤) :
    outerSource F 2 sT e w ≫ F.left = fromFunction sT (e*w) ≫ (ratioPoint 0).val := by
  rw [outerSource, Category.assoc, (modelMap_spec F 2).2.1, ← Category.assoc,
    planeFromFunctions_line]
  simp [leftPolynomial, leftIndex]

@[reassoc] theorem secondOuterSource_right (F : StandardSource) {T : Scheme}
    (sT : T ⟶ ComplexBase) (e w : RingSections T ⊤) :
    outerSource F 2 sT e w ≫ F.right = fromFunction sT w ≫ (ratioPoint 1).val := by
  rw [outerSource, Category.assoc, (modelMap_spec F 2).2.2, ← Category.assoc,
    planeFromFunctions_line]
  simp [rightPolynomial, rightIndex]

theorem outerSource_natural (F : StandardSource) (k : Fin 3) {T Y : Scheme}
    (sT : T ⟶ ComplexBase) (sY : Y ⟶ ComplexBase) (f : T ⟶ Y)
    (hf : f ≫ sY = sT) (e w : RingSections Y ⊤) :
    f ≫ outerSource F k sY e w = outerSource F k sT (f.appTop e) (f.appTop w) := by
  rw [outerSource, ← Category.assoc, planeFromFunctions_natural sT sY f hf]
  rfl

theorem firstOuterSource_zero_parameter (F : StandardSource) (m : SourceMarks F)
    {T : Scheme} (sT : T ⟶ ComplexBase) (w : RingSections T ⊤) :
    outerSource F 1 sT 0 w = fromFunction sT w ≫ (ratioPoint 1).val ≫ m.branchLeft := by
  apply StandardSourceProof.coordinates_ext F
  · rw [outerSource_parameter F 1 (by decide), fromFunction_zero,
      Category.assoc, Category.assoc, m.left_base,
      ← Category.assoc (ratioPoint 1).val P.structureMap,
      (ratioPoint 1).property, ← Category.assoc, fromFunction_over]
  · rw [firstOuterSource_left, Category.assoc, Category.assoc, m.left_left,
      Category.comp_id]
  · rw [firstOuterSource_right, zero_mul, fromFunction_zero, Category.assoc,
      ratioPoint_zero_marking, Category.assoc, Category.assoc, m.left_right,
      ← Category.assoc (ratioPoint 1).val P.structureMap,
      (ratioPoint 1).property, ← Category.assoc, fromFunction_over]

theorem secondOuterSource_zero_parameter (F : StandardSource) (m : SourceMarks F)
    {T : Scheme} (sT : T ⟶ ComplexBase) (w : RingSections T ⊤) :
    outerSource F 2 sT 0 w = fromFunction sT w ≫ (ratioPoint 1).val ≫ m.branchRight := by
  apply StandardSourceProof.coordinates_ext F
  · rw [outerSource_parameter F 2 (by decide), fromFunction_zero,
      Category.assoc, Category.assoc, m.right_base,
      ← Category.assoc (ratioPoint 1).val P.structureMap,
      (ratioPoint 1).property, ← Category.assoc, fromFunction_over]
  · rw [secondOuterSource_left, zero_mul, fromFunction_zero, Category.assoc,
      ratioPoint_zero_marking, Category.assoc, Category.assoc, m.right_left,
      ← Category.assoc (ratioPoint 1).val P.structureMap,
      (ratioPoint 1).property, ← Category.assoc, fromFunction_over]
  · rw [secondOuterSource_right, Category.assoc, Category.assoc, m.right_right,
      Category.comp_id]

theorem firstOuterSource_zero_coordinate (F : StandardSource) (m : SourceMarks F)
    {T : Scheme} (sT : T ⟶ ComplexBase) (e : RingSections T ⊤) :
    outerSource F 1 sT e 0 = fromFunction sT e ≫ m.first := by
  apply StandardSourceProof.coordinates_ext F
  · rw [outerSource_parameter F 1 (by decide), Category.assoc,
      m.first_base, Category.comp_id]
  · rw [firstOuterSource_left, fromFunction_zero, Category.assoc,
      ratioPoint_zero_infinity, Category.assoc, m.first_left,
      ← Category.assoc, fromFunction_over]
  · rw [firstOuterSource_right, mul_zero, fromFunction_zero, Category.assoc,
      ratioPoint_zero_marking, Category.assoc, m.first_right,
      ← Category.assoc, fromFunction_over]

theorem secondOuterSource_zero_coordinate (F : StandardSource) (m : SourceMarks F)
    {T : Scheme} (sT : T ⟶ ComplexBase) (e : RingSections T ⊤) :
    outerSource F 2 sT e 0 = fromFunction sT e ≫ m.second := by
  apply StandardSourceProof.coordinates_ext F
  · rw [outerSource_parameter F 2 (by decide), Category.assoc,
      m.second_base, Category.comp_id]
  · rw [secondOuterSource_left, mul_zero, fromFunction_zero, Category.assoc,
      ratioPoint_zero_marking, Category.assoc, m.second_left,
      ← Category.assoc, fromFunction_over]
  · rw [secondOuterSource_right, fromFunction_zero, Category.assoc,
      ratioPoint_zero_infinity, Category.assoc, m.second_right,
      ← Category.assoc, fromFunction_over]

def outerFamily (F : StandardSource) (k : Fin 3) (hk : k ≠ 0) {T : Scheme}
    (sT : T ⟶ ComplexBase) (e w : RingSections T ⊤) (he : e^2 = 0) :
    T ⟶ SourceOver F epsilonParameter :=
  pullback.lift (outerSource F k sT e w) (SquareZeroFunction.point sT e he)
    (by rw [outerSource_parameter F k hk, SquareZeroFunction.point_parameter])

@[reassoc] theorem outerFamily_source (F : StandardSource) (k : Fin 3) (hk : k ≠ 0)
    {T : Scheme} (sT : T ⟶ ComplexBase) (e w : RingSections T ⊤) (he : e^2 = 0) :
    outerFamily F k hk sT e w he ≫ pullback.fst F.parameter epsilonParameter =
      outerSource F k sT e w := by
  simp [outerFamily]

@[reassoc] theorem outerFamily_parameter (F : StandardSource) (k : Fin 3) (hk : k ≠ 0)
    {T : Scheme} (sT : T ⟶ ComplexBase) (e w : RingSections T ⊤) (he : e^2 = 0) :
    outerFamily F k hk sT e w he ≫ pullback.snd F.parameter epsilonParameter =
      SquareZeroFunction.point sT e he := by
  simp [outerFamily]

@[reassoc] theorem outerFamily_over (F : StandardSource) (k : Fin 3) (hk : k ≠ 0)
    {T : Scheme} (sT : T ⟶ ComplexBase) (e w : RingSections T ⊤) (he : e^2 = 0) :
    outerFamily F k hk sT e w he ≫ pullback.snd F.parameter epsilonParameter ≫
      Infinitesimal.dualToC = sT := by
  rw [outerFamily_parameter_assoc, SquareZeroFunction.point_over]

variable {n : ℕ} {X : ContactFanoManifold n} {D : SuitablePair X} (G : Germ D)

def firstNodeMap : AffineDual ⟶ SourceOver G.source epsilonParameter :=
  nodeFamily G.source (toC affineLineToC) coordinate epsilon
    (by rw [mul_pow, epsilon_square, mul_zero])

def secondNodeMap : AffineDual ⟶ SourceOver G.source epsilonParameter :=
  nodeFamily G.source (toC affineLineToC) epsilon coordinate
    (by rw [mul_pow, epsilon_square, zero_mul])

theorem firstNodeMap_reduction :
    zeroSection affineLineToC ≫ firstNodeMap G = (ratioPoint 0).val ≫ firstBranch G := by
  apply pullback.hom_ext
  · rw [Category.assoc, firstNodeMap, nodeFamily_source]
    change zeroSection affineLineToC ≫
        nodeSource G.source (toC affineLineToC) coordinate epsilon =
      ((ratioPoint 0).val ≫ firstBranch G) ≫ pullback.fst G.source.parameter epsilonParameter
    rw [nodeSource_natural G.source affineLineToC (toC affineLineToC)
      (zeroSection affineLineToC) (zeroSection_overC affineLineToC),
      zero_coordinate, zero_epsilon, nodeSource_zero_right G.source G.marks,
      parameter_fromFunction, Category.id_comp]
    simp only [firstBranch, Category.assoc, pullback.lift_fst]
  · rw [Category.assoc, firstNodeMap, nodeFamily_parameter]
    change zeroSection affineLineToC ≫
        SquareZeroFunction.point (toC affineLineToC) (coordinate*epsilon) _ =
      ((ratioPoint 0).val ≫ firstBranch G) ≫ pullback.snd G.source.parameter epsilonParameter
    simp only [SquareZeroFunction.point_natural (toC affineLineToC) affineLineToC
      (zeroSection affineLineToC) (zeroSection_overC affineLineToC),
      map_mul, zero_epsilon, mul_zero, SquareZeroFunction.point_zero]
    simp only [firstBranch, Category.assoc, pullback.lift_snd]
    rw [← Category.assoc, (ratioPoint 0).property]

theorem secondNodeMap_reduction :
    zeroSection affineLineToC ≫ secondNodeMap G = (ratioPoint 0).val ≫ secondBranch G := by
  apply pullback.hom_ext
  · rw [Category.assoc, secondNodeMap, nodeFamily_source]
    change zeroSection affineLineToC ≫
        nodeSource G.source (toC affineLineToC) epsilon coordinate =
      ((ratioPoint 0).val ≫ secondBranch G) ≫ pullback.fst G.source.parameter epsilonParameter
    rw [nodeSource_natural G.source affineLineToC (toC affineLineToC)
      (zeroSection affineLineToC) (zeroSection_overC affineLineToC),
      zero_coordinate, zero_epsilon, nodeSource_zero_left G.source G.marks,
      parameter_fromFunction, Category.id_comp]
    simp only [secondBranch, Category.assoc, pullback.lift_fst]
  · rw [Category.assoc, secondNodeMap, nodeFamily_parameter]
    change zeroSection affineLineToC ≫
        SquareZeroFunction.point (toC affineLineToC) (epsilon*coordinate) _ =
      ((ratioPoint 0).val ≫ secondBranch G) ≫ pullback.snd G.source.parameter epsilonParameter
    simp only [SquareZeroFunction.point_natural (toC affineLineToC) affineLineToC
      (zeroSection affineLineToC) (zeroSection_overC affineLineToC),
      map_mul, zero_epsilon, zero_mul, SquareZeroFunction.point_zero]
    simp only [secondBranch, Category.assoc, pullback.lift_snd]
    rw [← Category.assoc, (ratioPoint 0).property]

/-- The local deformation with velocity uA is defined on the entire
node chart by setting v equal to its new epsilon. -/
def firstNodeDeformation (z : G.chart.Tangent) (hz : G.baseDifferential z = 1) :
    FamilyVariation.Deformation affineLineToC X.variety.structureMap
      ((ratioPoint 0).val ≫ D.first.curve.map) where
  map := firstNodeMap G ≫ deformedMap G z hz
  overC := by
    rw [Category.assoc, deformedMap_over]
    exact nodeFamily_over _ _ _ _ _
  reduces := by
    rw [← Category.assoc, firstNodeMap_reduction, Category.assoc, firstBranch_reduction]

/-- The second local deformation uses the same source map, with the two
node coordinates exchanged. No independent regular constant is chosen. -/
def secondNodeDeformation (z : G.chart.Tangent) (hz : G.baseDifferential z = 1) :
    FamilyVariation.Deformation affineLineToC X.variety.structureMap
      ((ratioPoint 0).val ≫ D.second.curve.map) where
  map := secondNodeMap G ≫ deformedMap G z hz
  overC := by
    rw [Category.assoc, deformedMap_over]
    exact nodeFamily_over _ _ _ _ _
  reduces := by
    rw [← Category.assoc, secondNodeMap_reduction, Category.assoc, secondBranch_reduction]

def sourceEpsilon : RingSections MixedFamily.DoubleDual ⊤ :=
  (projection Infinitesimal.dualToC).appTop
    ((Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).inv Infinitesimal.epsilon)

def parameterEpsilon : RingSections MixedFamily.DoubleDual ⊤ :=
  (parameter Infinitesimal.dualToC).appTop
    ((Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).inv Infinitesimal.epsilon)

theorem sourceChange_coordinate :
    (DualThickening.map epsilonParameter epsilonParameter_over).appTop coordinate = sourceEpsilon := by
  rw [coordinate, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
    map_projection, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    epsilonParameter_function]
  rfl

theorem sourceChange_epsilon :
    (DualThickening.map epsilonParameter epsilonParameter_over).appTop epsilon = parameterEpsilon := by
  rw [epsilon, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, map_parameter]
  rfl

theorem swap_sourceEpsilon : MixedFamily.swap.appTop sourceEpsilon = parameterEpsilon := by
  rw [sourceEpsilon, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
    MixedFamily.swap_projection]
  rfl

theorem swap_parameterEpsilon : MixedFamily.swap.appTop parameterEpsilon = sourceEpsilon := by
  rw [parameterEpsilon, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
    MixedFamily.swap_parameter]
  rfl

/-- Both node restrictions are literally the same map on the full
double-dual scheme after swapping its two actual factors. -/
theorem nodeMaps_interchange :
    DualThickening.map epsilonParameter epsilonParameter_over ≫ firstNodeMap G =
      MixedFamily.swap ≫ DualThickening.map epsilonParameter epsilonParameter_over ≫
        secondNodeMap G := by
  unfold firstNodeMap secondNodeMap
  simp only [nodeFamily_natural G.source (toC Infinitesimal.dualToC) (toC affineLineToC)
    (DualThickening.map epsilonParameter epsilonParameter_over)
    (DualThickening.map_overC epsilonParameter epsilonParameter_over),
    nodeFamily_natural G.source (toC Infinitesimal.dualToC) (toC affineLineToC)
    (DualThickening.map epsilonParameter epsilonParameter_over)
    (DualThickening.map_overC epsilonParameter epsilonParameter_over),
    sourceChange_coordinate, sourceChange_epsilon]
  simp only [nodeFamily_natural G.source (toC Infinitesimal.dualToC) (toC Infinitesimal.dualToC)
    MixedFamily.swap MixedFamily.swap_overC, swap_sourceEpsilon, swap_parameterEpsilon]

theorem nodeDeformations_interchange (z : G.chart.Tangent) (hz : G.baseDifferential z = 1) :
    ((firstNodeDeformation G z hz).pullback epsilonParameter epsilonParameter_over).map =
      MixedFamily.swap ≫
        ((secondNodeDeformation G z hz).pullback epsilonParameter epsilonParameter_over).map := by
  change DualThickening.map epsilonParameter epsilonParameter_over ≫
      firstNodeMap G ≫ deformedMap G z hz =
    MixedFamily.swap ≫ DualThickening.map epsilonParameter epsilonParameter_over ≫
      secondNodeMap G ≫ deformedMap G z hz
  simpa only [Category.assoc] using congrArg (fun h => h ≫ deformedMap G z hz)
    (nodeMaps_interchange G)

/-- The regular constants of the two auxiliary node variations agree on
every local target function, as successive derivatives of the same map. -/
theorem node_mixed_derivatives (z : G.chart.Tangent) (hz : G.baseDifferential z = 1)
    (U : X.variety.scheme.Opens)
    (hfirst : ⊤ ≤ epsilonParameter ⁻¹ᵁ (((ratioPoint 0).val ≫ D.first.curve.map) ⁻¹ᵁ U))
    (hsecond : ⊤ ≤ epsilonParameter ⁻¹ᵁ (((ratioPoint 0).val ≫ D.second.curve.map) ⁻¹ᵁ U))
    (a : RingSections X.variety.scheme U) :
    LocalVelocityComparison.derivativeAlong epsilonParameter epsilonParameter_over
        (((ratioPoint 0).val ≫ D.first.curve.map) ⁻¹ᵁ U) hfirst
        ((firstNodeDeformation G z hz).onFunction U a) =
      LocalVelocityComparison.derivativeAlong epsilonParameter epsilonParameter_over
        (((ratioPoint 0).val ≫ D.second.curve.map) ⁻¹ᵁ U) hsecond
        ((secondNodeDeformation G z hz).onFunction U a) :=
  LocalVelocityComparison.mixed_derivative_of_restrictions_eq
    (firstNodeDeformation G z hz) (secondNodeDeformation G z hz)
    epsilonParameter epsilonParameter_over epsilonParameter epsilonParameter_over
    (nodeDeformations_interchange G z hz) U hfirst hsecond a

def firstOuterMap : AffineDual ⟶ SourceOver G.source epsilonParameter :=
  outerFamily G.source 1 (by decide) (toC affineLineToC) epsilon coordinate epsilon_square

def secondOuterMap : AffineDual ⟶ SourceOver G.source epsilonParameter :=
  outerFamily G.source 2 (by decide) (toC affineLineToC) epsilon coordinate epsilon_square

theorem firstOuterMap_parameter :
    firstOuterMap G ≫ pullback.snd G.source.parameter epsilonParameter =
      parameter affineLineToC := by
  rw [firstOuterMap, outerFamily_parameter]
  apply SquareZeroFunction.point_ext (toC affineLineToC)
  · exact SquareZeroFunction.point_over _ _ _
  · exact parameter_overC _
  · rw [SquareZeroFunction.point_epsilon]
    rfl

theorem secondOuterMap_parameter :
    secondOuterMap G ≫ pullback.snd G.source.parameter epsilonParameter =
      parameter affineLineToC := by
  rw [secondOuterMap, outerFamily_parameter]
  apply SquareZeroFunction.point_ext (toC affineLineToC)
  · exact SquareZeroFunction.point_over _ _ _
  · exact parameter_overC _
  · rw [SquareZeroFunction.point_epsilon]
    rfl

theorem firstOuterMap_reduction :
    zeroSection affineLineToC ≫ firstOuterMap G = (ratioPoint 1).val ≫ firstBranch G := by
  apply pullback.hom_ext
  · rw [Category.assoc, firstOuterMap, outerFamily_source]
    change zeroSection affineLineToC ≫
        outerSource G.source 1 (toC affineLineToC) epsilon coordinate =
      ((ratioPoint 1).val ≫ firstBranch G) ≫ pullback.fst G.source.parameter epsilonParameter
    rw [outerSource_natural G.source 1 affineLineToC (toC affineLineToC)
      (zeroSection affineLineToC) (zeroSection_overC affineLineToC),
      zero_coordinate, zero_epsilon, firstOuterSource_zero_parameter G.source G.marks,
      parameter_fromFunction, Category.id_comp]
    simp only [firstBranch, Category.assoc, pullback.lift_fst]
  · rw [Category.assoc, firstOuterMap_parameter, zeroSection_parameter]
    simp only [firstBranch, Category.assoc, pullback.lift_snd]
    rw [← Category.assoc, (ratioPoint 1).property]

theorem secondOuterMap_reduction :
    zeroSection affineLineToC ≫ secondOuterMap G = (ratioPoint 1).val ≫ secondBranch G := by
  apply pullback.hom_ext
  · rw [Category.assoc, secondOuterMap, outerFamily_source]
    change zeroSection affineLineToC ≫
        outerSource G.source 2 (toC affineLineToC) epsilon coordinate =
      ((ratioPoint 1).val ≫ secondBranch G) ≫ pullback.fst G.source.parameter epsilonParameter
    rw [outerSource_natural G.source 2 affineLineToC (toC affineLineToC)
      (zeroSection affineLineToC) (zeroSection_overC affineLineToC),
      zero_coordinate, zero_epsilon, secondOuterSource_zero_parameter G.source G.marks,
      parameter_fromFunction, Category.id_comp]
    simp only [secondBranch, Category.assoc, pullback.lift_fst]
  · rw [Category.assoc, secondOuterMap_parameter, zeroSection_parameter]
    simp only [secondBranch, Category.assoc, pullback.lift_snd]
    rw [← Category.assoc, (ratioPoint 1).property]

/-- The original punctured first-branch variation, including its actual
infinity endpoint. In this chart v=epsilon*w and the smoothing base is
the unchanged epsilon. -/
def firstOuterDeformation (z : G.chart.Tangent) (hz : G.baseDifferential z = 1) :
    FamilyVariation.Deformation affineLineToC X.variety.structureMap
      ((ratioPoint 1).val ≫ D.first.curve.map) where
  map := firstOuterMap G ≫ deformedMap G z hz
  overC := by
    rw [Category.assoc, deformedMap_over, ← Category.assoc, firstOuterMap_parameter]
    exact parameter_overC _
  reduces := by
    rw [← Category.assoc, firstOuterMap_reduction, Category.assoc, firstBranch_reduction]

def secondOuterDeformation (z : G.chart.Tangent) (hz : G.baseDifferential z = 1) :
    FamilyVariation.Deformation affineLineToC X.variety.structureMap
      ((ratioPoint 1).val ≫ D.second.curve.map) where
  map := secondOuterMap G ≫ deformedMap G z hz
  overC := by
    rw [Category.assoc, deformedMap_over, ← Category.assoc, secondOuterMap_parameter]
    exact parameter_overC _
  reduces := by
    rw [← Category.assoc, secondOuterMap_reduction, Category.assoc, secondBranch_reduction]

theorem epsilon_fromFunction {Y : Scheme} (sY : Y ⟶ ComplexBase) :
    fromFunction (toC sY) ((parameter sY).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).inv Infinitesimal.epsilon)) =
      parameter sY ≫ epsilonParameter := by
  symm
  apply fromFunction_unique
  · rw [Category.assoc, epsilonParameter_over, parameter_overC]
  · rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, epsilonParameter_function]

theorem endpoint_coordinate :
    (DualThickening.map (scalarPoint 0) (scalarPoint_overC 0)).appTop coordinate = 0 := by
  rw [coordinate, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
    map_projection, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    SourceMarksProof.scalarPoint_zero_parameter, map_zero]

theorem endpoint_epsilon :
    (DualThickening.map (scalarPoint 0) (scalarPoint_overC 0)).appTop epsilon =
      (parameter (𝟙 ComplexBase)).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).inv Infinitesimal.epsilon) := by
  rw [epsilon, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, map_parameter]

theorem firstOuterMap_endpoint :
    DualThickening.map (scalarPoint 0) (scalarPoint_overC 0) ≫ firstOuterMap G =
      parameter (𝟙 ComplexBase) ≫ markLift G.source G.marks.first G.marks.first_base := by
  apply pullback.hom_ext
  · rw [Category.assoc, firstOuterMap, outerFamily_source]
    change DualThickening.map (scalarPoint 0) (scalarPoint_overC 0) ≫
        outerSource G.source 1 (toC affineLineToC) epsilon coordinate = _
    rw [outerSource_natural G.source 1 (toC (𝟙 ComplexBase)) (toC affineLineToC)
      (DualThickening.map (scalarPoint 0) (scalarPoint_overC 0))
      (DualThickening.map_overC _ _), endpoint_coordinate,
      firstOuterSource_zero_coordinate G.source G.marks, endpoint_epsilon,
      epsilon_fromFunction]
    simp only [markLift, Category.assoc, pullback.lift_fst]
  · rw [Category.assoc, firstOuterMap_parameter, map_parameter]
    simp [markLift]

theorem secondOuterMap_endpoint :
    DualThickening.map (scalarPoint 0) (scalarPoint_overC 0) ≫ secondOuterMap G =
      parameter (𝟙 ComplexBase) ≫ markLift G.source G.marks.second G.marks.second_base := by
  apply pullback.hom_ext
  · rw [Category.assoc, secondOuterMap, outerFamily_source]
    change DualThickening.map (scalarPoint 0) (scalarPoint_overC 0) ≫
        outerSource G.source 2 (toC affineLineToC) epsilon coordinate = _
    rw [outerSource_natural G.source 2 (toC (𝟙 ComplexBase)) (toC affineLineToC)
      (DualThickening.map (scalarPoint 0) (scalarPoint_overC 0))
      (DualThickening.map_overC _ _), endpoint_coordinate,
      secondOuterSource_zero_coordinate G.source G.marks, endpoint_epsilon,
      epsilon_fromFunction]
    simp only [markLift, Category.assoc, pullback.lift_fst]
  · rw [Category.assoc, secondOuterMap_parameter, map_parameter]
    simp [markLift]

theorem firstOuter_fixed (z : G.chart.Tangent) (hz : G.baseDifferential z = 1)
    (he : G.endpointDifferential z = 0) :
    (firstOuterDeformation G z hz).IsFixedAlong (scalarPoint 0) (scalarPoint_overC 0) := by
  change DualThickening.map (scalarPoint 0) (scalarPoint_overC 0) ≫
      firstOuterMap G ≫ deformedMap G z hz =
    projection (𝟙 ComplexBase) ≫ (scalarPoint 0 ≫ (ratioPoint 1).val ≫ D.first.curve.map)
  rw [← Category.assoc, firstOuterMap_endpoint, Category.assoc,
    deformedMap_firstEndpoint G z hz he,
    ← Category.assoc (parameter (𝟙 ComplexBase)) Infinitesimal.dualToC,
    parameter_overC]
  rw [← Category.assoc (scalarPoint 0) (ratioPoint 1).val, ratioPoint_zero_infinity]
  simp only [toC, Category.comp_id]

theorem secondOuter_fixed (z : G.chart.Tangent) (hz : G.baseDifferential z = 1)
    (he : G.endpointDifferential z = 0) :
    (secondOuterDeformation G z hz).IsFixedAlong (scalarPoint 0) (scalarPoint_overC 0) := by
  change DualThickening.map (scalarPoint 0) (scalarPoint_overC 0) ≫
      secondOuterMap G ≫ deformedMap G z hz =
    projection (𝟙 ComplexBase) ≫ (scalarPoint 0 ≫ (ratioPoint 1).val ≫ D.second.curve.map)
  rw [← Category.assoc, secondOuterMap_endpoint, Category.assoc,
    deformedMap_secondEndpoint G z hz he,
    ← Category.assoc (parameter (𝟙 ComplexBase)) Infinitesimal.dualToC,
    parameter_overC]
  rw [← Category.assoc (scalarPoint 0) (ratioPoint 1).val, ratioPoint_zero_infinity]
  simp only [toC, Category.comp_id]

theorem firstOuter_divisible (z : G.chart.Tangent) (hz : G.baseDifferential z = 1)
    (he : G.endpointDifferential z = 0) :
    ∃ b : GlobalSections (pullbackModule ((ratioPoint 1).val ≫ D.first.curve.map)
        (tangentSheaf X.variety.structureMap)),
      (firstOuterDeformation G z hz).variation X.variety = parameterFunction • b := by
  letI := LocalExtensionSplitting.quasicoherent_of_locallyFreeRank
    (pullback_locallyFree ((ratioPoint 1).val ≫ D.first.curve.map)
      (smooth_tangent_rank X.variety.structureMap (2*n+1) X.variety.smooth))
  apply LeBrunSalamon.StandardInputs.affineLine_section_divisible
  change pullSection (scalarPoint 0)
    (sectionFromValue (sectionValue ((firstOuterDeformation G z hz).section X.variety))) = 0
  rw [sectionFromValue_sectionValue]
  exact (firstOuterDeformation G z hz).fixed_section X.variety
    (scalarPoint 0) (scalarPoint_overC 0) (firstOuter_fixed G z hz he)

theorem secondOuter_divisible (z : G.chart.Tangent) (hz : G.baseDifferential z = 1)
    (he : G.endpointDifferential z = 0) :
    ∃ b : GlobalSections (pullbackModule ((ratioPoint 1).val ≫ D.second.curve.map)
        (tangentSheaf X.variety.structureMap)),
      (secondOuterDeformation G z hz).variation X.variety = parameterFunction • b := by
  letI := LocalExtensionSplitting.quasicoherent_of_locallyFreeRank
    (pullback_locallyFree ((ratioPoint 1).val ≫ D.second.curve.map)
      (smooth_tangent_rank X.variety.structureMap (2*n+1) X.variety.smooth))
  apply LeBrunSalamon.StandardInputs.affineLine_section_divisible
  change pullSection (scalarPoint 0)
    (sectionFromValue (sectionValue ((secondOuterDeformation G z hz).section X.variety))) = 0
  rw [sectionFromValue_sectionValue]
  exact (secondOuterDeformation G z hz).fixed_section X.variety
    (scalarPoint 0) (scalarPoint_overC 0) (secondOuter_fixed G z hz he)

end BranchCharts

namespace InfinitesimalHorizontality

open DualThickening FamilyVariation

variable {Y : Scheme} {d : ℕ} (M : SmoothProperComplexVariety d)
variable {sY : Y ⟶ ComplexBase} {f : Y ⟶ M.scheme}

/-- The actual target cotangent differential, followed by passage to
differentials relative to the fixed dual-number parameter. -/
def targetToRelative (E : Deformation sY M.structureMap f) :
    pullbackModule E.map (cotangentSheaf M.structureMap) ⟶
      cotangentSheaf (parameter sY) :=
  cotangentMap E.map M.structureMap ≫
    eqToHom (congrArg cotangentSheaf
      (E.overC.trans (parameter_overC sY).symm)) ≫
        cotangentToRelative (parameter sY) Infinitesimal.dualToC

theorem targetToRelative_differential (E : Deformation sY M.structureMap f)
    (U : M.scheme.Opens) (a : RingSections M.scheme U) :
    (targetToRelative M E).app (E.map ⁻¹ᵁ U)
      (pullLocalSection E.map (cotangentSheaf M.structureMap) U
        ((cotangentPresentation M.structureMap).differential.apply U a)) =
      (cotangentPresentation (parameter sY)).differential.apply
        (E.map ⁻¹ᵁ U) (E.map.app U a) := by
  change (cotangentToRelative (parameter sY) Infinitesimal.dualToC).app _
    ((eqToHom (congrArg cotangentSheaf
      (E.overC.trans (parameter_overC sY).symm))).app _
      ((cotangentMap E.map M.structureMap).app _
        (pullLocalSection E.map (cotangentSheaf M.structureMap) U
          ((cotangentPresentation M.structureMap).differential.apply U a)))) = _
  rw [ContactDerivativeIsoProof.cotangentMap_differential,
    ContactDerivativeIsoProof.differential_transport,
    CotangentTransitivityRederivedV02.cotangentToRelative_differential]
  exact E.overC.trans (parameter_overC sY).symm

/-- The source coordinate is held fixed in the dual-number direction.
The only comparison used is the canonical cotangent base-change map. -/
def relativeCotangent (E : Deformation sY M.structureMap f) :
    pullbackModule E.map (cotangentSheaf M.structureMap) ⟶
      pullbackModule (projection sY) (cotangentSheaf sY) := by
  letI := LeBrunSalamon.StandardInputs.cotangentPullback_isIso sY Infinitesimal.dualToC
  exact targetToRelative M E ≫ inv (CotangentBaseChange.canonicalMap sY Infinitesimal.dualToC)

/-- The genuine relative tangent differential of a first-order family.
Dual base change retains the original pairing with local differentials. -/
def relativeDifferential (E : Deformation sY M.structureMap f) :
    pullbackModule (projection sY) (tangentSheaf sY) ⟶
      pullbackModule E.map (tangentSheaf M.structureMap) := by
  letI := dualBaseChange_isIso E.map (smooth_cotangent_rank M.structureMap d M.smooth)
  exact dualBaseChange (projection sY) (cotangentSheaf sY) ≫
    ContactDerivativeIsoProof.dualMap (relativeCotangent M E) ≫ inv (dualBaseChange E.map (cotangentSheaf M.structureMap))

/-- On the actual first-order deformation of a degree-one curve, every
map from the pulled source tangent bundle to the pulled contact line
vanishes. The ordinary central O(2)-to-O(1) calculation is used twice
through the generic square-zero filtration. -/
theorem contactHom_zero {n : ℕ} {X : ContactFanoManifold n} (f : FreeLine X)
    (E : Deformation P.structureMap X.variety.structureMap f.curve.map)
    (v : pullbackModule (projection P.structureMap) (tangentSheaf P.structureMap) ⟶
      pullbackModule E.map X.contact.sequence.line.sheaf) : v = 0 := by
  apply LeBrunSalamon.StandardInputs.dualThickening_hom_vanishing P.structureMap
    (intrinsicTangentBundle (projectiveLineVariety P))
    (pullbackLine E.map X.contact.sequence.line) _ v
  intro m
  let e := compositionPullback (zeroSection P.structureMap) E.map f.curve.map
    E.reduces X.contact.sequence.line.sheaf
  apply (cancel_mono e.hom).mp
  rw [zero_comp]
  exact LeBrunSalamon.PhaseThirtyTwo.intrinsicContactLine_velocity_zero P marking X.variety X.contact f.curve
    f.degreeOne (m ≫ e.hom)

/-- Horizontality holds on the entire nonreduced first-order family,
for the actual relative differential defined above. -/
theorem relative_contact_zero {n : ℕ} {X : ContactFanoManifold n} (f : FreeLine X)
    (E : Deformation P.structureMap X.variety.structureMap f.curve.map) :
    relativeDifferential X.variety E ≫
      (Scheme.Modules.pullback E.map).map X.contact.sequence.form = 0 :=
  contactHom_zero f E _

end InfinitesimalHorizontality

namespace DualScaling

open DualThickening FamilyVariation

variable {Y : Scheme} (sY : Y ⟶ ComplexBase)

def globalEpsilon : RingSections (space sY) ⊤ :=
  (parameter sY).appTop
    ((Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).inv Infinitesimal.epsilon)

theorem globalEpsilon_square : globalEpsilon sY ^ 2 = 0 := by
  rw [globalEpsilon, ← map_pow, ← map_pow, Infinitesimal.epsilon_square, map_zero, map_zero]

theorem zero_globalEpsilon : (zeroSection sY).appTop (globalEpsilon sY) = 0 := by
  rw [globalEpsilon, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
    zeroSection_parameter, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    origin_epsilon, map_zero]

/-- Multiplication of the actual epsilon by a regular source function;
the source projection is retained exactly. -/
def map (c : RingSections Y ⊤) : space sY ⟶ space sY :=
  pullback.lift (projection sY)
    (SquareZeroFunction.point (toC sY)
      (globalEpsilon sY * (projection sY).appTop c)
      (by rw [mul_pow, globalEpsilon_square, zero_mul]))
    (SquareZeroFunction.point_over _ _ _).symm

@[reassoc] theorem map_projection (c : RingSections Y ⊤) :
    map sY c ≫ projection sY = projection sY := by
  simp [map, projection]

@[reassoc] theorem map_overC (c : RingSections Y ⊤) :
    map sY c ≫ toC sY = toC sY := by
  rw [toC, ← Category.assoc, map_projection]

@[reassoc] theorem map_parameter (c : RingSections Y ⊤) :
    map sY c ≫ parameter sY = SquareZeroFunction.point (toC sY)
      (globalEpsilon sY * (projection sY).appTop c)
      (by rw [mul_pow, globalEpsilon_square, zero_mul]) := by
  simp only [map, parameter, pullback.lift_snd]

theorem map_epsilon (c : RingSections Y ⊤) :
    (map sY c).appTop (globalEpsilon sY) =
      globalEpsilon sY * (projection sY).appTop c := by
  change (map sY c).appTop ((parameter sY).appTop
    ((Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).inv Infinitesimal.epsilon)) = _
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, map_parameter,
    SquareZeroFunction.point_epsilon]

@[reassoc] theorem zeroSection_map (c : RingSections Y ⊤) :
    zeroSection sY ≫ map sY c = zeroSection sY := by
  apply pullback.hom_ext
  · change (zeroSection sY ≫ map sY c) ≫ projection sY = zeroSection sY ≫ projection sY
    rw [Category.assoc, map_projection]
  · change (zeroSection sY ≫ map sY c) ≫ parameter sY = zeroSection sY ≫ parameter sY
    rw [Category.assoc, map_parameter]
    simp only [SquareZeroFunction.point_natural (toC sY) sY (zeroSection sY) (zeroSection_overC sY),
      map_mul, zero_globalEpsilon, zero_mul, SquareZeroFunction.point_zero,
      zeroSection_parameter]

theorem map_preimage (c : RingSections Y ⊤) (U : Y.Opens) :
    map sY c ⁻¹ᵁ (projection sY ⁻¹ᵁ U) = projection sY ⁻¹ᵁ U := by
  change (map sY c ≫ projection sY) ⁻¹ᵁ U = _
  rw [map_projection]

def onFunctions (c : RingSections Y ⊤) (U : Y.Opens) :
    (space sY).presheaf.obj (op (projection sY ⁻¹ᵁ U)) ⟶
      (space sY).presheaf.obj (op (projection sY ⁻¹ᵁ U)) :=
  (map sY c).appLE (projection sY ⁻¹ᵁ U) (projection sY ⁻¹ᵁ U)
    (map_preimage sY c U).ge

theorem onFunctions_projection (c : RingSections Y ⊤) (U : Y.Opens)
    (a : RingSections Y U) :
    onFunctions sY c U ((projection sY).app U a) = (projection sY).app U a := by
  have h : (projection sY).app U ≫ onFunctions sY c U = (projection sY).app U := by
    rw [(projection sY).app_eq_appLE]
    unfold onFunctions
    rw [Scheme.Hom.appLE_comp_appLE]
    exact appLE_of_map_eq (map_projection sY c) U _ _ _
  exact congrArg (fun q => q a) h

theorem onFunctions_epsilon (c : RingSections Y ⊤) (U : Y.Opens) :
    onFunctions sY c U (epsilonOn sY U) = epsilonOn sY U *
      (projection sY).app U (Y.presheaf.map (homOfLE le_top).op c) := by
  have hres : (space sY).presheaf.map (homOfLE le_top).op ≫ onFunctions sY c U =
      (map sY c).appTop ≫ (space sY).presheaf.map (homOfLE le_top).op := by
    unfold onFunctions
    rw [Scheme.Hom.map_appLE]
    rw [show (map sY c).appTop = (map sY c).appLE ⊤ ⊤ le_rfl by
      simp [Scheme.Hom.appLE]]
    rw [Scheme.Hom.appLE_map]
  have h := congrArg (fun q => q (globalEpsilon sY)) hres
  change onFunctions sY c U (epsilonOn sY U) =
    (space sY).presheaf.map (homOfLE le_top).op
      ((map sY c).appTop (globalEpsilon sY)) at h
  rw [map_epsilon, map_mul] at h
  refine h.trans ?_
  congr 1
  exact projection_restrict sY (homOfLE le_top) c

theorem onFunctions_normalForm (c : RingSections Y ⊤) (U : Y.Opens)
    (a b : RingSections Y U) :
    onFunctions sY c U (normalForm sY U a b) =
      normalForm sY U a (Y.presheaf.map (homOfLE le_top).op c * b) := by
  simp only [normalForm, map_add, map_mul, onFunctions_projection, onFunctions_epsilon]
  rw [mul_assoc]

theorem coefficient_onFunctions (c : RingSections Y ⊤) (U : Y.Opens)
    (a : RingSections (space sY) (projection sY ⁻¹ᵁ U)) :
    coefficient sY U (onFunctions sY c U a) =
      Y.presheaf.map (homOfLE le_top).op c * coefficient sY U a := by
  conv_lhs => rw [reconstruct sY U a, onFunctions_normalForm, coefficient_normalForm]

variable {X : Scheme} {sX : X ⟶ ComplexBase} {f : Y ⟶ X}

def deformation (E : Deformation sY sX f) (c : RingSections Y ⊤) :
    Deformation sY sX f where
  map := map sY c ≫ E.map
  overC := by rw [Category.assoc, E.overC, map_overC]
  reduces := by rw [← Category.assoc, zeroSection_map, E.reduces]

theorem functionPullback_deformation (E : Deformation sY sX f) (c : RingSections Y ⊤)
    (U : X.Opens) :
    functionPullback sY (deformation sY E c).map f (deformation sY E c).reduces U =
      functionPullback sY E.map f E.reduces U ≫ onFunctions sY c (f ⁻¹ᵁ U) := by
  unfold functionPullback onFunctions deformation
  rw [Scheme.Hom.appLE_comp_appLE]

theorem deformation_onFunction (E : Deformation sY sX f) (c : RingSections Y ⊤)
    (U : X.Opens) (a : RingSections X U) :
    (deformation sY E c).onFunction U a =
      Y.presheaf.map (homOfLE le_top).op c * E.onFunction U a := by
  unfold Deformation.onFunction
  rw [functionPullback_deformation, CommRingCat.comp_apply, coefficient_onFunctions]

theorem deformation_cotangentHom (E : Deformation sY sX f) (c : RingSections Y ⊤) :
    (deformation sY E c).cotangentHom =
      E.cotangentHom ≫ GlobalScalars.scalarEnd (structureModule Y) c := by
  symm
  apply (deformation sY E c).cotangentHom_unique
  intro U a
  change (GlobalScalars.scalarEnd (structureModule Y) c).app (f ⁻¹ᵁ U)
    (E.cotangentHom.app (f ⁻¹ᵁ U)
      (pullLocalSection f (cotangentSheaf sX) U
        ((cotangentPresentation sX).differential.apply U a))) = _
  rw [GlobalScalars.scalarEnd_app, E.cotangentHom_differential, deformation_onFunction]
  rfl

theorem scalarEnd_natural {E F : OModule Y} (h : E ⟶ F) (c : RingSections Y ⊤) :
    GlobalScalars.scalarEnd E c ≫ h = h ≫ GlobalScalars.scalarEnd F c := by
  apply Scheme.Modules.hom_ext
  intro U
  ext e
  change h.app U ((GlobalScalars.scalarEnd E c).app U e) =
    (GlobalScalars.scalarEnd F c).app U (h.app U e)
  rw [GlobalScalars.scalarEnd_app, GlobalScalars.scalarEnd_app, Scheme.Modules.Hom.app_smul]

theorem homSection_scalar {E : OModule Y} (h : E ⟶ structureModule Y)
    (c : RingSections Y ⊤) :
    TwoChartSections.homSection (h ≫ GlobalScalars.scalarEnd (structureModule Y) c) =
      TwoChartSections.homSection h ≫ GlobalScalars.scalarEnd (dualSheaf E) c := by
  apply ContactDerivativeIsoProof.dual_hom_ext
  intro U r e
  change RingSections Y U at r
  let t : RingSections Y U :=
    Y.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op c
  let hs : SectionsOn (dualSheaf E) U :=
    Scheme.Modules.Hom.app (TwoChartSections.homSection h) U r
  have heval : (dualEvaluation E).apply U hs e = r • h.app U e :=
    homSection_evaluate h U r e
  have hlinear : (dualEvaluation E).apply U (t • hs) e =
      t • ((dualEvaluation E).apply U hs e) := by
    exact congrArg
      (fun k : SectionsOn E U →ₗ[RingSections Y U] SectionsOn (structureModule Y) U =>
        k e)
      (map_smul ((dualEvaluation E).apply U) t hs)
  change (dualEvaluation E).apply U
      (Scheme.Modules.Hom.app
        (TwoChartSections.homSection (h ≫ GlobalScalars.scalarEnd (structureModule Y) c)) U r) e =
    (dualEvaluation E).apply U (t • hs) e
  calc
    _ = r • (h ≫ GlobalScalars.scalarEnd (structureModule Y) c).app U e :=
      homSection_evaluate (h ≫ GlobalScalars.scalarEnd (structureModule Y) c) U r e
    _ = r • (t • h.app U e) := rfl
    _ = t • (r • h.app U e) := smul_comm r t (h.app U e)
    _ = t • ((dualEvaluation E).apply U hs e) :=
      congrArg (fun z : SectionsOn (structureModule Y) U => t • z) heval.symm
    _ = _ := hlinear.symm

theorem deformation_section {d : ℕ} (M : SmoothProperComplexVariety d)
    {f : Y ⟶ M.scheme} (E : Deformation sY M.structureMap f) (c : RingSections Y ⊤) :
    (deformation sY E c).section M =
      E.section M ≫ GlobalScalars.scalarEnd (pullbackModule f (tangentSheaf M.structureMap)) c := by
  letI := dualBaseChange_isIso f (smooth_cotangent_rank M.structureMap d M.smooth)
  apply (cancel_mono (dualBaseChange f (cotangentSheaf M.structureMap))).mp
  rw [(deformation sY E c).section_normalized, deformation_cotangentHom,
    homSection_scalar, Category.assoc, scalarEnd_natural, ← Category.assoc,
    E.section_normalized]

theorem deformation_variation {d : ℕ} (M : SmoothProperComplexVariety d)
    {f : Y ⟶ M.scheme} (E : Deformation sY M.structureMap f) (c : RingSections Y ⊤) :
    (deformation sY E c).variation M =
      c • (show GlobalSections (pullbackModule f (tangentSheaf M.structureMap))
        from E.variation M) := by
  unfold Deformation.variation
  rw [deformation_section, sectionValue_comp, GlobalScalars.scalarEnd_app]
  change (Y.presheaf.map (𝟙 (op ⊤)) c) • sectionValue (E.section M) = _
  rw [CategoryTheory.Functor.map_id]
  rfl

theorem map_source_function (c a : RingSections Y ⊤) :
    (map sY c).appTop ((projection sY).appTop a) = (projection sY).appTop a := by
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, map_projection]

theorem scale_one : map sY 1 = 𝟙 (space sY) := by
  apply pullback.hom_ext
  · change map sY 1 ≫ projection sY = (𝟙 (space sY)) ≫ projection sY
    rw [map_projection, Category.id_comp]
  · change map sY 1 ≫ parameter sY = (𝟙 (space sY)) ≫ parameter sY
    rw [Category.id_comp]
    apply SquareZeroFunction.point_ext (toC sY)
    · rw [Category.assoc, parameter_overC, map_overC]
    · exact parameter_overC _
    · change (map sY 1).appTop (globalEpsilon sY) = globalEpsilon sY
      rw [map_epsilon, map_one, mul_one]

theorem scale_mul (c d : RingSections Y ⊤) :
    map sY c ≫ map sY d = map sY (c*d) := by
  apply pullback.hom_ext
  · change (map sY c ≫ map sY d) ≫ projection sY = map sY (c*d) ≫ projection sY
    rw [Category.assoc, map_projection, map_projection, map_projection]
  · change (map sY c ≫ map sY d) ≫ parameter sY = map sY (c*d) ≫ parameter sY
    apply SquareZeroFunction.point_ext (toC sY)
    · rw [Category.assoc, Category.assoc, parameter_overC, map_overC, map_overC]
    · rw [Category.assoc, parameter_overC, map_overC]
    · change (map sY c).appTop ((map sY d).appTop (globalEpsilon sY)) =
        (map sY (c*d)).appTop (globalEpsilon sY)
      rw [map_epsilon, map_mul, map_epsilon, map_source_function, map_epsilon, map_mul]
      ring

theorem sourceMap_epsilon {Z : Scheme} {sZ : Z ⟶ ComplexBase}
    (g : Y ⟶ Z) (hg : g ≫ sZ = sY) :
    (DualThickening.map g hg).appTop (globalEpsilon sZ) = globalEpsilon sY := by
  rw [globalEpsilon, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
    DualThickening.map_parameter]
  rfl

theorem sourceMap_function {Z : Scheme} {sZ : Z ⟶ ComplexBase}
    (g : Y ⟶ Z) (hg : g ≫ sZ = sY) (c : RingSections Z ⊤) :
    (DualThickening.map g hg).appTop ((projection sZ).appTop c) =
      (projection sY).appTop (g.appTop c) := by
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
    DualThickening.map_projection, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]

theorem map_natural {Z : Scheme} {sZ : Z ⟶ ComplexBase}
    (g : Y ⟶ Z) (hg : g ≫ sZ = sY) (c : RingSections Z ⊤) :
    DualThickening.map g hg ≫ map sZ c =
      map sY (g.appTop c) ≫ DualThickening.map g hg := by
  apply pullback.hom_ext
  · change (DualThickening.map g hg ≫ map sZ c) ≫ projection sZ =
      (map sY (g.appTop c) ≫ DualThickening.map g hg) ≫ projection sZ
    rw [Category.assoc, map_projection, Category.assoc, DualThickening.map_projection,
      ← Category.assoc, map_projection]
  · change (DualThickening.map g hg ≫ map sZ c) ≫ parameter sZ =
      (map sY (g.appTop c) ≫ DualThickening.map g hg) ≫ parameter sZ
    apply SquareZeroFunction.point_ext (toC sY)
    · rw [Category.assoc, Category.assoc, parameter_overC, map_overC,
        DualThickening.map_overC]
    · rw [Category.assoc, Category.assoc, parameter_overC, DualThickening.map_overC,
        map_overC]
    · change (DualThickening.map g hg).appTop ((map sZ c).appTop (globalEpsilon sZ)) =
        (map sY (g.appTop c)).appTop ((DualThickening.map g hg).appTop (globalEpsilon sZ))
      rw [map_epsilon, map_mul, sourceMap_epsilon, sourceMap_function, map_epsilon]

theorem deformation_one (E : Deformation sY sX f) : deformation sY E 1 = E := by
  apply Deformation.ext
  change map sY 1 ≫ E.map = E.map
  rw [scale_one, Category.id_comp]

theorem deformation_mul (E : Deformation sY sX f) (c d : RingSections Y ⊤) :
    deformation sY (deformation sY E d) c = deformation sY E (c*d) := by
  apply Deformation.ext
  change map sY c ≫ map sY d ≫ E.map = map sY (c*d) ≫ E.map
  rw [← Category.assoc, scale_mul]

theorem deformation_sourceChange {Z : Scheme} {sZ : Z ⟶ ComplexBase}
    {f : Z ⟶ X} (E : Deformation sZ sX f)
    (g : Y ⟶ Z) (hg : g ≫ sZ = sY) (c : RingSections Z ⊤) :
    (deformation sZ E c).pullback g hg =
      deformation sY (E.pullback g hg) (g.appTop c) := by
  apply Deformation.ext
  change DualThickening.map g hg ≫ map sZ c ≫ E.map =
    map sY (g.appTop c) ≫ DualThickening.map g hg ≫ E.map
  rw [← Category.assoc, map_natural, Category.assoc]

end DualScaling

namespace BranchCharts

open CoordinateCharts SourceAffineCharts DualThickening

theorem outerFamily_natural (F : StandardSource) (k : Fin 3) (hk : k ≠ 0)
    {T Y : Scheme} (sT : T ⟶ ComplexBase) (sY : Y ⟶ ComplexBase) (f : T ⟶ Y)
    (hf : f ≫ sY = sT) (e w : RingSections Y ⊤) (he : e^2 = 0) :
    f ≫ outerFamily F k hk sY e w he =
      outerFamily F k hk sT (f.appTop e) (f.appTop w)
        (by rw [← map_pow, he, map_zero]) := by
  apply pullback.hom_ext
  · rw [Category.assoc, outerFamily_source, outerFamily_source,
      outerSource_natural F k sT sY f hf]
  · rw [Category.assoc, outerFamily_parameter, outerFamily_parameter,
      SquareZeroFunction.point_natural sY sT f hf]

/-- The actual transition from the node to the first infinity chart.
The product aw=1 is the reciprocal projective-coordinate identity. -/
theorem nodeFamily_eq_firstOuter (F : StandardSource) {T : Scheme}
    (sT : T ⟶ ComplexBase) (a b w : RingSections T ⊤)
    (hab : (a*b)^2 = 0) (haw : a*w = 1) :
    nodeFamily F sT a b hab = outerFamily F 1 (by decide) sT (a*b) w hab := by
  apply pullback.hom_ext
  · rw [nodeFamily_source, outerFamily_source]
    apply StandardSourceProof.coordinates_ext F
    · rw [nodeSource_parameter, outerSource_parameter F 1 (by decide)]
    · rw [nodeSource_left, firstOuterSource_left]
      symm
      apply PuncturedSourceProof.reciprocal_ratios sT
        (fromFunction sT w) (fromFunction sT a)
        (fromFunction_over _ _) (fromFunction_over _ _)
      rw [fromFunction_parameter, fromFunction_parameter, mul_comm, haw]
    · rw [nodeSource_right, firstOuterSource_right]
      have h : (a*b)*w = b := by
        calc (a*b)*w = (a*w)*b := by ring
             _ = b := by rw [haw, one_mul]
      rw [h]
  · rw [nodeFamily_parameter, outerFamily_parameter]

theorem nodeFamily_eq_secondOuter (F : StandardSource) {T : Scheme}
    (sT : T ⟶ ComplexBase) (a b w : RingSections T ⊤)
    (hab : (a*b)^2 = 0) (hbw : b*w = 1) :
    nodeFamily F sT a b hab = outerFamily F 2 (by decide) sT (a*b) w hab := by
  apply pullback.hom_ext
  · rw [nodeFamily_source, outerFamily_source]
    apply StandardSourceProof.coordinates_ext F
    · rw [nodeSource_parameter, outerSource_parameter F 2 (by decide)]
    · rw [nodeSource_left, secondOuterSource_left, mul_assoc, hbw, mul_one]
    · rw [nodeSource_right, secondOuterSource_right]
      symm
      apply PuncturedSourceProof.reciprocal_ratios sT
        (fromFunction sT w) (fromFunction sT b)
        (fromFunction_over _ _) (fromFunction_over _ _)
      rw [fromFunction_parameter, fromFunction_parameter, mul_comm, hbw]
  · rw [nodeFamily_parameter, outerFamily_parameter]

theorem sourceChange_coordinate_general {T : Scheme} (sT : T ⟶ ComplexBase)
    (u : T ⟶ AffineLine) (hu : u ≫ affineLineToC = sT) :
    (DualThickening.map u hu).appTop coordinate =
      (projection sT).appTop (u.appTop parameterFunction) := by
  rw [coordinate, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
    DualThickening.map_projection, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]

theorem sourceChange_epsilon_general {T : Scheme} (sT : T ⟶ ComplexBase)
    (u : T ⟶ AffineLine) (hu : u ≫ affineLineToC = sT) :
    (DualThickening.map u hu).appTop epsilon = DualScaling.globalEpsilon sT := by
  rw [epsilon, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
    DualThickening.map_parameter]
  rfl

theorem scaling_source_function {T : Scheme} (sT : T ⟶ ComplexBase)
    (c a : RingSections T ⊤) :
    (DualScaling.map sT c).appTop ((projection sT).appTop a) =
      (projection sT).appTop a := by
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, DualScaling.map_projection]

variable {n : ℕ} {X : ContactFanoManifold n} {D : SuitablePair X} (G : Germ D)

/-- On every actual reciprocal overlap, the local auxiliary source map
is the original punctured-branch source map with epsilon multiplied by u. -/
theorem firstNodeMap_scaled_outer {T : Scheme} (sT : T ⟶ ComplexBase)
    (u w : T ⟶ AffineLine) (hu : u ≫ affineLineToC = sT)
    (hw : w ≫ affineLineToC = sT)
    (huw : u.appTop parameterFunction * w.appTop parameterFunction = 1) :
    DualThickening.map u hu ≫ firstNodeMap G =
      DualScaling.map sT (u.appTop parameterFunction) ≫
        DualThickening.map w hw ≫ firstOuterMap G := by
  unfold firstNodeMap firstOuterMap
  simp only [nodeFamily_natural G.source (toC sT) (toC affineLineToC)
      (DualThickening.map u hu) (DualThickening.map_overC u hu),
    outerFamily_natural G.source 1 (by decide) (toC sT) (toC affineLineToC)
      (DualThickening.map w hw) (DualThickening.map_overC w hw),
    sourceChange_coordinate_general, sourceChange_epsilon_general,
    sourceChange_coordinate_general, sourceChange_epsilon_general,
    outerFamily_natural G.source 1 (by decide) (toC sT) (toC sT)
      (DualScaling.map sT (u.appTop parameterFunction)) (DualScaling.map_overC _ _),
    DualScaling.map_epsilon, scaling_source_function]
  simp only [mul_comm (DualScaling.globalEpsilon sT)
    ((projection sT).appTop (u.appTop parameterFunction))]
  apply nodeFamily_eq_firstOuter
  rw [← map_mul, huw, map_one]

theorem secondNodeMap_scaled_outer {T : Scheme} (sT : T ⟶ ComplexBase)
    (u w : T ⟶ AffineLine) (hu : u ≫ affineLineToC = sT)
    (hw : w ≫ affineLineToC = sT)
    (huw : u.appTop parameterFunction * w.appTop parameterFunction = 1) :
    DualThickening.map u hu ≫ secondNodeMap G =
      DualScaling.map sT (u.appTop parameterFunction) ≫
        DualThickening.map w hw ≫ secondOuterMap G := by
  unfold secondNodeMap secondOuterMap
  simp only [nodeFamily_natural G.source (toC sT) (toC affineLineToC)
      (DualThickening.map u hu) (DualThickening.map_overC u hu),
    outerFamily_natural G.source 2 (by decide) (toC sT) (toC affineLineToC)
      (DualThickening.map w hw) (DualThickening.map_overC w hw),
    sourceChange_coordinate_general, sourceChange_epsilon_general,
    sourceChange_coordinate_general, sourceChange_epsilon_general,
    outerFamily_natural G.source 2 (by decide) (toC sT) (toC sT)
      (DualScaling.map sT (u.appTop parameterFunction)) (DualScaling.map_overC _ _),
    DualScaling.map_epsilon, scaling_source_function]
  apply nodeFamily_eq_secondOuter
  rw [← map_mul, huw, map_one]

theorem firstNodeDeformation_scaled_outer {T : Scheme} (sT : T ⟶ ComplexBase)
    (u w : T ⟶ AffineLine) (hu : u ≫ affineLineToC = sT)
    (hw : w ≫ affineLineToC = sT)
    (huw : u.appTop parameterFunction * w.appTop parameterFunction = 1)
    (z : G.chart.Tangent) (hz : G.baseDifferential z = 1) :
    ((firstNodeDeformation G z hz).pullback u hu).map =
      (DualScaling.deformation sT ((firstOuterDeformation G z hz).pullback w hw)
        (u.appTop parameterFunction)).map := by
  change DualThickening.map u hu ≫ firstNodeMap G ≫ deformedMap G z hz =
    DualScaling.map sT (u.appTop parameterFunction) ≫
      DualThickening.map w hw ≫ firstOuterMap G ≫ deformedMap G z hz
  simpa only [Category.assoc] using congrArg (fun f => f ≫ deformedMap G z hz)
    (firstNodeMap_scaled_outer G sT u w hu hw huw)

theorem secondNodeDeformation_scaled_outer {T : Scheme} (sT : T ⟶ ComplexBase)
    (u w : T ⟶ AffineLine) (hu : u ≫ affineLineToC = sT)
    (hw : w ≫ affineLineToC = sT)
    (huw : u.appTop parameterFunction * w.appTop parameterFunction = 1)
    (z : G.chart.Tangent) (hz : G.baseDifferential z = 1) :
    ((secondNodeDeformation G z hz).pullback u hu).map =
      (DualScaling.deformation sT ((secondOuterDeformation G z hz).pullback w hw)
        (u.appTop parameterFunction)).map := by
  change DualThickening.map u hu ≫ secondNodeMap G ≫ deformedMap G z hz =
    DualScaling.map sT (u.appTop parameterFunction) ≫
      DualThickening.map w hw ≫ secondOuterMap G ≫ deformedMap G z hz
  simpa only [Category.assoc] using congrArg (fun f => f ≫ deformedMap G z hz)
    (secondNodeMap_scaled_outer G sT u w hu hw huw)

end BranchCharts

namespace DeformationGluing

open CoordinateCharts DualThickening FamilyVariation

/-- The canonical base-change square for a source map on dual thickenings. -/
def mapPullbackIso {Y Z : Scheme} {sY : Y ⟶ ComplexBase} {sZ : Z ⟶ ComplexBase}
    (g : Y ⟶ Z) (hg : g ≫ sZ = sY) :
    space sY ≅ pullback g (projection sZ) := by
  subst sY
  exact (pullbackRightPullbackFstIso sZ Infinitesimal.dualToC g).symm

theorem mapPullbackIso_snd {Y Z : Scheme}
    {sY : Y ⟶ ComplexBase} {sZ : Z ⟶ ComplexBase}
    (g : Y ⟶ Z) (hg : g ≫ sZ = sY) :
    (mapPullbackIso g hg).hom ≫ pullback.snd g (projection sZ) =
      DualThickening.map g hg := by
  subst sY
  apply pullback.hom_ext
  · change ((pullbackRightPullbackFstIso sZ Infinitesimal.dualToC g).inv ≫
        pullback.snd g (pullback.fst sZ Infinitesimal.dualToC)) ≫
        pullback.fst sZ Infinitesimal.dualToC = _
    rw [Category.assoc, pullbackRightPullbackFstIso_inv_snd_fst]
    exact (DualThickening.map_projection g rfl).symm
  · change ((pullbackRightPullbackFstIso sZ Infinitesimal.dualToC g).inv ≫
        pullback.snd g (pullback.fst sZ Infinitesimal.dualToC)) ≫
        pullback.snd sZ Infinitesimal.dualToC = _
    rw [Category.assoc, pullbackRightPullbackFstIso_inv_snd_snd]
    exact (DualThickening.map_parameter g rfl).symm

theorem map_open {Y Z : Scheme} {sY : Y ⟶ ComplexBase} {sZ : Z ⟶ ComplexBase}
    (g : Y ⟶ Z) [IsOpenImmersion g] (hg : g ≫ sZ = sY) :
    IsOpenImmersion (DualThickening.map g hg) := by
  rw [← mapPullbackIso_snd g hg]
  infer_instance

def chartMap (i : Fin 2) : space affineLineToC ⟶ space P.structureMap :=
  DualThickening.map (ratioPoint i).val (ratioPoint i).property

instance chartMap_open (i : Fin 2) : IsOpenImmersion (chartMap i) := by
  letI := ratioPoint_openImmersion i
  exact map_open (ratioPoint i).val (ratioPoint i).property

def cover : (space P.structureMap).OpenCover where
  I₀ := Fin 2
  X _ := space affineLineToC
  f := chartMap
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, inferInstance⟩
    intro x
    have hx : projection P.structureMap x ∈ (⨆ i : Fin 2, ratioOpen i) := by
      rw [ratioOpen_cover]
      trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    have hr : projection P.structureMap x ∈ Set.range (ratioPoint i).val := by
      rw [ratioPoint_range]
      exact hi
    obtain ⟨a, ha⟩ := hr
    refine ⟨i, ⟨zeroSection affineLineToC a, ?_⟩⟩
    have h := congrArg (fun f : AffineLine ⟶ space P.structureMap => f a)
      (zeroSection_naturality (ratioPoint i).val (ratioPoint i).property)
    change chartMap i (zeroSection affineLineToC a) =
      zeroSection P.structureMap ((ratioPoint i).val a) at h
    rw [h, ha, zeroSection_projection_apply]

/-- Ratios at the same projective point multiply to one, including on
nonreduced test schemes. This is proved from the chosen quotient sections. -/
theorem ratios_reciprocal {T : Scheme} (u w : T ⟶ AffineLine)
    (h : u ≫ (ratioPoint 0).val = w ≫ (ratioPoint 1).val) :
    u.appTop parameterFunction * w.appTop parameterFunction = 1 := by
  let f := u ≫ (ratioPoint 0).val
  letI : IsIso (pullSection f ((projectiveCoordinates 1).coordinate 0)) :=
    ratioPull_self_isIso u 0
  letI : IsIso (pullSection f ((projectiveCoordinates 1).coordinate 1)) := by
    dsimp [f]
    rw [h]
    exact ratioPull_self_isIso w 1
  have h0 : ratioFunction f 0 = u.appTop parameterFunction := ratioFunction_comp u 0
  have h1 : ratioFunction f 1 = w.appTop parameterFunction := by
    letI := ratioPull_self_isIso w 1
    dsimp [f]
    simpa only [h] using ratioFunction_comp w 1
  have e0 : scalarSection (ratioFunction f 0) =
      pullSection f ((projectiveCoordinates 1).coordinate 1) ≫
        (asIso (pullSection f ((projectiveCoordinates 1).coordinate 0))).inv := by
    change sectionFromValue (sectionValue _) = _
    exact sectionFromValue_sectionValue _
  have e1 : scalarSection (ratioFunction f 1) =
      pullSection f ((projectiveCoordinates 1).coordinate 0) ≫
        (asIso (pullSection f ((projectiveCoordinates 1).coordinate 1))).inv := by
    change sectionFromValue (sectionValue _) = _
    exact sectionFromValue_sectionValue _
  have he : scalarSection (ratioFunction f 0 * ratioFunction f 1) = scalarSection 1 := by
    rw [SourceAffineCharts.scalarSection_mul, e0, e1, scalarSection_one]
    change (asIso (pullSection f ((projectiveCoordinates 1).coordinate 1))).hom ≫
        (asIso (pullSection f ((projectiveCoordinates 1).coordinate 0))).inv ≫
        ((asIso (pullSection f ((projectiveCoordinates 1).coordinate 0))).hom ≫
          (asIso (pullSection f ((projectiveCoordinates 1).coordinate 1))).inv) = _
    rw [Iso.inv_hom_id_assoc, Iso.hom_inv_id]
  have hv := congrArg sectionValue he
  simpa only [scalarSection, sectionFromValue_spec, h0, h1] using hv

abbrev Overlap : Scheme := pullback (ratioPoint 0).val (ratioPoint 1).val

def overlapFirst : Overlap ⟶ AffineLine := pullback.fst _ _
def overlapSecond : Overlap ⟶ AffineLine := pullback.snd _ _
def overlapBase : Overlap ⟶ ComplexBase := overlapFirst ≫ affineLineToC

theorem overlapSecond_over : overlapSecond ≫ affineLineToC = overlapBase := by
  have h := congrArg (fun f => f ≫ P.structureMap)
    (pullback.condition (f := (ratioPoint 0).val) (g := (ratioPoint 1).val))
  simpa only [Category.assoc, (ratioPoint 0).property, (ratioPoint 1).property,
    overlapFirst, overlapSecond, overlapBase] using h.symm

theorem overlap_reciprocal :
    overlapFirst.appTop parameterFunction * overlapSecond.appTop parameterFunction = 1 :=
  ratios_reciprocal overlapFirst overlapSecond pullback.condition

/-- The intersection of the two thickened charts factors through the
thickening of the actual central chart intersection, with both maps fixed. -/
theorem overlap_factor {T : Scheme}
    (a b : T ⟶ space affineLineToC) (h : a ≫ chartMap 0 = b ≫ chartMap 1) :
    ∃ q : T ⟶ space overlapBase,
      q ≫ DualThickening.map overlapFirst rfl = a ∧
        q ≫ DualThickening.map overlapSecond overlapSecond_over = b := by
  have hp : (a ≫ projection affineLineToC) ≫ (ratioPoint 0).val =
      (b ≫ projection affineLineToC) ≫ (ratioPoint 1).val := by
    have hc := congrArg (fun f => f ≫ projection P.structureMap) h
    simpa only [chartMap, Category.assoc, DualThickening.map_projection] using hc
  have he : a ≫ parameter affineLineToC = b ≫ parameter affineLineToC := by
    have hc := congrArg (fun f => f ≫ parameter P.structureMap) h
    simpa only [chartMap, Category.assoc, DualThickening.map_parameter] using hc
  let r : T ⟶ Overlap := pullback.lift
    (a ≫ projection affineLineToC) (b ≫ projection affineLineToC) hp
  let q : T ⟶ space overlapBase := pullback.lift r (a ≫ parameter affineLineToC) (by
    change r ≫ overlapFirst ≫ affineLineToC =
      (a ≫ parameter affineLineToC) ≫ Infinitesimal.dualToC
    rw [← Category.assoc, show r ≫ overlapFirst = a ≫ projection affineLineToC from
      pullback.lift_fst _ _ _, Category.assoc, Category.assoc, parameter_overC]
    rfl)
  refine ⟨q, ?_, ?_⟩
  · apply pullback.hom_ext
    · change (q ≫ DualThickening.map overlapFirst rfl) ≫ projection affineLineToC =
        a ≫ projection affineLineToC
      rw [Category.assoc, DualThickening.map_projection, ← Category.assoc]
      simp only [q, r, projection, overlapFirst, pullback.lift_fst, pullback.lift_fst_assoc]
    · change (q ≫ DualThickening.map overlapFirst rfl) ≫ parameter affineLineToC =
        a ≫ parameter affineLineToC
      rw [Category.assoc, DualThickening.map_parameter]
      exact pullback.lift_snd _ _ _
  · apply pullback.hom_ext
    · change (q ≫ DualThickening.map overlapSecond overlapSecond_over) ≫
        projection affineLineToC = b ≫ projection affineLineToC
      rw [Category.assoc, DualThickening.map_projection, ← Category.assoc]
      simp only [q, r, projection, overlapSecond, pullback.lift_fst, pullback.lift_snd, pullback.lift_snd_assoc]
    · change (q ≫ DualThickening.map overlapSecond overlapSecond_over) ≫
        parameter affineLineToC = b ≫ parameter affineLineToC
      rw [Category.assoc, DualThickening.map_parameter]
      exact (pullback.lift_snd _ _ _).trans he

variable {Z : Scheme} (sZ : Z ⟶ ComplexBase) (f : ProjectiveLine ⟶ Z)
variable (E₀ : Deformation affineLineToC sZ ((ratioPoint 0).val ≫ f))
variable (E₁ : Deformation affineLineToC sZ ((ratioPoint 1).val ≫ f))
variable (hE : (E₀.pullback overlapFirst rfl).map =
  (E₁.pullback overlapSecond overlapSecond_over).map)

def localMap (i : Fin 2) : space affineLineToC ⟶ Z :=
  Fin.cases E₀.map (fun _ => E₁.map) i

include hE in
theorem localMap_compatible {T : Scheme} (i j : Fin 2)
    (a b : T ⟶ space affineLineToC) (h : a ≫ chartMap i = b ≫ chartMap j) :
    a ≫ localMap sZ f E₀ E₁ i = b ≫ localMap sZ f E₀ E₁ j := by
  have h01 : ∀ (a b : T ⟶ space affineLineToC), a ≫ chartMap 0 = b ≫ chartMap 1 →
      a ≫ E₀.map = b ≫ E₁.map := by
    intro a b h
    obtain ⟨q, hq₀, hq₁⟩ := overlap_factor a b h
    rw [← hq₀, ← hq₁, Category.assoc, Category.assoc]
    exact congrArg (fun k => q ≫ k) hE
  fin_cases i <;> fin_cases j
  · rw [(cancel_mono (chartMap 0)).mp h]
  · exact h01 a b h
  · exact (h01 b a h.symm).symm
  · rw [(cancel_mono (chartMap 1)).mp h]

def gluedMap : space P.structureMap ⟶ Z :=
  cover.glueMorphisms (localMap sZ f E₀ E₁)
    (fun i j => localMap_compatible sZ f E₀ E₁ hE i j _ _ pullback.condition)

@[reassoc] theorem chart_gluedMap (i : Fin 2) :
    chartMap i ≫ gluedMap sZ f E₀ E₁ hE = localMap sZ f E₀ E₁ i :=
  cover.ι_glueMorphisms _ _ i

theorem gluedMap_over : gluedMap sZ f E₀ E₁ hE ≫ sZ = toC P.structureMap := by
  apply cover.hom_ext
  intro i
  change Fin 2 at i
  change chartMap i ≫ (gluedMap sZ f E₀ E₁ hE ≫ sZ) = chartMap i ≫ toC P.structureMap
  rw [← Category.assoc, chart_gluedMap]
  have hc := DualThickening.map_overC (ratioPoint i).val (ratioPoint i).property
  change chartMap i ≫ toC P.structureMap = toC affineLineToC at hc
  rw [hc]
  fin_cases i
  · change E₀.map ≫ sZ = toC affineLineToC
    exact E₀.overC
  · change E₁.map ≫ sZ = toC affineLineToC
    exact E₁.overC

theorem gluedMap_reduces : zeroSection P.structureMap ≫ gluedMap sZ f E₀ E₁ hE = f := by
  apply SourceAffineCharts.projective_maps_ext
  intro i
  rw [← Category.assoc, ← zeroSection_naturality (ratioPoint i).val (ratioPoint i).property,
    Category.assoc]
  change zeroSection affineLineToC ≫ chartMap i ≫ gluedMap sZ f E₀ E₁ hE = _
  rw [chart_gluedMap]
  fin_cases i
  · exact E₀.reduces
  · exact E₁.reduces

/-- Compatible actual maps on the two dual charts glue to an actual
global first-order deformation, with its original central map. -/
def glued : Deformation P.structureMap sZ f where
  map := gluedMap sZ f E₀ E₁ hE
  overC := gluedMap_over sZ f E₀ E₁ hE
  reduces := gluedMap_reduces sZ f E₀ E₁ hE

theorem glued_first :
    (glued sZ f E₀ E₁ hE).pullback (ratioPoint 0).val (ratioPoint 0).property = E₀ := by
  apply Deformation.ext
  exact chart_gluedMap sZ f E₀ E₁ hE 0

theorem glued_second :
    (glued sZ f E₀ E₁ hE).pullback (ratioPoint 1).val (ratioPoint 1).property = E₁ := by
  apply Deformation.ext
  exact chart_gluedMap sZ f E₀ E₁ hE 1

/-- A divisible outer-chart variation is an actual rescaling of a unique
outer-chart deformation. Its reciprocal rescaling then glues with the
specified node-chart map to a global deformation of the original curve. -/
theorem exists_global_of_divisible {d : ℕ} (M : SmoothProperComplexVariety d)
    (f : ProjectiveLine ⟶ M.scheme) (hf : f ≫ M.structureMap = P.structureMap)
    (E₀ : Deformation affineLineToC M.structureMap ((ratioPoint 0).val ≫ f))
    (Einf : Deformation affineLineToC M.structureMap ((ratioPoint 1).val ≫ f))
    (hscaled : (E₀.pullback overlapFirst rfl).map =
      (DualScaling.deformation overlapBase
        (Einf.pullback overlapSecond overlapSecond_over)
        (overlapFirst.appTop parameterFunction)).map)
    (hdiv : ∃ b : GlobalSections (pullbackModule ((ratioPoint 1).val ≫ f)
      (tangentSheaf M.structureMap)), Einf.variation M = parameterFunction • b) :
    ∃ E : Deformation P.structureMap M.structureMap f,
      E.pullback (ratioPoint 0).val (ratioPoint 0).property = E₀ := by
  obtain ⟨b, hb⟩ := hdiv
  have hfo : ((ratioPoint 1).val ≫ f) ≫ M.structureMap = affineLineToC := by
    rw [Category.assoc, hf, (ratioPoint 1).property]
  obtain ⟨B, hB⟩ := (Normalization.NodalTangent.variation_bijective M hfo).surjective b
  have houter : Einf = DualScaling.deformation affineLineToC B parameterFunction := by
    apply (Normalization.NodalTangent.variation_bijective M hfo).injective
    change Einf.variation M = (DualScaling.deformation affineLineToC B parameterFunction).variation M
    change B.variation M = b at hB
    rw [DualScaling.deformation_variation, hB]
    exact hb
  have hcompat : (E₀.pullback overlapFirst rfl).map =
      (B.pullback overlapSecond overlapSecond_over).map := by
    rw [houter, DualScaling.deformation_sourceChange, DualScaling.deformation_mul,
      overlap_reciprocal, DualScaling.deformation_one] at hscaled
    exact hscaled
  exact ⟨glued M.structureMap f E₀ B hcompat,
    glued_first M.structureMap f E₀ B hcompat⟩

end DeformationGluing

namespace GlobalAuxiliary

open CoordinateCharts FamilyVariation BranchCharts

variable {n : ℕ} {X : ContactFanoManifold n} {D : SuitablePair X} (G : Germ D)

/-- The first node variation extends across infinity because its
punctured variation vanishes at the fixed endpoint. -/
theorem first_exists (z : G.chart.Tangent) (hz : G.baseDifferential z = 1)
    (he : G.endpointDifferential z = 0) :
    ∃ E : Deformation P.structureMap X.variety.structureMap D.first.curve.map,
      E.pullback (ratioPoint 0).val (ratioPoint 0).property =
        firstNodeDeformation G z hz := by
  apply DeformationGluing.exists_global_of_divisible X.variety D.first.curve.map
    D.first.curve.overC (firstNodeDeformation G z hz) (firstOuterDeformation G z hz)
  · exact firstNodeDeformation_scaled_outer G DeformationGluing.overlapBase
      DeformationGluing.overlapFirst DeformationGluing.overlapSecond rfl
      DeformationGluing.overlapSecond_over DeformationGluing.overlap_reciprocal z hz
  · exact firstOuter_divisible G z hz he

/-- The second branch uses the same construction with the two node
coordinates interchanged; no independent mixed constant is introduced. -/
theorem second_exists (z : G.chart.Tangent) (hz : G.baseDifferential z = 1)
    (he : G.endpointDifferential z = 0) :
    ∃ E : Deformation P.structureMap X.variety.structureMap D.second.curve.map,
      E.pullback (ratioPoint 0).val (ratioPoint 0).property =
        secondNodeDeformation G z hz := by
  apply DeformationGluing.exists_global_of_divisible X.variety D.second.curve.map
    D.second.curve.overC (secondNodeDeformation G z hz) (secondOuterDeformation G z hz)
  · exact secondNodeDeformation_scaled_outer G DeformationGluing.overlapBase
      DeformationGluing.overlapFirst DeformationGluing.overlapSecond rfl
      DeformationGluing.overlapSecond_over DeformationGluing.overlap_reciprocal z hz
  · exact secondOuter_divisible G z hz he

end GlobalAuxiliary

namespace LocalContactCovector

open LeBrunSalamon.Refinement.Jets
open PointFrame.LocalFrameJetProof
open ContactDerivativeIsoProof

/-- Fixing a genuine local section in the second argument of a sheaf
pairing gives an actual morphism on the corresponding open site. -/
def pairWith {Y : Scheme} {E F H : OModule Y}
    (b : SheafBilinearMap E F H) (U : Y.Opens) (w : SectionsOn F U) :
    E.over U ⟶ H.over U :=
  HomConstruction.sectionOverEquiv E H U
    (HomConstruction.localCurry (TensorConstruction.flip b) U w)

theorem pairWith_apply {Y : Scheme} {E F H : OModule Y}
    (b : SheafBilinearMap E F H) (U : Y.Opens) (w : SectionsOn F U)
    (V : Over U) (v : SectionsOn E V.left) :
    (pairWith b U w).val.app (op V) v =
      b.apply V.left v (F.presheaf.map V.hom.op w) := rfl

/-- A genuine local pairing is pulled back with its actual local section,
not with an arbitrary section-space identification. -/
theorem pullOver_pairWith {Y Z : Scheme} (f : Z ⟶ Y)
    {E F H : OModule Y} (b : SheafBilinearMap E F H)
    (U : Y.Opens) (w : SectionsOn F U) :
    pullOverHom f U (pairWith b U w) =
      pairWith (pullbackPair f b) (f ⁻¹ᵁ U) (pullLocalSection f F U w) := by
  apply (PullbackPairProof.localUnitPrecompose_bijective f E (pullbackModule f H) U).injective
  apply SheafOfModules.hom_ext
  ext V v
  change (pullOverHom f U (pairWith b U w)).val.app
      (op ((Over.post (TopologicalSpace.Opens.map f.base)).obj V.unop))
      (pullLocalSection f E V.unop.left v) =
    (pairWith (pullbackPair f b) (f ⁻¹ᵁ U) (pullLocalSection f F U w)).val.app
      (op ((Over.post (TopologicalSpace.Opens.map f.base)).obj V.unop))
      (pullLocalSection f E V.unop.left v)
  rw [pullOverHom_unit, pairWith_apply, pairWith_apply]
  change pullLocalSection f H V.unop.left
      (b.apply V.unop.left v (F.presheaf.map V.unop.hom.op w)) =
    (pullbackPair f b).apply (f ⁻¹ᵁ V.unop.left)
      (pullLocalSection f E V.unop.left v)
      ((pullbackModule f F).presheaf.map
        ((TopologicalSpace.Opens.map f.base).map V.unop.hom).op
        (pullLocalSection f F U w))
  rw [PullbackPairProof.pullLocalSection_restrict, pullbackPair_normalized]

theorem pullOver_global {Y Z : Scheme} (f : Z ⟶ Y) (U : Y.Opens)
    {E F : OModule Y} (p : E ⟶ F) :
    pullOverHom f U (p.over U) = ((Scheme.Modules.pullback f).map p).over (f ⁻¹ᵁ U) := by
  apply (PullbackPairProof.localUnitPrecompose_bijective f E (pullbackModule f F) U).injective
  apply SheafOfModules.hom_ext
  ext V v
  change (pullOverHom f U (p.over U)).val.app
      (op ((Over.post (TopologicalSpace.Opens.map f.base)).obj V.unop))
      (pullLocalSection f E V.unop.left v) =
    ((Scheme.Modules.pullback f).map p).app (f ⁻¹ᵁ V.unop.left)
      (pullLocalSection f E V.unop.left v)
  rw [pullOverHom_unit]
  change pullLocalSection f F V.unop.left (p.app V.unop.left v) = _
  exact (ExternalExchangeCoherenceProof.pullLocalSection_map f p V.unop.left v).symm

theorem frameIso_inv_apply {Y : Scheme} {L : LineBundle Y}
    (H : AffineLineFrame L) (s : SectionsOn L.sheaf H.openSet) :
    (frameIso H).inv.val.app (op (Over.mk (𝟙 H.openSet))) s = H.coefficient s := by
  apply H.coefficient.symm.injective
  rw [H.coefficient.symm_apply_apply]
  have h := congrArg (fun q : L.sheaf.over H.openSet ⟶ L.sheaf.over H.openSet =>
    q.val.app (op (Over.mk (𝟙 H.openSet))) s) (frameIso H).inv_hom_id
  change (frameMap H).val.app (op (Over.mk (𝟙 H.openSet)))
    ((frameIso H).inv.val.app (op (Over.mk (𝟙 H.openSet))) s) = s at h
  rw [frameMap_apply] at h
  exact h

/-- Equality against the actual affine tangent sections is equality of
actual local sheaf morphisms, by affine quasi-coherent faithfulness. -/
theorem contact_eq_pair {n : ℕ} {X : SmoothProperComplexVariety (2*n+1)}
    (C : IntrinsicContactStructure X) (H : AffineLineFrame C.sequence.line)
    (w : SectionsOn (cotangentSheaf X.structureMap) H.openSet)
    (hw : ∀ v : SectionsOn (tangentSheaf X.structureMap) H.openSet,
      (dualEvaluation (cotangentSheaf X.structureMap)).apply H.openSet v w =
        localContactValue C H v) :
    pairWith (dualEvaluation (cotangentSheaf X.structureMap)) H.openSet w =
      C.sequence.form.over H.openSet ≫ (frameIso H).inv := by
  letI := LocalExtensionSplitting.quasicoherent_of_locallyFreeRank
    (smooth_tangent_rank X.structureMap (2*n+1) X.smooth)
  letI := LocalExtensionSplitting.quasicoherent_of_locallyFreeRank (structureModule_rank X.scheme)
  apply Skeleton.AdjointContactTransportProof.affine_over_hom_ext H.openSet H.isAffine
  intro v
  rw [pairWith_apply]
  change (dualEvaluation (cotangentSheaf X.structureMap)).apply H.openSet v
    ((cotangentSheaf X.structureMap).presheaf.map (𝟙 H.openSet).op w) = _
  have hid : (cotangentSheaf X.structureMap).presheaf.map (𝟙 H.openSet).op w = w := by simp
  rw [hid]
  change (dualEvaluation (cotangentSheaf X.structureMap)).apply H.openSet v w =
    (frameIso H).inv.val.app (op (Over.mk (𝟙 H.openSet)))
      (C.sequence.form.app H.openSet v)
  rw [frameIso_inv_apply]
  exact hw v

/-- The framed contact value on any pulled-back tangent vector is the
canonical dual pairing with the pulled local cotangent section. -/
theorem pulled_contact_pair {n : ℕ} {X : SmoothProperComplexVariety (2*n+1)}
    (C : IntrinsicContactStructure X) (H : AffineLineFrame C.sequence.line)
    (w : SectionsOn (cotangentSheaf X.structureMap) H.openSet)
    (hw : ∀ v : SectionsOn (tangentSheaf X.structureMap) H.openSet,
      (dualEvaluation (cotangentSheaf X.structureMap)).apply H.openSet v w =
        localContactValue C H v)
    {Y : Scheme} (f : Y ⟶ X.scheme) (V : Y.Opens) (hV : V ≤ f ⁻¹ᵁ H.openSet)
    (v : SectionsOn (pullbackModule f (tangentSheaf X.structureMap)) V) :
    coefficientOn H f V hV (((Scheme.Modules.pullback f).map C.sequence.form).app V v) =
      (dualEvaluation (pullbackModule f (cotangentSheaf X.structureMap))).apply V
        ((dualBaseChange f (cotangentSheaf X.structureMap)).app V v)
        ((pullbackModule f (cotangentSheaf X.structureMap)).presheaf.map (homOfLE hV).op
          (pullLocalSection f (cotangentSheaf X.structureMap) H.openSet w)) := by
  have he := congrArg (fun q => pullOverHom f H.openSet q)
    (contact_eq_pair C H w hw)
  rw [pullOver_pairWith, pullOverHom_comp, pullOver_global] at he
  have hv := congrArg (fun q =>
    (q ≫ (unitPullbackMap f).over (f ⁻¹ᵁ H.openSet)).val.app
      (op (Over.mk (homOfLE hV))) v) he
  change (unitPullbackMap f).app V
      ((pullbackPair f (dualEvaluation (cotangentSheaf X.structureMap))).apply V v
        ((pullbackModule f (cotangentSheaf X.structureMap)).presheaf.map (homOfLE hV).op
          (pullLocalSection f (cotangentSheaf X.structureMap) H.openSet w))) =
    coefficientOn H f V hV (((Scheme.Modules.pullback f).map C.sequence.form).app V v) at hv
  exact hv.symm.trans (FamilyVariation.dualBaseChange_evaluate f
    (cotangentSheaf X.structureMap) V v _).symm

/-- All local linear forms detect a section of a finite locally free
sheaf. Canonical biduality supplies the detection; no pointwise criterion
on a nonreduced thickening is used. -/
theorem section_zero_of_dualPair_zero {Y : Scheme} {E : OModule Y} {r : ℕ}
    (hE : IsLocallyFreeOfRank E r) (U : Y.Opens) (w : SectionsOn E U)
    (hw : ∀ (V : Y.Opens) (i : V ⟶ U) (φ : SectionsOn (dualSheaf E) V),
      (dualEvaluation E).apply V φ (E.presheaf.map i.op w) = 0) : w = 0 := by
  obtain ⟨q, hq, hfree⟩ := hE
  letI := hq
  letI : IsIso (HomConstruction.Generic.bidualMap (R := Y.sheaf) E) :=
    HomConstruction.Generic.isIso_bidualMap_of_free_cover E q.X q.coversTop
      (fun _ => Fin r) (fun i => SheafTensor.localBasisTrivialization q hfree i)
  apply (ConcreteCategory.bijective_of_isIso
    ((SheafOfModules.evaluation _ (op U)).map
      (HomConstruction.Generic.bidualMap (R := Y.sheaf) E))).injective
  rw [map_zero]
  apply PresheafOfModules.hom_ext
  intro V
  ext φ
  let ψ := (internalHomGenericIso E (structureModule Y)).inv.app V.unop.left φ
  have hi : (internalHomGenericIso E (structureModule Y)).hom.app V.unop.left ψ = φ := by
    exact congrArg (fun k => k.app V.unop.left φ)
      (internalHomGenericIso E (structureModule Y)).inv_hom_id
  change HomConstruction.Generic.evaluationAt (R := Y.sheaf) E (structureModule Y)
    V.unop.left φ (E.presheaf.map V.unop.hom.op w) = 0
  rw [← hi, internalHomGenericIso_evaluate_pair]
  exact hw V.unop.left V.unop.hom ψ

/-- A finite expression in genuine differentials gives the corresponding
local cotangent section and its exact evaluation on every local vector. -/
def finiteForm {Y : Scheme} (sY : Y ⟶ ComplexBase) (U : Y.Opens)
    {m : ℕ} (a b : Fin m → RingSections Y U) : SectionsOn (cotangentSheaf sY) U :=
  ∑ i, a i • (cotangentPresentation sY).differential.apply U (b i)

theorem finiteForm_pair {Y : Scheme} (sY : Y ⟶ ComplexBase) (U : Y.Opens)
    {m : ℕ} (a b : Fin m → RingSections Y U)
    (v : SectionsOn (tangentSheaf sY) U) :
    (dualEvaluation (cotangentSheaf sY)).apply U v (finiteForm sY U a b) =
      ∑ i, a i * tangentActs sY U v (b i) := by
  simp only [finiteForm, map_sum, map_smul, smul_eq_mul]
  rfl

theorem pullLocalSection_sum {Y Z : Scheme} (f : Z ⟶ Y) (E : OModule Y)
    (U : Y.Opens) {m : ℕ} (v : Fin m → SectionsOn E U) :
    pullLocalSection f E U (∑ i, v i) = ∑ i, pullLocalSection f E U (v i) := by
  exact map_sum (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app E).app U).hom v _

theorem pullLocalSection_zero {Y Z : Scheme} (f : Z ⟶ Y) (E : OModule Y)
    (U : Y.Opens) : pullLocalSection f E U 0 = 0 := by
  exact (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app E).app U).hom.map_zero

end LocalContactCovector

namespace InfinitesimalHorizontality

open DualThickening FamilyVariation
open LocalContactCovector
open LeBrunSalamon.Refinement.Jets.PointFrame.LocalFrameJetProof

variable {n : ℕ} {X : ContactFanoManifold n}

/-- The relative tangent map is the actual dual of the relative
cotangent map, after the prescribed base-change comparisons. -/
theorem relativeDifferential_normalized (f : FreeLine X)
    (E : Deformation P.structureMap X.variety.structureMap f.curve.map) :
    relativeDifferential X.variety E ≫
      dualBaseChange E.map (cotangentSheaf X.variety.structureMap) =
    dualBaseChange (projection P.structureMap) (cotangentSheaf P.structureMap) ≫
      ContactDerivativeIsoProof.dualMap (relativeCotangent X.variety E) := by
  letI := dualBaseChange_isIso E.map
    (smooth_cotangent_rank X.variety.structureMap (2*n+1) X.variety.smooth)
  simp only [relativeDifferential, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-- Global first-order horizontality annihilates the actual local
cotangent contact form. The proof tests all local dual sections on the
whole nonreduced thickening. -/
theorem relativeCotangent_contact_zero (f : FreeLine X)
    (E : Deformation P.structureMap X.variety.structureMap f.curve.map)
    (H : AffineLineFrame X.contact.sequence.line)
    (w : SectionsOn (cotangentSheaf X.variety.structureMap) H.openSet)
    (hw : ∀ v : SectionsOn (tangentSheaf X.variety.structureMap) H.openSet,
      (dualEvaluation (cotangentSheaf X.variety.structureMap)).apply H.openSet v w =
        localContactValue X.contact H v) :
    (relativeCotangent X.variety E).app (E.map ⁻¹ᵁ H.openSet)
      (pullLocalSection E.map (cotangentSheaf X.variety.structureMap) H.openSet w) = 0 := by
  let Ω := cotangentSheaf P.structureMap
  have hΩ : IsLocallyFreeOfRank Ω 1 :=
    smooth_cotangent_rank P.structureMap 1 (projectiveLineVariety P).smooth
  letI := dualBaseChange_isIso (projection P.structureMap) hΩ
  apply section_zero_of_dualPair_zero (pullback_locallyFree (projection P.structureMap) hΩ)
  intro V i φ
  obtain ⟨u, hu⟩ := (ConcreteCategory.bijective_of_isIso
    ((dualBaseChange (projection P.structureMap) Ω).app V)).surjective φ
  let v := (relativeDifferential X.variety E).app V u
  have hform : ((Scheme.Modules.pullback E.map).map X.contact.sequence.form).app V v = 0 := by
    exact congrArg (fun q => q.app V u) (relative_contact_zero f E)
  have hp := pulled_contact_pair X.contact H w hw E.map V (leOfHom i) v
  rw [hform, map_zero] at hp
  have hn := congrArg (fun q => q.app V u) (relativeDifferential_normalized f E)
  change (dualBaseChange E.map (cotangentSheaf X.variety.structureMap)).app V v =
    (ContactDerivativeIsoProof.dualMap (relativeCotangent X.variety E)).app V
      ((dualBaseChange (projection P.structureMap) Ω).app V u) at hn
  rw [hu] at hn
  rw [hn, ContactDerivativeIsoProof.dualMap_evaluate] at hp
  rw [sheafHom_naturality]
  exact hp.symm

/-- The undivided scalar differential equation on an actual first-order
line deformation, for any finite expression of its contact covector. -/
theorem differential_sum_zero (f : FreeLine X)
    (E : Deformation P.structureMap X.variety.structureMap f.curve.map)
    (H : AffineLineFrame X.contact.sequence.line)
    {m : ℕ} (a b : Fin m → RingSections X.variety.scheme H.openSet)
    (hab : ∀ v : SectionsOn (tangentSheaf X.variety.structureMap) H.openSet,
      localContactValue X.contact H v =
        ∑ i, a i * tangentActs X.variety.structureMap H.openSet v (b i)) :
    (∑ i, E.map.app H.openSet (a i) •
      (cotangentPresentation (parameter P.structureMap)).differential.apply
        (E.map ⁻¹ᵁ H.openSet) (E.map.app H.openSet (b i))) = 0 := by
  let w := finiteForm X.variety.structureMap H.openSet a b
  have hw : ∀ v : SectionsOn (tangentSheaf X.variety.structureMap) H.openSet,
      (dualEvaluation (cotangentSheaf X.variety.structureMap)).apply H.openSet v w =
        localContactValue X.contact H v := by
    intro v
    rw [finiteForm_pair, hab]
  have hz := relativeCotangent_contact_zero f E H w hw
  letI := LeBrunSalamon.StandardInputs.cotangentPullback_isIso
    P.structureMap Infinitesimal.dualToC
  have hnorm : relativeCotangent X.variety E ≫
      LeBrunSalamon.CotangentBaseChange.canonicalMap P.structureMap Infinitesimal.dualToC =
        targetToRelative X.variety E := by
    simp only [relativeCotangent, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have ht := congrArg (fun z =>
    (LeBrunSalamon.CotangentBaseChange.canonicalMap P.structureMap Infinitesimal.dualToC).app
      (E.map ⁻¹ᵁ H.openSet) z) hz
  rw [map_zero] at ht
  change (relativeCotangent X.variety E ≫
    LeBrunSalamon.CotangentBaseChange.canonicalMap P.structureMap Infinitesimal.dualToC).app
      (E.map ⁻¹ᵁ H.openSet)
      (pullLocalSection E.map (cotangentSheaf X.variety.structureMap) H.openSet w) = 0 at ht
  rw [hnorm] at ht
  change (targetToRelative X.variety E).app (E.map ⁻¹ᵁ H.openSet)
    (pullLocalSection E.map (cotangentSheaf X.variety.structureMap) H.openSet
      (∑ i, a i • (cotangentPresentation X.variety.structureMap).differential.apply
        H.openSet (b i))) = 0 at ht
  simp only [pullLocalSection_sum, map_sum, PullbackPairProof.pullLocalSection_smul,
    Scheme.Modules.Hom.app_smul, targetToRelative_differential] at ht
  exact ht

end InfinitesimalHorizontality

namespace RelativeVariation

open DualThickening FamilyVariation

/-- A first-order map which is constant after an actual morphism k
annihilates all functions pulled from the base of k. -/
theorem onFunction_kills_of_constantComposite {Y T S : Scheme}
    {sY : Y ⟶ ComplexBase} {sT : T ⟶ ComplexBase} {f : Y ⟶ T}
    (D : Deformation sY sT f) (k : T ⟶ S)
    (hk : D.map ≫ k = projection sY ≫ (f ≫ k))
    (U : S.Opens) (a : RingSections S U) :
    D.onFunction (k ⁻¹ᵁ U) (k.app U a) = 0 := by
  have hp : k.app U ≫ functionPullback sY D.map f D.reduces (k ⁻¹ᵁ U) =
      (f ≫ k).app U ≫ (projection sY).app ((f ≫ k) ⁻¹ᵁ U) := by
    have hnorm := functionPullback_of_map_eq sY hk (f ≫ k)
      (by rw [← Category.assoc, D.reduces])
      (by rw [← Category.assoc, zeroSection_projection, Category.id_comp]) U
    exact (functionPullback_postcompose sY D.map f D.reduces k U).symm.trans
      (hnorm.trans (functionPullback_constant sY (f ≫ k) U))
  unfold Deformation.onFunction
  have ha := congrArg (fun q => q a) hp
  change coefficient sY ((f ≫ k) ⁻¹ᵁ U)
    ((k.app U ≫ functionPullback sY D.map f D.reduces (k ⁻¹ᵁ U)) a) = 0
  rw [ha]
  exact coefficient_projection sY ((f ≫ k) ⁻¹ᵁ U) ((f ≫ k).app U a)

/-- The normalized variation, now relative to any actual base over
which the first-order family is constant. -/
def derivation {Y T S : Scheme}
    {sY : Y ⟶ ComplexBase} {sT : T ⟶ ComplexBase} {f : Y ⟶ T}
    (D : Deformation sY sT f) (k : T ⟶ S)
    (hk : D.map ≫ k = projection sY ≫ (f ≫ k)) :
    RelativeSheafDerivation k ((Scheme.Modules.pushforward f).obj (structureModule Y)) where
  apply := D.onFunction
  zero := D.onFunction_zero
  add := D.onFunction_add
  leibniz := D.onFunction_leibniz
  naturality := D.onFunction_restrict
  killsBase := onFunction_kills_of_constantComposite D k hk

def cotangentHom {Y T S : Scheme}
    {sY : Y ⟶ ComplexBase} {sT : T ⟶ ComplexBase} {f : Y ⟶ T}
    (D : Deformation sY sT f) (k : T ⟶ S)
    (hk : D.map ≫ k = projection sY ≫ (f ≫ k)) :
    pullbackModule f (cotangentSheaf k) ⟶ structureModule Y :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm
    (differentialLift (derivation D k hk))

theorem cotangentHom_differential {Y T S : Scheme}
    {sY : Y ⟶ ComplexBase} {sT : T ⟶ ComplexBase} {f : Y ⟶ T}
    (D : Deformation sY sT f) (k : T ⟶ S)
    (hk : D.map ≫ k = projection sY ≫ (f ≫ k))
    (U : T.Opens) (a : RingSections T U) :
    (cotangentHom D k hk).app (f ⁻¹ᵁ U)
      (pullLocalSection f (cotangentSheaf k) U
        ((cotangentPresentation k).differential.apply U a)) = D.onFunction U a := by
  have h := congrArg (fun q : RelativeSheafDerivation k
    ((Scheme.Modules.pushforward f).obj (structureModule Y)) => q.apply U a)
      (differentialLift_spec (derivation D k hk))
  have hn := ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).apply_symm_apply
    (differentialLift (derivation D k hk))
  rw [← hn] at h
  exact h

end RelativeVariation

namespace SourceJetHorizontality

open DualThickening FamilyVariation

variable (τ : HomFirstJet.SourceLift P marking)

/-- The actual first-order source motion inside P1 times Dual, with the
entire family parameter held fixed. -/
def sourceDeformation : Deformation Infinitesimal.dualToC (toC P.structureMap)
    (FixedNodeHom.markingSection P marking Infinitesimal.dualToC) where
  map := HomFirstJet.sourceMap P marking Infinitesimal.dualToC τ
  overC := by
    change HomFirstJet.sourceMap P marking Infinitesimal.dualToC τ ≫
      projection P.structureMap ≫ P.structureMap = toC Infinitesimal.dualToC
    rw [← Category.assoc, projection, HomFirstJet.sourceMap_fst, Category.assoc, τ.overC,
      parameter_overC]
  reduces := HomFirstJet.sourceMap_reduces P marking Infinitesimal.dualToC τ

theorem sourceDeformation_relative :
    (sourceDeformation τ).map ≫ parameter P.structureMap =
      projection Infinitesimal.dualToC ≫
        (FixedNodeHom.markingSection P marking Infinitesimal.dualToC ≫
          parameter P.structureMap) := by
  rw [parameter, FixedNodeHom.markingSection_snd, Category.comp_id]
  exact HomFirstJet.sourceMap_snd P marking Infinitesimal.dualToC τ

theorem sourceDeformation_interchange :
    (sourceDeformation τ).map = MixedFamily.swap ≫ DualThickening.map τ.map τ.overC := by
  apply pullback.hom_ext
  · change (sourceDeformation τ).map ≫ projection P.structureMap =
      (MixedFamily.swap ≫ DualThickening.map τ.map τ.overC) ≫ projection P.structureMap
    rw [Category.assoc, DualThickening.map_projection, ← Category.assoc,
      MixedFamily.swap_projection]
    exact HomFirstJet.sourceMap_fst P marking Infinitesimal.dualToC τ
  · change (sourceDeformation τ).map ≫ parameter P.structureMap =
      (MixedFamily.swap ≫ DualThickening.map τ.map τ.overC) ≫ parameter P.structureMap
    rw [Category.assoc, DualThickening.map_parameter, MixedFamily.swap_parameter]
    exact HomFirstJet.sourceMap_snd P marking Infinitesimal.dualToC τ

variable {n : ℕ} {X : ContactFanoManifold n} (f : FreeLine X)
variable (E : Deformation P.structureMap X.variety.structureMap f.curve.map)

/-- The entire dual-number family of source velocities is horizontal.
This follows by applying the normalized relative cotangent functional to
the actual sheaf differential equation, before taking its epsilon part. -/
theorem contact_sum_zero (H : AffineLineFrame X.contact.sequence.line)
    {m : ℕ} (a b : Fin m → RingSections X.variety.scheme H.openSet)
    (hab : ∀ v : SectionsOn (tangentSheaf X.variety.structureMap) H.openSet,
      localContactValue X.contact H v =
        ∑ i, a i * tangentActs X.variety.structureMap H.openSet v (b i)) :
    (∑ i, (FixedNodeHom.markingSection P marking Infinitesimal.dualToC ≫ E.map).app
        H.openSet (a i) *
      ((sourceDeformation τ).postcompose E.map E.overC).onFunction H.openSet (b i)) = 0 := by
  let j := FixedNodeHom.markingSection P marking Infinitesimal.dualToC
  let U := E.map ⁻¹ᵁ H.openSet
  let φ := RelativeVariation.cotangentHom (sourceDeformation τ)
    (parameter P.structureMap) (sourceDeformation_relative τ)
  have h := congrArg (fun w => φ.app (j ⁻¹ᵁ U)
    (pullLocalSection j (cotangentSheaf (parameter P.structureMap)) U w))
      (InfinitesimalHorizontality.differential_sum_zero f E H a b hab)
  simp only [LocalContactCovector.pullLocalSection_sum, LocalContactCovector.pullLocalSection_zero,
    map_sum, PullbackPairProof.pullLocalSection_smul,
    Scheme.Modules.Hom.app_smul, map_zero] at h
  change (∑ i, j.app U (E.map.app H.openSet (a i)) •
    φ.app (j ⁻¹ᵁ U)
      (pullLocalSection j (cotangentSheaf (parameter P.structureMap)) U
        ((cotangentPresentation (parameter P.structureMap)).differential.apply U
          (E.map.app H.openSet (b i))))) = 0 at h
  simp only [φ, U, j, RelativeVariation.cotangentHom_differential, smul_eq_mul] at h
  simpa only [Deformation.postcompose_onFunction, Scheme.Hom.comp_app,
    CommRingCat.comp_apply, U, j] using! h

end SourceJetHorizontality

namespace MixedHorizontality

open DualThickening FamilyVariation DualMixedBridge
open scoped TensorProduct

/-- The two coefficient projections of the actual double thickening
agree with the previously fixed full tensor model. -/
theorem sourceZero_toMixed (z : DoubleFunctions) :
    MixedJet.sourceZero (toMixed z) =
      dualGlobalEquiv (reductionCoefficient Infinitesimal.dualToC ⊤ z) := by
  rw [toMixed_reconstruct]
  simp

theorem sourceDerivative_toMixed (z : DoubleFunctions) :
    MixedJet.sourceDerivative (toMixed z) =
      dualGlobalEquiv (coefficient Infinitesimal.dualToC ⊤ z) := by
  rw [toMixed_reconstruct]
  simp

/-- Both the reduced and infinitesimal coefficients of a local function
pulled to the entire double thickening have their actual normalization. -/
theorem actual_coefficients {Y : Scheme} {sY : Y ⟶ ComplexBase}
    {g : Infinitesimal.DualScheme ⟶ Y}
    (D : Deformation Infinitesimal.dualToC sY g)
    (U : Y.Opens) (hg : ⊤ ≤ g ⁻¹ᵁ U) (hD : ⊤ ≤ D.map ⁻¹ᵁ U)
    (a : RingSections Y U) :
    MixedJet.sourceZero (toMixed (D.map.appLE U ⊤ hD a)) =
        dualGlobalEquiv (g.appLE U ⊤ hg a) ∧
      MixedJet.sourceDerivative (toMixed (D.map.appLE U ⊤ hD a)) =
        dualGlobalEquiv (Infinitesimal.DualScheme.presheaf.map (homOfLE hg).op
          (D.onFunction U a)) := by
  have hrestrict : functionPullback Infinitesimal.dualToC D.map g D.reduces U ≫
      MixedFamily.DoubleDual.presheaf.map
        (((TopologicalSpace.Opens.map (projection Infinitesimal.dualToC).base).map
          (homOfLE hg)).op) = D.map.appLE U ⊤ hD := by
    unfold functionPullback
    rw [Scheme.Hom.appLE_map]
    rfl
  have hr := congrArg (fun q => q a) hrestrict
  simp only [CommRingCat.comp_apply] at hr
  have hc := coefficient_restrict Infinitesimal.dualToC (homOfLE hg)
    (functionPullback Infinitesimal.dualToC D.map g D.reduces U a)
  have hv := reductionCoefficient_restrict Infinitesimal.dualToC (homOfLE hg)
    (functionPullback Infinitesimal.dualToC D.map g D.reduces U a)
  rw [hr] at hc hv
  rw [reductionCoefficient_functionPullback] at hv
  constructor
  · rw [sourceZero_toMixed]
    simpa only [Scheme.Hom.appLE, CommRingCat.comp_apply] using! congrArg dualGlobalEquiv hv
  · rw [sourceDerivative_toMixed]
    exact congrArg dualGlobalEquiv hc

/-- A horizontal first-order contraction remains horizontal in the
actual double-jet tensor algebra. No equality of chosen coefficient maps
is assumed. -/
theorem tensor_sum_zero {Y : Scheme} {sY : Y ⟶ ComplexBase}
    {g : Infinitesimal.DualScheme ⟶ Y}
    (D : Deformation Infinitesimal.dualToC sY g)
    (U : Y.Opens) (hg : ⊤ ≤ g ⁻¹ᵁ U) (hD : ⊤ ≤ D.map ⁻¹ᵁ U)
    {m : ℕ} (a b : Fin m → RingSections Y U)
    (h : (∑ i, g.app U (a i) * D.onFunction U (b i)) = 0) :
    (∑ i, MixedJet.sourceZero (toMixed (D.map.appLE U ⊤ hD (a i))) *
      MixedJet.sourceDerivative (toMixed (D.map.appLE U ⊤ hD (b i)))) = 0 := by
  have hv (c : RingSections Y U) := (actual_coefficients D U hg hD c).1
  have hd (c : RingSections Y U) := (actual_coefficients D U hg hD c).2
  simp only [hv, hd]
  have hh := congrArg (fun z => dualGlobalEquiv
    (Infinitesimal.DualScheme.presheaf.map (homOfLE hg).op z)) h
  simpa only [map_sum, map_mul, map_zero, Scheme.Hom.appLE, CommRingCat.comp_apply] using hh

/-- Subtracting the two differentiated horizontal contractions cancels
the common mixed coefficient. This is the scalar obstruction to a pair
of nonorthogonal horizontal tangent directions. -/
theorem alternating_sum_zero {A : Type*}
    (F : A → MixedJet.Mixed) {m : ℕ} (a b : Fin m → A)
    (h₁ : (∑ i, MixedJet.sourceZero (F (a i)) *
      MixedJet.sourceDerivative (F (b i))) = 0)
    (h₂ : (∑ i, MixedJet.parameterZero (F (a i)) *
      MixedJet.parameterDerivative (F (b i))) = 0) :
    (∑ i, (MixedJet.sourceCoeff (F (a i)) * MixedJet.parameterCoeff (F (b i)) -
      MixedJet.parameterCoeff (F (a i)) * MixedJet.sourceCoeff (F (b i)))) = 0 := by
  have h₁' := congrArg MixedJet.dualCoefficient h₁
  have h₂' := congrArg MixedJet.dualCoefficient h₂
  simp only [map_sum, map_zero, MixedJet.dualCoefficient_mul] at h₁' h₂'
  have hval (z : MixedJet.Mixed) : Infinitesimal.residue (MixedJet.parameterZero z) =
      MixedJet.value z := by
    induction z using TensorProduct.inductionOn with
    | tmul c d => simp [MixedJet.value, mul_comm]
    | add z w hz hw => simp only [map_add, hz, hw]
  have hpar (z : MixedJet.Mixed) : MixedJet.dualCoefficient (MixedJet.parameterZero z) =
      MixedJet.sourceCoeff z := by
    induction z using TensorProduct.inductionOn with
    | tmul c d => simp [MixedJet.sourceCoeff, mul_comm]
    | add z w hz hw => simp only [map_add, hz, hw]
  simp only [hval, hpar, MixedJet.parameterDerivative_residue,
    ← MixedJet.derivative_exchange] at h₂'
  change (∑ i, (MixedJet.value (F (a i)) * MixedJet.mixedCoeff (F (b i)) +
    MixedJet.sourceCoeff (F (b i)) * MixedJet.parameterCoeff (F (a i)))) = 0 at h₁'
  change (∑ i, (MixedJet.value (F (a i)) * MixedJet.mixedCoeff (F (b i)) +
    MixedJet.parameterCoeff (F (b i)) * MixedJet.sourceCoeff (F (a i)))) = 0 at h₂'
  calc
    _ = (∑ i, (MixedJet.value (F (a i)) * MixedJet.mixedCoeff (F (b i)) +
          MixedJet.parameterCoeff (F (b i)) * MixedJet.sourceCoeff (F (a i)))) -
        (∑ i, (MixedJet.value (F (a i)) * MixedJet.mixedCoeff (F (b i)) +
          MixedJet.sourceCoeff (F (b i)) * MixedJet.parameterCoeff (F (a i)))) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = 0 := by rw [h₁', h₂', sub_self]

end MixedHorizontality

namespace PointLevi

open LeBrunSalamon.Refinement.Jets
open PositiveFrame

variable {n : ℕ} {X : ContactFanoManifold n} {x : ComplexPoint X.variety}
variable (F : PointFrame X.variety X.contact.sequence.line x)

/-- The actual line fiber vanishes exactly when its coefficient in the
specified affine frame vanishes at the actual point. -/
theorem localLineFiber_zero_iff (s : SectionsOn X.contact.sequence.line.sheaf F.frame.openSet) :
    localFiberValue x.map X.contact.sequence.line.sheaf F.frame.openSet F.pointSupport s = 0 ↔
      F.evaluation (F.frame.coefficient s) = 0 := by
  have hc := F.lineFiberCoefficient_local (F.frame.coefficient s)
  rw [F.frame.coefficient.symm_apply_apply] at hc
  have he : (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
      (F.lineFiberCoefficient (localFiberValue x.map X.contact.sequence.line.sheaf
        F.frame.openSet F.pointSupport s)) = F.evaluation (F.frame.coefficient s) := by
    rw [hc]
    exact (F.evaluation_eq_localRingValue (F.frame.coefficient s)).symm
  constructor
  · intro h
    rw [← he, h, map_zero, map_zero]
  · intro h
    apply F.lineFiberCoefficient.injective
    apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).injective
    rw [map_zero, map_zero, he, h]

/-- Every specified distribution fiber vector has an actual affine
horizontal lift. A general tangent lift is corrected by the local contact
value, whose coefficient vanishes at the chosen point. -/
theorem distribution_localLift
    (u : Fiber X.contact.sequence.distribution.sheaf x.map) :
    ∃ v : SectionsOn X.contact.sequence.distribution.sheaf F.frame.openSet,
      localFiberValue x.map X.contact.sequence.distribution.sheaf
        F.frame.openSet F.pointSupport v = u := by
  obtain ⟨w, hw⟩ := F.evaluateVector_surjective
    (F.fiberEquiv (fiberMap X.contact.sequence.inclusion x.map u))
  have hvalue : localFiberValue x.map (tangentSheaf X.variety.structureMap)
      F.frame.openSet F.pointSupport w = fiberMap X.contact.sequence.inclusion x.map u :=
    F.fiberEquiv.injective ((F.fiberEquiv_local w).trans hw)
  have hθ : F.evaluation (localContactValue X.contact F.frame w) = 0 := by
    apply (localLineFiber_zero_iff F (X.contact.sequence.form.app F.frame.openSet w)).mp
    erw [localFiberValue_map, hvalue, ← ContactPositive.fiberMap_comp,
      X.contact.sequence.comp_zero]
    exact PositiveFrame.fiberMap_zero _ _ _ _
  obtain ⟨r, hr⟩ := localContactValue_unit X.contact F.frame
  let w₀ := w - localContactValue X.contact F.frame w • r
  have hw₀ : localContactValue X.contact F.frame w₀ = 0 := by
    rw [localContactValue_sub, localContactValue_smul, hr, mul_one, sub_self]
  have he : F.evaluateVector w₀ =
      F.fiberEquiv (fiberMap X.contact.sequence.inclusion x.map u) := by
    rw [F.evaluateVector_sub, F.evaluateVector_smul, hθ, zero_smul, sub_zero, hw]
  have hform : X.contact.sequence.form.app F.frame.openSet w₀ = 0 := by
    apply F.frame.coefficient.injective
    exact hw₀.trans (map_zero F.frame.coefficient).symm
  obtain ⟨v, hv⟩ := ContactClosureProof.exists_kernelSection X.contact.sequence.inclusion
    X.contact.sequence.form X.contact.sequence.comp_zero X.contact.sequence.shortExact
    F.frame.openSet w₀ hform
  refine ⟨v, ?_⟩
  apply SuitablePairAlgebra.inclusionFiber_injective X x
  rw [← localFiberValue_map, hv]
  apply F.fiberEquiv.injective
  erw [F.fiberEquiv_local, he]

/-- The bracket-defined original Levi pairing is detected by the scalar
exterior form after the actual fiber/point-derivation comparison. -/
theorem exterior_ne_zero (A : ContactAtPoint X.contact F)
    (a b : TangentFiber X.variety x) (hab : NonzeroLeviPair X x a b) :
    A.exterior (F.fiberEquiv a) (F.fiberEquiv b) ≠ 0 := by
  obtain ⟨u, v, hu, hv, hn⟩ := hab
  obtain ⟨u₀, hu₀⟩ := distribution_localLift F u
  obtain ⟨v₀, hv₀⟩ := distribution_localLift F v
  let U := X.contact.sequence.inclusion.app F.frame.openSet u₀
  let V := X.contact.sequence.inclusion.app F.frame.openSet v₀
  have hU : localContactValue X.contact F.frame U = 0 := by
    change F.frame.coefficient ((X.contact.sequence.inclusion ≫ X.contact.sequence.form).app
      F.frame.openSet u₀) = 0
    rw [X.contact.sequence.comp_zero]
    simp
  have hV : localContactValue X.contact F.frame V = 0 := by
    change F.frame.coefficient ((X.contact.sequence.inclusion ≫ X.contact.sequence.form).app
      F.frame.openSet v₀) = 0
    rw [X.contact.sequence.comp_zero]
    simp
  have heU : F.evaluateVector U = F.fiberEquiv a := by
    erw [← F.fiberEquiv_local, localFiberValue_map, hu₀, hu]
  have heV : F.evaluateVector V = F.fiberEquiv b := by
    erw [← F.fiberEquiv_local, localFiberValue_map, hv₀, hv]
  intro hzero
  have hscalar := (A.exterior_normalized U V).symm.trans
    ((congrArg₂ (fun u v => A.exterior u v) heU heV).trans hzero)
  simp only [scalarExterior, hU, hV, TangentActionProof.zero_function,
    sub_self, zero_sub, map_neg, neg_eq_zero] at hscalar
  have hfiber : localFiberValue x.map X.contact.sequence.line.sheaf
      F.frame.openSet F.pointSupport
      ((intrinsicLeviPair X.contact.sequence).apply F.frame.openSet u₀ v₀) = 0 := by
    apply (localLineFiber_zero_iff F _).mpr
    exact hscalar
  apply hn
  rw [← hu₀, ← hv₀]
  exact (localFiberValue_pair x.map (intrinsicLeviPair X.contact.sequence)
    F.frame.openSet F.pointSupport u₀ v₀).trans hfiber

/-- The local scalar exterior derivative of a finite covector expression
has the usual antisymmetric coefficient formula. The two second
iterations cancel by the actual intrinsic bracket action. -/
theorem scalarExterior_finite {m : ℕ}
    (a b : Fin m → F.ChartRing)
    (hab : ∀ v : SectionsOn (tangentSheaf X.variety.structureMap) F.frame.openSet,
      localContactValue X.contact F.frame v =
        ∑ i, (show RingSections X.variety.scheme F.frame.openSet from a i) * tangentActs X.variety.structureMap F.frame.openSet v (b i))
    (u v : SectionsOn (tangentSheaf X.variety.structureMap) F.frame.openSet) :
    scalarExterior X.contact F u v =
      ∑ i, (tangentActs X.variety.structureMap F.frame.openSet u (a i) *
          tangentActs X.variety.structureMap F.frame.openSet v (b i) -
        tangentActs X.variety.structureMap F.frame.openSet v (a i) *
          tangentActs X.variety.structureMap F.frame.openSet u (b i)) := by
  have hsum (w : SectionsOn (tangentSheaf X.variety.structureMap) F.frame.openSet)
      (c : Fin m → F.ChartRing) :
      tangentActs X.variety.structureMap F.frame.openSet w (∑ i, c i) =
        ∑ i, tangentActs X.variety.structureMap F.frame.openSet w (c i) :=
    map_sum (TangentActionProof.functionAddHom X.variety.structureMap F.frame.openSet w) c _
  rw [scalarExterior, hab v, hab u, hab (tangentBracket X.variety.structureMap F.frame.openSet u v),
    hsum, hsum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [TangentActionProof.leibniz, TangentActionProof.leibniz, tangentBracket_spec]
  ring

/-- The same antisymmetric formula on the original point-derivation
space. This fixes the comparison with the actual Levi fiber. -/
theorem exterior_finite (A : ContactAtPoint X.contact F) {m : ℕ}
    (a b : Fin m → F.ChartRing)
    (hab : ∀ v : SectionsOn (tangentSheaf X.variety.structureMap) F.frame.openSet,
      localContactValue X.contact F.frame v =
        ∑ i, (show RingSections X.variety.scheme F.frame.openSet from a i) * tangentActs X.variety.structureMap F.frame.openSet v (b i))
    (u v : F.Tangent) :
    A.exterior u v = ∑ i, (u.val (a i) * v.val (b i) - v.val (a i) * u.val (b i)) := by
  obtain ⟨u₀, rfl⟩ := F.evaluateVector_surjective u
  obtain ⟨v₀, rfl⟩ := F.evaluateVector_surjective v
  rw [A.exterior_normalized, scalarExterior_finite F a b hab]
  simp only [map_sum, map_sub, map_mul]
  rfl

/-- Finite projective duality supplies an actual finite differential
expression for the chosen affine contact form. -/
theorem finite_expression :
    ∃ (m : ℕ) (a b : Fin m → F.ChartRing),
      ∀ v : SectionsOn (tangentSheaf X.variety.structureMap) F.frame.openSet,
        localContactValue X.contact F.frame v =
          ∑ i, (show RingSections X.variety.scheme F.frame.openSet from a i) * tangentActs X.variety.structureMap F.frame.openSet v (b i) := by
  letI : Algebra.Smooth ℂ F.ChartRing := PointFrame.EvaluateVectorProof.chartRing_smooth F
  obtain ⟨m, a, b, hab⟩ := LeBrunSalamon.Refinement.FiniteCovectorExpression.exists_fin_of_smooth
    (ContactAtPointProof.affineContactCovector X.contact F)
  refine ⟨m, a, b, ?_⟩
  intro v
  simpa only [ContactAtPointProof.affineContactCovector_intrinsic,
    F.affineVectorEquiv_apply] using hab (F.affineVectorEquiv v)

end PointLevi

namespace NodeDirections

open CoordinateCharts SourceAffineCharts
open LeBrunSalamon.Refinement.Jets

/-- The node coordinate fixes a genuine nonzero source tangent, with the
same epsilon normalization used by both actual branch charts. -/
def sourceLift : HomFirstJet.SourceLift P marking :=
  push (ratioPoint 0).val (ratioPoint 0).property ratioPoint_zero_marking
    (lift BaseDifferentialProof.baseChart BaseDifferentialProof.unitDirection)

def markedPoint : ComplexPoint (projectiveLineVariety P) :=
  ⟨marking.map, marking.overC⟩

def sourceVector : TangentFiber (projectiveLineVariety P) markedPoint :=
  SourceTangent.pointVector (projectiveLineVariety P) markedPoint sourceLift

theorem sourceVector_ne_zero : sourceVector ≠ 0 := by
  letI := ratioPoint_openImmersion 0
  let e := AffineIntrinsic.tangentEquiv BaseDifferentialProof.baseChart
    (projectiveLineVariety P) markedPoint (ratioPoint 0).val
    (ratioPoint 0).property ratioPoint_zero_marking
  have he : e BaseDifferentialProof.unitDirection = sourceVector :=
    AffineIntrinsic.tangentEquiv_pointVector BaseDifferentialProof.baseChart
      (projectiveLineVariety P) markedPoint (ratioPoint 0).val
      (ratioPoint 0).property ratioPoint_zero_marking BaseDifferentialProof.unitDirection
  intro hzero
  have hv : BaseDifferentialProof.unitDirection = 0 :=
    e.injective ((he.trans hzero).trans e.map_zero.symm)
  have h := BaseDifferentialProof.unitDirection_parameter
  rw [hv] at h
  exact zero_ne_one h

variable {n : ℕ} {X : ContactFanoManifold n}

def branchLift (f : FreeLine X) (x : ComplexPoint X.variety)
    (hx : marking.map ≫ f.curve.map = x.map) :
    Infinitesimal.PointLift X.variety.scheme X.variety.structureMap ⟨x.map, x.overC⟩ :=
  push f.curve.map f.curve.overC hx sourceLift

theorem branchVector_eq_pointVector (f : FreeLine X) (x : ComplexPoint X.variety)
    (hx : marking.map ≫ f.curve.map = x.map) :
    nodeDifferential f x hx sourceVector =
      SourceTangent.pointVector X.variety x (branchLift f x hx) := by
  symm
  exact SourceTangent.pointVector_push (projectiveLineVariety P) X.variety
    f.curve.map f.curve.overC markedPoint x hx sourceLift

/-- Any original nonzero source parameters are nonzero multiples of the
coordinate tangent. Thus the supplied actual Levi transversality holds
for the normalized vectors used by the epsilon source charts. -/
theorem transverse (D : SuitablePair X) :
    NonzeroLeviPair X D.node
      (nodeDifferential D.first D.node D.firstAtNode sourceVector)
      (nodeDifferential D.second D.node D.secondAtNode sourceVector) := by
  have hr : Module.finrank ℂ (Fiber (tangentSheaf P.structureMap) marking.map) = 1 :=
    fiber_dimension (intrinsicTangentBundle (projectiveLineVariety P)) marking.map
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hr sourceVector_ne_zero D.firstParameter
  obtain ⟨d, hd⟩ := exists_smul_eq_of_finrank_eq_one hr sourceVector_ne_zero D.secondParameter
  have hc0 : c ≠ 0 := by
    intro h
    apply D.firstParameter_ne
    rw [← hc, h, zero_smul]
  have hd0 : d ≠ 0 := by
    intro h
    apply D.secondParameter_ne
    rw [← hd, h, zero_smul]
  apply (nonzeroLeviPair_rescale X D.node _ _ c d hc0 hd0).mp
  simpa only [← hc, ← hd, map_smul] using D.transverse

/-- Coefficients of the actual point lift are exactly the action of its
original tangent-fiber vector in the specified target affine frame. -/
theorem pointLift_coefficient {x : ComplexPoint X.variety}
    (F : PointFrame X.variety X.contact.sequence.line x)
    (τ : Infinitesimal.PointLift X.variety.scheme X.variety.structureMap ⟨x.map, x.overC⟩)
    (hτ : ⊤ ≤ τ.map ⁻¹ᵁ F.frame.openSet) (a : F.ChartRing) :
    MixedJet.dualCoefficient (DualMixedBridge.dualGlobalEquiv
      (τ.map.appLE F.frame.openSet ⊤ hτ a)) =
        (F.fiberEquiv (SourceTangent.pointVector X.variety x τ)).val a := by
  exact (SourceTangent.pointVector_local_pairing X.variety x τ
    F.frame.openSet F.pointSupport hτ a).symm

end NodeDirections

namespace NodeTensor

open DualThickening FamilyVariation DualMixedBridge
open CoordinateCharts SourceAffineCharts
open LeBrunSalamon.Refinement.Jets
open scoped TensorProduct

theorem thickening_map_comp {Y Z W : Scheme}
    {sY : Y ⟶ ComplexBase} {sZ : Z ⟶ ComplexBase} {sW : W ⟶ ComplexBase}
    (f : Y ⟶ Z) (hf : f ≫ sZ = sY) (g : Z ⟶ W) (hg : g ≫ sW = sZ) :
    DualThickening.map (f ≫ g) (by rw [Category.assoc, hg, hf]) =
      DualThickening.map f hf ≫ DualThickening.map g hg := by
  apply pullback.hom_ext
  · change _ ≫ projection sW = _ ≫ projection sW
    simp only [Category.assoc, map_projection]
    simpa only [Category.assoc] using
      (congrArg (fun k => k ≫ g) (DualThickening.map_projection f hf)).symm
  · change _ ≫ parameter sW = _ ≫ parameter sW
    simp only [Category.assoc, map_parameter]

theorem center_support {Y : Scheme} {sY : Y ⟶ ComplexBase}
    {g : Infinitesimal.DualScheme ⟶ Y}
    (E : Deformation Infinitesimal.dualToC sY g)
    (U : Y.Opens) (hE : ⊤ ≤ E.map ⁻¹ᵁ U) : ⊤ ≤ g ⁻¹ᵁ U := by
  intro p hp
  have h := hE (show zeroSection Infinitesimal.dualToC p ∈
    (⊤ : MixedFamily.DoubleDual.Opens) by trivial)
  change (zeroSection Infinitesimal.dualToC ≫ E.map) p ∈ U at h
  rwa [E.reduces] at h

theorem sourceZero_comm (w : MixedJet.Mixed) :
    MixedJet.sourceZero (Algebra.TensorProduct.comm ℂ MixedJet.Dual MixedJet.Dual w) =
      MixedJet.parameterZero w := by
  induction w using TensorProduct.inductionOn with
  | tmul a b => simp
  | add u v hu hv => simp only [map_add, hu, hv]

theorem parameterCoeff_comm (w : MixedJet.Mixed) :
    MixedJet.parameterCoeff (Algebra.TensorProduct.comm ℂ MixedJet.Dual MixedJet.Dual w) =
      MixedJet.sourceCoeff w := by
  induction w using TensorProduct.inductionOn with
  | tmul a b => simp [MixedJet.parameterCoeff, MixedJet.sourceCoeff, mul_comm]
  | add u v hu hv => simp only [map_add, hu, hv]

/-- The complete double-jet coordinate of every local function commutes
with the actual scheme interchange; no coefficient-only identification
is assumed. -/
theorem functions_interchange {Y : Scheme}
    (M₁ M₂ : MixedFamily.DoubleDual ⟶ Y) (hM : M₁ = MixedFamily.swap ≫ M₂)
    (U : Y.Opens) (h₁ : ⊤ ≤ M₁ ⁻¹ᵁ U) (h₂ : ⊤ ≤ M₂ ⁻¹ᵁ U)
    (a : RingSections Y U) :
    toMixed (M₁.appLE U ⊤ h₁ a) =
      Algebra.TensorProduct.comm ℂ MixedJet.Dual MixedJet.Dual
        (toMixed (M₂.appLE U ⊤ h₂ a)) := by
  have hp := congrArg (fun k => k a) (swap_appLE M₂ U h₂)
  rw [← appLE_of_map_eq hM U ⊤ h₁ _] at hp
  change swapFunctions (M₂.appLE U ⊤ h₂ a) = M₁.appLE U ⊤ h₁ a at hp
  rw [← hp, toMixed_swap]

variable {n : ℕ} {X : ContactFanoManifold n}

theorem branch_support (f : FreeLine X) (x : ComplexPoint X.variety)
    (hx : marking.map ≫ f.curve.map = x.map)
    (F : PointFrame X.variety X.contact.sequence.line x) :
    ⊤ ≤ (epsilonParameter ≫ (ratioPoint 0).val ≫ f.curve.map) ⁻¹ᵁ F.frame.openSet := by
  have h := LocalVelocityComparison.pointLift_top_le_preimage
    (NodeDirections.branchLift f x hx) F.frame.openSet
    (by rintro _ ⟨p, rfl⟩; exact F.pointSupport trivial)
  simpa only [NodeDirections.branchLift, NodeDirections.sourceLift, push, epsilonParameter,
    Category.assoc] using h

/-- The coefficient along the unreplaced branch source is the original
df-vector. The actual reduction of the node deformation supplies this
normalization before the two tensor factors are exchanged. -/
theorem branch_parameterCoeff (f : FreeLine X) (x : ComplexPoint X.variety)
    (hx : marking.map ≫ f.curve.map = x.map)
    (F : PointFrame X.variety X.contact.sequence.line x)
    (E : Deformation affineLineToC X.variety.structureMap
      ((ratioPoint 0).val ≫ f.curve.map))
    (hE : ⊤ ≤ (E.pullback epsilonParameter epsilonParameter_over).map ⁻¹ᵁ F.frame.openSet)
    (a : F.ChartRing) :
    MixedJet.parameterCoeff (toMixed
      ((E.pullback epsilonParameter epsilonParameter_over).map.appLE
        F.frame.openSet ⊤ hE a)) =
      (F.fiberEquiv (nodeDifferential f x hx NodeDirections.sourceVector)).val a := by
  change MixedJet.dualCoefficient (MixedJet.sourceZero (toMixed
    ((E.pullback epsilonParameter epsilonParameter_over).map.appLE
      F.frame.openSet ⊤ hE a))) = _
  rw [(MixedHorizontality.actual_coefficients
    (E.pullback epsilonParameter epsilonParameter_over) F.frame.openSet
    (branch_support f x hx F) hE a).1]
  rw [NodeDirections.branchVector_eq_pointVector]
  have hτ : ⊤ ≤ (NodeDirections.branchLift f x hx).map ⁻¹ᵁ F.frame.openSet := by
    simpa only [NodeDirections.branchLift, NodeDirections.sourceLift, push,
      epsilonParameter, Category.assoc] using branch_support f x hx F
  have hm : (NodeDirections.branchLift f x hx).map =
      epsilonParameter ≫ (ratioPoint 0).val ≫ f.curve.map := by
    simp only [NodeDirections.branchLift, NodeDirections.sourceLift, push,
      epsilonParameter, Category.assoc]
  rw [← appLE_of_map_eq hm F.frame.openSet ⊤ hτ (branch_support f x hx F)]
  exact NodeDirections.pointLift_coefficient F (NodeDirections.branchLift f x hx) hτ a

/-- Pulling an actual global auxiliary deformation along the normalized
source lift agrees with first restricting to the node chart and then
pulling along its coordinate epsilon. -/
theorem global_restriction (f : FreeLine X)
    (E : Deformation P.structureMap X.variety.structureMap f.curve.map)
    (E₀ : Deformation affineLineToC X.variety.structureMap
      ((ratioPoint 0).val ≫ f.curve.map))
    (hE : E.pullback (ratioPoint 0).val (ratioPoint 0).property = E₀) :
    (E.pullback NodeDirections.sourceLift.map NodeDirections.sourceLift.overC).map =
      (E₀.pullback epsilonParameter epsilonParameter_over).map := by
  have hm := congrArg Deformation.map hE
  change DualThickening.map (ratioPoint 0).val (ratioPoint 0).property ≫ E.map = E₀.map at hm
  change DualThickening.map (epsilonParameter ≫ (ratioPoint 0).val) _ ≫ E.map =
    DualThickening.map epsilonParameter epsilonParameter_over ≫ E₀.map
  rw [thickening_map_comp epsilonParameter epsilonParameter_over
    (ratioPoint 0).val (ratioPoint 0).property, Category.assoc, hm]

def sourceJet (f : FreeLine X)
    (E : Deformation P.structureMap X.variety.structureMap f.curve.map) :=
  (SourceJetHorizontality.sourceDeformation NodeDirections.sourceLift).postcompose
    E.map E.overC

theorem sourceJet_map (f : FreeLine X)
    (E : Deformation P.structureMap X.variety.structureMap f.curve.map) :
    (sourceJet f E).map = MixedFamily.swap ≫
      (E.pullback NodeDirections.sourceLift.map NodeDirections.sourceLift.overC).map := by
  change (SourceJetHorizontality.sourceDeformation NodeDirections.sourceLift).map ≫ E.map = _
  rw [SourceJetHorizontality.sourceDeformation_interchange, Category.assoc]
  rfl

/-- Horizontal contraction on the global auxiliary line supplies a
normalized tensor equation for any equal actual double-jet map. -/
theorem horizontal_on_map (f : FreeLine X)
    (E : Deformation P.structureMap X.variety.structureMap f.curve.map)
    (H : AffineLineFrame X.contact.sequence.line)
    {m : ℕ} (a b : Fin m → RingSections X.variety.scheme H.openSet)
    (hab : ∀ v : SectionsOn (tangentSheaf X.variety.structureMap) H.openSet,
      localContactValue X.contact H v =
        ∑ i, a i * tangentActs X.variety.structureMap H.openSet v (b i))
    (M : MixedFamily.DoubleDual ⟶ X.variety.scheme)
    (hM : (sourceJet f E).map = M) (hU : ⊤ ≤ M ⁻¹ᵁ H.openSet) :
    (∑ i, MixedJet.sourceZero (toMixed (M.appLE H.openSet ⊤ hU (a i))) *
      MixedJet.sourceDerivative (toMixed (M.appLE H.openSet ⊤ hU (b i)))) = 0 := by
  have hE : ⊤ ≤ (sourceJet f E).map ⁻¹ᵁ H.openSet := by rw [hM]; exact hU
  have h := MixedHorizontality.tensor_sum_zero (sourceJet f E) H.openSet
    (center_support (sourceJet f E) H.openSet hE) hE a b
    (SourceJetHorizontality.contact_sum_zero NodeDirections.sourceLift f E H a b hab)
  rw [appLE_of_map_eq hM H.openSet ⊤ hE hU] at h
  exact h

end NodeTensor

/-- The actual two branch maps make the mixed coefficients equal. Global
horizontal extensions then force the scalar exterior pairing of their
original nonzero df-vectors to vanish, contrary to the supplied Levi test. -/
theorem contradiction {n : ℕ} {X : ContactFanoManifold n} {D : SuitablePair X}
    (G : Germ D) (z : G.chart.Tangent) (hz : G.baseDifferential z = 1)
    (he : G.endpointDifferential z = 0) : False := by
  classical
  obtain ⟨E₁, hE₁⟩ := GlobalAuxiliary.first_exists G z hz he
  obtain ⟨E₂, hE₂⟩ := GlobalAuxiliary.second_exists G z hz he
  obtain ⟨F⟩ := LeBrunSalamon.Refinement.Jets.pointFrame_exists
    X.variety X.contact.sequence.line D.node
  obtain ⟨A⟩ := LeBrunSalamon.Refinement.Jets.contactAtPoint_exists X.contact F
  obtain ⟨m, a, b, hab⟩ := PointLevi.finite_expression F
  let N₁ := BranchCharts.firstNodeDeformation G z hz
  let N₂ := BranchCharts.secondNodeDeformation G z hz
  let M₁ := (N₁.pullback epsilonParameter epsilonParameter_over).map
  let M₂ := (N₂.pullback epsilonParameter epsilonParameter_over).map
  have hM : M₁ = MixedFamily.swap ≫ M₂ := BranchCharts.nodeDeformations_interchange G z hz
  have h₁ : ⊤ ≤ M₁ ⁻¹ᵁ F.frame.openSet :=
    DualMixedBridge.actualPullback_support N₁ epsilonParameter epsilonParameter_over
      F.frame.openSet (NodeTensor.branch_support D.first D.node D.firstAtNode F)
  have h₂ : ⊤ ≤ M₂ ⁻¹ᵁ F.frame.openSet :=
    DualMixedBridge.actualPullback_support N₂ epsilonParameter epsilonParameter_over
      F.frame.openSet (NodeTensor.branch_support D.second D.node D.secondAtNode F)
  have hJ₁ : (NodeTensor.sourceJet D.first E₁).map = M₂ := by
    rw [NodeTensor.sourceJet_map, NodeTensor.global_restriction D.first E₁ N₁ hE₁]
    change MixedFamily.swap ≫ M₁ = M₂
    rw [hM, ← Category.assoc, MixedFamily.swap_involutive, Category.id_comp]
  have hJ₂ : (NodeTensor.sourceJet D.second E₂).map = M₁ := by
    rw [NodeTensor.sourceJet_map, NodeTensor.global_restriction D.second E₂ N₂ hE₂]
    exact hM.symm
  let W : F.ChartRing → MixedJet.Mixed := fun c =>
    DualMixedBridge.toMixed (M₂.appLE F.frame.openSet ⊤ h₂ c)
  have hs : (∑ i, MixedJet.sourceZero (W (a i)) *
      MixedJet.sourceDerivative (W (b i))) = 0 :=
    NodeTensor.horizontal_on_map D.first E₁ F.frame a b hab M₂ hJ₁ h₂
  have hp : (∑ i, MixedJet.parameterZero (W (a i)) *
      MixedJet.parameterDerivative (W (b i))) = 0 := by
    have h := NodeTensor.horizontal_on_map D.second E₂ F.frame a b hab M₁ hJ₂ h₁
    simp only [NodeTensor.functions_interchange M₁ M₂ hM F.frame.openSet h₁ h₂,
      NodeTensor.sourceZero_comm, DualMixedBridge.sourceDerivative_comm] at h
    exact h
  have hfirst (c : F.ChartRing) : MixedJet.sourceCoeff (W c) =
      (F.fiberEquiv (nodeDifferential D.first D.node D.firstAtNode
        NodeDirections.sourceVector)).val c := by
    calc
      MixedJet.sourceCoeff (W c) = MixedJet.parameterCoeff
          (Algebra.TensorProduct.comm ℂ MixedJet.Dual MixedJet.Dual (W c)) :=
        (NodeTensor.parameterCoeff_comm (W c)).symm
      _ = MixedJet.parameterCoeff (DualMixedBridge.toMixed
          (M₁.appLE F.frame.openSet ⊤ h₁ c)) :=
        congrArg MixedJet.parameterCoeff
          (NodeTensor.functions_interchange M₁ M₂ hM F.frame.openSet h₁ h₂ c).symm
      _ = _ := NodeTensor.branch_parameterCoeff D.first D.node D.firstAtNode F N₁ h₁ c
  have hsecond (c : F.ChartRing) : MixedJet.parameterCoeff (W c) =
      (F.fiberEquiv (nodeDifferential D.second D.node D.secondAtNode
        NodeDirections.sourceVector)).val c :=
    NodeTensor.branch_parameterCoeff D.second D.node D.secondAtNode F N₂ h₂ c
  have hzero := MixedHorizontality.alternating_sum_zero W a b hs hp
  simp only [hfirst, hsecond] at hzero
  apply PointLevi.exterior_ne_zero F A _ _ (NodeDirections.transverse D)
  rw [PointLevi.exterior_finite F A a b hab]
  exact hzero

end LeBrunSalamon.Construction.Smoothing.FixedEndsProof

namespace LeBrunSalamon.Construction.Smoothing

/-- Source sm:fixed-ends. The common constant is essential; two unrelated
regular constants would not force the nonzero Levi pairing to vanish. -/
theorem germ_noFixedEnds {n : ℕ} {X : ContactFanoManifold n}
    {D : SuitablePair X} (G : Germ D) : G.NoFixedEnds := by
  rintro ⟨z, hz, he⟩
  exact FixedEndsProof.contradiction G z hz he

end LeBrunSalamon.Construction.Smoothing

end

#print axioms LeBrunSalamon.Construction.Smoothing.germ_noFixedEnds

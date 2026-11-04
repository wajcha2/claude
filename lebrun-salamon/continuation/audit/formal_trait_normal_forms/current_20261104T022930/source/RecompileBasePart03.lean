import RecompileBasePart02

noncomputable section

set_option autoImplicit false
open Bundle
open scoped Bundle ContDiff ENNReal
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance 100] LieRing.ofAssociativeRing
open CategoryTheory
open AlgebraicGeometry
open CategoryTheory.Limits


/-!
# Phase 20 -- contact-line splitting and the smoothing evaluation cokernel

This phase separates the NUMERICAL profile of a standard free contact line from the GEOMETRIC assertions
needed to find a suitable pair and smooth it. The local missing evaluation direction is a one-dimensional
quotient; the smoothing parameter must map nontrivially to that quotient.
-/

namespace LeBrunSalamon.Stage3Lines

theorem card_fin_filter_lt (N k : ℕ) (hk : k < N) :
    (Finset.univ.filter (fun i : Fin N => i.val < k)).card = k := by
  have hset : Finset.univ.filter (fun i : Fin N => i.val < k) =
      Finset.Iio (⟨k, hk⟩ : Fin N) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio, Fin.lt_def]
  rw [hset, Fin.card_Iio]

theorem sum_fin_ite_lt {M : Type*} [AddCommMonoid M] (N k : ℕ) (hk : k < N)
    (a b : M) :
    (∑ i : Fin N, if i.val < k then a else b) = k • a + (N-k) • b := by
  rw [Finset.sum_ite]
  have hcard := Finset.card_filter_add_card_filter_not
    (s := Finset.univ) (p := fun i : Fin N => i.val < k)
  simp only [card_fin_filter_lt N k hk, Finset.card_univ, Fintype.card_fin] at hcard
  have hnot : (Finset.univ.filter (fun i : Fin N => ¬ i.val < k)).card = N-k := by
    omega
  simp only [Finset.sum_const, card_fin_filter_lt N k hk, hnot]

theorem sum_standardLineProfile {M : Type*} [AddCommMonoid M]
    (n : ℕ) (hn : 1 ≤ n) (a b c : M) :
    (∑ i : Fin (2*n+1), if i.val = 0 then a else if i.val < n then b else c) =
      a + (n-1) • b + (n+1) • c := by
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, ite_true, Fin.val_succ, Nat.add_eq_zero_iff,
    one_ne_zero, and_false, ite_false]
  have hcut : ∀ i : Fin (2*n), i.val + 1 < n ↔ i.val < n-1 := by
    intro i
    omega
  simp_rw [hcut]
  rw [sum_fin_ite_lt (2*n) (n-1) (by omega)]
  have hsub : 2*n-(n-1) = n+1 := by omega
  rw [hsub, add_assoc]

end LeBrunSalamon.Stage3Lines

namespace LeBrunSalamon.PhaseTwenty

open LeBrunSalamon.PhaseEighteen
open LeBrunSalamon.PhaseNineteen

/-- Standard free contact-line splitting in the primitive Picard case: `O(2) ⊕ O(1)^(n-1) ⊕ O^(n+1)` for
`n ≥ 1`. It is a numerical profile and NOT an identification of bundles. -/
def standardContactLineProfile (n : ℕ) :
    TangentSplittingProfile (2 * n + 1) :=
  ⟨fun i => if i.val = 0 then 2 else if i.val < n then 1 else 0⟩

/-- A standard free contact line is free numerically. -/
theorem standardContactLineProfile_free (n : ℕ) :
    (standardContactLineProfile n).IsFree := by
  intro i
  change (0 : ℤ) ≤
    (if i.val = 0 then 2 else if i.val < n then 1 else 0)
  split_ifs <;> omega

/-- Its total tangent degree is `n+1`, consistent with
`-K_X = L^(n+1)` and a line of contact degree one. -/
theorem standardContactLineProfile_degree (n : ℕ) (hn : 1 ≤ n) :
    (∑ i : Fin (2*n+1), (standardContactLineProfile n).degree i) = (n : ℤ)+1 := by
  change (∑ i : Fin (2*n+1), if i.val = 0 then (2 : ℤ) else
    if i.val < n then 1 else 0) = (n : ℤ)+1
  rw [LeBrunSalamon.Stage3Lines.sum_standardLineProfile n hn]
  simp only [nsmul_eq_mul, mul_one, mul_zero, add_zero]
  omega

/-- The positive subbundle has rank n and the trivial quotient has rank n+1. -/
theorem standardContactLineProfile_positive_rank (n : ℕ) (hn : 1 ≤ n) :
    (Finset.univ.filter (fun i : Fin (2*n+1) =>
      0 < (standardContactLineProfile n).degree i)).card = n := by
  have hset : Finset.univ.filter (fun i : Fin (2*n+1) =>
      0 < (standardContactLineProfile n).degree i) =
      Finset.univ.filter (fun i : Fin (2*n+1) => i.val < n) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    dsimp [standardContactLineProfile]
    split_ifs <;> omega
  rw [hset, LeBrunSalamon.Stage3Lines.card_fin_filter_lt (2*n+1) n (by omega)]

/-- The expected cohomology dimensions for the contact line. -/
theorem standardContactLineProfile_cohomology (n : ℕ) (hn : 1 ≤ n) :
    (standardContactLineProfile n).predictedHZero = 3*n+2 ∧
    (standardContactLineProfile n).predictedHOne = 0 ∧
    (standardContactLineProfile n).predictedTwoMarkedHZero = 1 ∧
    (standardContactLineProfile n).predictedTwoMarkedHOne = n+1 := by
  have h0 : ∀ i : Fin (2*n+1),
      ((standardContactLineProfile n).degree i+1).toNat =
        if i.val = 0 then 3 else if i.val < n then 2 else 1 := by
    intro i
    dsimp [standardContactLineProfile]
    split_ifs <;> norm_num
  have h1 : ∀ i : Fin (2*n+1),
      (-(standardContactLineProfile n).degree i-1).toNat = 0 := by
    intro i
    dsimp [standardContactLineProfile]
    split_ifs <;> norm_num
  have h20 : ∀ i : Fin (2*n+1),
      ((standardContactLineProfile n).degree i-1).toNat =
        if i.val = 0 then 1 else if i.val < n then 0 else 0 := by
    intro i
    dsimp [standardContactLineProfile]
    split_ifs <;> norm_num
  have h21 : ∀ i : Fin (2*n+1),
      (1-(standardContactLineProfile n).degree i).toNat =
        if i.val = 0 then 0 else if i.val < n then 0 else 1 := by
    intro i
    dsimp [standardContactLineProfile]
    split_ifs <;> norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [TangentSplittingProfile.predictedHZero, h0,
      LeBrunSalamon.Stage3Lines.sum_standardLineProfile n hn, nsmul_eq_mul, Nat.cast_id, mul_one]
    omega
  · simp only [TangentSplittingProfile.predictedHOne, h1, Finset.sum_const_zero]
  · simp only [TangentSplittingProfile.predictedTwoMarkedHZero, h20,
      LeBrunSalamon.Stage3Lines.sum_standardLineProfile n hn, smul_zero, add_zero]
  · simp only [TangentSplittingProfile.predictedTwoMarkedHOne, h21,
      LeBrunSalamon.Stage3Lines.sum_standardLineProfile n hn, smul_zero, zero_add, nsmul_eq_mul, Nat.cast_id, mul_one]

section PairAndSmoothing

variable (V : Type*) [AddCommGroup V] [Module ℂ V]

/-- A pair of Lagrangian positive tangent subspaces with complementary sum, and two selected tangent
directions of nonzero mixed Levi pairing. This is a LOCAL algebraic object; a suitable pair of contact
lines must be constructed geometrically using Kebekus and Legendrian tangent cones. -/
structure SuitablePositiveTangentPair (n : ℕ) where
  levi : V →ₗ[ℂ] (V →ₗ[ℂ] ℂ)
  skew : ∀ u v : V, levi u v = -levi v u
  nondegenerate : ∀ u : V,
    (∀ v : V, levi u v = 0) → u = 0
  first : Submodule ℂ V
  second : Submodule ℂ V
  firstRank : Module.finrank ℂ first = n
  secondRank : Module.finrank ℂ second = n
  firstIsotropic : ∀ u v : V,
    u ∈ first → v ∈ first → levi u v = 0
  secondIsotropic : ∀ u v : V,
    u ∈ second → v ∈ second → levi u v = 0
  complementary : first ⊔ second = ⊤
  firstVelocity : V
  secondVelocity : V
  firstVelocity_mem : firstVelocity ∈ first
  secondVelocity_mem : secondVelocity ∈ second
  mixedNonzero : levi firstVelocity secondVelocity ≠ 0

/-- Both subspaces have trivial intersection when they are isotropic,
complementary, and each has half the total dimension. -/
theorem suitablePair_intersection_trivial (V : Type*)
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (n : ℕ) (P : SuitablePositiveTangentPair V n)
    (hDim : Module.finrank ℂ V = 2*n) : P.first ⊓ P.second = ⊥ := by
  apply eq_bot_iff.mpr
  intro u hu
  change u = 0
  apply P.nondegenerate u
  intro v
  have hv : v ∈ P.first ⊔ P.second := by rw [P.complementary]; trivial
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
  rw [map_add, P.firstIsotropic u a hu.1 ha, P.secondIsotropic u b hu.2 hb, add_zero]

/-- The selected pair can never have zero velocity in either branch. -/
theorem suitablePair_velocities_nonzero (V : Type*)
    [AddCommGroup V] [Module ℂ V]
    (n : ℕ) (P : SuitablePositiveTangentPair V n) :
    P.firstVelocity ≠ 0 ∧ P.secondVelocity ≠ 0 := by
  constructor
  · intro h
    apply P.mixedNonzero
    rw [h, map_zero, LinearMap.zero_apply]
  · intro h
    apply P.mixedNonzero
    rw [h, map_zero]

end PairAndSmoothing

section EvaluationCokernel

variable (E V : Type*)
variable [AddCommGroup E] [Module ℂ E]
variable [AddCommGroup V] [Module ℂ V]

/-- Finite-dimensional linear-algebra shadow of the smoothing argument.
The vertical evaluation map has a one-dimensional cokernel detected by
`missing`, and a base-smoothing tangent vector crosses that hyperplane.

The existence of this package from the nodal map is a geometric theorem
(`H¹` normalization, relative Hom smoothness, and local contact jets). -/
structure SmoothingEvaluationPackage where
  verticalEvaluation : E →ₗ[ℂ] V
  missing : V →ₗ[ℂ] ℂ
  missing_nonzero : missing ≠ 0
  verticalImage : ∀ v : V,
    missing v = 0 ↔ ∃ e : E, verticalEvaluation e = v
  smoothingDirection : V
  smoothingTransverse : missing smoothingDirection ≠ 0

/-- The extra smoothing parameter fills the one missing evaluation direction. This is the linear-algebra
conclusion required before asserting the geometric two-point evaluation map is submersive. -/
theorem smoothing_fills_evaluation_cokernel
    (P : SmoothingEvaluationPackage E V) (v : V) :
    ∃ e : E, ∃ c : ℂ,
      P.verticalEvaluation e + c • P.smoothingDirection = v := by
  let c : ℂ := P.missing v / P.missing P.smoothingDirection
  have hker : P.missing (v - c • P.smoothingDirection) = 0 := by
    rw [map_sub, map_smul]
    change P.missing v - c * P.missing P.smoothingDirection = 0
    rw [show c * P.missing P.smoothingDirection = P.missing v from
      div_mul_cancel₀ _ P.smoothingTransverse, sub_self]
  obtain ⟨e, he⟩ := (P.verticalImage _).1 hker
  refine ⟨e, c, ?_⟩
  rw [he, sub_add_cancel]

/-- The vertical image is contained in the indicated hyperplane. -/
theorem verticalEvaluation_ker_missing
    (P : SmoothingEvaluationPackage E V) (e : E) :
    P.missing (P.verticalEvaluation e) = 0 :=
  (P.verticalImage (P.verticalEvaluation e)).2 ⟨e, rfl⟩

/-- The smoothing direction is not already generated by vertical
deformations fixing the smoothing parameter. -/
theorem smoothing_not_vertical
    (P : SmoothingEvaluationPackage E V) :
    ¬ ∃ e : E, P.verticalEvaluation e = P.smoothingDirection := by
  rintro ⟨e, he⟩
  have hzero := verticalEvaluation_ker_missing E V P e
  rw [he] at hzero
  exact P.smoothingTransverse hzero

end EvaluationCokernel

end LeBrunSalamon.PhaseTwenty

/-!
# Phase 21 -- degree-two stable maps, moving pairs, and descent data

The manuscript uses a proper (coarse) space of unmarked stable maps, its universal-curve square, two
tensor lifts, and a descent theorem. The existing phases do NOT construct a stable-map Deligne--Mumford
stack or coarse algebraic space. The honest statements below use scheme morphisms and sheaf maps, and
therefore form a RESTRICTED scheme-level interface. The passage from an algebraic stack/coarse space to
this interface remains a serious mathematical dependency.
-/

namespace LeBrunSalamon.PhaseTwentyOne

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open LeBrunSalamon.PhaseOne
open LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseEight
open LeBrunSalamon.PhaseSixteen

/-! ## 21A. Basic degree accounting in a stable-map boundary -/

/-- Positive degrees of the non-contracted components of a connected reducible curve. This does NOT encode
the dual graph or stability of contracted components. -/
structure PositiveComponentDegrees (r : ℕ) where
  degree : Fin r → ℕ
  positive : ∀ i : Fin r, 0 < degree i

/-- The total contact degree of the non-contracted components. -/
def PositiveComponentDegrees.total {r : ℕ}
    (D : PositiveComponentDegrees r) : ℕ :=
  ∑ i : Fin r, D.degree i

noncomputable section
set_option autoImplicit false

namespace PositiveDegreeProof

theorem atMostTwoPositiveComponents {r : ℕ}
    (D : PositiveComponentDegrees r)
    (h : D.total = 2) : r ≤ 2 := by
  calc
    r = ∑ _i : Fin r, (1 : ℕ) := by simp
    _ ≤ D.total := by
      unfold PositiveComponentDegrees.total
      exact Finset.sum_le_sum (fun i _ => Nat.succ_le_iff.mpr (D.positive i))
    _ = 2 := h

theorem twoPositiveComponents_haveDegreeOne
    (D : PositiveComponentDegrees 2)
    (h : D.total = 2) :
    D.degree 0 = 1 ∧ D.degree 1 = 1 := by
  have hsum : D.degree 0 + D.degree 1 = 2 := by
    simpa [PositiveComponentDegrees.total, Fin.sum_univ_two] using h
  have h0 := D.positive 0
  have h1 := D.positive 1
  constructor <;> omega

theorem onePositiveComponent_hasDegreeTwo
    (D : PositiveComponentDegrees 1)
    (h : D.total = 2) : D.degree 0 = 2 := by
  simpa [PositiveComponentDegrees.total] using h

end PositiveDegreeProof

end

/-- There can be at most two non-contracted components of an
unmarked stable map of total contact degree two. -/
theorem atMostTwoPositiveComponents {r : ℕ}
    (D : PositiveComponentDegrees r)
    (h : D.total = 2) : r ≤ 2 := by
  exact LeBrunSalamon.PhaseTwentyOne.PositiveDegreeProof.atMostTwoPositiveComponents (r := r) (D := D) (h := h)

/-- If there are exactly two non-contracted components, each has contact degree one. This is the numerical
part of the boundary-tree lemma. -/
theorem twoPositiveComponents_haveDegreeOne
    (D : PositiveComponentDegrees 2)
    (h : D.total = 2) :
    D.degree 0 = 1 ∧ D.degree 1 = 1 := by
  exact LeBrunSalamon.PhaseTwentyOne.PositiveDegreeProof.twoPositiveComponents_haveDegreeOne (D := D) (h := h)

/-- If the source is irreducible, its unique positive-degree component has degree two. -/
theorem onePositiveComponent_hasDegreeTwo
    (D : PositiveComponentDegrees 1)
    (h : D.total = 2) : D.degree 0 = 2 := by
  exact LeBrunSalamon.PhaseTwentyOne.PositiveDegreeProof.onePositiveComponent_hasDegreeTwo (D := D) (h := h)

/-! ## 21B. The two genuine tensor lifts of the contact value -/

/-- Scheme-level analogue of the moving-pair tensor data:

  W12 ∈ H⁰(Y,p*(T_X ⊠ L)),
  W21 ∈ H⁰(Y,p*(L ⊠ T_X)),

with a common image in p*(L ⊠ L).

All three sheaves are explicitly SUPPLIED: the external tensor
products and their canonical contact quotient maps are not yet in
mathlib's API used by this file.  The equations are actual morphism
equalities, not merely numerical evaluations at points. -/
structure MovingPairContactValue
    {d : ℕ} (X : SmoothProperComplexVariety d)
    (E12 E21 M : OModule (SelfProduct X.structureMap)) where
  source : Scheme
  projection : source ⟶ SelfProduct X.structureMap
  proper : IsProper projection
  dominant : DenseRange (fun y : source => projection y)
  map12 : E12 ⟶ M
  map21 : E21 ⟶ M
  vectorLift12 :
    (Scheme.Modules.pullback projection).obj
      (SheafOfModules.unit (SelfProduct X.structureMap).ringCatSheaf) ⟶
    (Scheme.Modules.pullback projection).obj E12
  vectorLift21 :
    (Scheme.Modules.pullback projection).obj
      (SheafOfModules.unit (SelfProduct X.structureMap).ringCatSheaf) ⟶
    (Scheme.Modules.pullback projection).obj E21
  commonContactValue :
    vectorLift12 ≫ (Scheme.Modules.pullback projection).map map12 =
      vectorLift21 ≫ (Scheme.Modules.pullback projection).map map21

/-- The common value as a genuine morphism of pulled-back sheaves. -/
noncomputable def MovingPairContactValue.value
    {d : ℕ} {X : SmoothProperComplexVariety d}
    {E12 E21 M : OModule (SelfProduct X.structureMap)}
    (D : MovingPairContactValue X E12 E21 M) :=
  D.vectorLift12 ≫ (Scheme.Modules.pullback D.projection).map D.map12

/-- The precisely typed global-section descent statement:
there is a B on X×X whose pullback equals the common value. -/
def MovingPairContactValue.AdmitsDescent
    {d : ℕ} {X : SmoothProperComplexVariety d}
    {E12 E21 M : OModule (SelfProduct X.structureMap)}
    (D : MovingPairContactValue X E12 E21 M) : Prop :=
  ∃ B : AlgebraicSection M, restrictSection D.projection B = D.value

/-- Sections of M on X×X are determined by their pullback to Y provided the latter map is injective on
sections. Dominance by itself does not imply injectivity over a possibly nonreduced target. -/
def MovingPairContactValue.SectionPullbackInjective
    {d : ℕ} {X : SmoothProperComplexVariety d}
    {E12 E21 M : OModule (SelfProduct X.structureMap)}
    (D : MovingPairContactValue X E12 E21 M) : Prop :=
  Function.Injective (fun B : AlgebraicSection M =>
    restrictSection D.projection B)

/-- Uniqueness in contact-value descent, CONDITIONAL on an actual
pullback-injectivity statement; this is not the deep existence theorem. -/
theorem movingPair_descent_unique
    {d : ℕ} {X : SmoothProperComplexVariety d}
    {E12 E21 M : OModule (SelfProduct X.structureMap)}
    (D : MovingPairContactValue X E12 E21 M)
    (hinj : D.SectionPullbackInjective)
    {B C : AlgebraicSection M}
    (hB : restrictSection D.projection B = D.value)
    (hC : restrictSection D.projection C = D.value) :
    B = C := by
  exact hinj (hB.trans hC.symm)

/-- The restriction of a descended section is the common value
computed using the second tensor lift as well. -/
theorem movingPair_descent_from_secondLift
    {d : ℕ} {X : SmoothProperComplexVariety d}
    {E12 E21 M : OModule (SelfProduct X.structureMap)}
    (D : MovingPairContactValue X E12 E21 M)
    (B : AlgebraicSection M)
    (hB : restrictSection D.projection B = D.value) :
    restrictSection D.projection B =
      D.vectorLift21 ≫
        (Scheme.Modules.pullback D.projection).map D.map21 := by
  calc
    restrictSection D.projection B = D.value := hB
    _ = D.vectorLift21 ≫
          (Scheme.Modules.pullback D.projection).map D.map21 :=
      D.commonContactValue

/-- The descent lemma from the manuscript is NOT simply `dominant + proper → existence of B`: it
additionally uses the two tensor lifts, covering contact lines, a finite image, unramifiedness tests, and
simple connectedness. A package that certifies the FINISHED descent is recorded without silently asserting
those geometric hypotheses have been formalized. -/
structure DescendedMovingPair
    {d : ℕ} {X : SmoothProperComplexVariety d}
    {E12 E21 M : OModule (SelfProduct X.structureMap)}
    (D : MovingPairContactValue X E12 E21 M) where
  «section» : AlgebraicSection M
  pullbackEqualsValue : restrictSection D.projection «section» = D.value

/-- Exchange symmetry follows from uniqueness of descent PROVIDED both the descended section and its
exchange satisfy the same pullback identity. Proving exchange compatibility for the stable-map tensor is a
separate theorem. -/
theorem descendedSection_isSymmetric
    {d : ℕ} {X : SmoothProperComplexVariety d}
    {E12 E21 M : OModule (SelfProduct X.structureMap)}
    (D : MovingPairContactValue X E12 E21 M)
    (h : DescendedMovingPair D)
    (τ : TwoPointExchangeIdentification X.structureMap M)
    (hinv : τ.IsInvolutiveOnGlobalSections)
    (hinj : D.SectionPullbackInjective)
    (hExchange : restrictSection D.projection
      (τ.swapSection h.«section») = D.value) :
    IsSymmetricUnderExchange X.structureMap M h.«section» τ := by
  refine ⟨hinv, ?_⟩
  exact hinj (hExchange.trans h.pullbackEqualsValue.symm)

/-! ## 21C. What quadratic vanishing actually contributes -/

/-- When the self-product is separated, the descended B may additionally vanish quadratically on the
actual diagonal. This condition is independent of dominance or properness of the map Y→X². -/
def DescendedMovingPair.VanishesQuadratically
    {d : ℕ} {X : SmoothProperComplexVariety d}
    [IsSeparated X.structureMap]
    {E12 E21 M : OModule (SelfProduct X.structureMap)}
    {D : MovingPairContactValue X E12 E21 M}
    (h : DescendedMovingPair D) : Prop :=
  VanishesQuadraticallyAlongDiagonal X.structureMap M h.«section»

/-- Exact quadratic vanishing is strictly stronger than just quadratic vanishing. It is the expected
consequence of a nonzero contact quadratic symbol. -/
def DescendedMovingPair.HasExactQuadraticOrder
    {d : ℕ} {X : SmoothProperComplexVariety d}
    [IsSeparated X.structureMap]
    {E12 E21 M : OModule (SelfProduct X.structureMap)}
    {D : MovingPairContactValue X E12 E21 M}
    (h : DescendedMovingPair D) : Prop :=
  HasExactDiagonalOrder X.structureMap M h.«section» 2

/-- Exact order two implies vanishing to order two. -/
theorem exactOrderTwo_implies_quadraticVanishing
    {d : ℕ} {X : SmoothProperComplexVariety d}
    [IsSeparated X.structureMap]
    {E12 E21 M : OModule (SelfProduct X.structureMap)}
    {D : MovingPairContactValue X E12 E21 M}
    (h : DescendedMovingPair D)
    (he : h.HasExactQuadraticOrder) :
    h.VanishesQuadratically :=
  he.1

end LeBrunSalamon.PhaseTwentyOne

/-!
# Phase 22 -- the nonvacuous symmetric-jet criterion in linear algebra

The actual manuscript proves first-jet generation by associating to a symmetric two-point kernel B a map
`beta : X → P(H⁰(L))`. In a local frame this map is described by a NONZERO section-valued function `w(x)`.
The derivative is injective modulo the line spanned by `w(x)` because of the full *cubic* contact Taylor
calculation (Phase 19).

This phase makes the final finite-dimensional argument precise: `w ≠ 0` and `dw(v) ∈ C*w ⇒ v=0` force
evaluation of sections to separate both values and first derivatives. The global construction of `w` from
B is still to be formalized via L⊠L and base change.
-/

namespace LeBrunSalamon.PhaseTwentyTwo

open LeBrunSalamon.PhaseNineteen
open LeBrunSalamon.PhaseSeventeen

section JetCriterion

variable (V S : Type*)
variable [AddCommGroup V] [Module ℂ V]
variable [AddCommGroup S] [Module ℂ S]

/-- One point of the kernel map, in a trivialization of its source line bundle: `w(x)` and the derivative
`dw_x` in a vector space of sections. This is ordinary algebraic differential data, not an unconstructed
projectivization of a scheme. -/
structure SectionValuedFirstJet where
  value : S
  derivative : V →ₗ[ℂ] S

variable {V S}

/-- The linear-algebra criterion for the corresponding map to
projective space to be immersive at the chosen point. -/
def SectionValuedFirstJet.IsProjectivelyImmersive
    (J : SectionValuedFirstJet V S) : Prop :=
  J.value ≠ 0 ∧
    ∀ (v : V) (k : ℂ), J.derivative v = k • J.value → v = 0

/-- Contraction against a linear functional on S gives the value
and the differential of a global section produced from B. -/
def SectionValuedFirstJet.contractedJet
    (J : SectionValuedFirstJet V S)
    (ell : S →ₗ[ℂ] ℂ) : TrivializedFirstJet V :=
  (ell J.value, ell.comp J.derivative)

/-- All ordinary first jets are attained by contractions of the section-valued kernel. This is a
SURJECTIVITY assertion, not just a rank count. -/
def SectionValuedFirstJet.SeparatesFirstJets
    (J : SectionValuedFirstJet V S) : Prop :=
  Function.Surjective J.contractedJet

variable (V S)

/-- The projective immersion criterion implies surjectivity of the dual first-jet map. This is the finite-
dimensional separation lemma used immediately after the symmetric-jet calculation. -/
theorem immersiveKernel_separatesFirstJets
    [FiniteDimensional ℂ V]
    (J : SectionValuedFirstJet V S)
    (h : J.IsProjectivelyImmersive) :
    J.SeparatesFirstJets := by
  let f : (ℂ × V) →ₗ[ℂ] S :=
    (LinearMap.fst ℂ ℂ V).smulRight J.value +
      J.derivative.comp (LinearMap.snd ℂ ℂ V)
  have hz : ∀ p : ℂ × V, f p = 0 → p = 0 := by
    intro p hp
    change p.1 • J.value + J.derivative p.2 = 0 at hp
    have hd : J.derivative p.2 = (-p.1) • J.value := by
      rw [neg_smul]
      exact eq_neg_iff_add_eq_zero.mpr (by simpa [add_comm] using hp)
    have hv : p.2 = 0 := h.2 p.2 (-p.1) hd
    have hc : p.1 • J.value = 0 := by simpa [hv] using hp
    have ha : p.1 = 0 := (smul_eq_zero.mp hc).resolve_right h.1
    exact Prod.ext ha hv
  have hf : Function.Injective f := by
    intro p q hpq
    apply sub_eq_zero.mp
    exact hz (p-q) (by rw [map_sub, hpq, sub_self])
  intro j
  let t : (ℂ × V) →ₗ[ℂ] ℂ :=
    (LinearMap.fst ℂ ℂ V).smulRight j.1 +
      j.2.comp (LinearMap.snd ℂ ℂ V)
  obtain ⟨ell, he⟩ := LinearMap.dualMap_surjective_of_injective hf t
  refine ⟨ell, ?_⟩
  apply Prod.ext
  · change ell J.value = j.1
    have h0 := LinearMap.congr_fun he (1, 0)
    change ell (f (1, 0)) = t (1, 0) at h0
    simpa [f, t] using h0
  · apply LinearMap.ext
    intro v
    have hv := LinearMap.congr_fun he (0, v)
    change ell (f (0, v)) = t (0, v) at hv
    simpa [f, t, SectionValuedFirstJet.contractedJet] using hv

/-- Conversely, jet separation implies that w is nonzero and that
its derivative is injective modulo the line it spans. -/
theorem separatingKernel_isImmersive
    (J : SectionValuedFirstJet V S)
    (h : J.SeparatesFirstJets) :
    J.IsProjectivelyImmersive := by
  constructor
  · intro hz
    obtain ⟨ell, hell⟩ := h (1, 0)
    have he := congrArg Prod.fst hell
    change ell J.value = 1 at he
    simp [hz] at he
  · intro v k hv
    apply (Module.forall_dual_apply_eq_zero_iff ℂ v).mp
    intro φ
    obtain ⟨ell, hell⟩ := h (0, φ)
    have hval := congrArg Prod.fst hell
    change ell J.value = 0 at hval
    have hder := congrArg Prod.snd hell
    have he := LinearMap.congr_fun hder v
    change ell (J.derivative v) = φ v at he
    rw [hv, map_smul, hval, smul_zero] at he
    exact he.symm

/-- The two conditions are equivalent over a finite-dimensional
tangent space.  The section space need not be given a preferred basis. -/
theorem immersiveKernel_iff_firstJetSeparation
    [FiniteDimensional ℂ V]
    (J : SectionValuedFirstJet V S) :
    J.IsProjectivelyImmersive ↔ J.SeparatesFirstJets := by
  constructor
  · exact immersiveKernel_separatesFirstJets V S J
  · exact separatingKernel_isImmersive V S J

/-- A local symmetric-kernel certificate.  It links the derivative
`dw` to the specific coefficient identities from the contact Taylor
calculation.  The link is not automatically available for an arbitrary
section-valued map; obtaining it from a global symmetric B is the
nontrivial diagonal-symbol theorem.

These are *necessary local equations*, not a fabricated contact-Fano
classification hypothesis. -/
structure SymmetricKernelContactJet where
  contact : ContactOneJet V
  kernel : SectionValuedFirstJet V S
  valueNonzero : kernel.value ≠ 0
  linearSymbolConstraint :
    ∀ (v : V) (k : ℂ),
      kernel.derivative v = k • kernel.value →
        ∀ s : V, contact.theta s * contact.theta v = 0
  quadraticSymbolConstraint :
    ∀ (v : V) (k : ℂ),
      kernel.derivative v = k • kernel.value →
        ∀ s : V,
          contact.theta s *
            (contact.exteriorValue v s - k * contact.theta s) = 0

/-- The symmetric contact symbol, including its cubic consequence,
forces the projective kernel map to be immersive. -/
theorem symmetricKernel_projectiveImmersion
    (K : SymmetricKernelContactJet V S) :
    K.kernel.IsProjectivelyImmersive := by
  refine ⟨K.valueNonzero, ?_⟩
  intro v k hv
  exact contactJet_noProjectiveKernel V K.contact v k
    (K.linearSymbolConstraint v k hv)
    (K.quadraticSymbolConstraint v k hv)

/-- This is the decisive finite-dimensional implication from the
symmetric two-point contact kernel to first-jet generation. -/
theorem symmetricKernel_firstJets
    [FiniteDimensional ℂ V]
    (K : SymmetricKernelContactJet V S) :
    K.kernel.SeparatesFirstJets :=
  immersiveKernel_separatesFirstJets V S K.kernel
    (symmetricKernel_projectiveImmersion V S K)

/-- This only unpacks the NONZERO FIELD of the local certificate. It does NOT prove nonvanishing from a
global quadratic symbol. That geometric obligation is stated separately in `Core.NormalizedContactKernel`.
The historical declaration name is retained for source compatibility. -/
theorem symmetricKernel_nonvanishing_of_quadraticSymbol
    (K : SymmetricKernelContactJet V S) :
    K.kernel.value ≠ 0 :=
  K.valueNonzero

end JetCriterion

end LeBrunSalamon.PhaseTwentyTwo

/-!
# Phase 23 -- global jet-to-transitivity and contact-classification targets

This phase assembles previously formalized candidate-level hypotheses without asserting that arbitrary
contact exact sequences are genuine contact Fano manifolds. It also records the DATA that a future proof
must construct to identify an adjoint orbit contact-isomorphically.
-/

namespace LeBrunSalamon.PhaseTwentyThree

open LeBrunSalamon.PhaseTwo

open CategoryTheory
open AlgebraicGeometry
open LeBrunSalamon.PhaseOne
open LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseFour
open LeBrunSalamon.PhaseSeven
open LeBrunSalamon.PhaseTen

/-- The complete current GLOBAL assumption layer for the jet-to-transitivity implication. The still-
missing intrinsic tangent sheaf and contact Hamiltonian correspondence are visible through the
compatibility certificate and are NOT asserted to exist generally. -/
structure ContactJetTransitivityPackage (n : ℕ) where
  geometry : ProjectiveContactCandidate n
  jetGeneration : SeparatesFirstJets geometry.contact.variety
    geometry.contact.contactSequence.line
  HamiltonianCompatibility :
    HamiltonianFirstJetCompatibility n geometry.contact

/-- Global Hamiltonian fields span every fibre once the contact
first-jet compatibility map has been constructed. -/
theorem contactJetTransitivity_globalSpanning
    {n : ℕ} (P : ContactJetTransitivityPackage n) :
    SpecifiedGlobalFieldsSpanEverywhere n P.geometry.contact
      P.HamiltonianCompatibility.liftedHamiltonianFields :=
  firstJets_and_Hamiltonians_span P.geometry.contact
    P.HamiltonianCompatibility P.jetGeneration

/-- The distinguished fields surject under the given Hamiltonian map.
This follows from the explicitly supplied section-to-field right inverse,
not from an unproved global contact Lie-derivative construction. -/
theorem contactJetTransitivity_HamiltonianSurjective
    {n : ℕ} (P : ContactJetTransitivityPackage n) :
    IsSpecifiedHamiltonianMapSurjective n P.geometry.contact
      P.HamiltonianCompatibility.liftedHamiltonianFields := by
  intro h
  exact ⟨P.HamiltonianCompatibility.fieldOfSection h,
    ⟨h, rfl⟩,
    P.HamiltonianCompatibility.hamiltonian_rightInverse h⟩

/-- The pointwise linear Lie-algebra-to-tangent map required to integrate an infinitesimal action to a
transitive action. This is finite- dimensional algebraic action data, not the mere existence of a spanning
set of arbitrary sheaf sections. -/
structure InfinitesimalActionAt (g V : Type*)
    [LieRing g] [LieAlgebra ℂ g]
    [AddCommGroup V] [Module ℂ V] where
  evaluate : g →ₗ[ℂ] V
  surjective : Function.Surjective evaluate

/-- A pointwise evaluation FAMILY at complex points, with a finite-dimensional Lie algebra as source. This
is a candidate, not a Lie-algebra action: linearity of evaluation, brackets and integration remain to be
supplied. We deliberately use a function-valued field rather than assuming a nonexistent scalar-module
instance on sheaf Homs. -/
structure GlobalInfinitesimalContactActionCandidate
    (g : Type*) [LieRing g] [LieAlgebra ℂ g]
    (n : ℕ) (X : ContactCandidate n) where
  finiteDimensional : Module.Finite ℂ g
  valueAt : ∀ x : ComplexPoint X.variety,
    g →
      ((Scheme.Modules.pullback x.map).obj
          (SheafOfModules.unit X.variety.scheme.ringCatSheaf) ⟶
       (Scheme.Modules.pullback x.map).obj X.tangent.sheaf)
  surjectiveAt : ∀ x : ComplexPoint X.variety,
    Function.Surjective (valueAt x)

/-- There is a meaningful distinction between: (a) infinitesimal transitivity of this Lie algebra, (b) a
connected ALGEBRAIC group integrating the action, and (c) an honest transitive group-scheme action on X.
The following proposition only unpacks (a). -/
def GlobalInfinitesimalContactActionCandidate.IsPointwiseSurjective
    {g : Type*} [LieRing g] [LieAlgebra ℂ g]
    {n : ℕ} {X : ContactCandidate n}
    (A : GlobalInfinitesimalContactActionCandidate g n X) : Prop :=
  ∀ x : ComplexPoint X.variety,
    Function.Surjective (A.valueAt x)

/-- The infinitesimal package really has surjective evaluations. -/
theorem globalInfinitesimalAction_spans
    {g : Type*} [LieRing g] [LieAlgebra ℂ g]
    {n : ℕ} {X : ContactCandidate n}
    (A : GlobalInfinitesimalContactActionCandidate g n X) :
    A.IsPointwiseSurjective :=
  A.surjectiveAt

/-- Point-set incidence model used in the Picard-number-two branch: a line contained in a hyperplane of a
complex vector space. This is a genuine flag of subspaces; the incidence VARIETY scheme and its contact
form are still to be constructed. -/
structure PointHyperplaneIncidence (n : ℕ) where
  line : Submodule ℂ (Fin (n + 2) → ℂ)
  hyperplane : Submodule ℂ (Fin (n + 2) → ℂ)
  lineRank : Module.finrank ℂ line = 1
  hyperplaneRank : Module.finrank ℂ hyperplane = n + 1
  included : line ≤ hyperplane

/-- A simple nilpotent-orbit model packaged with the actual structural
questions to settle: choice of Lie algebra, nonzero nilpotent vector,
and a projectivized orbit.  It is NOT yet an adjoint algebraic variety. -/
structure MarkedAdjointOrbitData
    (G : Type*) [Group G]
    (g : Type*) [LieRing g] [LieAlgebra ℂ g] where
  finite : Module.Finite ℂ g
  simple : IsSimpleComplexLieAlgebra g
  action : BracketPreservingLinearAction G g
  vector : g
  nonzero : vector ≠ 0
  nilpotent : IsAdjointNilpotent vector

/-- The underlying set of projective lines obtained from the chosen
nilpotent orbit, as a genuine subset of the submodule space. -/
def MarkedAdjointOrbitData.projectiveOrbit
    {G : Type*} [Group G]
    {g : Type*} [LieRing g] [LieAlgebra ℂ g]
    (D : MarkedAdjointOrbitData G g) :
    Set (Submodule ℂ g) :=
  projectiveOrbitAsLines D.action D.vector

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseFour LeBrunSalamon.PhaseSeven LeBrunSalamon.PhaseTen

namespace MarkedOrbitProof

theorem markedAdjointOrbit_nonzeroRepresentative
    {G : Type*} [Group G]
    {g : Type*} [LieRing g] [LieAlgebra ℂ g]
    (D : MarkedAdjointOrbitData G g)
    (ell : Submodule ℂ g) (hell : ell ∈ D.projectiveOrbit) :
    ∃ v : g, v ≠ 0 ∧ ell = Submodule.span ℂ ({v} : Set g) := by
  obtain ⟨sigma, hsigma⟩ := hell
  refine ⟨D.action.act sigma D.vector, ?_, hsigma⟩
  intro hz
  apply D.nonzero
  apply (D.action.act sigma).injective
  simpa only [map_zero] using hz

end MarkedOrbitProof

end

/-- Every point in the marked orbit is the line of a NONZERO vector. This is a preliminary nonvacuity
check before identifying an adjoint orbit with an algebraic projective homogeneous variety. -/
theorem markedAdjointOrbit_nonzeroRepresentative
    {G : Type*} [Group G]
    {g : Type*} [LieRing g] [LieAlgebra ℂ g]
    (D : MarkedAdjointOrbitData G g)
    (ell : Submodule ℂ g) (hell : ell ∈ D.projectiveOrbit) :
    ∃ v : g, v ≠ 0 ∧ ell = Submodule.span ℂ ({v} : Set g) := by
  exact LeBrunSalamon.PhaseTwentyThree.MarkedOrbitProof.markedAdjointOrbit_nonzeroRepresentative (G := G) (g := g) (D := D) (ell := ell) (hell := hell)

end LeBrunSalamon.PhaseTwentyThree

/-!
# Phase 24 -- numerical twistor normalization and the Wolf-space bridge

The Riemannian statement in the main namespace is the assertion `nabla R = 0`; the algebraic contact-Fano
classification is a separate theorem. The bridge requires the positive twistor theorem, Kodaira
algebraicity, simple-connectedness of Fano manifolds, classification of homogeneous contact varieties,
Wolf's correspondence, and LeBrun's metric uniqueness theorem.

Here we add the quantitative statements that can be expressed WITHOUT claiming those large theories have
been developed in mathlib.
-/

namespace LeBrunSalamon.PhaseTwentyFour

open LeBrunSalamon.PhaseFive
open LeBrunSalamon.PhaseSix
open LeBrunSalamon.PhaseEighteen

/-- Scale factor `c` such that, for an Einstein metric with positive scalar curvature `s` on a
quaternionic-Kähler 4n-manifold, `g_hat = c*g` has scalar curvature `16*n*(n+2)`. This is the
normalization used by the twistor correspondence. -/
noncomputable def quaternionicNormalizationFactor
    (n : ℕ) (scalar : ℝ) : ℝ :=
  scalar / (16 * (n : ℝ) * ((n : ℝ) + 2))

noncomputable section
set_option autoImplicit false
open LeBrunSalamon.PhaseEighteen

namespace NumericalNormalizationProof

theorem quaternionicNormalizationFactor_pos
    (n : ℕ) (hn : 1 ≤ n) (scalar : ℝ) (hs : 0 < scalar) :
    0 < quaternionicNormalizationFactor n scalar := by
  have hnNat : 0 < n := by omega
  have hnReal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnNat
  unfold quaternionicNormalizationFactor
  apply div_pos hs
  positivity

end NumericalNormalizationProof

end

/-- The normalization factor is strictly positive for positive
quaternionic dimension and positive scalar curvature. -/
theorem quaternionicNormalizationFactor_pos
    (n : ℕ) (hn : 1 ≤ n) (scalar : ℝ) (hs : 0 < scalar) :
    0 < quaternionicNormalizationFactor n scalar := by
  exact LeBrunSalamon.PhaseTwentyFour.NumericalNormalizationProof.quaternionicNormalizationFactor_pos (n := n) (hn := hn) (scalar := scalar) (hs := hs)

/-- The scalar curvature of a metric under a constant positive rescaling `g -> c*g` is divided by `c`.
Here only the numerical operation is defined; the Riemannian tensorial theorem is separate. -/
def scalarAfterConstantRescaling (scalar scale : ℝ) : ℝ :=
  scalar / scale

noncomputable section
set_option autoImplicit false
open LeBrunSalamon.PhaseEighteen

namespace NumericalNormalizationProof

theorem normalizedQuaternionicScalar
    (n : ℕ) (hn : 1 ≤ n) (scalar : ℝ) (hs : 0 < scalar) :
    scalarAfterConstantRescaling scalar
      (quaternionicNormalizationFactor n scalar) =
        16 * (n : ℝ) * ((n : ℝ) + 2) := by
  change scalar / (scalar / (16 * (n : ℝ) * ((n : ℝ) + 2))) = _
  exact div_div_cancel₀ (ne_of_gt hs)

end NumericalNormalizationProof

end

/-- Numerical recovery of the canonical quaternionic scalar curvature. -/
theorem normalizedQuaternionicScalar
    (n : ℕ) (hn : 1 ≤ n) (scalar : ℝ) (hs : 0 < scalar) :
    scalarAfterConstantRescaling scalar
      (quaternionicNormalizationFactor n scalar) =
        16 * (n : ℝ) * ((n : ℝ) + 2) := by
  exact LeBrunSalamon.PhaseTwentyFour.NumericalNormalizationProof.normalizedQuaternionicScalar (n := n) (hn := hn) (scalar := scalar) (hs := hs)

/-- The contact line degree of a minimal contact line. -/
def contactLineDegree : ℤ := 1

/-- A twistor fibre is TRANSVERSE and has contact degree TWO.  This
is not the same class of curves as a contact line. -/
def twistorFibreContactDegree : ℤ := 2

/-- Under `-K_X=(n+1)L`, the expected anticanonical degree of an L-degree-e curve. -/
def anticanonicalDegreeFromContactDegree (n : ℕ)
    (e : ℤ) : ℤ :=
  ((n : ℤ) + 1) * e

/-- Degree-one contact lines and degree-two twistor fibres are
numerically distinct in every quaternionic dimension. -/
theorem twistorFibre_not_contactLine :
    twistorFibreContactDegree ≠ contactLineDegree := by
  decide

noncomputable section
set_option autoImplicit false
open LeBrunSalamon.PhaseEighteen

namespace NumericalNormalizationProof

theorem twistorFibre_expectedTangentDegree
    (n : ℕ) :
    (∑ i : Fin (2 * n + 1), (quasiLineProfile n).degree i) =
      2 * ((n : ℤ) + 1) := by
  simp [quasiLineProfile, Fin.sum_univ_succ, Nat.cast_mul] <;> ring

end NumericalNormalizationProof

end

/-- The quasi-line splitting has the right rank and total tangent
degree for a twistor fibre: O(2) ⊕ O(1)^(2n). -/
theorem twistorFibre_expectedTangentDegree
    (n : ℕ) :
    (∑ i : Fin (2 * n + 1), (quasiLineProfile n).degree i) =
      2 * ((n : ℤ) + 1) := by
  exact LeBrunSalamon.PhaseTwentyFour.NumericalNormalizationProof.twistorFibre_expectedTangentDegree (n := n)

/-- The difference between the anticanonical degrees of a twistor
fibre and a contact line is exactly `n+1`. -/
theorem twistorFibre_degree_difference (n : ℕ) :
    anticanonicalDegreeFromContactDegree n twistorFibreContactDegree -
      anticanonicalDegreeFromContactDegree n contactLineDegree =
      (n : ℤ) + 1 := by
  unfold anticanonicalDegreeFromContactDegree
    twistorFibreContactDegree contactLineDegree
  ring

/-- The relevant Wolf-space family labels in a fixed dimension. A finite family of possible labels is not
the construction of the associated homogeneous Riemannian spaces. -/
def RelevantWolfFamilies (n : ℕ) : Set WolfFamily :=
  {W | W.IsRelevantInDimension n}

/-- The quaternionic projective family exists as a LABEL in every quaternionic dimension at least two.
Constructing its symmetric metric and twistor contact variety is still part of the bridge. -/
theorem quaternionicProjective_family_relevant
    (n : ℕ) (hn : 2 ≤ n) :
    WolfFamily.quaternionicProjective n ∈ RelevantWolfFamilies n := by
  exact ⟨hn, rfl⟩

/-- Exceptional Wolf labels have only their specified quaternionic dimensions. -/
theorem wolfG2_quaternionicDimension :
    WolfFamily.exceptionalG2.quaternionicDimension = 2 :=
  rfl

theorem wolfF4_quaternionicDimension :
    WolfFamily.exceptionalF4.quaternionicDimension = 7 :=
  rfl

theorem wolfE6_quaternionicDimension :
    WolfFamily.exceptionalE6.quaternionicDimension = 10 :=
  rfl

theorem wolfE7_quaternionicDimension :
    WolfFamily.exceptionalE7.quaternionicDimension = 16 :=
  rfl

theorem wolfE8_quaternionicDimension :
    WolfFamily.exceptionalE8.quaternionicDimension = 28 :=
  rfl

end LeBrunSalamon.PhaseTwentyFour

/-!
# Phase 25 -- intrinsic sheaf operations and universal differentials

PRIMARY SOURCES: Stacks Project, Tags 01UM, 01CF, 01PR; mathlib `AlgebraicGeometry/Modules/Sheaf`,
`Algebra/Category/ModuleCat/Presheaf/Monoidal`, and `Algebra/Category/ModuleCat/Presheaf/Sheafification`.

The tensor sheaf below is the sheafification of the actual tensor presheaf. Internal Hom, exterior powers
and relative differentials are specified by their universal properties and then chosen using explicitly
admitted existence lemmas. Thus the objects are mathematically constrained, not arbitrary sheaves, but
THEIR CONSTRUCTION STILL DEPENDS ON `sorry`. No existence lemma in this section is a claim that its proof
is completed.
-/

namespace LeBrunSalamon.PhaseTwentyFive

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseThree

/-- Functions and module sections on an actual scheme open. -/
abbrev RingSections (X : Scheme) (U : X.Opens) :=
  ↥(X.presheaf.obj (Opposite.op U))

abbrev SectionsOn {X : Scheme} (E : OModule X) (U : X.Opens) :=
  ↥(E.presheaf.obj (Opposite.op U))

abbrev structureModule (X : Scheme) : OModule X :=
  SheafOfModules.unit X.ringCatSheaf

/-- The tensor PRESHEAF must be sheafified. Tensoring global sections
is not a substitute for the tensor product of sheaves. -/
def tensorSheaf {X : Scheme} (E F : OModule X) : OModule X :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
    (PresheafOfModulesOfCommRing.Monoidal.tensorObj
      (R := X.presheaf) E.val F.val)

/-- Naturality of an actual morphism of module sheaves on sections. -/
theorem sheafHom_naturality {X : Scheme} {E F : OModule X}
    (h : E ⟶ F) {U V : X.Opens} (i : U ⟶ V) (e : SectionsOn E V) :
    F.presheaf.map i.op (h.app V e) = h.app U (E.presheaf.map i.op e) :=
  (PresheafOfModules.naturality_apply h.val i.op e).symm

/-- A bilinear map of sheaves, expressed on every open and compatible
with restriction. Bilinearity uses the LOCAL ring O_X(U). -/
structure SheafBilinearMap {X : Scheme} (E F G : OModule X) where
  apply : ∀ U : X.Opens,
    SectionsOn E U →ₗ[RingSections X U]
      (SectionsOn F U →ₗ[RingSections X U] SectionsOn G U)
  naturality : ∀ {U V : X.Opens} (i : U ⟶ V)
      (e : SectionsOn E V) (f : SectionsOn F V),
    G.presheaf.map i.op (apply V e f) =
      apply U (E.presheaf.map i.op e) (F.presheaf.map i.op f)

/-- Postcomposition is ordinary application of a sheaf morphism. -/
def SheafBilinearMap.postcompose {X : Scheme} {E F G H : OModule X}
    (b : SheafBilinearMap E F G) (h : G ⟶ H) :
    SheafBilinearMap E F H where
  apply U :=
    { toFun := fun e =>
        { toFun := fun f => h.app U (b.apply U e f)
          map_add' := by intros; simp
          map_smul' := by intros; simp }
      map_add' := by intros; apply LinearMap.ext; intro z; simp
      map_smul' := by intros; apply LinearMap.ext; intro z; simp }
  naturality := by
    intro U V i e f
    dsimp
    rw [sheafHom_naturality, b.naturality]

/-- Pull both inputs through genuine sheaf morphisms. -/
def SheafBilinearMap.precompose {X : Scheme}
    {E F E' F' G : OModule X}
    (b : SheafBilinearMap E' F' G) (f : E ⟶ E') (g : F ⟶ F') :
    SheafBilinearMap E F G where
  apply U :=
    { toFun := fun e =>
        { toFun := fun z => b.apply U (f.app U e) (g.app U z)
          map_add' := by intros; simp
          map_smul' := by intros; simp }
      map_add' := by intros; apply LinearMap.ext; intro z; simp
      map_smul' := by intros; apply LinearMap.ext; intro z; simp }
  naturality := by
    intro U V i e z
    dsimp
    rw [b.naturality, sheafHom_naturality, sheafHom_naturality]

/-- Universal pairing into the concrete sheafified tensor presheaf.
Choosing such a pairing fixes all induced maps in this section. -/
structure TensorSheafPresentation {X : Scheme} (E F : OModule X) where
  pair : SheafBilinearMap E F (tensorSheaf E F)
  universal : ∀ G : OModule X,
    Function.Bijective
      (fun h : tensorSheaf E F ⟶ G => pair.postcompose h)

theorem sheafBilinearMap_ext {X : Scheme} {E F G : OModule X}
    (b c : SheafBilinearMap E F G)
    (h : ∀ U e f, b.apply U e f = c.apply U e f) : b = c := by
  cases b
  cases c
  congr 1
  funext U
  ext e f
  exact h U e f

namespace TensorConstruction

set_option backward.isDefEq.respectTransparency false

abbrev presheaf {X : Scheme} (E F : OModule X) :=
  PresheafOfModulesOfCommRing.Monoidal.tensorObj
    (R := X.presheaf) E.val F.val

def homToBilinear {X : Scheme} {E F G : OModule X}
    (h : presheaf E F ⟶ G.val) : SheafBilinearMap E F G where
  apply U := TensorProduct.curry (h.app (Opposite.op U)).hom
  naturality := by
    intro U V i e f
    change G.val.map i.op (h.app (Opposite.op V) (e ⊗ₜ[RingSections X V] f)) =
      h.app (Opposite.op U)
        ((E.val.map i.op e) ⊗ₜ[RingSections X U] (F.val.map i.op f))
    exact (PresheafOfModules.naturality_apply h i.op
      (e ⊗ₜ[RingSections X V] f)).symm

def bilinearToHom {X : Scheme} {E F G : OModule X}
    (b : SheafBilinearMap E F G) : presheaf E F ⟶ G.val :=
  PresheafOfModulesOfCommRing.homMk
    (fun U => ModuleCat.ofHom (TensorProduct.lift (b.apply U.unop)))
    (fun i => ModuleCat.MonoidalCategory.tensor_ext (fun e f => by
      exact (b.naturality i.unop e f).symm))

def presheafHomEquiv {X : Scheme} (E F G : OModule X) :
    (presheaf E F ⟶ G.val) ≃ SheafBilinearMap E F G where
  toFun := homToBilinear
  invFun := bilinearToHom
  left_inv h := by
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro e f
    rfl
  right_inv b := by
    apply sheafBilinearMap_ext
    intro U e f
    rfl

def sheafHomEquiv {X : Scheme} (E F G : OModule X) :
    (tensorSheaf E F ⟶ G) ≃ SheafBilinearMap E F G :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj)).trans
    (presheafHomEquiv E F G)

def presentation {X : Scheme} (E F : OModule X) : TensorSheafPresentation E F where
  pair := sheafHomEquiv E F (tensorSheaf E F) (𝟙 _)
  universal G := by
    have hp : (fun h : tensorSheaf E F ⟶ G =>
        (sheafHomEquiv E F (tensorSheaf E F) (𝟙 _)).postcompose h) =
        sheafHomEquiv E F G := by
      funext h
      apply sheafBilinearMap_ext
      intro U e f
      rfl
    rw [hp]
    exact (sheafHomEquiv E F G).bijective


end TensorConstruction

/-- The sheafification of the actual tensor presheaf has its canonical universal property. -/
theorem tensorSheafPresentation_exists {X : Scheme} (E F : OModule X) :
    Nonempty (TensorSheafPresentation E F) := ⟨TensorConstruction.presentation E F⟩

def tensorPresentation {X : Scheme} (E F : OModule X) :
    TensorSheafPresentation E F :=
  TensorConstruction.presentation E F

def tensorLift {X : Scheme} {E F G : OModule X}
    (b : SheafBilinearMap E F G) : tensorSheaf E F ⟶ G :=
  (Equiv.ofBijective
    (fun h : tensorSheaf E F ⟶ G =>
      (tensorPresentation E F).pair.postcompose h)
    ((tensorPresentation E F).universal G)).symm b

/-- This tensor map is induced by the CHOSEN universal pairing,
so subsequent coherence statements use one consistent convention. -/
def tensorMap {X : Scheme} {E F E' F' : OModule X}
    (f : E ⟶ E') (g : F ⟶ F') :
    tensorSheaf E F ⟶ tensorSheaf E' F' :=
  tensorLift ((tensorPresentation E' F').pair.precompose f g)



theorem tensorLift_pair {X : Scheme} {E F G : OModule X}
    (b : SheafBilinearMap E F G) :
    (tensorPresentation E F).pair.postcompose (tensorLift b) = b := by
  exact (Equiv.ofBijective _ ((tensorPresentation E F).universal G)).apply_symm_apply b

theorem tensorMap_apply {X : Scheme} {E F E' F' : OModule X}
    (f : E ⟶ E') (g : F ⟶ F') (U : X.Opens)
    (e : SectionsOn E U) (z : SectionsOn F U) :
    (tensorMap f g).app U ((tensorPresentation E F).pair.apply U e z) =
      (tensorPresentation E' F').pair.apply U (f.app U e) (g.app U z) := by
  exact congrArg (fun b : SheafBilinearMap E F (tensorSheaf E' F') => b.apply U e z)
    (tensorLift_pair ((tensorPresentation E' F').pair.precompose f g))

theorem tensorMap_id {X : Scheme} (E F : OModule X) :
    tensorMap (𝟙 E) (𝟙 F) = 𝟙 (tensorSheaf E F) := by
  apply ((tensorPresentation E F).universal _).1
  apply sheafBilinearMap_ext
  intro U e f
  change (tensorMap (𝟙 E) (𝟙 F)).app U ((tensorPresentation E F).pair.apply U e f) = _
  rw [tensorMap_apply]
  rfl

theorem tensorMap_comp {X : Scheme} {E₀ E₁ E₂ F₀ F₁ F₂ : OModule X}
    (f : E₀ ⟶ E₁) (f' : E₁ ⟶ E₂)
    (g : F₀ ⟶ F₁) (g' : F₁ ⟶ F₂) :
    tensorMap (f ≫ f') (g ≫ g') = tensorMap f g ≫ tensorMap f' g' := by
  apply ((tensorPresentation E₀ F₀).universal _).1
  apply sheafBilinearMap_ext
  intro U e z
  change (tensorMap (f ≫ f') (g ≫ g')).app U ((tensorPresentation E₀ F₀).pair.apply U e z) =
    (tensorMap f' g').app U ((tensorMap f g).app U ((tensorPresentation E₀ F₀).pair.apply U e z))
  rw [tensorMap_apply, tensorMap_apply, tensorMap_apply]
  rfl

def tensorIso {X : Scheme} {E F E' F' : OModule X}
    (e : E ≅ E') (f : F ≅ F') : tensorSheaf E F ≅ tensorSheaf E' F' where
  hom := tensorMap e.hom f.hom
  inv := tensorMap e.inv f.inv
  hom_inv_id := by rw [← tensorMap_comp, e.hom_inv_id, f.hom_inv_id, tensorMap_id]
  inv_hom_id := by rw [← tensorMap_comp, e.inv_hom_id, f.inv_hom_id, tensorMap_id]

namespace TensorConstruction

set_option backward.isDefEq.respectTransparency false

def flip {X : Scheme} {E F G : OModule X} (b : SheafBilinearMap E F G) :
    SheafBilinearMap F E G where
  apply U := (b.apply U).flip
  naturality := by intro U V i f e; exact b.naturality i e f

def commHom {X : Scheme} (E F : OModule X) : tensorSheaf E F ⟶ tensorSheaf F E :=
  tensorLift (flip (tensorPresentation F E).pair)

theorem commHom_pair {X : Scheme} (E F : OModule X) (U : X.Opens)
    (e : SectionsOn E U) (f : SectionsOn F U) :
    (commHom E F).app U ((tensorPresentation E F).pair.apply U e f) =
      (tensorPresentation F E).pair.apply U f e := by
  exact congrArg (fun b : SheafBilinearMap E F (tensorSheaf F E) => b.apply U e f)
    (tensorLift_pair (flip (tensorPresentation F E).pair))

def commIso {X : Scheme} (E F : OModule X) : tensorSheaf E F ≅ tensorSheaf F E where
  hom := commHom E F
  inv := commHom F E
  hom_inv_id := by
    apply ((tensorPresentation E F).universal _).1
    apply sheafBilinearMap_ext
    intro U e f
    change (commHom F E).app U
        ((commHom E F).app U ((tensorPresentation E F).pair.apply U e f)) = _
    rw [commHom_pair, commHom_pair]
    rfl
  inv_hom_id := by
    apply ((tensorPresentation F E).universal _).1
    apply sheafBilinearMap_ext
    intro U f e
    change (commHom E F).app U
        ((commHom F E).app U ((tensorPresentation F E).pair.apply U f e)) = _
    rw [commHom_pair, commHom_pair]
    rfl

def scalarPair {X : Scheme} (E : OModule X) :
    SheafBilinearMap (structureModule X) E E where
  apply U := LinearMap.lsmul (RingSections X U) (SectionsOn E U)
  naturality := by
    intro U V i a e
    exact E.val.map_smul i.op a e

def leftUnitHom {X : Scheme} (E : OModule X) :
    tensorSheaf (structureModule X) E ⟶ E := tensorLift (scalarPair E)

theorem leftUnitHom_pair {X : Scheme} (E : OModule X) (U : X.Opens)
    (a : RingSections X U) (e : SectionsOn E U) :
    (leftUnitHom E).app U ((tensorPresentation (structureModule X) E).pair.apply U a e) =
      a • e := by
  exact congrArg (fun b : SheafBilinearMap (structureModule X) E E => b.apply U a e)
    (tensorLift_pair (scalarPair E))

def leftUnitInv {X : Scheme} (E : OModule X) :
    E ⟶ tensorSheaf (structureModule X) E where
  val := PresheafOfModulesOfCommRing.homMk
    (fun U => ModuleCat.ofHom
      (X := E.val.obj U) (Y := (tensorSheaf (structureModule X) E).val.obj U)
      ((tensorPresentation (structureModule X) E).pair.apply U.unop
        (1 : RingSections X U.unop)))
    (by
      intro U V i
      ext e
      change (tensorPresentation (structureModule X) E).pair.apply V.unop
          (1 : RingSections X V.unop) (E.val.map i e) =
        (tensorSheaf (structureModule X) E).val.map i
          ((tensorPresentation (structureModule X) E).pair.apply U.unop
            (1 : RingSections X U.unop) e)
      have h := (tensorPresentation (structureModule X) E).pair.naturality
        i.unop (1 : RingSections X U.unop) e
      change (tensorSheaf (structureModule X) E).val.map i
          ((tensorPresentation (structureModule X) E).pair.apply U.unop
            (1 : RingSections X U.unop) e) =
        (tensorPresentation (structureModule X) E).pair.apply V.unop
          (X.presheaf.map i (1 : RingSections X U.unop)) (E.val.map i e) at h
      simpa only [map_one] using h.symm)

def leftUnitIso {X : Scheme} (E : OModule X) :
    tensorSheaf (structureModule X) E ≅ E where
  hom := leftUnitHom E
  inv := leftUnitInv E
  hom_inv_id := by
    apply ((tensorPresentation (structureModule X) E).universal _).1
    apply sheafBilinearMap_ext
    intro U a e
    change (tensorPresentation (structureModule X) E).pair.apply U (1 : RingSections X U)
        ((leftUnitHom E).app U
          ((tensorPresentation (structureModule X) E).pair.apply U a e)) =
      (tensorPresentation (structureModule X) E).pair.apply U a e
    rw [leftUnitHom_pair, map_smul]
    have h := congrArg (fun f => f e)
      (((tensorPresentation (structureModule X) E).pair.apply U).map_smul a
        (1 : RingSections X U))
    simpa using h.symm
  inv_hom_id := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    ext e
    change (leftUnitHom E).app U.unop
      ((tensorPresentation (structureModule X) E).pair.apply U.unop
        (1 : RingSections X U.unop) e) = e
    rw [leftUnitHom_pair, one_smul]


end TensorConstruction


theorem tensorSheaf_comm {X : Scheme} (E F : OModule X) :
    Nonempty (tensorSheaf E F ≅ tensorSheaf F E) := ⟨TensorConstruction.commIso E F⟩

theorem tensorSheaf_leftUnit {X : Scheme} (E : OModule X) :
    Nonempty (tensorSheaf (structureModule X) E ≅ E) := ⟨TensorConstruction.leftUnitIso E⟩

theorem tensorSheaf_rightUnit {X : Scheme} (E : OModule X) :
    Nonempty (tensorSheaf E (structureModule X) ≅ E) := ⟨TensorConstruction.commIso E (structureModule X) ≪≫ TensorConstruction.leftUnitIso E⟩

/-- **Published input (exact).** Pullback of modules on ringed spaces
commutes with tensor product.  This is the direct formal encoding of
Stacks Project, Lemma 17.16.4 (Tag 01CD); no contact-geometric or
LeBrun--Salamon hypothesis occurs in the statement. -/
theorem _root_.LeBrunSalamon.PublishedInputs.SheafFunctoriality.pullback_tensorProduct
    {X Y : Scheme} (f : X ⟶ Y) (E F : OModule Y) :
    Nonempty (pullbackModule f (tensorSheaf E F) ≅
      tensorSheaf (pullbackModule f E) (pullbackModule f F)) := by
  sorry

/-- Project API wrapper for the exact tensor-pullback input. -/
theorem tensorSheaf_pullback {X Y : Scheme} (f : X ⟶ Y)
    (E F : OModule Y) :
    Nonempty (pullbackModule f (tensorSheaf E F) ≅
      tensorSheaf (pullbackModule f E) (pullbackModule f F)) :=
  LeBrunSalamon.PublishedInputs.SheafFunctoriality.pullback_tensorProduct f E F

end LeBrunSalamon.PhaseTwentyFive

namespace LeBrunSalamon.SheafTensor
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CategoryTheory.MonoidalCategory
open LeBrunSalamon.PhaseOne
set_option backward.isDefEq.respectTransparency false

variable {C : Type} [Category.{0} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{0})
  [HasSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat]

/-- A finite free module sheaf has the expected underlying free presheaf. -/
def underlyingFreeIso (I : Type) [Finite I] :
    (SheafOfModules.free (R := R) I).val ≅
      ∐ (fun _ : I => (SheafOfModules.unit R).val) :=
  (asIso (sigmaComparison (SheafOfModules.forget R)
    (fun _ : I => SheafOfModules.unit R))).symm

section Commutative
variable (Rc : Sheaf J CommRingCat.{0})
abbrev ringSheafOfComm : Sheaf J RingCat :=
  (sheafCompose J (forget₂ CommRingCat RingCat)).obj Rc

abbrev tensorPresheaf (E F : SheafOfModules (ringSheafOfComm Rc)) :=
  PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := Rc.obj) E.val F.val

def tensor (E F : SheafOfModules (ringSheafOfComm Rc)) : SheafOfModules (ringSheafOfComm Rc) :=
  (PresheafOfModules.sheafification (𝟙 (ringSheafOfComm Rc).obj)).obj (tensorPresheaf Rc E F)

def tensorIso {E E' F F' : SheafOfModules (ringSheafOfComm Rc)} (e : E ≅ E') (f : F ≅ F') :
    tensor Rc E F ≅ tensor Rc E' F' :=
  (PresheafOfModules.sheafification (𝟙 (ringSheafOfComm Rc).obj)).mapIso
    (CategoryTheory.MonoidalCategory.tensorIso (C := PresheafOfModulesOfCommRing Rc.obj)
      ((SheafOfModules.forget (ringSheafOfComm Rc)).mapIso e)
      ((SheafOfModules.forget (ringSheafOfComm Rc)).mapIso f))

def presheafUnitTensorFreeIso (I K : Type) :
    (∐ (fun _ : I => (𝟙_ (PresheafOfModulesOfCommRing Rc.obj)))) ⊗
      (∐ (fun _ : K => (𝟙_ (PresheafOfModulesOfCommRing Rc.obj)))) ≅
      ∐ (fun _ : Σ _ : I, K => (𝟙_ (PresheafOfModulesOfCommRing Rc.obj))) :=
  (asIso (sigmaComparison
    (tensorRight (∐ (fun _ : K => (𝟙_ (PresheafOfModulesOfCommRing Rc.obj)))))
    (fun _ : I => (𝟙_ (PresheafOfModulesOfCommRing Rc.obj))))).symm ≪≫
  Sigma.mapIso (fun _ : I =>
    (asIso (sigmaComparison (tensorLeft (𝟙_ (PresheafOfModulesOfCommRing Rc.obj)))
      (fun _ : K => (𝟙_ (PresheafOfModulesOfCommRing Rc.obj))))).symm ≪≫
      Sigma.mapIso (fun _ : K => λ_ (𝟙_ (PresheafOfModulesOfCommRing Rc.obj)))) ≪≫
  sigmaSigmaIso (fun _ : I => K)
    (fun _ _ => (𝟙_ (PresheafOfModulesOfCommRing Rc.obj)))

def sheafificationUnitIso :
    (PresheafOfModules.sheafification (𝟙 (ringSheafOfComm Rc).obj)).obj
      (𝟙_ (PresheafOfModulesOfCommRing Rc.obj)) ≅ SheafOfModules.unit (ringSheafOfComm Rc) :=
  asIso ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheafOfComm Rc).obj)).counit.app
    (SheafOfModules.unit (ringSheafOfComm Rc)))

/-- Tensoring finite free sheaves multiplies their basis sets. -/
def freeTensorIso (I K : Type) [Finite I] [Finite K] :
    tensor Rc (SheafOfModules.free (R := (ringSheafOfComm Rc)) I) (SheafOfModules.free (R := (ringSheafOfComm Rc)) K) ≅
      SheafOfModules.free (R := (ringSheafOfComm Rc)) (Σ _ : I, K) :=
  (PresheafOfModules.sheafification (𝟙 (ringSheafOfComm Rc).obj)).mapIso
    (CategoryTheory.MonoidalCategory.tensorIso (C := PresheafOfModulesOfCommRing Rc.obj) (underlyingFreeIso (ringSheafOfComm Rc) I)
      (underlyingFreeIso (ringSheafOfComm Rc) K) ≪≫ presheafUnitTensorFreeIso Rc I K) ≪≫
  (asIso (sigmaComparison (PresheafOfModules.sheafification (𝟙 (ringSheafOfComm Rc).obj))
    (fun _ : Σ _ : I, K => (𝟙_ (PresheafOfModulesOfCommRing Rc.obj))))).symm ≪≫
  Sigma.mapIso (fun _ => sheafificationUnitIso Rc)

end Commutative

/-- Relabel the generators of a free sheaf by an equivalence. -/
def freeReindexIso {C : Type*} [Category* C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat) [HasSheafify J AddCommGrpCat]
    [J.WEqualsLocallyBijective AddCommGrpCat]
    {I K : Type} (e : I ≃ K) :
    SheafOfModules.free (R := R) I ≅ SheafOfModules.free (R := R) K :=
  (SheafOfModules.freeFunctor (R := R)).mapIso e.toIso

/-- A local trivialization remains a trivialization after shrinking its open. -/
def freeTrivializationRestrict {X : Scheme} {E : OModule X}
    {U V : X.Opens} (f : V ⟶ U) {I : Type}
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ E.over U) :
    SheafOfModules.free (R := X.ringCatSheaf.over V) I ≅ E.over V :=
  SheafOfModules.mapFreeIso (SheafOfModules.overMap X.ringCatSheaf f) I
      (SheafOfModules.overMapUnitIso (R := X.ringCatSheaf) f).symm ≪≫
    (SheafOfModules.overMap X.ringCatSheaf f).mapIso e ≪≫
    (SheafOfModules.overFunctorMap X.ringCatSheaf f).app E

/-- The chart indexed by a local free basis, with basis relabelled by Fin r. -/
def localBasisTrivialization {X : Scheme} {E : OModule X} {r : ℕ}
    (q : SheafOfModules.LocalGeneratorsData.{0} E) [q.IsLocallyFreeData]
    (hr : ∀ i : q.I, Nonempty ((q.generators i).I ≃ Fin r)) (i : q.I) :
    SheafOfModules.free (R := X.ringCatSheaf.over (q.X i)) (Fin r) ≅ E.over (q.X i) :=
  freeReindexIso _ (hr i).some.symm ≪≫ asIso (q.generators i).π

/-- Intersections of two genuine local-generator covers still cover. -/
theorem intersectCover {X : Scheme} {E F : OModule X}
    (q : SheafOfModules.LocalGeneratorsData.{0} E)
    (q' : SheafOfModules.LocalGeneratorsData.{0} F) :
    (Opens.grothendieckTopology X).CoversTop
      (fun i : q.I × q'.I => q.X i.1 ⊓ q'.X i.2) := by
  apply (Opens.coversTop_iff X _).mpr
  have hq := (Opens.coversTop_iff X q.X).mp q.coversTop
  have hq' := (Opens.coversTop_iff X q'.X).mp q'.coversTop
  change (⨆ i : q.I × q'.I, q.X i.1 ⊓ q'.X i.2) = ⊤
  apply eq_top_iff.mpr
  intro x hx
  obtain ⟨i, hi⟩ := hq.exists_mem x
  obtain ⟨j, hj⟩ := hq'.exists_mem x
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨(i, j), hi, hj⟩

/-- Assemble genuine finite-rank local freeness from a free cover. -/
theorem rank_of_free_cover {X : Scheme} (E : OModule X) (r : ℕ)
    {ι : Type} (U : ι → X.Opens)
    (hU : (Opens.grothendieckTopology X).CoversTop U)
    (e : ∀ i, SheafOfModules.free (R := X.ringCatSheaf.over (U i)) (Fin r) ≅ E.over (U i)) :
    IsLocallyFreeOfRank E r := by
  let q : SheafOfModules.LocalGeneratorsData.{0} E :=
    { I := ι
      X := U
      coversTop := hU
      generators := fun i => (SheafOfModules.free.generatingSections
        (R := X.ringCatSheaf.over (U i)) (Fin r)).ofEpi (e i).hom }
  refine ⟨q, ?_, fun _ => ⟨Equiv.refl _⟩⟩
  constructor
  intro i
  change IsIso ((SheafOfModules.free.generatingSections (Fin r)).ofEpi (e i).hom).π
  rw [SheafOfModules.GeneratingSections.ofEpi_π]
  infer_instance

/-- Two finite-rank locally free sheaves admit a common free cover. -/
theorem exists_common_free_cover {X : Scheme} {E F : OModule X} {r s : ℕ}
    (hE : IsLocallyFreeOfRank E r) (hF : IsLocallyFreeOfRank F s) :
    ∃ (ι : Type) (U : ι → X.Opens),
      (Opens.grothendieckTopology X).CoversTop U ∧
      Nonempty (∀ i, SheafOfModules.free (R := X.ringCatSheaf.over (U i)) (Fin r) ≅ E.over (U i)) ∧
      Nonempty (∀ i, SheafOfModules.free (R := X.ringCatSheaf.over (U i)) (Fin s) ≅ F.over (U i)) := by
  obtain ⟨q, hq, hr⟩ := hE
  obtain ⟨q', hq', hs⟩ := hF
  letI := hq
  letI := hq'
  refine ⟨q.I × q'.I, (fun i => q.X i.1 ⊓ q'.X i.2), intersectCover q q', ?_, ?_⟩
  · exact ⟨fun i => freeTrivializationRestrict (homOfLE inf_le_left)
      (localBasisTrivialization q hr i.1)⟩
  · exact ⟨fun i => freeTrivializationRestrict (homOfLE inf_le_right)
      (localBasisTrivialization q' hs i.2)⟩

abbrev overPresheaf (X : Scheme) (U : X.Opens) :=
  PresheafOfModules.pushforward₀ (Over.forget U) X.ringCatSheaf.obj

def sheafificationOverHom (X : Scheme) (U : X.Opens)
    (P : PresheafOfModules X.ringCatSheaf.obj) :
    (PresheafOfModules.sheafification (𝟙 (X.ringCatSheaf.over U).obj)).obj
      ((overPresheaf X U).obj P) ⟶
    ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P).over U :=
  (PresheafOfModules.sheafificationHomEquiv
    (𝟙 (X.ringCatSheaf.over U).obj)).symm
      ((overPresheaf X U).map
        ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P))

theorem sheafificationOverHom_toSheaf (X : Scheme) (U : X.Opens)
    (P : PresheafOfModules X.ringCatSheaf.obj) :
    (SheafOfModules.toSheaf (X.ringCatSheaf.over U)).map
        (sheafificationOverHom X U P) =
      ((Over.forget U).pushforwardContinuousSheafificationCompatibility AddCommGrpCat
        ((Opens.grothendieckTopology X).over U) (Opens.grothendieckTopology X)).hom.app
        P.presheaf := by
  apply (sheafToPresheaf _ AddCommGrpCat).map_injective
  change ((SheafOfModules.toSheaf (X.ringCatSheaf.over U)).map
        (sheafificationOverHom X U P)).hom =
      (((Over.forget U).pushforwardContinuousSheafificationCompatibility AddCommGrpCat
        ((Opens.grothendieckTopology X).over U) (Opens.grothendieckTopology X)).hom.app
        P.presheaf).hom
  rw [Functor.pushforwardContinuousSheafificationCompatibility_hom_app_hom]
  change _ = CategoryTheory.sheafifyLift _ _ _
  rw [sheafificationOverHom, PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm]
  rfl

instance sheafificationOverHom_isIso (X : Scheme) (U : X.Opens)
    (P : PresheafOfModules X.ringCatSheaf.obj) :
    IsIso (sheafificationOverHom X U P) := by
  haveI : IsIso ((SheafOfModules.toSheaf (X.ringCatSheaf.over U)).map
      (sheafificationOverHom X U P)) := by
    rw [sheafificationOverHom_toSheaf]
    infer_instance
  exact isIso_of_reflects_iso _ (SheafOfModules.toSheaf (X.ringCatSheaf.over U))

/-- Restriction to an actual open commutes with the associated module sheaf. -/
def sheafificationOverIso (X : Scheme) (U : X.Opens)
    (P : PresheafOfModules X.ringCatSheaf.obj) :
    (PresheafOfModules.sheafification (𝟙 (X.ringCatSheaf.over U).obj)).obj
      ((overPresheaf X U).obj P) ≅
    ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P).over U :=
  asIso (sheafificationOverHom X U P)

/-- The sheafified tensor over the ringed site of opens contained in U. -/
def overTensor (X : Scheme) (U : X.Opens)
    (E F : SheafOfModules (X.ringCatSheaf.over U)) :
    SheafOfModules (X.ringCatSheaf.over U) :=
  (PresheafOfModules.sheafification (𝟙 (X.ringCatSheaf.over U).obj)).obj
    (PresheafOfModulesOfCommRing.Monoidal.tensorObj
      (R := (Over.forget U).op ⋙ X.presheaf) E.val F.val)

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
def overTensorPresheafIso {X : Scheme} (U : X.Opens) (E F : X.Modules) :
    (overPresheaf X U).obj
      (PresheafOfModulesOfCommRing.Monoidal.tensorObj
        (R := X.presheaf) E.val F.val) ≅
    PresheafOfModulesOfCommRing.Monoidal.tensorObj
      (R := (Over.forget U).op ⋙ X.presheaf) (E.over U).val (F.over U).val :=
  PresheafOfModules.isoMk
    (M₁ := (overPresheaf X U).obj
      (PresheafOfModulesOfCommRing.Monoidal.tensorObj
        (R := X.presheaf) E.val F.val))
    (M₂ := PresheafOfModulesOfCommRing.Monoidal.tensorObj
      (R := (Over.forget U).op ⋙ X.presheaf) (E.over U).val (F.over U).val)
    (fun _ => Iso.refl _)
    (fun {V W} _ => ModuleCat.MonoidalCategory.tensor_ext
      (R := X.presheaf.obj (Opposite.op V.unop.left)) (fun _ _ => rfl))

/-- The actual tensor sheaf, restricted to U, is the local sheafified tensor. -/
def tensorOverIso {X : Scheme} (U : X.Opens) (E F : X.Modules) :
    (PhaseTwentyFive.tensorSheaf E F).over U ≅
      overTensor X U (E.over U) (F.over U) :=
  (sheafificationOverIso X U
    (PresheafOfModulesOfCommRing.Monoidal.tensorObj
      (R := X.presheaf) E.val F.val)).symm ≪≫
    (PresheafOfModules.sheafification (𝟙 (X.ringCatSheaf.over U).obj)).mapIso
      (overTensorPresheafIso U E F)

/-- Tensoring two finite-rank local trivializations gives their product rank. -/
theorem locallyFree_tensor {X : Scheme} {E F : OModule X} {r s : ℕ}
    (hE : IsLocallyFreeOfRank E r) (hF : IsLocallyFreeOfRank F s) :
    IsLocallyFreeOfRank (PhaseTwentyFive.tensorSheaf E F) (r * s) := by
  obtain ⟨q, hq, hr⟩ := hE
  obtain ⟨q', hq', hs⟩ := hF
  letI := hq
  letI := hq'
  let U : q.I × q'.I → X.Opens := fun i => q.X i.1 ⊓ q'.X i.2
  let eE (i : q.I × q'.I) :
      SheafOfModules.free (R := X.ringCatSheaf.over (U i)) (Fin r) ≅ E.over (U i) :=
    freeTrivializationRestrict (homOfLE inf_le_left) (localBasisTrivialization q hr i.1)
  let eF (i : q.I × q'.I) :
      SheafOfModules.free (R := X.ringCatSheaf.over (U i)) (Fin s) ≅ F.over (U i) :=
    freeTrivializationRestrict (homOfLE inf_le_right) (localBasisTrivialization q' hs i.2)
  let e (i : q.I × q'.I) :
      SheafOfModules.free (R := X.ringCatSheaf.over (U i)) (Fin (r * s)) ≅
        (PhaseTwentyFive.tensorSheaf E F).over (U i) :=
    freeReindexIso _ ((Equiv.sigmaEquivProd (Fin r) (Fin s)).trans finProdFinEquiv).symm ≪≫
      (freeTensorIso (X.sheaf.over (U i)) (Fin r) (Fin s)).symm ≪≫
      tensorIso (X.sheaf.over (U i)) (eE i) (eF i) ≪≫
      (tensorOverIso (U i) E F).symm
  let qT : SheafOfModules.LocalGeneratorsData.{0} (PhaseTwentyFive.tensorSheaf E F) :=
    { I := q.I × q'.I
      X := U
      coversTop := intersectCover q q'
      generators := fun i => (SheafOfModules.free.generatingSections
        (R := X.ringCatSheaf.over (U i)) (Fin (r * s))).ofEpi (e i).hom }
  refine ⟨qT, ?_, fun _ => ⟨Equiv.refl _⟩⟩
  constructor
  intro i
  change IsIso ((SheafOfModules.free.generatingSections (Fin (r * s))).ofEpi (e i).hom).π
  rw [SheafOfModules.GeneratingSections.ofEpi_π]
  infer_instance

end LeBrunSalamon.SheafTensor

namespace LeBrunSalamon.PhaseTwentyFive
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree

theorem tensorSheaf_locallyFree {X : Scheme} {E F : OModule X}
    {r s : ℕ} (hE : IsLocallyFreeOfRank E r)
    (hF : IsLocallyFreeOfRank F s) :
    IsLocallyFreeOfRank (tensorSheaf E F) (r * s) := SheafTensor.locallyFree_tensor hE hF

/-- Internal Hom is characterized by the tensor-Hom adjunction,
not by a choice of a bundle with the right numerical rank. -/
structure InternalHomPresentation {X : Scheme} (E F : OModule X) where
  object : OModule X
  evaluate : tensorSheaf object E ⟶ F
  universal : ∀ Z : OModule X,
    Function.Bijective (fun h : Z ⟶ object =>
      tensorMap h (𝟙 E) ≫ evaluate)

/-! Concrete comparison and functoriality for internal-Hom presentations. -/
section InternalHomFunctorLemmas
set_option backward.isDefEq.respectTransparency false

namespace InternalHomPresentation

variable {X : Scheme} {E F G Z W : OModule X}

/-- The actual evaluation map associated with a morphism into a representing sheaf. -/
def uncurry (H : InternalHomPresentation E F) (h : Z ⟶ H.object) :
    tensorSheaf Z E ⟶ F :=
  tensorMap h (𝟙 E) ≫ H.evaluate

/-- The representing bijection, retaining the specified evaluation. -/
def homEquiv (H : InternalHomPresentation E F) (Z : OModule X) :
    (Z ⟶ H.object) ≃ (tensorSheaf Z E ⟶ F) :=
  Equiv.ofBijective H.uncurry (H.universal Z)

def curry (H : InternalHomPresentation E F) (f : tensorSheaf Z E ⟶ F) :
    Z ⟶ H.object :=
  (H.homEquiv Z).symm f

@[simp] theorem uncurry_curry (H : InternalHomPresentation E F)
    (f : tensorSheaf Z E ⟶ F) : H.uncurry (H.curry f) = f :=
  (H.homEquiv Z).apply_symm_apply f

@[simp] theorem curry_uncurry (H : InternalHomPresentation E F)
    (h : Z ⟶ H.object) : H.curry (H.uncurry h) = h :=
  (H.homEquiv Z).symm_apply_apply h

theorem hom_ext (H : InternalHomPresentation E F) {f g : Z ⟶ H.object}
    (h : H.uncurry f = H.uncurry g) : f = g :=
  (H.universal Z).1 h

@[simp] theorem uncurry_id (H : InternalHomPresentation E F) :
    H.uncurry (𝟙 H.object) = H.evaluate := by
  simp [uncurry, tensorMap_id]

theorem uncurry_comp (H : InternalHomPresentation E F)
    (f : W ⟶ Z) (g : Z ⟶ H.object) :
    H.uncurry (f ≫ g) = tensorMap f (𝟙 E) ≫ H.uncurry g := by
  have h : tensorMap (f ≫ g) (𝟙 E) =
      tensorMap f (𝟙 E) ≫ tensorMap g (𝟙 E) := by
    simpa using tensorMap_comp f g (𝟙 E) (𝟙 E)
  simp only [uncurry, h, Category.assoc]

theorem curry_precompose (H : InternalHomPresentation E F)
    (f : W ⟶ Z) (g : tensorSheaf Z E ⟶ F) :
    H.curry (tensorMap f (𝟙 E) ≫ g) = f ≫ H.curry g := by
  apply H.hom_ext
  rw [uncurry_curry, uncurry_comp, uncurry_curry]

/-- The comparison between two actual representing objects. -/
def comparison (H K : InternalHomPresentation E F) : H.object ⟶ K.object :=
  K.curry H.evaluate

@[simp] theorem uncurry_comparison (H K : InternalHomPresentation E F) :
    K.uncurry (H.comparison K) = H.evaluate :=
  K.uncurry_curry H.evaluate

@[simp] theorem comparison_self (H : InternalHomPresentation E F) :
    H.comparison H = 𝟙 H.object := by
  apply H.hom_ext
  rw [uncurry_comparison, uncurry_id]

theorem comparison_comp (H K L : InternalHomPresentation E F) :
    H.comparison K ≫ K.comparison L = H.comparison L := by
  apply L.hom_ext
  rw [uncurry_comp, uncurry_comparison, uncurry_comparison]
  exact H.uncurry_comparison K

/-- Uniqueness of the internal Hom, compatible with its evaluation. -/
def uniqueIso (H K : InternalHomPresentation E F) : H.object ≅ K.object where
  hom := H.comparison K
  inv := K.comparison H
  hom_inv_id := by rw [comparison_comp, comparison_self]
  inv_hom_id := by rw [comparison_comp, comparison_self]

theorem uniqueIso_evaluate (H K : InternalHomPresentation E F) :
    tensorMap (H.uniqueIso K).hom (𝟙 E) ≫ K.evaluate = H.evaluate :=
  H.uncurry_comparison K

/-- Contravariance in the source and covariance in the target. -/
def map {E' F' : OModule X} (H : InternalHomPresentation E F)
    (K : InternalHomPresentation E' F') (f : E' ⟶ E) (g : F ⟶ F') :
    H.object ⟶ K.object :=
  K.curry (tensorMap (𝟙 H.object) f ≫ H.evaluate ≫ g)

@[simp] theorem uncurry_map {E' F' : OModule X}
    (H : InternalHomPresentation E F) (K : InternalHomPresentation E' F')
    (f : E' ⟶ E) (g : F ⟶ F') :
    K.uncurry (H.map K f g) = tensorMap (𝟙 H.object) f ≫ H.evaluate ≫ g :=
  K.uncurry_curry _

@[simp] theorem map_id (H : InternalHomPresentation E F) :
    H.map H (𝟙 E) (𝟙 F) = 𝟙 H.object := by
  apply H.hom_ext
  simp only [uncurry_map, tensorMap_id, Category.id_comp, Category.comp_id, uncurry_id]

theorem map_comp {E' F' E'' F'' : OModule X}
    (H : InternalHomPresentation E F) (K : InternalHomPresentation E' F')
    (L : InternalHomPresentation E'' F'')
    (f : E' ⟶ E) (g : F ⟶ F') (f' : E'' ⟶ E') (g' : F' ⟶ F'') :
    H.map K f g ≫ K.map L f' g' = H.map L (f' ≫ f) (g ≫ g') := by
  apply L.hom_ext
  rw [uncurry_comp, uncurry_map, uncurry_map]
  have interchange :
      tensorMap (H.map K f g) (𝟙 E'') ≫ tensorMap (𝟙 K.object) f' =
        tensorMap (𝟙 H.object) f' ≫ tensorMap (H.map K f g) (𝟙 E') := by
    rw [← tensorMap_comp, ← tensorMap_comp]
    simp
  rw [← Category.assoc, ← Category.assoc, interchange]
  simp only [Category.assoc]
  change tensorMap (𝟙 H.object) f' ≫ K.uncurry (H.map K f g) ≫ g' = _
  rw [uncurry_map]
  rw [← Category.assoc, ← Category.assoc, ← tensorMap_comp]
  simp

def mapIso {E' F' : OModule X}
    (H : InternalHomPresentation E F) (K : InternalHomPresentation E' F')
    (e : E ≅ E') (f : F ≅ F') : H.object ≅ K.object where
  hom := H.map K e.inv f.hom
  inv := K.map H e.hom f.inv
  hom_inv_id := by rw [map_comp]; simpa using H.map_id
  inv_hom_id := by rw [map_comp]; simpa using K.map_id

end InternalHomPresentation

/-- Tensoring on the right by a fixed actual module sheaf. -/
def tensorRightFunctor {X : Scheme} (E : OModule X) : OModule X ⥤ OModule X where
  obj Z := tensorSheaf Z E
  map f := tensorMap f (𝟙 E)
  map_id Z := tensorMap_id Z E
  map_comp f g := by simpa using tensorMap_comp f g (𝟙 E) (𝟙 E)

/-- The covariant Hom functor supplied by a family of actual presentations. -/
def internalHomFunctor {X : Scheme} {E : OModule X}
    (H : ∀ F : OModule X, InternalHomPresentation E F) : OModule X ⥤ OModule X where
  obj F := (H F).object
  map {F F'} g := (H F).map (H F') (𝟙 E) g
  map_id F := (H F).map_id
  map_comp {F F' F''} f g := by
    simpa using ((H F).map_comp (H F') (H F'') (𝟙 E) f (𝟙 E) g).symm

namespace InternalHomPresentation

variable {X : Scheme} {E F F' Z : OModule X}

theorem curry_postcompose (H : InternalHomPresentation E F)
    (K : InternalHomPresentation E F')
    (f : tensorSheaf Z E ⟶ F) (g : F ⟶ F') :
    K.curry (f ≫ g) = H.curry f ≫ H.map K (𝟙 E) g := by
  apply K.hom_ext
  rw [uncurry_curry, uncurry_comp, uncurry_map]
  simp only [tensorMap_id, Category.id_comp]
  rw [← Category.assoc]
  change f ≫ g = H.uncurry (H.curry f) ≫ g
  rw [uncurry_curry]

end InternalHomPresentation

/-- The genuine tensor-Hom adjunction, derived from evaluation and its universal property. -/
def tensorHomAdjunction {X : Scheme} {E : OModule X}
    (H : ∀ F : OModule X, InternalHomPresentation E F) :
    tensorRightFunctor E ⊣ internalHomFunctor H :=
  Adjunction.mkOfHomEquiv
    { homEquiv Z F := ((H F).homEquiv Z).symm
      homEquiv_naturality_left_symm := by
        intro Z' Z F f g
        exact (H F).uncurry_comp f g
      homEquiv_naturality_right := by
        intro Z F F' f g
        exact (H F).curry_postcompose (H F') f g }

/-- Tensor preserves colimits once its actual right adjoint has been constructed. -/
theorem tensorRight_preservesColimits {X : Scheme} {E : OModule X}
    (H : ∀ F : OModule X, InternalHomPresentation E F) :
    PreservesColimits (tensorRightFunctor E) := by
  letI := (tensorHomAdjunction H).isLeftAdjoint
  infer_instance

namespace TensorConstruction

variable {X : Scheme}

/-- A concrete right unit isomorphism, using the same pairing as tensorMap. -/
def rightUnitIso (E : OModule X) : tensorSheaf E (structureModule X) ≅ E :=
  commIso E (structureModule X) ≪≫ leftUnitIso E

theorem rightUnitIso_hom_pair (E : OModule X) (U : X.Opens)
    (e : SectionsOn E U) (a : RingSections X U) :
    (rightUnitIso E).hom.app U
      ((tensorPresentation E (structureModule X)).pair.apply U e a) = a • e := by
  change (leftUnitHom E).app U ((commHom E (structureModule X)).app U
    ((tensorPresentation E (structureModule X)).pair.apply U e a)) = _
  rw [commHom_pair, leftUnitHom_pair]

theorem rightUnitIso_hom_naturality {E F : OModule X} (f : E ⟶ F) :
    tensorMap f (𝟙 (structureModule X)) ≫ (rightUnitIso F).hom =
      (rightUnitIso E).hom ≫ f := by
  apply ((tensorPresentation E (structureModule X)).universal F).1
  apply sheafBilinearMap_ext
  intro U e a
  change (rightUnitIso F).hom.app U
      ((tensorMap f (𝟙 (structureModule X))).app U
        ((tensorPresentation E (structureModule X)).pair.apply U e a)) =
    f.app U ((rightUnitIso E).hom.app U
      ((tensorPresentation E (structureModule X)).pair.apply U e a))
  rw [tensorMap_apply, rightUnitIso_hom_pair, rightUnitIso_hom_pair]
  simp

theorem leftUnitIso_hom_naturality {E F : OModule X} (f : E ⟶ F) :
    tensorMap (𝟙 (structureModule X)) f ≫ (leftUnitIso F).hom =
      (leftUnitIso E).hom ≫ f := by
  apply ((tensorPresentation (structureModule X) E).universal F).1
  apply sheafBilinearMap_ext
  intro U a e
  change (leftUnitHom F).app U
      ((tensorMap (𝟙 (structureModule X)) f).app U
        ((tensorPresentation (structureModule X) E).pair.apply U a e)) =
    f.app U ((leftUnitHom E).app U
      ((tensorPresentation (structureModule X) E).pair.apply U a e))
  rw [tensorMap_apply, leftUnitHom_pair, leftUnitHom_pair]
  simp

end TensorConstruction

namespace InternalHomPresentation

variable {X : Scheme}

/-- Hom from the structure module is represented by the target sheaf itself. -/
def unitSource (F : OModule X) : InternalHomPresentation (structureModule X) F where
  object := F
  evaluate := (TensorConstruction.rightUnitIso F).hom
  universal Z := by
    have hf :
        (fun h : Z ⟶ F => tensorMap h (𝟙 (structureModule X)) ≫
          (TensorConstruction.rightUnitIso F).hom) =
        (fun h : Z ⟶ F => (TensorConstruction.rightUnitIso Z).hom ≫ h) :=
      funext TensorConstruction.rightUnitIso_hom_naturality
    rw [hf]
    constructor
    · intro f g h
      exact (cancel_epi _).mp h
    · intro g
      refine ⟨(TensorConstruction.rightUnitIso Z).inv ≫ g, ?_⟩
      simp

/-- An evaluation-compatible comparison with Hom(O,F), for any chosen presentation. -/
def unitSourceIso {F : OModule X}
    (H : InternalHomPresentation (structureModule X) F) : H.object ≅ F :=
  H.uniqueIso (unitSource F)

end InternalHomPresentation

variable {X : Scheme}

theorem tensorMap_commuting_square {A B C D : OModule X} (f : A ⟶ B) (g : C ⟶ D) :
    tensorMap f (𝟙 C) ≫ tensorMap (𝟙 B) g =
      tensorMap (𝟙 A) g ≫ tensorMap f (𝟙 D) := by
  rw [← tensorMap_comp, ← tensorMap_comp]
  simp

def tensorLeftFunctor (E : OModule X) : OModule X ⥤ OModule X where
  obj Z := tensorSheaf E Z
  map f := tensorMap (𝟙 E) f
  map_id Z := tensorMap_id E Z
  map_comp f g := by simpa using tensorMap_comp (𝟙 E) (𝟙 E) f g

def tensorCommNaturalIso (E : OModule X) : tensorLeftFunctor E ≅ tensorRightFunctor E :=
  NatIso.ofComponents (fun Z => TensorConstruction.commIso E Z) (by
    intro Z W f
    apply ((tensorPresentation E Z).universal _).1
    apply sheafBilinearMap_ext
    intro U e z
    change (TensorConstruction.commHom E W).app U
        ((tensorMap (𝟙 E) f).app U ((tensorPresentation E Z).pair.apply U e z)) =
      (tensorMap f (𝟙 E)).app U
        ((TensorConstruction.commHom E Z).app U ((tensorPresentation E Z).pair.apply U e z))
    rw [tensorMap_apply, TensorConstruction.commHom_pair,
      TensorConstruction.commHom_pair, tensorMap_apply])

theorem tensorLeft_preservesColimits {E : OModule X}
    (H : ∀ F : OModule X, InternalHomPresentation E F) :
    PreservesColimits (tensorLeftFunctor E) := by
  letI := tensorRight_preservesColimits H
  exact preservesColimits_of_natIso (tensorCommNaturalIso E).symm

namespace InternalHomPresentation

variable (H : ∀ E F : OModule X, InternalHomPresentation E F)
variable {I : Type} (E : I → OModule X)

/-- The actual tensor images of a coproduct cocone form a colimit. -/
def tensorCoproductIsColimit (Z : OModule X) :
    IsColimit (Cofan.mk (tensorSheaf Z (∐ E))
      (fun i => tensorMap (𝟙 Z) (Sigma.ι E i))) := by
  letI := tensorLeft_preservesColimits (H Z)
  exact isColimitOfHasCoproductOfPreservesColimit (tensorLeftFunctor Z) E

def tensorCoproductDesc {Z F : OModule X}
    (f : ∀ i, tensorSheaf Z (E i) ⟶ F) : tensorSheaf Z (∐ E) ⟶ F :=
  Cofan.IsColimit.desc (tensorCoproductIsColimit H E Z) f

@[reassoc (attr := simp)] theorem tensorCoproduct_ι_desc {Z F : OModule X}
    (f : ∀ i, tensorSheaf Z (E i) ⟶ F) (i : I) :
    tensorMap (𝟙 Z) (Sigma.ι E i) ≫ tensorCoproductDesc H E f = f i :=
  (tensorCoproductIsColimit H E Z).fac (Cofan.mk F f) (Discrete.mk i)

include H in
theorem tensorCoproduct_hom_ext {Z F : OModule X}
    {f g : tensorSheaf Z (∐ E) ⟶ F}
    (h : ∀ i, tensorMap (𝟙 Z) (Sigma.ι E i) ≫ f =
      tensorMap (𝟙 Z) (Sigma.ι E i) ≫ g) : f = g :=
  Cofan.IsColimit.hom_ext (tensorCoproductIsColimit H E Z) f g h

def coproductObject (F : OModule X) : OModule X :=
  ∏ᶜ (fun i => (H (E i) F).object)

def coproductEvaluate (F : OModule X) : tensorSheaf (coproductObject H E F) (∐ E) ⟶ F :=
  tensorCoproductDesc H E
    (fun i => (H (E i) F).uncurry (Pi.π (fun i => (H (E i) F).object) i))

def coproductCurry {Z F : OModule X} (f : tensorSheaf Z (∐ E) ⟶ F) :
    Z ⟶ coproductObject H E F :=
  Pi.lift (fun i => (H (E i) F).curry (tensorMap (𝟙 Z) (Sigma.ι E i) ≫ f))

@[reassoc (attr := simp)] theorem coproductCurry_π {Z F : OModule X}
    (f : tensorSheaf Z (∐ E) ⟶ F) (i : I) :
    coproductCurry H E f ≫ Pi.π (fun i => (H (E i) F).object) i =
      (H (E i) F).curry (tensorMap (𝟙 Z) (Sigma.ι E i) ≫ f) :=
  Pi.lift_comp_π _ _

@[reassoc] theorem coproductEvaluate_ι (F : OModule X) (i : I) :
    tensorMap (𝟙 (coproductObject H E F)) (Sigma.ι E i) ≫ coproductEvaluate H E F =
      (H (E i) F).uncurry (Pi.π (fun i => (H (E i) F).object) i) :=
  tensorCoproduct_ι_desc H E _ i

theorem coproductEvaluate_naturality_component {Z F : OModule X}
    (h : Z ⟶ coproductObject H E F) (i : I) :
    tensorMap (𝟙 Z) (Sigma.ι E i) ≫ tensorMap h (𝟙 (∐ E)) ≫
        coproductEvaluate H E F =
      (H (E i) F).uncurry (h ≫ Pi.π (fun i => (H (E i) F).object) i) := by
  rw [← Category.assoc, ← tensorMap_commuting_square, Category.assoc,
    coproductEvaluate_ι, ← uncurry_comp]

theorem coproduct_uncurry_curry {Z F : OModule X} (f : tensorSheaf Z (∐ E) ⟶ F) :
    tensorMap (coproductCurry H E f) (𝟙 (∐ E)) ≫ coproductEvaluate H E F = f := by
  apply tensorCoproduct_hom_ext H E
  intro i
  rw [coproductEvaluate_naturality_component, coproductCurry_π, uncurry_curry]

theorem coproduct_curry_uncurry {Z F : OModule X}
    (h : Z ⟶ coproductObject H E F) :
    coproductCurry H E (tensorMap h (𝟙 (∐ E)) ≫ coproductEvaluate H E F) = h := by
  apply Pi.hom_ext
  intro i
  rw [coproductCurry_π, coproductEvaluate_naturality_component, curry_uncurry]

/-- Hom from an actual coproduct is represented by the product of the Hom sheaves. -/
def sourceCoproduct (F : OModule X) : InternalHomPresentation (∐ E) F where
  object := coproductObject H E F
  evaluate := coproductEvaluate H E F
  universal Z := by
    constructor
    · intro f g h
      have h' := congrArg (coproductCurry H E) h
      simpa only [coproduct_curry_uncurry] using h'
    · intro f
      exact ⟨coproductCurry H E f, coproduct_uncurry_curry H E f⟩

def sourceCoproductIso (F : OModule X)
    (K : InternalHomPresentation (∐ E) F) :
    K.object ≅ ∏ᶜ (fun i => (H (E i) F).object) :=
  K.uniqueIso (sourceCoproduct H E F)

/-- The Hom sheaf of a free source is the product of copies of its target. -/
def freeSourceIso (F : OModule X) (I : Type)
    (K : InternalHomPresentation (SheafOfModules.free (R := X.ringCatSheaf) I) F) :
    K.object ≅ ∏ᶜ (fun _ : I => F) :=
  sourceCoproductIso H (fun _ : I => structureModule X) F K ≪≫
    Pi.mapIso (fun _ => (H (structureModule X) F).unitSourceIso)

/-- A finite free source and free target give an actual free Hom sheaf. -/
def freeHomIso (I J : Type) [Finite I]
    (K : InternalHomPresentation
      (SheafOfModules.free (R := X.ringCatSheaf) I)
      (SheafOfModules.free (R := X.ringCatSheaf) J)) :
    K.object ≅ SheafOfModules.free (R := X.ringCatSheaf) (Σ _ : I, J) := by
  letI : HasBiproduct (fun _ : I => SheafOfModules.free (R := X.ringCatSheaf) J) :=
    HasBiproduct.of_hasProduct _
  exact freeSourceIso H (SheafOfModules.free J) I K ≪≫
    biproductIso (fun _ : I => SheafOfModules.free (R := X.ringCatSheaf) J) ≪≫
    sigmaSigmaIso (fun _ : I => J) (fun _ _ => structureModule X)

/-- In particular, duality preserves the chosen finite free rank. -/
def freeDualIso (I : Type) [Finite I]
    (K : InternalHomPresentation
      (SheafOfModules.free (R := X.ringCatSheaf) I) (structureModule X)) :
    K.object ≅ SheafOfModules.free (R := X.ringCatSheaf) I := by
  letI : HasBiproduct (fun _ : I => structureModule X) :=
    HasBiproduct.of_hasProduct _
  exact freeSourceIso H (structureModule X) I K ≪≫
    biproductIso (fun _ : I => structureModule X)

def finiteFreeHomIso (r s : ℕ)
    (K : InternalHomPresentation
      (SheafOfModules.free (R := X.ringCatSheaf) (Fin r))
      (SheafOfModules.free (R := X.ringCatSheaf) (Fin s))) :
    K.object ≅ SheafOfModules.free (R := X.ringCatSheaf) (Fin (r*s)) :=
  freeHomIso H (Fin r) (Fin s) K ≪≫
    (SheafOfModules.freeFunctor (R := X.ringCatSheaf)).mapIso
      (((Equiv.sigmaEquivProd (Fin r) (Fin s)).trans finProdFinEquiv).toIso)

/-- The rank calculation is transported through the specified free trivializations. -/
def isoOfFreeTrivializations {E F : OModule X} (K : InternalHomPresentation E F)
    {r s : ℕ} (e : E ≅ SheafOfModules.free (R := X.ringCatSheaf) (Fin r))
    (f : F ≅ SheafOfModules.free (R := X.ringCatSheaf) (Fin s)) :
    K.object ≅ SheafOfModules.free (R := X.ringCatSheaf) (Fin (r*s)) :=
  K.mapIso (H _ _) e f ≪≫ finiteFreeHomIso H r s (H _ _)

end InternalHomPresentation

namespace HomConstruction

open Opposite

set_option backward.isDefEq.respectTransparency false

abbrev restricted {X : Scheme} (E : OModule X) (U : X.Opens) :=
  (PresheafOfModules.pushforward₀ (Over.forget U) X.ringCatSheaf.obj).obj E.val

abbrev Section {X : Scheme} (E F : OModule X) (U : X.Opens) :=
  restricted E U ⟶ restricted F U

abbrev forgetSection {X : Scheme} {E F : OModule X} {U : X.Opens}
    (φ : Section E F U) : (presheafHom E.presheaf F.presheaf).obj (op U) :=
  (PresheafOfModules.toPresheaf _).map φ

theorem forgetSection_injective {X : Scheme} (E F : OModule X) (U : X.Opens) :
    Function.Injective (forgetSection (E := E) (F := F) (U := U)) :=
  (PresheafOfModules.toPresheaf _).map_injective

def smulSection {X : Scheme} {E F : OModule X} {U : X.Opens}
    (r : RingSections X U) (φ : Section E F U) : Section E F U where
  app V := ModuleCat.ofHom ((X.presheaf.map V.unop.hom.op r) •
    (show SectionsOn E V.unop.left →ₗ[RingSections X V.unop.left] SectionsOn F V.unop.left
      from (φ.app V).hom))
  naturality := by
    intro V W i
    ext e
    change X.presheaf.map W.unop.hom.op r • φ.app W (E.val.map i.unop.left.op e) =
      F.val.map i.unop.left.op (X.presheaf.map V.unop.hom.op r • φ.app V e)
    have hφ := PresheafOfModules.naturality_apply φ i e
    change φ.app W (E.val.map i.unop.left.op e) =
      F.val.map i.unop.left.op (φ.app V e) at hφ
    rw [F.val.map_smul, hφ]
    congr 1
    change X.presheaf.map W.unop.hom.op r =
      (X.presheaf.map V.unop.hom.op ≫ X.presheaf.map i.unop.left.op) r
    rw [← X.presheaf.map_comp]
    congr 3

instance sectionSMul {X : Scheme} (E F : OModule X) (U : X.Opens) :
    SMul (RingSections X U) (Section E F U) := ⟨smulSection⟩

@[simp] theorem section_smul_app {X : Scheme} {E F : OModule X} {U : X.Opens}
    (r : RingSections X U) (φ : Section E F U) (V : (Over U)ᵒᵖ)
    (e : E.val.obj (op V.unop.left)) :
    (r • φ).app V e = X.presheaf.map V.unop.hom.op r • φ.app V e := rfl

instance sectionModule {X : Scheme} (E F : OModule X) (U : X.Opens) :
    Module (RingSections X U) (Section E F U) where
  one_smul φ := by
    ext V e
    change X.presheaf.map V.unop.hom.op 1 • φ.app V e = φ.app V e
    simp
  mul_smul a b φ := by
    ext V e
    change X.presheaf.map V.unop.hom.op (a*b) • φ.app V e =
      X.presheaf.map V.unop.hom.op a • (X.presheaf.map V.unop.hom.op b • φ.app V e)
    simp only [map_mul, mul_smul]
  smul_zero a := by
    ext V e
    change X.presheaf.map V.unop.hom.op a • (0 : SectionsOn F V.unop.left) = 0
    simp
  smul_add a φ ψ := by
    ext V e
    change X.presheaf.map V.unop.hom.op a • (φ.app V e + ψ.app V e) =
      X.presheaf.map V.unop.hom.op a • φ.app V e + X.presheaf.map V.unop.hom.op a • ψ.app V e
    exact smul_add _ _ _
  add_smul a b φ := by
    ext V e
    change X.presheaf.map V.unop.hom.op (a+b) • φ.app V e =
      X.presheaf.map V.unop.hom.op a • φ.app V e + X.presheaf.map V.unop.hom.op b • φ.app V e
    simp only [map_add, add_smul]
  zero_smul φ := by
    ext V e
    change X.presheaf.map V.unop.hom.op 0 • φ.app V e = 0
    simp

end HomConstruction

namespace HomConstruction

open Opposite

set_option backward.isDefEq.respectTransparency false

abbrev IsLinear {X : Scheme} {E F : OModule X} {U : X.Opens}
    (φ : (presheafHom E.presheaf F.presheaf).obj (op U)) : Prop :=
  ∀ (V : (Over U)ᵒᵖ) (r : RingSections X V.unop.left) (e : SectionsOn E V.unop.left),
    φ.app V (r • e) =
      @SMul.smul (RingSections X V.unop.left) (SectionsOn F V.unop.left) inferInstance r (φ.app V e)

def ofLinear {X : Scheme} {E F : OModule X} {U : X.Opens}
    (φ : (presheafHom E.presheaf F.presheaf).obj (op U)) (hφ : IsLinear φ) :
    Section E F U := PresheafOfModules.homMk φ hφ

@[simp] theorem forgetSection_ofLinear {X : Scheme} {E F : OModule X} {U : X.Opens}
    (φ : (presheafHom E.presheaf F.presheaf).obj (op U)) (hφ : IsLinear φ) :
    forgetSection (ofLinear φ hφ) = φ := rfl

theorem forgetSection_isLinear {X : Scheme} {E F : OModule X} {U : X.Opens}
    (φ : Section E F U) : IsLinear (forgetSection φ) := by
  intro V r e
  exact (φ.app V).hom.map_smul r e

def restrictSection {X : Scheme} {E F : OModule X} {U V : X.Opens}
    (i : V ⟶ U) (φ : Section E F U) : Section E F V :=
  ofLinear ((presheafHom E.presheaf F.presheaf).map i.op (forgetSection φ))
    (by intro W r e; exact (φ.app (op ((Over.map i).obj W.unop))).hom.map_smul r e)

@[simp] theorem restrictSection_app {X : Scheme} {E F : OModule X} {U V : X.Opens}
    (i : V ⟶ U) (φ : Section E F U) (W : (Over V)ᵒᵖ) :
    (restrictSection i φ).app W = φ.app (op ((Over.map i).obj W.unop)) := rfl

@[simp] theorem forgetSection_restrict {X : Scheme} {E F : OModule X} {U V : X.Opens}
    (i : V ⟶ U) (φ : Section E F U) :
    forgetSection (restrictSection i φ) =
      (presheafHom E.presheaf F.presheaf).map i.op (forgetSection φ) := rfl

@[simp] theorem restrictSection_id {X : Scheme} {E F : OModule X} {U : X.Opens}
    (φ : Section E F U) : restrictSection (𝟙 U) φ = φ := by
  apply forgetSection_injective
  rw [forgetSection_restrict, op_id, (presheafHom E.presheaf F.presheaf).map_id]
  rfl

@[simp] theorem restrictSection_comp {X : Scheme} {E F : OModule X} {U V W : X.Opens}
    (i : V ⟶ U) (j : W ⟶ V) (φ : Section E F U) :
    restrictSection (j ≫ i) φ = restrictSection j (restrictSection i φ) := by
  apply forgetSection_injective
  simp only [forgetSection_restrict, op_comp, CategoryTheory.Functor.map_comp]
  rfl

def restrictAddHom {X : Scheme} {E F : OModule X} {U V : X.Opens}
    (i : V ⟶ U) : Section E F U →+ Section E F V where
  toFun := restrictSection i
  map_zero' := by ext W e; rfl
  map_add' φ ψ := by ext W e; rfl

def additivePresheaf {X : Scheme} (E F : OModule X) : X.Opensᵒᵖ ⥤ AddCommGrpCat where
  obj U := AddCommGrpCat.of (Section E F U.unop)
  map i := AddCommGrpCat.ofHom (restrictAddHom i.unop)
  map_id U := ConcreteCategory.hom_ext _ _ (fun φ => restrictSection_id φ)
  map_comp i j := ConcreteCategory.hom_ext _ _ (fun φ => restrictSection_comp i.unop j.unop φ)

instance additivePresheafModule {X : Scheme} (E F : OModule X) (U : X.Opensᵒᵖ) :
    Module (X.ringCatSheaf.obj.obj U) ((additivePresheaf E F).obj U) :=
  sectionModule E F U.unop

theorem restrictSection_smul {X : Scheme} {E F : OModule X} {U V : X.Opens}
    (i : V ⟶ U) (r : RingSections X U) (φ : Section E F U) :
    restrictSection i (r • φ) = X.presheaf.map i.op r • restrictSection i φ := by
  ext W e
  change X.presheaf.map ((Over.map i).obj W.unop).hom.op r •
      (φ.app (op ((Over.map i).obj W.unop)) e : SectionsOn F W.unop.left) =
    X.presheaf.map W.unop.hom.op (X.presheaf.map i.op r) •
      (φ.app (op ((Over.map i).obj W.unop)) e : SectionsOn F W.unop.left)
  congr 1
  change X.presheaf.map (W.unop.hom ≫ i).op r = _
  rw [op_comp, X.presheaf.map_comp]
  rfl

def presheaf {X : Scheme} (E F : OModule X) : PresheafOfModules X.ringCatSheaf.obj :=
  PresheafOfModules.ofPresheaf (additivePresheaf E F)
    (by intro U V i r φ; exact restrictSection_smul i.unop r φ)

/-- The linearity predicate on local additive natural transformations. -/
def linearSubfunctor {X : Scheme} (E F : OModule X) :
    Subfunctor (presheafHom E.presheaf F.presheaf) where
  obj U := {φ | IsLinear φ}
  map i φ hφ W r e := hφ (op ((Over.map i.unop).obj W.unop)) r e

def sectionEquiv {X : Scheme} (E F : OModule X) (U : X.Opens) :
    Section E F U ≃ (linearSubfunctor E F).toFunctor.obj (op U) where
  toFun φ := ⟨forgetSection φ, forgetSection_isLinear φ⟩
  invFun φ := ofLinear φ.val φ.property
  left_inv φ := forgetSection_injective E F U rfl
  right_inv φ := Subtype.ext rfl

def underlyingIso {X : Scheme} (E F : OModule X) :
    (presheaf E F).presheaf ⋙ CategoryTheory.forget AddCommGrpCat ≅
      (linearSubfunctor E F).toFunctor :=
  NatIso.ofComponents (fun U => (sectionEquiv E F U.unop).toIso) (by intro U V i; rfl)

end HomConstruction

namespace HomConstruction

open Opposite

set_option backward.isDefEq.respectTransparency false

lemma linear_at_of_restrict {X : Scheme} {E F : OModule X} {U V : X.Opens}
    (φ : (presheafHom E.presheaf F.presheaf).obj (op U)) (i : V ⟶ U)
    (h : IsLinear ((presheafHom E.presheaf F.presheaf).map i.op φ))
    (r : RingSections X V) (e : SectionsOn E V) :
    φ.app (op (Over.mk i)) (r • e) =
      @SMul.smul (RingSections X V) (SectionsOn F V) inferInstance r
        (φ.app (op (Over.mk i)) e) := by
  have hmap := presheafHom_map_app_op_mk_id (F := E.presheaf) (G := F.presheaf) i φ
  have hleft := congrArg (fun f => f (r • e)) hmap
  have hright := congrArg (fun f =>
    @SMul.smul (RingSections X V) (SectionsOn F V) inferInstance r (f e)) hmap
  exact hleft.symm.trans ((h (op (Over.mk (𝟙 V))) r e).trans hright)

lemma linearSubfunctor_isSheaf {X : Scheme} (E F : OModule X) :
    Presieve.IsSheaf (Opens.grothendieckTopology X)
      (linearSubfunctor E F).toFunctor := by
  have hhom : Presieve.IsSheaf (Opens.grothendieckTopology X)
      (presheafHom E.presheaf F.presheaf) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp (F.isSheaf.hom E.presheaf)
  apply (Subfunctor.isSheaf_iff _ hhom).mpr
  intro U φ hcover V r e
  let S := (linearSubfunctor E F).sieveOfSection φ
  apply F.isSheaf.isSeparated _ (S.pullback V.unop.hom)
    ((Opens.grothendieckTopology X).pullback_stable V.unop.hom hcover)
  intro W g hg
  let f : Over.mk (g ≫ V.unop.hom) ⟶ V.unop := Over.homMk g
  have hn (z : SectionsOn E V.unop.left) :
      φ.app (op (Over.mk (g ≫ V.unop.hom))) (E.val.map g.op z) =
        F.val.map g.op (φ.app V z) := by
    exact congrArg (fun h => h z) (φ.naturality f.op)
  change F.val.map g.op (φ.app V (r • e)) =
    F.val.map g.op (@SMul.smul (RingSections X V.unop.left) (SectionsOn F V.unop.left)
      inferInstance r (φ.app V e))
  have he := E.val.map_smul g.op r e
  have hf := F.val.map_smul g.op r (φ.app V e)
  have hlocal := linear_at_of_restrict φ (g ≫ V.unop.hom) hg
    (X.presheaf.map g.op r) (E.val.map g.op e)
  exact (hn (r • e)).symm.trans
    ((congrArg (fun z => φ.app (op (Over.mk (g ≫ V.unop.hom))) z) he).trans
      (hlocal.trans ((congrArg (fun z : SectionsOn F W => X.presheaf.map g.op r • z)
        (hn e)).trans hf.symm)))

/-- The genuine internal-Hom sheaf: local sections are linear morphisms
between the restrictions of the two module sheaves. -/
def object {X : Scheme} (E F : OModule X) : OModule X where
  val := presheaf E F
  isSheaf := by
    apply Presheaf.isSheaf_of_isSheaf_comp (Opens.grothendieckTopology X)
      (s := CategoryTheory.forget AddCommGrpCat)
    apply (Presheaf.isSheaf_of_iso_iff (underlyingIso E F)).mpr
    exact (isSheaf_iff_isSheaf_of_type _ _).mpr (linearSubfunctor_isSheaf E F)


end HomConstruction

namespace HomConstruction

open Opposite

set_option backward.isDefEq.respectTransparency false

def evaluationAt {X : Scheme} (E F : OModule X) (U : X.Opens) :
    Section E F U →ₗ[RingSections X U]
      (SectionsOn E U →ₗ[RingSections X U] SectionsOn F U) where
  toFun φ := (φ.app (op (Over.mk (𝟙 U)))).hom
  map_add' φ ψ := rfl
  map_smul' r φ := by
    ext e
    change X.presheaf.map (𝟙 U).op r • φ.app (op (Over.mk (𝟙 U))) e =
      r • φ.app (op (Over.mk (𝟙 U))) e
    simp

lemma evaluationAt_restrict {X : Scheme} {E F : OModule X} {U V : X.Opens}
    (i : V ⟶ U) (φ : Section E F U) (e : SectionsOn E V) :
    evaluationAt E F V (HomConstruction.restrictSection i φ) e =
      φ.app (op (Over.mk i)) e := by
  exact congrArg (fun f => f e)
    (presheafHom_map_app_op_mk_id (F := E.presheaf) (G := F.presheaf) i (forgetSection φ))


def evaluatePair {X : Scheme} (E F : OModule X) :
    SheafBilinearMap (object E F) E F where
  apply U := evaluationAt E F U
  naturality := by
    intro U V i φ e
    change F.val.map i.op (φ.app (op (Over.mk (𝟙 V))) e) =
      (HomConstruction.restrictSection i φ).app (op (Over.mk (𝟙 U))) (E.val.map i.op e)
    have hh := PresheafOfModules.naturality_apply φ
      (Over.homMk i : Over.mk i ⟶ Over.mk (𝟙 V)).op e
    change φ.app (op (Over.mk i)) (E.val.map i.op e) =
      F.val.map i.op (φ.app (op (Over.mk (𝟙 V))) e) at hh
    exact hh.symm.trans (evaluationAt_restrict i φ (E.val.map i.op e)).symm

def localCurry {X : Scheme} {Z E F : OModule X} (b : SheafBilinearMap Z E F)
    (U : X.Opens) (z : SectionsOn Z U) : Section E F U where
  app V := ModuleCat.ofHom (b.apply V.unop.left (Z.val.map V.unop.hom.op z))
  naturality := by
    intro V W i
    ext e
    change b.apply W.unop.left (Z.val.map W.unop.hom.op z)
        (E.val.map i.unop.left.op e) =
      F.val.map i.unop.left.op (b.apply V.unop.left (Z.val.map V.unop.hom.op z) e)
    have hb := b.naturality i.unop.left (Z.val.map V.unop.hom.op z) e
    change F.val.map i.unop.left.op (b.apply V.unop.left (Z.val.map V.unop.hom.op z) e) =
      b.apply W.unop.left (Z.val.map i.unop.left.op (Z.val.map V.unop.hom.op z))
        (E.val.map i.unop.left.op e) at hb
    apply Eq.trans ?_ hb.symm
    congr 2
    exact (Z.val.congr_map_apply (show W.unop.hom.op =
      V.unop.hom.op ≫ i.unop.left.op from congrArg Quiver.Hom.op (Over.w i.unop).symm) z).trans
        (Z.val.map_comp_apply V.unop.hom.op i.unop.left.op z)

def curryBilinear {X : Scheme} {Z E F : OModule X} (b : SheafBilinearMap Z E F) :
    Z ⟶ object E F where
  val := PresheafOfModulesOfCommRing.homMk
    (fun U => ModuleCat.ofHom
      { toFun := localCurry b U.unop
        map_add' z z' := by
          change localCurry b U.unop (z+z') = localCurry b U.unop z + localCurry b U.unop z'
          ext V e
          change b.apply V.unop.left (Z.val.map V.unop.hom.op (z+z')) e =
            b.apply V.unop.left (Z.val.map V.unop.hom.op z) e +
              b.apply V.unop.left (Z.val.map V.unop.hom.op z') e
          simp
        map_smul' r z := by
          change localCurry b U.unop (r • z) = smulSection r (localCurry b U.unop z)
          ext V e
          change b.apply V.unop.left (Z.val.map V.unop.hom.op (r • z)) e =
            X.presheaf.map V.unop.hom.op r • b.apply V.unop.left (Z.val.map V.unop.hom.op z) e
          exact (congrArg (fun w : SectionsOn Z V.unop.left => b.apply V.unop.left w e)
            (Z.val.map_smul V.unop.hom.op r z)).trans
              (congrArg (fun f => f e) ((b.apply V.unop.left).map_smul
                (X.presheaf.map V.unop.hom.op r) (Z.val.map V.unop.hom.op z))) })
    (by
      intro U V i
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      change localCurry b V.unop (Z.val.map i z) =
        HomConstruction.restrictSection i.unop (localCurry b U.unop z)
      ext W e
      change b.apply W.unop.left
          (Z.val.map W.unop.hom.op (Z.val.map i z)) e =
        b.apply W.unop.left
          (Z.val.map ((Over.map i.unop).obj W.unop).hom.op z) e
      rw [← PresheafOfModules.map_comp_apply]
      rfl)

lemma evaluationAt_localCurry {X : Scheme} {Z E F : OModule X}
    (b : SheafBilinearMap Z E F) (U : X.Opens) (z : SectionsOn Z U) (e : SectionsOn E U) :
    evaluationAt E F U (localCurry b U z) e = b.apply U z e := by
  change b.apply U (Z.val.map (𝟙 U).op z) e = _
  simp

lemma curryBilinear_evaluate {X : Scheme} {Z E F : OModule X}
    (h : Z ⟶ object E F) :
    curryBilinear ((evaluatePair E F).precompose h (𝟙 E)) = h := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro e
  change evaluationAt E F V.unop.left (h.app V.unop.left (Z.val.map V.unop.hom.op z)) e =
    (h.app U.unop z).app V e
  have hn := PresheafOfModules.naturality_apply h.val V.unop.hom.op z
  change h.app V.unop.left (Z.val.map V.unop.hom.op z) =
    HomConstruction.restrictSection V.unop.hom (h.app U.unop z) at hn
  rw [hn, evaluationAt_restrict]
  congr 2

lemma evaluate_curryBilinear {X : Scheme} {Z E F : OModule X}
    (b : SheafBilinearMap Z E F) :
    (evaluatePair E F).precompose (curryBilinear b) (𝟙 E) = b := by
  apply sheafBilinearMap_ext
  intro U z e
  exact evaluationAt_localCurry b U z e

def bilinearEquiv {X : Scheme} (Z E F : OModule X) :
    (Z ⟶ object E F) ≃ SheafBilinearMap Z E F where
  toFun h := (evaluatePair E F).precompose h (𝟙 E)
  invFun := curryBilinear
  left_inv := curryBilinear_evaluate
  right_inv := evaluate_curryBilinear

def tensorHomEquiv {X : Scheme} (Z E F : OModule X) :
    (Z ⟶ object E F) ≃ (tensorSheaf Z E ⟶ F) :=
  (bilinearEquiv Z E F).trans
    (Equiv.ofBijective
      (fun h : tensorSheaf Z E ⟶ F => (tensorPresentation Z E).pair.postcompose h)
      ((tensorPresentation Z E).universal F)).symm

def presentation {X : Scheme} (E F : OModule X) : InternalHomPresentation E F where
  object := object E F
  evaluate := tensorLift (evaluatePair E F)
  universal Z := by
    have heq : (fun h : Z ⟶ object E F =>
        tensorMap h (𝟙 E) ≫ tensorLift (evaluatePair E F)) = tensorHomEquiv Z E F := by
      funext h
      apply ((tensorPresentation Z E).universal F).1
      change (tensorPresentation Z E).pair.postcompose
        (tensorMap h (𝟙 E) ≫ tensorLift (evaluatePair E F)) =
        (tensorPresentation Z E).pair.postcompose
          (tensorLift ((evaluatePair E F).precompose h (𝟙 E)))
      rw [tensorLift_pair]
      apply sheafBilinearMap_ext
      intro U z e
      change (tensorLift (evaluatePair E F)).app U
          ((tensorMap h (𝟙 E)).app U ((tensorPresentation Z E).pair.apply U z e)) = _
      rw [tensorMap_apply]
      exact congrArg (fun b : SheafBilinearMap (object E F) E F =>
        b.apply U (h.app U z) e) (tensorLift_pair (evaluatePair E F))
    rw [heq]
    exact (tensorHomEquiv Z E F).bijective

theorem internalHomPresentation_exists_proved {X : Scheme} (E F : OModule X) :
    Nonempty (InternalHomPresentation E F) := ⟨presentation E F⟩


end HomConstruction

namespace HomConstruction

open Opposite

set_option backward.isDefEq.respectTransparency false

def sectionOverEquiv {X : Scheme} (E F : OModule X) (U : X.Opens) :
    Section E F U ≃ (E.over U ⟶ F.over U) where
  toFun φ := ⟨φ⟩
  invFun φ :=
    { app V := φ.val.app V
      naturality := by
        intro V W i
        ext e
        exact PresheafOfModules.naturality_apply φ.val i e }
  left_inv φ := by ext V e; rfl
  right_inv φ := by ext V e; rfl

@[simp] theorem sectionOverEquiv_app {X : Scheme} (E F : OModule X) (U : X.Opens)
    (φ : SectionsOn (object E F) U) (V : (Over U)ᵒᵖ) :
    (sectionOverEquiv E F U φ).val.app V = φ.app V := rfl

theorem sectionOverEquiv_restrict {X : Scheme} (E F : OModule X) {U V : X.Opens}
    (i : V ⟶ U) (φ : Section E F U) :
    sectionOverEquiv E F V (HomConstruction.restrictSection i φ) =
      (SheafOfModules.overFunctorMap X.ringCatSheaf i).inv.app E ≫
        (SheafOfModules.overMap X.ringCatSheaf i).map (sectionOverEquiv E F U φ) ≫
          (SheafOfModules.overFunctorMap X.ringCatSheaf i).hom.app F := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  ext e
  rfl


end HomConstruction


end InternalHomFunctorLemmas

end LeBrunSalamon.PhaseTwentyFive

namespace LeBrunSalamon.SheafTensor
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwentyFive
set_option backward.isDefEq.respectTransparency false

section

abbrev tensorWithPresheaf {X : Scheme}
    (P : PresheafOfModules X.ringCatSheaf.obj) (E : OModule X) :=
  PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) P E.val

/-- Bilinear maps whose first argument is an arbitrary module presheaf.
The target and second argument are genuine module sheaves. -/
structure PresheafBilinearMap {X : Scheme}
    (P : PresheafOfModules X.ringCatSheaf.obj) (E F : OModule X) where
  apply : ∀ U : X.Opens, P.obj (op U) →ₗ[RingSections X U]
    (SectionsOn E U →ₗ[RingSections X U] SectionsOn F U)
  naturality : ∀ {U V : X.Opens} (i : U ⟶ V)
      (p : P.obj (op V)) (e : SectionsOn E V),
    F.presheaf.map i.op (apply V p e) =
      apply U (P.map i.op p) (E.presheaf.map i.op e)

theorem presheafBilinearMap_ext {X : Scheme}
    {P : PresheafOfModules X.ringCatSheaf.obj} {E F : OModule X}
    (b c : PresheafBilinearMap P E F)
    (h : ∀ U p e, b.apply U p e = c.apply U p e) : b = c := by
  cases b
  cases c
  congr 1
  funext U
  ext p e
  exact h U p e

def tensorHomToBilinear {X : Scheme}
    {P : PresheafOfModules X.ringCatSheaf.obj} {E F : OModule X}
    (h : tensorWithPresheaf P E ⟶ F.val) : PresheafBilinearMap P E F where
  apply U := TensorProduct.curry (h.app (op U)).hom
  naturality := by
    intro U V i p e
    exact (PresheafOfModules.naturality_apply h i.op
      (p ⊗ₜ[RingSections X V] e)).symm

def bilinearToTensorHom {X : Scheme}
    {P : PresheafOfModules X.ringCatSheaf.obj} {E F : OModule X}
    (b : PresheafBilinearMap P E F) : tensorWithPresheaf P E ⟶ F.val :=
  PresheafOfModulesOfCommRing.homMk
    (fun U => ModuleCat.ofHom (TensorProduct.lift (b.apply U.unop)))
    (fun i => ModuleCat.MonoidalCategory.tensor_ext (fun p e =>
      (b.naturality i.unop p e).symm))

def tensorBilinearEquiv {X : Scheme}
    (P : PresheafOfModules X.ringCatSheaf.obj) (E F : OModule X) :
    (tensorWithPresheaf P E ⟶ F.val) ≃ PresheafBilinearMap P E F where
  toFun := tensorHomToBilinear
  invFun := bilinearToTensorHom
  left_inv h := by
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro p e
    rfl
  right_inv b := by
    apply presheafBilinearMap_ext
    intro U p e
    rfl

namespace PresheafCurrying

open HomConstruction

def localCurry {X : Scheme}
    {P : PresheafOfModules X.ringCatSheaf.obj} {E F : OModule X}
    (b : PresheafBilinearMap P E F) (U : X.Opens) (p : P.obj (op U)) :
    Section E F U where
  app V := ModuleCat.ofHom (b.apply V.unop.left (P.map V.unop.hom.op p))
  naturality := by
    intro V W i
    ext e
    change b.apply W.unop.left (P.map W.unop.hom.op p)
        (E.val.map i.unop.left.op e) =
      F.val.map i.unop.left.op (b.apply V.unop.left (P.map V.unop.hom.op p) e)
    have hb := b.naturality i.unop.left (P.map V.unop.hom.op p) e
    change F.val.map i.unop.left.op (b.apply V.unop.left (P.map V.unop.hom.op p) e) =
      b.apply W.unop.left (P.map i.unop.left.op (P.map V.unop.hom.op p))
        (E.val.map i.unop.left.op e) at hb
    apply Eq.trans ?_ hb.symm
    congr 2
    exact (P.congr_map_apply (show W.unop.hom.op =
      V.unop.hom.op ≫ i.unop.left.op from congrArg Quiver.Hom.op (Over.w i.unop).symm) p).trans
        (P.map_comp_apply V.unop.hom.op i.unop.left.op p)

/-- Currying does not require the first argument to satisfy the sheaf condition. -/
def curryBilinear {X : Scheme}
    {P : PresheafOfModules X.ringCatSheaf.obj} {E F : OModule X}
    (b : PresheafBilinearMap P E F) : P ⟶ (object E F).val :=
  PresheafOfModulesOfCommRing.homMk
    (fun U => ModuleCat.ofHom
      { toFun := localCurry b U.unop
        map_add' p p' := by
          change localCurry b U.unop (p+p') = localCurry b U.unop p + localCurry b U.unop p'
          ext V e
          change b.apply V.unop.left (P.map V.unop.hom.op (p+p')) e =
            b.apply V.unop.left (P.map V.unop.hom.op p) e +
              b.apply V.unop.left (P.map V.unop.hom.op p') e
          simp
        map_smul' r p := by
          change localCurry b U.unop (r • p) = smulSection r (localCurry b U.unop p)
          ext V e
          change b.apply V.unop.left (P.map V.unop.hom.op (r • p)) e =
            X.presheaf.map V.unop.hom.op r • b.apply V.unop.left (P.map V.unop.hom.op p) e
          exact (congrArg (fun w : P.obj (op V.unop.left) => b.apply V.unop.left w e)
            (P.map_smul V.unop.hom.op r p)).trans
              (congrArg (fun f => f e) ((b.apply V.unop.left).map_smul
                (X.presheaf.map V.unop.hom.op r) (P.map V.unop.hom.op p))) })
    (by
      intro U V i
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro p
      change localCurry b V.unop (P.map i p) =
        HomConstruction.restrictSection i.unop (localCurry b U.unop p)
      ext W e
      change b.apply W.unop.left (P.map W.unop.hom.op (P.map i p)) e =
        b.apply W.unop.left (P.map ((Over.map i.unop).obj W.unop).hom.op p) e
      rw [← PresheafOfModules.map_comp_apply]
      rfl)

lemma evaluationAt_localCurry {X : Scheme}
    {P : PresheafOfModules X.ringCatSheaf.obj} {E F : OModule X}
    (b : PresheafBilinearMap P E F) (U : X.Opens)
    (p : P.obj (op U)) (e : SectionsOn E U) :
    evaluationAt E F U (localCurry b U p) e = b.apply U p e := by
  change b.apply U (P.map (𝟙 U).op p) e = _
  simp

def uncurryBilinear {X : Scheme}
    {P : PresheafOfModules X.ringCatSheaf.obj} {E F : OModule X}
    (h : P ⟶ (object E F).val) : PresheafBilinearMap P E F where
  apply U := (evaluationAt E F U).comp (h.app (op U)).hom
  naturality := by
    intro U V i p e
    change F.val.map i.op (evaluationAt E F V (h.app (op V) p) e) =
      evaluationAt E F U (h.app (op U) (P.map i.op p)) (E.val.map i.op e)
    have hn := PresheafOfModules.naturality_apply h i.op p
    change h.app (op U) (P.map i.op p) =
      HomConstruction.restrictSection i (h.app (op V) p) at hn
    rw [hn]
    exact (evaluatePair E F).naturality i (h.app (op V) p) e

lemma curry_uncurry {X : Scheme}
    {P : PresheafOfModules X.ringCatSheaf.obj} {E F : OModule X}
    (h : P ⟶ (object E F).val) : curryBilinear (uncurryBilinear h) = h := by
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro p
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro e
  change evaluationAt E F V.unop.left (h.app (op V.unop.left) (P.map V.unop.hom.op p)) e =
    (h.app U p).app V e
  have hn := PresheafOfModules.naturality_apply h V.unop.hom.op p
  change h.app (op V.unop.left) (P.map V.unop.hom.op p) =
    HomConstruction.restrictSection V.unop.hom (h.app U p) at hn
  rw [hn, evaluationAt_restrict]
  congr 2

lemma uncurry_curry {X : Scheme}
    {P : PresheafOfModules X.ringCatSheaf.obj} {E F : OModule X}
    (b : PresheafBilinearMap P E F) : uncurryBilinear (curryBilinear b) = b := by
  apply presheafBilinearMap_ext
  intro U p e
  exact evaluationAt_localCurry b U p e

def bilinearHomEquiv {X : Scheme}
    (P : PresheafOfModules X.ringCatSheaf.obj) (E F : OModule X) :
    PresheafBilinearMap P E F ≃ (P ⟶ (object E F).val) where
  toFun := curryBilinear
  invFun := uncurryBilinear
  left_inv := uncurry_curry
  right_inv := curry_uncurry

end PresheafCurrying

/-- The tensor-Hom equivalence before sheafification of its first argument. -/
def presheafTensorHomEquiv {X : Scheme}
    (P : PresheafOfModules X.ringCatSheaf.obj) (E F : OModule X) :
    (tensorWithPresheaf P E ⟶ F.val) ≃ (P ⟶ (HomConstruction.object E F).val) :=
  (tensorBilinearEquiv P E F).trans (PresheafCurrying.bilinearHomEquiv P E F)

lemma presheafTensorHomEquiv_precompose {X : Scheme}
    {P Q : PresheafOfModules X.ringCatSheaf.obj} {E F : OModule X}
    (f : P ⟶ Q) (h : tensorWithPresheaf Q E ⟶ F.val) :
    presheafTensorHomEquiv P E F
        (PresheafOfModulesOfCommRing.Monoidal.tensorHom f (𝟙 E.val) ≫ h) =
      f ≫ presheafTensorHomEquiv Q E F h := by
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro p
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro e
  change h.app (op V.unop.left)
      ((f.app (op V.unop.left) (P.map V.unop.hom.op p)) ⊗ₜ[RingSections X V.unop.left] e) =
    h.app (op V.unop.left)
      ((Q.map V.unop.hom.op (f.app U p)) ⊗ₜ[RingSections X V.unop.left] e)
  rw [PresheafOfModules.naturality_apply]

end
section

abbrev associatedSheaf {X : Scheme} (P : PresheafOfModules X.ringCatSheaf.obj) : OModule X :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P

/-- The natural map induced by sheafifying the first argument of a tensor product. -/
def tensorSheafificationHom {X : Scheme}
    (P : PresheafOfModules X.ringCatSheaf.obj) (E : OModule X) :
    associatedSheaf (tensorWithPresheaf P E) ⟶ tensorSheaf (associatedSheaf P) E :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
    (PresheafOfModulesOfCommRing.Monoidal.tensorHom
      ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P)
      (𝟙 E.val))

/-- The genuine Hom sheaf absorbs sheafification in a tensor argument. -/
def tensorSheafificationHomEquiv {X : Scheme}
    (P : PresheafOfModules X.ringCatSheaf.obj) (E F : OModule X) :
    (tensorSheaf (associatedSheaf P) E ⟶ F) ≃
      (associatedSheaf (tensorWithPresheaf P E) ⟶ F) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj)
    (P := tensorWithPresheaf (associatedSheaf P).val E) (F := F)).trans
    ((presheafTensorHomEquiv (associatedSheaf P).val E F).trans
      (((SheafOfModules.fullyFaithfulForget X.ringCatSheaf).homEquiv
        (X := associatedSheaf P) (Y := HomConstruction.object E F)).symm.trans
        ((PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj)
          (P := P) (F := HomConstruction.object E F)).trans
          ((presheafTensorHomEquiv P E F).symm.trans
            (PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj)
              (P := tensorWithPresheaf P E) (F := F)).symm))))

lemma tensorSheafificationHomEquiv_apply {X : Scheme}
    (P : PresheafOfModules X.ringCatSheaf.obj) (E F : OModule X)
    (h : tensorSheaf (associatedSheaf P) E ⟶ F) :
    tensorSheafificationHomEquiv P E F h = tensorSheafificationHom P E ≫ h := by
  apply (PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj)
    (P := tensorWithPresheaf P E) (F := F)).injective
  apply (presheafTensorHomEquiv P E F).injective
  dsimp only [tensorSheafificationHomEquiv, Equiv.trans_apply]
  erw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  change adj.homEquiv P (HomConstruction.object E F)
      ((SheafOfModules.fullyFaithfulForget X.ringCatSheaf).homEquiv.symm
        (presheafTensorHomEquiv (associatedSheaf P).val E F
          ((PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj)) h))) =
    presheafTensorHomEquiv P E F
      (adj.homEquiv (tensorWithPresheaf P E) F
        ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
          (PresheafOfModulesOfCommRing.Monoidal.tensorHom (adj.unit.app P) (𝟙 E.val)) ≫ h))
  let hp := (PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj)
    (P := tensorWithPresheaf (associatedSheaf P).val E) (F := F)) h
  have h₁ : adj.homEquiv P (HomConstruction.object E F)
      ((SheafOfModules.fullyFaithfulForget X.ringCatSheaf).homEquiv.symm
        (presheafTensorHomEquiv (associatedSheaf P).val E F hp)) =
      adj.unit.app P ≫ presheafTensorHomEquiv (associatedSheaf P).val E F hp := rfl
  have h₂ := presheafTensorHomEquiv_precompose (adj.unit.app P) hp
  have h₃ := adj.homEquiv_naturality_left
    (PresheafOfModulesOfCommRing.Monoidal.tensorHom (adj.unit.app P) (𝟙 E.val)) h
  exact h₁.trans (h₂.symm.trans (congrArg (presheafTensorHomEquiv P E F) h₃.symm))

instance tensorSheafificationHom_isIso {X : Scheme}
    (P : PresheafOfModules X.ringCatSheaf.obj) (E : OModule X) :
    IsIso (tensorSheafificationHom P E) := by
  apply isIso_of_coyoneda_map_bijective
  intro F
  have heq : (fun h => tensorSheafificationHom P E ≫ h) =
      tensorSheafificationHomEquiv P E F := by
    funext h
    exact (tensorSheafificationHomEquiv_apply P E F h).symm
  rw [heq]
  exact (tensorSheafificationHomEquiv P E F).bijective

/-- Inserting sheafification before tensoring does not change the resulting sheaf. -/
def tensorSheafificationIso {X : Scheme}
    (P : PresheafOfModules X.ringCatSheaf.obj) (E : OModule X) :
    associatedSheaf (tensorWithPresheaf P E) ≅ tensorSheaf (associatedSheaf P) E :=
  asIso (tensorSheafificationHom P E)

/-- Associativity of the actual sheafified tensor product. -/
def associativityIso {X : Scheme} (E F G : OModule X) :
    tensorSheaf (tensorSheaf E F) G ≅ tensorSheaf E (tensorSheaf F G) :=
  (tensorSheafificationIso (TensorConstruction.presheaf E F) G).symm ≪≫
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
      ((CategoryTheory.MonoidalCategory.associator
        (C := PresheafOfModulesOfCommRing X.presheaf) E.val F.val G.val) ≪≫
        (CategoryTheory.BraidedCategory.braiding
          (C := PresheafOfModulesOfCommRing X.presheaf) E.val
          (TensorConstruction.presheaf F G))) ≪≫
    tensorSheafificationIso (TensorConstruction.presheaf F G) E ≪≫
    TensorConstruction.commIso (tensorSheaf F G) E

end
section

def sheafificationUnit {X : Scheme} (P : PresheafOfModules X.ringCatSheaf.obj) :
    P ⟶ (associatedSheaf P).val :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P

lemma tensorPair_eq_unit {X : Scheme} (E F : OModule X) (U : X.Opens)
    (e : SectionsOn E U) (f : SectionsOn F U) :
    (tensorPresentation E F).pair.apply U e f =
      (sheafificationUnit (TensorConstruction.presheaf E F)).app (op U)
        (e ⊗ₜ[RingSections X U] f) := rfl

lemma sheafification_map_apply_unit {X : Scheme}
    {P Q : PresheafOfModules X.ringCatSheaf.obj} (f : P ⟶ Q)
    (U : X.Opens) (p : P.obj (op U)) :
    ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map f).val.app (op U)
      ((sheafificationUnit P).app (op U) p) =
      (sheafificationUnit Q).app (op U) (f.app (op U) p) := by
  have hn := (PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).unit.naturality f
  exact (congrArg (fun k : P ⟶ (associatedSheaf Q).val => k.app (op U) p) hn).symm

/-- The universal-pairing tensor map agrees with sheafification of the actual tensor map. -/
theorem tensorMap_eq_sheafificationMap {X : Scheme} {E F E' F' : OModule X}
    (f : E ⟶ E') (g : F ⟶ F') :
    tensorMap f g =
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
        (PresheafOfModulesOfCommRing.Monoidal.tensorHom f.val g.val) := by
  apply ((tensorPresentation E F).universal _).1
  apply sheafBilinearMap_ext
  intro U e z
  change (tensorMap f g).app U ((tensorPresentation E F).pair.apply U e z) = _
  erw [tensorMap_apply]
  change (tensorPresentation E' F').pair.apply U (f.app U e) (g.app U z) =
    ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (PresheafOfModulesOfCommRing.Monoidal.tensorHom f.val g.val)).val.app (op U)
        ((tensorPresentation E F).pair.apply U e z)
  erw [tensorPair_eq_unit, tensorPair_eq_unit, sheafification_map_apply_unit]
  rfl

lemma tensorSheafificationHom_pair {X : Scheme}
    (P : PresheafOfModules X.ringCatSheaf.obj) (E : OModule X)
    (U : X.Opens) (p : P.obj (op U)) (e : SectionsOn E U) :
    (tensorSheafificationHom P E).app U
      ((sheafificationUnit (tensorWithPresheaf P E)).app (op U)
        (p ⊗ₜ[RingSections X U] e)) =
      (tensorPresentation (associatedSheaf P) E).pair.apply U
        ((sheafificationUnit P).app (op U) p) e := by
  change ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (PresheafOfModulesOfCommRing.Monoidal.tensorHom (sheafificationUnit P) (𝟙 E.val))).val.app (op U)
      ((sheafificationUnit (tensorWithPresheaf P E)).app (op U)
        (p ⊗ₜ[RingSections X U] e)) = _
  erw [sheafification_map_apply_unit, tensorPair_eq_unit]

lemma tensorSheafificationIso_inv_pair {X : Scheme}
    (P : PresheafOfModules X.ringCatSheaf.obj) (E : OModule X)
    (U : X.Opens) (p : P.obj (op U)) (e : SectionsOn E U) :
    (tensorSheafificationIso P E).inv.app U
      ((tensorPresentation (associatedSheaf P) E).pair.apply U
        ((sheafificationUnit P).app (op U) p) e) =
      (sheafificationUnit (tensorWithPresheaf P E)).app (op U)
        (p ⊗ₜ[RingSections X U] e) := by
  erw [← tensorSheafificationHom_pair]
  exact congrArg (fun k : associatedSheaf (tensorWithPresheaf P E) ⟶
      associatedSheaf (tensorWithPresheaf P E) =>
      k.app U ((sheafificationUnit (tensorWithPresheaf P E)).app (op U)
        (p ⊗ₜ[RingSections X U] e))) (tensorSheafificationIso P E).hom_inv_id

/-- The associativity isomorphism has the expected action on the canonical local triple pairing. -/
theorem associativityIso_hom_pair {X : Scheme} (E F G : OModule X) (U : X.Opens)
    (e : SectionsOn E U) (f : SectionsOn F U) (g : SectionsOn G U) :
    (associativityIso E F G).hom.app U
      ((tensorPresentation (tensorSheaf E F) G).pair.apply U
        ((tensorPresentation E F).pair.apply U e f) g) =
      (tensorPresentation E (tensorSheaf F G)).pair.apply U e
        ((tensorPresentation F G).pair.apply U f g) := by
  let t := (CategoryTheory.MonoidalCategory.associator
    (C := PresheafOfModulesOfCommRing X.presheaf) E.val F.val G.val) ≪≫
      (CategoryTheory.BraidedCategory.braiding
        (C := PresheafOfModulesOfCommRing X.presheaf) E.val
        (TensorConstruction.presheaf F G))
  change (TensorConstruction.commHom (tensorSheaf F G) E).app U
      ((tensorSheafificationHom (TensorConstruction.presheaf F G) E).app U
        (((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map t.hom).val.app (op U)
          ((tensorSheafificationIso (TensorConstruction.presheaf E F) G).inv.app U
            ((tensorPresentation (associatedSheaf (TensorConstruction.presheaf E F)) G).pair.apply U
              ((sheafificationUnit (TensorConstruction.presheaf E F)).app (op U)
                (e ⊗ₜ[RingSections X U] f)) g)))) = _
  let cm := (TensorConstruction.commHom (tensorSheaf F G) E).app U
  let ab := (tensorSheafificationHom (TensorConstruction.presheaf F G) E).app U
  let mt := ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map t.hom).val.app (op U)
  exact (congrArg (fun z => cm (ab (mt z)))
    (tensorSheafificationIso_inv_pair (TensorConstruction.presheaf E F) G U
      (e ⊗ₜ[RingSections X U] f) g)).trans
    ((congrArg (fun z => cm (ab z))
      (sheafification_map_apply_unit t.hom U
        ((e ⊗ₜ[RingSections X U] f) ⊗ₜ[RingSections X U] g))).trans
      ((congrArg (fun z => cm z)
        (tensorSheafificationHom_pair (TensorConstruction.presheaf F G) E U
          (f ⊗ₜ[RingSections X U] g) e)).trans
        (TensorConstruction.commHom_pair (tensorSheaf F G) E U
          ((sheafificationUnit (TensorConstruction.presheaf F G)).app (op U)
            (f ⊗ₜ[RingSections X U] g)) e)))

end

end LeBrunSalamon.SheafTensor

namespace LeBrunSalamon.PhaseTwentyFive
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree

theorem tensorSheaf_assoc {X : Scheme} (E F G : OModule X) :
    Nonempty (tensorSheaf (tensorSheaf E F) G ≅
      tensorSheaf E (tensorSheaf F G)) := ⟨SheafTensor.associativityIso E F G⟩

theorem internalHomPresentation_exists {X : Scheme} (E F : OModule X) :
    Nonempty (InternalHomPresentation E F) := ⟨HomConstruction.presentation E F⟩

def internalHomPresentation {X : Scheme} (E F : OModule X) :
    InternalHomPresentation E F :=
  Classical.choice (internalHomPresentation_exists E F)

abbrev internalHomSheaf {X : Scheme} (E F : OModule X) : OModule X :=
  (internalHomPresentation E F).object

abbrev dualSheaf {X : Scheme} (E : OModule X) : OModule X :=
  internalHomSheaf E (structureModule X)

def currySheaf {X : Scheme} {Z E F : OModule X}
    (f : tensorSheaf Z E ⟶ F) : Z ⟶ internalHomSheaf E F :=
  (Equiv.ofBijective
    (fun h : Z ⟶ internalHomSheaf E F =>
      tensorMap h (𝟙 E) ≫ (internalHomPresentation E F).evaluate)
    ((internalHomPresentation E F).universal Z)).symm f

theorem currySheaf_evaluate {X : Scheme} {Z E F : OModule X}
    (f : tensorSheaf Z E ⟶ F) :
    tensorMap (currySheaf f) (𝟙 E) ≫
      (internalHomPresentation E F).evaluate = f := by
  exact (Equiv.ofBijective _ ((internalHomPresentation E F).universal Z)).apply_symm_apply f

end LeBrunSalamon.PhaseTwentyFive

namespace LeBrunSalamon.SheafModuleLocal
open CategoryTheory CategoryTheory.Limits Opposite
set_option backward.isDefEq.respectTransparency false

section

variable {C : Type} [Category C] {J : GrothendieckTopology C}
variable {R : Sheaf J RingCat} (M : SheafOfModules R) (U : C)

/-- A section on U determines its compatible family on the category of objects over U. -/
def sectionOver (s : M.val.obj (op U)) : (M.over U).sections where
  val V := M.val.map V.unop.hom.op s
  property := by
    intro V W i
    change M.val.map i.unop.left.op (M.val.map V.unop.hom.op s) =
      M.val.map W.unop.hom.op s
    have hi : V.unop.hom.op ≫ i.unop.left.op = W.unop.hom.op := by
      rw [← op_comp]
      exact congrArg Quiver.Hom.op (Over.w i.unop)
    rw [← PresheafOfModules.map_comp_apply, hi]

def sectionsOverEquiv : (M.over U).sections ≃ M.val.obj (op U) where
  toFun s := s.val (op (Over.mk (𝟙 U)))
  invFun := sectionOver M U
  left_inv s := by
    ext V
    let i : V.unop ⟶ Over.mk (𝟙 U) := Over.homMk V.unop.hom
    exact s.property i.op
  right_inv s := by
    change M.val.map (𝟙 U).op s = s
    simp

@[simp] theorem sectionsOverEquiv_apply (s : (M.over U).sections) :
    sectionsOverEquiv M U s = s.val (op (Over.mk (𝟙 U))) := rfl

@[simp] theorem sectionsOverEquiv_symm_val (s : M.val.obj (op U))
    (V : (Over U)ᵒᵖ) :
    ((sectionsOverEquiv M U).symm s).val V = M.val.map V.unop.hom.op s := rfl

theorem sectionsOverEquiv_naturality {N : SheafOfModules R} (f : M ⟶ N)
    (s : (M.over U).sections) :
    sectionsOverEquiv N U (SheafOfModules.sectionsMap (f.over U) s) =
      f.val.app (op U) (sectionsOverEquiv M U s) := rfl

/-- A morphism from the local unit is determined by its value on 1 at U. -/
def unitOverHomEquiv :
    (SheafOfModules.unit (R.over U) ⟶ M.over U) ≃ M.val.obj (op U) :=
  (M.over U).unitHomEquiv.trans (sectionsOverEquiv M U)

@[simp] theorem unitOverHomEquiv_apply
    (f : SheafOfModules.unit (R.over U) ⟶ M.over U) :
    unitOverHomEquiv M U f =
      f.val.app (op (Over.mk (𝟙 U))) (1 : R.obj.obj (op U)) := rfl

end
section

variable {C : Type} [Category.{0} C] [HasBinaryProducts C]
variable {J : GrothendieckTopology C} {R : Sheaf J RingCat}
variable [HasSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat]
variable [∀ U, HasSheafify (J.over U) AddCommGrpCat]
variable [∀ U, (J.over U).WEqualsLocallyBijective AddCommGrpCat]

instance overFunctor_isLeftAdjoint (U : C) :
    (SheafOfModules.overFunctor R U).IsLeftAdjoint :=
  (SheafOfModules.overPushforwardOverAdj (R := R) U).isLeftAdjoint

/-- Restricting a free sheaf preserves its specified generators. -/
def overFreeIso (I : Type) (U : C) :
    SheafOfModules.free (R := R.over U) I ≅ (SheafOfModules.free (R := R) I).over U :=
  SheafOfModules.mapFreeIso (SheafOfModules.overFunctor R U) I (Iso.refl _)

@[reassoc (attr := simp)] theorem ι_overFreeIso (I : Type) (U : C) (i : I) :
    SheafOfModules.ιFree (R := R.over U) i ≫ (overFreeIso (R := R) I U).hom =
      (SheafOfModules.overFunctor R U).map (SheafOfModules.ιFree (R := R) i) := by
  simpa [overFreeIso] using
    SheafOfModules.ιFree_mapFreeIso_hom (SheafOfModules.overFunctor R U) I (Iso.refl _) i

/-- Morphisms from a restricted free sheaf are determined by the images of its basis. -/
def freeOverHomEquiv (F : SheafOfModules R) (I : Type) (U : C) :
    ((SheafOfModules.free (R := R) I).over U ⟶ F.over U) ≃
      (I → F.val.obj (op U)) :=
  (Iso.homCongr (overFreeIso (R := R) I U).symm (Iso.refl (F.over U))).trans
    ((F.over U).freeHomEquiv.trans
      (Equiv.piCongrRight (fun _ : I => sectionsOverEquiv F U)))

theorem freeOverHomEquiv_apply (F : SheafOfModules R) (I : Type) (U : C)
    (f : (SheafOfModules.free (R := R) I).over U ⟶ F.over U) (i : I) :
    freeOverHomEquiv F I U f i =
      f.val.app (op (Over.mk (𝟙 U))) ((SheafOfModules.freeSection (R := R) i).val (op U)) := by
  change (SheafOfModules.ιFree (R := R.over U) i ≫
    (overFreeIso (R := R) I U).hom ≫ f).val.app (op (Over.mk (𝟙 U)))
      (1 : R.obj.obj (op U)) = _
  rw [← Category.assoc, ι_overFreeIso]
  rfl

end

end LeBrunSalamon.SheafModuleLocal

end

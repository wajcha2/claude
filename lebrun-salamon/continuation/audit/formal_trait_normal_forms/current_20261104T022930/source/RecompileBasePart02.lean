import RecompileBasePart01

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
# Phase 10 -- diagonal-symbol, jet, and infinitesimal-symmetry statements

The central geometric implication in the proposed algebraic proof is

  symmetric two-point kernel with contact quadratic symbol
    -> first-jet generation of L
    -> spanning by global contact Hamiltonian vector fields.

The first arrow still requires the canonical external tensor square `L ⊠ L`, and an intrinsic comparison
of its quadratic diagonal symbol with `θ²`. We do not fabricate this missing comparison. The SECOND arrow
is now packaged as an explicit, checkable compatibility diagram and an ordinary Lean theorem statement.
-/

namespace LeBrunSalamon.PhaseTen

open CategoryTheory
open AlgebraicGeometry
open LeBrunSalamon.PhaseOne
open LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseFour
open LeBrunSalamon.PhaseSeven
open LeBrunSalamon.PhaseEight

section AffineDiagonal

variable (A : Type*) [CommRing A] [Algebra ℂ A]

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct
open LeBrunSalamon.PhaseThree LeBrunSalamon.PhaseSeven

namespace AffineDiagonalProof

theorem zero_of_eq_neg {M : Type*} [AddCommGroup M] [Module ℂ M]
    (x : M) (h : x = -x) : x = 0 := by
  have hadd : x + x = 0 := by
    calc
      x + x = x + (-x) := congrArg (fun y : M => x + y) h
      _ = 0 := add_neg_cancel x
  have htwo : (2 : ℂ) • x = 0 := by
    simpa only [two_smul] using hadd
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

variable (A : Type*) [CommRing A] [Algebra ℂ A]

theorem diagonalMultiplication_tmul (a b : A) :
    affineDiagonalMultiplication A (a ⊗ₜ[ℂ] b) = a * b := by
  simp [affineDiagonalMultiplication, smul_eq_mul]

theorem diagonalMultiplication_swap (u : AffineTwoPointRing A) :
    affineDiagonalMultiplication A ((TensorProduct.comm ℂ A A) u) =
      affineDiagonalMultiplication A u := by
  refine TensorProduct.inductionOn u ?_ ?_
  · intro a b
    simp only [TensorProduct.comm_tmul, diagonalMultiplication_tmul, mul_comm]
  · intro x y hx hy
    simp only [map_add, hx, hy]

theorem tensorSwap_mul (u v : AffineTwoPointRing A) :
    (TensorProduct.comm ℂ A A) (u * v) =
      (TensorProduct.comm ℂ A A) u * (TensorProduct.comm ℂ A A) v := by
  exact (Algebra.TensorProduct.comm ℂ A A).map_mul u v

theorem affineQuadratic_implies_diagonalVanishing
    (u : AffineTwoPointRing A)
    (h : AffineVanishesQuadratically A u) :
    AffineVanishesToOrder A u 1 := by
  exact (Ideal.pow_le_pow_right (I := affineDiagonalIdeal A) (by decide : 1 ≤ 2)) h

theorem affineDiagonalVanishes_mono
    (u : AffineTwoPointRing A) {m n : ℕ}
    (hmn : m ≤ n) (h : AffineVanishesToOrder A u n) :
    AffineVanishesToOrder A u m := by
  exact (Ideal.pow_le_pow_right (I := affineDiagonalIdeal A) hmn) h

theorem affineSwap_preservesDiagonalOrder
    (u : AffineTwoPointRing A) (k : ℕ)
    (h : AffineVanishesToOrder A u k) :
    AffineVanishesToOrder A ((TensorProduct.comm ℂ A A) u) k := by
  let f : AffineTwoPointRing A →+* AffineTwoPointRing A :=
    (Algebra.TensorProduct.comm ℂ A A).toAlgHom.toRingHom
  have hI : affineDiagonalIdeal A ≤ (affineDiagonalIdeal A).comap f := by
    intro v hv
    change affineDiagonalMultiplication A ((TensorProduct.comm ℂ A A) v) = 0
    change affineDiagonalMultiplication A v = 0 at hv
    rw [diagonalMultiplication_swap]
    exact hv
  have hpow : (affineDiagonalIdeal A) ^ k ≤
      ((affineDiagonalIdeal A) ^ k).comap f :=
    (Ideal.pow_right_mono hI k).trans
      (Ideal.le_comap_pow (f := f) (K := affineDiagonalIdeal A) k)
  change f u ∈ (affineDiagonalIdeal A) ^ k
  exact hpow h

theorem affineSymmetric_and_antisymmetric_eq_zero
    (u : AffineTwoPointRing A)
    (hs : IsSymmetricAffineTwoPointFunction A u)
    (ha : IsAntisymmetricAffineTwoPointFunction A u) :
    u = 0 := by
  exact zero_of_eq_neg u (hs.symm.trans ha)

theorem affineDiagonalSymbol_equivalence_trans
    {u v w : AffineTwoPointRing A} {k : ℕ}
    (huv : HaveSameAffineDiagonalSymbol A u v k)
    (hvw : HaveSameAffineDiagonalSymbol A v w k) :
    HaveSameAffineDiagonalSymbol A u w k := by
  refine ⟨huv.1, hvw.2.1, ?_⟩
  have he : u - w = (u - v) + (v - w) := by ring
  rw [he]
  exact (affineDiagonalIdeal A ^ (k + 1)).add_mem huv.2.2 hvw.2.2

end AffineDiagonalProof

end

/-- Restriction to the diagonal is weaker than quadratic vanishing.
At the ring level this is `I_Δ² ⊆ I_Δ`. -/
theorem affineQuadratic_implies_diagonalVanishing
    (u : AffineTwoPointRing A)
    (h : AffineVanishesQuadratically A u) :
    AffineVanishesToOrder A u 1 := by
  exact LeBrunSalamon.PhaseTen.AffineDiagonalProof.affineQuadratic_implies_diagonalVanishing (A := A) (u := u) (h := h)

/-- Vanishing is monotone in the order: `I^n ⊆ I^m` for `m ≤ n`. -/
theorem affineDiagonalVanishes_mono
    (u : AffineTwoPointRing A) {m n : ℕ}
    (hmn : m ≤ n) (h : AffineVanishesToOrder A u n) :
    AffineVanishesToOrder A u m := by
  exact LeBrunSalamon.PhaseTen.AffineDiagonalProof.affineDiagonalVanishes_mono (A := A) (u := u) (m := m) (n := n) (hmn := hmn) (h := h)

/-- The ideal of the diagonal, and hence every power, is preserved by interchanging the two factors. -/
theorem affineSwap_preservesDiagonalOrder
    (u : AffineTwoPointRing A) (k : ℕ)
    (h : AffineVanishesToOrder A u k) :
    AffineVanishesToOrder A ((TensorProduct.comm ℂ A A) u) k := by
  exact LeBrunSalamon.PhaseTen.AffineDiagonalProof.affineSwap_preservesDiagonalOrder (A := A) (u := u) (k := k) (h := h)

/-- In characteristic zero a two-point function cannot be both
symmetric and antisymmetric unless it vanishes identically. -/
theorem affineSymmetric_and_antisymmetric_eq_zero
    (u : AffineTwoPointRing A)
    (hs : IsSymmetricAffineTwoPointFunction A u)
    (ha : IsAntisymmetricAffineTwoPointFunction A u) :
    u = 0 := by
  exact LeBrunSalamon.PhaseTen.AffineDiagonalProof.affineSymmetric_and_antisymmetric_eq_zero (A := A) (u := u) (hs := hs) (ha := ha)

/-- Congruence modulo the next power of `I_Δ` is an equivalence relation
among functions already vanishing to a fixed order. -/
theorem affineDiagonalSymbol_equivalence_trans
    {u v w : AffineTwoPointRing A} {k : ℕ}
    (huv : HaveSameAffineDiagonalSymbol A u v k)
    (hvw : HaveSameAffineDiagonalSymbol A v w k) :
    HaveSameAffineDiagonalSymbol A u w k := by
  exact LeBrunSalamon.PhaseTen.AffineDiagonalProof.affineDiagonalSymbol_equivalence_trans (A := A) (u := u) (v := v) (w := w) (k := k) (huv := huv) (hvw := hvw)

end AffineDiagonal

/- The exact LeBrunSalamon.PhaseTen.separatesFirstJets_implies_globallyGenerated declaration is relocated below its dependencies at the module end. -/


/-! ## 10C. Precise Hamiltonian-jet compatibility -/

/-- The fibre of the supplied tangent sheaf at a C-valued point, expressed through mathlib's honest
pullback of the O_X-module. The source is kept as `x*O_X`; its canonical identification with O_C is not
assumed definitionally. -/
abbrev TangentEvaluationAt
    (n : ℕ) (X : ContactCandidate n)
    (x : ComplexPoint X.variety) :=
  ((Scheme.Modules.pullback x.map).obj
      (SheafOfModules.unit X.variety.scheme.ringCatSheaf) ⟶
    (Scheme.Modules.pullback x.map).obj X.tangent.sheaf)

/-- The first-jet fibre of the contact-line candidate at a complex
point, represented as sections over Spec(O_X/m_x²). -/
abbrev ContactLineFirstJetAt
    (n : ℕ) (X : ContactCandidate n)
    (x : ComplexPoint X.variety) :=
  ((Scheme.Modules.pullback (pointPowerInclusion x 2)).obj
      (SheafOfModules.unit X.variety.scheme.ringCatSheaf) ⟶
    (Scheme.Modules.pullback (pointPowerInclusion x 2)).obj
      X.contactSequence.line.sheaf)

/-- A *certificate* that the value of a contact Hamiltonian vector
field at a point is determined by its first jet, with the resulting
map from first jets onto the tangent fibre.

In the intended contact manifold this map is induced by the canonical
contact Hamiltonian correspondence and the perfect Levi pairing.
Those ingredients are NOT YET CONSTRUCTED globally in Phases 1--8.
Consequently this is explicit geometric data, not a claim that every
`ContactCandidate` automatically possesses it. -/
structure HamiltonianFirstJetCompatibility
    (n : ℕ) (X : ContactCandidate n) where
  /-- A chosen global-field lift of every contact-line section. -/
  fieldOfSection :
    AlgebraicSection X.contactSequence.line.sheaf → GlobalVectorField n X
  /-- Its Hamiltonian really is the original section. -/
  hamiltonian_rightInverse :
    ∀ h, globalHamiltonian n X (fieldOfSection h) = h
  /-- Evaluation is induced by the first jet of the Hamiltonian. -/
  jetToTangent :
    ∀ x : ComplexPoint X.variety,
      ContactLineFirstJetAt n X x → TangentEvaluationAt n X x
  /-- The contact Levi isomorphism makes this map surjective.
      It has a one-dimensional kernel at a smooth contact point. -/
  jetToTangent_surjective :
    ∀ x : ComplexPoint X.variety, Function.Surjective (jetToTangent x)
  /-- The global and first-jet evaluations commute. -/
  commutes : ∀ (x : ComplexPoint X.variety)
      (h : AlgebraicSection X.contactSequence.line.sheaf),
    jetToTangent x
        (jetRestrictionAt x X.contactSequence.line.sheaf 1 h) =
      restrictSection x.map (fieldOfSection h)

/-- The image of the specified global Hamiltonian lifting map. This is not called a set of contact-
preserving fields until the intrinsic contact-vector-field property has been constructed and proved. -/
def HamiltonianFirstJetCompatibility.liftedHamiltonianFields
    {n : ℕ} {X : ContactCandidate n}
    (J : HamiltonianFirstJetCompatibility n X) :
    Set (GlobalVectorField n X) :=
  Set.range J.fieldOfSection

/-- Once first-jet separation and the *precise* evaluation diagram are
available, global Hamiltonian fields span all tangent fibres.

This is the algebraic formal target of the jet-to-homogeneity step;
its hypotheses are deliberately stronger than merely knowing the
abstract surjectivity of H⁰(T_X) → H⁰(L). -/
theorem firstJets_and_Hamiltonians_span
    {n : ℕ} (X : ContactCandidate n)
    (J : HamiltonianFirstJetCompatibility n X)
    (hjet : SeparatesFirstJets X.variety X.contactSequence.line) :
    SpecifiedGlobalFieldsSpanEverywhere n X J.liftedHamiltonianFields := by
  intro x v
  obtain ⟨j, hj⟩ := J.jetToTangent_surjective x v
  obtain ⟨s, hs⟩ := hjet x j
  refine ⟨J.fieldOfSection s, ⟨s, rfl⟩, ?_⟩
  calc
    restrictSection x.map (J.fieldOfSection s) =
        J.jetToTangent x
          (jetRestrictionAt x X.contactSequence.line.sheaf 1 s) :=
      (J.commutes x s).symm
    _ = J.jetToTangent x j := by rw [hs]
    _ = v := hj

/-- The corresponding package for a projective contact-*candidate*. This is intentionally not called
`ContactFanoManifold`: intrinsic tangent identification, global Levi nondegeneracy and ampleness are still
needed before the classification theorem can be stated unconditionally. -/
structure JetGeneratedProjectiveContactCandidate (n : ℕ) where
  geometry : ProjectiveContactCandidate n
  firstJets :
    SeparatesFirstJets geometry.contact.variety
      geometry.contact.contactSequence.line
  compatibility : HamiltonianFirstJetCompatibility n geometry.contact

/-- An immediate formal consequence of the package, independent of
whether the full contact Fano classification has been formalized. -/
theorem JetGeneratedProjectiveContactCandidate.globalFieldsSpan
    {n : ℕ} (X : JetGeneratedProjectiveContactCandidate n) :
    SpecifiedGlobalFieldsSpanEverywhere n X.geometry.contact
      X.compatibility.liftedHamiltonianFields := by
  exact firstJets_and_Hamiltonians_span X.geometry.contact
    X.compatibility X.firstJets

end LeBrunSalamon.PhaseTen

/-!
# Phase 11 -- affine contact calculus and the Reeb/Hamiltonian identities

This phase develops a genuine local algebraic calculus from the affine contact form already defined in
Phase 1. In particular the Cartan differential and Lie derivative are EXPRESSIONS IN DERIVATIONS, not new
primitives, and all Reeb or Hamiltonian uniqueness/existence statements carry the actual perfect Levi and
surjectivity hypotheses.

The statements with `sorry` are deliberately unproved. They do not provide any global contact-Fano
existence theorem. The contact-Hamiltonian correspondence itself was introduced as an unproved theorem in
Phase 9.
-/

namespace LeBrunSalamon.PhaseEleven

open LeBrunSalamon.PhaseOne
open LeBrunSalamon.PhaseFour
open LeBrunSalamon.PhaseNine

variable {A : Type*} [CommRing A] [Algebra ℂ A]

/-! ## 11A. Algebraic exterior differential and Lie derivative -/

/-- Cartan's algebraic formula for the exterior differential of a trivialized contact form, evaluated on
two genuine `ℂ`-derivations: `dθ(V,W) = V(θ(W)) - W(θ(V)) - θ([V,W])`. It does not presuppose an exterior-
power sheaf. -/
def affineExteriorDerivativeValue
    (θ : AffineOneForm A) (V W : AffineVectorFields A) : A :=
  V (θ W) - W (θ V) - θ ⁅V, W⁆

/-- Lie derivative of a one-form along an affine vector field, evaluated
on a second vector field: `(L_V θ)(W) = V(θ(W)) - θ([V,W])`. -/
def affineLieDerivativeValue
    (θ : AffineOneForm A) (V W : AffineVectorFields A) : A :=
  V (θ W) - θ ⁅V, W⁆

noncomputable section
set_option autoImplicit false
open LeBrunSalamon.PhaseOne
open LeBrunSalamon.PhaseFour
open LeBrunSalamon.PhaseNine
variable {A : Type*} [CommRing A] [Algebra ℂ A]

namespace AffineCartanProofCandidate

/-- Multiplication of a derivation by a function has the actual Leibniz correction. -/
theorem derivation_bracket_smul_left (a : A) (V W : AffineVectorFields A) :
    ⁅a • V, W⁆ = a • ⁅V, W⁆ - W a • V := by
  apply Derivation.ext
  intro x
  change a * V (W x) - W (a * V x) =
    a * (V (W x) - W (V x)) - W a * V x
  rw [Derivation.leibniz]
  simp only [smul_eq_mul]
  ring

/-- The corresponding Leibniz formula in the second argument. -/
theorem derivation_bracket_smul_right (a : A) (V W : AffineVectorFields A) :
    ⁅V, a • W⁆ = V a • W + a • ⁅V, W⁆ := by
  apply Derivation.ext
  intro x
  change V (a * W x) - a * W (V x) =
    V a * W x + a * (V (W x) - W (V x))
  rw [Derivation.leibniz]
  simp only [smul_eq_mul]
  ring

theorem affineCartanFormula_proved
    (θ : AffineOneForm A) (V W : AffineVectorFields A) :
    affineLieDerivativeValue θ V W =
      affineExteriorDerivativeValue θ V W + W (θ V) := by
  unfold affineLieDerivativeValue affineExteriorDerivativeValue
  ring

theorem affineExteriorDerivative_self_proved
    (θ : AffineOneForm A) (V : AffineVectorFields A) :
    affineExteriorDerivativeValue θ V V = 0 := by
  unfold affineExteriorDerivativeValue
  rw [lie_self, map_zero, sub_self, sub_zero]

theorem affineExteriorDerivative_skew_proved
    (θ : AffineOneForm A) (V W : AffineVectorFields A) :
    affineExteriorDerivativeValue θ V W =
      -affineExteriorDerivativeValue θ W V := by
  unfold affineExteriorDerivativeValue
  rw [← lie_skew V W, map_neg]
  ring

theorem affineExteriorDerivative_smul_left_proved
    (θ : AffineOneForm A) (a : A)
    (V W : AffineVectorFields A) :
    affineExteriorDerivativeValue θ (a • V) W =
      a * affineExteriorDerivativeValue θ V W := by
  change a * V (θ W) - W (θ (a • V)) - θ ⁅a • V, W⁆ =
    a * (V (θ W) - W (θ V) - θ ⁅V, W⁆)
  rw [derivation_bracket_smul_left]
  simp only [map_sub, map_smul, smul_eq_mul, Derivation.leibniz]
  ring

theorem affineExteriorDerivative_smul_right_proved
    (θ : AffineOneForm A) (a : A)
    (V W : AffineVectorFields A) :
    affineExteriorDerivativeValue θ V (a • W) =
      a * affineExteriorDerivativeValue θ V W := by
  change V (θ (a • W)) - a * W (θ V) - θ ⁅V, a • W⁆ =
    a * (V (θ W) - W (θ V) - θ ⁅V, W⁆)
  rw [derivation_bracket_smul_right]
  simp only [map_add, map_smul, smul_eq_mul, Derivation.leibniz]
  ring

theorem affineLevi_eq_negativeExteriorDerivative_proved
    (θ : AffineOneForm A)
    (V W : AffineDistribution θ) :
    affineLeviValue θ V W =
      -affineExteriorDerivativeValue θ V.1 W.1 := by
  have hV : θ V.1 = 0 := V.2
  have hW : θ W.1 = 0 := W.2
  simp only [affineLeviValue, affineExteriorDerivativeValue, hV, hW,
    map_zero, sub_self, zero_sub, neg_neg]

end AffineCartanProofCandidate

end

/-- The algebraic Cartan formula `L_V θ = ι_V dθ + d(θ(V))`, expressed pointwise on a test derivation. -/
theorem affineCartanFormula
    (θ : AffineOneForm A) (V W : AffineVectorFields A) :
    affineLieDerivativeValue θ V W =
      affineExteriorDerivativeValue θ V W + W (θ V) := by
  exact LeBrunSalamon.PhaseEleven.AffineCartanProofCandidate.affineCartanFormula_proved (A := A) (θ := θ) (V := V) (W := W)

/-- Alternation of the exterior derivative of a one-form. -/
theorem affineExteriorDerivative_self
    (θ : AffineOneForm A) (V : AffineVectorFields A) :
    affineExteriorDerivativeValue θ V V = 0 := by
  exact LeBrunSalamon.PhaseEleven.AffineCartanProofCandidate.affineExteriorDerivative_self_proved (A := A) (θ := θ) (V := V)

/-- Skew symmetry of the exterior differential. -/
theorem affineExteriorDerivative_skew
    (θ : AffineOneForm A) (V W : AffineVectorFields A) :
    affineExteriorDerivativeValue θ V W =
      -affineExteriorDerivativeValue θ W V := by
  exact LeBrunSalamon.PhaseEleven.AffineCartanProofCandidate.affineExteriorDerivative_skew_proved (A := A) (θ := θ) (V := V) (W := W)

/-- `dθ` is linear over the FUNCTION RING in its first argument,
although the three individual terms in Cartan's formula are not. -/
theorem affineExteriorDerivative_smul_left
    (θ : AffineOneForm A) (a : A)
    (V W : AffineVectorFields A) :
    affineExteriorDerivativeValue θ (a • V) W =
      a * affineExteriorDerivativeValue θ V W := by
  exact LeBrunSalamon.PhaseEleven.AffineCartanProofCandidate.affineExteriorDerivative_smul_left_proved (A := A) (θ := θ) (a := a) (V := V) (W := W)

/-- `dθ` is A-linear in its second argument. -/
theorem affineExteriorDerivative_smul_right
    (θ : AffineOneForm A) (a : A)
    (V W : AffineVectorFields A) :
    affineExteriorDerivativeValue θ V (a • W) =
      a * affineExteriorDerivativeValue θ V W := by
  exact LeBrunSalamon.PhaseEleven.AffineCartanProofCandidate.affineExteriorDerivative_smul_right_proved (A := A) (θ := θ) (a := a) (V := V) (W := W)

/-- On the hyperplane `ker θ`, the affine Levi form from Phase 1 is `-dθ`. The sign is important when
comparing with the global contact Levi form and contact-Hamiltonian conventions. -/
theorem affineLevi_eq_negativeExteriorDerivative
    (θ : AffineOneForm A)
    (V W : AffineDistribution θ) :
    affineLeviValue θ V W =
      -affineExteriorDerivativeValue θ V.1 W.1 := by
  exact LeBrunSalamon.PhaseEleven.AffineCartanProofCandidate.affineLevi_eq_negativeExteriorDerivative_proved (A := A) (θ := θ) (V := V) (W := W)

/-! ## 11B. Contact-preserving and strict contact vector fields -/

/-- A vector field preserves the trivialized one-form *strictly* when its Lie derivative vanishes
identically. This is stronger than preserving the CONTACT DISTRIBUTION. -/
def IsStrictAffineContactVectorField
    (θ : AffineOneForm A) (V : AffineVectorFields A) : Prop :=
  ∀ W : AffineVectorFields A, affineLieDerivativeValue θ V W = 0

/-- A vector field preserves the contact distribution conformally: `L_V θ = a θ` for a global regular
function `a`. The multiplier is necessarily unique when `θ` is onto `A`. -/
def IsConformalAffineContactVectorField
    (θ : AffineOneForm A) (V : AffineVectorFields A) : Prop :=
  ∃ a : A, ∀ W : AffineVectorFields A,
    affineLieDerivativeValue θ V W = a * θ W

noncomputable section
set_option autoImplicit false
open LeBrunSalamon.PhaseOne
open LeBrunSalamon.PhaseFour
open LeBrunSalamon.PhaseNine
variable {A : Type*} [CommRing A] [Algebra ℂ A]

namespace AffineCartanProofCandidate

theorem strictAffineContact_implies_contact_proved
    (θ : AffineOneForm A) (V : AffineVectorFields A)
    (hV : IsStrictAffineContactVectorField θ V) :
    IsAffineContactVectorField θ V := by
  intro W
  have hW : θ W.1 = 0 := W.2
  have h := hV W.1
  change V (θ W.1) - θ ⁅V, W.1⁆ = 0 at h
  rw [hW, map_zero, zero_sub] at h
  exact neg_eq_zero.mp h

end AffineCartanProofCandidate

end

/-- Strict contact transformations preserve the contact distribution. -/
theorem strictAffineContact_implies_contact
    (θ : AffineOneForm A) (V : AffineVectorFields A)
    (hV : IsStrictAffineContactVectorField θ V) :
    IsAffineContactVectorField θ V := by
  exact LeBrunSalamon.PhaseEleven.AffineCartanProofCandidate.strictAffineContact_implies_contact_proved (A := A) (θ := θ) (V := V) (hV := hV)

noncomputable section
set_option autoImplicit false
open LeBrunSalamon.PhaseOne
open LeBrunSalamon.PhaseFour
open LeBrunSalamon.PhaseNine
variable {A : Type*} [CommRing A] [Algebra ℂ A]

namespace AffineReebProofCandidate

theorem derivation_bracket_smul_right (a : A) (V W : AffineVectorFields A) :
    ⁅V, a • W⁆ = V a • W + a • ⁅V, W⁆ := by
  apply Derivation.ext
  intro x
  change V (a * W x) - a * W (V x) =
    V a * W x + a * (V (W x) - W (V x))
  rw [Derivation.leibniz]
  simp only [smul_eq_mul]
  ring

/-- The two derivation terms cancel, giving linearity in the test field. -/
def affineLieDerivativeLinear (θ : AffineOneForm A) (V : AffineVectorFields A) :
    AffineVectorFields A →ₗ[A] A where
  toFun W := affineLieDerivativeValue θ V W
  map_add' W Z := by
    change V (θ (W + Z)) - θ ⁅V, W + Z⁆ =
      (V (θ W) - θ ⁅V, W⁆) + (V (θ Z) - θ ⁅V, Z⁆)
    simp only [map_add, lie_add]
    ring
  map_smul' a W := by
    change V (θ (a • W)) - θ ⁅V, a • W⁆ =
      a * (V (θ W) - θ ⁅V, W⁆)
    rw [derivation_bracket_smul_right]
    simp only [map_add, map_smul, smul_eq_mul, Derivation.leibniz]
    ring

theorem conformalContact_iff_preservesDistribution_proved
    (θ : AffineOneForm A) (V : AffineVectorFields A)
    (honto : Function.Surjective θ) :
    IsConformalAffineContactVectorField θ V ↔
      IsAffineContactVectorField θ V := by
  constructor
  · rintro ⟨a, ha⟩ u
    have hu : θ u.1 = 0 := u.2
    have h := ha u.1
    change V (θ u.1) - θ ⁅V, u.1⁆ = a * θ u.1 at h
    rw [hu, map_zero, zero_sub, mul_zero] at h
    exact neg_eq_zero.mp h
  · intro hV
    obtain ⟨E, hE⟩ := honto 1
    refine ⟨affineLieDerivativeValue θ V E, ?_⟩
    intro W
    let u : AffineDistribution θ := ⟨W - θ W • E, by
      change θ (W - θ W • E) = 0
      rw [map_sub, map_smul, hE]
      simp only [smul_eq_mul, mul_one, sub_self]⟩
    have hzero : affineLieDerivativeLinear θ V u.1 = 0 := by
      have hu : θ u.1 = 0 := u.2
      change V (θ u.1) - θ ⁅V, u.1⁆ = 0
      rw [hu, map_zero, hV u, sub_self]
    change affineLieDerivativeLinear θ V (W - θ W • E) = 0 at hzero
    rw [map_sub, map_smul, smul_eq_mul] at hzero
    have hfactor : affineLieDerivativeValue θ V W =
        θ W * affineLieDerivativeValue θ V E := sub_eq_zero.mp hzero
    exact hfactor.trans (mul_comm _ _)

theorem conformalContact_multiplier_unique_proved
    (θ : AffineOneForm A)
    (honto : Function.Surjective θ)
    (V : AffineVectorFields A) (a b : A)
    (ha : ∀ W : AffineVectorFields A,
      affineLieDerivativeValue θ V W = a * θ W)
    (hb : ∀ W : AffineVectorFields A,
      affineLieDerivativeValue θ V W = b * θ W) :
    a = b := by
  obtain ⟨E, hE⟩ := honto 1
  have h := (ha E).symm.trans (hb E)
  simpa only [hE, mul_one] using h

end AffineReebProofCandidate

end

/-- For a surjective one-form, preservation of `ker θ` is equivalent to preserving θ up to multiplication
by a function. The statement does NOT require choosing a global Reeb field. -/
theorem conformalContact_iff_preservesDistribution
    (θ : AffineOneForm A) (V : AffineVectorFields A)
    (honto : Function.Surjective θ) :
    IsConformalAffineContactVectorField θ V ↔
      IsAffineContactVectorField θ V := by
  exact LeBrunSalamon.PhaseEleven.AffineReebProofCandidate.conformalContact_iff_preservesDistribution_proved (A := A) (θ := θ) (V := V) (honto := honto)

/-- The conformal multiplier, if it exists, is unique for surjective θ. -/
theorem conformalContact_multiplier_unique
    (θ : AffineOneForm A)
    (honto : Function.Surjective θ)
    (V : AffineVectorFields A) (a b : A)
    (ha : ∀ W : AffineVectorFields A,
      affineLieDerivativeValue θ V W = a * θ W)
    (hb : ∀ W : AffineVectorFields A,
      affineLieDerivativeValue θ V W = b * θ W) :
    a = b := by
  exact LeBrunSalamon.PhaseEleven.AffineReebProofCandidate.conformalContact_multiplier_unique_proved (A := A) (θ := θ) (honto := honto) (V := V) (a := a) (b := b) (ha := ha) (hb := hb)

/-! ## 11C. The algebraic Reeb vector field -/

/-- A Reeb field for a trivialized affine contact form has `θ(R)=1` and `ι_R dθ=0`. The
existence/uniqueness theorem needs surjectivity and nondegeneracy of the contact Levi form. -/
def IsAffineReebField
    (θ : AffineOneForm A) (R : AffineVectorFields A) : Prop :=
  θ R = 1 ∧
    ∀ W : AffineVectorFields A,
      affineExteriorDerivativeValue θ R W = 0

/-- For an affine one-form, the existence of a Reeb derivation is an
actual proposition, not a definition that secretly provides a field. -/
def HasAffineReebField (θ : AffineOneForm A) : Prop :=
  ∃ R : AffineVectorFields A, IsAffineReebField θ R

/-- On a genuine affine contact chart, the Hamiltonian vector field corresponding to the constant function
1 is a concrete candidate Reeb field, constructed from the Phase 9 Hamiltonian equivalence. -/
noncomputable def reebFromContactHamiltonian
    (θ : AffineOneForm A) (hθ : IsAffineContactForm θ) :
    AffineVectorFields A :=
  ((contactHamiltonianEquiv θ hθ).symm 1).1

noncomputable section
set_option autoImplicit false
open LeBrunSalamon.PhaseOne
open LeBrunSalamon.PhaseFour
open LeBrunSalamon.PhaseNine
variable {A : Type*} [CommRing A] [Algebra ℂ A]

namespace AffineReebProofCandidate

/-- This helper belongs after the original Reeb predicate in any insertion. -/
theorem affineReeb_bracket_value
    (θ : AffineOneForm A) (R : AffineVectorFields A)
    (hR : IsAffineReebField θ R) (W : AffineVectorFields A) :
    θ ⁅R, W⁆ = R (θ W) := by
  have h := hR.2 W
  change R (θ W) - W (θ R) - θ ⁅R, W⁆ = 0 at h
  rw [hR.1, Derivation.map_one_eq_zero, sub_zero] at h
  exact (sub_eq_zero.mp h).symm

theorem reebFromContactHamiltonian_isReeb_proved
    (θ : AffineOneForm A) (hθ : IsAffineContactForm θ) :
    IsAffineReebField θ (reebFromContactHamiltonian θ hθ) := by
  let R : AffineVectorFields A := reebFromContactHamiltonian θ hθ
  have hvalue : θ R = 1 := by
    change (contactHamiltonianEquiv θ hθ)
      ((contactHamiltonianEquiv θ hθ).symm 1) = 1
    exact (contactHamiltonianEquiv θ hθ).apply_symm_apply 1
  have hpres : IsAffineContactVectorField θ R :=
    ((contactHamiltonianEquiv θ hθ).symm 1).2
  obtain ⟨a, ha⟩ :=
    (conformalContact_iff_preservesDistribution_proved θ R hθ.1).2 hpres
  have ha0 : a = 0 := by
    have h := ha R
    change R (θ R) - θ ⁅R, R⁆ = a * θ R at h
    simpa only [hvalue, Derivation.map_one_eq_zero, lie_self, map_zero,
      sub_self, mul_one] using h.symm
  change IsAffineReebField θ R
  refine ⟨hvalue, ?_⟩
  intro W
  have hzero := ha W
  rw [ha0, zero_mul] at hzero
  change R (θ W) - W (θ R) - θ ⁅R, W⁆ = 0
  rw [hvalue, Derivation.map_one_eq_zero, sub_zero]
  exact hzero

theorem affineReeb_unique_proved
    (θ : AffineOneForm A) (hθ : IsAffineContactForm θ)
    (R S : AffineVectorFields A)
    (hR : IsAffineReebField θ R)
    (hS : IsAffineReebField θ S) :
    R = S := by
  obtain ⟨b, hperfect, hnormalize⟩ := hθ.2
  let u : AffineDistribution θ := ⟨R - S, by
    change θ (R - S) = 0
    rw [map_sub, hR.1, hS.1, sub_self]⟩
  have hb : b u = 0 := by
    apply LinearMap.ext
    intro w
    change b u w = 0
    rw [hnormalize u w]
    change θ ⁅R - S, w.1⁆ = 0
    rw [sub_lie, map_sub,
      affineReeb_bracket_value θ R hR w.1,
      affineReeb_bracket_value θ S hS w.1]
    have hw : θ w.1 = 0 := w.2
    simp only [hw, map_zero, sub_self]
  have hu0 : u = 0 := hperfect.2.1 (hb.trans (map_zero b).symm)
  have hdiff : R - S = 0 := congrArg (fun z : AffineDistribution θ => z.1) hu0
  exact sub_eq_zero.mp hdiff

theorem affineContact_hasReeb_proved
    (θ : AffineOneForm A) (hθ : IsAffineContactForm θ) :
    HasAffineReebField θ := by
  exact ⟨reebFromContactHamiltonian θ hθ,
    reebFromContactHamiltonian_isReeb_proved θ hθ⟩

end AffineReebProofCandidate

end

/-- The Hamiltonian field of 1 is precisely the Reeb field.
This is a geometric theorem, NOT part of the definition of Reeb. -/
theorem reebFromContactHamiltonian_isReeb
    (θ : AffineOneForm A) (hθ : IsAffineContactForm θ) :
    IsAffineReebField θ (reebFromContactHamiltonian θ hθ) := by
  exact LeBrunSalamon.PhaseEleven.AffineReebProofCandidate.reebFromContactHamiltonian_isReeb_proved (A := A) (θ := θ) (hθ := hθ)

/-- Uniqueness of Reeb vector fields follows from the perfect Levi pairing on `ker θ`. -/
theorem affineReeb_unique
    (θ : AffineOneForm A) (hθ : IsAffineContactForm θ)
    (R S : AffineVectorFields A)
    (hR : IsAffineReebField θ R)
    (hS : IsAffineReebField θ S) :
    R = S := by
  exact LeBrunSalamon.PhaseEleven.AffineReebProofCandidate.affineReeb_unique_proved (A := A) (θ := θ) (hθ := hθ) (R := R) (S := S) (hR := hR) (hS := hS)

/-- Existence of a Reeb field on a genuine affine contact chart. -/
theorem affineContact_hasReeb
    (θ : AffineOneForm A) (hθ : IsAffineContactForm θ) :
    HasAffineReebField θ := by
  exact LeBrunSalamon.PhaseEleven.AffineReebProofCandidate.affineContact_hasReeb_proved (A := A) (θ := θ) (hθ := hθ)

noncomputable section
set_option autoImplicit false
open LeBrunSalamon.PhaseOne
open LeBrunSalamon.PhaseFour
open LeBrunSalamon.PhaseNine
variable {A : Type*} [CommRing A] [Algebra ℂ A]

namespace AffineCartanProofCandidate

theorem affineReeb_is_strictContact_proved
    (θ : AffineOneForm A) (R : AffineVectorFields A)
    (hR : IsAffineReebField θ R) :
    IsStrictAffineContactVectorField θ R := by
  intro W
  rw [affineCartanFormula_proved, hR.2 W, hR.1,
    Derivation.map_one_eq_zero, zero_add]

end AffineCartanProofCandidate

end

/-- Reeb fields preserve the chosen contact one-form, not merely its
kernel. This is the algebraic identity `L_R θ=0`. -/
theorem affineReeb_is_strictContact
    (θ : AffineOneForm A) (R : AffineVectorFields A)
    (hR : IsAffineReebField θ R) :
    IsStrictAffineContactVectorField θ R := by
  exact LeBrunSalamon.PhaseEleven.AffineCartanProofCandidate.affineReeb_is_strictContact_proved (A := A) (θ := θ) (R := R) (hR := hR)

/-! ## 11D. Hamiltonian formulae and the Jacobi algebra -/

/-- The genuine contact Hamiltonian derivation corresponding to `f`,
constructed from the Phase 9 existence-and-uniqueness statements. -/
noncomputable def affineContactHamiltonianField
    (θ : AffineOneForm A) (hθ : IsAffineContactForm θ)
    (f : A) : AffineVectorFields A :=
  ((contactHamiltonianEquiv θ hθ).symm f).1

noncomputable section
set_option autoImplicit false
open LeBrunSalamon.PhaseOne
open LeBrunSalamon.PhaseFour
open LeBrunSalamon.PhaseNine
variable {A : Type*} [CommRing A] [Algebra ℂ A]

namespace AffineCartanProofCandidate

theorem affineContactHamiltonianField_value_proved
    (θ : AffineOneForm A) (hθ : IsAffineContactForm θ)
    (f : A) :
    θ (affineContactHamiltonianField θ hθ f) = f := by
  change (contactHamiltonianEquiv θ hθ)
    ((contactHamiltonianEquiv θ hθ).symm f) = f
  exact (contactHamiltonianEquiv θ hθ).apply_symm_apply f

theorem affineContactHamiltonianField_preserves_proved
    (θ : AffineOneForm A) (hθ : IsAffineContactForm θ)
    (f : A) :
    IsAffineContactVectorField θ
      (affineContactHamiltonianField θ hθ f) := by
  exact ((contactHamiltonianEquiv θ hθ).symm f).2

end AffineCartanProofCandidate

end

/-- The constructed field has Hamiltonian equal to `f`. -/
theorem affineContactHamiltonianField_value
    (θ : AffineOneForm A) (hθ : IsAffineContactForm θ)
    (f : A) :
    θ (affineContactHamiltonianField θ hθ f) = f := by
  exact LeBrunSalamon.PhaseEleven.AffineCartanProofCandidate.affineContactHamiltonianField_value_proved (A := A) (θ := θ) (hθ := hθ) (f := f)

/-- The constructed field preserves the contact distribution. -/
theorem affineContactHamiltonianField_preserves
    (θ : AffineOneForm A) (hθ : IsAffineContactForm θ)
    (f : A) :
    IsAffineContactVectorField θ
      (affineContactHamiltonianField θ hθ f) := by
  exact LeBrunSalamon.PhaseEleven.AffineCartanProofCandidate.affineContactHamiltonianField_preserves_proved (A := A) (θ := θ) (hθ := hθ) (f := f)

noncomputable section
set_option autoImplicit false
open LeBrunSalamon.PhaseOne
open LeBrunSalamon.PhaseFour
open LeBrunSalamon.PhaseNine
variable {A : Type*} [CommRing A] [Algebra ℂ A]

namespace AffineReebProofCandidate

theorem affineHamiltonian_lieDerivative_proved
    (θ : AffineOneForm A) (hθ : IsAffineContactForm θ)
    (f : A) (W : AffineVectorFields A) :
    affineLieDerivativeValue θ
      (affineContactHamiltonianField θ hθ f) W =
      (reebFromContactHamiltonian θ hθ f) * θ W := by
  let V : AffineVectorFields A := affineContactHamiltonianField θ hθ f
  let R : AffineVectorFields A := reebFromContactHamiltonian θ hθ
  have hvalue : θ V = f := by
    change (contactHamiltonianEquiv θ hθ)
      ((contactHamiltonianEquiv θ hθ).symm f) = f
    exact (contactHamiltonianEquiv θ hθ).apply_symm_apply f
  have hpres : IsAffineContactVectorField θ V :=
    ((contactHamiltonianEquiv θ hθ).symm f).2
  have hR : IsAffineReebField θ R := reebFromContactHamiltonian_isReeb_proved θ hθ
  obtain ⟨a, ha⟩ :=
    (conformalContact_iff_preservesDistribution_proved θ V hθ.1).2 hpres
  have hamult : a = R f := by
    calc
      a = a * θ R := by rw [hR.1, mul_one]
      _ = affineLieDerivativeValue θ V R := (ha R).symm
      _ = θ ⁅R, V⁆ := by
        change V (θ R) - θ ⁅V, R⁆ = θ ⁅R, V⁆
        rw [hR.1, Derivation.map_one_eq_zero, ← lie_skew V R,
          map_neg, zero_sub, neg_neg]
      _ = R (θ V) := affineReeb_bracket_value θ R hR V
      _ = R f := congrArg (fun c : A => R c) hvalue
  change affineLieDerivativeValue θ V W = R f * θ W
  rw [ha W, hamult]

theorem jacobiBracket_one_left_proved
    (θ : AffineOneForm A) (hθ : IsAffineContactForm θ)
    (f : A) :
    contactJacobiBracket θ hθ 1 f =
      reebFromContactHamiltonian θ hθ f := by
  let R : AffineVectorFields A := reebFromContactHamiltonian θ hθ
  let V : AffineVectorFields A := affineContactHamiltonianField θ hθ f
  have hvalue : θ V = f := by
    change (contactHamiltonianEquiv θ hθ)
      ((contactHamiltonianEquiv θ hθ).symm f) = f
    exact (contactHamiltonianEquiv θ hθ).apply_symm_apply f
  have hR : IsAffineReebField θ R := reebFromContactHamiltonian_isReeb_proved θ hθ
  change θ ⁅R, V⁆ = R f
  rw [affineReeb_bracket_value θ R hR V, hvalue]

theorem jacobiBracket_one_right_proved
    (θ : AffineOneForm A) (hθ : IsAffineContactForm θ)
    (f : A) :
    contactJacobiBracket θ hθ f 1 =
      -(reebFromContactHamiltonian θ hθ f) := by
  let R : AffineVectorFields A := reebFromContactHamiltonian θ hθ
  let V : AffineVectorFields A := affineContactHamiltonianField θ hθ f
  have hleft : θ ⁅R, V⁆ = R f := jacobiBracket_one_left_proved θ hθ f
  change θ ⁅V, R⁆ = -(R f)
  rw [← lie_skew V R, map_neg, hleft]

end AffineReebProofCandidate

end

/-- The Lie derivative of θ along `X_f` equals `R(f) θ`: this is the standard contact Hamiltonian identity
with the chosen Cartan sign convention. -/
theorem affineHamiltonian_lieDerivative
    (θ : AffineOneForm A) (hθ : IsAffineContactForm θ)
    (f : A) (W : AffineVectorFields A) :
    affineLieDerivativeValue θ
      (affineContactHamiltonianField θ hθ f) W =
      (reebFromContactHamiltonian θ hθ f) * θ W := by
  exact LeBrunSalamon.PhaseEleven.AffineReebProofCandidate.affineHamiltonian_lieDerivative_proved (A := A) (θ := θ) (hθ := hθ) (f := f) (W := W)

/-- The Jacobi bracket with the unit recovers differentiation by the
Reeb field: `{1,f} = R(f)` for the convention `{f,g}=θ([X_f,X_g])`. -/
theorem jacobiBracket_one_left
    (θ : AffineOneForm A) (hθ : IsAffineContactForm θ)
    (f : A) :
    contactJacobiBracket θ hθ 1 f =
      reebFromContactHamiltonian θ hθ f := by
  exact LeBrunSalamon.PhaseEleven.AffineReebProofCandidate.jacobiBracket_one_left_proved (A := A) (θ := θ) (hθ := hθ) (f := f)

/-- Consequently `{f,1} = -R(f)`. -/
theorem jacobiBracket_one_right
    (θ : AffineOneForm A) (hθ : IsAffineContactForm θ)
    (f : A) :
    contactJacobiBracket θ hθ f 1 =
      -(reebFromContactHamiltonian θ hθ f) := by
  exact LeBrunSalamon.PhaseEleven.AffineReebProofCandidate.jacobiBracket_one_right_proved (A := A) (θ := θ) (hθ := hθ) (f := f)

/-- An affine regular function is a first integral of the Reeb flow
when its derivative along the Reeb derivation is zero. -/
def IsAffineReebInvariant
    (θ : AffineOneForm A) (hθ : IsAffineContactForm θ)
    (f : A) : Prop :=
  reebFromContactHamiltonian θ hθ f = 0

/- Source-only Phase 3 integration: affine_hamiltonian_followups_2. -/
noncomputable section
set_option autoImplicit false
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseFour LeBrunSalamon.PhaseNine
variable {A : Type*} [CommRing A] [Algebra ℂ A]

namespace AffineFollowupProofCandidate

theorem reebInvariant_implies_strictContact_proved
    (θ : AffineOneForm A) (hθ : IsAffineContactForm θ)
    (f : A) (hf : IsAffineReebInvariant θ hθ f) :
    IsStrictAffineContactVectorField θ
      (affineContactHamiltonianField θ hθ f) := by
  change reebFromContactHamiltonian θ hθ f = 0 at hf
  intro W
  rw [affineHamiltonian_lieDerivative, hf, zero_mul]

theorem reeb_derives_contactJacobiBracket_proved
    (θ : AffineOneForm A) (hθ : IsAffineContactForm θ)
    (f g : A) :
    reebFromContactHamiltonian θ hθ
      (contactJacobiBracket θ hθ f g) =
      contactJacobiBracket θ hθ
        (reebFromContactHamiltonian θ hθ f) g +
      contactJacobiBracket θ hθ f
        (reebFromContactHamiltonian θ hθ g) := by
  let R : AffineVectorFields A := ((contactHamiltonianEquiv θ hθ).symm 1).1
  let V : AffineVectorFields A := ((contactHamiltonianEquiv θ hθ).symm f).1
  let W : AffineVectorFields A := ((contactHamiltonianEquiv θ hθ).symm g).1
  rw [← jacobiBracket_one_left θ hθ (contactJacobiBracket θ hθ f g),
    ← jacobiBracket_one_left θ hθ f, ← jacobiBracket_one_left θ hθ g]
  change θ ⁅R, ((contactHamiltonianEquiv θ hθ).symm
      (contactJacobiBracket θ hθ f g)).1⁆ =
    θ ⁅((contactHamiltonianEquiv θ hθ).symm
      (contactJacobiBracket θ hθ 1 f)).1, W⁆ +
    θ ⁅V, ((contactHamiltonianEquiv θ hθ).symm
      (contactJacobiBracket θ hθ 1 g)).1⁆
  rw [PhaseNine.AffineContactProofCandidate.contactHamiltonianEquiv_symm_bracket_val
      θ hθ f g,
    PhaseNine.AffineContactProofCandidate.contactHamiltonianEquiv_symm_bracket_val
      θ hθ 1 f,
    PhaseNine.AffineContactProofCandidate.contactHamiltonianEquiv_symm_bracket_val
      θ hθ 1 g]
  simpa only [map_add] using
    congrArg (fun Z : AffineVectorFields A => θ Z) (leibniz_lie R V W)

theorem contactHamiltonianField_bracket_proved
    (θ : AffineOneForm A) (hθ : IsAffineContactForm θ)
    (f g : A) :
    ⁅affineContactHamiltonianField θ hθ f,
      affineContactHamiltonianField θ hθ g⁆ =
    affineContactHamiltonianField θ hθ
      (contactJacobiBracket θ hθ f g) := by
  simpa only [affineContactHamiltonianField] using
    (PhaseNine.AffineContactProofCandidate.contactHamiltonianEquiv_symm_bracket_val
      θ hθ f g).symm

theorem contactJacobiBracket_add_left_proved
    (θ : AffineOneForm A) (hθ : IsAffineContactForm θ)
    (f g h : A) :
    contactJacobiBracket θ hθ (f + g) h =
      contactJacobiBracket θ hθ f h +
      contactJacobiBracket θ hθ g h := by
  unfold contactJacobiBracket affineJacobiValue
  rw [PhaseNine.AffineFollowupProofCandidate.inverse_add θ hθ f g,
    add_lie, map_add]

theorem contactJacobiBracket_add_right_proved
    (θ : AffineOneForm A) (hθ : IsAffineContactForm θ)
    (f g h : A) :
    contactJacobiBracket θ hθ f (g + h) =
      contactJacobiBracket θ hθ f g +
      contactJacobiBracket θ hθ f h := by
  unfold contactJacobiBracket affineJacobiValue
  rw [PhaseNine.AffineFollowupProofCandidate.inverse_add θ hθ g h,
    lie_add, map_add]

theorem contactJacobiBracket_smul_left_proved
    (θ : AffineOneForm A) (hθ : IsAffineContactForm θ)
    (c : ℂ) (f g : A) :
    contactJacobiBracket θ hθ (c • f) g =
      c • contactJacobiBracket θ hθ f g := by
  unfold contactJacobiBracket affineJacobiValue
  rw [PhaseNine.AffineFollowupProofCandidate.inverse_smul θ hθ c f, smul_lie]
  exact map_smul (θ.restrictScalars ℂ) c _

theorem contactJacobiBracket_smul_right_proved
    (θ : AffineOneForm A) (hθ : IsAffineContactForm θ)
    (c : ℂ) (f g : A) :
    contactJacobiBracket θ hθ f (c • g) =
      c • contactJacobiBracket θ hθ f g := by
  unfold contactJacobiBracket affineJacobiValue
  rw [PhaseNine.AffineFollowupProofCandidate.inverse_smul θ hθ c g, lie_smul]
  exact map_smul (θ.restrictScalars ℂ) c _

theorem reeb_commutator_hamiltonian_proved
    (θ : AffineOneForm A) (hθ : IsAffineContactForm θ)
    (f : A) :
    ⁅reebFromContactHamiltonian θ hθ,
      affineContactHamiltonianField θ hθ f⁆ =
    affineContactHamiltonianField θ hθ
      (reebFromContactHamiltonian θ hθ f) := by
  change ⁅affineContactHamiltonianField θ hθ 1,
      affineContactHamiltonianField θ hθ f⁆ =
    affineContactHamiltonianField θ hθ (reebFromContactHamiltonian θ hθ f)
  rw [contactHamiltonianField_bracket_proved, jacobiBracket_one_left]

theorem reebInvariant_closedUnderJacobi_proved
    (θ : AffineOneForm A) (hθ : IsAffineContactForm θ)
    (f g : A)
    (hf : IsAffineReebInvariant θ hθ f)
    (hg : IsAffineReebInvariant θ hθ g) :
    IsAffineReebInvariant θ hθ
      (contactJacobiBracket θ hθ f g) := by
  change reebFromContactHamiltonian θ hθ f = 0 at hf
  change reebFromContactHamiltonian θ hθ g = 0 at hg
  change reebFromContactHamiltonian θ hθ (contactJacobiBracket θ hθ f g) = 0
  rw [reeb_derives_contactJacobiBracket_proved, hf, hg]
  simp only [contactJacobiBracket, affineJacobiValue,
    PhaseNine.AffineFollowupProofCandidate.inverse_zero,
    zero_lie, lie_zero, map_zero, zero_add]

end AffineFollowupProofCandidate
end


/-- Reeb-invariant Hamiltonians generate STRICT contact vector fields. -/
theorem reebInvariant_implies_strictContact
    (θ : AffineOneForm A) (hθ : IsAffineContactForm θ)
    (f : A) (hf : IsAffineReebInvariant θ hθ f) :
    IsStrictAffineContactVectorField θ
      (affineContactHamiltonianField θ hθ f) := by
  exact LeBrunSalamon.PhaseEleven.AffineFollowupProofCandidate.reebInvariant_implies_strictContact_proved (θ := θ) (hθ := hθ) (f := f) (hf := hf)

/-- Reeb differentiation acts by derivations of the Jacobi bracket.
This follows from the Jacobi identity and `{1,f}=R(f)`. -/
theorem reeb_derives_contactJacobiBracket
    (θ : AffineOneForm A) (hθ : IsAffineContactForm θ)
    (f g : A) :
    reebFromContactHamiltonian θ hθ
      (contactJacobiBracket θ hθ f g) =
      contactJacobiBracket θ hθ
        (reebFromContactHamiltonian θ hθ f) g +
      contactJacobiBracket θ hθ f
        (reebFromContactHamiltonian θ hθ g) := by
  exact LeBrunSalamon.PhaseEleven.AffineFollowupProofCandidate.reeb_derives_contactJacobiBracket_proved (θ := θ) (hθ := hθ) (f := f) (g := g)

/-- Hamiltonian fields intertwine the Jacobi bracket and the ordinary Lie bracket of derivations. This is
the key local Lie-algebra statement needed before constructing the global automorphism Lie algebra. -/
theorem contactHamiltonianField_bracket
    (θ : AffineOneForm A) (hθ : IsAffineContactForm θ)
    (f g : A) :
    ⁅affineContactHamiltonianField θ hθ f,
      affineContactHamiltonianField θ hθ g⁆ =
    affineContactHamiltonianField θ hθ
      (contactJacobiBracket θ hθ f g) := by
  exact LeBrunSalamon.PhaseEleven.AffineFollowupProofCandidate.contactHamiltonianField_bracket_proved (θ := θ) (hθ := hθ) (f := f) (g := g)

/-- The Jacobi bracket is additive in its first entry. -/
theorem contactJacobiBracket_add_left
    (θ : AffineOneForm A) (hθ : IsAffineContactForm θ)
    (f g h : A) :
    contactJacobiBracket θ hθ (f + g) h =
      contactJacobiBracket θ hθ f h +
      contactJacobiBracket θ hθ g h := by
  exact LeBrunSalamon.PhaseEleven.AffineFollowupProofCandidate.contactJacobiBracket_add_left_proved (θ := θ) (hθ := hθ) (f := f) (g := g) (h := h)

/-- The Jacobi bracket is additive in its second entry. -/
theorem contactJacobiBracket_add_right
    (θ : AffineOneForm A) (hθ : IsAffineContactForm θ)
    (f g h : A) :
    contactJacobiBracket θ hθ f (g + h) =
      contactJacobiBracket θ hθ f g +
      contactJacobiBracket θ hθ f h := by
  exact LeBrunSalamon.PhaseEleven.AffineFollowupProofCandidate.contactJacobiBracket_add_right_proved (θ := θ) (hθ := hθ) (f := f) (g := g) (h := h)

/-- The Jacobi bracket is ℂ-linear in the first entry.
It is generally NOT linear over A with respect to multiplication. -/
theorem contactJacobiBracket_smul_left
    (θ : AffineOneForm A) (hθ : IsAffineContactForm θ)
    (c : ℂ) (f g : A) :
    contactJacobiBracket θ hθ (c • f) g =
      c • contactJacobiBracket θ hθ f g := by
  exact LeBrunSalamon.PhaseEleven.AffineFollowupProofCandidate.contactJacobiBracket_smul_left_proved (θ := θ) (hθ := hθ) (c := c) (f := f) (g := g)

/-- The Jacobi bracket is ℂ-linear in the second entry. -/
theorem contactJacobiBracket_smul_right
    (θ : AffineOneForm A) (hθ : IsAffineContactForm θ)
    (c : ℂ) (f g : A) :
    contactJacobiBracket θ hθ f (c • g) =
      c • contactJacobiBracket θ hθ f g := by
  exact LeBrunSalamon.PhaseEleven.AffineFollowupProofCandidate.contactJacobiBracket_smul_right_proved (θ := θ) (hθ := hθ) (c := c) (f := f) (g := g)

/-- The Reeb derivation commutes with X_f up to the Hamiltonian field of R(f): `[R,X_f] = X_{R(f)}`. -/
theorem reeb_commutator_hamiltonian
    (θ : AffineOneForm A) (hθ : IsAffineContactForm θ)
    (f : A) :
    ⁅reebFromContactHamiltonian θ hθ,
      affineContactHamiltonianField θ hθ f⁆ =
    affineContactHamiltonianField θ hθ
      (reebFromContactHamiltonian θ hθ f) := by
  exact LeBrunSalamon.PhaseEleven.AffineFollowupProofCandidate.reeb_commutator_hamiltonian_proved (θ := θ) (hθ := hθ) (f := f)

/-- The Jacobi bracket preserves the subspace of functions constant along the Reeb derivation. -/
theorem reebInvariant_closedUnderJacobi
    (θ : AffineOneForm A) (hθ : IsAffineContactForm θ)
    (f g : A)
    (hf : IsAffineReebInvariant θ hθ f)
    (hg : IsAffineReebInvariant θ hθ g) :
    IsAffineReebInvariant θ hθ
      (contactJacobiBracket θ hθ f g) := by
  exact LeBrunSalamon.PhaseEleven.AffineFollowupProofCandidate.reebInvariant_closedUnderJacobi_proved (θ := θ) (hθ := hθ) (f := f) (g := g) (hf := hf) (hg := hg)

end LeBrunSalamon.PhaseEleven

/-!
# Phase 12 -- quadratic diagonal symbols and exchange parity

On the diagonal Δ of X×X, a symmetric section of `L ⊠ L` with order two has leading symbol in `Sym²(Ω¹_X)
⊗ L²`. The expected contact-geometric symbol is `θ ⊗ θ`. We formalize the fibrewise symbol with the
genuine mathlib tensor product and prove-free statements about its symmetry.

At the AFFINE level, the exchange map acts by `(-1)^k` on `I_Δ^k / I_Δ^(k+1)`. Thus symmetric functions
cannot have a first NONZERO term of odd diagonal order. Those results are stated directly for the actual
affine diagonal ideal. The global sheaf `L ⊠ L` and its filtered associated graded is not implemented in
this early phase (the actual external product is supplied in Phase 28); no arbitrary sheaf is relabelled
as an external tensor square.
-/

namespace LeBrunSalamon.PhaseTwelve

open LeBrunSalamon.PhaseOne
open LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseSeven
open scoped TensorProduct

/-! ## 12A. The fibrewise rank-one quadratic contact symbol -/

variable {V L : Type*}
variable [AddCommGroup V] [Module ℂ V]
variable [AddCommGroup L] [Module ℂ L]

/-- The tensor-valued quadratic *polarization* of the contact form:
`(v,w) ↦ θ(v) ⊗ θ(w)` in `L ⊗_ℂ L`.

On the diagonal of a contact variety, the quadratic symbol of the
symmetric two-point kernel is expected to agree with this expression,
up to the conventionally normalized scalar. -/
def contactQuadraticSymbolValue
    (θ : V →ₗ[ℂ] L) (v w : V) : L ⊗[ℂ] L :=
  (θ v) ⊗ₜ[ℂ] (θ w)

/-- A proposed leading-symbol function has EXACTLY the rank-one contact quadratic polarization induced by
`θ`. This is a precise algebraic equation, not an unexplained geometric predicate. -/
def IsContactQuadraticSymbol
    (θ : V →ₗ[ℂ] L)
    (B : V → V → L ⊗[ℂ] L) : Prop :=
  ∀ v w : V, B v w = contactQuadraticSymbolValue θ v w

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct
open LeBrunSalamon.PhaseThree LeBrunSalamon.PhaseSeven
open LeBrunSalamon.PhaseTen.AffineDiagonalProof
variable {V L : Type*}
variable [AddCommGroup V] [Module ℂ V]
variable [AddCommGroup L] [Module ℂ L]

namespace AffineSymbolProof

theorem contactQuadraticSymbol_exchange
    (θ : V →ₗ[ℂ] L) (v w : V) :
    (TensorProduct.comm ℂ L L)
      (contactQuadraticSymbolValue θ v w) =
        contactQuadraticSymbolValue θ w v := by
  simp [contactQuadraticSymbolValue]

theorem contactQuadraticSymbol_left_kernel
    (θ : V →ₗ[ℂ] L) (v w : V)
    (hv : θ v = 0) :
    contactQuadraticSymbolValue θ v w = 0 := by
  simp [contactQuadraticSymbolValue, hv]

theorem contactQuadraticSymbol_right_kernel
    (θ : V →ₗ[ℂ] L) (v w : V)
    (hw : θ w = 0) :
    contactQuadraticSymbolValue θ v w = 0 := by
  simp [contactQuadraticSymbolValue, hw]

theorem contactQuadraticSymbol_nonzero
    [Nontrivial L] (θ : V →ₗ[ℂ] L)
    (hθ : Function.Surjective θ) :
    ∃ v : V, contactQuadraticSymbolValue θ v v ≠ 0 := by
  classical
  obtain ⟨z, hz⟩ := exists_ne (0 : L)
  obtain ⟨v, hv⟩ := hθ z
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one ℂ hz
  refine ⟨v, ?_⟩
  intro hzero
  have he := congrArg
    (fun t : L ⊗[ℂ] L =>
      (TensorProduct.lid ℂ ℂ) ((TensorProduct.map φ φ) t)) hzero
  simpa [contactQuadraticSymbolValue, hv, hφ] using he

end AffineSymbolProof

end

/-- Exchange of the two tensor factors interchanges the arguments
of the contact quadratic polarization. -/
theorem contactQuadraticSymbol_exchange
    (θ : V →ₗ[ℂ] L) (v w : V) :
    (TensorProduct.comm ℂ L L)
      (contactQuadraticSymbolValue θ v w) =
        contactQuadraticSymbolValue θ w v := by
  exact LeBrunSalamon.PhaseTwelve.AffineSymbolProof.contactQuadraticSymbol_exchange (V := V) (L := L) (θ := θ) (v := v) (w := w)

/-- If a tangent vector lies in `ker θ`, the quadratic contact symbol
vanishes when evaluated with that vector in the first argument. -/
theorem contactQuadraticSymbol_left_kernel
    (θ : V →ₗ[ℂ] L) (v w : V)
    (hv : θ v = 0) :
    contactQuadraticSymbolValue θ v w = 0 := by
  exact LeBrunSalamon.PhaseTwelve.AffineSymbolProof.contactQuadraticSymbol_left_kernel (V := V) (L := L) (θ := θ) (v := v) (w := w) (hv := hv)

/-- The same vanishing condition in the second argument. -/
theorem contactQuadraticSymbol_right_kernel
    (θ : V →ₗ[ℂ] L) (v w : V)
    (hw : θ w = 0) :
    contactQuadraticSymbolValue θ v w = 0 := by
  exact LeBrunSalamon.PhaseTwelve.AffineSymbolProof.contactQuadraticSymbol_right_kernel (V := V) (L := L) (θ := θ) (v := v) (w := w) (hw := hw)

/-- Nontriviality of the contact symbol when the contact form is onto a nonzero line. This detects the
danger of a *zero* chosen contact form masquerading as a nondegenerate contact structure. -/
theorem contactQuadraticSymbol_nonzero
    [Nontrivial L] (θ : V →ₗ[ℂ] L)
    (hθ : Function.Surjective θ) :
    ∃ v : V, contactQuadraticSymbolValue θ v v ≠ 0 := by
  exact LeBrunSalamon.PhaseTwelve.AffineSymbolProof.contactQuadraticSymbol_nonzero (V := V) (L := L) (θ := θ) (hθ := hθ)

/-! ## 12B. Actual symbol classes in the affine principal-parts quotient -/

/-- The class of an affine two-point function modulo `I_Δ^(k+1)`. For a function in `I_Δ^k`, this class IS
its degree-k leading symbol, represented as an element of the genuine quotient ring of principal parts,
rather than in a newly postulated associated-graded module. -/
noncomputable def affineSymbolModNext
    (A : Type*) [CommRing A] [Algebra ℂ A]
    (k : ℕ) (u : AffineTwoPointRing A) :
    affinePrincipalParts A k :=
  (Ideal.Quotient.mk ((affineDiagonalIdeal A) ^ (k + 1))) u

/-- An honest degree-k affine leading symbol: an element in `I^k`
with its class computed modulo `I^(k+1)`. -/
structure AffineLeadingSymbol
    (A : Type*) [CommRing A] [Algebra ℂ A]
    (k : ℕ) where
  representative : AffineTwoPointRing A
  orderAtLeast : AffineVanishesToOrder A representative k

/-- Map a chosen representative of a degree-k symbol into its real principal-parts quotient. Different
representatives may give the same symbol; this equality is treated by a theorem below. -/
noncomputable def AffineLeadingSymbol.value
    {A : Type*} [CommRing A] [Algebra ℂ A]
    {k : ℕ} (s : AffineLeadingSymbol A k) :
    affinePrincipalParts A k :=
  affineSymbolModNext A k s.representative

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct
open LeBrunSalamon.PhaseThree LeBrunSalamon.PhaseSeven
open LeBrunSalamon.PhaseTen.AffineDiagonalProof

namespace AffineSymbolProof

theorem affineLeadingSymbol_zero_iff
    (A : Type*) [CommRing A] [Algebra ℂ A]
    (k : ℕ) (s : AffineLeadingSymbol A k) :
    s.value = 0 ↔
      AffineVanishesToOrder A s.representative (k + 1) := by
  change (Ideal.Quotient.mk ((affineDiagonalIdeal A) ^ (k + 1)))
      s.representative = 0 ↔
    s.representative ∈ (affineDiagonalIdeal A) ^ (k + 1)
  exact Ideal.Quotient.eq_zero_iff_mem

theorem affineLeadingSymbol_eq_of_congruent
    (A : Type*) [CommRing A] [Algebra ℂ A]
    (k : ℕ) (u v : AffineLeadingSymbol A k)
    (h : HaveSameAffineDiagonalSymbol A u.representative v.representative k) :
    u.value = v.value := by
  change (Ideal.Quotient.mk ((affineDiagonalIdeal A) ^ (k + 1))) u.representative =
    (Ideal.Quotient.mk ((affineDiagonalIdeal A) ^ (k + 1))) v.representative
  exact Ideal.Quotient.eq.2 h.2.2

section AffineDiagonal

variable (A : Type*) [CommRing A] [Algebra ℂ A]

theorem diagonalDifference_mem (a : A) :
    (1 : A) ⊗ₜ[ℂ] a - a ⊗ₜ[ℂ] (1 : A) ∈ affineDiagonalIdeal A := by
  change affineDiagonalMultiplication A
    ((1 : A) ⊗ₜ[ℂ] a - a ⊗ₜ[ℂ] (1 : A)) = 0
  simp only [map_sub, diagonalMultiplication_tmul, one_mul, mul_one, sub_self]

theorem swap_sub_mem (u : AffineTwoPointRing A) :
    (TensorProduct.comm ℂ A A) u - u ∈ affineDiagonalIdeal A := by
  change affineDiagonalMultiplication A ((TensorProduct.comm ℂ A A) u - u) = 0
  rw [map_sub, diagonalMultiplication_swap, sub_self]

/-- The first-order remainder is a product of actual diagonal differences. -/
theorem swap_first_order_remainder_mem (u : AffineTwoPointRing A) :
    (TensorProduct.comm ℂ A A) u + u -
      (affineDiagonalMultiplication A u ⊗ₜ[ℂ] (1 : A)) -
      ((1 : A) ⊗ₜ[ℂ] affineDiagonalMultiplication A u) ∈
      (affineDiagonalIdeal A) ^ 2 := by
  refine TensorProduct.inductionOn u ?_ ?_
  · intro a b
    have hmul :
        (((1 : A) ⊗ₜ[ℂ] a - a ⊗ₜ[ℂ] (1 : A)) *
          ((1 : A) ⊗ₜ[ℂ] b - b ⊗ₜ[ℂ] (1 : A))) ∈
          (affineDiagonalIdeal A) ^ 2 := by
      simpa only [pow_two] using
        Ideal.mul_mem_mul (diagonalDifference_mem A a) (diagonalDifference_mem A b)
    have he :
        (TensorProduct.comm ℂ A A) (a ⊗ₜ[ℂ] b) + (a ⊗ₜ[ℂ] b) -
          (affineDiagonalMultiplication A (a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] (1 : A)) -
          ((1 : A) ⊗ₜ[ℂ] affineDiagonalMultiplication A (a ⊗ₜ[ℂ] b)) =
        -(((1 : A) ⊗ₜ[ℂ] a - a ⊗ₜ[ℂ] (1 : A)) *
          ((1 : A) ⊗ₜ[ℂ] b - b ⊗ₜ[ℂ] (1 : A))) := by
      simp only [TensorProduct.comm_tmul, diagonalMultiplication_tmul,
        mul_sub, sub_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
      abel
    rw [he]
    exact ((affineDiagonalIdeal A) ^ 2).neg_mem hmul
  · intro x y hx hy
    have he :
        (TensorProduct.comm ℂ A A) (x + y) + (x + y) -
          (affineDiagonalMultiplication A (x + y) ⊗ₜ[ℂ] (1 : A)) -
          ((1 : A) ⊗ₜ[ℂ] affineDiagonalMultiplication A (x + y)) =
        ((TensorProduct.comm ℂ A A) x + x -
          (affineDiagonalMultiplication A x ⊗ₜ[ℂ] (1 : A)) -
          ((1 : A) ⊗ₜ[ℂ] affineDiagonalMultiplication A x)) +
        ((TensorProduct.comm ℂ A A) y + y -
          (affineDiagonalMultiplication A y ⊗ₜ[ℂ] (1 : A)) -
          ((1 : A) ⊗ₜ[ℂ] affineDiagonalMultiplication A y)) := by
      simp only [map_add, TensorProduct.add_tmul, TensorProduct.tmul_add]
      abel
    rw [he]
    exact ((affineDiagonalIdeal A) ^ 2).add_mem hx hy

theorem swap_add_mem_square (u : AffineTwoPointRing A)
    (hu : u ∈ affineDiagonalIdeal A) :
    (TensorProduct.comm ℂ A A) u + u ∈ (affineDiagonalIdeal A) ^ 2 := by
  have hz : affineDiagonalMultiplication A u = 0 := hu
  simpa only [hz, TensorProduct.zero_tmul, TensorProduct.tmul_zero, sub_zero] using
    swap_first_order_remainder_mem A u

/-- Multiplicativity raises the first-order sign calculation to every ideal power. -/
theorem swap_power_sign_remainder_mem (k : ℕ) (u : AffineTwoPointRing A)
    (hu : u ∈ (affineDiagonalIdeal A) ^ k) :
    (TensorProduct.comm ℂ A A) u - (-1 : AffineTwoPointRing A) ^ k * u ∈
      (affineDiagonalIdeal A) ^ (k + 1) := by
  induction k generalizing u with
  | zero =>
    simpa only [pow_zero, one_mul, zero_add, pow_one] using swap_sub_mem A u
  | succ k ih =>
    have hu' : u ∈ (affineDiagonalIdeal A) ^ k * affineDiagonalIdeal A := by
      simpa only [pow_succ] using hu
    refine Submodule.mul_induction_on hu' ?_ ?_
    · intro a ha b hb
      have hswap : (TensorProduct.comm ℂ A A) a ∈ (affineDiagonalIdeal A) ^ k :=
        LeBrunSalamon.PhaseTen.AffineDiagonalProof.affineSwap_preservesDiagonalOrder A a k ha
      have hfirst : (TensorProduct.comm ℂ A A) a *
          ((TensorProduct.comm ℂ A A) b + b) ∈ (affineDiagonalIdeal A) ^ (k + 2) := by
        simpa only [← pow_add] using
          Ideal.mul_mem_mul hswap (swap_add_mem_square A b hb)
      have hsecond :
          ((TensorProduct.comm ℂ A A) a - (-1 : AffineTwoPointRing A) ^ k * a) * b ∈
            (affineDiagonalIdeal A) ^ (k + 2) := by
        simpa only [← pow_succ, Nat.add_assoc] using Ideal.mul_mem_mul (ih a ha) hb
      have he :
          (TensorProduct.comm ℂ A A) (a * b) -
              (-1 : AffineTwoPointRing A) ^ (k + 1) * (a * b) =
          (TensorProduct.comm ℂ A A) a * ((TensorProduct.comm ℂ A A) b + b) -
            ((TensorProduct.comm ℂ A A) a - (-1 : AffineTwoPointRing A) ^ k * a) * b := by
        rw [tensorSwap_mul, pow_succ]
        ring
      rw [he]
      exact ((affineDiagonalIdeal A) ^ (k + 2)).sub_mem hfirst hsecond
    · intro x y hx hy
      have he :
          (TensorProduct.comm ℂ A A) (x + y) -
              (-1 : AffineTwoPointRing A) ^ (k + 1) * (x + y) =
          ((TensorProduct.comm ℂ A A) x - (-1 : AffineTwoPointRing A) ^ (k + 1) * x) +
            ((TensorProduct.comm ℂ A A) y - (-1 : AffineTwoPointRing A) ^ (k + 1) * y) := by
        rw [map_add]
        ring
      rw [he]
      exact ((affineDiagonalIdeal A) ^ (k + 2)).add_mem hx hy

end AffineDiagonal

theorem affineSymbol_exchange_sign
    (A : Type*) [CommRing A] [Algebra ℂ A]
    (k : ℕ) (s : AffineLeadingSymbol A k) :
    affineSymbolModNext A k
        ((TensorProduct.comm ℂ A A) s.representative) =
      (-1 : affinePrincipalParts A k) ^ k * s.value := by
  have he :
      (Ideal.Quotient.mk ((affineDiagonalIdeal A) ^ (k + 1)))
          ((TensorProduct.comm ℂ A A) s.representative) =
      (Ideal.Quotient.mk ((affineDiagonalIdeal A) ^ (k + 1)))
          ((-1 : AffineTwoPointRing A) ^ k * s.representative) :=
    Ideal.Quotient.eq.2 (swap_power_sign_remainder_mem A k s.representative s.orderAtLeast)
  simpa only [affineSymbolModNext, AffineLeadingSymbol.value,
    map_mul, map_pow, map_neg, map_one] using he

section AffineDiagonal

variable (A : Type*) [CommRing A] [Algebra ℂ A]

theorem affineVanishingOrder_mul
    (u v : AffineTwoPointRing A) (r s : ℕ)
    (hu : AffineVanishesToOrder A u r)
    (hv : AffineVanishesToOrder A v s) :
    AffineVanishesToOrder A (u * v) (r + s) := by
  change u * v ∈ (affineDiagonalIdeal A) ^ (r + s)
  rw [pow_add]
  exact Ideal.mul_mem_mul hu hv

theorem affineSameSymbol_preservesExactOrder
    (u v : AffineTwoPointRing A) (k : ℕ)
    (h : HaveSameAffineDiagonalSymbol A u v k)
    (hu : HasExactAffineDiagonalOrder A u k) :
    HasExactAffineDiagonalOrder A v k := by
  refine ⟨h.2.1, ?_⟩
  intro hv
  apply hu.2
  change u ∈ (affineDiagonalIdeal A) ^ (k + 1)
  simpa only [sub_add_cancel] using
    ((affineDiagonalIdeal A) ^ (k + 1)).add_mem h.2.2 hv

theorem symmetric_oddOrder_raisesVanishing
    (u : AffineTwoPointRing A) (k : ℕ)
    (hu : IsSymmetricAffineTwoPointFunction A u)
    (hord : AffineVanishesToOrder A u (2 * k + 1)) :
    AffineVanishesToOrder A u (2 * k + 2) := by
  have he := affineSymbol_exchange_sign A (2 * k + 1) ⟨u, hord⟩
  change affineSymbolModNext A (2 * k + 1) ((TensorProduct.comm ℂ A A) u) =
    (-1 : affinePrincipalParts A (2 * k + 1)) ^ (2 * k + 1) *
      affineSymbolModNext A (2 * k + 1) u at he
  have hsign : (-1 : affinePrincipalParts A (2 * k + 1)) ^ (2 * k + 1) = -1 := by
    simp [pow_add, pow_mul]
  change (TensorProduct.comm ℂ A A) u = u at hu
  rw [hu, hsign, neg_one_mul] at he
  have hz := zero_of_eq_neg (affineSymbolModNext A (2 * k + 1) u) he
  have hnext := (affineLeadingSymbol_zero_iff A (2 * k + 1) ⟨u, hord⟩).mp hz
  simpa only [Nat.add_assoc] using hnext

theorem antisymmetric_evenOrder_raisesVanishing
    (u : AffineTwoPointRing A) (k : ℕ)
    (hu : IsAntisymmetricAffineTwoPointFunction A u)
    (hord : AffineVanishesToOrder A u (2 * k)) :
    AffineVanishesToOrder A u (2 * k + 1) := by
  have he := affineSymbol_exchange_sign A (2 * k) ⟨u, hord⟩
  change (Ideal.Quotient.mk ((affineDiagonalIdeal A) ^ (2 * k + 1)))
      ((TensorProduct.comm ℂ A A) u) =
    (-1 : affinePrincipalParts A (2 * k)) ^ (2 * k) *
      affineSymbolModNext A (2 * k) u at he
  have hsign : (-1 : affinePrincipalParts A (2 * k)) ^ (2 * k) = 1 := by
    simp [pow_mul]
  change (TensorProduct.comm ℂ A A) u = -u at hu
  rw [hu, map_neg, hsign, one_mul] at he
  have hz := zero_of_eq_neg (affineSymbolModNext A (2 * k) u) he.symm
  exact (affineLeadingSymbol_zero_iff A (2 * k) ⟨u, hord⟩).mp hz

theorem symmetric_no_exact_oddOrder
    (u : AffineTwoPointRing A) (k : ℕ)
    (hu : IsSymmetricAffineTwoPointFunction A u) :
    ¬ HasExactAffineDiagonalOrder A u (2 * k + 1) := by
  intro hord
  apply hord.2
  simpa only [Nat.add_assoc] using symmetric_oddOrder_raisesVanishing A u k hu hord.1

theorem antisymmetric_no_exact_evenOrder
    (u : AffineTwoPointRing A) (k : ℕ)
    (hu : IsAntisymmetricAffineTwoPointFunction A u) :
    ¬ HasExactAffineDiagonalOrder A u (2 * k) := by
  intro hord
  exact hord.2 (antisymmetric_evenOrder_raisesVanishing A u k hu hord.1)

theorem square_of_antisymmetric_is_quadratic
    (u : AffineTwoPointRing A)
    (hu : IsAntisymmetricAffineTwoPointFunction A u) :
    IsSymmetricAffineTwoPointFunction A (u * u) ∧
      AffineVanishesQuadratically A (u * u) := by
  change (TensorProduct.comm ℂ A A) u = -u at hu
  refine ⟨?_, ?_⟩
  · change (TensorProduct.comm ℂ A A) (u * u) = u * u
    rw [tensorSwap_mul, hu, neg_mul_neg]
  · have hdiag := congrArg (affineDiagonalMultiplication A) hu
    rw [diagonalMultiplication_swap, map_neg] at hdiag
    have hz := zero_of_eq_neg (affineDiagonalMultiplication A u) hdiag
    have hi : u ∈ affineDiagonalIdeal A := hz
    change u * u ∈ (affineDiagonalIdeal A) ^ 2
    simpa only [pow_two] using Ideal.mul_mem_mul hi hi

end AffineDiagonal

end AffineSymbolProof

end

/-- A leading symbol is zero iff its representative actually vanishes one order further. This is the
intrinsic content of the associated graded quotient `I^k/I^(k+1)`. -/
theorem affineLeadingSymbol_zero_iff
    (A : Type*) [CommRing A] [Algebra ℂ A]
    (k : ℕ) (s : AffineLeadingSymbol A k) :
    s.value = 0 ↔
      AffineVanishesToOrder A s.representative (k + 1) := by
  exact LeBrunSalamon.PhaseTwelve.AffineSymbolProof.affineLeadingSymbol_zero_iff (A := A) (k := k) (s := s)

/-- Two representatives with the same leading symbol map to the same class modulo `I^(k+1)`. -/
theorem affineLeadingSymbol_eq_of_congruent
    (A : Type*) [CommRing A] [Algebra ℂ A]
    (k : ℕ) (u v : AffineLeadingSymbol A k)
    (h : HaveSameAffineDiagonalSymbol A u.representative v.representative k) :
    u.value = v.value := by
  exact LeBrunSalamon.PhaseTwelve.AffineSymbolProof.affineLeadingSymbol_eq_of_congruent (A := A) (k := k) (u := u) (v := v) (h := h)

/-- Exchange acts on the degree-k associated-graded quotient by `(-1)^k`. This is a useful core
calculation behind the even/odd vanishing lemmas, and holds without any smoothness hypothesis on A. -/
theorem affineSymbol_exchange_sign
    (A : Type*) [CommRing A] [Algebra ℂ A]
    (k : ℕ) (s : AffineLeadingSymbol A k) :
    affineSymbolModNext A k
        ((TensorProduct.comm ℂ A A) s.representative) =
      (-1 : affinePrincipalParts A k) ^ k * s.value := by
  exact LeBrunSalamon.PhaseTwelve.AffineSymbolProof.affineSymbol_exchange_sign (A := A) (k := k) (s := s)

/-! ## 12C. Powers of the actual affine diagonal ideal -/

section AffineDiagonal

variable (A : Type*) [CommRing A] [Algebra ℂ A]

/-- Multiplying vanishing orders on the diagonal: if `u∈I^r` and `v∈I^s` then `uv∈I^(r+s)`. -/
theorem affineVanishingOrder_mul
    (u v : AffineTwoPointRing A) (r s : ℕ)
    (hu : AffineVanishesToOrder A u r)
    (hv : AffineVanishesToOrder A v s) :
    AffineVanishesToOrder A (u * v) (r + s) := by
  exact LeBrunSalamon.PhaseTwelve.AffineSymbolProof.affineVanishingOrder_mul (A := A) (u := u) (v := v) (r := r) (s := s) (hu := hu) (hv := hv)

/-- Congruent leading symbols have the same exact vanishing order,
provided the order was exact for one representative. -/
theorem affineSameSymbol_preservesExactOrder
    (u v : AffineTwoPointRing A) (k : ℕ)
    (h : HaveSameAffineDiagonalSymbol A u v k)
    (hu : HasExactAffineDiagonalOrder A u k) :
    HasExactAffineDiagonalOrder A v k := by
  exact LeBrunSalamon.PhaseTwelve.AffineSymbolProof.affineSameSymbol_preservesExactOrder (A := A) (u := u) (v := v) (k := k) (h := h) (hu := hu)

/-- Exchange is -1 on the conormal module `I/I²`; on its k-th tensor power it acts by `(-1)^k` modulo
higher-order terms. Consequently a SYMMETRIC function with vanishing order at least `2k+1` automatically
vanishes to order at least `2k+2` in characteristic zero. -/
theorem symmetric_oddOrder_raisesVanishing
    (u : AffineTwoPointRing A) (k : ℕ)
    (hu : IsSymmetricAffineTwoPointFunction A u)
    (hord : AffineVanishesToOrder A u (2 * k + 1)) :
    AffineVanishesToOrder A u (2 * k + 2) := by
  exact LeBrunSalamon.PhaseTwelve.AffineSymbolProof.symmetric_oddOrder_raisesVanishing (A := A) (u := u) (k := k) (hu := hu) (hord := hord)

/-- The antisymmetric parity counterpart: a sign-reversing function
cannot have a first nonzero term of EVEN order. -/
theorem antisymmetric_evenOrder_raisesVanishing
    (u : AffineTwoPointRing A) (k : ℕ)
    (hu : IsAntisymmetricAffineTwoPointFunction A u)
    (hord : AffineVanishesToOrder A u (2 * k)) :
    AffineVanishesToOrder A u (2 * k + 1) := by
  exact LeBrunSalamon.PhaseTwelve.AffineSymbolProof.antisymmetric_evenOrder_raisesVanishing (A := A) (u := u) (k := k) (hu := hu) (hord := hord)

/-- A symmetric affine two-point function has no exact ODD diagonal
vanishing order. It may vanish identically to every order. -/
theorem symmetric_no_exact_oddOrder
    (u : AffineTwoPointRing A) (k : ℕ)
    (hu : IsSymmetricAffineTwoPointFunction A u) :
    ¬ HasExactAffineDiagonalOrder A u (2 * k + 1) := by
  exact LeBrunSalamon.PhaseTwelve.AffineSymbolProof.symmetric_no_exact_oddOrder (A := A) (u := u) (k := k) (hu := hu)

/-- An antisymmetric affine two-point function has no exact EVEN vanishing order. -/
theorem antisymmetric_no_exact_evenOrder
    (u : AffineTwoPointRing A) (k : ℕ)
    (hu : IsAntisymmetricAffineTwoPointFunction A u) :
    ¬ HasExactAffineDiagonalOrder A u (2 * k) := by
  exact LeBrunSalamon.PhaseTwelve.AffineSymbolProof.antisymmetric_no_exact_evenOrder (A := A) (u := u) (k := k) (hu := hu)

/-- An antisymmetric function vanishes on the diagonal, and its square is a symmetric two-point function
vanishing quadratically. This is a concrete local construction of quadratic kernels (though the resulting
quadratic symbols need not be the contact symbol `θ⊗θ`). -/
theorem square_of_antisymmetric_is_quadratic
    (u : AffineTwoPointRing A)
    (hu : IsAntisymmetricAffineTwoPointFunction A u) :
    IsSymmetricAffineTwoPointFunction A (u * u) ∧
      AffineVanishesQuadratically A (u * u) := by
  exact LeBrunSalamon.PhaseTwelve.AffineSymbolProof.square_of_antisymmetric_is_quadratic (A := A) (u := u) (hu := hu)

/-- A specific affine quadratic two-point function, given as the square of an antisymmetric seed. The use
of `seed * seed` is actual ring multiplication in `A ⊗_ℂ A`. -/
def affineQuadraticKernelFromSeed
    (u : AffineTwoPointRing A) : AffineTwoPointRing A :=
  u * u

/-- The nondegeneracy of a quadratic kernel is NOT automatic: a seed may vanish to order two or may be
nilpotent. We therefore record the exact order as a separate predicate. -/
def IsNondegenerateAffineQuadraticKernel
    (u : AffineTwoPointRing A) : Prop :=
  IsAntisymmetricAffineTwoPointFunction A u ∧
    HasExactAffineDiagonalOrder A (affineQuadraticKernelFromSeed A u) 2

/-- Every nondegenerate affine quadratic kernel has exact second-order vanishing along the diagonal. This
merely extracts its *explicit* order condition; the relation with a contact one-form remains unproved. -/
theorem affineQuadraticKernel_exactOrder
    (u : AffineTwoPointRing A)
    (h : IsNondegenerateAffineQuadraticKernel A u) :
    HasExactAffineDiagonalOrder A (affineQuadraticKernelFromSeed A u) 2 := by
  exact h.2

end AffineDiagonal

end LeBrunSalamon.PhaseTwelve

/-!
# Phase 13 -- affine first jets of contact Hamiltonians

The local contact-Hamiltonian correspondence is a FIRST-ORDER operator. This phase states that assertion
on genuine affine rings and at genuine complex-valued points, rather than postulating a jet-to-tangent
map. These are proof obligations, not proved assertions; `sorry` is visible.
-/

namespace LeBrunSalamon.PhaseThirteen

open LeBrunSalamon.PhaseOne
open LeBrunSalamon.PhaseFour
open LeBrunSalamon.PhaseNine
open LeBrunSalamon.PhaseEleven

variable {A : Type*} [CommRing A] [Algebra ℂ A]

/-! ## 13A. First-order local rings and derivations at complex points -/

/-- The genuine maximal ideal of a complex-valued affine point. -/
noncomputable abbrev affinePointIdeal
    (p : A →ₐ[ℂ] ℂ) : Ideal A :=
  RingHom.ker p.toRingHom

/-- The first infinitesimal neighbourhood of an affine complex point: `A / m_p²`. This is the *ring of
first jets at p*, not the full space of jets of an arbitrary line bundle. -/
noncomputable abbrev affineFirstJetAlgebra
    (p : A →ₐ[ℂ] ℂ) :=
  A ⧸ ((affinePointIdeal p) ^ 2)

/-- Restrict a regular function to the actual first-order fat point. -/
noncomputable def affineFirstJet
    (p : A →ₐ[ℂ] ℂ) (f : A) : affineFirstJetAlgebra p :=
  (Ideal.Quotient.mk ((affinePointIdeal p) ^ 2)) f

/-- Equality of first jets is congruence modulo `m_p²`. -/
def SameAffineFirstJet
    (p : A →ₐ[ℂ] ℂ) (f g : A) : Prop :=
  f - g ∈ (affinePointIdeal p) ^ 2

/- Source-only Phase 3 integration: affine_firstjet_followups_1. -/
noncomputable section
set_option autoImplicit false
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseFour LeBrunSalamon.PhaseNine
variable {A : Type*} [CommRing A] [Algebra ℂ A]
open LeBrunSalamon.PhaseEleven

namespace AffineFirstJetProofCandidate

theorem derivation_vanishes_on_square_of_pointIdeal_proved
    (p : A →ₐ[ℂ] ℂ) (V : AffineVectorFields A) (f : A)
    (hf : f ∈ (affinePointIdeal p) ^ 2) :
    p (V f) = 0 := by
  rw [pow_two] at hf
  refine Submodule.mul_induction_on hf ?_ ?_
  · intro a ha b hb
    have ha0 : p a = 0 := ha
    have hb0 : p b = 0 := hb
    rw [Derivation.leibniz]
    simp only [smul_eq_mul, map_add, map_mul, ha0, hb0, zero_mul, zero_add]
  · intro a b ha hb
    simp only [map_add, ha, hb, zero_add]

theorem sameAffineFirstJet_same_value_proved
    (p : A →ₐ[ℂ] ℂ) (f g : A)
    (hfg : SameAffineFirstJet p f g) :
    p f = p g := by
  have hmem : f - g ∈ affinePointIdeal p :=
    (Ideal.pow_le_self (I := affinePointIdeal p) (by decide : (2 : ℕ) ≠ 0)) hfg
  exact (RingHom.sub_mem_ker_iff p.toRingHom).mp hmem

theorem affineFirstJet_eq_iff_proved
    (p : A →ₐ[ℂ] ℂ) (f g : A) :
    affineFirstJet p f = affineFirstJet p g ↔
      SameAffineFirstJet p f g := by
  change Ideal.Quotient.mk ((affinePointIdeal p) ^ 2) f =
      Ideal.Quotient.mk ((affinePointIdeal p) ^ 2) g ↔
    f - g ∈ (affinePointIdeal p) ^ 2
  exact Ideal.Quotient.eq

theorem sameAffineFirstJet_same_derivatives_proved
    (p : A →ₐ[ℂ] ℂ) (f g : A)
    (hfg : SameAffineFirstJet p f g) :
    ∀ V : AffineVectorFields A, p (V f) = p (V g) := by
  intro V
  have h := derivation_vanishes_on_square_of_pointIdeal_proved p V (f - g) hfg
  simpa only [map_sub, sub_eq_zero] using h

theorem affineVectorField_evaluatesToPointDerivation_proved
    (p : A →ₐ[ℂ] ℂ) (V : AffineVectorFields A) :
    ∃ D : AffineTangentAt A p,
      ∀ a : A, D.1 a = p (V a) := by
  let D : A →ₗ[ℂ] ℂ := p.toLinearMap.comp V.toLinearMap
  refine ⟨⟨D, ?_⟩, ?_⟩
  · intro a b
    change p (V (a * b)) = p a * p (V b) + p b * p (V a)
    rw [Derivation.leibniz]
    simp only [smul_eq_mul, map_add, map_mul]
  · intro a
    rfl

end AffineFirstJetProofCandidate
end


/-- A derivative of an element of `m_p²` evaluates to zero at `p`.
No nonsingularity hypothesis is needed: this is the Leibniz rule. -/
theorem derivation_vanishes_on_square_of_pointIdeal
    (p : A →ₐ[ℂ] ℂ) (V : AffineVectorFields A) (f : A)
    (hf : f ∈ (affinePointIdeal p) ^ 2) :
    p (V f) = 0 := by
  exact LeBrunSalamon.PhaseThirteen.AffineFirstJetProofCandidate.derivation_vanishes_on_square_of_pointIdeal_proved (p := p) (V := V) (f := f) (hf := hf)

/-- Elements with equal first jets have equal values at the point. -/
theorem sameAffineFirstJet_same_value
    (p : A →ₐ[ℂ] ℂ) (f g : A)
    (hfg : SameAffineFirstJet p f g) :
    p f = p g := by
  exact LeBrunSalamon.PhaseThirteen.AffineFirstJetProofCandidate.sameAffineFirstJet_same_value_proved (p := p) (f := f) (g := g) (hfg := hfg)

/-- First-jet congruence is detected by the quotient map. -/
theorem affineFirstJet_eq_iff
    (p : A →ₐ[ℂ] ℂ) (f g : A) :
    affineFirstJet p f = affineFirstJet p g ↔
      SameAffineFirstJet p f g := by
  exact LeBrunSalamon.PhaseThirteen.AffineFirstJetProofCandidate.affineFirstJet_eq_iff_proved (p := p) (f := f) (g := g)

/-- Agreement of first jets is agreement of *all* derivatives as well as of the value. The converse
requires enough derivations to detect the Zariski cotangent space; it is deliberately not claimed. -/
theorem sameAffineFirstJet_same_derivatives
    (p : A →ₐ[ℂ] ℂ) (f g : A)
    (hfg : SameAffineFirstJet p f g) :
    ∀ V : AffineVectorFields A, p (V f) = p (V g) := by
  exact LeBrunSalamon.PhaseThirteen.AffineFirstJetProofCandidate.sameAffineFirstJet_same_derivatives_proved (p := p) (f := f) (g := g) (hfg := hfg)

/-- Evaluation of a regular vector field at an affine point gives a point derivation. The existence of the
correctly typed point derivation is a theorem obligation here, not a new primitive tangent space. -/
theorem affineVectorField_evaluatesToPointDerivation
    (p : A →ₐ[ℂ] ℂ) (V : AffineVectorFields A) :
    ∃ D : AffineTangentAt A p,
      ∀ a : A, D.1 a = p (V a) := by
  exact LeBrunSalamon.PhaseThirteen.AffineFirstJetProofCandidate.affineVectorField_evaluatesToPointDerivation_proved (p := p) (V := V)

/-! ## 13B. The contact Hamiltonian operator has order one -/

/-- Two affine vector fields have the same Zariski tangent value at `p`
if their evaluations agree on every regular function. -/
def SameAffineVelocityAt
    (p : A →ₐ[ℂ] ℂ)
    (V W : AffineVectorFields A) : Prop :=
  ∀ a : A, p (V a) = p (W a)

/- Source-only Phase 3 integration: affine_hamiltonian_order_followups_1. -/
noncomputable section
set_option autoImplicit false
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseFour LeBrunSalamon.PhaseNine
variable {A : Type*} [CommRing A] [Algebra ℂ A]
open LeBrunSalamon.PhaseEleven

namespace HamiltonianOrderProof

theorem field_add (θ : AffineOneForm A) (hθ : IsAffineContactForm θ) (f g : A) :
    affineContactHamiltonianField θ hθ (f + g) =
      affineContactHamiltonianField θ hθ f + affineContactHamiltonianField θ hθ g := by
  exact PhaseNine.AffineFollowupProofCandidate.inverse_add θ hθ f g

theorem field_sub (θ : AffineOneForm A) (hθ : IsAffineContactForm θ) (f g : A) :
    affineContactHamiltonianField θ hθ (f - g) =
      affineContactHamiltonianField θ hθ f - affineContactHamiltonianField θ hθ g := by
  have h := field_add θ hθ (f - g) g
  rw [sub_add_cancel] at h
  exact (eq_sub_iff_add_eq).mpr h.symm

theorem jacobi_action (θ : AffineOneForm A) (hθ : IsAffineContactForm θ) (f g : A) :
    contactJacobiBracket θ hθ f g =
      affineContactHamiltonianField θ hθ f g - g * reebFromContactHamiltonian θ hθ f := by
  simpa only [affineContactHamiltonianField, jacobiBracket_one_right, mul_neg,
    sub_eq_add_neg] using PhaseNine.AffineFollowupProofCandidate.jacobi_action_formula θ hθ f g

theorem field_apply_eq (θ : AffineOneForm A) (hθ : IsAffineContactForm θ) (f g : A) :
    affineContactHamiltonianField θ hθ f g =
      contactJacobiBracket θ hθ f g + g * reebFromContactHamiltonian θ hθ f := by
  exact (sub_eq_iff_eq_add).mp (jacobi_action θ hθ f g).symm

theorem field_product_apply (θ : AffineOneForm A) (hθ : IsAffineContactForm θ)
    (f g a : A) :
    affineContactHamiltonianField θ hθ (f * g) a =
      f * affineContactHamiltonianField θ hθ g a +
        g * affineContactHamiltonianField θ hθ f a -
          f * g * reebFromContactHamiltonian θ hθ a := by
  rw [field_apply_eq θ hθ (f * g) a,
    contactJacobiBracket_skew θ hθ (f * g) a,
    PhaseNine.AffineFollowupProofCandidate.contactJacobiBracket_product_proved θ hθ a f g,
    jacobiBracket_one_right θ hθ a,
    contactJacobiBracket_skew θ hθ a f, contactJacobiBracket_skew θ hθ a g,
    jacobi_action θ hθ f a, jacobi_action θ hθ g a, Derivation.leibniz]
  simp only [smul_eq_mul]
  ring

theorem field_ideal_order (θ : AffineOneForm A) (hθ : IsAffineContactForm θ)
    (I : Ideal A) (k : ℕ) (f : A) (hf : f ∈ I ^ (k + 1)) (a : A) :
    affineContactHamiltonianField θ hθ f a ∈ I ^ k := by
  induction k generalizing f with
  | zero => simp
  | succ k ih =>
    have hf' : f ∈ I ^ (k + 1) * I := by simpa only [pow_succ] using hf
    refine Submodule.mul_induction_on hf' ?_ ?_
    · intro b hb c hc
      rw [field_product_apply]
      refine (I ^ (k + 1)).sub_mem ((I ^ (k + 1)).add_mem ?_ ?_) ?_
      · exact (I ^ (k + 1)).mul_mem_right (affineContactHamiltonianField θ hθ c a) hb
      · simpa only [pow_succ'] using Ideal.mul_mem_mul hc (ih b hb)
      · exact (I ^ (k + 1)).mul_mem_right (reebFromContactHamiltonian θ hθ a)
          ((I ^ (k + 1)).mul_mem_right c hb)
    · intro b c hb hc
      rw [field_add]
      change affineContactHamiltonianField θ hθ b a +
        affineContactHamiltonianField θ hθ c a ∈ I ^ (k + 1)
      exact (I ^ (k + 1)).add_mem hb hc

theorem contactHamiltonianField_depends_on_firstJet_proved
    (θ : AffineOneForm A) (hθ : IsAffineContactForm θ)
    (p : A →ₐ[ℂ] ℂ) (f g : A)
    (hfg : SameAffineFirstJet p f g) :
    SameAffineVelocityAt p
      (affineContactHamiltonianField θ hθ f)
      (affineContactHamiltonianField θ hθ g) := by
  intro a
  have h : affineContactHamiltonianField θ hθ (f - g) a ∈ affinePointIdeal p := by
    simpa only [pow_one] using field_ideal_order θ hθ (affinePointIdeal p) 1 (f - g) hfg a
  change p (affineContactHamiltonianField θ hθ (f - g) a) = 0 at h
  rw [field_sub] at h
  change p (affineContactHamiltonianField θ hθ f a -
    affineContactHamiltonianField θ hθ g a) = 0 at h
  rw [map_sub] at h
  exact sub_eq_zero.mp h

end HamiltonianOrderProof
end


/-- The value at a point of the contact Hamiltonian field `X_f` depends only on the first jet of `f`. This
is a central local geometric lemma behind the global map from first jets of L to tangent vectors. -/
theorem contactHamiltonianField_depends_on_firstJet
    (θ : AffineOneForm A) (hθ : IsAffineContactForm θ)
    (p : A →ₐ[ℂ] ℂ) (f g : A)
    (hfg : SameAffineFirstJet p f g) :
    SameAffineVelocityAt p
      (affineContactHamiltonianField θ hθ f)
      (affineContactHamiltonianField θ hθ g) := by
  exact LeBrunSalamon.PhaseThirteen.HamiltonianOrderProof.contactHamiltonianField_depends_on_firstJet_proved (θ := θ) (hθ := hθ) (p := p) (f := f) (g := g) (hfg := hfg)

/- Source-only Phase 3 integration: affine_firstjet_followups_2. -/
noncomputable section
set_option autoImplicit false
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseFour LeBrunSalamon.PhaseNine
variable {A : Type*} [CommRing A] [Algebra ℂ A]
open LeBrunSalamon.PhaseEleven

namespace AffineFirstJetProofCandidate

theorem hamiltonianField_eq
    (θ : AffineOneForm A) (hθ : IsAffineContactForm θ) (f : A)
    (V : AffineVectorFields A) (hV : IsAffineContactVectorField θ V)
    (hvalue : θ V = f) :
    affineContactHamiltonianField θ hθ f = V := by
  have h : (contactHamiltonianEquiv θ hθ).symm f =
      (⟨V, hV⟩ : AffineContactVectorFields θ) := by
    apply contactHamiltonian_injective θ hθ
    change θ (affineContactHamiltonianField θ hθ f) = θ V
    exact (affineContactHamiltonianField_value θ hθ f).trans hvalue.symm
  exact congrArg (fun W : AffineContactVectorFields θ => W.1) h

theorem contactHamiltonianField_add_proved
    (θ : AffineOneForm A) (hθ : IsAffineContactForm θ)
    (f g : A) :
    affineContactHamiltonianField θ hθ (f + g) =
      affineContactHamiltonianField θ hθ f +
        affineContactHamiltonianField θ hθ g := by
  apply hamiltonianField_eq θ hθ (f + g)
    (affineContactHamiltonianField θ hθ f + affineContactHamiltonianField θ hθ g)
  · intro u
    rw [add_lie, map_add,
      affineContactHamiltonianField_preserves θ hθ f u,
      affineContactHamiltonianField_preserves θ hθ g u, add_zero]
  · rw [map_add, affineContactHamiltonianField_value θ hθ f,
      affineContactHamiltonianField_value θ hθ g]

theorem contactHamiltonianField_smul_proved
    (θ : AffineOneForm A) (hθ : IsAffineContactForm θ)
    (c : ℂ) (f : A) :
    affineContactHamiltonianField θ hθ (c • f) =
      c • affineContactHamiltonianField θ hθ f := by
  apply hamiltonianField_eq θ hθ (c • f)
    (c • affineContactHamiltonianField θ hθ f)
  · intro u
    rw [smul_lie]
    change (θ.restrictScalars ℂ)
      (c • ⁅affineContactHamiltonianField θ hθ f, u.1⁆) = 0
    rw [map_smul]
    change c • θ ⁅affineContactHamiltonianField θ hθ f, u.1⁆ = 0
    rw [affineContactHamiltonianField_preserves θ hθ f u, smul_zero]
  · change (θ.restrictScalars ℂ)
      (c • affineContactHamiltonianField θ hθ f) = c • f
    rw [map_smul]
    change c • θ (affineContactHamiltonianField θ hθ f) = c • f
    rw [affineContactHamiltonianField_value θ hθ f]

end AffineFirstJetProofCandidate
end


/-- Contact Hamiltonian fields depend additively on the Hamiltonian.
This needs the additivity of the contact-Hamiltonian equivalence. -/
theorem contactHamiltonianField_add
    (θ : AffineOneForm A) (hθ : IsAffineContactForm θ)
    (f g : A) :
    affineContactHamiltonianField θ hθ (f + g) =
      affineContactHamiltonianField θ hθ f +
        affineContactHamiltonianField θ hθ g := by
  exact LeBrunSalamon.PhaseThirteen.AffineFirstJetProofCandidate.contactHamiltonianField_add_proved (θ := θ) (hθ := hθ) (f := f) (g := g)

/-- Contact Hamiltonian fields are complex-linear in the Hamiltonian.
They are not, in general, linear over the function ring `A`. -/
theorem contactHamiltonianField_smul
    (θ : AffineOneForm A) (hθ : IsAffineContactForm θ)
    (c : ℂ) (f : A) :
    affineContactHamiltonianField θ hθ (c • f) =
      c • affineContactHamiltonianField θ hθ f := by
  exact LeBrunSalamon.PhaseThirteen.AffineFirstJetProofCandidate.contactHamiltonianField_smul_proved (θ := θ) (hθ := hθ) (c := c) (f := f)

/-- The characteristic one-dimensional kernel of the map from Hamiltonian first jets to tangent vectors is
described by the contact form: f(p)=0 and df_p is a scalar multiple of θ_p. The condition itself is a
genuine equation on affine derivations. -/
def IsCharacteristicContactJet
    (θ : AffineOneForm A) (p : A →ₐ[ℂ] ℂ) (f : A) : Prop :=
  p f = 0 ∧
    ∃ c : ℂ, ∀ V : AffineVectorFields A,
      p (V f) = c * p (θ V)

/- Source-only Phase 3 integration: affine_velocity. -/
noncomputable section
set_option autoImplicit false
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseFour LeBrunSalamon.PhaseNine
open LeBrunSalamon.PhaseEleven
variable {A : Type*} [CommRing A] [Algebra ℂ A]

namespace AffineVelocityProof

theorem point_zero_differential (p : A →ₐ[ℂ] ℂ) (V : AffineVectorFields A)
    (hV : ∀ a : A, p (V a) = 0) (differential : KaehlerDifferential ℂ A) :
    p (V.liftKaehlerDifferential differential) = 0 := by
  have hmem : differential ∈ Submodule.span A (Set.range (KaehlerDifferential.D ℂ A)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hmem
  · rintro _ ⟨a, rfl⟩
    simpa only [Derivation.liftKaehlerDifferential_comp_D] using hV a
  · simp only [map_zero]
  · intro x y _ _ hx hy
    simp only [map_add, hx, hy, zero_add]
  · intro a x _ hx
    simp only [map_smul, smul_eq_mul, map_mul, hx, mul_zero]

theorem point_zero_covector
    [Module.Finite A (KaehlerDifferential ℂ A)]
    [Module.Projective A (KaehlerDifferential ℂ A)]
    (p : A →ₐ[ℂ] ℂ) (V : AffineVectorFields A)
    (hV : ∀ a : A, p (V a) = 0) (α : AffineOneForm A) : p (α V) = 0 := by
  let e : Module.Dual A (KaehlerDifferential ℂ A) ≃ₗ[A] AffineVectorFields A :=
    KaehlerDifferential.linearMapEquivDerivation ℂ A
  let φ : Module.Dual A (Module.Dual A (KaehlerDifferential ℂ A)) :=
    α.comp e.toLinearMap
  let differential : KaehlerDifferential ℂ A :=
    (Module.evalEquiv A (KaehlerDifferential ℂ A)).symm φ
  have he : e V.liftKaehlerDifferential = V := e.apply_symm_apply V
  have h : V.liftKaehlerDifferential differential = α V := by
    have h' := Module.apply_evalEquiv_symm_apply A (KaehlerDifferential ℂ A)
      V.liftKaehlerDifferential φ
    change V.liftKaehlerDifferential differential = α (e V.liftKaehlerDifferential) at h'
    simpa only [he] using h'
  rw [← h]
  exact point_zero_differential p V hV differential

def exteriorCovector (θ : AffineOneForm A) (V : AffineVectorFields A) :
    AffineOneForm A where
  toFun W := affineExteriorDerivativeValue θ W V
  map_add' X Y := by
    change X (θ V) + Y (θ V) - V (θ (X + Y)) - θ ⁅X + Y, V⁆ =
      (X (θ V) - V (θ X) - θ ⁅X, V⁆) +
        (Y (θ V) - V (θ Y) - θ ⁅Y, V⁆)
    simp only [map_add, add_lie]
    ring
  map_smul' a W := by
    change affineExteriorDerivativeValue θ (a • W) V =
      a * affineExteriorDerivativeValue θ W V
    exact affineExteriorDerivative_smul_left θ a W V

def horizontalProjection (θ : AffineOneForm A) (R : AffineVectorFields A)
    (hR : θ R = 1) : AffineVectorFields A →ₗ[A] AffineDistribution θ where
  toFun V := ⟨V - θ V • R, by
    change θ (V - θ V • R) = 0
    simp only [map_sub, map_smul, hR, smul_eq_mul, mul_one, sub_self]⟩
  map_add' V W := by
    apply Subtype.ext
    change V + W - θ (V + W) • R = (V - θ V • R) + (W - θ W • R)
    rw [map_add, add_smul]
    abel
  map_smul' a V := by
    apply Subtype.ext
    change a • V - θ (a • V) • R = a • (V - θ V • R)
    simp only [map_smul, smul_sub, smul_smul, smul_eq_mul]

theorem horizontalProjection_subtype (θ : AffineOneForm A)
    (R : AffineVectorFields A) (hR : θ R = 1) :
    (horizontalProjection θ R hR).comp (LinearMap.ker θ).subtype = LinearMap.id := by
  apply LinearMap.ext
  intro u
  apply Subtype.ext
  change (u : AffineVectorFields A) - θ u.val • R = u.val
  have hu : θ u.val = 0 := u.property
  rw [hu, zero_smul, sub_zero]

theorem vectorFields_reflexive
    [Module.Finite A (KaehlerDifferential ℂ A)]
    [Module.Projective A (KaehlerDifferential ℂ A)] :
    Module.IsReflexive A (AffineVectorFields A) := by
  exact Module.equiv (KaehlerDifferential.linearMapEquivDerivation ℂ A)

theorem distribution_reflexive [Module.IsReflexive A (AffineVectorFields A)]
    (θ : AffineOneForm A) (R : AffineVectorFields A) (hR : θ R = 1) :
    Module.IsReflexive A (AffineDistribution θ) :=
  Module.IsReflexive.of_split (LinearMap.ker θ).subtype
    (horizontalProjection θ R hR) (horizontalProjection_subtype θ R hR)

theorem perfectPair_point_zero
    {F : Type*} [AddCommGroup F] [Module A F] [Module.IsReflexive A F]
    (p : A →ₐ[ℂ] ℂ) (b : F →ₗ[A] Module.Dual A F)
    (hb : Function.Bijective b) (x : F)
    (hx : ∀ u : F, p (b x u) = 0) (ℓ : F →ₗ[A] A) : p (ℓ x) = 0 := by
  let e : F ≃ₗ[A] Module.Dual A F := LinearEquiv.ofBijective b hb
  let φ : Module.Dual A (Module.Dual A F) := ℓ.comp e.symm.toLinearMap
  let u : F := (Module.evalEquiv A F).symm φ
  have h := Module.apply_evalEquiv_symm_apply A F (b x) φ
  change b x u = ℓ (e.symm (b x)) at h
  have he : e.symm (b x) = x := e.symm_apply_apply x
  rw [he] at h
  rw [← h]
  exact hx u

theorem horizontal_hamiltonian_levi (θ : AffineOneForm A)
    (hθ : IsAffineContactForm θ) (R : AffineVectorFields A)
    (hR : IsAffineReebField θ R)
    (b : LineValuedBilinearForm A (AffineDistribution θ) A)
    (hb : ∀ u v : AffineDistribution θ, b u v = affineLeviValue θ u v)
    (f : A) (u : AffineDistribution θ) :
    b (horizontalProjection θ R hR.1 (affineContactHamiltonianField θ hθ f)) u =
      u.val f := by
  let X : AffineVectorFields A := affineContactHamiltonianField θ hθ f
  have hvalue : θ X = f := affineContactHamiltonianField_value θ hθ f
  have hX : θ ⁅X, u.val⁆ = 0 := affineContactHamiltonianField_preserves θ hθ f u
  have hu : θ u.val = 0 := u.property
  have hRu : θ ⁅R, u.val⁆ = 0 := by
    rw [AffineReebProofCandidate.affineReeb_bracket_value θ R hR u.val,
      hu, map_zero]
  rw [hb]
  change θ ⁅X - θ X • R, u.val⁆ = u.val f
  rw [hvalue, sub_lie, AffineCartanProofCandidate.derivation_bracket_smul_left]
  simp only [map_sub, map_smul, smul_eq_mul, hX, hRu, hR.1,
    mul_zero, mul_one, zero_sub, neg_neg]

theorem velocityZero_implies_characteristic
    [Module.Finite A (KaehlerDifferential ℂ A)]
    [Module.Projective A (KaehlerDifferential ℂ A)]
    (θ : AffineOneForm A) (hθ : IsAffineContactForm θ)
    (p : A →ₐ[ℂ] ℂ) (f : A)
    (hzero : ∀ a : A, p ((affineContactHamiltonianField θ hθ f) a) = 0) :
    IsCharacteristicContactJet θ p f := by
  let X : AffineVectorFields A := affineContactHamiltonianField θ hθ f
  let R : AffineVectorFields A := reebFromContactHamiltonian θ hθ
  have hvalue : θ X = f := affineContactHamiltonianField_value θ hθ f
  have hf : p f = 0 := by
    have h := point_zero_covector p X hzero θ
    simpa only [hvalue] using h
  refine ⟨hf, p (R f), ?_⟩
  intro V
  have hext : p (affineExteriorDerivativeValue θ X V) = 0 :=
    point_zero_covector p X hzero (exteriorCovector θ V)
  have hcart := (affineCartanFormula θ X V).symm
  rw [hvalue] at hcart
  have hlie : affineLieDerivativeValue θ X V = R f * θ V :=
    affineHamiltonian_lieDerivative θ hθ f V
  have h := congrArg p (hcart.trans hlie)
  simpa only [map_add, map_mul, hext, zero_add] using h

theorem characteristic_implies_velocityZero
    [Module.Finite A (KaehlerDifferential ℂ A)]
    [Module.Projective A (KaehlerDifferential ℂ A)]
    (θ : AffineOneForm A) (hθ : IsAffineContactForm θ)
    (p : A →ₐ[ℂ] ℂ) (f : A) (hf : IsCharacteristicContactJet θ p f) :
    ∀ a : A, p ((affineContactHamiltonianField θ hθ f) a) = 0 := by
  obtain ⟨hf, c, hdf⟩ := hf
  let X : AffineVectorFields A := affineContactHamiltonianField θ hθ f
  let R : AffineVectorFields A := reebFromContactHamiltonian θ hθ
  have hR : IsAffineReebField θ R := reebFromContactHamiltonian_isReeb θ hθ
  let z : AffineDistribution θ := horizontalProjection θ R hR.1 X
  letI : Module.IsReflexive A (AffineVectorFields A) := vectorFields_reflexive
  letI : Module.IsReflexive A (AffineDistribution θ) := distribution_reflexive θ R hR.1
  obtain ⟨b, hb, hbrep⟩ := hθ.2
  have hz : ∀ u : AffineDistribution θ, p (b z u) = 0 := by
    intro u
    have hbu : b z u = u.val f := horizontal_hamiltonian_levi θ hθ R hR b hbrep f u
    have hu : θ u.val = 0 := u.property
    rw [hbu, hdf u.val, hu, map_zero, mul_zero]
  intro a
  let ℓ : AffineDistribution θ →ₗ[A] A :=
    { toFun := fun u => u.val a
      map_add' := fun u v => rfl
      map_smul' := fun r u => rfl }
  have hza : p (z.val a) = 0 := perfectPair_point_zero p b hb.2 z hz ℓ
  have hvalue : θ X = f := affineContactHamiltonianField_value θ hθ f
  have hzvalue : z.val a = X a - f * R a := by
    change X a - θ X * R a = X a - f * R a
    rw [hvalue]
  rw [hzvalue, map_sub, map_mul, hf, zero_mul, sub_zero] at hza
  exact hza

theorem contactHamiltonianVelocity_zero_iff
    [Module.Finite A (KaehlerDifferential ℂ A)]
    [Module.Projective A (KaehlerDifferential ℂ A)]
    (θ : AffineOneForm A) (hθ : IsAffineContactForm θ)
    (p : A →ₐ[ℂ] ℂ) (f : A) :
    (∀ a : A, p ((affineContactHamiltonianField θ hθ f) a) = 0) ↔
      IsCharacteristicContactJet θ p f := by
  exact ⟨velocityZero_implies_characteristic θ hθ p f,
    characteristic_implies_velocityZero θ hθ p f⟩

end AffineVelocityProof
end


/- Contact Hamiltonian fields have zero value at `p` exactly for characteristic Hamiltonian first jets.
The local perfect Levi pairing is essential; this does *not* assert injectivity of the first-jet map. -/
/-- AUDIT REPAIR: the implication from vanishing as a point derivation to vanishing of all covector
evaluations uses finite projectivity of Ω¹. These hypotheses hold on smooth affine charts; they are not
consequences of the bare definition of an arbitrary complex algebra. -/
theorem contactHamiltonianVelocity_zero_iff
    [Module.Finite A (KaehlerDifferential ℂ A)]
    [Module.Projective A (KaehlerDifferential ℂ A)]
    (θ : AffineOneForm A) (hθ : IsAffineContactForm θ)
    (p : A →ₐ[ℂ] ℂ) (f : A) :
    (∀ a : A, p ((affineContactHamiltonianField θ hθ f) a) = 0) ↔
      IsCharacteristicContactJet θ p f := by
  exact LeBrunSalamon.PhaseThirteen.AffineVelocityProof.contactHamiltonianVelocity_zero_iff (θ := θ) (hθ := hθ) (p := p) (f := f)

/- Source-only Phase 3 integration: affine_firstjet_followups_3. -/
noncomputable section
set_option autoImplicit false
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseFour LeBrunSalamon.PhaseNine
variable {A : Type*} [CommRing A] [Algebra ℂ A]
open LeBrunSalamon.PhaseEleven

namespace AffineFirstJetProofCandidate

theorem squarePointIdeal_characteristicContactJet_proved
    (θ : AffineOneForm A) (p : A →ₐ[ℂ] ℂ) (f : A)
    (hf : f ∈ (affinePointIdeal p) ^ 2) :
    IsCharacteristicContactJet θ p f := by
  refine ⟨?_, ⟨0, ?_⟩⟩
  · have hmem : f ∈ affinePointIdeal p :=
      (Ideal.pow_le_self (I := affinePointIdeal p) (by decide : (2 : ℕ) ≠ 0)) hf
    exact hmem
  · intro V
    rw [derivation_vanishes_on_square_of_pointIdeal_proved p V f hf, zero_mul]

end AffineFirstJetProofCandidate
end


/-- A function vanishing to second order at p represents the zero
Hamiltonian first jet, hence a characteristic first jet. -/
theorem squarePointIdeal_characteristicContactJet
    (θ : AffineOneForm A) (p : A →ₐ[ℂ] ℂ) (f : A)
    (hf : f ∈ (affinePointIdeal p) ^ 2) :
    IsCharacteristicContactJet θ p f := by
  exact LeBrunSalamon.PhaseThirteen.AffineFirstJetProofCandidate.squarePointIdeal_characteristicContactJet_proved (θ := θ) (p := p) (f := f) (hf := hf)

end LeBrunSalamon.PhaseThirteen

/-!
# Phase 14 -- genuine slices of a global two-point kernel

An arbitrary O-module on X×X is NOT L⊠L. Nevertheless actual slices, restriction of global sections,
exchange, and diagonal vanishing can be formulated using the existing mathlib pullback functor. A
trivialization of L at a chosen complex point is represented by an explicit isomorphism on that slice; it
is not silently canonical.

IMPORTANT: the restriction of an order-two kernel to a fixed-point slice has ZERO FIRST JET at the slicing
point. Any proof claiming that these slices *alone* give first-jet generation must therefore be corrected.
-/

namespace LeBrunSalamon.PhaseFourteen

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open LeBrunSalamon.PhaseOne
open LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseEight

/-! ## 14A. Geometric slice maps X -> X×_C X -/

/-- The slice `y ↦ (y,x)` associated to a specified complex point `x : Spec(C) -> X`. The laws force the
chosen scheme map to be the actual slice by the universal property of the fibre product. -/
structure TwoPointSliceAt {d : ℕ}
    (X : SmoothProperComplexVariety d)
    (x : ComplexPoint X) where
  map : X.scheme ⟶ SelfProduct X.structureMap
  firstLaw :
    map ≫ firstProjection X.structureMap = 𝟙 X.scheme
  secondLaw :
    map ≫ secondProjection X.structureMap = X.structureMap ≫ x.map

/-- A canonical slice exists for every complex point. The proof is
an application of the universal property of the scheme fibre square. -/
theorem twoPointSlice_exists {d : ℕ}
    (X : SmoothProperComplexVariety d)
    (x : ComplexPoint X) :
    Nonempty (TwoPointSliceAt X x) := by
  have h : (𝟙 X.scheme) ≫ X.structureMap =
      (X.structureMap ≫ x.map) ≫ X.structureMap := by
    simp only [Category.id_comp, Category.assoc, x.overC, Category.comp_id]
  refine ⟨{ map := pullback.lift (𝟙 X.scheme) (X.structureMap ≫ x.map) h
            firstLaw := ?_
            secondLaw := ?_ }⟩
  · exact pullback.lift_fst _ _ _
  · exact pullback.lift_snd _ _ _

/-- A choice of the canonical slice, resting on the above existence theorem. In a compiled development it
would be preferable to use `pullback.lift` directly and prove the projection laws by `simp`. -/
noncomputable def canonicalTwoPointSlice {d : ℕ}
    (X : SmoothProperComplexVariety d)
    (x : ComplexPoint X) : TwoPointSliceAt X x :=
  Classical.choice (twoPointSlice_exists X x)

/-! ## 14B. Restricting a twisted two-point section -/

/-- A trivialization of the second, fixed, line-bundle factor along a slice. This is the geometric input
necessary to identify a section of L⊠L with a section of L. For an actual external square such a
trivialization exists over a C-point but is not canonical. A general chosen sheaf `E` on X×X need not
admit any such isomorphism. -/
structure TrivializedKernelSlice {d : ℕ}
    (X : SmoothProperComplexVariety d)
    (L : LineBundle X.scheme)
    (E : OModule (SelfProduct X.structureMap))
    (x : ComplexPoint X) where
  slice : TwoPointSliceAt X x
  onUnit :
    (Scheme.Modules.pullback slice.map).obj
      (SheafOfModules.unit (SelfProduct X.structureMap).ringCatSheaf) ≅
        SheafOfModules.unit X.scheme.ringCatSheaf
  onLine :
    (Scheme.Modules.pullback slice.map).obj E ≅ L.sheaf

/-- The actual restriction of a global two-point section to a slice, transported through the explicitly
supplied unit and line-bundle isomorphisms. Its result is an honest global section of L. -/
noncomputable def kernelSectionOnSlice {d : ℕ}
    (X : SmoothProperComplexVariety d)
    (L : LineBundle X.scheme)
    (E : OModule (SelfProduct X.structureMap))
    (x : ComplexPoint X)
    (S : TrivializedKernelSlice X L E x)
    (B : AlgebraicSection E) : AlgebraicSection L.sheaf :=
  S.onUnit.inv ≫
    (Scheme.Modules.pullback S.slice.map).map B ≫
      S.onLine.hom

/-- A proposed global quadratic kernel with all the properties that
can currently be checked using the *actual* scheme diagonal and swap.

The word CANDIDATE matters: this does not yet establish that `E` is
canonically `L⊠L`, nor that the quadratic symbol is `θ⊗θ`.
`exactOrderTwo` excludes the identically zero section. -/
structure SlicedQuadraticKernelCandidate {d : ℕ}
    (X : SmoothProperComplexVariety d)
    [AlgebraicGeometry.IsSeparated X.structureMap]
    (L : LineBundle X.scheme) where
  externalSheafCandidate : OModule (SelfProduct X.structureMap)
  exchange : TwoPointExchangeIdentification
    X.structureMap externalSheafCandidate
  «section» : AlgebraicSection externalSheafCandidate
  symmetric : IsSymmetricUnderExchange
    X.structureMap externalSheafCandidate «section» exchange
  exactOrderTwo : HasExactDiagonalOrder
    X.structureMap externalSheafCandidate «section» 2
  slices : ∀ x : ComplexPoint X,
    TrivializedKernelSlice X L externalSheafCandidate x

/-- A chosen quadratic kernel's section restricted to `(y,x)`, with
a trivialization of the contact line at `x`. -/
noncomputable def SlicedQuadraticKernelCandidate.at {d : ℕ}
    {X : SmoothProperComplexVariety d}
    [AlgebraicGeometry.IsSeparated X.structureMap]
    {L : LineBundle X.scheme}
    (B : SlicedQuadraticKernelCandidate X L)
    (x : ComplexPoint X) : AlgebraicSection L.sheaf :=
  kernelSectionOnSlice X L B.externalSheafCandidate x
    (B.slices x) B.«section»

set_option backward.isDefEq.respectTransparency false in
/-- A quadratic kernel is nonzero, since it has exact diagonal order 2.
This is a useful sanity check against vacuous kernel choices. -/
theorem slicedQuadraticKernel_nonzero {d : ℕ}
    (X : SmoothProperComplexVariety d)
    [AlgebraicGeometry.IsSeparated X.structureMap]
    (L : LineBundle X.scheme)
    (B : SlicedQuadraticKernelCandidate X L) :
    B.«section» ≠ 0 := by
  intro hzero
  apply B.exactOrderTwo.2
  change (Scheme.Modules.pullback
    (diagonalPowerInclusion X.structureMap (2 + 1))).map B.«section» = 0
  rw [hzero]
  exact Functor.map_zero (Scheme.Modules.pullback
    (diagonalPowerInclusion X.structureMap (2 + 1))) _ _

/- Source-only Phase 3 integration: sliced_quadratic_restriction. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree LeBrunSalamon.PhaseEight

namespace SliceRestrictionProof

theorem pullback_comp_zero_iff {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    {E F : OModule Z} (a : E ⟶ F) :
    (Scheme.Modules.pullback (f ≫ g)).map a = 0 ↔
      (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback g).map a) = 0 := by
  let e := Scheme.Modules.pullbackComp f g
  have he := e.hom.naturality a
  simp only [Functor.comp_map] at he
  constructor
  · intro h
    apply (cancel_mono (e.hom.app F)).1
    rw [zero_comp, he]
    change e.hom.app E ≫ (Scheme.Modules.pullback (f ≫ g)).map a = 0
    rw [h, comp_zero]
  · intro h
    apply (cancel_epi (e.hom.app E)).1
    rw [comp_zero, ← he]
    change (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback g).map a) ≫ _ = 0
    rw [h, zero_comp]

theorem ideal_power_le_map {X Y : Scheme} (f : X ⟶ Y) [IsAffineHom f]
    (I : X.IdealSheafData) (J : Y.IdealSheafData) (h : J ≤ I.map f) (k : ℕ) :
    J ^ k ≤ (I ^ k).map f := by
  intro U
  have hU : J.ideal U ≤ (I.map f).ideal U := h U
  rw [Scheme.IdealSheafData.ideal_map_of_isAffineHom] at hU
  rw [Scheme.IdealSheafData.ideal_map_of_isAffineHom]
  exact (Ideal.pow_right_mono hU k).trans
    (Ideal.le_comap_pow (f := (f.app U).hom)
      (K := I.ideal ⟨f ⁻¹ᵁ U, U.2.preimage f⟩) k)

theorem point_slice_diagonal {d : ℕ} (X : SmoothProperComplexVariety d)
    (x : ComplexPoint X) (S : TwoPointSliceAt X x) :
    x.map ≫ S.map = x.map ≫ diagonal X.structureMap := by
  apply pullback.hom_ext
  · simp only [Category.assoc, S.firstLaw, pullback.diagonal_fst, Category.comp_id]
  · simp only [Category.assoc, S.secondLaw, pullback.diagonal_snd, Category.comp_id]
    rw [← Category.assoc, x.overC, Category.id_comp]

theorem slicedQuadraticKernel_firstJet_zero {d : ℕ}
    (X : SmoothProperComplexVariety d) [IsSeparated X.structureMap]
    (L : LineBundle X.scheme) (B : SlicedQuadraticKernelCandidate X L)
    (x : ComplexPoint X) :
    jetRestrictionAt x L.sheaf 1 (B.at x) = 0 := by
  let S := B.slices x
  letI : IsAffineHom (S.slice.map ≫ firstProjection X.structureMap) := by
    rw [S.slice.firstLaw]
    infer_instance
  letI : IsAffineHom S.slice.map :=
    IsAffineHom.of_comp S.slice.map (firstProjection X.structureMap)
  have hI : diagonalIdeal X.structureMap ≤ (pointIdeal x).map S.slice.map := by
    change (diagonal X.structureMap).ker ≤ x.map.ker.map S.slice.map
    rw [Scheme.IdealSheafData.map_ker, point_slice_diagonal X x S.slice]
    exact Scheme.Hom.le_ker_comp x.map (diagonal X.structureMap)
  have hpow : diagonalIdeal X.structureMap ^ 2 ≤ ((pointIdeal x) ^ 2).map S.slice.map :=
    ideal_power_le_map S.slice.map (pointIdeal x) (diagonalIdeal X.structureMap) hI 2
  let j : pointPowerSubscheme x 2 ⟶ diagonalPowerSubscheme X.structureMap 2 :=
    Scheme.IdealSheafData.subschemeMap ((pointIdeal x) ^ 2)
      (diagonalIdeal X.structureMap ^ 2) S.slice.map hpow
  have hfac : j ≫ diagonalPowerInclusion X.structureMap 2 =
      pointPowerInclusion x 2 ≫ S.slice.map :=
    Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ hpow
  have hb : (Scheme.Modules.pullback (diagonalPowerInclusion X.structureMap 2)).map
      B.«section» = 0 := B.exactOrderTwo.1
  have hj : (Scheme.Modules.pullback (j ≫ diagonalPowerInclusion X.structureMap 2)).map
      B.«section» = 0 := by
    apply (pullback_comp_zero_iff j (diagonalPowerInclusion X.structureMap 2) B.«section»).mpr
    rw [hb, Functor.map_zero]
  have hmid : (Scheme.Modules.pullback (pointPowerInclusion x 2)).map
      ((Scheme.Modules.pullback S.slice.map).map B.«section») = 0 := by
    apply (pullback_comp_zero_iff (pointPowerInclusion x 2) S.slice.map B.«section»).mp
    rw [← hfac]
    exact hj
  change (Scheme.Modules.pullback (pointPowerInclusion x 2)).map
    (S.onUnit.inv ≫ (Scheme.Modules.pullback S.slice.map).map B.«section» ≫ S.onLine.hom) = 0
  simp only [Functor.map_comp, hmid, zero_comp, comp_zero]

end SliceRestrictionProof
end


/-- Fundamental restriction statement: for a section of an external square vanishing to order two along
the diagonal, its slice at x vanishes to order two at x. In particular the FIRST JET IS ZERO. This applies
to the explicitly trivialized candidate because the isomorphism of line sheaves preserves zero sections.
-/
theorem slicedQuadraticKernel_firstJet_zero {d : ℕ}
    (X : SmoothProperComplexVariety d)
    [AlgebraicGeometry.IsSeparated X.structureMap]
    (L : LineBundle X.scheme)
    (B : SlicedQuadraticKernelCandidate X L)
    (x : ComplexPoint X) :
    jetRestrictionAt x L.sheaf 1 (B.at x) = 0 := by
  exact SliceRestrictionProof.slicedQuadraticKernel_firstJet_zero X L B x

/-- In particular, a fixed-point slice vanishes at the slicing point.
The first-jet statement above is stronger. -/
theorem slicedQuadraticKernel_value_zero {d : ℕ}
    (X : SmoothProperComplexVariety d)
    [AlgebraicGeometry.IsSeparated X.structureMap]
    (L : LineBundle X.scheme)
    (B : SlicedQuadraticKernelCandidate X L)
    (x : ComplexPoint X) :
    jetRestrictionAt x L.sheaf 0 (B.at x) = 0 := by
  have hpow : (pointIdeal x) ^ 2 ≤ (pointIdeal x) ^ 1 := by
    intro U
    exact Ideal.pow_le_pow_right (I := (pointIdeal x).ideal U) (by decide : 1 ≤ 2)
  let i : pointPowerSubscheme x 1 ⟶ pointPowerSubscheme x 2 :=
    Scheme.IdealSheafData.inclusion hpow
  have hfac : i ≫ pointPowerInclusion x 2 = pointPowerInclusion x 1 :=
    Scheme.IdealSheafData.inclusion_subschemeι hpow
  have hfirst : (Scheme.Modules.pullback (pointPowerInclusion x 2)).map (B.at x) = 0 :=
    slicedQuadraticKernel_firstJet_zero X L B x
  have hi : (Scheme.Modules.pullback i).map
      ((Scheme.Modules.pullback (pointPowerInclusion x 2)).map (B.at x)) = 0 := by
    rw [hfirst, Functor.map_zero]
  have hcomp : (Scheme.Modules.pullback (i ≫ pointPowerInclusion x 2)).map (B.at x) = 0 :=
    (SliceRestrictionProof.pullback_comp_zero_iff i
      (pointPowerInclusion x 2) (B.at x)).mpr hi
  change (Scheme.Modules.pullback (pointPowerInclusion x 1)).map (B.at x) = 0
  rw [← hfac]
  exact hcomp

end LeBrunSalamon.PhaseFourteen

/-!
# Phase 15 -- geometric evaluation and conic-family proof obligations

This is the next non-formal step of the proof: produce families of very-free degree-two curves from nodal
unions of contact lines, and control their two-point evaluation. The structures below name the correct
geometric data. They do NOT assert that every contact Fano has such a family; producing it is the
substantial smoothing theorem.
-/

namespace LeBrunSalamon.PhaseFifteen

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open LeBrunSalamon.PhaseOne
open LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseSeven
open LeBrunSalamon.PhaseEight

/-- The two-point evaluation map of a genuinely marked proper flat family can hit every pair of DISTINCT
complex points. This is stronger than Zariski dominance; it is NOT asserted for arbitrary contact Fano
varieties, and it deliberately excludes the diagonal. Embedded conics cannot meet the same target point at
two different marked source points. -/
def HasOffDiagonalMarkedTwoPointEvaluation {d : ℕ}
    {X : SmoothProperComplexVariety d}
    {F : ProperFlatFamilyOfMaps X}
    (marks : TwoMarkedFamilyOfMaps F) : Prop :=
  ∀ x y : ComplexPoint X, x.map ≠ y.map →
    ∃ b : ParameterPoint F,
      b.map ≫ marks.first.evaluation = x.map ∧
      b.map ≫ marks.second.evaluation = y.map

/-- Any two DISTINCT complex points are joined by a parametrized very free rational curve with two
distinct marked preimages. No claim for the diagonal is built in: requiring the SAME x at two distinct
marks would exclude every family consisting of embedded curves. -/
def IsOffDiagonalVeryFreeConnected
    (P : ProjectiveLineOverC) {d : ℕ}
    (X : SmoothProperComplexVariety d)
    (TX : AlgebraicVectorBundle X.scheme d) : Prop :=
  ∀ x y : ComplexPoint X, x.map ≠ y.map →
    ∃ f : TwoPointedVeryFreeCurve P X TX,
      f.marked.first.map ≫ f.marked.curve.map = x.map ∧
      f.marked.second.map ≫ f.marked.curve.map = y.map

/-- A flat family whose complex fibres have been identified with VERY FREE rational curves of CONTACT
DEGREE TWO. The `fibreIdentifies` equality checks the actual map to X, not just an abstract isomorphism of
source curves. The `overC` equality checks the base structures. No universal stable-map space is
postulated. -/
structure VeryFreeContactConicFamilyCandidate
    (P : ProjectiveLineOverC) (n : ℕ)
    (X : ContactCandidate n)
    (O2 : LineBundle ProjectiveLine) where
  family : ProperFlatFamilyOfMaps X.variety
  marks : TwoMarkedFamilyOfMaps family
  fibreModels : ∀ b : ParameterPoint family,
    ∃ e : fibreScheme family b ≅ ProjectiveLine,
    ∃ f : VeryFreeContactConicCandidate P n X O2,
      e.hom ≫ P.structureMap =
        pullback.snd family.projection b.map ∧
      e.inv ≫ fibreEvaluation family b = f.conic.curve.map

/-- An off-diagonal covering family of parametrized very-free contact conics. In the actual proof, generic
dominance of the two-point evaluation may be enough, and would be strictly weaker than this surjectivity
condition. It must be proved separately. -/
def VeryFreeContactConicFamilyCandidate.CoversDistinctPointPairs
    {P : ProjectiveLineOverC} {n : ℕ}
    {X : ContactCandidate n} {O2 : LineBundle ProjectiveLine}
    (F : VeryFreeContactConicFamilyCandidate P n X O2) : Prop :=
  HasOffDiagonalMarkedTwoPointEvaluation F.marks

/-- If a single family covers all pairs of distinct complex points and all its fibres are very free
rational conics, then the variety is off-diagonally very-free-connected. The proof constructs points of P¹
from the marked family sections using the fibre-product universal property, then uses `fibreModels`. -/
theorem conicFamily_covering_implies_offDiagonalVeryFreeConnected
    (P : ProjectiveLineOverC) (n : ℕ)
    (X : ContactCandidate n)
    (O2 : LineBundle ProjectiveLine)
    (F : VeryFreeContactConicFamilyCandidate P n X O2)
    (hcover : F.CoversDistinctPointPairs) :
    IsOffDiagonalVeryFreeConnected P X.variety X.tangent := by
  intro x y hxy
  obtain ⟨b, hbx, hby⟩ := hcover x y hxy
  obtain ⟨e, f, heC, heval⟩ := F.fibreModels b
  have lift_condition (m : MarkedFamilyOfMaps F.family) :
      (b.map ≫ m.mark) ≫ F.family.projection = (𝟙 ComplexBase) ≫ b.map := by
    rw [Category.assoc, m.sectionLaw, Category.comp_id, Category.id_comp]
  let lift (m : MarkedFamilyOfMaps F.family) : ComplexBase ⟶ fibreScheme F.family b :=
    pullback.lift (b.map ≫ m.mark) (𝟙 ComplexBase) (lift_condition m)
  have lift_first (m : MarkedFamilyOfMaps F.family) :
      lift m ≫ pullback.fst F.family.projection b.map = b.map ≫ m.mark :=
    pullback.lift_fst _ _ _
  have lift_second (m : MarkedFamilyOfMaps F.family) :
      lift m ≫ pullback.snd F.family.projection b.map = 𝟙 ComplexBase :=
    pullback.lift_snd _ _ _
  let point (m : MarkedFamilyOfMaps F.family) : ProjectiveLinePoint P :=
    { map := lift m ≫ e.hom
      overC := by
        rw [Category.assoc, heC]
        exact lift_second m }
  have heval' : e.hom ≫ f.conic.curve.map = fibreEvaluation F.family b := by
    rw [← heval, ← Category.assoc, e.hom_inv_id, Category.id_comp]
  have point_value (m : MarkedFamilyOfMaps F.family) :
      (point m).map ≫ f.conic.curve.map = b.map ≫ m.evaluation := by
    change (lift m ≫ e.hom) ≫ f.conic.curve.map = b.map ≫ m.evaluation
    rw [Category.assoc, heval']
    change lift m ≫ (pullback.fst F.family.projection b.map ≫ F.family.evaluation) =
      b.map ≫ (m.mark ≫ F.family.evaluation)
    rw [← Category.assoc, lift_first m, Category.assoc]
  have hx : (point F.marks.first).map ≫ f.conic.curve.map = x.map :=
    (point_value F.marks.first).trans hbx
  have hy : (point F.marks.second).map ≫ f.conic.curve.map = y.map :=
    (point_value F.marks.second).trans hby
  have hdistinct : (point F.marks.first).map ≠ (point F.marks.second).map := by
    intro heq
    apply hxy
    exact hx.symm.trans ((congrArg (fun q => q ≫ f.conic.curve.map) heq).trans hy)
  exact ⟨{ marked := { curve := f.conic.curve
                       first := point F.marks.first
                       second := point F.marks.second
                       distinct := hdistinct }
           veryFree := f.veryFree }, hx, hy⟩

/-! Historical Phase-15 checkpoint, superseded by Phases 25--35 and the
Core/Skeleton/Refinement interfaces. Definitions and admitted construction
statements must not be interpreted as completed global geometry. -/

end LeBrunSalamon.PhaseFifteen

/-!
# Phase 16 -- an actual two-point evaluation morphism

The previous phases kept the evaluation of a twice-marked family as an ordered pair of maps B → X. Here it
is packaged as a morphism B → X ×_{Spec ℂ} X, with its two defining projection laws. This makes Zariski
dominance, off-diagonal coverage, and generic finiteness genuinely different properties of ONE morphism.
No moduli space or dominant-evaluation theorem is postulated.
-/

namespace LeBrunSalamon.PhaseSixteen

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open LeBrunSalamon.PhaseOne
open LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseEight
open LeBrunSalamon.PhaseFifteen

/-- The scheme map sending a twice-marked curve to its ordered pair of marked images. The equations ensure
that it is the categorical pairing of the two genuine marked-point evaluation maps. -/
structure TwoPointEvaluationMorphism {d : ℕ}
    {X : SmoothProperComplexVariety d}
    {F : ProperFlatFamilyOfMaps X}
    (marks : TwoMarkedFamilyOfMaps F) where
  map : F.base ⟶ SelfProduct X.structureMap
  firstLaw :
    map ≫ firstProjection X.structureMap = marks.first.evaluation
  secondLaw :
    map ≫ secondProjection X.structureMap = marks.second.evaluation

/-- The universal property of the fibre square supplies the genuine morphism. Proving the common-base
condition only uses `evaluationOverC` and the section laws of the two marked points. -/
theorem twoPointEvaluationMorphism_exists {d : ℕ}
    {X : SmoothProperComplexVariety d}
    {F : ProperFlatFamilyOfMaps X}
    (marks : TwoMarkedFamilyOfMaps F) :
    Nonempty (TwoPointEvaluationMorphism marks) := by
  have overC (m : MarkedFamilyOfMaps F) :
      m.evaluation ≫ X.structureMap = F.baseToC := by
    change (m.mark ≫ F.evaluation) ≫ X.structureMap = F.baseToC
    rw [Category.assoc, F.evaluationOverC, ← Category.assoc,
      m.sectionLaw, Category.id_comp]
  refine ⟨{ map := pullback.lift marks.first.evaluation marks.second.evaluation
              ((overC marks.first).trans (overC marks.second).symm)
            firstLaw := ?_
            secondLaw := ?_ }⟩
  · exact pullback.lift_fst _ _ _
  · exact pullback.lift_snd _ _ _

/-- The uniquely determined map to the fibre square, chosen using its existence theorem. A future
compiler-backed version should define it by `pullback.lift` directly. -/
noncomputable def canonicalTwoPointEvaluationMorphism {d : ℕ}
    {X : SmoothProperComplexVariety d}
    {F : ProperFlatFamilyOfMaps X}
    (marks : TwoMarkedFamilyOfMaps F) :
    TwoPointEvaluationMorphism marks :=
  Classical.choice (twoPointEvaluationMorphism_exists marks)

/-- Dominance means dense image in the *Zariski topology* of the
scheme-theoretic two-point target, NOT surjectivity on ℂ-points. -/
def TwoPointEvaluationMorphism.IsDominant {d : ℕ}
    {X : SmoothProperComplexVariety d}
    {F : ProperFlatFamilyOfMaps X}
    {marks : TwoMarkedFamilyOfMaps F}
    (E : TwoPointEvaluationMorphism marks) : Prop :=
  DenseRange (fun b : F.base => E.map b)

/-- The stronger property of covering every ordered pair of *distinct* complex points. This excludes the
diagonal and therefore does not force an embedded conic to pass twice through its own image point. -/
def TwoPointEvaluationMorphism.IsOffDiagonalSurjective {d : ℕ}
    {X : SmoothProperComplexVariety d}
    {F : ProperFlatFamilyOfMaps X}
    {marks : TwoMarkedFamilyOfMaps F}
    (E : TwoPointEvaluationMorphism marks) : Prop :=
  ∀ x y : ComplexPoint X, x.map ≠ y.map →
    ∃ b : ParameterPoint F,
      b.map ≫ E.map ≫ firstProjection X.structureMap = x.map ∧
      b.map ≫ E.map ≫ secondProjection X.structureMap = y.map

/-- A genuinely separate, set-theoretic generic-finiteness condition: the fibres over a dense open subset
of the target consist of finitely many scheme points. This does NOT by itself prove scheme-theoretic
quasi-finiteness, separability or etaleness. -/
def TwoPointEvaluationMorphism.HasFiniteFibresOnDenseOpen {d : ℕ}
    {X : SmoothProperComplexVariety d}
    {F : ProperFlatFamilyOfMaps X}
    {marks : TwoMarkedFamilyOfMaps F}
    (E : TwoPointEvaluationMorphism marks) : Prop :=
  ∃ U : Set (SelfProduct X.structureMap),
    IsOpen U ∧ Dense U ∧
      ∀ z ∈ U, Set.Finite {b : F.base | E.map b = z}

/-- The new off-diagonal condition is exactly the one in Phase 15, expressed through the universal
pairing. This is only a diagram chase using the two projection laws. -/
theorem twoPointEvaluation_offDiagonal_iff {d : ℕ}
    {X : SmoothProperComplexVariety d}
    {F : ProperFlatFamilyOfMaps X}
    (marks : TwoMarkedFamilyOfMaps F)
    (E : TwoPointEvaluationMorphism marks) :
    E.IsOffDiagonalSurjective ↔
      HasOffDiagonalMarkedTwoPointEvaluation marks := by
  simp only [TwoPointEvaluationMorphism.IsOffDiagonalSurjective,
    HasOffDiagonalMarkedTwoPointEvaluation, E.firstLaw, E.secondLaw]

/-- The two evaluation maps of the family are recovered by the actual projections; this prevents
accidentally changing the ordered pair in a later argument. -/
theorem twoPointEvaluation_projection_first {d : ℕ}
    {X : SmoothProperComplexVariety d}
    {F : ProperFlatFamilyOfMaps X}
    {marks : TwoMarkedFamilyOfMaps F}
    (E : TwoPointEvaluationMorphism marks) :
    E.map ≫ firstProjection X.structureMap = marks.first.evaluation :=
  E.firstLaw

theorem twoPointEvaluation_projection_second {d : ℕ}
    {X : SmoothProperComplexVariety d}
    {F : ProperFlatFamilyOfMaps X}
    {marks : TwoMarkedFamilyOfMaps F}
    (E : TwoPointEvaluationMorphism marks) :
    E.map ≫ secondProjection X.structureMap = marks.second.evaluation :=
  E.secondLaw

end LeBrunSalamon.PhaseSixteen

/-!
# Phase 17 -- first-jet limitations of the rank-one contact symbol

If a symmetric two-point kernel B has symbol θ⊗θ and vanishes to order two on the diagonal, each fixed-
point slice B(x,-) has zero first jet at x. Differentiating in the x-variable produces, at x, a linear
functional proportional to θ_x. In particular these differentiated slices span at most ONE direction in
the cotangent space, and have zero constant term. They cannot, by themselves, generate all first jets.

The definitions below are genuine finite-dimensional linear algebra, independent of unconstructed global
external tensor products and jets. They make the extra geometric generation step a visible obligation.
-/

namespace LeBrunSalamon.PhaseSeventeen

/-- First-jet data after trivializing a line bundle at a point: a value
and a linear differential.  This is the local model ℂ ⊕ V*. -/
abbrev TrivializedFirstJet (V : Type*) [AddCommGroup V] [Module ℂ V] :=
  ℂ × (V →ₗ[ℂ] ℂ)

/-- Derivative in the first variable of a rank-one quadratic symbol, normalized so its polarization is
θ(v)θ(w). Depending on the normalization of the quadratic Taylor coefficient there may be an additional
scalar factor 2, which does not change its span. -/
def ContactQuadraticDerivative {V : Type*}
    [AddCommGroup V] [Module ℂ V]
    (θ : V →ₗ[ℂ] ℂ) (v : V) : V →ₗ[ℂ] ℂ :=
  (θ v) • θ

/-- The first jet coming from differentiating the *first* argument of B at the diagonal: its constant
value is zero, and its differential lies in the contact-form line. -/
def KernelDerivativeFirstJet {V : Type*}
    [AddCommGroup V] [Module ℂ V]
    (θ : V →ₗ[ℂ] ℂ) (v : V) : TrivializedFirstJet V :=
  (0, ContactQuadraticDerivative θ v)

/-- All differentials obtained in this way are multiples of θ. -/
theorem contactQuadraticDerivative_is_multiple {V : Type*}
    [AddCommGroup V] [Module ℂ V]
    (θ : V →ₗ[ℂ] ℂ) (v : V) :
    ∃ c : ℂ, ContactQuadraticDerivative θ v = c • θ := by
  exact ⟨θ v, rfl⟩

/-- The rank-one derivative annihilates every contact-horizontal vector, i.e. every vector in ker θ. -/
theorem contactQuadraticDerivative_vanishes_on_contact_plane
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (θ : V →ₗ[ℂ] ℂ) (v w : V) (hw : θ w = 0) :
    ContactQuadraticDerivative θ v w = 0 := by
  simp [ContactQuadraticDerivative, hw]

/-- The constant component of each such first jet is zero. -/
theorem kernelDerivativeFirstJet_value_zero {V : Type*}
    [AddCommGroup V] [Module ℂ V]
    (θ : V →ₗ[ℂ] ℂ) (v : V) :
    (KernelDerivativeFirstJet θ v).1 = 0 :=
  rfl

/-- Even a whole family of derivatives of a rank-one quadratic kernel cannot cover *all* first-jet data.
This is independent of the ambient dimension: a jet with nonzero value cannot occur. -/
theorem kernelDerivativeFirstJet_not_surjective {V : Type*}
    [AddCommGroup V] [Module ℂ V]
    (θ : V →ₗ[ℂ] ℂ) :
    ¬ Function.Surjective (KernelDerivativeFirstJet θ) := by
  intro h
  obtain ⟨v, hv⟩ := h ((1 : ℂ), (0 : V →ₗ[ℂ] ℂ))
  have hval : (0 : ℂ) = 1 := congrArg Prod.fst hv
  norm_num at hval

/-- At a contact point, any proof that a two-point kernel generates first jets must supply extra sections
beyond the derivatives above. This predicate records precisely the required spanning condition; no
statement asserts it holds for a contact-Fano candidate. -/
def HasComplementaryJetSources {V : Type*}
    [AddCommGroup V] [Module ℂ V]
    (θ : V →ₗ[ℂ] ℂ)
    (additional : Set (TrivializedFirstJet V)) : Prop :=
  ∀ j : TrivializedFirstJet V,
    ∃ v : V, ∃ a ∈ additional,
      j = KernelDerivativeFirstJet θ v + a

/-- A purely formal consequence: complementary first jets produce
all first jets once the extra geometric sections have been built. -/
theorem complementaryJetSources_cover {V : Type*}
    [AddCommGroup V] [Module ℂ V]
    (θ : V →ₗ[ℂ] ℂ)
    (additional : Set (TrivializedFirstJet V))
    (h : HasComplementaryJetSources θ additional) :
    ∀ j : TrivializedFirstJet V,
      ∃ v : V, ∃ a ∈ additional,
        KernelDerivativeFirstJet θ v + a = j := by
  intro j
  obtain ⟨v, a, ha, hj⟩ := h j
  exact ⟨v, a, ha, hj.symm⟩

end LeBrunSalamon.PhaseSeventeen

/-!
# Phase 18 -- numerical splitting and two-point deformation obligations

For a quasi-line in a (2n+1)-fold, the tangent bundle pulls back as
O(2) ⊕ O(1)^(2n).  This predicts:
  h⁰(f*T_X) = 4n+3,  h¹(f*T_X) = 0;
  h⁰(f*T_X(-p-q)) = 1, h¹(f*T_X(-p-q)) = 0;
  expected dimension Mbar_{0,2}(X,[f]) = 4n+2 = dim(X×X).
The one-dimensional kernel in H⁰(T(-p-q)) is precisely the expected
automorphism direction of (P¹,p,q).  None of these NUMERICAL identities
by itself proves dominance, unobstructed smoothing, generic etaleness,
or the existence of an actual vector-bundle splitting.  The profile is
an integer-valued target for future Birkhoff--Grothendieck formalization.
-/

namespace LeBrunSalamon.PhaseEighteen

/-- The list of degrees in a *candidate* splitting `⊕_{i : Fin r} O(a_i)` of a vector bundle on P¹. This
integer profile is not yet an isomorphism of algebraic bundles. -/
structure TangentSplittingProfile (r : ℕ) where
  degree : Fin r → ℤ

/-- Nonnegative summand degrees, the numerical criterion for free
curves once the splitting is realized by the actual pulled-back T_X. -/
def TangentSplittingProfile.IsFree {r : ℕ}
    (P : TangentSplittingProfile r) : Prop :=
  ∀ i, 0 ≤ P.degree i

/-- Positive summand degrees, the numerical criterion for very free
curves once the splitting is realized. -/
def TangentSplittingProfile.IsVeryFree {r : ℕ}
    (P : TangentSplittingProfile r) : Prop :=
  ∀ i, 1 ≤ P.degree i

/-- By the cohomology of O(a) on P¹, the predicted h⁰ of the split bundle is Σ max(a_i+1,0). -/
def TangentSplittingProfile.predictedHZero {r : ℕ}
    (P : TangentSplittingProfile r) : ℕ :=
  ∑ i : Fin r, (P.degree i + 1).toNat

/-- The predicted h¹ is Σ max(-a_i-1,0). -/
def TangentSplittingProfile.predictedHOne {r : ℕ}
    (P : TangentSplittingProfile r) : ℕ :=
  ∑ i : Fin r, (-P.degree i - 1).toNat

/-- For two distinct marked points p,q, twisting by -p-q subtracts
2 from each splitting degree, so h⁰ becomes Σ max(a_i-1,0). -/
def TangentSplittingProfile.predictedTwoMarkedHZero {r : ℕ}
    (P : TangentSplittingProfile r) : ℕ :=
  ∑ i : Fin r, (P.degree i - 1).toNat

/-- Similarly, h¹(f*T_X(-p-q)) = Σ max(1-a_i,0). -/
def TangentSplittingProfile.predictedTwoMarkedHOne {r : ℕ}
    (P : TangentSplittingProfile r) : ℕ :=
  ∑ i : Fin r, (1 - P.degree i).toNat

/-- Quasi-line profile on a (2n+1)-dimensional variety: `O(2) ⊕ O(1)^(2n)`. -/
def quasiLineProfile (n : ℕ) : TangentSplittingProfile (2 * n + 1) :=
  ⟨fun i => if i.val = 0 then 2 else 1⟩

/-- Quasi-lines are very free numerically. -/
theorem quasiLineProfile_veryFree (n : ℕ) :
    (quasiLineProfile n).IsVeryFree := by
  intro i
  change (1 : ℤ) ≤ (if i.val = 0 then 2 else 1)
  split_ifs <;> omega

/-- A numerical very-free profile is also free. -/
theorem veryFreeProfile_implies_free {r : ℕ}
    (P : TangentSplittingProfile r) (h : P.IsVeryFree) :
    P.IsFree := by
  intro i
  exact le_trans (by omega : (0 : ℤ) ≤ 1) (h i)

/-- Numerical deformation data for quasi-lines, to be identified with
sheaf cohomology only once O(a), pullbacks and the H¹ API exist. -/
theorem quasiLineProfile_cohomology (n : ℕ) :
    (quasiLineProfile n).predictedHZero = 4 * n + 3 ∧
    (quasiLineProfile n).predictedHOne = 0 ∧
    (quasiLineProfile n).predictedTwoMarkedHZero = 1 ∧
    (quasiLineProfile n).predictedTwoMarkedHOne = 0 := by
  simp [TangentSplittingProfile.predictedHZero, TangentSplittingProfile.predictedHOne,
    TangentSplittingProfile.predictedTwoMarkedHZero, TangentSplittingProfile.predictedTwoMarkedHOne,
    quasiLineProfile, Fin.sum_univ_succ]
  omega

/-- Expected dimension of the unparameterized genus-zero stable-map space with two marked points:
d-3+(-K_X·C)+2. This is a Riemann--Roch NUMBER, not a constructed moduli scheme. -/
def expectedTwoMarkedMapDimension
    (dimension : ℕ) (anticanonicalDegree : ℤ) : ℤ :=
  (dimension : ℤ) - 1 + anticanonicalDegree

/-- Expected relative dimension of the two-point evaluation morphism Mbar_{0,2}(X,[C]) → X×X. -/
def expectedTwoPointEvaluationRelativeDimension
    (dimension : ℕ) (anticanonicalDegree : ℤ) : ℤ :=
  expectedTwoMarkedMapDimension dimension anticanonicalDegree -
    2 * (dimension : ℤ)

/-- When -K_X=(n+1)L, a contact degree-two curve has anticanonical degree 2(n+1). The line-bundle
isomorphism is still a separate, unproved geometric requirement. -/
def expectedContactConicAnticanonicalDegree (n : ℕ) : ℤ :=
  2 * ((n : ℤ) + 1)

/-- The two-point evaluation from contact conics has expected RELATIVE dimension zero in complex dimension
2n+1. This is the numerical reason that very free conics, rather than degree-one contact lines, are a
promising source of a two-point correspondence. -/
theorem contactConic_expectedEvaluationRelativeDimension_zero (n : ℕ) :
    expectedTwoPointEvaluationRelativeDimension
      (2 * n + 1) (expectedContactConicAnticanonicalDegree n) = 0 := by
  unfold expectedTwoPointEvaluationRelativeDimension
    expectedTwoMarkedMapDimension expectedContactConicAnticanonicalDegree
  omega

/-- For a contact degree-one line, the expected relative dimension is
-(n+1), so a family of such lines cannot dominate X×X on this naive
expected-dimension count (absent exceptional excess-dimensional behavior). -/
theorem contactLine_expectedEvaluationRelativeDimension (n : ℕ) :
    expectedTwoPointEvaluationRelativeDimension
      (2 * n + 1) ((n : ℤ) + 1) = -((n : ℤ) + 1) := by
  unfold expectedTwoPointEvaluationRelativeDimension
    expectedTwoMarkedMapDimension
  omega

/-- In the quasi-line case, the predicted h⁰ minus the 3-dimensional
automorphism group of P¹ plus two markings equals dim(X×X). -/
theorem quasiLineProfile_twoMarked_dimension (n : ℕ) :
    (quasiLineProfile n).predictedHZero - 3 + 2 = 2 * (2 * n + 1) := by
  have h := (quasiLineProfile_cohomology n).1
  omega

end LeBrunSalamon.PhaseEighteen

/-!
## Earlier audit ledgers consolidated

The former phase-by-phase audit prose has been replaced by the final ledger at the end of this file. The
declarations of Phases 1--18 are retained. Selected elaboration and axiom probes are collected at the end.
-/

namespace LeBrunSalamon.PhaseNineteen

open LeBrunSalamon.PhaseSeventeen

section ContactTaylor

variable (V : Type*) [AddCommGroup V] [Module ℂ V]

/-- The first-order coefficient data of a local scalar contact form
`alpha`, including the injective Levi condition on `ker alpha`.

`D u v` represents the directional derivative of the coefficients of
`alpha` in direction `u`, evaluated on `v`.  Thus
`d alpha(u,v) = D u v - D v u`.

We do not require the coefficient space to carry coordinates or a
chosen symplectic basis. -/
structure ContactOneJet where
  theta : V →ₗ[ℂ] ℂ
  nonzero : theta ≠ 0
  coefficientDerivative : V →ₗ[ℂ] (V →ₗ[ℂ] ℂ)
  leviNondegenerate :
    ∀ v : V, theta v = 0 →
      (∀ w : V, theta w = 0 →
        coefficientDerivative v w - coefficientDerivative w v = 0) →
      v = 0

variable {V}

/-- The alternating exterior differential at the chosen point. -/
def ContactOneJet.exteriorValue (J : ContactOneJet V)
    (u v : V) : ℂ :=
  J.coefficientDerivative u v - J.coefficientDerivative v u

/-- The quadratic diagonal symbol `alpha(s)^2`. -/
def ContactOneJet.quadratic (J : ContactOneJet V) (s : V) : ℂ :=
  J.theta s * J.theta s

/-- The cubic term FORCED by exchange symmetry: `alpha(s) * (∂_s alpha)(s)`. -/
def ContactOneJet.forcedCubic (J : ContactOneJet V) (s : V) : ℂ :=
  J.theta s * J.coefficientDerivative s s

/-- The linear term of the derivative with respect to the first
point, holding the second point fixed, up to harmless normalization. -/
def ContactOneJet.firstSlotLinear (J : ContactOneJet V)
    (v s : V) : ℂ :=
  -2 * J.theta s * J.theta v

/-- The quadratic term of the same derivative. Its `theta(s) * d alpha(v,s)` contribution is the missing
ingredient not visible from the quadratic symbol alone. -/
def ContactOneJet.firstSlotQuadratic (J : ContactOneJet V)
    (v s : V) : ℂ :=
  J.theta s * J.exteriorValue v s -
    J.theta v * J.coefficientDerivative s s

variable (V)

/-- A local third-order Taylor expansion of a SYMMETRIC two-point kernel whose second diagonal symbol is
`theta^2`. The displayed identity is the degree-three exchange-symmetry constraint; realizing it from a
genuine `B` is a separate formalization task. -/
structure SymmetricContactThirdJet where
  contact : ContactOneJet V
  cubic : V → ℂ
  cubicSymmetry : ∀ s : V,
    cubic s + cubic s =
      contact.forcedCubic s + contact.forcedCubic s

/-- The cubic Taylor coefficient is uniquely forced by symmetry. -/
theorem symmetricContactThirdJet_forced
    (J : SymmetricContactThirdJet V) (s : V) :
    J.cubic s = J.contact.forcedCubic s := by
  have h := J.cubicSymmetry s
  linear_combination (1 / 2 : ℂ) * h

/-- The first-slot linear term has to vanish if the first-slot
derivative is proportional to the original quadratic kernel. -/
theorem contactJet_linearTerm_forces_horizontal
    (J : ContactOneJet V) (v : V)
    (h : ∀ s : V, J.theta s * J.theta v = 0) :
    J.theta v = 0 := by
  classical
  have hex : ∃ r : V, J.theta r ≠ 0 := by
    by_contra hn
    push Not at hn
    apply J.nonzero
    ext r
    exact hn r
  obtain ⟨r, hr⟩ := hex
  exact (mul_eq_zero.mp (h r)).resolve_left hr

/-- After eliminating the linear term, the quadratic terms of the same proportionality relation imply a
Levi-orthogonality identity. This is the key algebraic step in the manuscript's jet argument. -/
theorem contactJet_quadraticTerm_forces_LeviKernel
    (J : ContactOneJet V) (v : V) (k : ℂ)
    (hv : J.theta v = 0)
    (h : ∀ s : V,
      J.theta s * (J.exteriorValue v s - k * J.theta s) = 0) :
    ∀ w : V, J.theta w = 0 → J.exteriorValue v w = 0 := by
  classical
  have hex : ∃ r : V, J.theta r ≠ 0 := by
    by_contra hn
    push Not at hn
    apply J.nonzero
    ext r
    exact hn r
  obtain ⟨r, hr⟩ := hex
  intro w hw
  have hrw : J.theta (r + w) = J.theta r := by
    simp only [map_add, hw, add_zero]
  have h₁ : J.exteriorValue v r - k * J.theta r = 0 :=
    (mul_eq_zero.mp (h r)).resolve_left hr
  have h₂ : J.exteriorValue v (r + w) - k * J.theta (r + w) = 0 :=
    (mul_eq_zero.mp (h (r + w))).resolve_left (by rw [hrw]; exact hr)
  have hadd : J.exteriorValue v (r + w) =
      J.exteriorValue v r + J.exteriorValue v w := by
    simp only [ContactOneJet.exteriorValue, map_add, LinearMap.add_apply]
    ring
  rw [hadd, hrw] at h₂
  linear_combination h₂ - h₁

/-- The **nonvacuous local injectivity lemma** behind the symmetric jet criterion. It rules out a nonzero
direction whose derivative of the two-point kernel is pointwise proportional to the kernel. The hypotheses
are exactly the degree-one and degree-two Taylor identities, not an ad hoc projective immersion
assumption. -/
theorem contactJet_noProjectiveKernel
    (J : ContactOneJet V) (v : V) (k : ℂ)
    (hlinear : ∀ s : V, J.theta s * J.theta v = 0)
    (hquadratic : ∀ s : V,
      J.theta s * (J.exteriorValue v s - k * J.theta s) = 0) :
    v = 0 := by
  have hv : J.theta v = 0 :=
    contactJet_linearTerm_forces_horizontal V J v hlinear
  have hlevi :=
    contactJet_quadraticTerm_forces_LeviKernel V J v k hv hquadratic
  exact J.leviNondegenerate v hv hlevi

/-- An infinitesimal contact Hamiltonian at a point, characterized by value and derivative of its scalar
Hamiltonian in one frame. The second identity holds on `ker(theta)`. -/
structure ContactHamiltonianValue (J : ContactOneJet V)
    (f : ℂ) (df : V →ₗ[ℂ] ℂ) where
  vector : V
  contactValue : J.theta vector = f
  horizontalEquation : ∀ w : V,
    J.theta w = 0 → df w + J.exteriorValue vector w = 0

/-- A contact Hamiltonian VALUE is unique for a prescribed first jet.
This uses contact nondegeneracy, not positivity or compactness. -/
theorem contactHamiltonianValue_unique
    (J : ContactOneJet V) (f : ℂ) (df : V →ₗ[ℂ] ℂ)
    (H K : ContactHamiltonianValue V J f df) :
    H.vector = K.vector := by
  apply sub_eq_zero.mp
  apply J.leviNondegenerate (H.vector - K.vector)
  · simp [H.contactValue, K.contactValue]
  · intro w hw
    have hH := H.horizontalEquation w hw
    have hK := K.horizontalEquation w hw
    dsimp [ContactOneJet.exteriorValue] at hH hK
    simp only [map_sub, LinearMap.sub_apply]
    linear_combination hH - hK

/- Source-only Phase 3 integration: hamiltonian_value. -/
noncomputable section
set_option autoImplicit false
variable (V : Type*) [AddCommGroup V] [Module ℂ V]

namespace HamiltonianValueExistenceProof

def exteriorForm (J : ContactOneJet V) : V →ₗ[ℂ] (V →ₗ[ℂ] ℂ) :=
  J.coefficientDerivative - J.coefficientDerivative.flip

def horizontalContraction (J : ContactOneJet V) :
    (LinearMap.ker J.theta) →ₗ[ℂ] Module.Dual ℂ (LinearMap.ker J.theta) :=
  (exteriorForm V J).compl₁₂ (LinearMap.ker J.theta).subtype
    (LinearMap.ker J.theta).subtype

theorem horizontalContraction_injective (J : ContactOneJet V) :
    Function.Injective (horizontalContraction V J) := by
  intro a b hab
  apply sub_eq_zero.mp
  apply Subtype.ext
  apply J.leviNondegenerate ((a - b : LinearMap.ker J.theta) : V)
    (a - b : LinearMap.ker J.theta).property
  intro w hw
  have hz : horizontalContraction V J (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  exact congrArg
    (fun φ : Module.Dual ℂ (LinearMap.ker J.theta) => φ ⟨w, hw⟩) hz

theorem horizontalContraction_surjective [FiniteDimensional ℂ V]
    (J : ContactOneJet V) : Function.Surjective (horizontalContraction V J) := by
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := horizontalContraction V J)
    (Subspace.dual_finrank_eq (K := ℂ) (V := LinearMap.ker J.theta)).symm).mp
  exact horizontalContraction_injective V J

theorem contactHamiltonianValue_exists
    [FiniteDimensional ℂ V]
    (J : ContactOneJet V) (f : ℂ) (df : V →ₗ[ℂ] ℂ) :
    Nonempty (ContactHamiltonianValue V J f df) := by
  classical
  obtain ⟨z, hz⟩ : ∃ z : V, J.theta z ≠ 0 := by
    by_contra h
    push_neg at h
    apply J.nonzero
    ext z
    exact h z
  let v₀ : V := (f / J.theta z) • z
  have hv₀ : J.theta v₀ = f := by
    change J.theta ((f / J.theta z) • z) = f
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hz]
  let ψ : Module.Dual ℂ (LinearMap.ker J.theta) :=
    ((-df) - exteriorForm V J v₀).comp (LinearMap.ker J.theta).subtype
  obtain ⟨a, ha⟩ := horizontalContraction_surjective V J ψ
  refine ⟨{ vector := v₀ + (a : V)
            contactValue := ?_
            horizontalEquation := ?_ }⟩
  · have hθa : J.theta (a : V) = 0 := a.property
    rw [map_add, hv₀, hθa, add_zero]
  · intro w hw
    have he := congrArg
      (fun φ : Module.Dual ℂ (LinearMap.ker J.theta) => φ ⟨w, hw⟩) ha
    change J.exteriorValue (a : V) w = -df w - J.exteriorValue v₀ w at he
    have hadd : J.exteriorValue (v₀ + (a : V)) w =
        J.exteriorValue v₀ w + J.exteriorValue (a : V) w := by
      change exteriorForm V J (v₀ + (a : V)) w =
        exteriorForm V J v₀ w + exteriorForm V J (a : V) w
      rw [map_add, LinearMap.add_apply]
    rw [hadd, he]
    ring

end HamiltonianValueExistenceProof
end


/-- In finite complex dimension the contact Hamiltonian equations have a solution for any scalar value and
any cotangent vector. This is the local linear-algebra half of the Hamiltonian correspondence. -/
theorem contactHamiltonianValue_exists
    [FiniteDimensional ℂ V]
    (J : ContactOneJet V) (f : ℂ) (df : V →ₗ[ℂ] ℂ) :
    Nonempty (ContactHamiltonianValue V J f df) := by
  exact LeBrunSalamon.PhaseNineteen.HamiltonianValueExistenceProof.contactHamiltonianValue_exists (V := V) (J := J) (f := f) (df := df)

/-- Contact Hamiltonian velocity therefore depends only on the first
jet of the Hamiltonian, rather than its higher derivatives. -/
theorem sameFirstJet_sameContactHamiltonianValue
    (J : ContactOneJet V) (f : ℂ)
    (df : V →ₗ[ℂ] ℂ) (H K : ContactHamiltonianValue V J f df) :
    H.vector = K.vector :=
  contactHamiltonianValue_unique V J f df H K

/-- A local contact form has nonzero quadratic diagonal symbol. -/
theorem contactQuadratic_nonzero
    (J : ContactOneJet V) :
    ∃ s : V, J.quadratic s ≠ 0 := by
  have hex : ∃ s : V, J.theta s ≠ 0 := by
    by_contra h
    push Not at h
    apply J.nonzero
    ext s
    exact h s
  obtain ⟨s, hs⟩ := hex
  exact ⟨s, mul_ne_zero hs hs⟩

end ContactTaylor

end LeBrunSalamon.PhaseNineteen

end

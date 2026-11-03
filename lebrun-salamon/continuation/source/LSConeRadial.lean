import LSSuitableDirections
import LSConePole

/-!
## The radial vector is an actual tangent to the affine cone

SOURCE: `lines:cone-addition`, the radial-vector argument. Scalar stability
of the cone defines an actual polynomial curve `t ↦ t*v`. Its comorphism
factors through the vanishing-ideal quotient. Differentiation at one gives
a point derivation whose ambient coordinates are exactly `v`.

The localization comparison uses actual maps to the existing dual-number
algebra. Inverting a denominator whose value is nonzero preserves every
point tangent, including the radial tangent. No pointwise vector is simply
declared to belong to an unrelated tangent-space label.

New continuation; compilation is governed by the 35,000-line threshold.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry
open LeBrunSalamon.PhaseOne

namespace LeBrunSalamon.Construction.Lines.ConeRadial

open DirectionCones Infinitesimal

section Scaling

variable {ι : Type}

/-- A concrete coordinate point set is closed under every complex scalar. -/
def IsCone (S : Set (ι → ℂ)) : Prop :=
  ∀ v ∈ S, ∀ c : ℂ, c • v ∈ S

/-- Polynomial coordinates of the actual scaling curve through `v`. -/
def scalingPolynomial (v : ι → ℂ) : CoordinatePolynomial ι →ₐ[ℂ] Polynomial ℂ :=
  MvPolynomial.aeval (fun i => Polynomial.C (v i) * Polynomial.X)

theorem scalingPolynomial_evaluation (v : ι → ℂ) (c : ℂ)
    (f : CoordinatePolynomial ι) :
    (Polynomial.aeval c) (scalingPolynomial v f) = MvPolynomial.eval (c • v) f := by
  have h : (Polynomial.aeval c).comp (scalingPolynomial v) =
      MvPolynomial.aeval (c • v) := by
    ext i
    simp only [AlgHom.comp_apply, scalingPolynomial, MvPolynomial.aeval_X,
      map_mul, Polynomial.aeval_C, Polynomial.aeval_X,
      Algebra.algebraMap_self_apply, Pi.smul_apply, smul_eq_mul]
    exact mul_comm _ _
  exact congrArg (fun g : CoordinatePolynomial ι →ₐ[ℂ] ℂ => g f) h

/-- Vanishing on the entire scalar line is a polynomial identity because
the base field is infinite. This proves the quotient factorization. -/
theorem scalingPolynomial_kills_ideal (S : Set (ι → ℂ)) (hS : IsCone S)
    (v : ι → ℂ) (hv : v ∈ S) (f : CoordinatePolynomial ι)
    (hf : f ∈ vanishingIdeal S) : scalingPolynomial v f = 0 := by
  apply Polynomial.zero_of_eval_zero
  intro c
  change (Polynomial.aeval c) (scalingPolynomial v f) = 0
  rw [scalingPolynomial_evaluation]
  exact hf (c • v) (hS v hv c)

def scalingCurveComorphism (S : Set (ι → ℂ)) (hS : IsCone S)
    (v : ι → ℂ) (hv : v ∈ S) : CoordinateRing S →ₐ[ℂ] Polynomial ℂ :=
  Ideal.Quotient.liftₐ (vanishingIdeal S) (scalingPolynomial v)
    (scalingPolynomial_kills_ideal S hS v hv)

theorem scalingCurve_coordinate (S : Set (ι → ℂ)) (hS : IsCone S)
    (v : ι → ℂ) (hv : v ∈ S) (i : ι) :
    scalingCurveComorphism S hS v hv (coordinate S i) =
      Polynomial.C (v i) * Polynomial.X := MvPolynomial.aeval_X _ i

theorem scalingCurve_evaluation (S : Set (ι → ℂ)) (hS : IsCone S)
    (v : ι → ℂ) (hv : v ∈ S) (c : ℂ) :
    (Polynomial.aeval c).comp (scalingCurveComorphism S hS v hv) =
      quotientEvaluation S (c • v) (hS v hv c) := by
  apply quotientPoint_ext
  intro i
  simp only [AlgHom.comp_apply, scalingCurve_coordinate,
    quotientEvaluation_coordinate, map_mul, Polynomial.aeval_C,
    Polynomial.aeval_X, Pi.smul_apply, smul_eq_mul]
  exact mul_comm _ _

theorem scalingCurve_at_one (S : Set (ι → ℂ)) (hS : IsCone S)
    (v : ι → ℂ) (hv : v ∈ S) (a : CoordinateRing S) :
    (Polynomial.aeval (1 : ℂ)) (scalingCurveComorphism S hS v hv a) =
      quotientEvaluation S v hv a := by
  have h : (Polynomial.aeval (1 : ℂ)).comp (scalingCurveComorphism S hS v hv) =
      quotientEvaluation S v hv := by
    apply quotientPoint_ext
    intro i
    simp only [AlgHom.comp_apply, scalingCurve_coordinate,
      quotientEvaluation_coordinate, map_mul, Polynomial.aeval_C,
      Polynomial.aeval_X, Algebra.algebraMap_self_apply, mul_one]
  exact congrArg (fun g : CoordinateRing S →ₐ[ℂ] ℂ => g a) h

/-- The scaling curve as an actual scheme morphism. -/
def scalingCurveMorphism (S : Set (ι → ℂ)) (hS : IsCone S)
    (v : ι → ℂ) (hv : v ∈ S) :
    Spec (CommRingCat.of (Polynomial ℂ)) ⟶ closureScheme S :=
  affineMap (scalingCurveComorphism S hS v hv)

theorem scalingCurveMorphism_overC (S : Set (ι → ℂ)) (hS : IsCone S)
    (v : ι → ℂ) (hv : v ∈ S) :
    scalingCurveMorphism S hS v hv ≫ affineBaseMap (CoordinateRing S) =
      affineBaseMap (Polynomial ℂ) := affineMap_overC _

/-- Differentiate the actual scaling comorphism at one. -/
def radialTangent (S : Set (ι → ℂ)) (hS : IsCone S)
    (v : ι → ℂ) (hv : v ∈ S) :
    Tangent (CoordinateRing S) (quotientEvaluation S v hv) :=
  ⟨((Polynomial.aeval (1 : ℂ)).toLinearMap.comp Polynomial.derivative).comp
      (scalingCurveComorphism S hS v hv).toLinearMap, by
    intro a b
    change (Polynomial.aeval (1 : ℂ))
        (Polynomial.derivative (scalingCurveComorphism S hS v hv (a * b))) =
      quotientEvaluation S v hv a * (Polynomial.aeval (1 : ℂ))
        (Polynomial.derivative (scalingCurveComorphism S hS v hv b)) +
      quotientEvaluation S v hv b * (Polynomial.aeval (1 : ℂ))
        (Polynomial.derivative (scalingCurveComorphism S hS v hv a))
    rw [map_mul, Polynomial.derivative_mul, map_add, map_mul, map_mul]
    rw [scalingCurve_at_one, scalingCurve_at_one]
    ring⟩

theorem radialTangent_coordinate (S : Set (ι → ℂ)) (hS : IsCone S)
    (v : ι → ℂ) (hv : v ∈ S) (i : ι) :
    (radialTangent S hS v hv).val (coordinate S i) = v i := by
  change (Polynomial.aeval (1 : ℂ))
    (Polynomial.derivative (scalingCurveComorphism S hS v hv (coordinate S i))) = v i
  rw [scalingCurve_coordinate, Polynomial.derivative_C_mul_X]
  exact Polynomial.aeval_C _ _

/-- The coordinate map uses the actual project point-derivation space. -/
def tangentCoordinates (S : Set (ι → ℂ)) (p : CoordinateRing S →ₐ[ℂ] ℂ) :
    Tangent (CoordinateRing S) p →ₗ[ℂ] (ι → ℂ) where
  toFun D i := D.val (coordinate S i)
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

theorem radialVector_mem_tangentRange (S : Set (ι → ℂ)) (hS : IsCone S)
    (v : ι → ℂ) (hv : v ∈ S) :
    v ∈ LinearMap.range (tangentCoordinates S (quotientEvaluation S v hv)) := by
  refine ⟨radialTangent S hS v hv, ?_⟩
  funext i
  exact radialTangent_coordinate S hS v hv i

theorem quotientEvaluation_of_coordinates (S : Set (ι → ℂ)) (hS : EquationClosed S)
    (p : CoordinateRing S →ₐ[ℂ] ℂ) :
    quotientEvaluation S (fun i => p (coordinate S i)) (quotientPoint_mem S hS p) = p := by
  apply quotientPoint_ext
  intro i
  exact quotientEvaluation_coordinate S _ _ i

/-- Substitute the scalar multiple of each coordinate into a polynomial.
Cone stability makes this actual algebra endomorphism preserve its ideal. -/
def scalarSubstitution (c : ℂ) :
    CoordinatePolynomial ι →ₐ[ℂ] CoordinatePolynomial ι :=
  MvPolynomial.aeval (fun i => MvPolynomial.C c * MvPolynomial.X i)

theorem scalarSubstitution_evaluation (c : ℂ) (v : ι → ℂ)
    (f : CoordinatePolynomial ι) :
    MvPolynomial.eval v (scalarSubstitution c f) =
      MvPolynomial.eval (c • v) f := by
  have h : (MvPolynomial.aeval v).comp (scalarSubstitution c) =
      MvPolynomial.aeval (c • v) := by
    ext i
    simp [scalarSubstitution, Pi.smul_apply, smul_eq_mul]
  exact congrArg (fun g : CoordinatePolynomial ι →ₐ[ℂ] ℂ => g f) h

theorem scalarSubstitution_mem_ideal (S : Set (ι → ℂ)) (hcone : IsCone S)
    (c : ℂ) (f : CoordinatePolynomial ι) (hf : f ∈ vanishingIdeal S) :
    scalarSubstitution c f ∈ vanishingIdeal S := by
  intro v hv
  rw [scalarSubstitution_evaluation]
  exact hf (c • v) (hcone v hv c)

/-- The scaling polynomial factors at every point of the affine closure.
This uses invariance of the equations, so it does not require the original
point set to have already been identified with all closed points. -/
theorem scalingAtPoint_kills_ideal (S : Set (ι → ℂ)) (hcone : IsCone S)
    (p : CoordinateRing S →ₐ[ℂ] ℂ) (f : CoordinatePolynomial ι)
    (hf : f ∈ vanishingIdeal S) :
    scalingPolynomial (fun i => p (coordinate S i)) f = 0 := by
  apply Polynomial.zero_of_eval_zero
  intro c
  change (Polynomial.aeval c)
    (scalingPolynomial (fun i => p (coordinate S i)) f) = 0
  rw [scalingPolynomial_evaluation, ← scalarSubstitution_evaluation]
  exact quotientPoint_satisfiesEquations S p (scalarSubstitution c f)
    (scalarSubstitution_mem_ideal S hcone c f hf)

def scalingAtPointComorphism (S : Set (ι → ℂ)) (hcone : IsCone S)
    (p : CoordinateRing S →ₐ[ℂ] ℂ) : CoordinateRing S →ₐ[ℂ] Polynomial ℂ :=
  Ideal.Quotient.liftₐ (vanishingIdeal S)
    (scalingPolynomial (fun i => p (coordinate S i)))
    (scalingAtPoint_kills_ideal S hcone p)

theorem scalingAtPoint_coordinate (S : Set (ι → ℂ)) (hcone : IsCone S)
    (p : CoordinateRing S →ₐ[ℂ] ℂ) (i : ι) :
    scalingAtPointComorphism S hcone p (coordinate S i) =
      Polynomial.C (p (coordinate S i)) * Polynomial.X :=
  MvPolynomial.aeval_X _ i

theorem scalingAtPoint_at_one (S : Set (ι → ℂ)) (hcone : IsCone S)
    (p : CoordinateRing S →ₐ[ℂ] ℂ) (a : CoordinateRing S) :
    (Polynomial.aeval (1 : ℂ)) (scalingAtPointComorphism S hcone p a) = p a := by
  have h : (Polynomial.aeval (1 : ℂ)).comp
      (scalingAtPointComorphism S hcone p) = p := by
    apply quotientPoint_ext
    intro i
    simp only [AlgHom.comp_apply, scalingAtPoint_coordinate, map_mul,
      Polynomial.aeval_C, Polynomial.aeval_X, Algebra.algebraMap_self_apply, mul_one]
  exact congrArg (fun g : CoordinateRing S →ₐ[ℂ] ℂ => g a) h

/-- Every actual algebra point of the affine cone closure has the radial
derivation. Its center is the original point, without a closedness input. -/
def radialAtPoint (S : Set (ι → ℂ)) (hcone : IsCone S)
    (p : CoordinateRing S →ₐ[ℂ] ℂ) : Tangent (CoordinateRing S) p :=
  ⟨((Polynomial.aeval (1 : ℂ)).toLinearMap.comp Polynomial.derivative).comp
      (scalingAtPointComorphism S hcone p).toLinearMap, by
    intro a b
    change (Polynomial.aeval (1 : ℂ))
        (Polynomial.derivative (scalingAtPointComorphism S hcone p (a * b))) =
      p a * (Polynomial.aeval (1 : ℂ))
        (Polynomial.derivative (scalingAtPointComorphism S hcone p b)) +
      p b * (Polynomial.aeval (1 : ℂ))
        (Polynomial.derivative (scalingAtPointComorphism S hcone p a))
    rw [map_mul, Polynomial.derivative_mul, map_add, map_mul, map_mul]
    rw [scalingAtPoint_at_one, scalingAtPoint_at_one]
    ring⟩

theorem radialAtPoint_coordinate (S : Set (ι → ℂ))
    (hcone : IsCone S) (p : CoordinateRing S →ₐ[ℂ] ℂ) (i : ι) :
    (radialAtPoint S hcone p).val (coordinate S i) = p (coordinate S i) := by
  change (Polynomial.aeval (1 : ℂ))
    (Polynomial.derivative (scalingAtPointComorphism S hcone p (coordinate S i))) =
      p (coordinate S i)
  rw [scalingAtPoint_coordinate, Polynomial.derivative_C_mul_X]
  exact Polynomial.aeval_C _ _

end Scaling

section PointLocalization

/-- A dual number is invertible whenever its residue is nonzero. The
nilpotent first-order coefficient imposes no extra invertibility test. -/
theorem dual_isUnit_of_residue_ne_zero (z : Dual) (hz : residue z ≠ 0) : IsUnit z := by
  have hunit : IsUnit (algebraMap ℂ Dual (residue z)) :=
    (isUnit_iff_ne_zero.mpr hz).map (algebraMap ℂ Dual)
  have hnil : IsNilpotent (epsilon * algebraMap ℂ Dual (linearCoefficient z)) := by
    refine ⟨2, ?_⟩
    rw [mul_pow, epsilon_square, zero_mul]
  rw [dual_normalForm_reconstruct z]
  exact hnil.isUnit_add_left_of_commute hunit (Commute.all _ _)

variable {A L : Type*} [CommRing A] [Algebra ℂ A]
    [CommRing L] [Algebra A L] [Algebra ℂ L] [IsScalarTower ℂ A L]
    (S : Submonoid A) [IsLocalization S L]

def restrictedPoint (p : L →ₐ[ℂ] ℂ) : A →ₐ[ℂ] ℂ :=
  p.comp (Algebra.algHom ℂ A L)

theorem tangentToDual_units (p : L →ₐ[ℂ] ℂ)
    (D : Tangent A (restrictedPoint p)) (s : S) :
    IsUnit (tangentToDual (restrictedPoint p) D s) := by
  apply dual_isUnit_of_residue_ne_zero
  change residue (algebraMap ℂ Dual (p (algebraMap A L (s : A))) +
    epsilon * algebraMap ℂ Dual (D.val (s : A))) ≠ 0
  rw [residue_normalForm]
  exact ((IsLocalization.map_units L s).map p.toRingHom).ne_zero

/-- The unique localization of the actual first-order point lift. -/
def localizedDualPoint (p : L →ₐ[ℂ] ℂ)
    (D : Tangent A (restrictedPoint p)) : L →ₐ[ℂ] Dual :=
  IsLocalization.liftAlgHom (tangentToDual_units S p D)

theorem localizedDualPoint_base (p : L →ₐ[ℂ] ℂ)
    (D : Tangent A (restrictedPoint p)) (a : A) :
    localizedDualPoint S p D (algebraMap A L a) =
      tangentToDual (restrictedPoint p) D a :=
  IsLocalization.lift_eq _ a

theorem localizedDualPoint_residue (p : L →ₐ[ℂ] ℂ)
    (D : Tangent A (restrictedPoint p)) :
    residue.comp (localizedDualPoint S p D) = p := by
  apply IsLocalization.algHom_ext S
  ext a
  change residue (localizedDualPoint S p D (algebraMap A L a)) = p (algebraMap A L a)
  rw [localizedDualPoint_base]
  exact congrArg (fun f : A →ₐ[ℂ] ℂ => f a)
    (tangentToDual_residue (restrictedPoint p) D)

/-- A point tangent extends to the localization because its center is
already an actual point of that localization. -/
def localizeTangent (p : L →ₐ[ℂ] ℂ)
    (D : Tangent A (restrictedPoint p)) : Tangent L p :=
  ⟨{ toFun := fun a => linearCoefficient (localizedDualPoint S p D a)
     map_add' := by intro a b; rw [map_add, linearCoefficient_add]
     map_smul' := by
       intro c a
       simp only [map_smul, linearCoefficient_smul, RingHom.id_apply] }, by
    intro a b
    change linearCoefficient (localizedDualPoint S p D (a * b)) =
      p a * linearCoefficient (localizedDualPoint S p D b) +
      p b * linearCoefficient (localizedDualPoint S p D a)
    rw [map_mul, linearCoefficient_mul]
    have hres (a : L) : residue (localizedDualPoint S p D a) = p a :=
      congrArg (fun f : L →ₐ[ℂ] ℂ => f a) (localizedDualPoint_residue S p D)
    rw [hres a, hres b]⟩

theorem localizeTangent_base (p : L →ₐ[ℂ] ℂ)
    (D : Tangent A (restrictedPoint p)) (a : A) :
    (localizeTangent S p D).val (algebraMap A L a) = D.val a := by
  change linearCoefficient (localizedDualPoint S p D (algebraMap A L a)) = D.val a
  rw [localizedDualPoint_base]
  exact linearCoefficient_normalForm _ _

theorem localizeTangent_restrict (p : L →ₐ[ℂ] ℂ)
    (D : Tangent A (restrictedPoint p)) :
    tangentMap (Algebra.algHom ℂ A L) p (localizeTangent S p D) = D := by
  apply Subtype.ext
  ext a
  exact localizeTangent_base S p D a

end PointLocalization

section LocalizedCone

variable {ι : Type} (S : Set (ι → ℂ))
    (hcone : IsCone S)
    {L : Type*} [CommRing L] [Algebra (CoordinateRing S) L] [Algebra ℂ L]
    [IsScalarTower ℂ (CoordinateRing S) L]
    (M : Submonoid (CoordinateRing S)) [IsLocalization M L]

def localizedCoordinate (i : ι) : L :=
  algebraMap (CoordinateRing S) L (coordinate S i)

/-- The radial point tangent on the actual localized cone chart. -/
def localizedRadial (p : L →ₐ[ℂ] ℂ) : Tangent L p :=
  localizeTangent M p (radialAtPoint S hcone (restrictedPoint p))

theorem localizedRadial_coordinate (p : L →ₐ[ℂ] ℂ) (i : ι) :
    (localizedRadial S hcone M p).val (localizedCoordinate (L := L) S i) =
      p (localizedCoordinate (L := L) S i) := by
  rw [localizedRadial, localizedCoordinate, localizeTangent_base,
    radialAtPoint_coordinate]
  rfl

include hcone M in
/-- Tangent isotropy on the cone chart therefore annihilates the radial
one-form on every actual point tangent. This is the geometric input to
Kähler-module detection, rather than an assumed one-form equality. -/
theorem radial_pairing_zero_of_tangent_isotropy [Fintype ι]
    (ω : ι → ι → ℂ)
    (hisotropic : ∀ (p : L →ₐ[ℂ] ℂ) (D E : Tangent L p),
      ConePairing.pairing ω
        (fun i => D.val (localizedCoordinate (L := L) S i))
        (fun i => E.val (localizedCoordinate (L := L) S i)) = 0)
    (p : L →ₐ[ℂ] ℂ) (D : Tangent L p) :
    ConePairing.pairing ω
      (fun i => p (localizedCoordinate (L := L) S i))
      (fun i => D.val (localizedCoordinate (L := L) S i)) = 0 := by
  have h := hisotropic p (localizedRadial S hcone M p) D
  simpa only [localizedRadial_coordinate] using h

end LocalizedCone

end LeBrunSalamon.Construction.Lines.ConeRadial

end

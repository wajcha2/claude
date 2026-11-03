import LSSuitableDirections
import LSConeDiagonal
import LSConePole

/-!
## Detecting the radial Kahler form on actual smooth cone charts

SOURCE: `lines:cone-addition`, the passage from isotropic tangent spaces
to the vanishing of `omega(r,dr)` as a regular differential form.

The scalar detection theorem below is proved for the actual quotient by
the vanishing ideal and for its principal localizations. Module detection
uses projectivity, supplied for Kahler differentials by formal smoothness.
Reducedness alone is not used to detect an arbitrary module section.
Every tangent vector constructed here is an existing point derivation in
`Infinitesimal.Tangent`, with its Leibniz identity proved explicitly.

STATUS: new source; compilation deferred to the user's 35,000-line gate.
-/

noncomputable section
set_option autoImplicit false

namespace LeBrunSalamon.Construction.Lines.RadialDetection

open scoped TensorProduct

section PointDetection

variable {A : Type*} [CommRing A] [Algebra ℂ A]
variable {P : Type*}

/-- A specified family of actual complex algebra points detects scalar
functions. Keeping the family permits testing only points of the given
cone, even before its equation-closedness theorem is available. -/
def PointsDetect (points : P → A →ₐ[ℂ] ℂ) : Prop :=
  ∀ a : A, (∀ p : P, points p a = 0) → a = 0

/-- Scalar detection by all complex algebra points. This property is
proved below for the rings used in the cone argument. -/
def ComplexPointsSeparate (A : Type*) [CommRing A] [Algebra ℂ A] : Prop :=
  PointsDetect (fun p : A →ₐ[ℂ] ℂ => p)

theorem pointsDetect_iff_zero (points : P → A →ₐ[ℂ] ℂ)
    (hpoints : PointsDetect points) (a : A) :
    (∀ p, points p a = 0) ↔ a = 0 := by
  constructor
  · exact hpoints a
  · intro h p
    rw [h, map_zero]

theorem complexPointsSeparate_of_family (points : P → A →ₐ[ℂ] ℂ)
    (hpoints : PointsDetect points) : ComplexPointsSeparate A := by
  intro a ha
  exact hpoints a (fun p => ha (points p))

/-- Scalar detection also detects equality of two actual functions. -/
theorem pointsDetect_ext (points : P → A →ₐ[ℂ] ℂ)
    (hpoints : PointsDetect points) {a b : A}
    (h : ∀ p, points p a = points p b) : a = b := by
  apply sub_eq_zero.mp
  apply hpoints
  intro p
  rw [map_sub, h p, sub_self]

/-- For this quotient, scalar detection follows from the definition of
the vanishing ideal. No Nullstellensatz or smoothness input is needed. -/
theorem coordinateRing_pointsDetect {I : Type} (S : Set (I → ℂ)) :
    PointsDetect (fun v : S =>
      DirectionCones.quotientEvaluation S v.val v.property) := by
  intro a ha
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  intro v hv
  simpa only [DirectionCones.quotientEvaluation_mk] using ha ⟨v, hv⟩

theorem coordinateRing_complexPointsSeparate {I : Type} (S : Set (I → ℂ)) :
    ComplexPointsSeparate (DirectionCones.CoordinateRing S) :=
  complexPointsSeparate_of_family
    (fun v : S => DirectionCones.quotientEvaluation S v.val v.property)
    (coordinateRing_pointsDetect S)

end PointDetection

section PrincipalLocalization

variable {A L : Type*} [CommRing A] [CommRing L]
variable [Algebra ℂ A] [Algebra A L] [Algebra ℂ L]
variable [IsScalarTower ℂ A L]
variable (r : A) [IsLocalization.Away r L]

/-- The actual extension of a point whose denominator is nonzero to the
principal affine chart. Its construction uses localization's universal
property, not an abstract point-selection hypothesis. -/
def awayPoint (p : A →ₐ[ℂ] ℂ) (hp : p r ≠ 0) : L →ₐ[ℂ] ℂ :=
  IsLocalization.Away.liftAlgHom r (isUnit_iff_ne_zero.mpr hp)

@[simp] theorem awayPoint_algebraMap (p : A →ₐ[ℂ] ℂ) (hp : p r ≠ 0)
    (a : A) : awayPoint (L := L) r p hp (algebraMap A L a) = p a := by
  exact IsLocalization.Away.lift_eq r (isUnit_iff_ne_zero.mpr hp) a

/-- Restrict a chosen point family to the principal open and extend its
points to the actual localization. -/
def awayPointFamily {P : Type*} (points : P → A →ₐ[ℂ] ℂ) :
    {p : P // points p r ≠ 0} → L →ₐ[ℂ] ℂ :=
  fun p => awayPoint r (points p.val) p.property

@[simp] theorem awayPointFamily_algebraMap {P : Type*}
    (points : P → A →ₐ[ℂ] ℂ) (p : {p : P // points p r ≠ 0}) (a : A) :
    awayPointFamily (L := L) r points p (algebraMap A L a) = points p.val a :=
  awayPoint_algebraMap r (points p.val) p.property a

/-- A principal localization retains enough complex points to detect
functions. The proof multiplies the numerator by the denominator to
handle the points excluded from the principal open.

This statement deliberately concerns a principal localization. An
arbitrary localization, such as a function field, need not retain any
complex algebra point. -/
theorem pointsDetect_away {P : Type*} (points : P → A →ₐ[ℂ] ℂ)
    (hpoints : PointsDetect points) :
    PointsDetect (awayPointFamily (L := L) r points) := by
  intro z hz
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj r z
  have har : a * r = 0 := by
    apply hpoints
    intro p
    by_cases hp : points p r = 0
    · rw [map_mul, hp, mul_zero]
    · have hz' : awayPoint (L := L) r (points p) hp z = 0 := hz ⟨p, hp⟩
      have he := congrArg (awayPoint (L := L) r (points p) hp) ha
      simp only [map_mul, map_pow, awayPoint_algebraMap] at he
      rw [hz', zero_mul] at he
      rw [map_mul, ← he, zero_mul]
  have hma : algebraMap A L a = 0 := by
    apply (IsLocalization.Away.algebraMap_isUnit (S := L) r).mul_left_eq_zero.mp
    simpa only [map_mul, map_zero] using congrArg (algebraMap A L) har
  apply (IsLocalization.Away.algebraMap_pow_isUnit (S := L) r n).mul_left_eq_zero.mp
  exact ha.trans hma

include r in
theorem complexPointsSeparate_away (hA : ComplexPointsSeparate A) :
    ComplexPointsSeparate L :=
  complexPointsSeparate_of_family
    (awayPointFamily (L := L) r (fun p : A →ₐ[ℂ] ℂ => p))
    (pointsDetect_away r (fun p : A →ₐ[ℂ] ℂ => p) hA)

end PrincipalLocalization

section ProjectiveModules

variable {A : Type*} [CommRing A] [Algebra ℂ A]
variable {M : Type*} [AddCommGroup M] [Module A M]
variable [Module.Projective A M] {P : Type*}

/-- Projective-module sections are detected by dual functionals followed
by detecting scalar points. This is the precise module-theoretic input
needed for a smooth cotangent module. -/
theorem projective_eq_zero_of_pointFamily (points : P → A →ₐ[ℂ] ℂ)
    (hpoints : PointsDetect points) (m : M)
    (hm : ∀ (p : P) (ell : M →ₗ[A] A), points p (ell m) = 0) : m = 0 := by
  apply (Module.forall_dual_apply_eq_zero_iff A m).mp
  intro ell
  exact hpoints (ell m) (fun p => hm p ell)

theorem projective_eq_zero_of_pointwise (hA : ComplexPointsSeparate A) (m : M)
    (hm : ∀ (p : A →ₐ[ℂ] ℂ) (ell : M →ₗ[A] A), p (ell m) = 0) : m = 0 :=
  projective_eq_zero_of_pointFamily (fun p : A →ₐ[ℂ] ℂ => p) hA m hm

/-- Equality of actual projective-module sections can be checked on the
same pointwise dual evaluations. -/
theorem projective_ext_of_pointFamily (points : P → A →ₐ[ℂ] ℂ)
    (hpoints : PointsDetect points) {m n : M}
    (h : ∀ (p : P) (ell : M →ₗ[A] A), points p (ell m) = points p (ell n)) :
    m = n := by
  apply sub_eq_zero.mp
  apply projective_eq_zero_of_pointFamily points hpoints
  intro p ell
  rw [map_sub, map_sub, h p ell, sub_self]

end ProjectiveModules

section PointDerivations

variable {A : Type*} [CommRing A] [Algebra ℂ A]

/-- Evaluate a regular algebra derivation at a complex point. The target
is the pre-existing actual tangent submodule, not a new tangent model. -/
def specializeDerivation (p : A →ₐ[ℂ] ℂ) (D : Derivation ℂ A A) :
    Infinitesimal.Tangent A p :=
  ⟨p.toLinearMap.comp D.toLinearMap, by
    intro a b
    change p (D (a * b)) = p a * p (D b) + p b * p (D a)
    rw [D.leibniz]
    simp only [map_add, smul_eq_mul, map_mul]⟩

@[simp] theorem specializeDerivation_apply (p : A →ₐ[ℂ] ℂ)
    (D : Derivation ℂ A A) (a : A) :
    (specializeDerivation p D).val a = p (D a) := rfl

/-- An actual cotangent dual yields a point derivation by composing it
with the universal differential and then evaluating at the point. -/
def dualPointTangent (p : A →ₐ[ℂ] ℂ)
    (ell : KaehlerDifferential ℂ A →ₗ[A] A) : Infinitesimal.Tangent A p :=
  specializeDerivation p (ell.compDer (KaehlerDifferential.D ℂ A))

@[simp] theorem dualPointTangent_apply (p : A →ₐ[ℂ] ℂ)
    (ell : KaehlerDifferential ℂ A →ₗ[A] A) (a : A) :
    (dualPointTangent p ell).val a = p (ell (KaehlerDifferential.D ℂ A a)) := rfl

/-- The Leibniz identity is inherited by the constructed point tangent.
This provides its explicit comparison with a tangent derivation of a
polynomial quotient or a principal localization. -/
theorem dualPointTangent_leibniz (p : A →ₐ[ℂ] ℂ)
    (ell : KaehlerDifferential ℂ A →ₗ[A] A) (a b : A) :
    (dualPointTangent p ell).val (a * b) =
      p a * (dualPointTangent p ell).val b +
        p b * (dualPointTangent p ell).val a :=
  (dualPointTangent p ell).property a b

/-- An actual universal differential is detected by actual point
derivations whenever its module is projective and scalar points detect
functions. This auxiliary result also makes the use of dual separation
independent of the radial-coordinate formula. -/
theorem differential_eq_zero_of_pointTangents
    [Module.Projective A (KaehlerDifferential ℂ A)]
    (hA : ComplexPointsSeparate A) (a : A)
    (ha : ∀ (p : A →ₐ[ℂ] ℂ) (D : Infinitesimal.Tangent A p), D.val a = 0) :
    KaehlerDifferential.D ℂ A a = 0 := by
  apply projective_eq_zero_of_pointwise hA
  intro p ell
  exact ha p (dualPointTangent p ell)

end PointDerivations

section RadialForms

variable {A : Type*} [CommRing A] [Algebra ℂ A]
variable {I : Type*} [Fintype I]

/-- Exact evaluation of the actual radial Kahler form against a dual
and at a complex point. The right side is the ambient coordinate
pairing with the actual point derivation constructed from that dual. -/
theorem pointEvaluation_radialForm (p : A →ₐ[ℂ] ℂ)
    (ell : KaehlerDifferential ℂ A →ₗ[A] A)
    (r : I → A) (omega : I → I → ℂ) :
    p (ell (ConeDiagonal.radialForm r omega)) =
      ConePairing.pairing omega (fun i => p (r i))
        (fun i => (dualPointTangent p ell).val (r i)) := by
  unfold ConeDiagonal.radialForm ConePairing.pairing
  simp only [map_sum, LinearMap.map_smul_of_tower, map_smul, smul_eq_mul,
    map_mul, dualPointTangent_apply, Algebra.algebraMap_self_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Tangent annihilation on a detecting family gives equality of the
actual radial form, using projectivity of its cotangent module. -/
theorem radialForm_eq_zero_of_pointFamily
    [Module.Projective A (KaehlerDifferential ℂ A)]
    {P : Type*} (points : P → A →ₐ[ℂ] ℂ) (hpoints : PointsDetect points)
    (r : I → A) (omega : I → I → ℂ)
    (hpoint : ∀ (p : P) (D : Infinitesimal.Tangent A (points p)),
      ConePairing.pairing omega (fun i => points p (r i))
        (fun i => D.val (r i)) = 0) :
    ConeDiagonal.radialForm r omega = 0 := by
  apply projective_eq_zero_of_pointFamily points hpoints
  intro p ell
  rw [pointEvaluation_radialForm]
  exact hpoint p (dualPointTangent (points p) ell)

theorem radialForm_eq_zero_of_pointwise
    [Module.Projective A (KaehlerDifferential ℂ A)]
    (hA : ComplexPointsSeparate A) (r : I → A) (omega : I → I → ℂ)
    (hpoint : ∀ (p : A →ₐ[ℂ] ℂ) (D : Infinitesimal.Tangent A p),
      ConePairing.pairing omega (fun i => p (r i)) (fun i => D.val (r i)) = 0) :
    ConeDiagonal.radialForm r omega = 0 :=
  radialForm_eq_zero_of_pointFamily (fun p : A →ₐ[ℂ] ℂ => p) hA r omega hpoint

/-- Formal smoothness supplies the projectivity needed for detection.
No global choice of a free cotangent basis is required. -/
theorem smooth_radialForm_eq_zero_of_pointwise [Algebra.FormallySmooth ℂ A]
    (hA : ComplexPointsSeparate A) (r : I → A) (omega : I → I → ℂ)
    (hpoint : ∀ (p : A →ₐ[ℂ] ℂ) (D : Infinitesimal.Tangent A p),
      ConePairing.pairing omega (fun i => p (r i)) (fun i => D.val (r i)) = 0) :
    ConeDiagonal.radialForm r omega = 0 :=
  radialForm_eq_zero_of_pointwise hA r omega hpoint

/-- The tangent statement now gives cubic diagonal vanishing directly;
the radial one-form is a proved intermediate equality. -/
theorem smooth_coordinatePairing_mem_cube [Algebra.FormallySmooth ℂ A]
    (hA : ComplexPointsSeparate A) (r : I → A) (omega : I → I → ℂ)
    (hskew : ∀ i j, omega j i = -omega i j)
    (hpoint : ∀ (p : A →ₐ[ℂ] ℂ) (D : Infinitesimal.Tangent A p),
      ConePairing.pairing omega (fun i => p (r i)) (fun i => D.val (r i)) = 0) :
    ConeDiagonal.coordinatePairing r omega ∈ ConeDiagonal.diagonalIdeal A ^ 3 :=
  ConeDiagonal.coordinatePairing_mem_cube r omega hskew
    (smooth_radialForm_eq_zero_of_pointwise hA r omega hpoint)

end RadialForms

section ActualPrincipalConeCharts

variable {I : Type} (S : Set (I → ℂ))
variable (f : DirectionCones.CoordinateRing S)
variable {L : Type*} [CommRing L] [Algebra ℂ L]
variable [Algebra (DirectionCones.CoordinateRing S) L]
variable [IsScalarTower ℂ (DirectionCones.CoordinateRing S) L]
variable [IsLocalization.Away f L]

include f

/-- Scalar detection on the actual principal chart of the given affine
cone. This theorem imposes no smoothness or equation-closedness input. -/
theorem principalConeChart_complexPointsSeparate : ComplexPointsSeparate L :=
  complexPointsSeparate_away f (coordinateRing_complexPointsSeparate S)

variable [Fintype I] [Algebra.FormallySmooth ℂ L]

/-- The smooth principal-chart form of the radial vanishing statement.
The coordinates are the actual restrictions of polynomial generators. -/
theorem principalConeChart_radialForm_eq_zero (omega : I → I → ℂ)
    (hpoint : ∀ (p : L →ₐ[ℂ] ℂ) (D : Infinitesimal.Tangent L p),
      ConePairing.pairing omega
        (fun i => p (algebraMap (DirectionCones.CoordinateRing S) L
          (DirectionCones.coordinate S i)))
        (fun i => D.val (algebraMap (DirectionCones.CoordinateRing S) L
          (DirectionCones.coordinate S i))) = 0) :
    ConeDiagonal.radialForm
      (fun i => algebraMap (DirectionCones.CoordinateRing S) L
        (DirectionCones.coordinate S i)) omega = 0 :=
  smooth_radialForm_eq_zero_of_pointwise
    (principalConeChart_complexPointsSeparate S f)
    (fun i => algebraMap (DirectionCones.CoordinateRing S) L
      (DirectionCones.coordinate S i)) omega hpoint

/-- An alternative formulation only tests the original cone points in
the principal open. This is useful before classifying every complex
point of the quotient as a point of an equation-closed cone. -/
theorem principalConeChart_radialForm_eq_zero_on_cone
    (r : I → L) (omega : I → I → ℂ)
    (hpoint : ∀ (v : S)
      (hv : DirectionCones.quotientEvaluation S v.val v.property f ≠ 0)
      (D : Infinitesimal.Tangent L
        (awayPoint f (DirectionCones.quotientEvaluation S v.val v.property) hv)),
      ConePairing.pairing omega
        (fun i => awayPoint f (DirectionCones.quotientEvaluation S v.val v.property) hv
          (r i)) (fun i => D.val (r i)) = 0) :
    ConeDiagonal.radialForm r omega = 0 := by
  let points : S → DirectionCones.CoordinateRing S →ₐ[ℂ] ℂ :=
    fun v => DirectionCones.quotientEvaluation S v.val v.property
  apply radialForm_eq_zero_of_pointFamily (awayPointFamily (L := L) f points)
    (pointsDetect_away f points (coordinateRing_pointsDetect S)) r omega
  intro v D
  exact hpoint v.val v.property D

/-- The actual cubic diagonal statement on the smooth cone chart is now
derived solely from the pointwise tangent-annihilation input and the
skew matrix. There is no radial-form assumption in this interface. -/
theorem principalConeChart_coordinatePairing_mem_cube
    (omega : I → I → ℂ) (hskew : ∀ i j, omega j i = -omega i j)
    (hpoint : ∀ (p : L →ₐ[ℂ] ℂ) (D : Infinitesimal.Tangent L p),
      ConePairing.pairing omega
        (fun i => p (algebraMap (DirectionCones.CoordinateRing S) L
          (DirectionCones.coordinate S i)))
        (fun i => D.val (algebraMap (DirectionCones.CoordinateRing S) L
          (DirectionCones.coordinate S i))) = 0) :
    ConeDiagonal.coordinatePairing
      (fun i => algebraMap (DirectionCones.CoordinateRing S) L
        (DirectionCones.coordinate S i)) omega ∈ ConeDiagonal.diagonalIdeal L ^ 3 :=
  ConeDiagonal.coordinatePairing_mem_cube _ omega hskew
    (principalConeChart_radialForm_eq_zero S f omega hpoint)

end ActualPrincipalConeCharts

end LeBrunSalamon.Construction.Lines.RadialDetection

end

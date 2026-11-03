import FieldDifferentials
import LSConeIsotropy

/-!
## The cross-pairing is a nonzero constant on an actual fixed-sum family

SOURCE: `lines:cone-addition`, from the curve in a fixed-sum fiber to
`omega(a,b)=c` with `c` a nonzero complex scalar.

The characteristic-zero field-differential assertion formerly isolated
as FD-01 is proved in `FieldDifferentials`. A transcendental element gives an injective
polynomial evaluation map. Formal smoothness and the Jacobi--Zariski
sequence preserve the nonzero differential of the polynomial variable.
All deductions involving the cone pairing and fixed-sum family are proofs.

The maps out of the two affine charts, the integral coefficient ring,
its fraction field, and a complex point are actual algebra maps. No
existence of a curve or dominance conclusion is inserted as an input.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators TensorProduct

namespace LeBrunSalamon.Construction.Lines.CurvePairing

open ConePairing

section FieldConstants

variable {K : Type*} [Field K] [Algebra ℂ K]

/-- Vector-space dual separation turns vanishing against every actual
field derivation into equality of the universal differential itself. -/
theorem universalDifferential_eq_zero_of_all_derivations
    (a : K) (ha : ∀ D : Derivation ℂ K K, D a = 0) :
    KaehlerDifferential.D ℂ K a = 0 := by
  apply (Module.forall_dual_apply_eq_zero_iff K _).mp
  intro ell
  exact ha (ell.compDer (KaehlerDifferential.D ℂ K))

/-- Algebraic closedness of the actual base field converts the standard
algebraicity conclusion into a specified complex scalar. -/
theorem eq_complexScalar_of_all_derivations
    (a : K) (ha : ∀ D : Derivation ℂ K K, D a = 0) :
    ∃ c : ℂ, a = algebraMap ℂ K c := by
  have halg : IsAlgebraic ℂ a :=
    StandardInputs.FieldDifferentials.isAlgebraic_of_universalDifferential_zero
      ℂ K a (universalDifferential_eq_zero_of_all_derivations a ha)
  have hmem : a ∈ algebraicClosure ℂ K := mem_algebraicClosure_iff.mpr halg
  have hbot : algebraicClosure ℂ K = (⊥ : IntermediateField ℂ K) :=
    IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic (algebraicClosure ℂ K)
  rw [hbot] at hmem
  obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp hmem
  exact ⟨c, hc.symm⟩

end FieldConstants

section PullbackRadialForm

variable {I : Type*} [Fintype I]
variable {A B : Type*} [CommRing A] [CommRing B]
variable [Algebra ℂ A] [Algebra ℂ B] [Algebra A B] [IsScalarTower ℂ A B]

/-- The universal property of Kähler differentials evaluates the actual
radial form on any algebra derivation, with the original coefficient map. -/
theorem lift_radialForm (D : Derivation ℂ A B) (r : I → A) (ω : I → I → ℂ) :
    D.liftKaehlerDifferential (ConeDiagonal.radialForm r ω) =
      pairing ω (fun i => algebraMap A B (r i)) (fun i => D (r i)) := by
  unfold ConeDiagonal.radialForm pairing
  simp only [map_sum, LinearMap.map_smul_of_tower, map_smul,
    Derivation.liftKaehlerDifferential_comp_D, Algebra.smul_def]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end PullbackRadialForm

section RadialFormsAlongMaps

variable {I : Type*} [Fintype I]
variable {A K : Type*} [CommRing A] [CommRing K]
variable [Algebra ℂ A] [Algebra ℂ K]

/-- Pull a chart's radial identity through the actual coordinate map
into the coefficient algebra. A derivation of that algebra composes with
the map by the usual scalar tower, so no independent tangent vector is
chosen or presumed to be tangent to the chart. -/
theorem radial_pairing_eq_zero_along_map
    (φ : A →ₐ[ℂ] K) (D : Derivation ℂ K K)
    (r : I → A) (ω : I → I → ℂ)
    (hradial : ConeDiagonal.radialForm r ω = 0) :
    pairing ω (fun i => φ (r i)) (fun i => D (φ (r i))) = 0 := by
  letI : Algebra A K := φ.toAlgebra
  letI : IsScalarTower ℂ A K := IsScalarTower.of_algHom φ
  let d : Derivation ℂ A K := D.compAlgebraMap A
  have h := congrArg d.liftKaehlerDifferential hradial
  rw [lift_radialForm, map_zero] at h
  change pairing ω (fun i => φ (r i)) (fun i => D (φ (r i))) = 0 at h
  exact h

end RadialFormsAlongMaps

section FixedSumInField

variable {I : Type*} [Fintype I]
variable {A B K : Type*} [CommRing A] [CommRing B] [Field K]
variable [Algebra ℂ A] [Algebra ℂ B] [Algebra ℂ K]

/-- The manuscript's derivative cancellation for actual maps from the
two cone charts. Both radial identities are pulled back and the skew
symmetry reverses the second pairing. The fixed-sum equation is an
equality of actual functions in the coefficient field. -/
theorem fixedSum_pairing_derivation_eq_zero
    (φ : A →ₐ[ℂ] K) (ψ : B →ₐ[ℂ] K) (r : I → A) (u : I → B)
    (ω : I → I → ℂ) (hskew : ∀ i j, ω j i = -ω i j)
    (hr : ConeDiagonal.radialForm r ω = 0)
    (hu : ConeDiagonal.radialForm u ω = 0)
    (s : I → ℂ) (hfixed : ∀ i, φ (r i) + ψ (u i) = algebraMap ℂ K (s i))
    (D : Derivation ℂ K K) :
    D (pairing ω (fun i => φ (r i)) (fun i => ψ (u i))) = 0 := by
  apply derivative_pairing_eq_zero_of_fixed_sum D ω
  · exact fixed_sum_derivative D _ _ s hfixed
  · exact radial_pairing_eq_zero_along_map φ D r ω hr
  · rw [pairing_skew ω (fun i j => hskew j i),
      radial_pairing_eq_zero_along_map ψ D u ω hu, neg_zero]

/-- The characteristic-zero field theorem is used only after the
manuscript's fixed-sum calculation has killed every field derivation. -/
theorem fixedSum_pairing_eq_complexScalar
    (φ : A →ₐ[ℂ] K) (ψ : B →ₐ[ℂ] K) (r : I → A) (u : I → B)
    (ω : I → I → ℂ) (hskew : ∀ i j, ω j i = -ω i j)
    (hr : ConeDiagonal.radialForm r ω = 0)
    (hu : ConeDiagonal.radialForm u ω = 0)
    (s : I → ℂ) (hfixed : ∀ i, φ (r i) + ψ (u i) = algebraMap ℂ K (s i)) :
    ∃ c : ℂ, pairing ω (fun i => φ (r i)) (fun i => ψ (u i)) =
      algebraMap ℂ K c :=
  eq_complexScalar_of_all_derivations _
    (fixedSum_pairing_derivation_eq_zero φ ψ r u ω hskew hr hu s hfixed)

end FixedSumInField

section IntegralFamily

variable {I : Type*} [Fintype I]
variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] [IsDomain C]
variable [Algebra ℂ A] [Algebra ℂ B] [Algebra ℂ C]
variable (K : Type*) [Field K] [Algebra C K] [Algebra ℂ K]
variable [IsScalarTower ℂ C K] [IsFractionRing C K]

include K

/-- The constant identity in the function field descends to the actual
coordinate ring of the integral family by its injective fraction map. -/
theorem regularPairing_eq_complexScalar
    (φ : A →ₐ[ℂ] C) (ψ : B →ₐ[ℂ] C) (r : I → A) (u : I → B)
    (ω : I → I → ℂ) (hskew : ∀ i j, ω j i = -ω i j)
    (hr : ConeDiagonal.radialForm r ω = 0)
    (hu : ConeDiagonal.radialForm u ω = 0)
    (s : I → ℂ) (hfixed : ∀ i, φ (r i) + ψ (u i) = algebraMap ℂ C (s i)) :
    ∃ c : ℂ, pairing ω (fun i => φ (r i)) (fun i => ψ (u i)) =
      algebraMap ℂ C c := by
  let j : C →ₐ[ℂ] K := Algebra.algHom ℂ C K
  have hfield : ∀ i, (j.comp φ) (r i) + (j.comp ψ) (u i) =
      algebraMap ℂ K (s i) := by
    intro i
    simpa only [AlgHom.comp_apply, map_add, j.commutes] using congrArg j (hfixed i)
  obtain ⟨c, hc⟩ := fixedSum_pairing_eq_complexScalar
    (j.comp φ) (j.comp ψ) r u ω hskew hr hu s hfield
  refine ⟨c, ?_⟩
  apply IsFractionRing.injective C K
  change j (pairing ω (fun i => φ (r i)) (fun i => ψ (u i))) = j (algebraMap ℂ C c)
  rw [pairing_map, j.commutes]
  exact hc

/-- The scalar is determined by an actual complex point of the family.
This gives the normalization needed to prove that it is nonzero. -/
theorem regularPairing_eq_pointValue
    (φ : A →ₐ[ℂ] C) (ψ : B →ₐ[ℂ] C) (r : I → A) (u : I → B)
    (ω : I → I → ℂ) (hskew : ∀ i j, ω j i = -ω i j)
    (hr : ConeDiagonal.radialForm r ω = 0)
    (hu : ConeDiagonal.radialForm u ω = 0)
    (s : I → ℂ) (hfixed : ∀ i, φ (r i) + ψ (u i) = algebraMap ℂ C (s i))
    (p : C →ₐ[ℂ] ℂ) :
    pairing ω (fun i => φ (r i)) (fun i => ψ (u i)) =
      algebraMap ℂ C (pairing ω (fun i => p (φ (r i))) (fun i => p (ψ (u i)))) := by
  obtain ⟨c, hc⟩ := regularPairing_eq_complexScalar K φ ψ r u ω hskew hr hu s hfixed
  have hvalue : pairing ω (fun i => p (φ (r i))) (fun i => p (ψ (u i))) = c := by
    rw [← pairing_map p, hc]
    exact p.commutes c
  rw [hvalue]
  exact hc

/-- A nonorthogonal pair at one actual complex point makes the regular
cross-pairing a unit on the entire integral affine family. -/
theorem regularPairing_isUnit_of_nonorthogonal_point
    (φ : A →ₐ[ℂ] C) (ψ : B →ₐ[ℂ] C) (r : I → A) (u : I → B)
    (ω : I → I → ℂ) (hskew : ∀ i j, ω j i = -ω i j)
    (hr : ConeDiagonal.radialForm r ω = 0)
    (hu : ConeDiagonal.radialForm u ω = 0)
    (s : I → ℂ) (hfixed : ∀ i, φ (r i) + ψ (u i) = algebraMap ℂ C (s i))
    (p : C →ₐ[ℂ] ℂ)
    (hp : pairing ω (fun i => p (φ (r i))) (fun i => p (ψ (u i))) ≠ 0) :
    IsUnit (pairing ω (fun i => φ (r i)) (fun i => ψ (u i))) := by
  rw [regularPairing_eq_pointValue K φ ψ r u ω hskew hr hu s hfixed p]
  exact (isUnit_iff_ne_zero.mpr hp).map (algebraMap ℂ C)

end IntegralFamily

section ConsequencesOfTheConstant

variable {I : Type*} [Fintype I]
variable {C : Type*} [CommRing C] [Algebra ℂ C]

/-- A unit pairing stays nonzero at every actual complex point of the
family. This applies to the unit proved by the fixed-sum argument above. -/
theorem pairing_nonzero_at_every_point (ω : I → I → ℂ) (a b : I → C)
    (hunit : IsUnit (pairing ω a b)) (p : C →ₐ[ℂ] ℂ) :
    pairing ω (fun i => p (a i)) (fun i => p (b i)) ≠ 0 := by
  rw [← pairing_map p]
  exact (hunit.map p.toRingHom).ne_zero

/-- Neither coordinate of the curve of pairs can meet its cone vertex. -/
theorem coordinates_nonzero_at_every_point (ω : I → I → ℂ) (a b : I → C)
    (hunit : IsUnit (pairing ω a b)) (p : C →ₐ[ℂ] ℂ) :
    (fun i => p (a i)) ≠ 0 ∧ (fun i => p (b i)) ≠ 0 := by
  have hp := pairing_nonzero_at_every_point ω a b hunit p
  constructor
  · intro ha
    rw [ha] at hp
    exact hp (pairing_zero_left ω _)
  · intro hb
    rw [hb] at hp
    exact hp (pairing_zero_right ω _)

/-- The unit version also excludes the zero locus at every prime, so
the nonorthogonality condition holds scheme-theoretically on the family. -/
theorem pairing_avoids_every_prime (ω : I → I → ℂ) (a b : I → C)
    (hunit : IsUnit (pairing ω a b)) (p : PrimeSpectrum C) :
    pairing ω a b ∉ p.asIdeal :=
  Ideal.notMem_of_isUnit p.asIdeal hunit

end ConsequencesOfTheConstant

section ActualConeCharts

variable {I : Type} [Fintype I]
variable (S T : Set (I → ℂ))
variable (hS : ConeRadial.IsCone S) (hT : ConeRadial.IsCone T)
variable (f : DirectionCones.CoordinateRing S) (g : DirectionCones.CoordinateRing T)
variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] [IsDomain C]
variable [Algebra ℂ A] [Algebra ℂ B] [Algebra ℂ C]
variable [Algebra (DirectionCones.CoordinateRing S) A]
variable [Algebra (DirectionCones.CoordinateRing T) B]
variable [IsScalarTower ℂ (DirectionCones.CoordinateRing S) A]
variable [IsScalarTower ℂ (DirectionCones.CoordinateRing T) B]
variable [IsLocalization.Away f A] [IsLocalization.Away g B]
variable [Algebra.FormallySmooth ℂ A] [Algebra.FormallySmooth ℂ B]
variable (K : Type*) [Field K] [Algebra C K] [Algebra ℂ K]
variable [IsScalarTower ℂ C K] [IsFractionRing C K]

include hS hT f g K

/-- Direct specialization to actual smooth principal charts of two
possibly different cones. Their tangent isotropy supplies the radial identities;
the fixed-sum family and its chosen point supply a nonzero constant
pairing. In particular, radial-form vanishing is no longer a premise. -/
theorem localizedPairing_isUnit_of_tangent_isotropy
    (ω : I → I → ℂ) (hskew : ∀ i j, ω j i = -ω i j)
    (hA : ∀ (p : A →ₐ[ℂ] ℂ) (D E : Infinitesimal.Tangent A p),
      pairing ω (fun i => D.val (ConeRadial.localizedCoordinate (L := A) S i))
        (fun i => E.val (ConeRadial.localizedCoordinate (L := A) S i)) = 0)
    (hB : ∀ (p : B →ₐ[ℂ] ℂ) (D E : Infinitesimal.Tangent B p),
      pairing ω (fun i => D.val (ConeRadial.localizedCoordinate (L := B) T i))
        (fun i => E.val (ConeRadial.localizedCoordinate (L := B) T i)) = 0)
    (φ : A →ₐ[ℂ] C) (ψ : B →ₐ[ℂ] C) (s : I → ℂ)
    (hfixed : ∀ i,
      φ (ConeRadial.localizedCoordinate (L := A) S i) +
        ψ (ConeRadial.localizedCoordinate (L := B) T i) = algebraMap ℂ C (s i))
    (p : C →ₐ[ℂ] ℂ)
    (hp : pairing ω
      (fun i => p (φ (ConeRadial.localizedCoordinate (L := A) S i)))
      (fun i => p (ψ (ConeRadial.localizedCoordinate (L := B) T i))) ≠ 0) :
    IsUnit (pairing ω
      (fun i => φ (ConeRadial.localizedCoordinate (L := A) S i))
      (fun i => ψ (ConeRadial.localizedCoordinate (L := B) T i))) :=
  regularPairing_isUnit_of_nonorthogonal_point K φ ψ
    (ConeRadial.localizedCoordinate (L := A) S)
    (ConeRadial.localizedCoordinate (L := B) T) ω hskew
    (ConeIsotropy.radialForm_eq_zero_of_tangent_isotropy S hS f (L := A) ω hA)
    (ConeIsotropy.radialForm_eq_zero_of_tangent_isotropy T hT g (L := B) ω hB)
    s hfixed p hp

end ActualConeCharts

end LeBrunSalamon.Construction.Lines.CurvePairing

end

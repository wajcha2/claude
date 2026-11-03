import LSConeRadial
import LSConeLocalization

/-!
## Faithful ambient coordinates for cone tangent spaces

SOURCE: `lines:cone-addition`. The tangent-space isotropy assertion must
refer to the actual derivative of the cone inclusion. Coordinate values
determine a point derivation on a polynomial quotient and on every
localization at which the point exists. Thus the ambient tangent image
below is an actual embedded vector space, not an independent label.

New continuation; compilation remains subject to the 35,000-line gate.
-/

noncomputable section
set_option autoImplicit false

namespace LeBrunSalamon.Construction.Lines.ConeRadial

open DirectionCones Infinitesimal

section TangentCoordinates

variable {A : Type*} [CommRing A] [Algebra ℂ A]

/-- Equality of actual first-order point lifts detects the derivation. -/
theorem tangent_eq_of_dual_eq (p : A →ₐ[ℂ] ℂ) (D E : Tangent A p)
    (h : tangentToDual p D = tangentToDual p E) : D = E := by
  apply Subtype.ext
  ext a
  have he := congrArg (fun f : A →ₐ[ℂ] Dual => linearCoefficient (f a)) h
  change linearCoefficient (algebraMap ℂ Dual (p a) +
      epsilon * algebraMap ℂ Dual (D.val a)) =
    linearCoefficient (algebraMap ℂ Dual (p a) +
      epsilon * algebraMap ℂ Dual (E.val a)) at he
  simpa only [linearCoefficient_normalForm] using he

/-- Algebra generators detect all tangent coordinates by their actual
dual-number lifts. This proof also applies to nonreduced quotients. -/
theorem tangent_eq_of_generatorValues {ι : Type*}
    (r : ι → A) (hgen : Algebra.adjoin ℂ (Set.range r) = ⊤)
    (p : A →ₐ[ℂ] ℂ) (D E : Tangent A p)
    (h : ∀ i, D.val (r i) = E.val (r i)) : D = E := by
  apply tangent_eq_of_dual_eq p D E
  apply AlgHom.ext_of_adjoin_eq_top hgen
  rintro _ ⟨i, rfl⟩
  change algebraMap ℂ Dual (p (r i)) + epsilon * algebraMap ℂ Dual (D.val (r i)) =
    algebraMap ℂ Dual (p (r i)) + epsilon * algebraMap ℂ Dual (E.val (r i))
  rw [h i]

/-- Denominators impose no extra tangent-coordinate data once the point
is a point of the actual localization. -/
theorem tangent_eq_of_localized_generatorValues
    {L : Type*} [CommRing L] [Algebra A L] [Algebra ℂ L]
    [IsScalarTower ℂ A L] (M : Submonoid A) [IsLocalization M L]
    {ι : Type*} (r : ι → A) (hgen : Algebra.adjoin ℂ (Set.range r) = ⊤)
    (p : L →ₐ[ℂ] ℂ) (D E : Tangent L p)
    (h : ∀ i, D.val (algebraMap A L (r i)) = E.val (algebraMap A L (r i))) :
    D = E := by
  apply tangent_eq_of_dual_eq p D E
  apply IsLocalization.algHom_ext M
  apply AlgHom.ext_of_adjoin_eq_top hgen
  rintro _ ⟨i, rfl⟩
  change algebraMap ℂ Dual (p (algebraMap A L (r i))) +
      epsilon * algebraMap ℂ Dual (D.val (algebraMap A L (r i))) =
    algebraMap ℂ Dual (p (algebraMap A L (r i))) +
      epsilon * algebraMap ℂ Dual (E.val (algebraMap A L (r i)))
  rw [h i]

theorem tangentCoordinates_injective {ι : Type}
    (S : Set (ι → ℂ)) (p : CoordinateRing S →ₐ[ℂ] ℂ) :
    Function.Injective (tangentCoordinates S p) := by
  intro D E h
  apply tangent_eq_of_generatorValues (coordinate S)
    (ConeArcs.quotientCoordinates_generate (vanishingIdeal S)) p D E
  intro i
  exact congrFun h i

end TangentCoordinates

section LocalizedCoordinates

variable {ι : Type} (S : Set (ι → ℂ))
    {L : Type*} [CommRing L] [Algebra (CoordinateRing S) L] [Algebra ℂ L]
    [IsScalarTower ℂ (CoordinateRing S) L]

/-- The derivative of the actual ambient coordinate functions. -/
def localizedTangentCoordinates (p : L →ₐ[ℂ] ℂ) :
    Tangent L p →ₗ[ℂ] (ι → ℂ) where
  toFun D i := D.val (localizedCoordinate (L := L) S i)
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

theorem localizedTangentCoordinates_injective
    (M : Submonoid (CoordinateRing S)) [IsLocalization M L]
    (p : L →ₐ[ℂ] ℂ) :
    Function.Injective (localizedTangentCoordinates S p) := by
  intro D E h
  apply tangent_eq_of_localized_generatorValues M (coordinate S)
    (ConeArcs.quotientCoordinates_generate (vanishingIdeal S)) p D E
  intro i
  exact congrFun h i

/-- The embedded tangent subspace of the affine ambient coordinate space. -/
def ambientTangent (p : L →ₐ[ℂ] ℂ) : Submodule ℂ (ι → ℂ) :=
  LinearMap.range (localizedTangentCoordinates S p)

theorem radial_mem_ambientTangent (hcone : IsCone S)
    (M : Submonoid (CoordinateRing S)) [IsLocalization M L]
    (p : L →ₐ[ℂ] ℂ) :
    (fun i => p (localizedCoordinate (L := L) S i)) ∈ ambientTangent S p := by
  refine ⟨localizedRadial S hcone M p, ?_⟩
  funext i
  exact localizedRadial_coordinate S hcone M p i

/-- Isotropy of this genuine ambient subspace is exactly the statement
on all actual point derivations used in the radial-form proof. -/
theorem ambientTangent_isotropic_iff [Fintype ι]
    (p : L →ₐ[ℂ] ℂ) (ω : ι → ι → ℂ) :
    (∀ v ∈ ambientTangent S p, ∀ w ∈ ambientTangent S p,
      ConePairing.pairing ω v w = 0) ↔
    (∀ D E : Tangent L p,
      ConePairing.pairing ω
        (fun i => D.val (localizedCoordinate (L := L) S i))
        (fun i => E.val (localizedCoordinate (L := L) S i)) = 0) := by
  constructor
  · intro h D E
    exact h _ ⟨D, rfl⟩ _ ⟨E, rfl⟩
  · intro h v hv w hw
    obtain ⟨D, rfl⟩ := hv
    obtain ⟨E, rfl⟩ := hw
    exact h D E

end LocalizedCoordinates

/-- The concrete component cones already constructed from the actual
projective embedding satisfy precisely the scaling input used above. -/
theorem componentConePoints_isCone {N : ℕ} (D : ReducedProjectiveDirections N)
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (e : V ≃ₗ[ℂ] (Fin (N+1) → ℂ)) (C : D.Component) :
    IsCone (D.componentConePoints e C) := by
  intro v hv c
  exact D.componentConePoints_smul e C hv c

end LeBrunSalamon.Construction.Lines.ConeRadial

end

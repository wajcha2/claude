import LSAffineCurveSelection
import LSConeRescaledArcs
import LSConeOpen

/-!
## The fixed-sum quotient is the actual affine addition fiber

The universal algebra map is constructed explicitly from the two cone
maps and their fixed-sum identity. The resulting square is then proved
to be a pushout of commutative rings and hence a pullback of spectra.
This identifies the ring used for curve selection with the existing
scheme-theoretic fiber of `DirectionCones.additionMorphism`.

SOURCE ONLY, UNCOMPILED. No compiler was invoked while preparing this file.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace LeBrunSalamon.Construction.Lines.AffineCurveSelection

open DirectionCones

variable {ι : Type}

theorem fixedSumIdeal_le_ker
    (S T : Set (ι → ℂ)) (s : ι → ℂ)
    {A : Type*} [CommRing A] [Algebra ℂ A]
    (a : CoordinateRing S →ₐ[ℂ] A) (b : CoordinateRing T →ₐ[ℂ] A)
    (hfixed : ∀ i, a (coordinate S i) + b (coordinate T i) = algebraMap ℂ A (s i)) :
    fixedSumIdeal S T s ≤
      RingHom.ker (MvPolynomial.aeval (fun i => a (coordinate S i))).toRingHom := by
  have hcomp :
      (MvPolynomial.aeval (fun i => a (coordinate S i))).comp
        (fixedSumSubstitution s) =
      MvPolynomial.aeval (fun i => b (coordinate T i)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, fixedSumSubstitution, MvPolynomial.aeval_X,
      map_sub, MvPolynomial.aeval_C]
    rw [← hfixed i]
    ring
  unfold fixedSumIdeal
  apply sup_le
  · intro p hp
    exact LaurentRescaling.quotientMap_satisfiesEquations S a hp
  · rw [Ideal.map_le_iff_le_comap]
    intro p hp
    change MvPolynomial.aeval (fun i => a (coordinate S i))
      (fixedSumSubstitution s p) = 0
    change ((MvPolynomial.aeval (fun i => a (coordinate S i))).comp
      (fixedSumSubstitution s)) p = 0
    rw [hcomp]
    exact LaurentRescaling.quotientMap_satisfiesEquations T b hp

def fixedSumLift
    (S T : Set (ι → ℂ)) (s : ι → ℂ)
    {A : Type*} [CommRing A] [Algebra ℂ A]
    (a : CoordinateRing S →ₐ[ℂ] A) (b : CoordinateRing T →ₐ[ℂ] A)
    (hfixed : ∀ i, a (coordinate S i) + b (coordinate T i) = algebraMap ℂ A (s i)) :
    FixedSumRing S T s →ₐ[ℂ] A :=
  Ideal.Quotient.liftₐ (fixedSumIdeal S T s)
    (MvPolynomial.aeval (fun i => a (coordinate S i)))
    (fun _ hp => fixedSumIdeal_le_ker S T s a b hfixed hp)

@[simp]
theorem fixedSumLift_coordinate
    (S T : Set (ι → ℂ)) (s : ι → ℂ)
    {A : Type*} [CommRing A] [Algebra ℂ A]
    (a : CoordinateRing S →ₐ[ℂ] A) (b : CoordinateRing T →ₐ[ℂ] A)
    (hfixed : ∀ i, a (coordinate S i) + b (coordinate T i) = algebraMap ℂ A (s i))
    (i : ι) :
    fixedSumLift S T s a b hfixed
      (ConeArcs.quotientCoordinate (fixedSumIdeal S T s) i) = a (coordinate S i) :=
  MvPolynomial.aeval_X (fun j => a (coordinate S j)) i

theorem fixedSumLift_first
    (S T : Set (ι → ℂ)) (s : ι → ℂ)
    {A : Type*} [CommRing A] [Algebra ℂ A]
    (a : CoordinateRing S →ₐ[ℂ] A) (b : CoordinateRing T →ₐ[ℂ] A)
    (hfixed : ∀ i, a (coordinate S i) + b (coordinate T i) = algebraMap ℂ A (s i)) :
    (fixedSumLift S T s a b hfixed).comp (fixedFirst S T s) = a := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  change fixedSumLift S T s a b hfixed
    (fixedFirst S T s (coordinate S i)) = a (coordinate S i)
  rw [fixedFirst_coordinate, fixedSumLift_coordinate]

theorem fixedSumLift_second
    (S T : Set (ι → ℂ)) (s : ι → ℂ)
    {A : Type*} [CommRing A] [Algebra ℂ A]
    (a : CoordinateRing S →ₐ[ℂ] A) (b : CoordinateRing T →ₐ[ℂ] A)
    (hfixed : ∀ i, a (coordinate S i) + b (coordinate T i) = algebraMap ℂ A (s i)) :
    (fixedSumLift S T s a b hfixed).comp (fixedSecond S T s) = b := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  change fixedSumLift S T s a b hfixed
    (fixedSecond S T s (coordinate T i)) = b (coordinate T i)
  rw [fixedSecond_coordinate, map_sub, AlgHom.commutes, fixedSumLift_coordinate,
    ← hfixed i]
  ring

theorem fixedFirst_surjective (S T : Set (ι → ℂ)) (s : ι → ℂ) :
    Function.Surjective (fixedFirst S T s) := by
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨Ideal.Quotient.mk (vanishingIdeal S) p, rfl⟩

/-- The map from the original tensor-product coordinate ring to the
fixed-sum quotient, retaining the exact original cone-factor maps. -/
def fixedPair (S T : Set (ι → ℂ)) (s : ι → ℂ) :
    ProductRing S T →ₐ[ℂ] FixedSumRing S T s :=
  Algebra.TensorProduct.lift (fixedFirst S T s) (fixedSecond S T s)
    (fun _ _ => Commute.all _ _)

@[simp]
theorem fixedPair_includeLeft (S T : Set (ι → ℂ)) (s : ι → ℂ)
    (x : CoordinateRing S) :
    fixedPair S T s (Algebra.TensorProduct.includeLeft (S := ℂ) x) = fixedFirst S T s x := by
  simp [fixedPair]

@[simp]
theorem fixedPair_includeRight (S T : Set (ι → ℂ)) (s : ι → ℂ)
    (x : CoordinateRing T) :
    fixedPair S T s (Algebra.TensorProduct.includeRight x) = fixedSecond S T s x := by
  simp [fixedPair]

theorem fixedPair_surjective (S T : Set (ι → ℂ)) (s : ι → ℂ) :
    Function.Surjective (fixedPair S T s) := by
  intro x
  obtain ⟨a, rfl⟩ := fixedFirst_surjective S T s x
  exact ⟨Algebra.TensorProduct.includeLeft (S := ℂ) a, fixedPair_includeLeft S T s a⟩

theorem fixedPair_addition (S T : Set (ι → ℂ)) (s : ι → ℂ) :
    (fixedPair S T s).comp (additionComorphism S T) =
      (Algebra.ofId ℂ (FixedSumRing S T s)).comp (MvPolynomial.aeval s) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, additionComorphism_X, firstCoordinate,
    secondCoordinate, map_add, fixedPair_includeLeft, fixedPair_includeRight,
    MvPolynomial.aeval_X, Algebra.ofId_apply]
  exact fixedSum_equation S T s i

theorem fixedSumLift_pair
    (S T : Set (ι → ℂ)) (s : ι → ℂ)
    {A : Type*} [CommRing A] [Algebra ℂ A]
    (a : CoordinateRing S →ₐ[ℂ] A) (b : CoordinateRing T →ₐ[ℂ] A)
    (hfixed : ∀ i, a (coordinate S i) + b (coordinate T i) = algebraMap ℂ A (s i)) :
    (fixedSumLift S T s a b hfixed).comp (fixedPair S T s) =
      Algebra.TensorProduct.lift a b (fun _ _ => Commute.all _ _) := by
  apply Algebra.TensorProduct.ext'
  intro x y
  simp only [AlgHom.comp_apply, fixedPair, Algebra.TensorProduct.lift_tmul, map_mul]
  congr 1
  · exact AlgHom.congr_fun (fixedSumLift_first S T s a b hfixed) x
  · exact AlgHom.congr_fun (fixedSumLift_second S T s a b hfixed) y

set_option backward.isDefEq.respectTransparency.types false in
/-- This is a pushout in the category of all commutative rings. The
target complex algebra structure is derived from the given map from C,
so the result is stronger than a test on preselected complex algebras. -/
theorem fixedSum_pushout (S T : Set (ι → ℂ)) (s : ι → ℂ) :
    IsPushout
      (CommRingCat.ofHom (R := CoordinatePolynomial ι) (S := ProductRing S T)
        (additionComorphism S T).toRingHom)
      (CommRingCat.ofHom (MvPolynomial.eval s))
      (CommRingCat.ofHom (R := ProductRing S T) (S := FixedSumRing S T s)
        (fixedPair S T s).toRingHom)
      (CommRingCat.ofHom (algebraMap ℂ (FixedSumRing S T s))) := by
  apply IsPushout.mk'
  · apply CommRingCat.hom_ext
    exact congrArg AlgHom.toRingHom (fixedPair_addition S T s)
  · intro D f g h _hC
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    obtain ⟨y, rfl⟩ := fixedPair_surjective S T s x
    exact congrArg (fun h : CommRingCat.of (ProductRing S T) ⟶ D => h.hom y) h
  · intro D a b hab
    letI : Algebra ℂ D := b.hom.toAlgebra
    let aRing : ProductRing S T →+* D := a.hom
    let scalarMap := @Algebra.algebraMap ℂ (ProductRing S T)
      (inferInstance : CommSemiring ℂ)
      (inferInstance : Semiring (ProductRing S T))
      (inferInstance : Algebra ℂ (ProductRing S T))
    have hsc : ∀ c : ℂ,
        aRing (scalarMap c) = algebraMap ℂ D c := by
      intro c
      have h := congrArg
        (fun h : CommRingCat.of (CoordinatePolynomial ι) ⟶ D =>
          h.hom (MvPolynomial.C c)) hab
      change a.hom ((additionComorphism S T) (MvPolynomial.C c)) =
        b.hom (MvPolynomial.eval s (MvPolynomial.C c)) at h
      rw [MvPolynomial.eval_C] at h
      change a.hom ((additionComorphism S T)
        (algebraMap ℂ (CoordinatePolynomial ι) c)) = algebraMap ℂ D c at h
      rw [(additionComorphism S T).commutes c] at h
      exact h
    let aAlg : ProductRing S T →ₐ[ℂ] D := { aRing with commutes' := hsc }
    let aFirst : CoordinateRing S →ₐ[ℂ] D :=
      aAlg.comp Algebra.TensorProduct.includeLeft
    let aSecond : CoordinateRing T →ₐ[ℂ] D :=
      aAlg.comp Algebra.TensorProduct.includeRight
    have hfixed : ∀ i,
        aFirst (coordinate S i) + aSecond (coordinate T i) = algebraMap ℂ D (s i) := by
      intro i
      have h := congrArg
        (fun h : CommRingCat.of (CoordinatePolynomial ι) ⟶ D =>
          h.hom (MvPolynomial.X i)) hab
      change a.hom ((additionComorphism S T) (MvPolynomial.X i)) =
        b.hom (MvPolynomial.eval s (MvPolynomial.X i)) at h
      rw [additionComorphism_X, MvPolynomial.eval_X, RingHom.map_add aRing] at h
      exact h
    let l := fixedSumLift S T s aFirst aSecond hfixed
    refine ⟨CommRingCat.ofHom l.toRingHom, ?_, ?_⟩
    · apply CommRingCat.hom_ext
      apply Algebra.TensorProduct.ringHom_ext
      · apply RingHom.ext
        intro x
        change l (fixedPair S T s (Algebra.TensorProduct.includeLeft (S := ℂ) x)) =
          a.hom (Algebra.TensorProduct.includeLeft (S := ℂ) x)
        rw [fixedPair_includeLeft]
        exact AlgHom.congr_fun (fixedSumLift_first S T s aFirst aSecond hfixed) x
      · apply RingHom.ext
        intro x
        change l (fixedPair S T s (Algebra.TensorProduct.includeRight x)) =
          a.hom (Algebra.TensorProduct.includeRight x)
        rw [fixedPair_includeRight]
        exact AlgHom.congr_fun (fixedSumLift_second S T s aFirst aSecond hfixed) x
    · apply CommRingCat.hom_ext
      apply RingHom.ext
      intro c
      exact l.commutes c

/-- The explicit quotient used for curve selection is the fiber of
the actual addition morphism over the actual complex vector s. -/
theorem fixedSum_isPullback (S T : Set (ι → ℂ)) (s : ι → ℂ) :
    IsPullback
      (affineMap (fixedPair S T s)) (affineBaseMap (FixedSumRing S T s))
      (additionMorphism S T) (coordinatePoint s) :=
  AlgebraicGeometry.isPullback_SpecMap_of_isPushout _ _ _ _ (fixedSum_pushout S T s)

section NonorthogonalFiber

variable [Fintype ι]

theorem fixedPair_pairingFunction (S T : Set (ι → ℂ))
    (s : ι → ℂ) (omega : ι → ι → ℂ) :
    fixedPair S T s (ConeGeometry.pairingFunction S T omega) =
      fixedPairing S T s omega := by
  simpa only [ConeGeometry.pairingFunction, fixedPairing,
    firstCoordinate, secondCoordinate, fixedPair_includeLeft, fixedPair_includeRight] using
    ConePairing.pairing_map (fixedPair S T s) omega
      (firstCoordinate S T) (secondCoordinate S T)

/-- The actual localization morphism from the nonorthogonal part of
the fixed-sum fiber to that fiber. -/
def nonorthogonalFiberLocalization (S T : Set (ι → ℂ))
    (s : ι → ℂ) (omega : ι → ι → ℂ) :
    Spec (CommRingCat.of (NonorthogonalFiberRing S T s omega)) ⟶
      Spec (CommRingCat.of (FixedSumRing S T s)) :=
  affineMap (Algebra.algHom ℂ (FixedSumRing S T s)
    (NonorthogonalFiberRing S T s omega))

instance nonorthogonalFiberLocalization_isOpenImmersion
    (S T : Set (ι → ℂ)) (s : ι → ℂ) (omega : ι → ι → ℂ) :
    IsOpenImmersion (nonorthogonalFiberLocalization S T s omega) :=
  inferInstanceAs (IsOpenImmersion
    (Spec.map (CommRingCat.ofHom (algebraMap (FixedSumRing S T s)
      (Localization.Away (fixedPairing S T s omega))))))

/-- Restriction lands in the original product's nonorthogonality open,
because its original pairing function is the inverted fiber element. -/
def nonorthogonalFiberToOpen (S T : Set (ι → ℂ))
    (s : ι → ℂ) (omega : ι → ι → ℂ) :
    Spec (CommRingCat.of (NonorthogonalFiberRing S T s omega)) ⟶
      (ConeGeometry.nonorthogonalOpen S T omega).toScheme :=
  IsOpenImmersion.lift (ConeGeometry.nonorthogonalOpen S T omega).ι
    (nonorthogonalFiberLocalization S T s omega ≫ affineMap (fixedPair S T s)) (by
      rw [Scheme.Opens.range_ι]
      rintro z ⟨p, rfl⟩
      change algebraMap (FixedSumRing S T s) (NonorthogonalFiberRing S T s omega)
        (fixedPair S T s (ConeGeometry.pairingFunction S T omega)) ∉ p.asIdeal
      rw [fixedPair_pairingFunction]
      exact Ideal.notMem_of_isUnit p.asIdeal
        (IsLocalization.Away.algebraMap_isUnit (fixedPairing S T s omega)))

@[reassoc]
theorem nonorthogonalFiberToOpen_ι (S T : Set (ι → ℂ))
    (s : ι → ℂ) (omega : ι → ι → ℂ) :
    nonorthogonalFiberToOpen S T s omega ≫
        (ConeGeometry.nonorthogonalOpen S T omega).ι =
      nonorthogonalFiberLocalization S T s omega ≫ affineMap (fixedPair S T s) :=
  IsOpenImmersion.lift_fac _ _ _

/-- The localization is exactly the inverse image of the original
nonorthogonality open, not a separately chosen open subset. -/
theorem nonorthogonalFiber_isPullback_open (S T : Set (ι → ℂ))
    (s : ι → ℂ) (omega : ι → ι → ℂ) :
    IsPullback (nonorthogonalFiberToOpen S T s omega)
      (nonorthogonalFiberLocalization S T s omega)
      (ConeGeometry.nonorthogonalOpen S T omega).ι (affineMap (fixedPair S T s)) := by
  apply IsOpenImmersion.isPullback
  · exact (nonorthogonalFiberToOpen_ι S T s omega).symm
  · rw [Scheme.Opens.opensRange_ι]
    exact
      (SpecMap_preimage_basicOpen
        (R := CommRingCat.of (ProductRing S T))
        (S := CommRingCat.of (FixedSumRing S T s))
        (CommRingCat.ofHom (R := ProductRing S T) (S := FixedSumRing S T s)
          (fixedPair S T s).toRingHom)
        (ConeGeometry.pairingFunction S T omega)).trans
      ((congrArg (fun f : FixedSumRing S T s =>
          PrimeSpectrum.basicOpen (R := FixedSumRing S T s) f)
        (fixedPair_pairingFunction S T s omega)).trans
        (Scheme.Hom.opensRange_localizationAway
          (R := CommRingCat.of (FixedSumRing S T s))
          (fixedPairing S T s omega)).symm)

/-- The very ring in which the integral curve was selected is the
scheme-theoretic fiber of the original nonorthogonal addition map. -/
theorem nonorthogonalFiber_isPullback (S T : Set (ι → ℂ))
    (s : ι → ℂ) (omega : ι → ι → ℂ) :
    IsPullback (nonorthogonalFiberToOpen S T s omega)
      (affineBaseMap (NonorthogonalFiberRing S T s omega))
      (ConeGeometry.nonorthogonalAddition S T omega) (coordinatePoint s) := by
  have h := (nonorthogonalFiber_isPullback_open S T s omega).paste_vert
    (fixedSum_isPullback S T s)
  simpa only [nonorthogonalFiberLocalization, affineMap_overC,
    ConeGeometry.nonorthogonalAddition] using h

end NonorthogonalFiber

end LeBrunSalamon.Construction.Lines.AffineCurveSelection

end

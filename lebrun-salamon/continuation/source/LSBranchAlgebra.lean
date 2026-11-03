import LSContactLineTests

/-!
The ordinary local algebra in the transverse branch argument.  The
completion is the actual maximal-ideal completion.  Faithful flatness
descends the ideal equality, so the ramification index is attached to
the original local-ring map rather than to a formal numerical label.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace LeBrunSalamon.Construction.Descent.BranchAlgebra

abbrev Completion (R : Type*) [CommRing R] [IsLocalRing R] :=
  AdicCompletion (IsLocalRing.maximalIdeal R) R

variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/-- A power-series completion detects that the original ring is a
domain, using the actual injective completion homomorphism. -/
theorem domain_of_completion
    (q : Completion R ≃+* PowerSeries ℂ) : IsDomain R := by
  letI : Module.FaithfullyFlat R (Completion R) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact Function.Injective.isDomain
    (q.toRingHom.comp (algebraMap R (Completion R)))
    (q.injective.comp (FaithfulSMul.algebraMap_injective R (Completion R)))

/-- Completion preserves the minimal number of generators of the
maximal ideal.  A one-variable power-series completion therefore makes
the original Noetherian local domain a discrete valuation ring. -/
theorem dvr_of_completion [IsDomain R]
    (q : Completion R ≃+* PowerSeries ℂ) : IsDiscreteValuationRing R := by
  apply IsLocalRing.finrank_CotangentSpace_eq_one_iff.mp
  rw [← IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
  calc
    (IsLocalRing.maximalIdeal R).spanFinrank =
        (IsLocalRing.maximalIdeal (Completion R)).spanFinrank :=
      AdicCompletion.spanFinrank_maximalIdeal_eq.symm
    _ = ((IsLocalRing.maximalIdeal (Completion R)).map q.toRingHom).spanFinrank :=
      (Ideal.spanFinrank_map_eq_of_ringEquiv q _).symm
    _ = (IsLocalRing.maximalIdeal (PowerSeries ℂ)).spanFinrank := by
      have hmax : (IsLocalRing.maximalIdeal (Completion R)).map q.toRingHom =
          IsLocalRing.maximalIdeal (PowerSeries ℂ) :=
        IsLocalRing.map_ringEquiv_maximalIdeal q
      exact congrArg (fun I : Ideal (PowerSeries ℂ) => I.spanFinrank) hmax
    _ = 1 := by
      rw [PowerSeries.maximalIdeal_eq_span_X]
      exact Submodule.spanFinrank_singleton PowerSeries.X_ne_zero

variable {B : Type*} [CommRing B] [IsLocalRing B]

/-- The normalized completed parameter determines the exact image of
the base maximal ideal in the original ring.  Both changes of ideals
below are injective: completion is faithfully flat and q is an actual
ring isomorphism. -/
theorem maximalIdeal_image_eq_pow
    (f : B →+* R) (τ : B)
    (hτ : IsLocalRing.maximalIdeal B = Ideal.span {τ})
    (q : Completion R ≃+* PowerSeries ℂ) (e : ℕ)
    (u : (PowerSeries ℂ)ˣ)
    (hq : q (algebraMap R (Completion R) (f τ)) = PowerSeries.X ^ e * u.val) :
    (IsLocalRing.maximalIdeal B).map f = (IsLocalRing.maximalIdeal R) ^ e := by
  letI : Module.FaithfullyFlat R (Completion R) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  apply Ideal.map_injective_of_faithfullyFlat (A := R) (B := Completion R)
  apply q.idealComapOrderIso.symm.injective
  change (((IsLocalRing.maximalIdeal B).map f).map
      (algebraMap R (Completion R))).map q.toRingHom =
    (((IsLocalRing.maximalIdeal R) ^ e).map
      (algebraMap R (Completion R))).map q.toRingHom
  have hnormalized : q.toRingHom (algebraMap R (Completion R) (f τ)) =
      PowerSeries.X ^ e * u.val := hq
  have hmax : (IsLocalRing.maximalIdeal (Completion R)).map q.toRingHom =
      IsLocalRing.maximalIdeal (PowerSeries ℂ) :=
    IsLocalRing.map_ringEquiv_maximalIdeal q
  rw [hτ, Ideal.map_span, Set.image_singleton,
    Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton, hnormalized,
    Ideal.map_pow, ← AdicCompletion.maximalIdeal_eq_map,
    Ideal.map_pow, hmax,
    PowerSeries.maximalIdeal_eq_span_X, Ideal.span_singleton_pow,
    Ideal.span_singleton_mul_right_unit u.isUnit]

/-- The same normalization rules out a component lying over a single
base point: its actual base maximal ideal has nonzero image. -/
theorem maximalIdeal_image_ne_bot
    (f : B →+* R) (τ : B)
    (hτ : IsLocalRing.maximalIdeal B = Ideal.span {τ})
    (q : Completion R ≃+* PowerSeries ℂ) (e : ℕ)
    (u : (PowerSeries ℂ)ˣ)
    (hq : q (algebraMap R (Completion R) (f τ)) = PowerSeries.X ^ e * u.val) :
    (IsLocalRing.maximalIdeal B).map f ≠ ⊥ := by
  intro hzero
  have ht : τ ∈ IsLocalRing.maximalIdeal B := by
    rw [hτ]
    exact Ideal.subset_span (Set.mem_singleton τ)
  have hft := Ideal.mem_map_of_mem f ht
  rw [hzero] at hft
  have hf : f τ = 0 := Ideal.mem_bot.mp hft
  have hnonzero : PowerSeries.X ^ e * u.val ≠ (0 : PowerSeries ℂ) :=
    mul_ne_zero (pow_ne_zero e PowerSeries.X_ne_zero) u.ne_zero
  apply hnonzero
  rw [← hq, hf, map_zero, map_zero]

/-- Ramification ideal powers are preserved by an actual stalk
isomorphism on the source.  This is the passage from the already
regular pullback germ to its component normalization. -/
theorem maximalIdeal_image_comp_of_stalkIso
    {A B C : Scheme} (f : A ⟶ B) (g : B ⟶ C) (x : A)
    [IsIso (f.stalkMap x)] (e : ℕ)
    (h : (IsLocalRing.maximalIdeal (C.presheaf.stalk (g (f x)))).map
        (g.stalkMap (f x)).hom =
      (IsLocalRing.maximalIdeal (B.presheaf.stalk (f x))) ^ e) :
    (IsLocalRing.maximalIdeal (C.presheaf.stalk ((f ≫ g) x))).map
        ((f ≫ g).stalkMap x).hom =
      (IsLocalRing.maximalIdeal (A.presheaf.stalk x)) ^ e := by
  rw [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp, ← Ideal.map_map]
  change ((IsLocalRing.maximalIdeal (C.presheaf.stalk (g (f x)))).map
      (g.stalkMap (f x)).hom).map (f.stalkMap x).hom =
    (IsLocalRing.maximalIdeal (A.presheaf.stalk x)) ^ e
  rw [h, Ideal.map_pow, IsLocalRing.map_maximalIdeal_of_surjective
      (f.stalkMap x).hom (ConcreteCategory.bijective_of_isIso (f.stalkMap x)).2]

end LeBrunSalamon.Construction.Descent.BranchAlgebra

end

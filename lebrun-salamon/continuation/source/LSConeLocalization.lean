import LSConeArcs

/-!
## Ambient-coordinate congruence controls all functions on a cone chart

The two arcs are already actual algebra maps to `C[[t]]`.  Reduce them
modulo `(t^k)`, compare them on algebra generators, and then use uniqueness
for localization.  This proves agreement on inverted denominators as well
as polynomial functions without assuming a separate estimate for each
regular function.  It applies to actual localizations of coordinate-ring
quotients and does not assume smoothness or a Taylor expansion.

Place after `cone_arc_bridge.lean.txt`.
UNCOMPILED continuation, according to the user's 35,000-line build gate.
-/

noncomputable section
set_option autoImplicit false

namespace LeBrunSalamon.Construction.Lines.ConeArcs

open ConePole

variable {A : Type*} [CommRing A] [Algebra ℂ A]

/-- Equality on algebra generators suffices for equality on the actual
nonreduced truncated disc, not merely equality at its closed point. -/
theorem reduction_eq_of_generators {ι : Type*}
    (r : ι → A) (hgen : Algebra.adjoin ℂ (Set.range r) = ⊤)
    (k : ℕ) (p q : A →ₐ[ℂ] Series)
    (hcoord : ∀ i, q (r i) - p (r i) ∈ orderIdeal k) :
    reduction k p = reduction k q := by
  apply AlgHom.ext_of_adjoin_eq_top hgen
  rintro _ ⟨i, rfl⟩
  change Ideal.Quotient.mk (orderIdeal k) (p (r i)) =
    Ideal.Quotient.mk (orderIdeal k) (q (r i))
  exact (Ideal.Quotient.eq.mpr (hcoord i)).symm

/-- Localization adds no extra congruence conditions once both arcs
exist as actual algebra maps out of the localized ring. -/
theorem reduction_eq_of_localized_generators
    {L : Type*} [CommRing L] [Algebra A L] [Algebra ℂ L]
    [IsScalarTower ℂ A L] (S : Submonoid A) [IsLocalization S L]
    {ι : Type*} (r : ι → A)
    (hgen : Algebra.adjoin ℂ (Set.range r) = ⊤)
    (k : ℕ) (p q : L →ₐ[ℂ] Series)
    (hcoord : ∀ i, q (algebraMap A L (r i)) -
      p (algebraMap A L (r i)) ∈ orderIdeal k) :
    reduction k p = reduction k q := by
  apply IsLocalization.algHom_ext S
  apply AlgHom.ext_of_adjoin_eq_top hgen
  rintro _ ⟨i, rfl⟩
  change Ideal.Quotient.mk (orderIdeal k) (p (algebraMap A L (r i))) =
    Ideal.Quotient.mk (orderIdeal k) (q (algebraMap A L (r i)))
  exact (Ideal.Quotient.eq.mpr (hcoord i)).symm

theorem localized_functions_congruent_of_generators
    {L : Type*} [CommRing L] [Algebra A L] [Algebra ℂ L]
    [IsScalarTower ℂ A L] (S : Submonoid A) [IsLocalization S L]
    {ι : Type*} (r : ι → A)
    (hgen : Algebra.adjoin ℂ (Set.range r) = ⊤)
    (k : ℕ) (p q : L →ₐ[ℂ] Series)
    (hcoord : ∀ i, q (algebraMap A L (r i)) -
      p (algebraMap A L (r i)) ∈ orderIdeal k) :
    ∀ a : L, q a - p a ∈ orderIdeal k :=
  (reduction_eq_iff k p q).mp
    (reduction_eq_of_localized_generators S r hgen k p q hcoord)

/-- The actual ambient coordinate functions in an affine closed
subscheme's coordinate ring. -/
def quotientCoordinate {ι : Type*} (I : Ideal (MvPolynomial ι ℂ))
    (i : ι) : MvPolynomial ι ℂ ⧸ I :=
  Ideal.Quotient.mk I (MvPolynomial.X i)

/-- The required generation statement is proved for a coordinate-ring
quotient, rather than stored as an additional geometric input. -/
theorem quotientCoordinates_generate {ι : Type*}
    (I : Ideal (MvPolynomial ι ℂ)) :
    Algebra.adjoin ℂ (Set.range (quotientCoordinate I)) = ⊤ := by
  rw [Algebra.adjoin_range_eq_range_aeval]
  have hmap : MvPolynomial.aeval (quotientCoordinate I) =
      Ideal.Quotient.mkₐ ℂ I := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [MvPolynomial.aeval_X, quotientCoordinate,
      Ideal.Quotient.mkₐ_eq_mk]
  rw [hmap]
  exact (AlgHom.range_eq_top _).mpr (Ideal.Quotient.mkₐ_surjective ℂ I)

/-- Ambient-coordinate congruence therefore gives agreement modulo the
full `t^k` on every regular function of an actual localized cone chart. -/
theorem reduction_eq_on_localized_quotient {ι : Type*}
    (I : Ideal (MvPolynomial ι ℂ))
    {L : Type*} [CommRing L] [Algebra (MvPolynomial ι ℂ ⧸ I) L]
    [Algebra ℂ L] [IsScalarTower ℂ (MvPolynomial ι ℂ ⧸ I) L]
    (S : Submonoid (MvPolynomial ι ℂ ⧸ I)) [IsLocalization S L]
    (k : ℕ) (p q : L →ₐ[ℂ] Series)
    (hcoord : ∀ i,
      q (algebraMap (MvPolynomial ι ℂ ⧸ I) L (quotientCoordinate I i)) -
      p (algebraMap (MvPolynomial ι ℂ ⧸ I) L (quotientCoordinate I i)) ∈
        orderIdeal k) :
    reduction k p = reduction k q :=
  reduction_eq_of_localized_generators S (quotientCoordinate I)
    (quotientCoordinates_generate I) k p q hcoord

/-- On a genuine localized coordinate-quotient chart, the ambient
rescaling equations themselves give the full congruence required for
the cone-addition contradiction. No all-functions congruence hypothesis
is supplied by the caller. The geometric radial-form identity remains
explicit. -/
theorem localized_rescaled_nonorthogonal_arcs_impossible
    {ι : Type*} [Fintype ι] (I : Ideal (MvPolynomial ι ℂ))
    {L : Type*} [CommRing L] [Algebra (MvPolynomial ι ℂ ⧸ I) L]
    [Algebra ℂ L] [IsScalarTower ℂ (MvPolynomial ι ℂ ⧸ I) L]
    (S : Submonoid (MvPolynomial ι ℂ ⧸ I)) [IsLocalization S L]
    {K : Type*} [CommRing K] [Algebra ℂ K]
    (p q : L →ₐ[ℂ] Series) (ω : ι → ι → ℂ)
    (hskew : ∀ i j, ω j i = -ω i j)
    (hradial : ConeDiagonal.radialForm
      (fun i => algebraMap (MvPolynomial ι ℂ ⧸ I) L (quotientCoordinate I i)) ω = 0)
    (k : ℕ) (hk : 0 < k) (s : ι → ℂ)
    (hrescale : ∀ i,
      p (algebraMap (MvPolynomial ι ℂ ⧸ I) L (quotientCoordinate I i)) -
      q (algebraMap (MvPolynomial ι ℂ ⧸ I) L (quotientCoordinate I i)) =
        (PowerSeries.X : Series) ^ k * PowerSeries.C (s i))
    (j : Series →ₐ[ℂ] K) (hj : Function.Injective j)
    (a b : ι → K) (c : ℂ) (hc : c ≠ 0)
    (hp : ∀ i,
      j (p (algebraMap (MvPolynomial ι ℂ ⧸ I) L (quotientCoordinate I i))) =
        j (PowerSeries.X : Series) ^ k * a i)
    (hq : ∀ i,
      j (q (algebraMap (MvPolynomial ι ℂ ⧸ I) L (quotientCoordinate I i))) =
        -(j (PowerSeries.X : Series) ^ k * b i))
    (hpair : ConePairing.pairing ω a b = algebraMap ℂ K c) : False := by
  let r : ι → L := fun i =>
    algebraMap (MvPolynomial ι ℂ ⧸ I) L (quotientCoordinate I i)
  have hcoord : ∀ i, q (r i) - p (r i) ∈ orderIdeal k := by
    intro i
    have h := difference_mem_of_rescaling
      (fun i => p (r i)) (fun i => q (r i)) s k hrescale i
    simpa only [neg_sub] using (orderIdeal k).neg_mem h
  have hclose : reduction k p = reduction k q :=
    reduction_eq_on_localized_quotient I S k p q hcoord
  exact rescaled_nonorthogonal_arcs_impossible p q r ω hskew hradial
    k hk hclose j hj a b c hc hp hq hpair

end LeBrunSalamon.Construction.Lines.ConeArcs

end

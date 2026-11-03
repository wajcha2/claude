import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Topology.Algebra.Valued.WithVal

/-!
# Laurent expansion from a rational place

The three field-theoretic published inputs below have independent statements:
existence of a pole, finiteness of a place's residue field, and the power-series
description of the completion at a rational place. The affine dimension formula
is a fourth, independent input. The passage from an affine curve to these inputs,
the residue-field identification, the completion inclusion, and the sign of the
Laurent order are proved below.

This draft is not accepted until its statements, primary references, and native
kernel receipt have all been checked.
-/

noncomputable section
set_option autoImplicit false

open scoped WithZero
open Topology

namespace LeBrunSalamon.PublishedInputs.FunctionFields

/-- Dimension equals transcendence degree for a finite type domain over a field.
Stacks Project, Lemma 10.116.1, Tag 00P0. The natural-number parameter only spells
out the equality between the different codomains of the two dimension functions. -/
theorem dimension_transcendenceDegree
    (k B : Type) [Field k] [CommRing B] [IsDomain B] [Algebra k B]
    [Algebra.FiniteType k B] (d : ℕ) (hdim : ringKrullDim B = d) :
    Algebra.trdeg k (FractionRing B) = d := by
  sorry

/-- A transcendental function in a one-variable function field has a pole.
Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., Corollary 1.1.20.
`EssFiniteType` is finite generation as a field; see mathlib's
`IntermediateField.fg_top_iff`. Multiplicative valuations reverse the additive
valuation convention, so a pole has value greater than one. -/
theorem exists_pole
    (k K : Type) [Field k] [Field K] [Algebra k K]
    [Algebra.EssFiniteType k K] (hdim : Algebra.trdeg k K = 1)
    (z : K) (hz : Transcendental k z) :
    ∃ v : Valuation K ℤᵐ⁰,
      v.IsTrivialOn k ∧ Function.Surjective v ∧ 1 < v z := by
  sorry

/-- The residue field of a place of a one-variable function field is finite over
the constant field. Stichtenoth, Proposition 1.1.15, the finite-degree conclusion.
No algebraic closedness or chosen pole is assumed in this input. -/
theorem place_residue_finite
    (k K : Type) [Field k] [Field K] [Algebra k K]
    [Algebra.EssFiniteType k K] (hdim : Algebra.trdeg k K = 1)
    (v : Valuation K ℤᵐ⁰) [v.IsTrivialOn k] (hv : Function.Surjective v) :
    Module.Finite k (IsLocalRing.ResidueField v.valuationSubring) := by
  sorry

/-- Bump, Algebraic Geometry (1998), Proposition 10.8, p.128.
A complete discretely valued field containing a coefficient field is the
Laurent-series field over that coefficient field. The simultaneous isomorphism
of its valuation ring with the power-series ring is expressed by the last
equivalence. This is the generic complete-field theorem: the passage to the
completion of the original place and its residue-field identification are
proved separately below. -/
theorem completeDiscreteValuation_series
    (k K : Type) [Field k] [Field K] [Algebra k K] [Valued K ℤᵐ⁰]
    [CompleteSpace K] [(Valued.v : Valuation K ℤᵐ⁰).IsTrivialOn k]
    (hv : Function.Surjective (Valued.v : K → ℤᵐ⁰))
    (hres : Function.Bijective
      (algebraMap k (IsLocalRing.ResidueField
        (Valued.v : Valuation K ℤᵐ⁰).valuationSubring))) :
    ∃ e : K ≃ₐ[k] LaurentSeries k,
      ∀ x : K, (Valued.v (e x) : ℤᵐ⁰) ≤ 1 ↔ Valued.v x ≤ 1 := by
  sorry

end LeBrunSalamon.PublishedInputs.FunctionFields

namespace LeBrunSalamon.FunctionFieldPlaces

open LeBrunSalamon.PublishedInputs.FunctionFields

/-- Surjectivity on the actual residue field is precisely approximation of an
integer by a constant modulo the maximal ideal. -/
theorem residue_approximation
    (k K : Type) [Field k] [Field K] [Algebra k K]
    (v : Valuation K ℤᵐ⁰) [v.IsTrivialOn k]
    (hres : Function.Surjective
      (algebraMap k (IsLocalRing.ResidueField v.valuationSubring)))
    (x : K) (hx : v x ≤ 1) :
    ∃ c : k, v (x - algebraMap k K c) < 1 := by
  let a : v.valuationSubring := ⟨x, hx⟩
  obtain ⟨c, hc⟩ := hres (IsLocalRing.residue _ a)
  refine ⟨c, ?_⟩
  change v ((a - algebraMap k v.valuationSubring c : v.valuationSubring) : K) < 1
  apply (v.mem_maximalIdeal_iff).mp
  apply (IsLocalRing.residue_eq_zero_iff _).mp
  change IsLocalRing.residue _ (a - algebraMap k v.valuationSubring c) = 0
  rw [map_sub]
  change IsLocalRing.residue _ a - algebraMap k
    (IsLocalRing.ResidueField v.valuationSubring) c = 0
  rw [hc, sub_self]

/-- The coefficient map into the completion uses the actual completion
inclusion of the original valued field. -/
def completionAlgebra
    (k K : Type) [Field k] [Field K] [Algebra k K]
    (v : Valuation K ℤᵐ⁰) : Algebra k v.Completion :=
  ((UniformSpace.Completion.coeRingHom : WithVal v →+* v.Completion).comp
    (algebraMap k (WithVal v))).toAlgebra

theorem completion_trivial
    (k K : Type) [Field k] [Field K] [Algebra k K]
    (v : Valuation K ℤᵐ⁰) [v.IsTrivialOn k] :
    letI := completionAlgebra k K v
    (Valued.v : Valuation v.Completion ℤᵐ⁰).IsTrivialOn k := by
  letI := completionAlgebra k K v
  constructor
  intro c hc
  change (Valued.v ((WithVal.toVal v (algebraMap k K c)) : v.Completion) : ℤᵐ⁰) = 1
  rw [Valued.valuedCompletion_apply]
  change v (algebraMap k K c) = 1
  exact Valuation.IsTrivialOn.eq_one c hc

/-- Density of the original field supplies approximation modulo the maximal
ideal in its completion. Both valuation bounds are checked on the actual
inclusion, so this does not assume a residue-field comparison theorem. -/
theorem completion_approximation
    (k K : Type) [Field k] [Field K] [Algebra k K]
    (v : Valuation K ℤᵐ⁰) [v.IsTrivialOn k]
    (hres : Function.Surjective
      (algebraMap k (IsLocalRing.ResidueField v.valuationSubring)))
    (x : v.Completion) (hx : (Valued.v x : ℤᵐ⁰) ≤ 1) :
    ∃ c : k, (Valued.v (x - ((algebraMap k K c : K) : v.Completion)) : ℤᵐ⁰) < 1 := by
  have hb : {y : v.Completion | (Valued.v (y - x) : ℤᵐ⁰) < 1} ∈ 𝓝 x := by
    rw [Valued.mem_nhds]
    refine ⟨1, ?_⟩
    intro y hy
    simpa only [Valuation.restrict_lt_iff_lt_embedding, Units.val_one, map_one] using hy
  obtain ⟨y, hy⟩ := UniformSpace.Completion.denseRange_coe.mem_nhds hb
  have hy' : (Valued.v (x - (y : v.Completion)) : ℤᵐ⁰) < 1 := by
    rwa [Valuation.map_sub_swap]
  have hyint : v y.ofVal ≤ 1 := by
    have htri := (Valued.v : Valuation v.Completion ℤᵐ⁰).map_add
      ((y : v.Completion) - x) x
    simp only [sub_add_cancel] at htri
    have := le_trans htri (max_le (le_of_lt hy) hx)
    simpa only [Valued.valuedCompletion_apply, ← WithVal.apply_ofVal] using this
  obtain ⟨c, hc⟩ := residue_approximation k K v hres y.ofVal hyint
  refine ⟨c, ?_⟩
  have hc' : (Valued.v ((y : v.Completion) -
      ((algebraMap k K c : K) : v.Completion)) : ℤᵐ⁰) < 1 := by
    simpa only [← UniformSpace.Completion.coe_sub, Valued.valuedCompletion_apply,
      ← WithVal.apply_ofVal, WithVal.ofVal_sub, WithVal.ofVal_toVal] using hc
  have htri := (Valued.v : Valuation v.Completion ℤᵐ⁰).map_add
    (x - (y : v.Completion))
    ((y : v.Completion) - ((algebraMap k K c : K) : v.Completion))
  rw [sub_add_sub_cancel] at htri
  exact lt_of_le_of_lt htri (max_lt hy' hc')

/-- The completion has the same coefficient residue field, proved by choosing
a representative and applying the preceding density argument. -/
theorem completion_residue_bijective
    (k K : Type) [Field k] [Field K] [Algebra k K]
    (v : Valuation K ℤᵐ⁰) [v.IsTrivialOn k]
    (hres : Function.Bijective
      (algebraMap k (IsLocalRing.ResidueField v.valuationSubring))) :
    letI := completionAlgebra k K v
    letI := completion_trivial k K v
    Function.Bijective (algebraMap k (IsLocalRing.ResidueField
      (Valued.v : Valuation v.Completion ℤᵐ⁰).valuationSubring)) := by
  letI := completionAlgebra k K v
  letI := completion_trivial k K v
  let w : Valuation v.Completion ℤᵐ⁰ := Valued.v
  refine ⟨(algebraMap k _).injective, ?_⟩
  intro z
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective (R := w.valuationSubring) z
  obtain ⟨c, hc⟩ := completion_approximation k K v hres.surjective a.val a.property
  refine ⟨c, ?_⟩
  have hm : a - algebraMap k w.valuationSubring c ∈
      IsLocalRing.maximalIdeal w.valuationSubring :=
    w.mem_maximalIdeal_iff.mpr hc
  have hz := (IsLocalRing.residue_eq_zero_iff _).mpr hm
  rw [map_sub, sub_eq_zero] at hz
  exact hz.symm

/-- Apply only the generic complete-field theorem after proving its completion
and coefficient-field hypotheses. -/
theorem rational_place_completion
    (k K : Type) [Field k] [Field K] [Algebra k K]
    (v : Valuation K ℤᵐ⁰) [v.IsTrivialOn k] (hv : Function.Surjective v)
    (hres : Function.Bijective
      (algebraMap k (IsLocalRing.ResidueField v.valuationSubring))) :
    ∃ e : v.Completion ≃+* LaurentSeries k,
      (∀ c : k, e ((algebraMap k K c : K) : v.Completion) =
        algebraMap k (LaurentSeries k) c) ∧
      ∀ x : v.Completion, (Valued.v (e x) : ℤᵐ⁰) ≤ 1 ↔ Valued.v x ≤ 1 := by
  letI := completionAlgebra k K v
  letI := completion_trivial k K v
  have hvbase : Function.Surjective (Valued.v : WithVal v → ℤᵐ⁰) := by
    intro z
    obtain ⟨a, ha⟩ := hv z
    exact ⟨WithVal.toVal v a, ha⟩
  have hv' : Function.Surjective (Valued.v : v.Completion → ℤᵐ⁰) :=
    Valued.valuedCompletion_surjective_iff.mpr hvbase
  obtain ⟨e, he⟩ := completeDiscreteValuation_series k v.Completion hv'
    (completion_residue_bijective k K v hres)
  exact ⟨e.toRingEquiv, fun c => e.commutes c, he⟩

/-- Over an algebraically closed field, an element outside the coefficient field
is transcendental. This is proved using its actual minimal polynomial. -/
theorem transcendental_of_nonconstant
    (k K : Type) [Field k] [IsAlgClosed k] [Field K] [Algebra k K]
    (z : K) (hz : ¬ ∃ c : k, algebraMap k K c = z) :
    Transcendental k z := by
  intro h
  have hi := h.isIntegral
  have hdegree := IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible hi)
  have hmonic : (minpoly k z).leadingCoeff = 1 := (minpoly.monic hi).leadingCoeff
  have he := minpoly.aeval k z
  rw [Polynomial.eq_X_add_C_of_degree_eq_one hdegree, hmonic,
    Polynomial.C_1, one_mul, map_add, Polynomial.aeval_X,
    Polynomial.aeval_C, add_eq_zero_iff_eq_neg] at he
  exact hz ⟨-(minpoly k z).coeff 0, by rw [map_neg]; exact he.symm⟩

/-- A nonconstant element remains nonconstant under the actual fraction map. -/
theorem fraction_nonconstant
    (k B : Type) [Field k] [CommRing B] [IsDomain B] [Algebra k B]
    (f : B) (hf : ¬ ∃ c : k, algebraMap k B c = f) :
    ¬ ∃ c : k, algebraMap k (FractionRing B) c =
      algebraMap B (FractionRing B) f := by
  rintro ⟨c, hc⟩
  apply hf
  refine ⟨c, (IsFractionRing.injective B (FractionRing B)) ?_⟩
  rw [← IsScalarTower.algebraMap_apply k B (FractionRing B)]
  exact hc

/-- The actual algebra injection into the valuation completion, followed by its
constant-preserving series isomorphism. -/
def completionEmbedding
    (k K : Type) [Field k] [Field K] [Algebra k K]
    (v : Valuation K ℤᵐ⁰) (e : v.Completion ≃+* LaurentSeries k)
    (hc : ∀ c : k, e ((algebraMap k K c : K) : v.Completion) =
      algebraMap k (LaurentSeries k) c) : K →ₐ[k] LaurentSeries k where
  __ := e.toRingHom.comp
    ((UniformSpace.Completion.coeRingHom : WithVal v →+* v.Completion).comp
      (WithVal.equiv v).symm.toRingHom)
  commutes' c := hc c

theorem completionEmbedding_integer
    (k K : Type) [Field k] [Field K] [Algebra k K]
    (v : Valuation K ℤᵐ⁰) (e : v.Completion ≃+* LaurentSeries k)
    (hc : ∀ c : k, e ((algebraMap k K c : K) : v.Completion) =
      algebraMap k (LaurentSeries k) c)
    (he : ∀ x : v.Completion, (Valued.v (e x) : ℤᵐ⁰) ≤ 1 ↔ Valued.v x ≤ 1)
    (z : K) : (Valued.v (completionEmbedding k K v e hc z) : ℤᵐ⁰) ≤ 1 ↔ v z ≤ 1 := by
  change (Valued.v (e (WithVal.toVal v z : v.Completion)) : ℤᵐ⁰) ≤ 1 ↔ v z ≤ 1
  rw [he, Valued.valuedCompletion_apply]
  rfl

/-- A pole for the standard multiplicative Laurent valuation has negative order. -/
theorem order_neg_of_one_lt_valuation
    (k : Type) [Field k] (z : LaurentSeries k)
    (hz : (1 : ℤᵐ⁰) < Valued.v z) : z.order < 0 := by
  by_contra! h
  apply (not_le_of_gt hz)
  rw [LaurentSeries.valuation_le_iff_coeff_lt_log_eq_zero k one_ne_zero,
    WithZero.log_one, neg_zero]
  intro n hn
  exact HahnSeries.coeff_eq_zero_of_lt_order (lt_of_lt_of_le hn h)

/-- The former composite admission, now assembled from the separately named
published field-theory statements and proved coefficient/valuation transports. -/
theorem laurentExpansionAtPole
    (B : Type) [CommRing B] [IsDomain B] [Algebra ℂ B] [Algebra.FiniteType ℂ B]
    (hdim : ringKrullDim B = 1) (f : B)
    (hf : ¬ ∃ c : ℂ, algebraMap ℂ B c = f) :
    ∃ j : FractionRing B →ₐ[ℂ] LaurentSeries ℂ,
      (j (algebraMap B (FractionRing B) f)).order < 0 := by
  let K := FractionRing B
  letI : Algebra.EssFiniteType B K :=
    Algebra.EssFiniteType.of_isLocalization K (nonZeroDivisors B)
  letI : Algebra.EssFiniteType ℂ K := Algebra.EssFiniteType.comp ℂ B K
  have htrdeg : Algebra.trdeg ℂ K = 1 := dimension_transcendenceDegree ℂ B 1 hdim
  have ht := transcendental_of_nonconstant ℂ K (algebraMap B K f)
    (fraction_nonconstant ℂ B f hf)
  obtain ⟨v, hvk, hvs, hvf⟩ := exists_pole ℂ K htrdeg (algebraMap B K f) ht
  letI := hvk
  letI := place_residue_finite ℂ K htrdeg v hvs
  have hres : Function.Bijective
      (algebraMap ℂ (IsLocalRing.ResidueField v.valuationSubring)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  obtain ⟨e, hc, he⟩ := rational_place_completion ℂ K v hvs hres
  refine ⟨completionEmbedding ℂ K v e hc, order_neg_of_one_lt_valuation ℂ _ ?_⟩
  apply lt_of_not_ge
  intro hint
  exact not_le_of_gt hvf ((completionEmbedding_integer ℂ K v e hc he _).mp hint)

end LeBrunSalamon.FunctionFieldPlaces

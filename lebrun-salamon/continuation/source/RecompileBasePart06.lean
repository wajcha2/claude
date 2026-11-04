import RecompileBasePart05

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
# Phase 29 -- node algebras, stable source trees, and effective descent

The polynomial node uv=a and the normalization equalizer are actual rings. The tree statements concern
actual finite simple graphs, rather than a list of positive degrees that omits contracted components.
Their identification with moduli-space boundaries is a separate theorem.
-/

namespace LeBrunSalamon.PhaseTwentyNine

open scoped TensorProduct

section NodeAlgebra

variable (R : Type*) [CommRing R]

abbrev NodePolynomialRing := MvPolynomial (Fin 2) R

def nodeEquation (a : R) : NodePolynomialRing R :=
  MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C a

def nodeIdeal (a : R) : Ideal (NodePolynomialRing R) :=
  Ideal.span {nodeEquation R a}

abbrev NodeAlgebra (a : R) := NodePolynomialRing R ⧸ nodeIdeal R a

def nodeU (a : R) : NodeAlgebra R a :=
  Ideal.Quotient.mk (nodeIdeal R a) (MvPolynomial.X 0)

def nodeV (a : R) : NodeAlgebra R a :=
  Ideal.Quotient.mk (nodeIdeal R a) (MvPolynomial.X 1)

noncomputable section
set_option autoImplicit false
variable (R : Type*) [CommRing R]

namespace NodeAlgebraProof

theorem node_relation (a : R) :
    nodeU R a * nodeV R a = algebraMap R (NodeAlgebra R a) a := by
  have hm : nodeEquation R a ∈ nodeIdeal R a :=
    Ideal.subset_span (Set.mem_singleton _)
  have hz : Ideal.Quotient.mk (nodeIdeal R a) (nodeEquation R a) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hm
  apply sub_eq_zero.mp
  change Ideal.Quotient.mk (nodeIdeal R a) (MvPolynomial.X 0) *
      Ideal.Quotient.mk (nodeIdeal R a) (MvPolynomial.X 1) -
      Ideal.Quotient.mk (nodeIdeal R a) (MvPolynomial.C a) = 0
  simpa only [nodeEquation, map_sub, map_mul] using hz

section UniversalLift

variable {A : Type*} [CommRing A] [Algebra R A]

theorem nodeIdeal_le_ker_aeval (a : R) (u v : A)
    (h : u * v = algebraMap R A a) :
    nodeIdeal R a ≤ RingHom.ker
      (MvPolynomial.aeval (fun i : Fin 2 => if i = 0 then u else v)).toRingHom := by
  change Ideal.span {nodeEquation R a} ≤ _
  apply Ideal.span_le.mpr
  intro p hp
  have hp' : p = nodeEquation R a := Set.mem_singleton_iff.mp hp
  subst p
  apply RingHom.mem_ker.mpr
  simp [nodeEquation, MvPolynomial.aeval_C, h]

def nodeLift (a : R) (u v : A) (h : u * v = algebraMap R A a) :
    NodeAlgebra R a →ₐ[R] A :=
  Ideal.Quotient.liftₐ (nodeIdeal R a)
    (MvPolynomial.aeval (fun i : Fin 2 => if i = 0 then u else v))
    (fun p hp => RingHom.mem_ker.mp (nodeIdeal_le_ker_aeval R a u v h hp))

theorem nodeLift_mk (a : R) (u v : A) (h : u * v = algebraMap R A a)
    (p : NodePolynomialRing R) :
    nodeLift R a u v h (Ideal.Quotient.mk (nodeIdeal R a) p) =
      MvPolynomial.aeval (fun i : Fin 2 => if i = 0 then u else v) p := rfl

theorem nodeLift_nodeU (a : R) (u v : A) (h : u * v = algebraMap R A a) :
    nodeLift R a u v h (nodeU R a) = u := by
  rw [nodeU, nodeLift_mk]
  simp

theorem nodeLift_nodeV (a : R) (u v : A) (h : u * v = algebraMap R A a) :
    nodeLift R a u v h (nodeV R a) = v := by
  rw [nodeV, nodeLift_mk]
  simp

theorem nodeAlgHom_ext (a : R) {f g : NodeAlgebra R a →ₐ[R] A}
    (hu : f (nodeU R a) = g (nodeU R a))
    (hv : f (nodeV R a) = g (nodeV R a)) : f = g := by
  apply Ideal.Quotient.algHom_ext R
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · exact hu
  · exact hv

theorem aeval_at_zero (p : Polynomial R) :
    Polynomial.aeval (0 : A) p = algebraMap R A (Polynomial.eval 0 p) := by
  simpa only [map_zero] using
    (Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval (A := A) (0 : R) p)

/-- The nonconstant parts on distinct branches have zero product. -/
theorem aeval_cross_zero (u v : A) (h : u * v = 0) (p q : Polynomial R) :
    (Polynomial.aeval u p - algebraMap R A (Polynomial.eval 0 p)) *
      (Polynomial.aeval v q - algebraMap R A (Polynomial.eval 0 q)) = 0 := by
  have hp : Polynomial.X ∣ p - Polynomial.C (Polynomial.eval 0 p) := by
    apply Polynomial.X_dvd_iff.mpr
    simp [Polynomial.coeff_zero_eq_eval_zero]
  have hq : Polynomial.X ∣ q - Polynomial.C (Polynomial.eval 0 q) := by
    apply Polynomial.X_dvd_iff.mpr
    simp [Polynomial.coeff_zero_eq_eval_zero]
  obtain ⟨p', hp'⟩ := hp
  obtain ⟨q', hq'⟩ := hq
  calc
    _ = Polynomial.aeval u (p - Polynomial.C (Polynomial.eval 0 p)) *
        Polynomial.aeval v (q - Polynomial.C (Polynomial.eval 0 q)) := by
          simp only [map_sub, Polynomial.aeval_C]
    _ = (u * Polynomial.aeval u p') * (v * Polynomial.aeval v q') := by
          rw [hp', hq']
          simp only [map_mul, Polynomial.aeval_X]
    _ = (u * v) * (Polynomial.aeval u p' * Polynomial.aeval v q') := by ring
    _ = 0 := by rw [h, zero_mul]

end UniversalLift

end NodeAlgebraProof

end

theorem node_relation (a : R) :
    nodeU R a * nodeV R a = algebraMap R (NodeAlgebra R a) a := by
  exact LeBrunSalamon.PhaseTwentyNine.NodeAlgebraProof.node_relation (R := R) (a := a)

/- Source-only Phase 3 integration: node_normal_form. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable (R : Type*) [CommRing R]

namespace NodeNormalFormProof

def normalMonomial (a : R) (d : Fin 2 →₀ ℕ) : ℤ →₀ R :=
  Finsupp.single ((d 0 : ℤ) - (d 1 : ℤ)) (a ^ min (d 0) (d 1))

def normalPolynomial (a : R) : NodePolynomialRing R →ₗ[R] (ℤ →₀ R) :=
  (Finsupp.linearCombination R (normalMonomial R a)).comp
    (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap

theorem normalPolynomial_monomial (a : R) (d : Fin 2 →₀ ℕ) (c : R) :
    normalPolynomial R a (MvPolynomial.monomial d c) =
      Finsupp.single ((d 0 : ℤ) - (d 1 : ℤ)) (c * a ^ min (d 0) (d 1)) := by
  change Finsupp.linearCombination R (normalMonomial R a) (Finsupp.single d c) = _
  rw [Finsupp.linearCombination_single]
  simp only [normalMonomial, Finsupp.smul_single, smul_eq_mul]

theorem normalPolynomial_mul_uv (a : R) (p : NodePolynomialRing R) :
    normalPolynomial R a (p * (MvPolynomial.X 0 * MvPolynomial.X 1)) =
      a • normalPolynomial R a p := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial d c =>
      simp only [MvPolynomial.X, MvPolynomial.monomial_mul_monomial, mul_one,
        normalPolynomial_monomial]
      have h0 :
          (d + (Finsupp.single 0 1 + Finsupp.single 1 1) : Fin 2 →₀ ℕ) 0 =
            d 0 + 1 := by simp
      have h1 :
          (d + (Finsupp.single 0 1 + Finsupp.single 1 1) : Fin 2 →₀ ℕ) 1 =
            d 1 + 1 := by simp
      rw [h0, h1]
      have hw : ((d 0 + 1 : ℕ) : ℤ) - ((d 1 + 1 : ℕ) : ℤ) =
          (d 0 : ℤ) - (d 1 : ℤ) := by omega
      have hm : min (d 0 + 1) (d 1 + 1) = min (d 0) (d 1) + 1 := by omega
      rw [hw, hm, pow_succ]
      simp only [Finsupp.smul_single, smul_eq_mul]
      congr 1
      ring
  | add p q hp hq =>
      simp only [add_mul, map_add, hp, hq, smul_add]

theorem normalPolynomial_mul_equation (a : R) (p : NodePolynomialRing R) :
    normalPolynomial R a (p * nodeEquation R a) = 0 := by
  rw [nodeEquation, mul_sub, map_sub, normalPolynomial_mul_uv]
  rw [mul_comm p (MvPolynomial.C a), MvPolynomial.C_mul', map_smul]
  exact sub_self _

theorem nodeIdeal_le_normalPolynomial_ker (a : R) :
    (nodeIdeal R a).restrictScalars R ≤ LinearMap.ker (normalPolynomial R a) := by
  intro p hp
  change p ∈ Ideal.span {nodeEquation R a} at hp
  obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.mp hp
  exact normalPolynomial_mul_equation R a q

def normalForm (a : R) : NodeAlgebra R a →ₗ[R] (ℤ →₀ R) :=
  (((nodeIdeal R a).restrictScalars R).liftQ (normalPolynomial R a)
      (nodeIdeal_le_normalPolynomial_ker R a)).comp
    (Submodule.Quotient.restrictScalarsEquiv R (nodeIdeal R a)).symm.toLinearMap

theorem normalForm_mk (a : R) (p : NodePolynomialRing R) :
    normalForm R a (Ideal.Quotient.mk (nodeIdeal R a) p) =
      normalPolynomial R a p := rfl

def normalPower (a : R) (z : ℤ) : NodeAlgebra R a :=
  nodeU R a ^ z.toNat * nodeV R a ^ (-z).toNat

def fromNormal (a : R) : (ℤ →₀ R) →ₗ[R] NodeAlgebra R a :=
  Finsupp.linearCombination R (normalPower R a)

theorem fromNormal_single (a : R) (z : ℤ) (c : R) :
    fromNormal R a (Finsupp.single z c) = c • normalPower R a z :=
  Finsupp.linearCombination_single _ _ _

theorem mixed_power_normalization (a : R) (m n : ℕ) :
    nodeU R a ^ m * nodeV R a ^ n =
      algebraMap R (NodeAlgebra R a) (a ^ min m n) *
        normalPower R a ((m : ℤ) - (n : ℤ)) := by
  have hp : ((m : ℤ) - (n : ℤ)).toNat = m - n := by omega
  have hn : (-((m : ℤ) - (n : ℤ))).toNat = n - m := by omega
  rw [normalPower, hp, hn]
  calc
    _ = (nodeU R a ^ min m n * nodeU R a ^ (m - n)) *
        (nodeV R a ^ min m n * nodeV R a ^ (n - m)) := by
          have hm : min m n + (m - n) = m := by omega
          have hn' : min m n + (n - m) = n := by omega
          rw [← pow_add, ← pow_add, hm, hn']
    _ = (nodeU R a * nodeV R a) ^ min m n *
        (nodeU R a ^ (m - n) * nodeV R a ^ (n - m)) := by
          rw [mul_pow]
          ring
    _ = _ := by rw [node_relation, map_pow]

theorem reconstruct_monomial (a : R) (d : Fin 2 →₀ ℕ) (c : R) :
    fromNormal R a (normalPolynomial R a (MvPolynomial.monomial d c)) =
      Ideal.Quotient.mk (nodeIdeal R a) (MvPolynomial.monomial d c) := by
  rw [normalPolynomial_monomial, fromNormal_single, MvPolynomial.monomial_fin_two]
  simp only [map_mul, map_pow]
  change (c * a ^ min (d 0) (d 1)) •
      normalPower R a ((d 0 : ℤ) - (d 1 : ℤ)) =
    algebraMap R (NodeAlgebra R a) c * nodeU R a ^ d 0 * nodeV R a ^ d 1
  calc
    _ = algebraMap R (NodeAlgebra R a) (c * a ^ min (d 0) (d 1)) *
        normalPower R a ((d 0 : ℤ) - (d 1 : ℤ)) :=
      Algebra.smul_def _ _
    _ = (algebraMap R (NodeAlgebra R a) c *
        algebraMap R (NodeAlgebra R a) (a ^ min (d 0) (d 1))) *
        normalPower R a ((d 0 : ℤ) - (d 1 : ℤ)) :=
      congrArg (fun z : NodeAlgebra R a =>
        z * normalPower R a ((d 0 : ℤ) - (d 1 : ℤ)))
        (map_mul (algebraMap R (NodeAlgebra R a)) c (a ^ min (d 0) (d 1)))
    _ = algebraMap R (NodeAlgebra R a) c *
        (algebraMap R (NodeAlgebra R a) (a ^ min (d 0) (d 1)) *
          normalPower R a ((d 0 : ℤ) - (d 1 : ℤ))) :=
      mul_assoc _ _ _
    _ = algebraMap R (NodeAlgebra R a) c *
        (nodeU R a ^ d 0 * nodeV R a ^ d 1) :=
      congrArg (fun z : NodeAlgebra R a => algebraMap R (NodeAlgebra R a) c * z)
        (mixed_power_normalization R a (d 0) (d 1)).symm
    _ = _ := (mul_assoc _ _ _).symm

theorem reconstruct_polynomial (a : R) (p : NodePolynomialRing R) :
    fromNormal R a (normalPolynomial R a p) =
      Ideal.Quotient.mk (nodeIdeal R a) p := by
  induction p using MvPolynomial.induction_on' with
  | monomial d c => exact reconstruct_monomial R a d c
  | add p q hp hq =>
      rw [(normalPolynomial R a).map_add p q,
        (fromNormal R a).map_add (normalPolynomial R a p) (normalPolynomial R a q),
        RingHom.map_add (Ideal.Quotient.mk (nodeIdeal R a)) p q, hp, hq]

theorem reconstruct (a : R) (x : NodeAlgebra R a) :
    fromNormal R a (normalForm R a x) = x := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [normalForm_mk, reconstruct_polynomial]

theorem normalForm_injective (a : R) : Function.Injective (normalForm R a) := by
  intro x y h
  have hh := congrArg (fromNormal R a) h
  simpa only [reconstruct] using hh

theorem flat (a : R) : Module.Flat R (NodeAlgebra R a) := by
  apply Module.Flat.of_retract (normalForm R a) (fromNormal R a)
  exact LinearMap.ext (reconstruct R a)

def laurentMap (a : R) : NodeAlgebra R a →ₐ[R] AddMonoidAlgebra R ℤ :=
  NodeAlgebraProof.nodeLift R a
    (AddMonoidAlgebra.single 1 1) (AddMonoidAlgebra.single (-1) a)
    (by
      simp only [AddMonoidAlgebra.single_mul_single, add_neg_cancel, one_mul]
      rfl)

theorem laurentMap_nodeU (a : R) :
    laurentMap R a (nodeU R a) = AddMonoidAlgebra.single 1 1 :=
  NodeAlgebraProof.nodeLift_nodeU R a _ _ _

theorem laurentMap_nodeV (a : R) :
    laurentMap R a (nodeV R a) = AddMonoidAlgebra.single (-1) a :=
  NodeAlgebraProof.nodeLift_nodeV R a _ _ _

theorem laurentMap_normalPower (a : R) (z : ℤ) :
    laurentMap R a (normalPower R a z) =
      AddMonoidAlgebra.single z (a ^ (-z).toNat) := by
  rw [normalPower, map_mul, map_pow, map_pow, laurentMap_nodeU, laurentMap_nodeV]
  simp only [AddMonoidAlgebra.single_pow, AddMonoidAlgebra.single_mul_single,
    one_pow, one_mul, nsmul_eq_mul, mul_one, mul_neg, mul_one]
  congr 1
  omega

theorem laurentMap_fromNormal_coeff (a : R) (f : ℤ →₀ R) (z : ℤ) :
    (laurentMap R a (fromNormal R a f)).coeff z = f z * a ^ (-z).toNat := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, zero_mul]
  | add f g hf hg =>
      simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hf, hg, add_mul]
  | single i c =>
      rw [fromNormal_single, map_smul, laurentMap_normalPower]
      simp only [AddMonoidAlgebra.coeff_smul, AddMonoidAlgebra.coeff_single,
        Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply]
      split_ifs with hiz
      · subst z
        rfl
      · simp only [mul_zero, zero_mul]

theorem laurentMap_injective [IsDomain R] (a : R) (ha : a ≠ 0) :
    Function.Injective (laurentMap R a) := by
  intro x y hxy
  apply normalForm_injective R a
  ext z
  apply mul_right_cancel₀ (pow_ne_zero (-z).toNat ha)
  rw [← laurentMap_fromNormal_coeff, ← laurentMap_fromNormal_coeff,
    reconstruct, reconstruct, hxy]

theorem domain [IsDomain R] (a : R) (ha : a ≠ 0) : IsDomain (NodeAlgebra R a) :=
  Function.Injective.isDomain (laurentMap R a) (laurentMap_injective R a ha)

end NodeNormalFormProof
end


/-- Flatness of this elementary model does not require a != 0. -/
theorem nodeAlgebra_flat (a : R) : Module.Flat R (NodeAlgebra R a) := by
  exact NodeNormalFormProof.flat R a

/-- The smoothing parameter must be nonzero for integrality. -/
theorem nodeAlgebra_domain [IsDomain R] (a : R) (ha : a ≠ 0) :
    IsDomain (NodeAlgebra R a) := by
  exact NodeNormalFormProof.domain R a ha

/-- Polynomial functions on the two branches agreeing at the node. -/
def BranchEqualizer : Subalgebra R (Polynomial R × Polynomial R) where
  carrier := {p | Polynomial.eval 0 p.1 = Polynomial.eval 0 p.2}
  zero_mem' := by simp
  add_mem' := by
    intro p q hp hq
    change Polynomial.eval 0 (p.1 + q.1) = Polynomial.eval 0 (p.2 + q.2)
    simp only [Polynomial.eval_add]
    exact congrArg₂ (· + ·) hp hq
  one_mem' := by simp
  mul_mem' := by
    intro p q hp hq
    change Polynomial.eval 0 (p.1 * q.1) = Polynomial.eval 0 (p.2 * q.2)
    simp only [Polynomial.eval_mul]
    exact congrArg₂ (· * ·) hp hq
  algebraMap_mem' := by intro r; rfl

noncomputable section
set_option autoImplicit false
variable (R : Type*) [CommRing R]

namespace NodeAlgebraProof

def branchU : BranchEqualizer R :=
  ⟨(Polynomial.X, 0), by
    change Polynomial.eval 0 (Polynomial.X : Polynomial R) =
      Polynomial.eval 0 (0 : Polynomial R)
    simp⟩

def branchV : BranchEqualizer R :=
  ⟨(0, Polynomial.X), by
    change Polynomial.eval 0 (0 : Polynomial R) =
      Polynomial.eval 0 (Polynomial.X : Polynomial R)
    simp⟩

theorem branchU_mul_branchV : branchU R * branchV R = 0 := by
  apply Subtype.ext
  change (Polynomial.X * (0 : Polynomial R), (0 : Polynomial R) * Polynomial.X) =
    (0, 0)
  simp

section BranchLift

variable {A : Type*} [CommRing A] [Algebra R A]

/-- Evaluation on both branches, with the common constant counted once. -/
def branchLift (u v : A) (h : u * v = 0) : BranchEqualizer R →ₐ[R] A where
  toFun b := Polynomial.aeval u b.val.1 + Polynomial.aeval v b.val.2 -
    algebraMap R A (Polynomial.eval 0 b.val.1)
  map_zero' := by
    change Polynomial.aeval u (0 : Polynomial R) + Polynomial.aeval v (0 : Polynomial R) -
      algebraMap R A (Polynomial.eval 0 (0 : Polynomial R)) = 0
    simp
  map_one' := by
    change Polynomial.aeval u (1 : Polynomial R) + Polynomial.aeval v (1 : Polynomial R) -
      algebraMap R A (Polynomial.eval 0 (1 : Polynomial R)) = 1
    simp
  map_add' b c := by
    change Polynomial.aeval u (b.val.1 + c.val.1) +
        Polynomial.aeval v (b.val.2 + c.val.2) -
        algebraMap R A (Polynomial.eval 0 (b.val.1 + c.val.1)) =
      (Polynomial.aeval u b.val.1 + Polynomial.aeval v b.val.2 -
        algebraMap R A (Polynomial.eval 0 b.val.1)) +
      (Polynomial.aeval u c.val.1 + Polynomial.aeval v c.val.2 -
        algebraMap R A (Polynomial.eval 0 c.val.1))
    simp only [map_add, Polynomial.eval_add]
    ring
  map_mul' b c := by
    have hb : Polynomial.eval 0 b.val.1 = Polynomial.eval 0 b.val.2 := b.property
    have hc : Polynomial.eval 0 c.val.1 = Polynomial.eval 0 c.val.2 := c.property
    have hcross₁ := aeval_cross_zero R u v h b.val.1 c.val.2
    have hcross₂ := aeval_cross_zero R u v h c.val.1 b.val.2
    rw [← hc] at hcross₁
    rw [← hb] at hcross₂
    change Polynomial.aeval u (b.val.1 * c.val.1) +
        Polynomial.aeval v (b.val.2 * c.val.2) -
        algebraMap R A (Polynomial.eval 0 (b.val.1 * c.val.1)) =
      (Polynomial.aeval u b.val.1 + Polynomial.aeval v b.val.2 -
        algebraMap R A (Polynomial.eval 0 b.val.1)) *
      (Polynomial.aeval u c.val.1 + Polynomial.aeval v c.val.2 -
        algebraMap R A (Polynomial.eval 0 c.val.1))
    simp only [map_mul, Polynomial.eval_mul]
    linear_combination -hcross₁ - hcross₂
  commutes' r := by
    change Polynomial.aeval u (Polynomial.C r) + Polynomial.aeval v (Polynomial.C r) -
      algebraMap R A (Polynomial.eval 0 (Polynomial.C r)) = algebraMap R A r
    simp

theorem branchLift_branchU (u v : A) (h : u * v = 0) :
    branchLift R u v h (branchU R) = u := by
  change Polynomial.aeval u (Polynomial.X : Polynomial R) +
    Polynomial.aeval v (0 : Polynomial R) -
    algebraMap R A (Polynomial.eval 0 (Polynomial.X : Polynomial R)) = u
  simp

theorem branchLift_branchV (u v : A) (h : u * v = 0) :
    branchLift R u v h (branchV R) = v := by
  change Polynomial.aeval u (0 : Polynomial R) +
    Polynomial.aeval v (Polynomial.X : Polynomial R) -
    algebraMap R A (Polynomial.eval 0 (0 : Polynomial R)) = v
  simp

end BranchLift

theorem aeval_branchU_val (p : Polynomial R) :
    (Polynomial.aeval (branchU R) p).val =
      (p, Polynomial.C (Polynomial.eval 0 p)) := by
  rw [Polynomial.aeval_subalgebra_coe]
  change Polynomial.aeval ((Polynomial.X : Polynomial R), (0 : Polynomial R)) p = _
  rw [Polynomial.aeval_prod_apply]
  simp only [Polynomial.aeval_X_left_apply, aeval_at_zero, Polynomial.algebraMap_eq]

theorem aeval_branchV_val (p : Polynomial R) :
    (Polynomial.aeval (branchV R) p).val =
      (Polynomial.C (Polynomial.eval 0 p), p) := by
  rw [Polynomial.aeval_subalgebra_coe]
  change Polynomial.aeval ((0 : Polynomial R), (Polynomial.X : Polynomial R)) p = _
  rw [Polynomial.aeval_prod_apply]
  simp only [Polynomial.aeval_X_left_apply, aeval_at_zero, Polynomial.algebraMap_eq]

def nodeToEqualizer : NodeAlgebra R 0 →ₐ[R] BranchEqualizer R :=
  nodeLift R 0 (branchU R) (branchV R) (by simpa using branchU_mul_branchV R)

def equalizerToNode : BranchEqualizer R →ₐ[R] NodeAlgebra R 0 :=
  branchLift R (nodeU R 0) (nodeV R 0) (by simpa using node_relation R 0)

theorem nodeToEqualizer_nodeU : nodeToEqualizer R (nodeU R 0) = branchU R := by
  simp only [nodeToEqualizer, nodeLift_nodeU]

theorem nodeToEqualizer_nodeV : nodeToEqualizer R (nodeV R 0) = branchV R := by
  simp only [nodeToEqualizer, nodeLift_nodeV]

theorem equalizerToNode_branchU : equalizerToNode R (branchU R) = nodeU R 0 := by
  simp only [equalizerToNode, branchLift_branchU]

theorem equalizerToNode_branchV : equalizerToNode R (branchV R) = nodeV R 0 := by
  simp only [equalizerToNode, branchLift_branchV]

theorem nodeToEqualizer_aeval_nodeU (p : Polynomial R) :
    (nodeToEqualizer R (Polynomial.aeval (nodeU R 0) p)).val =
      (p, Polynomial.C (Polynomial.eval 0 p)) := by
  rw [← Polynomial.aeval_algHom_apply, nodeToEqualizer_nodeU]
  exact aeval_branchU_val R p

theorem nodeToEqualizer_aeval_nodeV (p : Polynomial R) :
    (nodeToEqualizer R (Polynomial.aeval (nodeV R 0) p)).val =
      (Polynomial.C (Polynomial.eval 0 p), p) := by
  rw [← Polynomial.aeval_algHom_apply, nodeToEqualizer_nodeV]
  exact aeval_branchV_val R p

theorem equalizerToNode_comp_nodeToEqualizer :
    (equalizerToNode R).comp (nodeToEqualizer R) = AlgHom.id R (NodeAlgebra R 0) := by
  apply nodeAlgHom_ext R 0
  · simp only [AlgHom.comp_apply, nodeToEqualizer_nodeU, equalizerToNode_branchU,
      AlgHom.id_apply]
  · simp only [AlgHom.comp_apply, nodeToEqualizer_nodeV, equalizerToNode_branchV,
      AlgHom.id_apply]

theorem nodeToEqualizer_comp_equalizerToNode :
    (nodeToEqualizer R).comp (equalizerToNode R) = AlgHom.id R (BranchEqualizer R) := by
  apply AlgHom.ext
  intro b
  apply Subtype.ext
  change (nodeToEqualizer R
    (Polynomial.aeval (nodeU R 0) b.val.1 + Polynomial.aeval (nodeV R 0) b.val.2 -
      algebraMap R (NodeAlgebra R 0) (Polynomial.eval 0 b.val.1))).val = b.val
  simp only [map_sub, map_add, AlgHom.commutes]
  change (nodeToEqualizer R (Polynomial.aeval (nodeU R 0) b.val.1)).val +
      (nodeToEqualizer R (Polynomial.aeval (nodeV R 0) b.val.2)).val -
      (algebraMap R (BranchEqualizer R) (Polynomial.eval 0 b.val.1)).val = b.val
  rw [nodeToEqualizer_aeval_nodeU, nodeToEqualizer_aeval_nodeV]
  change (b.val.1, Polynomial.C (Polynomial.eval 0 b.val.1)) +
      (Polynomial.C (Polynomial.eval 0 b.val.2), b.val.2) -
      (Polynomial.C (Polynomial.eval 0 b.val.1), Polynomial.C (Polynomial.eval 0 b.val.1)) =
      (b.val.1, b.val.2)
  have hb : Polynomial.eval 0 b.val.1 = Polynomial.eval 0 b.val.2 := b.property
  apply Prod.ext
  · change b.val.1 + Polynomial.C (Polynomial.eval 0 b.val.2) -
      Polynomial.C (Polynomial.eval 0 b.val.1) = b.val.1
    rw [← hb]
    ring
  · change Polynomial.C (Polynomial.eval 0 b.val.1) + b.val.2 -
      Polynomial.C (Polynomial.eval 0 b.val.1) = b.val.2
    ring

def normalizationEquiv : NodeAlgebra R 0 ≃ₐ[R] BranchEqualizer R :=
  AlgEquiv.ofAlgHom (nodeToEqualizer R) (equalizerToNode R)
    (nodeToEqualizer_comp_equalizerToNode R) (equalizerToNode_comp_nodeToEqualizer R)

theorem node_normalizationEqualizer :
    ∃ e : NodeAlgebra R 0 ≃ₐ[R] BranchEqualizer R,
      (e (nodeU R 0)).val = (Polynomial.X, 0) ∧
      (e (nodeV R 0)).val = (0, Polynomial.X) := by
  refine ⟨normalizationEquiv R, ?_, ?_⟩
  · change (nodeToEqualizer R (nodeU R 0)).val = (Polynomial.X, 0)
    rw [nodeToEqualizer_nodeU]
    rfl
  · change (nodeToEqualizer R (nodeV R 0)).val = (0, Polynomial.X)
    rw [nodeToEqualizer_nodeV]
    rfl

theorem node_u_nonzero [Nontrivial R] : nodeU R 0 ≠ 0 := by
  intro h
  have hh := congrArg (fun z : NodeAlgebra R 0 => (nodeToEqualizer R z).val.1) h
  have hx : (Polynomial.X : Polynomial R) = 0 := by
    have hz : ((0 : BranchEqualizer R).val).1 = (0 : Polynomial R) := rfl
    simpa only [nodeToEqualizer_nodeU, branchU, map_zero, hz] using hh
  exact Polynomial.X_ne_zero hx

theorem node_v_nonzero [Nontrivial R] : nodeV R 0 ≠ 0 := by
  intro h
  have hh := congrArg (fun z : NodeAlgebra R 0 => (nodeToEqualizer R z).val.2) h
  have hx : (Polynomial.X : Polynomial R) = 0 := by
    have hz : ((0 : BranchEqualizer R).val).2 = (0 : Polynomial R) := rfl
    simpa only [nodeToEqualizer_nodeV, branchV, map_zero, hz] using hh
  exact Polynomial.X_ne_zero hx

theorem node_special_not_domain [Nontrivial R] :
    ¬ IsDomain (NodeAlgebra R 0) := by
  intro h
  letI : IsDomain (NodeAlgebra R 0) := h
  have hz : nodeU R 0 * nodeV R 0 = 0 := by simpa using node_relation R 0
  rcases mul_eq_zero.mp hz with hu | hv
  · exact node_u_nonzero R hu
  · exact node_v_nonzero R hv

theorem branch_function_gluing (p q : Polynomial R)
    (h : Polynomial.eval 0 p = Polynomial.eval 0 q) :
    ∃! b : BranchEqualizer R, b.val = (p, q) := by
  refine ⟨⟨(p, q), h⟩, rfl, ?_⟩
  intro b hb
  exact Subtype.ext hb

end NodeAlgebraProof

end

/-- The isomorphism is required to identify BOTH branch coordinates.
An unconstrained equivalence of rings would lose the geometric map. -/
theorem node_normalizationEqualizer :
    ∃ e : NodeAlgebra R 0 ≃ₐ[R] BranchEqualizer R,
      (e (nodeU R 0)).val = (Polynomial.X, 0) ∧
      (e (nodeV R 0)).val = (0, Polynomial.X) := by
  exact LeBrunSalamon.PhaseTwentyNine.NodeAlgebraProof.node_normalizationEqualizer (R := R)

theorem node_u_nonzero [Nontrivial R] : nodeU R 0 ≠ 0 := by
  exact LeBrunSalamon.PhaseTwentyNine.NodeAlgebraProof.node_u_nonzero (R := R)

theorem node_v_nonzero [Nontrivial R] : nodeV R 0 ≠ 0 := by
  exact LeBrunSalamon.PhaseTwentyNine.NodeAlgebraProof.node_v_nonzero (R := R)

theorem node_special_not_domain [Nontrivial R] :
    ¬ IsDomain (NodeAlgebra R 0) := by
  exact LeBrunSalamon.PhaseTwentyNine.NodeAlgebraProof.node_special_not_domain (R := R)

/-- Agreement of functions on the branches is sufficient and necessary
for gluing at the ordinary reduced node, in this actual local model. -/
theorem branch_function_gluing (p q : Polynomial R)
    (h : Polynomial.eval 0 p = Polynomial.eval 0 q) :
    ∃! b : BranchEqualizer R, b.val = (p, q) := by
  exact LeBrunSalamon.PhaseTwentyNine.NodeAlgebraProof.branch_function_gluing (R := R) (p := p) (q := q) (h := h)

end NodeAlgebra

section StableTrees

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- The valence is the cardinality of the actual finite neighbor set. -/
def graphValence (G : SimpleGraph V) (v : V) : ℕ := by
  classical
  exact (Finset.univ.filter (fun w => G.Adj v w)).card

/-- Degree labels on a genus-zero UNMARKED dual graph. Contracted
vertices require valence at least three. Marks would change stability. -/
structure StableUnmarkedTree where
  graph : SimpleGraph V
  tree : graph.IsTree
  degree : V → ℕ
  contractedStable : ∀ v, degree v = 0 →
    3 ≤ graphValence graph v

/-- The total ample degree counts only noncontracted components. -/
def StableUnmarkedTree.totalDegree (T : StableUnmarkedTree (V := V)) : ℕ :=
  ∑ v, T.degree v

noncomputable section
set_option autoImplicit false

open scoped BigOperators

namespace DualGraphProof

variable {V : Type*} [Fintype V]

/-- The project's valence is the degree of the same actual simple graph. -/
theorem graphValence_eq_degree (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    graphValence G v = G.degree v := by
  classical
  unfold graphValence
  rw [← G.card_neighborFinset_eq_degree v]
  apply congrArg Finset.card
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, SimpleGraph.mem_neighborFinset]

theorem degree_le_total (T : StableUnmarkedTree (V := V)) (v : V) :
    T.degree v ≤ T.totalDegree := by
  classical
  change T.degree v ≤ ∑ w : V, T.degree w
  exact Finset.single_le_sum (fun w _ => Nat.zero_le (T.degree w)) (Finset.mem_univ v)

/-- Tree valences and unmarked stability give an actual vertex bound.
Every vertex contributes at least three to valence plus twice its degree. -/
theorem vertex_bound_of_nontrivial [Nontrivial V] (T : StableUnmarkedTree (V := V)) :
    Fintype.card V + 2 ≤ 2 * T.totalDegree := by
  classical
  have hpoint : ∀ v : V, 3 ≤ T.graph.degree v + 2 * T.degree v := by
    intro v
    by_cases hz : T.degree v = 0
    · have hs := T.contractedStable v hz
      rw [graphValence_eq_degree] at hs
      omega
    · have hv := T.tree.preconnected.degree_pos_of_nontrivial v
      omega
  have hsum : (∑ _v : V, (3 : ℕ)) ≤
      ∑ v : V, (T.graph.degree v + 2 * T.degree v) :=
    Finset.sum_le_sum (fun v _ => hpoint v)
  have hsum' : Fintype.card V * 3 ≤
      (∑ v : V, T.graph.degree v) + 2 * T.totalDegree := by
    simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul,
      Finset.sum_add_distrib, ← Finset.mul_sum, StableUnmarkedTree.totalDegree] using hsum
  have htree := T.tree.card_edgeFinset
  have hvalence := T.graph.sum_degrees_eq_twice_card_edges
  omega

/-- The exact original no-contracted-components proposition, with fresh name. -/
theorem stableDegreeTwoTree_noContracted
    (T : StableUnmarkedTree (V := V)) (h : T.totalDegree = 2) :
    ∀ v, 0 < T.degree v := by
  classical
  intro v
  by_contra hpos
  have hz : T.degree v = 0 := by omega
  have hs := T.contractedStable v hz
  rw [graphValence_eq_degree] at hs
  have hn := T.graph.degree_lt_card_verts v
  haveI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hb := vertex_bound_of_nontrivial T
  rw [h] at hb
  omega

theorem stableDegreeTwoTree_atMostTwoVertices
    (T : StableUnmarkedTree (V := V)) (h : T.totalDegree = 2) :
    Fintype.card V ≤ 2 := by
  classical
  have hs : (∑ _v : V, (1 : ℕ)) ≤ ∑ v : V, T.degree v :=
    Finset.sum_le_sum (fun v _ => stableDegreeTwoTree_noContracted T h v)
  have hn : Fintype.card V ≤ T.totalDegree := by
    simpa [StableUnmarkedTree.totalDegree] using hs
  omega

/-- With a unique actual vertex, its label is the entire degree sum. -/
theorem degree_eq_total_of_card_eq_one (T : StableUnmarkedTree (V := V))
    (hcard : Fintype.card V = 1) (v : V) : T.degree v = T.totalDegree := by
  classical
  haveI : Subsingleton V := Fintype.card_le_one_iff_subsingleton.mp (by omega)
  change T.degree v = ∑ w : V, T.degree w
  symm
  apply Finset.sum_eq_single v
  · intro w _ hne
    exact (hne (Subsingleton.elim w v)).elim
  · simp

theorem stableDegreeTwoTree_classification
    (T : StableUnmarkedTree (V := V)) (h : T.totalDegree = 2) :
    (Fintype.card V = 1 ∧ ∀ v, T.degree v = 2) ∨
    (Fintype.card V = 2 ∧ ∀ v, T.degree v = 1) := by
  classical
  haveI : Nonempty V := T.tree.connected.nonempty
  have hc := stableDegreeTwoTree_atMostTwoVertices T h
  have hp : 0 < Fintype.card V := Fintype.card_pos
  have hcards : Fintype.card V = 1 ∨ Fintype.card V = 2 := by omega
  rcases hcards with hcard | hcard
  · exact Or.inl ⟨hcard, fun v => (degree_eq_total_of_card_eq_one T hcard v).trans h⟩
  · refine Or.inr ⟨hcard, ?_⟩
    have hsum : (∑ _v : V, (1 : ℕ)) = ∑ v : V, T.degree v := by
      calc
        _ = Fintype.card V := by simp
        _ = T.totalDegree := hcard.trans h.symm
        _ = _ := rfl
    have hall := (Finset.sum_eq_sum_iff_of_le
      (s := Finset.univ) (f := fun _v : V => (1 : ℕ)) (g := fun v => T.degree v)
      (fun v _ => stableDegreeTwoTree_noContracted T h v)).mp hsum
    exact fun v => (hall v (Finset.mem_univ v)).symm

theorem stableDegreeOneTree_singleComponent
    (T : StableUnmarkedTree (V := V)) (h : T.totalDegree = 1) :
    Fintype.card V = 1 ∧ ∀ v, T.degree v = 1 := by
  classical
  haveI : Nonempty V := T.tree.connected.nonempty
  have hcard : Fintype.card V = 1 := by
    by_contra hc
    have hp : 0 < Fintype.card V := Fintype.card_pos
    haveI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    have hb := vertex_bound_of_nontrivial T
    rw [h] at hb
    omega
  exact ⟨hcard, fun v => (degree_eq_total_of_card_eq_one T hcard v).trans h⟩

theorem stableUnmarkedTree_positiveDegree
    (T : StableUnmarkedTree (V := V)) : 0 < T.totalDegree := by
  classical
  haveI : Nonempty V := T.tree.connected.nonempty
  rcases subsingleton_or_nontrivial V with hs | hn
  · letI : Subsingleton V := hs
    let v : V := Classical.ofNonempty
    have hv : T.graph.degree v = 0 := SimpleGraph.degree_eq_zero_of_subsingleton v
    have hp : 0 < T.degree v := by
      by_contra hpos
      have hz : T.degree v = 0 := by omega
      have hstable := T.contractedStable v hz
      rw [graphValence_eq_degree, hv] at hstable
      omega
    exact lt_of_lt_of_le hp (degree_le_total T v)
  · letI : Nontrivial V := hn
    obtain ⟨v, hv⟩ := T.tree.exists_vert_degree_one_of_nontrivial
    have hp : 0 < T.degree v := by
      by_contra hpos
      have hz : T.degree v = 0 := by omega
      have hstable := T.contractedStable v hz
      rw [graphValence_eq_degree, hv] at hstable
      omega
    exact lt_of_lt_of_le hp (degree_le_total T v)

end DualGraphProof

end

/-- Unlike the older positive-degree list, this theorem EXCLUDES
contracted components by using the graph and unmarked stability. -/
theorem stableDegreeTwoTree_noContracted
    (T : StableUnmarkedTree (V := V)) (h : T.totalDegree = 2) :
    ∀ v, 0 < T.degree v := by
  exact DualGraphProof.stableDegreeTwoTree_noContracted T h

theorem stableDegreeTwoTree_atMostTwoVertices
    (T : StableUnmarkedTree (V := V)) (h : T.totalDegree = 2) :
    Fintype.card V ≤ 2 := by
  exact DualGraphProof.stableDegreeTwoTree_atMostTwoVertices T h

theorem stableDegreeTwoTree_classification
    (T : StableUnmarkedTree (V := V)) (h : T.totalDegree = 2) :
    (Fintype.card V = 1 ∧ ∀ v, T.degree v = 2) ∨
    (Fintype.card V = 2 ∧ ∀ v, T.degree v = 1) := by
  exact DualGraphProof.stableDegreeTwoTree_classification T h

theorem stableDegreeOneTree_singleComponent
    (T : StableUnmarkedTree (V := V)) (h : T.totalDegree = 1) :
    Fintype.card V = 1 ∧ ∀ v, T.degree v = 1 := by
  exact DualGraphProof.stableDegreeOneTree_singleComponent T h

theorem stableUnmarkedTree_positiveDegree
    (T : StableUnmarkedTree (V := V)) : 0 < T.totalDegree := by
  exact DualGraphProof.stableUnmarkedTree_positiveDegree T

/-- The contact-line proof uses the UNMARKED degree-two boundary. For marked stable maps, contracted
vertices with enough marks can occur and the preceding classification must not be reused unchanged. -/
structure StableMarkedTree (m : ℕ) where
  graph : SimpleGraph V
  tree : graph.IsTree
  degree : V → ℕ
  markingVertex : Fin m → V
  contractedStable : ∀ v, degree v = 0 →
    3 ≤ graphValence graph v +
      (Finset.univ.filter (fun i => markingVertex i = v)).card

end StableTrees

section FaithfullyFlatDescent

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]

/-- Equality in the two pullbacks is the actual Cech descent condition. -/
def IsScalarDescentCompatible (b : B) : Prop :=
  (b ⊗ₜ[A] (1 : B)) = ((1 : B) ⊗ₜ[A] b)

noncomputable section
set_option autoImplicit false
open scoped TensorProduct
variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]

namespace ScalarDescentProofCandidate

theorem algebraMap_descentCompatible (a : A) :
    IsScalarDescentCompatible A B (algebraMap A B a) := by
  change (algebraMap A B a) ⊗ₜ[A] (1 : B) =
    (1 : B) ⊗ₜ[A] (algebraMap A B a)
  simpa only [Algebra.TensorProduct.includeLeftSubRight_apply, sub_eq_zero] using
    (Algebra.TensorProduct.includeLeftSubRight_algebraMap_zero (R := A) (S := B) a)

theorem faithfullyFlat_scalar_descent [Module.FaithfullyFlat A B]
    (b : B) (hb : IsScalarDescentCompatible A B b) :
    ∃! a : A, algebraMap A B a = b := by
  have hz : Algebra.TensorProduct.includeLeftSubRight A B b = 0 := by
    change b ⊗ₜ[A] (1 : B) - (1 : B) ⊗ₜ[A] b = 0
    exact sub_eq_zero.mpr hb
  have he : Function.Exact (Algebra.linearMap A B)
      (Algebra.TensorProduct.includeLeftSubRight A B) :=
    Algebra.IsEffective.of_faithfullyFlat A B
  obtain ⟨a, ha⟩ := (he b).mp hz
  have ha0 : algebraMap A B a = b := ha
  refine ⟨a, ha0, ?_⟩
  intro a' ha'
  exact FaithfulSMul.algebraMap_injective A B (ha'.trans ha0.symm)

theorem faithfullyFlat_scalar_descent_iff [Module.FaithfullyFlat A B]
    (b : B) :
    IsScalarDescentCompatible A B b ↔
      ∃ a : A, algebraMap A B a = b := by
  constructor
  · intro hb
    exact (faithfullyFlat_scalar_descent A B b hb).exists
  · rintro ⟨a, rfl⟩
    exact algebraMap_descentCompatible A B a

theorem faithfullyFlat_algebraMap_injective [Module.FaithfullyFlat A B] :
    Function.Injective (algebraMap A B) := by
  exact FaithfulSMul.algebraMap_injective A B

theorem faithfullyFlat_vector_descent [Module.FaithfullyFlat A B]
    (r : ℕ) (b : Fin r → B)
    (hb : ∀ i, IsScalarDescentCompatible A B (b i)) :
    ∃! a : Fin r → A, ∀ i, algebraMap A B (a i) = b i := by
  classical
  have h : ∀ i : Fin r, ∃ a : A, algebraMap A B a = b i := fun i =>
    (faithfullyFlat_scalar_descent A B (b i) (hb i)).exists
  choose a ha using h
  refine ⟨a, ha, ?_⟩
  intro a' ha'
  funext i
  exact faithfullyFlat_algebraMap_injective A B ((ha' i).trans (ha i).symm)

theorem scalarDescentCompatible_add {b c : B}
    (hb : IsScalarDescentCompatible A B b)
    (hc : IsScalarDescentCompatible A B c) :
    IsScalarDescentCompatible A B (b + c) := by
  change (b + c) ⊗ₜ[A] (1 : B) = (1 : B) ⊗ₜ[A] (b + c)
  rw [TensorProduct.add_tmul, TensorProduct.tmul_add]
  exact congrArg₂ (fun x y : B ⊗[A] B => x + y) hb hc

theorem scalarDescentCompatible_mul {b c : B}
    (hb : IsScalarDescentCompatible A B b)
    (hc : IsScalarDescentCompatible A B c) :
    IsScalarDescentCompatible A B (b * c) := by
  change (b * c) ⊗ₜ[A] (1 : B) = (1 : B) ⊗ₜ[A] (b * c)
  calc
    (b * c) ⊗ₜ[A] (1 : B) =
        (b ⊗ₜ[A] (1 : B)) * (c ⊗ₜ[A] (1 : B)) := by
          simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    _ = ((1 : B) ⊗ₜ[A] b) * ((1 : B) ⊗ₜ[A] c) :=
      congrArg₂ (fun x y : B ⊗[A] B => x * y) hb hc
    _ = (1 : B) ⊗ₜ[A] (b * c) := by
      simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

end ScalarDescentProofCandidate

end

theorem algebraMap_descentCompatible (a : A) :
    IsScalarDescentCompatible A B (algebraMap A B a) := by
  exact LeBrunSalamon.PhaseTwentyNine.ScalarDescentProofCandidate.algebraMap_descentCompatible (A := A) (B := B) (a := a)

/-- Faithful flatness is essential; injectivity alone is not an
adequate replacement for effective descent. -/
theorem faithfullyFlat_scalar_descent [Module.FaithfullyFlat A B]
    (b : B) (hb : IsScalarDescentCompatible A B b) :
    ∃! a : A, algebraMap A B a = b := by
  exact LeBrunSalamon.PhaseTwentyNine.ScalarDescentProofCandidate.faithfullyFlat_scalar_descent (A := A) (B := B) (b := b) (hb := hb)

theorem faithfullyFlat_scalar_descent_iff [Module.FaithfullyFlat A B]
    (b : B) :
    IsScalarDescentCompatible A B b ↔
      ∃ a : A, algebraMap A B a = b := by
  exact LeBrunSalamon.PhaseTwentyNine.ScalarDescentProofCandidate.faithfullyFlat_scalar_descent_iff (A := A) (B := B) (b := b)

theorem faithfullyFlat_algebraMap_injective [Module.FaithfullyFlat A B] :
    Function.Injective (algebraMap A B) := by
  exact LeBrunSalamon.PhaseTwentyNine.ScalarDescentProofCandidate.faithfullyFlat_algebraMap_injective (A := A) (B := B)

/-- In a local line frame, a section descends exactly when its scalar
coefficient does. This is later glued using the transition units. -/
theorem faithfullyFlat_vector_descent [Module.FaithfullyFlat A B]
    (r : ℕ) (b : Fin r → B)
    (hb : ∀ i, IsScalarDescentCompatible A B (b i)) :
    ∃! a : Fin r → A, ∀ i, algebraMap A B (a i) = b i := by
  exact LeBrunSalamon.PhaseTwentyNine.ScalarDescentProofCandidate.faithfullyFlat_vector_descent (A := A) (B := B) (r := r) (b := b) (hb := hb)

theorem scalarDescentCompatible_add {b c : B}
    (hb : IsScalarDescentCompatible A B b)
    (hc : IsScalarDescentCompatible A B c) :
    IsScalarDescentCompatible A B (b + c) := by
  exact LeBrunSalamon.PhaseTwentyNine.ScalarDescentProofCandidate.scalarDescentCompatible_add (A := A) (B := B) (b := b) (c := c) (hb := hb) (hc := hc)

theorem scalarDescentCompatible_mul {b c : B}
    (hb : IsScalarDescentCompatible A B b)
    (hc : IsScalarDescentCompatible A B c) :
    IsScalarDescentCompatible A B (b * c) := by
  exact LeBrunSalamon.PhaseTwentyNine.ScalarDescentProofCandidate.scalarDescentCompatible_mul (A := A) (B := B) (b := b) (c := c) (hb := hb) (hc := hc)

end FaithfullyFlatDescent

end LeBrunSalamon.PhaseTwentyNine

/-!
# Phase 30 -- intrinsic differentials and the conormal sequence

The map df is defined by pulling BACK FUNCTIONS, applying the universal
derivation on the source, and using the pullback/pushforward adjunction.
It is not a supplied linear map with the right source and target.
-/

namespace LeBrunSalamon.PhaseThirty

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix

set_option backward.isDefEq.respectTransparency false in
/-- The derivation a |-> d(f# a) with values in f_* Ω_{X/S}. -/
def pulledFunctionDifferential {X Y S : Scheme}
    (f : X ⟶ Y) (s : Y ⟶ S) :
    RelativeSheafDerivation s
      ((Scheme.Modules.pushforward f).obj (cotangentSheaf (f ≫ s))) where
  apply U a := (cotangentPresentation (f ≫ s)).differential.apply
    (f ⁻¹ᵁ U) (f.app U a)
  zero := by intro U; simp [(cotangentPresentation (f ≫ s)).differential.zero]
  add := by intros; simp [(cotangentPresentation (f ≫ s)).differential.add]
  leibniz := by
    intro U a b
    change (cotangentPresentation (f ≫ s)).differential.apply (f ⁻¹ᵁ U)
        (f.app U (a * b)) =
      (f.app U a) • (cotangentPresentation (f ≫ s)).differential.apply (f ⁻¹ᵁ U) (f.app U b) +
      (f.app U b) • (cotangentPresentation (f ≫ s)).differential.apply (f ⁻¹ᵁ U) (f.app U a)
    rw [map_mul]
    exact (cotangentPresentation (f ≫ s)).differential.leibniz _ _ _
  naturality := by
    intro U V i a
    exact ((cotangentPresentation (f ≫ s)).differential.naturality
      ((TopologicalSpace.Opens.map f.base).map i) (f.app V a)).trans
        (congrArg ((cotangentPresentation (f ≫ s)).differential.apply (f ⁻¹ᵁ U))
          (congrArg (fun t => t a) (f.naturality i.op)).symm)
  killsBase := by
    intro W a
    exact (cotangentPresentation (f ≫ s)).differential.killsBase W a

/-- The genuine cotangent differential f*Ω_{Y/S} -> Ω_{X/S}. -/
def cotangentMap {X Y S : Scheme} (f : X ⟶ Y) (s : Y ⟶ S) :
    pullbackModule f (cotangentSheaf s) ⟶ cotangentSheaf (f ≫ s) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv
    (cotangentSheaf s) (cotangentSheaf (f ≫ s))).symm
      (differentialLift (pulledFunctionDifferential f s))

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix

namespace CotangentConsequenceProof

theorem cotangentMap_adjoint {X Y S : Scheme} (f : X ⟶ Y) (s : Y ⟶ S) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv
      (cotangentSheaf s) (cotangentSheaf (f ≫ s)) (cotangentMap f s) =
        differentialLift (pulledFunctionDifferential f s) := by
  exact ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv
    (cotangentSheaf s) (cotangentSheaf (f ≫ s))).apply_symm_apply
      (differentialLift (pulledFunctionDifferential f s))

end CotangentConsequenceProof

end

theorem cotangentMap_adjoint {X Y S : Scheme} (f : X ⟶ Y) (s : Y ⟶ S) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv
      (cotangentSheaf s) (cotangentSheaf (f ≫ s)) (cotangentMap f s) =
        differentialLift (pulledFunctionDifferential f s) := by
  exact LeBrunSalamon.PhaseThirty.CotangentConsequenceProof.cotangentMap_adjoint (X := X) (Y := Y) (S := S) (f := f) (s := s)

set_option backward.isDefEq.respectTransparency false in
/-- Relative derivations with smaller base may be viewed over a larger
base via composition; the function formula is unchanged. -/
def relativeDifferentialOverComposite {X Y S : Scheme}
    (f : X ⟶ Y) (s : Y ⟶ S) :
    RelativeSheafDerivation (f ≫ s) (cotangentSheaf f) where
  apply := (cotangentPresentation f).differential.apply
  zero := (cotangentPresentation f).differential.zero
  add := (cotangentPresentation f).differential.add
  leibniz := (cotangentPresentation f).differential.leibniz
  naturality := (cotangentPresentation f).differential.naturality
  killsBase := by
    intro W a
    exact (cotangentPresentation f).differential.killsBase (s ⁻¹ᵁ W) (s.app W a)

def cotangentToRelative {X Y S : Scheme} (f : X ⟶ Y) (s : Y ⟶ S) :
    cotangentSheaf (f ≫ s) ⟶ cotangentSheaf f :=
  differentialLift (relativeDifferentialOverComposite f s)

/- Source-only Phase 3 integration: cotangent_early. -/
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
set_option backward.isDefEq.respectTransparency false

namespace CotangentTransitivityRederivedV02

theorem relativeDerivation_ext {X S : Scheme} {s : X ⟶ S} {E : OModule X}
    (D D' : RelativeSheafDerivation s E)
    (h : ∀ U a, D.apply U a = D'.apply U a) : D = D' := by
  have hfun : D.apply = D'.apply := funext (fun U => funext (h U))
  cases D
  cases D'
  cases hfun
  rfl

theorem cotangentHom_ext {X S : Scheme} {s : X ⟶ S} {E : OModule X}
    (h k : cotangentSheaf s ⟶ E)
    (heq : ∀ U a,
      h.app U ((cotangentPresentation s).differential.apply U a) =
      k.app U ((cotangentPresentation s).differential.apply U a)) : h = k := by
  apply ((cotangentPresentation s).universal E).1
  apply relativeDerivation_ext
  exact heq

theorem cotangentMap_adjoint {X Y S : Scheme} (f : X ⟶ Y) (s : Y ⟶ S) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv
      (cotangentSheaf s) (cotangentSheaf (f ≫ s)) (cotangentMap f s) =
        differentialLift (pulledFunctionDifferential f s) := by
  exact ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv
    (cotangentSheaf s) (cotangentSheaf (f ≫ s))).apply_symm_apply
      (differentialLift (pulledFunctionDifferential f s))

theorem cotangentToRelative_differential {X Y S : Scheme}
    (f : X ⟶ Y) (s : Y ⟶ S) (U : X.Opens) (a : RingSections X U) :
    (cotangentToRelative f s).app U
      ((cotangentPresentation (f ≫ s)).differential.apply U a) =
        (cotangentPresentation f).differential.apply U a := by
  exact congrArg
    (fun D : RelativeSheafDerivation (f ≫ s) (cotangentSheaf f) => D.apply U a)
    (differentialLift_spec (relativeDifferentialOverComposite f s))

theorem cotangent_transitivity_zero {X Y S : Scheme}
    (f : X ⟶ Y) (s : Y ⟶ S) :
    cotangentMap f s ≫ cotangentToRelative f s = 0 := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv
    (cotangentSheaf s) (cotangentSheaf f)).injective
  rw [Adjunction.homEquiv_naturality_right, cotangentMap_adjoint,
    Adjunction.homAddEquiv_zero]
  apply cotangentHom_ext
  intro U a
  have hd := congrArg
    (fun D : RelativeSheafDerivation s
      ((Scheme.Modules.pushforward f).obj (cotangentSheaf (f ≫ s))) => D.apply U a)
    (differentialLift_spec (pulledFunctionDifferential f s))
  change (differentialLift (pulledFunctionDifferential f s)).app U
      ((cotangentPresentation s).differential.apply U a) =
    (cotangentPresentation (f ≫ s)).differential.apply (f ⁻¹ᵁ U) (f.app U a) at hd
  change (cotangentToRelative f s).app (f ⁻¹ᵁ U)
    ((differentialLift (pulledFunctionDifferential f s)).app U
      ((cotangentPresentation s).differential.apply U a)) = 0
  exact (congrArg ((cotangentToRelative f s).app (f ⁻¹ᵁ U)) hd).trans
    ((cotangentToRelative_differential f s (f ⁻¹ᵁ U) (f.app U a)).trans
      ((cotangentPresentation f).differential.killsBase U a))

theorem cotangentToRelative_epi {X Y S : Scheme}
    (f : X ⟶ Y) (s : Y ⟶ S) : Epi (cotangentToRelative f s) := by
  refine ⟨?_⟩
  intro E h k heq
  apply cotangentHom_ext
  intro U a
  have hv := congrArg
    (fun q : cotangentSheaf (f ≫ s) ⟶ E =>
      q.app U ((cotangentPresentation (f ≫ s)).differential.apply U a)) heq
  change h.app U ((cotangentToRelative f s).app U
      ((cotangentPresentation (f ≫ s)).differential.apply U a)) =
    k.app U ((cotangentToRelative f s).app U
      ((cotangentPresentation (f ≫ s)).differential.apply U a)) at hv
  simpa only [cotangentToRelative_differential] using hv

theorem kills_pulledFunction_of_comp_zero {X Y S : Scheme}
    (f : X ⟶ Y) (s : Y ⟶ S) {E : OModule X}
    (h : cotangentSheaf (f ≫ s) ⟶ E) (hh : cotangentMap f s ≫ h = 0)
    (U : Y.Opens) (a : RingSections Y U) :
    h.app (f ⁻¹ᵁ U)
      ((cotangentPresentation (f ≫ s)).differential.apply (f ⁻¹ᵁ U) (f.app U a)) = 0 := by
  have ha := congrArg
    ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv (cotangentSheaf s) E) hh
  rw [Adjunction.homEquiv_naturality_right, cotangentMap_adjoint,
    Adjunction.homAddEquiv_zero] at ha
  have hv := congrArg
    (fun q : cotangentSheaf s ⟶ (Scheme.Modules.pushforward f).obj E =>
      q.app U ((cotangentPresentation s).differential.apply U a)) ha
  change h.app (f ⁻¹ᵁ U)
    ((differentialLift (pulledFunctionDifferential f s)).app U
      ((cotangentPresentation s).differential.apply U a)) = 0 at hv
  have hd := congrArg
    (fun D : RelativeSheafDerivation s
      ((Scheme.Modules.pushforward f).obj (cotangentSheaf (f ≫ s))) => D.apply U a)
    (differentialLift_spec (pulledFunctionDifferential f s))
  change (differentialLift (pulledFunctionDifferential f s)).app U
      ((cotangentPresentation s).differential.apply U a) =
    (cotangentPresentation (f ≫ s)).differential.apply (f ⁻¹ᵁ U) (f.app U a) at hd
  exact (congrArg (h.app (f ⁻¹ᵁ U)) hd).symm.trans hv

def relativeDerivationOfCompZero {X Y S : Scheme}
    (f : X ⟶ Y) (s : Y ⟶ S) {E : OModule X}
    (h : cotangentSheaf (f ≫ s) ⟶ E) (hh : cotangentMap f s ≫ h = 0) :
    RelativeSheafDerivation f E where
  apply := ((cotangentPresentation (f ≫ s)).differential.postcompose h).apply
  zero := ((cotangentPresentation (f ≫ s)).differential.postcompose h).zero
  add := ((cotangentPresentation (f ≫ s)).differential.postcompose h).add
  leibniz := ((cotangentPresentation (f ≫ s)).differential.postcompose h).leibniz
  naturality := ((cotangentPresentation (f ≫ s)).differential.postcompose h).naturality
  killsBase := kills_pulledFunction_of_comp_zero f s h hh

def cotangentDesc {X Y S : Scheme}
    (f : X ⟶ Y) (s : Y ⟶ S) {E : OModule X}
    (h : cotangentSheaf (f ≫ s) ⟶ E) (hh : cotangentMap f s ≫ h = 0) :
    cotangentSheaf f ⟶ E :=
  differentialLift (relativeDerivationOfCompZero f s h hh)

theorem cotangentDesc_fac {X Y S : Scheme}
    (f : X ⟶ Y) (s : Y ⟶ S) {E : OModule X}
    (h : cotangentSheaf (f ≫ s) ⟶ E) (hh : cotangentMap f s ≫ h = 0) :
    cotangentToRelative f s ≫ cotangentDesc f s h hh = h := by
  apply cotangentHom_ext
  intro U a
  change (cotangentDesc f s h hh).app U
    ((cotangentToRelative f s).app U
      ((cotangentPresentation (f ≫ s)).differential.apply U a)) =
    h.app U ((cotangentPresentation (f ≫ s)).differential.apply U a)
  rw [cotangentToRelative_differential]
  exact congrArg (fun D : RelativeSheafDerivation f E => D.apply U a)
    (differentialLift_spec (relativeDerivationOfCompZero f s h hh))

def cotangentToRelative_isCokernel {X Y S : Scheme}
    (f : X ⟶ Y) (s : Y ⟶ S) :
    IsColimit (CokernelCofork.ofπ (cotangentToRelative f s)
      (cotangent_transitivity_zero f s)) := by
  letI : Epi (cotangentToRelative f s) := cotangentToRelative_epi f s
  refine CokernelCofork.IsColimit.ofπ' (cotangentToRelative f s)
    (cotangent_transitivity_zero f s) ?_
  intro E h hh
  exact ⟨cotangentDesc f s h hh, cotangentDesc_fac f s h hh⟩

end CotangentTransitivityRederivedV02
end


theorem cotangent_transitivity_zero {X Y S : Scheme}
    (f : X ⟶ Y) (s : Y ⟶ S) :
    cotangentMap f s ≫ cotangentToRelative f s = 0 := by
  exact LeBrunSalamon.PhaseThirty.CotangentTransitivityRederivedV02.cotangent_transitivity_zero (f := f) (s := s)

def cotangentTransitivityComplex {X Y S : Scheme}
    (f : X ⟶ Y) (s : Y ⟶ S) : ShortComplex (OModule X) :=
  ShortComplex.mk (cotangentMap f s) (cotangentToRelative f s)
    (cotangent_transitivity_zero f s)

/- Source-only Phase 3 integration: cotangent_exact. -/
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
set_option backward.isDefEq.respectTransparency false

namespace CotangentTransitivityRederivedV02

theorem cotangent_transitivity_exact {X Y S : Scheme}
    (f : X ⟶ Y) (s : Y ⟶ S) :
    (cotangentTransitivityComplex f s).Exact := by
  exact (cotangentTransitivityComplex f s).exact_of_g_is_cokernel
    (cotangentToRelative_isCokernel f s)

end CotangentTransitivityRederivedV02
end


theorem cotangent_transitivity_exact {X Y S : Scheme}
    (f : X ⟶ Y) (s : Y ⟶ S) :
    (cotangentTransitivityComplex f s).Exact := by
  exact LeBrunSalamon.PhaseThirty.CotangentTransitivityRederivedV02.cotangent_transitivity_exact (f := f) (s := s)

theorem cotangentToRelative_epi {X Y S : Scheme}
    (f : X ⟶ Y) (s : Y ⟶ S) : Epi (cotangentToRelative f s) := by
  exact LeBrunSalamon.PhaseThirty.CotangentTransitivityRederivedV02.cotangentToRelative_epi (f := f) (s := s)


section CotangentImmersionProofSection
set_option backward.isDefEq.respectTransparency false

namespace CotangentImmersionProof

/-- The canonical-map condition is the local differential formula after adjunction. -/
def CanonicalMap {X Y S : Scheme} (f : X ⟶ Y) (s : Y ⟶ S)
    (P : CotangentPresentation s) (Q : CotangentPresentation (f ≫ s))
    (q : pullbackModule f P.object ⟶ Q.object) : Prop :=
  ∀ (U : Y.Opens) (a : RingSections Y U),
    (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv
      P.object Q.object q).app U) (P.differential.apply U a) =
      Q.differential.apply (f ⁻¹ᵁ U) (f.app U a)

/-- A morphism with the canonical local differential formula is unique. -/
theorem canonicalMap_unique {X Y S : Scheme} (f : X ⟶ Y) (s : Y ⟶ S)
    (P : CotangentPresentation s) (Q : CotangentPresentation (f ≫ s))
    (q q' : pullbackModule f P.object ⟶ Q.object)
    (hq : CanonicalMap f s P Q q) (hq' : CanonicalMap f s P Q q') :
    q = q' := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv
    P.object Q.object).injective
  apply (P.universal ((Scheme.Modules.pushforward f).obj Q.object)).1
  apply CotangentTransitivityRederivedV02.relativeDerivation_ext
  intro U a
  exact (hq U a).trans (hq' U a).symm

/-- The project's definition has exactly the canonical local differential formula. -/
theorem cotangentMap_canonical {X Y S : Scheme}
    (f : X ⟶ Y) (s : Y ⟶ S) :
    CanonicalMap f s (cotangentPresentation s)
      (cotangentPresentation (f ≫ s)) (cotangentMap f s) := by
  intro U a
  rw [cotangentMap_adjoint]
  exact congrArg
    (fun D : RelativeSheafDerivation s
      ((Scheme.Modules.pushforward f).obj (cotangentSheaf (f ≫ s))) => D.apply U a)
    (differentialLift_spec (pulledFunctionDifferential f s))

/-- Exact published restriction theorem: universal differentials restrict along
an open immersion, with the local differential formula. Stacks Project
Lemma 29.33.3 (Tag 01US); the canonical-map characterization is
Lemma 29.33.8 (Tag 01UV). The inputs are arbitrary universal presentations,
not the project's chosen cotangent sheaves or chosen differential map. -/
theorem _root_.LeBrunSalamon.PublishedInputs.Differentials.openImmersionPresentation
    {X Y S : Scheme} (f : X ⟶ Y) [IsOpenImmersion f] (s : Y ⟶ S)
    (P : CotangentPresentation s) (Q : CotangentPresentation (f ≫ s)) :
    ∃ e : pullbackModule f P.object ≅ Q.object,
      CanonicalMap f s P Q e.hom := by
  sorry

/-- Exact published surjectivity part of the conormal sequence for an
immersion. Stacks Project Lemma 29.33.15 (Tag 01UZ), with its differential
specified by Lemma 29.33.8 (Tag 01UV). This has no smoothness, dimension,
kernel-rank, or chosen-project-map hypothesis or conclusion. -/
theorem _root_.LeBrunSalamon.PublishedInputs.Differentials.immersionPresentationSurjection
    {X Y S : Scheme} (f : X ⟶ Y) [IsImmersion f] (s : Y ⟶ S)
    (P : CotangentPresentation s) (Q : CotangentPresentation (f ≫ s)) :
    ∃ q : pullbackModule f P.object ⟶ Q.object,
      Epi q ∧ CanonicalMap f s P Q q := by
  sorry

/-- Generic finite locally free kernel/rank fact. Stacks Project,
Section 17.26 (Tag 0B37), states that finite locally free sheaves form
an exact category with surjections as admissible epimorphisms, and that
ranks add in short exact sequences. Here the two constant ranks are
d+c and d. This is a theorem about arbitrary sheaf morphisms; no
differential, immersion, or smooth morphism occurs in the statement. -/
theorem _root_.LeBrunSalamon.PublishedInputs.SheafFunctoriality.epi_kernel_locallyFreeOfRank
    {X : Scheme} {E F : OModule X} (q : E ⟶ F) [Epi q] (d c : ℕ)
    (hE : IsLocallyFreeOfRank E (d + c))
    (hF : IsLocallyFreeOfRank F d) :
    IsLocallyFreeOfRank (kernel q) c := by
  sorry


/-- The open-restriction input is used only through its actual compatible isomorphism. -/
theorem openImmersion_from_restriction {X Y S : Scheme}
    (f : X ⟶ Y) [IsOpenImmersion f] (s : Y ⟶ S)
    (hRestriction : ∃ e : pullbackModule f (cotangentSheaf s) ≅
        cotangentSheaf (f ≫ s),
      CanonicalMap f s (cotangentPresentation s)
        (cotangentPresentation (f ≫ s)) e.hom) :
    IsIso (cotangentMap f s) := by
  obtain ⟨e, he⟩ := hRestriction
  have h : cotangentMap f s = e.hom :=
    canonicalMap_unique f s _ _ _ _ (cotangentMap_canonical f s) he
  rw [h]
  infer_instance

/-- The immersion input yields an epimorphism of the actual chosen differential. -/
theorem cotangentMap_epi_from_surjection {X Y S : Scheme}
    (f : X ⟶ Y) (s : Y ⟶ S)
    (hSurjection : ∃ q : pullbackModule f (cotangentSheaf s) ⟶
        cotangentSheaf (f ≫ s),
      Epi q ∧ CanonicalMap f s (cotangentPresentation s)
        (cotangentPresentation (f ≫ s)) q) :
    Epi (cotangentMap f s) := by
  obtain ⟨q, hq, hcanonical⟩ := hSurjection
  have h : q = cotangentMap f s :=
    canonicalMap_unique f s _ _ _ _ hcanonical (cotangentMap_canonical f s)
  simpa only [h] using hq

/-- The rank calculation uses only a generic kernel theorem and the two existing rank facts. -/
theorem conormal_rank_from_inputs
    (kernelRank : ∀ {X : Scheme} {E F : OModule X}
      (q : E ⟶ F) [Epi q] (d c : ℕ),
      IsLocallyFreeOfRank E (d + c) →
      IsLocallyFreeOfRank F d →
      IsLocallyFreeOfRank (kernel q) c)
    {X Y S : Scheme} (f : X ⟶ Y) [IsClosedImmersion f] (s : Y ⟶ S)
    (d c : ℕ) (hY : SmoothOfRelativeDimension (d + c) s)
    (hX : SmoothOfRelativeDimension d (f ≫ s))
    (hSurjection : Epi (cotangentMap f s)) :
    IsLocallyFreeOfRank (kernel (cotangentMap f s)) c := by
  letI := hSurjection
  exact kernelRank (cotangentMap f s) d c
    (pullback_locallyFree f (smooth_cotangent_rank s (d + c) hY))
    (smooth_cotangent_rank (f ≫ s) d hX)


end CotangentImmersionProof
end CotangentImmersionProofSection

/-- The intrinsic derivative for an open immersion is an isomorphism. -/
theorem openImmersion_cotangentMap_isIso {X Y S : Scheme}
    (f : X ⟶ Y) [IsOpenImmersion f] (s : Y ⟶ S) :
    IsIso (cotangentMap f s) := by
  exact CotangentImmersionProof.openImmersion_from_restriction f s
    (LeBrunSalamon.PublishedInputs.Differentials.openImmersionPresentation
      f s (cotangentPresentation s) (cotangentPresentation (f ≫ s)))

/-- The kernel of the actual differential. For a regular closed immersion between smooth schemes this is
the usual conormal sheaf. For arbitrary immersions it must not be silently identified with I/I². -/
abbrev differentialConormal {X Y S : Scheme} (f : X ⟶ Y) (s : Y ⟶ S) :
    OModule X := kernel (cotangentMap f s)

abbrev differentialNormal {X Y S : Scheme} (f : X ⟶ Y) (s : Y ⟶ S) :
    OModule X := dualSheaf (differentialConormal f s)

/-- In the smooth closed-immersion setting the conormal has the
expected rank. Dimensions are stated as d and d+c, not Nat subtraction. -/
theorem smoothClosedImmersion_conormal_rank {X Y S : Scheme}
    (f : X ⟶ Y) [IsClosedImmersion f] (s : Y ⟶ S)
    (d c : ℕ) (hY : SmoothOfRelativeDimension (d + c) s)
    (hX : SmoothOfRelativeDimension d (f ≫ s)) :
    IsLocallyFreeOfRank (differentialConormal f s) c := by
  exact CotangentImmersionProof.conormal_rank_from_inputs
    LeBrunSalamon.PublishedInputs.SheafFunctoriality.epi_kernel_locallyFreeOfRank
    f s d c hY hX
    (CotangentImmersionProof.cotangentMap_epi_from_surjection f s
      (LeBrunSalamon.PublishedInputs.Differentials.immersionPresentationSurjection
        f s (cotangentPresentation s) (cotangentPresentation (f ≫ s))))

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix

namespace CotangentConsequenceProof

theorem smoothClosedImmersion_normal_rank {X Y S : Scheme}
    (f : X ⟶ Y) [IsClosedImmersion f] (s : Y ⟶ S)
    (d c : ℕ) (hY : SmoothOfRelativeDimension (d + c) s)
    (hX : SmoothOfRelativeDimension d (f ≫ s)) :
    IsLocallyFreeOfRank (differentialNormal f s) c := by
  exact dualSheaf_locallyFree (smoothClosedImmersion_conormal_rank f s d c hY hX)

end CotangentConsequenceProof

end

theorem smoothClosedImmersion_normal_rank {X Y S : Scheme}
    (f : X ⟶ Y) [IsClosedImmersion f] (s : Y ⟶ S)
    (d c : ℕ) (hY : SmoothOfRelativeDimension (d + c) s)
    (hX : SmoothOfRelativeDimension d (f ≫ s)) :
    IsLocallyFreeOfRank (differentialNormal f s) c := by
  exact LeBrunSalamon.PhaseThirty.CotangentConsequenceProof.smoothClosedImmersion_normal_rank (X := X) (Y := Y) (S := S) (f := f) (s := s) (d := d) (c := c) (hY := hY) (hX := hX)

/-- A dual form of df that does not require an arbitrary isomorphism between f*TY and Hom(f*ΩY,O_X). -/
def tangentMapRaw {X Y S : Scheme} (f : X ⟶ Y) (s : Y ⟶ S) :
    tangentSheaf (f ≫ s) ⟶
      internalHomSheaf (pullbackModule f (cotangentSheaf s)) (structureModule X) :=
  currySheaf
    (tensorMap (𝟙 (tangentSheaf (f ≫ s))) (cotangentMap f s) ≫
      (internalHomPresentation (cotangentSheaf (f ≫ s))
        (structureModule X)).evaluate)

/-- **Published primitive (characteristic-zero separability).** Debarre,
`Rational curves on algebraic varieties`, GAeL XVIII notes (2010, revised
14 November 2020), section 2.4, printed p.23, the paragraph immediately
after (2.1): for a nonconstant separable map P1_k -> X whose image is in the
smooth locus, the differential includes T_P1 in f* T_X.  Here the base is
`ℂ`, so the induced algebraic extension of curve function fields is separable.
This is the nonzero canonical cotangent differential form of that primitive,
not an existence assertion about an arbitrary map of the same sheaves.

The actual map is fixed by `pulledFunctionDifferential` and the proved
`cotangentMap_adjoint`: on local functions its adjoint is a |-> d(f# a).
The explicit pulled-local-section formula is also proved downstream as
`Skeleton.ContactDerivativeIsoProof.cotangentMap_differential`.
`ProjectiveLineOverC` is the binary polynomial Proj with a coefficient-spectrum
isomorphism; `RationalCurve` supplies the actual map over that base and its
nonconstancy.  See `audit/NONCONSTANT_DIFFERENTIAL_SOURCE_ELIGIBILITY.json`
for the expanded-hypothesis audit.  Mathematical source eligibility is
separate from current-graph native replay, which remains a required gate.
Primary source:
https://perso.imj-prg.fr/wp-content/uploads/debarre-pub/NotesGAEL.pdf -/
theorem _root_.LeBrunSalamon.PublishedInputs.ProjectiveLineGeometry.nonconstantCurveDifferential
    (P : ProjectiveLineOverC) {d : ℕ}
    (X : SmoothProperComplexVariety d) (f : RationalCurve P X) :
    cotangentMap f.map X.structureMap ≠ 0 := by
  sorry

/-- Project wrapper for nonvanishing of the differential. -/
theorem nonconstant_complexCurve_differential_ne_zero
    (P : ProjectiveLineOverC) {d : ℕ}
    (X : SmoothProperComplexVariety d) (f : RationalCurve P X) :
    cotangentMap f.map X.structureMap ≠ 0 :=
  LeBrunSalamon.PublishedInputs.ProjectiveLineGeometry.nonconstantCurveDifferential
    P X f

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix

namespace CotangentConsequenceProof

theorem cotangent_rank_preserved_on_open {X S : Scheme}
    (s : X ⟶ S) (d : ℕ) (hs : SmoothOfRelativeDimension d s)
    (U : X.Opens) :
    IsLocallyFreeOfRank (pullbackModule U.ι (cotangentSheaf s)) d := by
  exact pullback_locallyFree U.ι (smooth_cotangent_rank s d hs)

end CotangentConsequenceProof

end

/-- Pullback by a dominant morphism does not make a nonzero line bundle section vanish on a reduced
target; the target-rank hypothesis is supplied by the vector-bundle formulation in Phase 28. -/
theorem cotangent_rank_preserved_on_open {X S : Scheme}
    (s : X ⟶ S) (d : ℕ) (hs : SmoothOfRelativeDimension d s)
    (U : X.Opens) :
    IsLocallyFreeOfRank (pullbackModule U.ι (cotangentSheaf s)) d := by
  exact LeBrunSalamon.PhaseThirty.CotangentConsequenceProof.cotangent_rank_preserved_on_open (X := X) (S := S) (s := s) (d := d) (hs := hs) (U := U)

end LeBrunSalamon.PhaseThirty

/-!
# Phase 31 -- finite jets, point derivations, and order estimates

All quotients here are quotients of actual commutative rings. Distinct point interpolation uses Chinese
remainders on an AFFINE chart; it must not be misread as global jet generation for an ample line bundle.
-/

namespace LeBrunSalamon.PhaseThirtyOne

open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseFour
open LeBrunSalamon.PhaseNine LeBrunSalamon.PhaseEleven
open LeBrunSalamon.PhaseThirteen

variable {A : Type*} [CommRing A] [Algebra ℂ A]

abbrev AffineJetAlgebra (p : A →ₐ[ℂ] ℂ) (k : ℕ) :=
  A ⧸ ((affinePointIdeal p) ^ (k + 1))

def affineJet (p : A →ₐ[ℂ] ℂ) (k : ℕ) : A →+* AffineJetAlgebra p k :=
  Ideal.Quotient.mk ((affinePointIdeal p) ^ (k + 1))

def jetTruncation (p : A →ₐ[ℂ] ℂ) (i j : ℕ) (h : j ≤ i) :
    AffineJetAlgebra p i →+* AffineJetAlgebra p j :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1))

theorem jetTruncation_surjective (p : A →ₐ[ℂ] ℂ)
    (i j : ℕ) (h : j ≤ i) :
    Function.Surjective (jetTruncation p i j h) :=
  Ideal.Quotient.factor_surjective _

theorem jetTruncation_mk (p : A →ₐ[ℂ] ℂ)
    (i j : ℕ) (h : j ≤ i) (a : A) :
    jetTruncation p i j h (affineJet p i a) = affineJet p j a := rfl

theorem jetTruncation_comp (p : A →ₐ[ℂ] ℂ)
    (i j k : ℕ) (hij : j ≤ i) (hjk : k ≤ j) :
    (jetTruncation p j k hjk).comp (jetTruncation p i j hij) =
      jetTruncation p i k (le_trans hjk hij) :=
  Ideal.Quotient.factor_comp _ _

theorem affineJet_eq_iff (p : A →ₐ[ℂ] ℂ) (k : ℕ) (f g : A) :
    affineJet p k f = affineJet p k g ↔
      f - g ∈ (affinePointIdeal p) ^ (k + 1) :=
  Ideal.Quotient.eq

theorem affineJet_zero_iff (p : A →ₐ[ℂ] ℂ) (k : ℕ) (f : A) :
    affineJet p k f = 0 ↔ f ∈ (affinePointIdeal p) ^ (k + 1) :=
  Ideal.Quotient.eq_zero_iff_mem

theorem sameJet_implies_sameLowerJet (p : A →ₐ[ℂ] ℂ)
    (i j : ℕ) (h : j ≤ i) (f g : A)
    (hfg : affineJet p i f = affineJet p i g) :
    affineJet p j f = affineJet p j g :=
  congrArg (jetTruncation p i j h) hfg

/- Source-only Phase 3 integration: affine_crt_crt_kernels. -/
noncomputable section
set_option autoImplicit false
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseFour LeBrunSalamon.PhaseNine
open LeBrunSalamon.PhaseThirteen
variable {A : Type*} [CommRing A] [Algebra ℂ A]
set_option backward.isDefEq.respectTransparency false

namespace AffineCRTOrderProof

theorem distinctPointIdeals_comaximal (p q : A →ₐ[ℂ] ℂ) (hpq : p ≠ q) :
    affinePointIdeal p ⊔ affinePointIdeal q = ⊤ := by
  letI : (affinePointIdeal p).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective p.toRingHom (by
      intro c
      exact ⟨algebraMap ℂ A c, p.commutes c⟩)
  letI : (affinePointIdeal q).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective q.toRingHom (by
      intro c
      exact ⟨algebraMap ℂ A c, q.commutes c⟩)
  have hne : affinePointIdeal p ≠ affinePointIdeal q := by
    intro heq
    apply hpq
    apply AlgHom.ext
    intro a
    have hpz : a - algebraMap ℂ A (p a) ∈ affinePointIdeal p := by
      change p (a - algebraMap ℂ A (p a)) = 0
      simp only [map_sub, AlgHom.commutes, Algebra.algebraMap_self_apply, sub_self]
    have hqz : q (a - algebraMap ℂ A (p a)) = 0 := by
      change a - algebraMap ℂ A (p a) ∈ affinePointIdeal q
      rw [← heq]
      exact hpz
    have hqa : q a - p a = 0 := by
      simpa only [map_sub, AlgHom.commutes, Algebra.algebraMap_self_apply] using hqz
    exact (sub_eq_zero.mp hqa).symm
  exact (Ideal.isCoprime_of_isMaximal hne).sup_eq

theorem distinctPointPowers_comaximal (p q : A →ₐ[ℂ] ℂ)
    (hpq : p ≠ q) (i j : ℕ) :
    (affinePointIdeal p) ^ (i + 1) ⊔
      (affinePointIdeal q) ^ (j + 1) = ⊤ := by
  exact Ideal.pow_sup_pow_eq_top
    (LeBrunSalamon.PhaseThirtyOne.AffineCRTOrderProof.distinctPointIdeals_comaximal p q hpq)

end AffineCRTOrderProof
end


/-- Distinct C-valued algebra points have distinct maximal kernels. -/
theorem distinctPointIdeals_comaximal (p q : A →ₐ[ℂ] ℂ) (hpq : p ≠ q) :
    affinePointIdeal p ⊔ affinePointIdeal q = ⊤ := by
  exact LeBrunSalamon.PhaseThirtyOne.AffineCRTOrderProof.distinctPointIdeals_comaximal (p := p) (q := q) (hpq := hpq)

theorem distinctPointPowers_comaximal (p q : A →ₐ[ℂ] ℂ)
    (hpq : p ≠ q) (i j : ℕ) :
    (affinePointIdeal p) ^ (i + 1) ⊔
      (affinePointIdeal q) ^ (j + 1) = ⊤ := by
  exact LeBrunSalamon.PhaseThirtyOne.AffineCRTOrderProof.distinctPointPowers_comaximal (p := p) (q := q) (hpq := hpq) (i := i) (j := j)

def affineTwoPointJet (p q : A →ₐ[ℂ] ℂ) (i j : ℕ) :
    A → AffineJetAlgebra p i × AffineJetAlgebra q j :=
  fun f => (affineJet p i f, affineJet q j f)

/- Source-only Phase 3 integration: affine_crt_crt_quotients. -/
noncomputable section
set_option autoImplicit false
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseFour LeBrunSalamon.PhaseNine
open LeBrunSalamon.PhaseThirteen
variable {A : Type*} [CommRing A] [Algebra ℂ A]
set_option backward.isDefEq.respectTransparency false

namespace AffineCRTOrderProof

theorem affineTwoPointJet_surjective (p q : A →ₐ[ℂ] ℂ)
    (hpq : p ≠ q) (i j : ℕ) :
    Function.Surjective (affineTwoPointJet p q i j) := by
  let I : Ideal A := (affinePointIdeal p) ^ (i + 1)
  let J : Ideal A := (affinePointIdeal q) ^ (j + 1)
  have hcop : IsCoprime I J := Ideal.isCoprime_iff_sup_eq.mpr
    (LeBrunSalamon.PhaseThirtyOne.AffineCRTOrderProof.distinctPointPowers_comaximal p q hpq i j)
  intro z
  obtain ⟨x, hx⟩ := (Ideal.quotientInfEquivQuotientProd I J hcop).surjective z
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine ⟨a, ?_⟩
  apply Prod.ext
  · change Ideal.Quotient.mk I a = z.1
    simpa only [Ideal.quotientInfEquivQuotientProd_fst, Ideal.Quotient.factor_mk] using
      congrArg Prod.fst hx
  · change Ideal.Quotient.mk J a = z.2
    simpa only [Ideal.quotientInfEquivQuotientProd_snd, Ideal.Quotient.factor_mk] using
      congrArg Prod.snd hx

theorem affineFinitePointJets_surjective {m : ℕ}
    (p : Fin m → A →ₐ[ℂ] ℂ) (hp : Function.Injective p)
    (k : Fin m → ℕ) :
    Function.Surjective
      (fun f : A => fun i : Fin m => affineJet (p i) (k i) f) := by
  let I : Fin m → Ideal A := fun i => (affinePointIdeal (p i)) ^ (k i + 1)
  have hI : Pairwise (fun i j => IsCoprime (I i) (I j)) := by
    intro i j hij
    exact Ideal.isCoprime_iff_sup_eq.mpr
      (LeBrunSalamon.PhaseThirtyOne.AffineCRTOrderProof.distinctPointPowers_comaximal
        (p i) (p j) (fun h => hij (hp h)) (k i) (k j))
  intro z
  obtain ⟨f, hf⟩ := Ideal.pi_quotient_surjective (I := I) hI z
  refine ⟨f, ?_⟩
  funext i
  change Ideal.Quotient.mk (I i) f = z i
  exact hf i

end AffineCRTOrderProof
end


theorem affineTwoPointJet_surjective (p q : A →ₐ[ℂ] ℂ)
    (hpq : p ≠ q) (i j : ℕ) :
    Function.Surjective (affineTwoPointJet p q i j) := by
  exact LeBrunSalamon.PhaseThirtyOne.AffineCRTOrderProof.affineTwoPointJet_surjective (p := p) (q := q) (hpq := hpq) (i := i) (j := j)

/-- This is an affine Chinese-remainder result, NOT a theorem about
H^0 of a line bundle on a proper variety. -/
theorem affineFinitePointJets_surjective {m : ℕ}
    (p : Fin m → A →ₐ[ℂ] ℂ) (hp : Function.Injective p)
    (k : Fin m → ℕ) :
    Function.Surjective
      (fun f : A => fun i : Fin m => affineJet (p i) (k i) f) := by
  exact LeBrunSalamon.PhaseThirtyOne.AffineCRTOrderProof.affineFinitePointJets_surjective (p := p) (hp := hp) (k := k)

/- Source-only Phase 3 integration: affine_point_derivation. -/
noncomputable section
set_option autoImplicit false
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseFour LeBrunSalamon.PhaseNine
open LeBrunSalamon.PhaseEleven LeBrunSalamon.PhaseThirteen
variable {A : Type*} [CommRing A] [Algebra ℂ A]

namespace AffinePointDerivationProof

theorem pointDerivation_vanishes_square (p : A →ₐ[ℂ] ℂ)
    (D : AffineTangentAt A p) (a : A)
    (ha : a ∈ (affinePointIdeal p) ^ 2) : D.val a = 0 := by
  rw [pow_two] at ha
  refine Submodule.mul_induction_on ha ?_ ?_
  · intro b hb c hc
    have hb0 : p b = 0 := hb
    have hc0 : p c = 0 := hc
    rw [D.property b c, hb0, hc0, zero_mul, zero_mul, zero_add]
  · intro b c hb hc
    simp only [map_add, hb, hc, zero_add]

def centeredFirstJet (p : A →ₐ[ℂ] ℂ) :
    A →ₗ[ℂ] affineFirstJetAlgebra p :=
  (Ideal.Quotient.mkₐ ℂ ((affinePointIdeal p) ^ 2)).toLinearMap -
    (Algebra.linearMap ℂ (affineFirstJetAlgebra p)).comp p.toLinearMap

theorem centeredFirstJet_apply (p : A →ₐ[ℂ] ℂ) (a : A) :
    centeredFirstJet p a = affineFirstJet p a -
      algebraMap ℂ (affineFirstJetAlgebra p) (p a) := rfl

theorem centeredFirstJet_mul (p : A →ₐ[ℂ] ℂ) (a b : A) :
    centeredFirstJet p (a * b) =
      p a • centeredFirstJet p b + p b • centeredFirstJet p a := by
  let q : A →ₐ[ℂ] affineFirstJetAlgebra p :=
    Ideal.Quotient.mkₐ ℂ ((affinePointIdeal p) ^ 2)
  have ha : a - algebraMap ℂ A (p a) ∈ affinePointIdeal p := by
    change p (a - algebraMap ℂ A (p a)) = 0
    simp only [map_sub, p.commutes, Algebra.algebraMap_self_apply, sub_self]
  have hb : b - algebraMap ℂ A (p b) ∈ affinePointIdeal p := by
    change p (b - algebraMap ℂ A (p b)) = 0
    simp only [map_sub, p.commutes, Algebra.algebraMap_self_apply, sub_self]
  have hprod : q ((a - algebraMap ℂ A (p a)) *
      (b - algebraMap ℂ A (p b))) = 0 := by
    change Ideal.Quotient.mk ((affinePointIdeal p) ^ 2)
      ((a - algebraMap ℂ A (p a)) * (b - algebraMap ℂ A (p b))) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [pow_two]
    exact Ideal.mul_mem_mul ha hb
  have hcenter :
      (q a - algebraMap ℂ (affineFirstJetAlgebra p) (p a)) *
        (q b - algebraMap ℂ (affineFirstJetAlgebra p) (p b)) = 0 := by
    simpa only [map_mul, map_sub, q.commutes] using hprod
  change q (a * b) - algebraMap ℂ (affineFirstJetAlgebra p) (p (a * b)) =
    p a • (q b - algebraMap ℂ (affineFirstJetAlgebra p) (p b)) +
      p b • (q a - algebraMap ℂ (affineFirstJetAlgebra p) (p a))
  simp only [map_mul, Algebra.smul_def]
  linear_combination hcenter

def pointDerivationOfFunctional (p : A →ₐ[ℂ] ℂ)
    (φ : affineFirstJetAlgebra p →ₗ[ℂ] ℂ) : AffineTangentAt A p :=
  ⟨φ.comp (centeredFirstJet p), by
    intro a b
    change φ (centeredFirstJet p (a * b)) =
      p a * φ (centeredFirstJet p b) + p b * φ (centeredFirstJet p a)
    rw [centeredFirstJet_mul]
    simp only [map_add, map_smul, smul_eq_mul]⟩

theorem allPointDerivations_detect_firstJet
    (p : A →ₐ[ℂ] ℂ) (f g : A) :
    SameAffineFirstJet p f g ↔
      p f = p g ∧ ∀ D : AffineTangentAt A p, D.val f = D.val g := by
  constructor
  · intro hfg
    refine ⟨?_, ?_⟩
    · have hmem : f - g ∈ affinePointIdeal p :=
        (Ideal.pow_le_self (I := affinePointIdeal p) (by decide : (2 : ℕ) ≠ 0)) hfg
      exact (RingHom.sub_mem_ker_iff p.toRingHom).mp hmem
    · intro D
      have h := pointDerivation_vanishes_square p D (f - g) hfg
      simpa only [map_sub, sub_eq_zero] using h
  · rintro ⟨hvalue, hder⟩
    by_contra hfg
    have hjet : affineFirstJet p (f - g) ≠ 0 := by
      intro hzero
      apply hfg
      change Ideal.Quotient.mk ((affinePointIdeal p) ^ 2) (f - g) = 0 at hzero
      exact Ideal.Quotient.eq_zero_iff_mem.mp hzero
    obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one ℂ hjet
    let D : AffineTangentAt A p := pointDerivationOfFunctional p φ
    have hzero : φ (centeredFirstJet p (f - g)) = 0 := by
      change D.val (f - g) = 0
      rw [map_sub, hder D, sub_self]
    rw [centeredFirstJet_apply] at hzero
    simp only [map_sub, hvalue, sub_self, map_zero, sub_zero] at hzero
    exact zero_ne_one (hzero.symm.trans hφ)

theorem pointDerivation_map_one (p : A →ₐ[ℂ] ℂ)
    (D : AffineTangentAt A p) : D.val 1 = 0 := by
  have h := D.property 1 1
  simp only [one_mul, map_one] at h
  exact add_eq_left.mp h.symm

theorem regularVectorFields_lift_pointDerivations
    [Module.Finite A (KaehlerDifferential ℂ A)]
    [Module.Projective A (KaehlerDifferential ℂ A)]
    (p : A →ₐ[ℂ] ℂ) (D : AffineTangentAt A p) :
    ∃ V : AffineVectorFields A, ∀ a : A, p (V a) = D.val a := by
  letI : Algebra A ℂ := p.toRingHom.toAlgebra
  letI : IsScalarTower ℂ A ℂ := IsScalarTower.of_algHom p
  let δ : Derivation ℂ A ℂ :=
    { toLinearMap := D.val
      map_one_eq_zero' := pointDerivation_map_one p D
      leibniz' := fun a b => by
        change D.val (a * b) = p a * D.val b + p b * D.val a
        exact D.property a b }
  have hp : Function.Surjective (Algebra.linearMap A ℂ) := by
    intro c
    refine ⟨algebraMap ℂ A c, ?_⟩
    change p (algebraMap ℂ A c) = c
    simpa only [Algebra.algebraMap_self_apply] using p.commutes c
  obtain ⟨L, hL⟩ := Module.projective_lifting_property
    (Algebra.linearMap A ℂ) δ.liftKaehlerDifferential hp
  refine ⟨KaehlerDifferential.linearMapEquivDerivation ℂ A L, ?_⟩
  intro a
  change p (L (KaehlerDifferential.D ℂ A a)) = D.val a
  have h := LinearMap.congr_fun hL (KaehlerDifferential.D ℂ A a)
  change p (L (KaehlerDifferential.D ℂ A a)) =
    δ.liftKaehlerDifferential (KaehlerDifferential.D ℂ A a) at h
  exact h.trans (δ.liftKaehlerDifferential_comp_D a)

def evaluatedVectorField (p : A →ₐ[ℂ] ℂ) (V : AffineVectorFields A) :
    AffineTangentAt A p :=
  ⟨p.toLinearMap.comp V.toLinearMap, by
    intro a b
    change p (V (a * b)) = p a * p (V b) + p b * p (V a)
    rw [Derivation.leibniz]
    simp only [smul_eq_mul, map_add, map_mul]⟩

theorem regularVectorFields_detect_firstJet
    [Module.Finite A (KaehlerDifferential ℂ A)]
    [Module.Projective A (KaehlerDifferential ℂ A)]
    (p : A →ₐ[ℂ] ℂ) (f g : A) :
    SameAffineFirstJet p f g ↔
      p f = p g ∧ ∀ V : AffineVectorFields A, p (V f) = p (V g) := by
  constructor
  · intro hfg
    obtain ⟨hvalue, hder⟩ := (allPointDerivations_detect_firstJet p f g).mp hfg
    refine ⟨hvalue, ?_⟩
    intro V
    exact hder (evaluatedVectorField p V)
  · rintro ⟨hvalue, hfields⟩
    apply (allPointDerivations_detect_firstJet p f g).mpr
    refine ⟨hvalue, ?_⟩
    intro D
    obtain ⟨V, hV⟩ := regularVectorFields_lift_pointDerivations p D
    rw [← hV f, ← hV g]
    exact hfields V

end AffinePointDerivationProof
end


/-- All point derivations, unlike only evaluations of global vector
fields, separate m/m² without a smoothness assumption. -/
theorem allPointDerivations_detect_firstJet
    (p : A →ₐ[ℂ] ℂ) (f g : A) :
    SameAffineFirstJet p f g ↔
      p f = p g ∧ ∀ D : AffineTangentAt A p, D.val f = D.val g := by
  exact LeBrunSalamon.PhaseThirtyOne.AffinePointDerivationProof.allPointDerivations_detect_firstJet (p := p) (f := f) (g := g)

/-- Finite projectivity of Ω is the needed duality/lifting hypothesis
when replacing arbitrary point derivations by regular vector fields. -/
theorem regularVectorFields_lift_pointDerivations
    [Module.Finite A (KaehlerDifferential ℂ A)]
    [Module.Projective A (KaehlerDifferential ℂ A)]
    (p : A →ₐ[ℂ] ℂ) (D : AffineTangentAt A p) :
    ∃ V : AffineVectorFields A, ∀ a : A, p (V a) = D.val a := by
  exact LeBrunSalamon.PhaseThirtyOne.AffinePointDerivationProof.regularVectorFields_lift_pointDerivations (p := p) (D := D)

theorem regularVectorFields_detect_firstJet
    [Module.Finite A (KaehlerDifferential ℂ A)]
    [Module.Projective A (KaehlerDifferential ℂ A)]
    (p : A →ₐ[ℂ] ℂ) (f g : A) :
    SameAffineFirstJet p f g ↔
      p f = p g ∧ ∀ V : AffineVectorFields A, p (V f) = p (V g) := by
  exact LeBrunSalamon.PhaseThirtyOne.AffinePointDerivationProof.regularVectorFields_detect_firstJet (p := p) (f := f) (g := g)

/- Source-only Phase 3 integration: affine_crt_ideal_orders. -/
noncomputable section
set_option autoImplicit false
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseFour LeBrunSalamon.PhaseNine
open LeBrunSalamon.PhaseThirteen
variable {A : Type*} [CommRing A] [Algebra ℂ A]
set_option backward.isDefEq.respectTransparency false

namespace AffineCRTOrderProof

theorem derivation_lowers_idealPower (I : Ideal A)
    (D : AffineVectorFields A) (k : ℕ) (a : A) (ha : a ∈ I ^ (k + 1)) :
    D a ∈ I ^ k := by
  induction k generalizing a with
  | zero => simp
  | succ k ih =>
    have ha' : a ∈ I ^ (k + 1) * I := by
      simpa only [pow_succ] using ha
    refine Submodule.mul_induction_on ha' ?_ ?_
    · intro b hb c hc
      simp only [Derivation.leibniz, smul_eq_mul]
      refine (I ^ (k + 1)).add_mem ((I ^ (k + 1)).mul_mem_right (D c) hb) ?_
      simpa only [pow_succ'] using Ideal.mul_mem_mul hc (ih b hb)
    · intro b c hb hc
      rw [map_add]
      exact (I ^ (k + 1)).add_mem hb hc

theorem derivation_preservesStableIdealPower (I : Ideal A)
    (D : AffineVectorFields A) (hI : ∀ a ∈ I, D a ∈ I)
    (k : ℕ) (a : A) (ha : a ∈ I ^ k) : D a ∈ I ^ k := by
  induction k generalizing a with
  | zero => simp
  | succ k ih =>
    rw [pow_succ] at ha ⊢
    refine Submodule.mul_induction_on ha ?_ ?_
    · intro b hb c hc
      simp only [Derivation.leibniz, smul_eq_mul]
      exact (I ^ k * I).add_mem
        (Ideal.mul_mem_mul hb (hI c hc))
        (Ideal.mul_mem_mul_rev (ih b hb) hc)
    · intro b c hb hc
      rw [map_add]
      exact (I ^ k * I).add_mem hb hc

theorem product_adds_pointOrder (p : A →ₐ[ℂ] ℂ)
    (r s : ℕ) (f g : A)
    (hf : f ∈ (affinePointIdeal p) ^ r)
    (hg : g ∈ (affinePointIdeal p) ^ s) :
    f * g ∈ (affinePointIdeal p) ^ (r + s) := by
  simpa only [pow_add] using Ideal.mul_mem_mul hf hg

theorem unit_preserves_pointOrder (p : A →ₐ[ℂ] ℂ)
    (k : ℕ) (u : Aˣ) (f : A) :
    (u : A) * f ∈ (affinePointIdeal p) ^ k ↔
      f ∈ (affinePointIdeal p) ^ k := by
  constructor
  · intro h
    simpa only [Units.inv_mul_cancel_left] using
      ((affinePointIdeal p) ^ k).mul_mem_left (↑u⁻¹ : A) h
  · intro h
    exact ((affinePointIdeal p) ^ k).mul_mem_left (u : A) h

end AffineCRTOrderProof
end


/-- A derivation lowers ideal-adic order by at most one. No invariance
of the ideal under the derivation is assumed. -/
theorem derivation_lowers_idealPower (I : Ideal A)
    (D : AffineVectorFields A) (k : ℕ) (a : A) (ha : a ∈ I ^ (k + 1)) :
    D a ∈ I ^ k := by
  exact LeBrunSalamon.PhaseThirtyOne.AffineCRTOrderProof.derivation_lowers_idealPower (I := I) (D := D) (k := k) (a := a) (ha := ha)

theorem derivation_preservesStableIdealPower (I : Ideal A)
    (D : AffineVectorFields A) (hI : ∀ a ∈ I, D a ∈ I)
    (k : ℕ) (a : A) (ha : a ∈ I ^ k) : D a ∈ I ^ k := by
  exact LeBrunSalamon.PhaseThirtyOne.AffineCRTOrderProof.derivation_preservesStableIdealPower (I := I) (D := D) (hI := hI) (k := k) (a := a) (ha := ha)

theorem product_adds_pointOrder (p : A →ₐ[ℂ] ℂ)
    (r s : ℕ) (f g : A)
    (hf : f ∈ (affinePointIdeal p) ^ r)
    (hg : g ∈ (affinePointIdeal p) ^ s) :
    f * g ∈ (affinePointIdeal p) ^ (r + s) := by
  exact LeBrunSalamon.PhaseThirtyOne.AffineCRTOrderProof.product_adds_pointOrder (p := p) (r := r) (s := s) (f := f) (g := g) (hf := hf) (hg := hg)

/-- Multiplying a local frame by a unit does not change order. -/
theorem unit_preserves_pointOrder (p : A →ₐ[ℂ] ℂ)
    (k : ℕ) (u : Aˣ) (f : A) :
    (u : A) * f ∈ (affinePointIdeal p) ^ k ↔
      f ∈ (affinePointIdeal p) ^ k := by
  exact LeBrunSalamon.PhaseThirtyOne.AffineCRTOrderProof.unit_preserves_pointOrder (p := p) (k := k) (u := u) (f := f)

/- Source-only Phase 3 integration: affine_hamiltonian_order_followups_2. -/
noncomputable section
set_option autoImplicit false
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseFour LeBrunSalamon.PhaseNine
variable {A : Type*} [CommRing A] [Algebra ℂ A]
open LeBrunSalamon.PhaseEleven
open LeBrunSalamon.PhaseThirteen LeBrunSalamon.PhaseThirteen.HamiltonianOrderProof

namespace HamiltonianOrderProof

theorem contactJacobi_value_depends_on_firstJets_proved
    (θ : AffineOneForm A) (hθ : IsAffineContactForm θ)
    (p : A →ₐ[ℂ] ℂ) (f f' g g' : A)
    (hf : SameAffineFirstJet p f f') (hg : SameAffineFirstJet p g g') :
    p (contactJacobiBracket θ hθ f g) =
      p (contactJacobiBracket θ hθ f' g') := by
  rw [jacobi_action, jacobi_action, map_sub, map_sub, map_mul, map_mul,
    contactHamiltonianField_depends_on_firstJet_proved θ hθ p f f' hf g,
    AffineFirstJetProofCandidate.sameAffineFirstJet_same_derivatives_proved p g g' hg
      (affineContactHamiltonianField θ hθ f'),
    AffineFirstJetProofCandidate.sameAffineFirstJet_same_value_proved p g g' hg,
    AffineFirstJetProofCandidate.sameAffineFirstJet_same_derivatives_proved p f f' hf
      (reebFromContactHamiltonian θ hθ)]

theorem contactHamiltonian_lowers_order_proved
    [Module.Finite A (KaehlerDifferential ℂ A)]
    [Module.Projective A (KaehlerDifferential ℂ A)]
    (θ : AffineOneForm A) (hθ : IsAffineContactForm θ)
    (p : A →ₐ[ℂ] ℂ) (k : ℕ) (f : A)
    (hf : f ∈ (affinePointIdeal p) ^ (k + 1)) (a : A) :
    affineContactHamiltonianField θ hθ f a ∈
      (affinePointIdeal p) ^ k := by
  exact field_ideal_order θ hθ (affinePointIdeal p) k f hf a

theorem derivation_image_order (I : Ideal A) (D : AffineVectorFields A)
    (r : ℕ) (hD : ∀ a : A, D a ∈ I ^ r)
    (s : ℕ) (f : A) (hf : f ∈ I ^ (s + 1)) : D f ∈ I ^ (r + s) := by
  induction s generalizing f with
  | zero => simpa only [Nat.add_zero] using hD f
  | succ s ih =>
    have hf' : f ∈ I ^ (s + 1) * I := by simpa only [pow_succ] using hf
    refine Submodule.mul_induction_on hf' ?_ ?_
    · intro b hb c hc
      rw [Derivation.leibniz]
      simp only [smul_eq_mul]
      apply (I ^ (r + (s + 1))).add_mem
      · have h : b * D c ∈ I ^ ((s + 1) + r) := by
          simpa only [pow_add] using Ideal.mul_mem_mul hb (hD c)
        simpa only [Nat.add_comm] using h
      · have h : c * D b ∈ I ^ ((r + s) + 1) := by
          simpa only [pow_succ'] using Ideal.mul_mem_mul hc (ih b hb)
        simpa only [Nat.add_assoc] using h
    · intro b c hb hc
      rw [map_add]
      exact (I ^ (r + (s + 1))).add_mem hb hc

theorem contactJacobi_order_bound_proved
    [Module.Finite A (KaehlerDifferential ℂ A)]
    [Module.Projective A (KaehlerDifferential ℂ A)]
    (θ : AffineOneForm A) (hθ : IsAffineContactForm θ)
    (p : A →ₐ[ℂ] ℂ) (r s : ℕ) (f g : A)
    (hf : f ∈ (affinePointIdeal p) ^ (r + 1))
    (hg : g ∈ (affinePointIdeal p) ^ (s + 1)) :
    contactJacobiBracket θ hθ f g ∈
      (affinePointIdeal p) ^ (r + s) := by
  let I := affinePointIdeal p
  have hX : affineContactHamiltonianField θ hθ f g ∈ I ^ (r + s) :=
    derivation_image_order I (affineContactHamiltonianField θ hθ f) r
      (fun a => field_ideal_order θ hθ I r f hf a) s g hg
  have hR : reebFromContactHamiltonian θ hθ f ∈ I ^ r :=
    AffineCRTOrderProof.derivation_lowers_idealPower I (reebFromContactHamiltonian θ hθ) r f hf
  have hgs : g ∈ I ^ s := Ideal.pow_le_pow_right (Nat.le_succ s) hg
  have hprod : g * reebFromContactHamiltonian θ hθ f ∈ I ^ (r + s) := by
    have h : g * reebFromContactHamiltonian θ hθ f ∈ I ^ (s + r) := by
      simpa only [pow_add] using Ideal.mul_mem_mul hgs hR
    simpa only [Nat.add_comm] using h
  rw [jacobi_action]
  exact (I ^ (r + s)).sub_mem hX hprod

theorem squareIdeal_closedUnderContactJacobi_proved
    [Module.Finite A (KaehlerDifferential ℂ A)]
    [Module.Projective A (KaehlerDifferential ℂ A)]
    (θ : AffineOneForm A) (hθ : IsAffineContactForm θ)
    (p : A →ₐ[ℂ] ℂ) (f g : A)
    (hf : f ∈ (affinePointIdeal p) ^ 2)
    (hg : g ∈ (affinePointIdeal p) ^ 2) :
    contactJacobiBracket θ hθ f g ∈ (affinePointIdeal p) ^ 2 := by
  exact contactJacobi_order_bound_proved θ hθ p 1 1 f g hf hg

end HamiltonianOrderProof
end


/-- Values of contact brackets depend on the two first jets; the
FIRST JET of the bracket generally also requires second jets. -/
theorem contactJacobi_value_depends_on_firstJets
    (θ : AffineOneForm A) (hθ : IsAffineContactForm θ)
    (p : A →ₐ[ℂ] ℂ) (f f' g g' : A)
    (hf : SameAffineFirstJet p f f') (hg : SameAffineFirstJet p g g') :
    p (contactJacobiBracket θ hθ f g) =
      p (contactJacobiBracket θ hθ f' g') := by
  exact LeBrunSalamon.PhaseThirtyOne.HamiltonianOrderProof.contactJacobi_value_depends_on_firstJets_proved (θ := θ) (hθ := hθ) (p := p) (f := f) (f' := f') (g := g) (g' := g') (hf := hf) (hg := hg)

/-- These order estimates are stated on finite-projective cotangent
charts, as needed for the global smooth-variety application. -/
theorem contactHamiltonian_lowers_order
    [Module.Finite A (KaehlerDifferential ℂ A)]
    [Module.Projective A (KaehlerDifferential ℂ A)]
    (θ : AffineOneForm A) (hθ : IsAffineContactForm θ)
    (p : A →ₐ[ℂ] ℂ) (k : ℕ) (f : A)
    (hf : f ∈ (affinePointIdeal p) ^ (k + 1)) (a : A) :
    affineContactHamiltonianField θ hθ f a ∈
      (affinePointIdeal p) ^ k := by
  exact LeBrunSalamon.PhaseThirtyOne.HamiltonianOrderProof.contactHamiltonian_lowers_order_proved (θ := θ) (hθ := hθ) (p := p) (k := k) (f := f) (hf := hf) (a := a)

theorem contactJacobi_order_bound
    [Module.Finite A (KaehlerDifferential ℂ A)]
    [Module.Projective A (KaehlerDifferential ℂ A)]
    (θ : AffineOneForm A) (hθ : IsAffineContactForm θ)
    (p : A →ₐ[ℂ] ℂ) (r s : ℕ) (f g : A)
    (hf : f ∈ (affinePointIdeal p) ^ (r + 1))
    (hg : g ∈ (affinePointIdeal p) ^ (s + 1)) :
    contactJacobiBracket θ hθ f g ∈
      (affinePointIdeal p) ^ (r + s) := by
  exact LeBrunSalamon.PhaseThirtyOne.HamiltonianOrderProof.contactJacobi_order_bound_proved (θ := θ) (hθ := hθ) (p := p) (r := r) (s := s) (f := f) (g := g) (hf := hf) (hg := hg)

theorem squareIdeal_closedUnderContactJacobi
    [Module.Finite A (KaehlerDifferential ℂ A)]
    [Module.Projective A (KaehlerDifferential ℂ A)]
    (θ : AffineOneForm A) (hθ : IsAffineContactForm θ)
    (p : A →ₐ[ℂ] ℂ) (f g : A)
    (hf : f ∈ (affinePointIdeal p) ^ 2)
    (hg : g ∈ (affinePointIdeal p) ^ 2) :
    contactJacobiBracket θ hθ f g ∈ (affinePointIdeal p) ^ 2 := by
  exact LeBrunSalamon.PhaseThirtyOne.HamiltonianOrderProof.squareIdeal_closedUnderContactJacobi_proved (θ := θ) (hθ := hθ) (p := p) (f := f) (g := g) (hf := hf) (hg := hg)

end LeBrunSalamon.PhaseThirtyOne

/-!
# Projective-line geometry: actual affine charts, overlaps, and point ideals

The following constructions refer to the original Proj scheme. The Laurent
complex calculations are separate from the remaining O(d) sheaf comparison.
-/

namespace LeBrunSalamon.Skeleton

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseSeven

/-- Constants in the degree-zero ring of the standard grading, with their actual ring laws. -/
def constantsToDegreeZero (N : ℕ) :
    ℂ →+* ↥(MvPolynomial.homogeneousSubmodule (Fin (N+1)) ℂ 0) where
  toFun c := ⟨MvPolynomial.C c, MvPolynomial.isHomogeneous_C (Fin (N+1)) c⟩
  map_zero' := by apply Subtype.ext; simp
  map_one' := by apply Subtype.ext; simp
  map_add' := by intro a b; apply Subtype.ext; simp
  map_mul' := by intro a b; apply Subtype.ext; simp

def projectiveBaseMap (N : ℕ) : ComplexProjectiveSpace N ⟶ ComplexBase :=
  Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin (N+1)) ℂ) ≫
    Spec.map (CommRingCat.ofHom (constantsToDegreeZero N))

/-- Degree-zero homogeneous polynomials are exactly the constants. -/
theorem constantsToDegreeZero_bijective (N : ℕ) :
    Function.Bijective (constantsToDegreeZero N) := by
  constructor
  · intro a b h
    apply MvPolynomial.C_injective (σ := Fin (N + 1))
    exact congrArg Subtype.val h
  · intro p
    refine ⟨p.val.coeff 0, ?_⟩
    apply Subtype.ext
    change MvPolynomial.C (p.val.coeff 0) = p.val
    have hp : MvPolynomial.IsHomogeneous p.val 0 := p.property
    have ht : p.val.totalDegree = 0 :=
      (MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin (N + 1))).mpr hp
    exact (MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp ht).symm

def degreeZeroEquiv (N : ℕ) :=
  RingEquiv.ofBijective (constantsToDegreeZero N) (constantsToDegreeZero_bijective N)

/-- The specified coefficient isomorphism, not an arbitrary field automorphism. -/
def zeroDegreeSchemeIso (N : ℕ) : ProjectiveDegreeZeroSpectrum N ≅ ComplexBase where
  hom := Spec.map (CommRingCat.ofHom (constantsToDegreeZero N))
  inv := Spec.map (CommRingCat.ofHom (degreeZeroEquiv N).symm.toRingHom)
  hom_inv_id := by
    rw [← Spec.map_comp]
    convert Spec.map_id (CommRingCat.of
      ↥(MvPolynomial.homogeneousSubmodule (Fin (N+1)) ℂ 0)) using 1
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact (degreeZeroEquiv N).apply_symm_apply a
  inv_hom_id := by
    rw [← Spec.map_comp]
    convert Spec.map_id (CommRingCat.of ℂ) using 1
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact (degreeZeroEquiv N).symm_apply_apply a

/-- Canonical source for the final project root. -/
def canonicalProjectiveLine : ProjectiveLineOverC := ⟨zeroDegreeSchemeIso 1⟩

theorem canonicalProjectiveLine_structureMap :
    canonicalProjectiveLine.structureMap = projectiveBaseMap 1 := rfl

end LeBrunSalamon.Skeleton

namespace LeBrunSalamon.P1Charts

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators LaurentPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

/-! ## Core -/

abbrev Binary := MvPolynomial (Fin 2) ℂ
abbrev grading := MvPolynomial.homogeneousSubmodule (Fin 2) ℂ
abbrev lineScheme : Scheme := Proj grading

theorem variable_degree (i : Fin 2) : (MvPolynomial.X i : Binary) ∈ grading 1 :=
  MvPolynomial.isHomogeneous_X _ _

theorem irrelevant_le_variableSpan :
    (HomogeneousIdeal.irrelevant grading).toIdeal ≤
      Ideal.span (Set.range (MvPolynomial.X : Fin 2 → Binary)) := by
  apply (HomogeneousIdeal.toIdeal_irrelevant_le grading).mpr
  intro n hn p hp
  change p ∈ MvPolynomial.idealOfVars (Fin 2) ℂ
  rw [← pow_one (MvPolynomial.idealOfVars (Fin 2) ℂ),
    MvPolynomial.mem_pow_idealOfVars_iff]
  intro d hd
  have hdeg := hp (MvPolynomial.mem_support_iff.mp hd)
  have hd' : d.degree = n := by
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hdeg
  omega

def chartOpen (i : Fin 2) : lineScheme.Opens :=
  Proj.basicOpen grading (MvPolynomial.X i)

abbrev ChartRing (i : Fin 2) :=
  HomogeneousLocalization.Away grading (MvPolynomial.X i : Binary)

def chartIso (i : Fin 2) :
    (chartOpen i).toScheme ≅ Spec (CommRingCat.of (ChartRing i)) :=
  Proj.basicOpenIsoSpec grading (MvPolynomial.X i) (variable_degree i) (by decide)

theorem chartOpen_cover : (⨆ i : Fin 2, chartOpen i) = ⊤ :=
  Proj.iSup_basicOpen_eq_top grading _ irrelevant_le_variableSpan

theorem chartOpen_zero_sup_one : chartOpen 0 ⊔ chartOpen 1 = ⊤ := by
  apply top_unique
  rw [← chartOpen_cover]
  apply iSup_le
  intro i
  fin_cases i
  · exact le_sup_left
  · exact le_sup_right

theorem chartOpen_affine (i : Fin 2) : IsAffineOpen (chartOpen i) :=
  Proj.isAffineOpen_basicOpen grading (MvPolynomial.X i) (variable_degree i) (by decide)

def affineCover : lineScheme.AffineOpenCover :=
  Proj.affineOpenCoverOfIrrelevantLESpan grading
    (MvPolynomial.X : Fin 2 → Binary) variable_degree (fun _ => by decide)
    irrelevant_le_variableSpan

def chartSectionsIso (i : Fin 2) :
    CommRingCat.of (ChartRing i) ≅ lineScheme.presheaf.obj (Opposite.op (chartOpen i)) :=
  Proj.basicOpenIsoAway grading (MvPolynomial.X i) (variable_degree i) (by decide)

def chartInclusion (i : Fin 2) : Spec (CommRingCat.of (ChartRing i)) ⟶ lineScheme :=
  Proj.awayι grading (MvPolynomial.X i) (variable_degree i) (by decide)

instance chartInclusion_isOpenImmersion (i : Fin 2) : IsOpenImmersion (chartInclusion i) :=
  inferInstanceAs (IsOpenImmersion
    (Proj.awayι grading (MvPolynomial.X i) (variable_degree i) (by decide)))

theorem chartInclusion_range (i : Fin 2) :
    (chartInclusion i).opensRange = chartOpen i :=
  Proj.opensRange_awayι grading (MvPolynomial.X i) (variable_degree i) (by decide)



/-! ## Algebra -/

def dehom (i : Fin 2) : Binary →+* Polynomial ℂ :=
  (MvPolynomial.aeval (fun j : Fin 2 => if j = i then 1 else Polynomial.X)).toRingHom

@[simp] theorem dehom_X_self (i : Fin 2) : dehom i (MvPolynomial.X i) = 1 := by
  simp [dehom]

@[simp] theorem dehom_X_other (i j : Fin 2) (h : j ≠ i) :
    dehom i (MvPolynomial.X j) = Polynomial.X := by
  simp [dehom, h]

def localizedDehom (i : Fin 2) :
    Localization.Away (MvPolynomial.X i : Binary) →+* Polynomial ℂ :=
  Localization.awayLift (dehom i) (MvPolynomial.X i) (by simp)

def chartToPolynomial (i : Fin 2) : ChartRing i →+* Polynomial ℂ :=
  (localizedDehom i).comp
    (algebraMap (ChartRing i) (Localization.Away (MvPolynomial.X i : Binary)))

theorem chartToPolynomial_mk (i : Fin 2) (n : ℕ) (p : Binary)
    (hp : p ∈ grading (n • 1)) :
    chartToPolynomial i (HomogeneousLocalization.Away.mk grading (variable_degree i) n p hp) =
      dehom i p := by
  change localizedDehom i
    (Localization.mk p ⟨(MvPolynomial.X i : Binary)^n, n, rfl⟩) = dehom i p
  unfold localizedDehom
  simpa only [one_pow, mul_one] using
    Localization.awayLift_mk (dehom i) (MvPolynomial.X i) p 1 (by simp) n

def swapBinary : Binary →ₐ[ℂ] Binary := MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1)

theorem swapBinary_involutive (p : Binary) : swapBinary (swapBinary p) = p := by
  simp only [swapBinary, MvPolynomial.rename_rename, Function.comp_def, Equiv.swap_apply_self]
  exact MvPolynomial.rename_id_apply p

theorem swapBinary_homogeneous {p : Binary} {n : ℕ} (hp : p.IsHomogeneous n) :
    (swapBinary p).IsHomogeneous n :=
  MvPolynomial.IsHomogeneous.rename_isHomogeneous hp

theorem dehom_one (p : Binary) : dehom 1 p = MvPolynomial.aeval ![Polynomial.X, 1] p := by
  have hv : (fun j : Fin 2 => if j = 1 then (1 : Polynomial ℂ) else Polynomial.X) =
      ![Polynomial.X, 1] := by
    funext j
    fin_cases j <;> simp
  change MvPolynomial.aeval (fun j : Fin 2 => if j = 1 then 1 else Polynomial.X) p = _
  rw [hv]

theorem dehom_zero_swap (p : Binary) : dehom 0 (swapBinary p) = dehom 1 p := by
  have h : (dehom 0).comp swapBinary.toRingHom = dehom 1 := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [dehom, swapBinary]
    · intro i
      fin_cases i <;> simp [dehom, swapBinary]
  exact congrArg (fun f : Binary →+* Polynomial ℂ => f p) h

theorem dehom_one_swap (p : Binary) : dehom 1 (swapBinary p) = dehom 0 p := by
  simpa only [swapBinary_involutive] using (dehom_zero_swap (swapBinary p)).symm

theorem homogeneous_dehom_eq_zero {i : Fin 2} {p : Binary} {n : ℕ}
    (hp : p.IsHomogeneous n) (h : dehom i p = 0) : p = 0 := by
  have one_case : ∀ (q : Binary), q.IsHomogeneous n → dehom 1 q = 0 → q = 0 := by
    intro q hq hq0
    have hh := Polynomial.homogenize_eq_of_isHomogeneous hq
      ((dehom_one q).symm.trans hq0)
    simpa using hh.symm
  fin_cases i
  · have hs : swapBinary p = 0 := one_case _ (swapBinary_homogeneous hp) (by
      rw [dehom_one_swap]
      exact h)
    have := congrArg swapBinary hs
    simpa [swapBinary_involutive] using this
  · exact one_case _ hp h

theorem chartToPolynomial_injective (i : Fin 2) : Function.Injective (chartToPolynomial i) := by
  apply (injective_iff_map_eq_zero (chartToPolynomial i)).mpr
  intro z hz
  obtain ⟨n, p, hp, rfl⟩ := HomogeneousLocalization.Away.mk_surjective grading (variable_degree i) z
  rw [chartToPolynomial_mk] at hz
  have hp0 : p = 0 := homogeneous_dehom_eq_zero (by simpa using hp) hz
  apply HomogeneousLocalization.val_injective
  simp [HomogeneousLocalization.Away.val_mk, hp0, Localization.mk_zero]

theorem chartToPolynomial_surjective (i : Fin 2) : Function.Surjective (chartToPolynomial i) := by
  intro p
  let q : Binary := p.homogenize p.natDegree
  have hq : q ∈ grading (p.natDegree • 1) := by
    simpa [q] using (Polynomial.isHomogeneous_homogenize (n := p.natDegree) p)
  have heval : dehom 1 q = p := by
    rw [dehom_one]
    exact Polynomial.aeval_homogenize_X_one p le_rfl
  have hsq : swapBinary q ∈ grading (p.natDegree • 1) := by
    exact swapBinary_homogeneous (show q.IsHomogeneous (p.natDegree • 1) from hq)
  fin_cases i
  · refine ⟨HomogeneousLocalization.Away.mk grading (variable_degree 0) p.natDegree
      (swapBinary q) hsq, ?_⟩
    exact (chartToPolynomial_mk 0 _ _ hsq).trans ((dehom_zero_swap q).trans heval)
  · refine ⟨HomogeneousLocalization.Away.mk grading (variable_degree 1) p.natDegree q hq, ?_⟩
    exact (chartToPolynomial_mk 1 _ _ hq).trans heval

def chartRingEquiv (i : Fin 2) : ChartRing i ≃+* Polynomial ℂ :=
  RingEquiv.ofBijective (chartToPolynomial i)
    ⟨chartToPolynomial_injective i, chartToPolynomial_surjective i⟩



/-! ## Geometry -/

/-- The two actual standard affine charts of Proj(ℂ[X₀,X₁]) have coordinate ring ℂ[t]. -/
def polynomialChartIso (i : Fin 2) :
    (chartOpen i).toScheme ≅ Spec (CommRingCat.of (Polynomial ℂ)) :=
  chartIso i ≪≫ Scheme.Spec.mapIso (chartRingEquiv i).symm.toCommRingCatIso.op

/-- The affine coordinate `Xⱼ/Xᵢ` on the standard chart `D₊(Xᵢ)`. -/
def ratio (i j : Fin 2) : ChartRing i :=
  HomogeneousLocalization.Away.isLocalizationElem (variable_degree i) (variable_degree j)

@[simp] theorem chartToPolynomial_ratio (i j : Fin 2) :
    chartToPolynomial i (ratio i j) = if j = i then 1 else Polynomial.X := by
  change chartToPolynomial i
    (HomogeneousLocalization.Away.mk grading (variable_degree i) 1
      ((MvPolynomial.X j : Binary)^1) _) = _
  rw [chartToPolynomial_mk]
  simp [dehom]

theorem chartInclusion_preimage_chart (i j : Fin 2) :
    chartInclusion i ⁻¹ᵁ chartOpen j = PrimeSpectrum.basicOpen (ratio i j) :=
  Proj.awayι_preimage_basicOpen grading (variable_degree i) (by decide)
    (variable_degree j) (by decide)

/-- Evaluation of the standard affine coordinate at a complex number. -/
def pointEval (i : Fin 2) (c : ℂ) : ChartRing i →+* ℂ :=
  (Polynomial.evalRingHom c).comp (chartToPolynomial i)

/-- A genuine scheme map Spec ℂ → Proj(ℂ[X₀,X₁]), factoring through chart i. -/
def pointMap (i : Fin 2) (c : ℂ) : Spec (CommRingCat.of ℂ) ⟶ lineScheme :=
  Spec.map (CommRingCat.ofHom (pointEval i c)) ≫ chartInclusion i

@[simp] theorem pointEval_ratio (i j : Fin 2) (c : ℂ) :
    pointEval i c (ratio i j) = if j = i then 1 else c := by
  simp only [pointEval, RingHom.comp_apply, chartToPolynomial_ratio]
  split_ifs <;> simp

theorem pointMap_preimage_chart (i j : Fin 2) (c : ℂ) :
    pointMap i c ⁻¹ᵁ chartOpen j =
      PrimeSpectrum.basicOpen (if j = i then (1 : ℂ) else c) := by
  rw [pointMap, Scheme.Hom.comp_preimage, chartInclusion_preimage_chart,
    SpecMap_preimage_basicOpen]
  exact congrArg PrimeSpectrum.basicOpen (pointEval_ratio i j c)

/-- The two coordinate points are distinct as scheme morphisms. -/
theorem coordinatePoints_distinct : pointMap 0 0 ≠ pointMap 1 0 := by
  intro h
  have hp := congrArg (fun f : Spec (CommRingCat.of ℂ) ⟶ lineScheme =>
    f ⁻¹ᵁ chartOpen 0) h
  simp only [pointMap_preimage_chart, ↓reduceIte, Fin.zero_ne_one,
    PrimeSpectrum.basicOpen_one, PrimeSpectrum.basicOpen_zero] at hp
  exact top_ne_bot hp

/-- The coefficient map into the degree-zero homogeneous part. -/
def constantsToZero : ℂ →+* ↥(grading 0) where
  toFun c := ⟨MvPolynomial.C c, MvPolynomial.isHomogeneous_C (Fin 2) c⟩
  map_zero' := by apply Subtype.ext; simp
  map_one' := by apply Subtype.ext; simp
  map_add' := by intro a b; apply Subtype.ext; simp
  map_mul' := by intro a b; apply Subtype.ext; simp

/-- The canonical structure map determined by constants, rather than by an arbitrary map. -/
def canonicalBaseMap : lineScheme ⟶ Spec (CommRingCat.of ℂ) :=
  Proj.toSpecZero grading ≫ Spec.map (CommRingCat.ofHom constantsToZero)

theorem chartToPolynomial_fromZero (i : Fin 2) (a : grading 0) :
    chartToPolynomial i
      (HomogeneousLocalization.fromZeroRingHom grading (.powers (MvPolynomial.X i)) a) =
      dehom i a.val := by
  change chartToPolynomial i
    (HomogeneousLocalization.Away.mk grading (variable_degree i) 0 a.val _) = _
  exact chartToPolynomial_mk i 0 a.val _

@[simp] theorem pointEval_constants (i : Fin 2) (c a : ℂ) :
    pointEval i c
      (HomogeneousLocalization.fromZeroRingHom grading (.powers (MvPolynomial.X i))
        (constantsToZero a)) = a := by
  simp [pointEval, chartToPolynomial_fromZero, constantsToZero, dehom]

theorem chartInclusion_baseMap (i : Fin 2) :
    chartInclusion i ≫ canonicalBaseMap =
      Spec.map (CommRingCat.ofHom constantsToZero ≫
        CommRingCat.ofHom
          (HomogeneousLocalization.fromZeroRingHom grading (.powers (MvPolynomial.X i)))) := by
  rw [canonicalBaseMap, ← Category.assoc]
  change (Proj.awayι grading (MvPolynomial.X i) (variable_degree i) (by decide) ≫
    Proj.toSpecZero grading) ≫ _ = _
  rw [Proj.awayι_toSpecZero, ← Spec.map_comp]

/-- Every affine coordinate evaluation defines an actual ℂ-point for the canonical base. -/
theorem pointMap_overC (i : Fin 2) (c : ℂ) :
    pointMap i c ≫ canonicalBaseMap = 𝟙 (Spec (CommRingCat.of ℂ)) := by
  rw [pointMap, Category.assoc, chartInclusion_baseMap, ← Spec.map_comp]
  have h : (CommRingCat.ofHom constantsToZero ≫
      CommRingCat.ofHom
        (HomogeneousLocalization.fromZeroRingHom grading (.powers (MvPolynomial.X i)))) ≫
      CommRingCat.ofHom (pointEval i c) = 𝟙 (CommRingCat.of ℂ) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact pointEval_constants i c a
  rw [h, Spec.map_id]

/-- The open immersion of the standard polynomial chart. -/
def polynomialChartInclusion (i : Fin 2) :
    Spec (CommRingCat.of (Polynomial ℂ)) ⟶ lineScheme :=
  (polynomialChartIso i).inv ≫ (chartOpen i).ι

instance polynomialChartInclusion_isOpenImmersion (i : Fin 2) :
    IsOpenImmersion (polynomialChartInclusion i) :=
  inferInstanceAs (IsOpenImmersion ((polynomialChartIso i).inv ≫ (chartOpen i).ι))

theorem polynomialChartInclusion_range (i : Fin 2) :
    (polynomialChartInclusion i).opensRange = chartOpen i := by
  exact (Scheme.Hom.opensRange_comp_of_isIso
    (polynomialChartIso i).inv (chartOpen i).ι).trans (Scheme.Opens.opensRange_ι _)

theorem pointMap_eq_polynomialChart (i : Fin 2) (c : ℂ) :
    pointMap i c =
      Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom c)) ≫
        polynomialChartInclusion i := by
  change Spec.map (CommRingCat.ofHom (chartToPolynomial i) ≫
    CommRingCat.ofHom (Polynomial.evalRingHom c)) ≫ chartInclusion i = _
  rw [Spec.map_comp, Category.assoc]
  rfl

/-- Any complex-valued scheme point factors through one of the actual polynomial charts. -/
theorem point_factors_polynomialChart (p : Spec (CommRingCat.of ℂ) ⟶ lineScheme) :
    ∃ i : Fin 2, ∃ q : Spec (CommRingCat.of ℂ) ⟶ Spec (CommRingCat.of (Polynomial ℂ)),
      q ≫ polynomialChartInclusion i = p := by
  have hx : p (default : PrimeSpectrum ℂ) ∈ ⨆ i : Fin 2, chartOpen i := by
    rw [chartOpen_cover]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  have hr : Set.range p ⊆ Set.range (polynomialChartInclusion i) := by
    rintro _ ⟨y, rfl⟩
    change p y ∈ (polynomialChartInclusion i).opensRange
    rw [polynomialChartInclusion_range]
    have hy : y = (default : PrimeSpectrum ℂ) := Subsingleton.elim _ _
    simpa only [hy] using hi
  exact ⟨i, IsOpenImmersion.lift (polynomialChartInclusion i) p hr,
    IsOpenImmersion.lift_fac _ _ _⟩


/-! ## Points -/

@[reassoc (attr := simp)] theorem polynomialChartIso_hom_inclusion (i : Fin 2) :
    (polynomialChartIso i).hom ≫ polynomialChartInclusion i = (chartOpen i).ι := by
  change (polynomialChartIso i).hom ≫
    ((polynomialChartIso i).inv ≫ (chartOpen i).ι) = _
  rw [Iso.hom_inv_id_assoc]

theorem polynomialChartInclusion_baseMap (i : Fin 2) :
    polynomialChartInclusion i ≫ canonicalBaseMap =
      Spec.map (CommRingCat.ofHom (Polynomial.C : ℂ →+* Polynomial ℂ)) := by
  change (Spec.map (CommRingCat.ofHom (chartToPolynomial i)) ≫ chartInclusion i) ≫
    canonicalBaseMap = _
  rw [Category.assoc, chartInclusion_baseMap, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  change chartToPolynomial i
    (HomogeneousLocalization.fromZeroRingHom grading (.powers (MvPolynomial.X i))
      (constantsToZero a)) = Polynomial.C a
  simp [chartToPolynomial_fromZero, constantsToZero, dehom]

/-- A point of the affine line over ℂ is evaluation at one complex scalar. -/
theorem affinePoint_overC_is_eval
    (q : Spec (CommRingCat.of ℂ) ⟶ Spec (CommRingCat.of (Polynomial ℂ)))
    (hq : q ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : ℂ →+* Polynomial ℂ)) =
      𝟙 (Spec (CommRingCat.of ℂ))) :
    ∃ c : ℂ, q = Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom c)) := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective q
  have hc : CommRingCat.ofHom (Polynomial.C : ℂ →+* Polynomial ℂ) ≫ φ =
      𝟙 (CommRingCat.of ℂ) := by
    apply Spec.map_injective
    simpa only [Spec.map_comp, Spec.map_id] using hq
  refine ⟨φ Polynomial.X, ?_⟩
  congr 1
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro a
    have ha := congrArg (fun f : CommRingCat.of ℂ ⟶ CommRingCat.of ℂ => f a) hc
    simpa using ha
  · simp

/-- A specified coordinate chart contains the entire image of a complex-valued point
as soon as it contains its unique underlying topological point. -/
theorem point_factors_chart_of_mem
    (p : Spec (CommRingCat.of ℂ) ⟶ lineScheme) (i : Fin 2)
    (hi : p (default : PrimeSpectrum ℂ) ∈ chartOpen i) :
    ∃ q : Spec (CommRingCat.of ℂ) ⟶ Spec (CommRingCat.of (Polynomial ℂ)),
      q ≫ polynomialChartInclusion i = p := by
  have hr : Set.range p ⊆ Set.range (polynomialChartInclusion i) := by
    rintro _ ⟨y, rfl⟩
    change p y ∈ (polynomialChartInclusion i).opensRange
    rw [polynomialChartInclusion_range]
    have hy : y = (default : PrimeSpectrum ℂ) := Subsingleton.elim _ _
    simpa only [hy] using hi
  exact ⟨IsOpenImmersion.lift (polynomialChartInclusion i) p hr,
    IsOpenImmersion.lift_fac _ _ _⟩

/-- For each chart, a complex-valued point either factors through it or misses it. -/
theorem point_chart_dichotomy (p : Spec (CommRingCat.of ℂ) ⟶ lineScheme) (i : Fin 2) :
    (∃ q : Spec (CommRingCat.of ℂ) ⟶ Spec (CommRingCat.of (Polynomial ℂ)),
      q ≫ polynomialChartInclusion i = p) ∨ p ⁻¹ᵁ chartOpen i = ⊥ := by
  classical
  by_cases hi : p (default : PrimeSpectrum ℂ) ∈ chartOpen i
  · exact Or.inl (point_factors_chart_of_mem p i hi)
  · right
    apply bot_unique
    intro y hy
    change p y ∈ chartOpen i at hy
    have hy' : y = (default : PrimeSpectrum ℂ) := Subsingleton.elim _ _
    exact False.elim (hi (by simpa only [hy'] using hy))

/-- Every canonical complex point is a coordinate evaluation in at least one chart. -/
theorem canonicalPoint_is_coordinate
    (p : Spec (CommRingCat.of ℂ) ⟶ lineScheme)
    (hp : p ≫ canonicalBaseMap = 𝟙 (Spec (CommRingCat.of ℂ))) :
    ∃ (i : Fin 2) (c : ℂ), pointMap i c = p := by
  obtain ⟨i, q, hq⟩ := point_factors_polynomialChart p
  have hqc : q ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : ℂ →+* Polynomial ℂ)) =
      𝟙 (Spec (CommRingCat.of ℂ)) := by
    rw [← polynomialChartInclusion_baseMap, ← Category.assoc, hq, hp]
  obtain ⟨c, rfl⟩ := affinePoint_overC_is_eval q hqc
  exact ⟨i, c, (pointMap_eq_polynomialChart i c).trans hq⟩

/-- On each standard affine chart, the ideal of a canonical complex point is either
an evaluation ideal or the ideal of an empty inverse image. -/
theorem canonicalPoint_chart_dichotomy
    (p : Spec (CommRingCat.of ℂ) ⟶ lineScheme)
    (hp : p ≫ canonicalBaseMap = 𝟙 (Spec (CommRingCat.of ℂ))) (i : Fin 2) :
    (∃ c : ℂ, Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom c)) ≫
      polynomialChartInclusion i = p) ∨ p ⁻¹ᵁ chartOpen i = ⊥ := by
  rcases point_chart_dichotomy p i with ⟨q, hq⟩ | hd
  · have hqc : q ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : ℂ →+* Polynomial ℂ)) =
        𝟙 (Spec (CommRingCat.of ℂ)) := by
      rw [← polynomialChartInclusion_baseMap, ← Category.assoc, hq, hp]
    obtain ⟨c, rfl⟩ := affinePoint_overC_is_eval q hqc
    exact Or.inl ⟨c, hq⟩
  · exact Or.inr hd


/-! ## Overlap -/

/-- The ring of the actual intersection D₊(X₀X₁). -/
abbrev OverlapRing :=
  HomogeneousLocalization.Away grading ((MvPolynomial.X 0 : Binary) * MvPolynomial.X 1)

def chartZeroToOverlap : ChartRing 0 →+* OverlapRing :=
  HomogeneousLocalization.awayMap grading (variable_degree 1) rfl

def chartOneToOverlap : ChartRing 1 →+* OverlapRing :=
  HomogeneousLocalization.awayMap grading (variable_degree 0) (mul_comm _ _)

local instance : Algebra (ChartRing 0) OverlapRing := chartZeroToOverlap.toAlgebra
local instance : IsLocalization.Away (ratio 0 1) OverlapRing :=
  HomogeneousLocalization.Away.isLocalization_mul
    (variable_degree 0) (variable_degree 1) rfl (by decide)

theorem coordinateSubmonoid_map :
    (Submonoid.powers (ratio 0 1)).map (chartRingEquiv 0).toMonoidHom =
      Submonoid.powers (Polynomial.X : Polynomial ℂ) := by
  rw [Submonoid.map_powers]
  congr 1
  change chartToPolynomial 0 (ratio 0 1) = Polynomial.X
  simp

/-- The coordinate ring of the actual overlap is the Laurent polynomial ring. -/
def overlapRingEquiv : OverlapRing ≃+* ℂ[T;T⁻¹] :=
  IsLocalization.ringEquivOfRingEquiv OverlapRing ℂ[T;T⁻¹]
    (chartRingEquiv 0) coordinateSubmonoid_map

theorem overlapRingEquiv_chartZero (a : ChartRing 0) :
    overlapRingEquiv (chartZeroToOverlap a) = (chartToPolynomial 0 a).toLaurent := by
  exact IsLocalization.ringEquivOfRingEquiv_eq coordinateSubmonoid_map a

@[simp] theorem overlapRingEquiv_ratioZero :
    overlapRingEquiv (chartZeroToOverlap (ratio 0 1)) = LaurentPolynomial.T 1 := by
  rw [overlapRingEquiv_chartZero, chartToPolynomial_ratio]
  simp

/-- Both affine coordinates multiply to one on the actual intersection. -/
theorem overlap_coordinates_inverse :
    chartZeroToOverlap (ratio 0 1) * chartOneToOverlap (ratio 1 0) = 1 := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_one,
    chartZeroToOverlap, chartOneToOverlap, ratio,
    HomogeneousLocalization.Away.isLocalizationElem,
    HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.Away.val_mk]
  simp only [pow_one, Localization.mk_mul]
  rw [← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, Submonoid.coe_mul, one_mul, mul_one]
  ring

@[simp] theorem overlapRingEquiv_ratioOne :
    overlapRingEquiv (chartOneToOverlap (ratio 1 0)) = LaurentPolynomial.T (-1) := by
  have h := congrArg overlapRingEquiv overlap_coordinates_inverse
  rw [map_mul, map_one, overlapRingEquiv_ratioZero] at h
  calc
    overlapRingEquiv (chartOneToOverlap (ratio 1 0)) =
        (LaurentPolynomial.T (-1) * LaurentPolynomial.T 1) *
          overlapRingEquiv (chartOneToOverlap (ratio 1 0)) := by
      rw [← LaurentPolynomial.T_add, neg_add_cancel, LaurentPolynomial.T_zero, one_mul]
    _ = LaurentPolynomial.T (-1) := by rw [mul_assoc, h, mul_one]

/-- The scheme-theoretic overlap of the two standard charts is Spec ℂ[t,t⁻¹]. -/
def overlapSchemeIso :
    pullback (chartInclusion 0) (chartInclusion 1) ≅ Spec (CommRingCat.of ℂ[T;T⁻¹]) :=
  Proj.pullbackAwayιIso grading (variable_degree 0) (by decide)
    (variable_degree 1) (by decide) rfl ≪≫
      Scheme.Spec.mapIso overlapRingEquiv.symm.toCommRingCatIso.op


/-! ## Transition -/

theorem chartRingEquiv_symm_C (i : Fin 2) (c : ℂ) :
    (chartRingEquiv i).symm (Polynomial.C c) =
      HomogeneousLocalization.fromZeroRingHom grading (.powers (MvPolynomial.X i))
        (constantsToZero c) := by
  apply (chartRingEquiv i).injective
  rw [RingEquiv.apply_symm_apply]
  change Polynomial.C c = chartToPolynomial i _
  simp [chartToPolynomial_fromZero, constantsToZero, dehom]

theorem chartRingEquiv_symm_X (i j : Fin 2) (h : j ≠ i) :
    (chartRingEquiv i).symm Polynomial.X = ratio i j := by
  apply (chartRingEquiv i).injective
  rw [RingEquiv.apply_symm_apply]
  change Polynomial.X = chartToPolynomial i (ratio i j)
  simp [h]

theorem overlapRingEquiv_chartOne_constant (c : ℂ) :
    overlapRingEquiv (chartOneToOverlap ((chartRingEquiv 1).symm (Polynomial.C c))) =
      LaurentPolynomial.C c := by
  rw [chartRingEquiv_symm_C]
  have h : chartOneToOverlap
      (HomogeneousLocalization.fromZeroRingHom grading (.powers (MvPolynomial.X 1))
        (constantsToZero c)) =
      chartZeroToOverlap
      (HomogeneousLocalization.fromZeroRingHom grading (.powers (MvPolynomial.X 0))
        (constantsToZero c)) := by
    simp only [chartOneToOverlap, chartZeroToOverlap,
      HomogeneousLocalization.awayMap_fromZeroRingHom]
  rw [h, overlapRingEquiv_chartZero, chartToPolynomial_fromZero]
  simp [constantsToZero, dehom]

/-- The second chart restricts by substituting the inverse of the first chart's variable. -/
theorem overlapRingEquiv_chartOne (a : ChartRing 1) :
    overlapRingEquiv (chartOneToOverlap a) =
      LaurentPolynomial.invert (chartToPolynomial 1 a).toLaurent := by
  have h : overlapRingEquiv.toRingHom.comp
        (chartOneToOverlap.comp (chartRingEquiv 1).symm.toRingHom) =
      LaurentPolynomial.invert.toRingHom.comp
        (Polynomial.toLaurent : Polynomial ℂ →+* ℂ[T;T⁻¹]) := by
    apply Polynomial.ringHom_ext
    · intro c
      change overlapRingEquiv (chartOneToOverlap ((chartRingEquiv 1).symm (Polynomial.C c))) =
        LaurentPolynomial.invert (Polynomial.C c).toLaurent
      rw [overlapRingEquiv_chartOne_constant]
      simp
    · change overlapRingEquiv (chartOneToOverlap ((chartRingEquiv 1).symm Polynomial.X)) =
        LaurentPolynomial.invert Polynomial.X.toLaurent
      rw [chartRingEquiv_symm_X 1 0 (by decide), overlapRingEquiv_ratioOne]
      simp
  have hh := congrArg (fun f : Polynomial ℂ →+* ℂ[T;T⁻¹] => f (chartRingEquiv 1 a)) h
  change overlapRingEquiv (chartOneToOverlap ((chartRingEquiv 1).symm (chartRingEquiv 1 a))) =
    LaurentPolynomial.invert (chartToPolynomial 1 a).toLaurent at hh
  simpa only [RingEquiv.symm_apply_apply] using hh

end LeBrunSalamon.P1Charts


namespace LeBrunSalamon.P1Restriction

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentyEight

/-- On an open subscheme, the structure map followed by the restriction
counit is the canonical isomorphism of structure sheaves. -/
theorem restrict_structurePushforwardMap {U X : Scheme} (j : U ⟶ X)
    [IsOpenImmersion j] :
    (Scheme.Modules.restrictFunctor j).map (structurePushforwardMap j) ≫
      (Scheme.Modules.restrictFunctorAdjCounitIso j).hom.app (structureModule U) =
        (Scheme.Modules.restrictUnitIso j).hom := by
  apply Scheme.Modules.hom_ext
  intro W
  ext a
  change U.presheaf.map (eqToHom (j.preimage_image_eq W).symm).op
      (j.app (j ''ᵁ W) a) = (j.appIso W).hom a
  exact congrArg
    (fun f : X.presheaf.obj (Opposite.op (j ''ᵁ W)) ⟶ U.presheaf.obj (Opposite.op W) => f a)
    (j.appIso_hom W).symm

/-- The actual pushforward of a map into an open chart, restricted back to
that chart, is identified using composition and the adjunction counit. -/
def restrictPushforwardIso {S U X : Scheme} (p : S ⟶ U) (j : U ⟶ X)
    [IsOpenImmersion j] :
    ((Scheme.Modules.pushforward (p ≫ j)).obj (structureModule S)).restrict j ≅
      (Scheme.Modules.pushforward p).obj (structureModule S) :=
  (Scheme.Modules.restrictFunctor j).mapIso
      (((Scheme.Modules.pushforwardComp p j).app (structureModule S)).symm) ≪≫
    (Scheme.Modules.restrictFunctorAdjCounitIso j).app
      ((Scheme.Modules.pushforward p).obj (structureModule S))

theorem restrict_structurePushforwardMap_comp {S U X : Scheme}
    (p : S ⟶ U) (j : U ⟶ X) [IsOpenImmersion j] :
    (Scheme.Modules.restrictFunctor j).map (structurePushforwardMap (p ≫ j)) ≫
      (restrictPushforwardIso p j).hom =
        (Scheme.Modules.restrictUnitIso j).hom ≫ structurePushforwardMap p := by
  have hc : structurePushforwardMap (p ≫ j) = structurePushforwardMap j ≫
      (Scheme.Modules.pushforward j).map (structurePushforwardMap p) ≫
      (Scheme.Modules.pushforwardComp p j).hom.app (structureModule S) := by
    apply Scheme.Modules.hom_ext
    intro W
    ext a
    rfl
  rw [hc]
  simp only [restrictPushforwardIso, Functor.map_comp, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Category.assoc]
  have hi : (Scheme.Modules.restrictFunctor j).map
      ((Scheme.Modules.pushforwardComp p j).hom.app (structureModule S)) ≫
      (Scheme.Modules.restrictFunctor j).map
        ((Scheme.Modules.pushforwardComp p j).app (structureModule S)).inv = 𝟙 _ := by
    rw [← Functor.map_comp]
    change (Scheme.Modules.restrictFunctor j).map
      (((Scheme.Modules.pushforwardComp p j).app (structureModule S)).hom ≫
        ((Scheme.Modules.pushforwardComp p j).app (structureModule S)).inv) = _
    rw [Iso.hom_inv_id, CategoryTheory.Functor.map_id]
  rw [← Category.assoc
    ((Scheme.Modules.restrictFunctor j).map
      ((Scheme.Modules.pushforwardComp p j).hom.app (structureModule S)))
    ((Scheme.Modules.restrictFunctor j).map
      ((Scheme.Modules.pushforwardComp p j).app (structureModule S)).inv), hi,
    Category.id_comp]
  rw [show (Scheme.Modules.restrictFunctor j).map
      ((Scheme.Modules.pushforward j).map (structurePushforwardMap p)) ≫
      ((Scheme.Modules.restrictFunctorAdjCounitIso j).app
        ((Scheme.Modules.pushforward p).obj (structureModule S))).hom =
      (Scheme.Modules.restrictFunctorAdjCounitIso j).hom.app (structureModule U) ≫
        structurePushforwardMap p from
      (Scheme.Modules.restrictFunctorAdjCounitIso j).hom.naturality
        (structurePushforwardMap p)]
  change (Scheme.Modules.restrictFunctor j).map (structurePushforwardMap j) ≫
    (Scheme.Modules.restrictFunctorAdjCounitIso j).hom.app (structureModule U) ≫
      structurePushforwardMap p = _
  rw [← Category.assoc, restrict_structurePushforwardMap]

theorem structurePushforwardMap_isIso {S T : Scheme} (e : S ⟶ T) [IsIso e] :
    IsIso (structurePushforwardMap e) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro W
  change IsIso ((forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).map (e.app W))
  infer_instance

/-- Precomposing a point with an isomorphism of its source preserves the
actual categorical kernel defining its ideal sheaf. -/
def structureKernel_precomposeIso {S T X : Scheme} (e : S ≅ T) (p : T ⟶ X) :
    kernel (structurePushforwardMap (e.hom ≫ p)) ≅ kernel (structurePushforwardMap p) := by
  letI := structurePushforwardMap_isIso e.hom
  let q := (Scheme.Modules.pushforward p).mapIso (asIso (structurePushforwardMap e.hom)) ≪≫
    (Scheme.Modules.pushforwardComp e.hom p).app (structureModule S)
  refine (kernel.mapIso (structurePushforwardMap p)
    (structurePushforwardMap (e.hom ≫ p)) (Iso.refl _) q ?_).symm
  apply Scheme.Modules.hom_ext
  intro W
  ext a
  rfl

end LeBrunSalamon.P1Restriction


namespace LeBrunSalamon.P1Ideal

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix

set_option backward.isDefEq.respectTransparency false in
/-- Injectivity survives the associated-sheaf construction, checked on every open via localization. -/
theorem tilde_map_injective {R : CommRingCat} {M N : ModuleCat R}
    (f : M ⟶ N) (hf : Function.Injective f) (U : (Spec R).Opens) :
    Function.Injective ((tilde.map f).app U) := by
  intro x y hxy
  apply Subtype.ext
  funext p
  apply IsLocalizedModule.map_injective p.val.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap p.val.asIdeal.primeCompl M)
    (LocalizedModule.mkLinearMap p.val.asIdeal.primeCompl N) f.hom hf
  exact congrArg (fun z => z.val p) hxy

set_option backward.isDefEq.respectTransparency false in
theorem tilde_map_mono {R : CommRingCat} {M N : ModuleCat R}
    (f : M ⟶ N) [Mono f] : Mono (tilde.map f) := by
  apply (Scheme.Modules.toPresheaf _).mono_of_mono_map
  have hmono (U : (TopologicalSpace.Opens (Spec R))ᵒᵖ) :
      Mono (((Scheme.Modules.toPresheaf _).map (tilde.map f)).app U) := by
    apply (AddCommGrpCat.mono_iff_injective _).mpr
    exact tilde_map_injective f ((ModuleCat.mono_iff_injective f).mp inferInstance) U.unop
  letI := hmono
  exact NatTrans.mono_of_mono_app _

set_option backward.isDefEq.respectTransparency false in
instance tilde_preservesMonomorphisms (R : CommRingCat) :
    (tilde.functor R).PreservesMonomorphisms where
  preserves f hf := by
    letI := hf
    exact tilde_map_mono f

set_option backward.isDefEq.respectTransparency false in
/-- The associated-sheaf functor is exact: it preserves monomorphisms and already preserves cokernels. -/
instance tilde_preservesHomology (R : CommRingCat) :
    (tilde.functor R).PreservesHomology :=
  Functor.preservesHomology_of_preservesMonos_and_cokernels _

set_option backward.isDefEq.respectTransparency false in
def affineKernelIso {R : CommRingCat} {M N : (Spec R).Modules}
    (f : M ⟶ N) [IsIso M.fromTildeΓ] [IsIso N.fromTildeΓ] :
    tilde (kernel ((moduleSpecΓFunctor (R := R)).map f)) ≅ kernel f := by
  letI := Functor.PreservesHomology.preservesKernel (tilde.functor R)
    ((moduleSpecΓFunctor (R := R)).map f)
  exact PreservesKernel.iso (tilde.functor R) ((moduleSpecΓFunctor (R := R)).map f) ≪≫
    kernel.mapIso _ f (asIso M.fromTildeΓ) (asIso N.fromTildeΓ)
      ((tilde.adjunction (R := R)).counit.naturality f)

set_option backward.isDefEq.respectTransparency false in
def affineKernelLinearIso {R : CommRingCat} {M N : (Spec R).Modules}
    (f : M ⟶ N) [IsIso M.fromTildeΓ] [IsIso N.fromTildeΓ] :
    tilde (ModuleCat.of R ((moduleSpecΓFunctor (R := R)).map f).hom.ker) ≅
      kernel f :=
  (tilde.functor R).mapIso (ModuleCat.kernelIsoKer _).symm ≪≫ affineKernelIso f

open LeBrunSalamon.PhaseTwentyEight

set_option backward.isDefEq.respectTransparency false in
def affineStructureKernelLinearIso {R S : CommRingCat} (φ : R ⟶ S) :
    RingHom.ker φ.hom ≃ₗ[R]
      ((moduleSpecΓFunctor (R := R)).map (structurePushforwardMap (Spec.map φ))).hom.ker := by
  let e := (tilde.isoTop (ModuleCat.of R R)).toLinearEquiv
  let g := ((moduleSpecΓFunctor (R := R)).map
    (structurePushforwardMap (Spec.map φ))).hom
  have h : g.ker.comap e.toLinearMap = RingHom.ker φ.hom := by
    ext x
    change g (e x) = 0 ↔ φ x = 0
    change (Spec.map φ).appTop ((Scheme.ΓSpecIso R).inv x) = 0 ↔ φ x = 0
    have heq : (Spec.map φ).appTop ((Scheme.ΓSpecIso R).inv x) =
        (Scheme.ΓSpecIso S).inv (φ x) :=
      (congrArg (fun k : R ⟶ Γ(Spec S, ⊤) => k x)
        (Scheme.ΓSpecIso_inv_naturality φ)).symm
    rw [heq]
    constructor
    · intro hx
      apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso S).inv).injective
      simpa only [map_zero] using hx
    · intro hx
      simpa only [hx, map_zero]
  exact (LinearEquiv.ofEq _ _ h.symm).trans (e.ofSubmodule' g.ker)

set_option backward.isDefEq.respectTransparency false in
/-- The categorical ideal kernel on an affine scheme is the associated module sheaf of the actual ring kernel. -/
def affineStructureKernelIso {R S : CommRingCat} (φ : R ⟶ S) :
    tilde (ModuleCat.of R (RingHom.ker φ.hom)) ≅
      kernel (structurePushforwardMap (Spec.map φ)) := by
  letI : IsIso ((Scheme.Modules.pushforward (Spec.map φ)).obj
      (structureModule (Spec S))).fromTildeΓ :=
    isIso_fromTildeΓ_pushforward φ (structureModule (Spec S))
  exact (tilde.functor R).mapIso (affineStructureKernelLinearIso φ).toModuleIso ≪≫
    affineKernelLinearIso (structurePushforwardMap (Spec.map φ))

/-- Multiplication by X-a identifies the polynomial ring with the evaluation ideal. -/
def polynomialEvalKernelEquiv (a : ℂ) :
    Polynomial ℂ ≃ₗ[Polynomial ℂ] RingHom.ker (Polynomial.evalRingHom a) :=
  (LinearEquiv.toSpanNonzeroSingleton (Polynomial ℂ) (Polynomial ℂ)
    (Polynomial.X - Polynomial.C a) (Polynomial.X_sub_C_ne_zero a)).trans
    (LinearEquiv.ofEq _ _ (Polynomial.ker_evalRingHom a).symm)

set_option backward.isDefEq.respectTransparency false in
/-- The actual ideal sheaf of a complex point on the affine line is trivial of rank one. -/
def affinePointIdealTrivialization (a : ℂ) :
    kernel (structurePushforwardMap
      (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a)))) ≅
      structureModule (Spec (CommRingCat.of (Polynomial ℂ))) :=
  (affineStructureKernelIso (CommRingCat.ofHom (Polynomial.evalRingHom a))).symm ≪≫
    (tilde.functor (CommRingCat.of (Polynomial ℂ))).mapIso
      (polynomialEvalKernelEquiv a).symm.toModuleIso ≪≫ tildeSelf

theorem affinePointIdeal_rankOne (a : ℂ) :
    IsLocallyFreeOfRank
      (kernel (structurePushforwardMap
        (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a))))) 1 :=
  locallyFreeOfRank_iso (affinePointIdealTrivialization a).symm
    (structureModule_rank _)

set_option backward.isDefEq.respectTransparency false in
theorem locallyFreeOfRank_of_openCover {X : Scheme} (E : OModule X)
    (r : ℕ) {ι : Type} (U : ι → X.Opens) (hU : TopologicalSpace.IsOpenCover U)
    (e : ∀ i, SheafOfModules.free (R := X.ringCatSheaf.over (U i)) (Fin r) ≅ E.over (U i)) :
    IsLocallyFreeOfRank E r := by
  let q : SheafOfModules.LocalGeneratorsData.{0} E :=
    { I := ι
      X := U
      coversTop := (Opens.coversTop_iff X U).mpr hU
      generators := fun i => (SheafOfModules.free.generatingSections
        (R := X.ringCatSheaf.over (U i)) (Fin r)).ofEpi (e i).hom }
  refine ⟨q, ?_, fun _ => ⟨Equiv.refl _⟩⟩
  constructor
  intro i
  change IsIso ((SheafOfModules.free.generatingSections (Fin r)).ofEpi (e i).hom).π
  rw [SheafOfModules.GeneratingSections.ofEpi_π]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- Assemble rank-one local freeness from trivializations on actual open subschemes. -/
theorem locallyFreeRankOne_of_restrictTrivial {X : Scheme} (E : OModule X)
    {ι : Type} (U : ι → X.Opens) (hU : TopologicalSpace.IsOpenCover U)
    (e : ∀ i, E.restrict (U i).ι ≅ structureModule (U i).toScheme) :
    IsLocallyFreeOfRank E 1 := by
  apply locallyFreeOfRank_of_openCover E 1 U hU
  intro i
  let F := (Scheme.Modules.overEquiv (U i)).functor
  let eunit : F.obj (SheafOfModules.unit (X.ringCatSheaf.over (U i))) ≅
      structureModule (U i).toScheme :=
    (Scheme.Modules.overFunctorEquiv (U i)).app (structureModule X) ≪≫
      Scheme.Modules.restrictUnitIso (U i).ι
  let eover : E.over (U i) ≅ SheafOfModules.unit (X.ringCatSheaf.over (U i)) :=
    F.preimageIso ((Scheme.Modules.overFunctorEquiv (U i)).app E ≪≫ e i ≪≫ eunit.symm)
  exact coproductUniqueIso (fun _ : Fin 1 =>
    SheafOfModules.unit (X.ringCatSheaf.over (U i))) ≪≫ eover.symm

set_option backward.isDefEq.respectTransparency false in
/-- Open restriction preserves finite limits, detected on the underlying abelian presheaves. -/
theorem restrict_preservesFiniteLimits {X U : Scheme} (j : U ⟶ X) [IsOpenImmersion j] :
    PreservesFiniteLimits (Scheme.Modules.restrictFunctor j) := by
  letI : PreservesFiniteLimits (Scheme.Modules.toPresheaf X) := by infer_instance
  letI : PreservesFiniteLimits
      ((Functor.whiskeringLeft (U.Opens)ᵒᵖ (X.Opens)ᵒᵖ AddCommGrpCat).obj
        j.opensFunctor.op) := by infer_instance
  letI : PreservesFiniteLimits
      (Scheme.Modules.restrictFunctor j ⋙ Scheme.Modules.toPresheaf U) := by
    change PreservesFiniteLimits
      (Scheme.Modules.toPresheaf X ⋙
        (Functor.whiskeringLeft (U.Opens)ᵒᵖ (X.Opens)ᵒᵖ AddCommGrpCat).obj j.opensFunctor.op)
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves
    (Scheme.Modules.restrictFunctor j) (Scheme.Modules.toPresheaf U)

set_option backward.isDefEq.respectTransparency false in
theorem restrict_pushforward_unit_isZero {S X U : Scheme} (p : S ⟶ X)
    (j : U ⟶ X) [IsOpenImmersion j] (h : p ⁻¹ᵁ j.opensRange = ⊥) :
    IsZero (((Scheme.Modules.pushforward p).obj (structureModule S)).restrict j) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  ext W x
  have hW : p ⁻¹ᵁ (j ''ᵁ W) = ⊥ :=
    le_bot_iff.mp ((p.preimage_mono (j.image_le_opensRange W)).trans (le_of_eq h))
  have hs : Subsingleton Γ(S, p ⁻¹ᵁ (j ''ᵁ W)) := by
    rw [hW]
    infer_instance
  exact hs.elim _ _

set_option backward.isDefEq.respectTransparency false in
/-- Off the image of a scheme map, its categorical structure-sheaf kernel is the unit sheaf. -/
def structureKernel_restrict_disjoint {S X U : Scheme} (p : S ⟶ X)
    (j : U ⟶ X) [IsOpenImmersion j] (h : p ⁻¹ᵁ j.opensRange = ⊥) :
    (kernel (structurePushforwardMap p)).restrict j ≅ structureModule U := by
  let F := Scheme.Modules.restrictFunctor j
  letI : PreservesFiniteLimits F := restrict_preservesFiniteLimits j
  have hz := restrict_pushforward_unit_isZero p j h
  exact PreservesKernel.iso F (structurePushforwardMap p) ≪≫
    kernelIsoOfEq (hz.eq_zero_of_tgt (F.map (structurePushforwardMap p))) ≪≫
      kernelZeroIsoSource ≪≫ Scheme.Modules.restrictUnitIso j


open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.P1Restriction

set_option backward.isDefEq.respectTransparency false in
def structureKernel_restrict_comp {S U X : Scheme} (p : S ⟶ U)
    (j : U ⟶ X) [IsOpenImmersion j] :
    (kernel (structurePushforwardMap (p ≫ j))).restrict j ≅
      kernel (structurePushforwardMap p) := by
  let F := Scheme.Modules.restrictFunctor j
  letI : PreservesFiniteLimits F := restrict_preservesFiniteLimits j
  exact PreservesKernel.iso F (structurePushforwardMap (p ≫ j)) ≪≫
    kernel.mapIso _ (structurePushforwardMap p) (Scheme.Modules.restrictUnitIso j)
      (restrictPushforwardIso p j) (restrict_structurePushforwardMap_comp p j)

set_option backward.isDefEq.respectTransparency false in
def restrictTrivial_of_iso {X U V : Scheme} (E : OModule X)
    (i : U ⟶ X) (j : V ⟶ X) [IsOpenImmersion i] [IsOpenImmersion j]
    (e : U ≅ V) (h : e.hom ≫ j = i)
    (hE : E.restrict j ≅ structureModule V) :
    E.restrict i ≅ structureModule U :=
  ((Scheme.Modules.restrictFunctorCongr h).app E).symm ≪≫
    (Scheme.Modules.restrictFunctorComp e.hom j).app E ≪≫
      (Scheme.Modules.restrictFunctor e.hom).mapIso hE ≪≫
        Scheme.Modules.restrictUnitIso e.hom

set_option backward.isDefEq.respectTransparency false in
/-- The ideal of every complex point on the actual Proj model of P1 is locally free of rank one. -/
theorem canonicalPointIdeal_rankOne
    (p : Spec (CommRingCat.of ℂ) ⟶ P1Charts.lineScheme)
    (hp : p ≫ P1Charts.canonicalBaseMap = 𝟙 (Spec (CommRingCat.of ℂ))) :
    IsLocallyFreeOfRank (kernel (structurePushforwardMap p)) 1 := by
  apply locallyFreeRankOne_of_restrictTrivial (kernel (structurePushforwardMap p))
    P1Charts.chartOpen P1Charts.chartOpen_cover
  intro i
  apply restrictTrivial_of_iso (kernel (structurePushforwardMap p))
    (P1Charts.chartOpen i).ι (P1Charts.polynomialChartInclusion i)
    (P1Charts.polynomialChartIso i) (P1Charts.polynomialChartIso_hom_inclusion i)
  apply Classical.choice
  rcases P1Charts.canonicalPoint_chart_dichotomy p hp i with ⟨a, rfl⟩ | hd
  · exact ⟨structureKernel_restrict_comp _ _ ≪≫ affinePointIdealTrivialization a⟩
  · exact ⟨structureKernel_restrict_disjoint p (P1Charts.polynomialChartInclusion i)
      (by simpa only [P1Charts.polynomialChartInclusion_range] using hd)⟩

end LeBrunSalamon.P1Ideal

end

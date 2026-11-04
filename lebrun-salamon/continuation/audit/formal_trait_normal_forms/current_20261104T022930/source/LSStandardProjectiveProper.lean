import LSStandardTautological

/-! Properness of standard polynomial Proj over its actual coefficient
ring. The degree-zero comparison and all instances are proved here. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace LeBrunSalamon.StandardProjectiveProper

variable (R : Type) [CommRing R] (N : ℕ)

theorem constants_bijective : Function.Bijective (StandardTautological.constants R N) := by
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

def degreeZeroEquiv : R ≃+* ↥(StandardTautological.grading R N 0) :=
  RingEquiv.ofBijective (StandardTautological.constants R N) (constants_bijective R N)

def coefficientIso : Spec (CommRingCat.of ↥(StandardTautological.grading R N 0)) ≅
    Spec (CommRingCat.of R) where
  hom := Spec.map (CommRingCat.ofHom (StandardTautological.constants R N))
  inv := Spec.map (CommRingCat.ofHom (degreeZeroEquiv R N).symm.toRingHom)
  hom_inv_id := by
    rw [← Spec.map_comp]
    convert Spec.map_id (CommRingCat.of ↥(StandardTautological.grading R N 0)) using 1
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact (degreeZeroEquiv R N).apply_symm_apply a
  inv_hom_id := by
    rw [← Spec.map_comp]
    convert Spec.map_id (CommRingCat.of R) using 1
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact (degreeZeroEquiv R N).symm_apply_apply a

theorem proper : IsProper (StandardTautological.toSpec R N) := by
  let A := MvPolynomial (Fin (N + 1)) R
  let G := StandardTautological.grading R N
  letI : IsScalarTower R (G 0) A :=
    IsScalarTower.of_algebraMap_eq (R := R) (S := ↥(G 0)) (A := A) (fun _ => rfl)
  letI : Algebra.FiniteType (G 0) A :=
    Algebra.FiniteType.of_restrictScalars_finiteType R (G 0) A
  change IsProper (Proj.toSpecZero G ≫ (coefficientIso R N).hom)
  infer_instance

theorem separated : IsSeparated (StandardTautological.toSpec R N) := by
  letI := proper R N
  infer_instance

end LeBrunSalamon.StandardProjectiveProper

end

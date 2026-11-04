import LSVelocityAdditionFamily

/-!
## Positive range of the actual scaled velocity differential

The linear coordinate functions are the same chosen lifts used to define
the global ambient projection. Their derivatives are compared directly
with the original Hom variation. In particular no reducedness assumption
on the full fixed-node Hom scheme is used in this comparison.

Source preparation only; compilation remains deferred.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseSeven LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentySix LeBrunSalamon.PhaseTwentySeven
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction

namespace LeBrunSalamon.Construction.Lines.ScaledVelocityDifferential

open DirectionCones VelocityCoordinates IntrinsicVelocityRange ContactVelocityFactorization

variable {n : ℕ} {X : ContactFanoManifold n}
variable (H : HomSpacePresentation P X.variety) (x : ComplexPoint X.variety)
variable (C : GlobalVelocity.TargetChart X.variety x) (A : Charts.PointedAffine)
variable (g : PointsOver A.scheme A.toC
  (FixedNodeHom.parameter P marking H x) (FixedNodeHom.toC P marking H x))

def coordinate (i : Fin (dimension (n := n) + 1)) : A.Ring :=
  velocityFunctions H x C A g
    (ambientPolynomial C.evaluation (ContactVelocityTarget.image X x C)
      (contactCoordinateBasis X x C) (MvPolynomial.X i))

variable (f : FreeLine X) (hf : marking.map ≫ f.curve.map = x.map)
variable (hat : A.point.val ≫ g.val =
  (HomDeformation.fixedCenter P H marking x f.curve.map f.curve.overC hf).val)

/-- Differentiating the actual lifted coordinate function is precisely
the original contact-fibre Hom differential in the fixed dual basis. -/
theorem coordinate_derivative (D : A.Tangent) (i : Fin (dimension (n := n) + 1)) :
    contactFrame X x C (originalContactDifferential H x C A g f hf hat D) i =
      D.val (coordinate H x C A g i) := by
  have h := ambientPolynomial_tangent C.evaluation (ContactVelocityTarget.image X x C)
    (contactCoordinateBasis X x C) (A.evaluation.comp (velocityFunctions H x C A g))
    (Infinitesimal.tangentMap (velocityFunctions H x C A g) A.evaluation D)
    (ContactVelocityTarget.imageEquiv X x C (originalContactDifferential H x C A g f hf hat D))
    (originalContactDifferential_evaluation H x C A g f hf hat D).symm i
  exact h

include hat in
/-- At the selected centre the same regular coordinate is the original
normalized node differential. This is a scheme-map normalization. -/
theorem coordinate_value (i : Fin (dimension (n := n) + 1)) :
    A.evaluation (coordinate H x C A g i) =
      contactFrame X x C (ScaledVelocities.nodeVector X x f hf) i := by
  let q := A.evaluation.comp (velocityFunctions H x C A g)
  have hv : AffineVelocity.tangentPointEquiv C.evaluation q =
      IntrinsicTangent.chartEvaluation C (ScaledVelocities.nodeVector X x f hf).val := by
    rw [show q = A.evaluation.comp (velocityFunctions H x C A g) from rfl,
      velocityFunctions_point]
    have hp : homPointOfAlgebra H x A g A.evaluation =
        HomDeformation.fixedCenter P H marking x f.curve.map f.curve.overC hf := by
      apply Subtype.ext
      change (pointOfAlgebra A A.evaluation).val ≫ g.val = _
      rw [pointOfAlgebra_evaluation]
      exact hat
    rw [hp]
    exact HomVelocityValue.value_fixedCenter H f x hf C
  have h := AlgHom.congr_fun
    (ambientPolynomial_point C.evaluation (ContactVelocityTarget.image X x C)
      (contactCoordinateBasis X x C) q
      (ContactVelocityTarget.imageEquiv X x C (ScaledVelocities.nodeVector X x f hf)) hv)
    (MvPolynomial.X i)
  simpa only [AlgHom.comp_apply, MvPolynomial.aeval_X] using h

def scalarDifferential (r : A.Ring) : A.Tangent →ₗ[ℂ] ℂ where
  toFun D := D.val r
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

/-- Both terms of the ordinary product rule are retained. -/
def differential (r : A.Ring) : A.Tangent →ₗ[ℂ] contactPlane X x :=
  A.evaluation r • originalContactDifferential H x C A g f hf hat +
    (scalarDifferential A r).smulRight (ScaledVelocities.nodeVector X x f hf)

theorem differential_positive (r : A.Ring) (D : A.Tangent) :
    (differential H x C A g f hf hat r D).val ∈ positiveNodeSpace f x hf := by
  change A.evaluation r • (originalContactDifferential H x C A g f hf hat D).val +
    D.val r • nodeDifferential f x hf (SourceTangent.sourceVector marking) ∈ positiveNodeSpace f x hf
  exact (positiveNodeSpace f x hf).add_mem
    ((positiveNodeSpace f x hf).smul_mem _
      (originalContactDifferential_positive H x C A g f hf hat D))
    ((positiveNodeSpace f x hf).smul_mem _
      (ContactPositive.nodeDifferential_mem_positiveNodeSpace f x hf (SourceTangent.sourceVector marking)))

/-- The product rule identifies this positive-range map with the actual
derivative of the scaled regular coordinate, including moving scalars. -/
theorem differential_coordinate (r : A.Ring) (D : A.Tangent)
    (i : Fin (dimension (n := n) + 1)) :
    contactFrame X x C (differential H x C A g f hf hat r D) i =
      D.val (r * coordinate H x C A g i) := by
  change contactFrame X x C
    (A.evaluation r • originalContactDifferential H x C A g f hf hat D +
      D.val r • ScaledVelocities.nodeVector X x f hf) i = _
  rw [map_add, map_smul, map_smul, Pi.add_apply, Pi.smul_apply, Pi.smul_apply,
    smul_eq_mul, smul_eq_mul, coordinate_derivative, ← coordinate_value H x C A g f hf hat i,
    D.property]
  ring

end LeBrunSalamon.Construction.Lines.ScaledVelocityDifferential

namespace LeBrunSalamon.Construction.Lines.SuitableAffineSource

open DirectionCones IntrinsicVelocityRange

/-- Smoothness of the actual map from an affine source gives
surjectivity of its actual comorphism differential. The Γ–Spec factor
is an isomorphism and is retained explicitly. -/
theorem tangentMap_surjective {R : Type} [CommRing R] [Algebra ℂ R]
    (A : Charts.PointedAffine) (f : A.scheme ⟶ Spec (CommRingCat.of R))
    (hf : f ≫ affineBaseMap R = A.toC) (hs : Smooth f) :
    Function.Surjective (Infinitesimal.tangentMap (schemeComorphism A f hf) A.evaluation) := by
  have htop : f.appTop.hom.Smooth :=
    (HasRingHomProperty.iff_of_isAffine (P := @Smooth) (f := f)).mp hs
  have hspec : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.Smooth :=
    RingHom.Smooth.of_bijective (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv)
  exact SmoothTangent.tangentMap_surjective_of_smooth (schemeComorphism A f hf)
    (hspec.comp htop) A.evaluation

/-- An actual dominant bounded family has a genuine pointed affine
subfamily on which its given map is smooth. The integral subfamily is
constructed by the earlier prime-quotient argument. -/
theorem exists_smooth_chart {I : Type} [Fintype I]
    {Y : Scheme} (sY : Y ⟶ ComplexBase)
    [LocallyOfFiniteType sY] [QuasiCompact sY]
    (f : Y ⟶ affineSpace I) (hf : f ≫ affineBaseMap (MvPolynomial I ℂ) = sY)
    (hd : DenseRange (fun y => f y)) :
    ∃ (A : Charts.PointedAffine)
      (j : PointsOver A.scheme A.toC Y sY), Smooth (j.val ≫ f) := by
  obtain ⟨T, g, ha, hi, hft, hqc, hdom⟩ :=
    FiniteTypeDominance.finiteType_exists_integralAffine_source sY f hd
  letI : IsAffine T := ha
  letI : IsIntegral T := hi
  letI : LocallyOfFiniteType (g ≫ sY) := hft
  letI : QuasiCompact (g ≫ sY) := hqc
  have hgf : (g ≫ f) ≫ affineBaseMap (MvPolynomial I ℂ) = g ≫ sY := by
    rw [Category.assoc, hf]
  letI : IsDominant (g ≫ f) := ⟨hdom⟩
  letI : LocallyOfFiniteType ((g ≫ f) ≫ affineBaseMap (MvPolynomial I ℂ)) := by
    rw [hgf]
    infer_instance
  letI : LocallyOfFiniteType (g ≫ f) :=
    locallyOfFiniteType_of_comp (g ≫ f) (affineBaseMap (MvPolynomial I ℂ))
  letI : QuasiCompact (g ≫ f) := inferInstance
  obtain ⟨W, q, _hWtop, hW, hsm, hq, _⟩ :=
    RelativeGenericSmoothness.finiteTypeComplex_exists_smooth_source_open_point
      (g ≫ sY) (affineBaseMap (MvPolynomial I ℂ)) (g ≫ f) hgf ⊤ Set.univ_nonempty
  letI : Smooth (W.ι ≫ (g ≫ f)) := hsm
  let tq : PointsOver ComplexBase (𝟙 ComplexBase) W.toScheme (W.ι ≫ (g ≫ sY)) := ⟨q, hq⟩
  obtain ⟨V, hV, hqV, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := W.toScheme) (x := q (IsLocalRing.closedPoint ℂ)) (U := ⊤) (by trivial)
  letI : IsAffine V.toScheme := hV
  let tV := HomDegree.pointInOpen tq V hqV
  let A : Charts.PointedAffine :=
    ⟨V.toScheme, hV, V.ι ≫ (W.ι ≫ (g ≫ sY)), tV⟩
  let j : PointsOver A.scheme A.toC Y sY :=
    ⟨V.ι ≫ (W.ι ≫ g), by simp only [A, Category.assoc]⟩
  refine ⟨A, j, ?_⟩
  have h : Smooth (V.ι ≫ (W.ι ≫ (g ≫ f))) := inferInstance
  simpa only [j, Category.assoc] using h

end LeBrunSalamon.Construction.Lines.SuitableAffineSource

end

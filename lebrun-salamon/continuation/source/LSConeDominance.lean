import LSConeFiberRigidity
import LSAdditionFiberPresentation
import LSRelativeGenericSmoothness
import Mathlib.Topology.KrullDimension

/-!
## Dominance of the actual nonorthogonal cone-addition map

The manuscript's curve-and-pole argument has already excluded positive-
dimensional nonorthogonal fibres.  This file applies the classical fibre-
dimension theorem to the actual source open and identifies its actual
scheme fibre with the fixed-sum localization used by that argument.

The remaining VMRT construction must provide the actual integral source,
its dimension, and the smooth isotropic component charts.  None of these
geometric hypotheses is replaced by a numerical label or a dominance
assumption.

Source preparation only; compilation is deferred to the final checkpoint.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne

namespace LeBrunSalamon.StandardInputs

/-- Classical finite-type fibre-dimension corollary, not a verbatim
statement in the project vocabulary.  Stacks 0B2L, Lemma 33.20.4(2)(a),
gives the local fibre-dimension bound after replacing the target by the
closure of the image.  A proper closed subset of affine N-space has
dimension at most N-1.  Finite type over the algebraically closed field
provides a closed complex point, whose actual image is `coordinatePoint`.

There is no cone, contact, or generic-dominance conclusion in this input.
The empty-index case has an impossible nondensity hypothesis because an
integral source is nonempty. -/
theorem finiteType_nondominant_positiveFiber
    {I : Type} [Fintype I] {Y : Scheme} [IsIntegral Y]
    (sY : Y ⟶ ComplexBase)
    [LocallyOfFiniteType sY] [QuasiCompact sY]
    (f : Y ⟶ Construction.Lines.DirectionCones.affineSpace I)
    (hf : f ≫ Construction.Lines.DirectionCones.affineBaseMap
      (Construction.Lines.DirectionCones.CoordinatePolynomial I) = sY)
    (hdim : (Fintype.card I : WithBot ℕ∞) ≤ topologicalKrullDim Y)
    (hnd : ¬ DenseRange (fun y => f y)) :
    ∃ s : I → ℂ, 1 ≤ topologicalKrullDim
      (pullback f (Construction.Lines.DirectionCones.coordinatePoint s) : Scheme) := by
  sorry

end LeBrunSalamon.StandardInputs

namespace LeBrunSalamon.Construction.Lines.ConeDominance

open DirectionCones ConeGeometry AffineCurveSelection

variable {N : ℕ} (D : ReducedProjectiveDirections N)
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable (e : V ≃ₗ[ℂ] (Fin (N + 1) → ℂ))

/-- The original fibre ring is identified with the actual scheme fibre
before any dimension comparison is made.  In particular the fibre is not
silently replaced by its reduction or by one chosen component. -/
theorem nonorthogonalFiber_dimension
    (S T : Set (Fin (N + 1) → ℂ))
    (omega : Fin (N + 1) → Fin (N + 1) → ℂ) (s : Fin (N + 1) → ℂ) :
    topologicalKrullDim
      (pullback (nonorthogonalAddition S T omega) (coordinatePoint s) : Scheme) =
      ringKrullDim (NonorthogonalFiberRing S T s omega) := by
  let E := (nonorthogonalFiber_isPullback S T s omega).isoPullback
  calc
    topologicalKrullDim
        (pullback (nonorthogonalAddition S T omega) (coordinatePoint s) : Scheme) =
        topologicalKrullDim
          (Spec (CommRingCat.of (NonorthogonalFiberRing S T s omega)) : Scheme) :=
      (IsHomeomorph.topologicalKrullDim_eq E.hom
        E.hom.homeomorph.isHomeomorph).symm
    _ = ringKrullDim (NonorthogonalFiberRing S T s omega) :=
      PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _

/-- The actual nonorthogonal addition morphism is dominant.  Its source
dimension, integrality, and finite-type hypotheses are genuine properties
of the component cones and their principal open.  The conclusion follows
from the already proved pole contradiction, without supposing that either
individual projective component spans the ambient space. -/
theorem component_nonorthogonalAddition_denseRange
    (hdisj : Pairwise (fun C E : D.Component => Disjoint C.val E.val))
    (hclosed : ∀ C : D.Component, EquationClosed (D.componentConePoints e C))
    (omega : Fin (N + 1) → Fin (N + 1) → ℂ)
    (hskew : ∀ i j, omega j i = -omega i j)
    (hcharts : ∀ (C : D.Component)
      (p : CoordinateRing (D.componentConePoints e C) →ₐ[ℂ] ℂ),
      (fun i => p (coordinate (D.componentConePoints e C) i)) ≠ 0 →
        ∃ u : CoordinateRing (D.componentConePoints e C), p u ≠ 0 ∧
          Algebra.FormallySmooth ℂ (Localization.Away u) ∧
          ∀ (z : Localization.Away u →ₐ[ℂ] ℂ)
            (A B : Infinitesimal.Tangent (Localization.Away u) z),
            ConePairing.pairing omega
              (fun i => A.val (ConeRadial.localizedCoordinate (L := Localization.Away u)
                (D.componentConePoints e C) i))
              (fun i => B.val (ConeRadial.localizedCoordinate (L := Localization.Away u)
                (D.componentConePoints e C) i)) = 0)
    (C E : D.Component)
    [IsIntegral (nonorthogonalOpen
      (D.componentConePoints e C) (D.componentConePoints e E) omega).toScheme]
    [LocallyOfFiniteType ((nonorthogonalOpen
      (D.componentConePoints e C) (D.componentConePoints e E) omega).ι ≫
      affineBaseMap (ProductRing (D.componentConePoints e C) (D.componentConePoints e E)))]
    [QuasiCompact ((nonorthogonalOpen
      (D.componentConePoints e C) (D.componentConePoints e E) omega).ι ≫
      affineBaseMap (ProductRing (D.componentConePoints e C) (D.componentConePoints e E)))]
    (hdim : (N + 1 : WithBot ℕ∞) ≤ topologicalKrullDim
      (nonorthogonalOpen
        (D.componentConePoints e C) (D.componentConePoints e E) omega).toScheme) :
    DenseRange (fun z => nonorthogonalAddition
      (D.componentConePoints e C) (D.componentConePoints e E) omega z) := by
  by_contra hnd
  obtain ⟨s, hs⟩ := LeBrunSalamon.StandardInputs.finiteType_nondominant_positiveFiber
    ((nonorthogonalOpen
      (D.componentConePoints e C) (D.componentConePoints e E) omega).ι ≫
      affineBaseMap (ProductRing (D.componentConePoints e C) (D.componentConePoints e E)))
    (nonorthogonalAddition (D.componentConePoints e C) (D.componentConePoints e E) omega)
    (nonorthogonalAddition_overC _ _ _)
    (by simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] using hdim) hnd
  rw [nonorthogonalFiber_dimension] at hs
  exact component_nonorthogonalFiber_not_positiveDim D e hdisj hclosed
    omega hskew hcharts C E s hs

/-- Dominance of the restriction implies dominance of the original
addition map, by inclusion of the actual images. -/
theorem addition_denseRange_of_nonorthogonalAddition
    (S T : Set (Fin (N + 1) → ℂ))
    (omega : Fin (N + 1) → Fin (N + 1) → ℂ)
    (h : DenseRange (fun z => nonorthogonalAddition S T omega z)) :
    DenseRange (fun z => additionMorphism S T z) := by
  change Dense (Set.range (fun z => additionMorphism S T z))
  apply h.mono
  rintro _ ⟨z, rfl⟩
  exact ⟨(nonorthogonalOpen S T omega).ι z, rfl⟩

end LeBrunSalamon.Construction.Lines.ConeDominance

end

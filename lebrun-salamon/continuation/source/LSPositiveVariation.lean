import RecompileExtensions

/-!
## First derivatives of sections vanishing at the fixed point

SOURCE: the final paragraph of `lines:suitable-pair`.

This proves the local-frame cancellation using the project's actual point
derivations. If all coefficients of a section in a subbundle frame vanish
at the point, differentiation of the frame contributes zero. The first
derivative therefore lies in the fiber spanned by the frame values.

The geometric inputs remain distinct: a fixed-value Hom tangent must be
identified with a section of `f*TX(-0)`; its projection to the trivial
quotient must be proved zero; and differentiation of the universal curve
must be identified with variation of the curve's node derivative. None
of those identifications is inferred from the algebra below alone.

STATUS: new source; compilation deferred until 35,000 integrated lines.
-/

noncomputable section
set_option autoImplicit false

open scoped BigOperators
open CategoryTheory AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySeven
open LeBrunSalamon.PhaseTwentyEight

namespace LeBrunSalamon.Construction.Lines.PositiveVariation

variable {A : Type*} [CommRing A] [Algebra ℂ A]
variable {ι κ : Type*} [Fintype κ]

/-- The vector of values of actual local coordinate functions. -/
def value (p : A →ₐ[ℂ] ℂ) (s : ι → A) : ι → ℂ := fun i => p (s i)

/-- First derivative in the supplied actual tangent vector. -/
def firstDerivative {p : A →ₐ[ℂ] ℂ} (D : Infinitesimal.Tangent A p)
    (s : ι → A) : ι → ℂ := fun i => D.val (s i)

/-- A section in a local frame, expressed in ambient coordinates. -/
def frameCombination (frame : κ → ι → A) (coefficient : κ → A) : ι → A :=
  fun i => ∑ j, frame j i * coefficient j

theorem value_frameCombination (p : A →ₐ[ℂ] ℂ)
    (frame : κ → ι → A) (coefficient : κ → A) :
    value p (frameCombination frame coefficient) =
      ∑ j, p (coefficient j) • value p (frame j) := by
  funext i
  simp only [value, frameCombination, map_sum, map_mul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

/-- The entire first derivative is retained until the coefficient values
are explicitly set to zero; in particular the moving-frame term is real. -/
theorem firstDerivative_frameCombination (p : A →ₐ[ℂ] ℂ)
    (D : Infinitesimal.Tangent A p)
    (frame : κ → ι → A) (coefficient : κ → A) :
    firstDerivative D (frameCombination frame coefficient) =
      (∑ j, D.val (coefficient j) • value p (frame j)) +
        (∑ j, p (coefficient j) • firstDerivative D (frame j)) := by
  funext i
  simp only [firstDerivative, value, frameCombination, map_sum,
    Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [D.property]
  ring

theorem value_eq_zero_of_coefficients_vanish (p : A →ₐ[ℂ] ℂ)
    (frame : κ → ι → A) (coefficient : κ → A)
    (hzero : ∀ j, p (coefficient j) = 0) :
    value p (frameCombination frame coefficient) = 0 := by
  rw [value_frameCombination]
  simp only [hzero, zero_smul, Finset.sum_const_zero]

/-- This is the precise cancellation used for a section of `P_f(-0)`:
only values of the frame, not its derivative, survive at the node. -/
theorem firstDerivative_of_coefficients_vanish (p : A →ₐ[ℂ] ℂ)
    (D : Infinitesimal.Tangent A p)
    (frame : κ → ι → A) (coefficient : κ → A)
    (hzero : ∀ j, p (coefficient j) = 0) :
    firstDerivative D (frameCombination frame coefficient) =
      ∑ j, D.val (coefficient j) • value p (frame j) := by
  rw [firstDerivative_frameCombination]
  simp only [hzero, zero_smul, Finset.sum_const_zero, add_zero]

/-- An actual frame has injective coefficient-to-fiber evaluation, so
the vanishing section value implies vanishing of every coefficient.
No choice of a splitting of the ambient bundle is required here. -/
theorem coefficients_vanish_of_value_zero (p : A →ₐ[ℂ] ℂ)
    (frame : κ → ι → A) (coefficient : κ → A)
    (hframe : Function.Injective (fun c : κ → ℂ => ∑ j, c j • value p (frame j)))
    (hzero : value p (frameCombination frame coefficient) = 0) :
    ∀ j, p (coefficient j) = 0 := by
  have hcoeff : (fun j => p (coefficient j)) = (0 : κ → ℂ) := by
    apply hframe
    change (∑ j, p (coefficient j) • value p (frame j)) =
      ∑ j, (0 : ℂ) • value p (frame j)
    rw [← value_frameCombination, hzero]
    simp
  intro j
  exact congrFun hcoeff j

theorem firstDerivative_mem_of_coefficients_vanish (p : A →ₐ[ℂ] ℂ)
    (D : Infinitesimal.Tangent A p)
    (frame : κ → ι → A) (coefficient : κ → A)
    (W : Submodule ℂ (ι → ℂ))
    (hframe : ∀ j, value p (frame j) ∈ W)
    (hzero : ∀ j, p (coefficient j) = 0) :
    firstDerivative D (frameCombination frame coefficient) ∈ W := by
  rw [firstDerivative_of_coefficients_vanish p D frame coefficient hzero]
  exact W.sum_mem (fun j _ => W.smul_mem _ (hframe j))

/-- The formulation for a section which itself vanishes at the point. -/
theorem firstDerivative_mem_of_value_zero (p : A →ₐ[ℂ] ℂ)
    (D : Infinitesimal.Tangent A p)
    (frame : κ → ι → A) (coefficient : κ → A)
    (W : Submodule ℂ (ι → ℂ))
    (hframe : ∀ j, value p (frame j) ∈ W)
    (hinj : Function.Injective (fun c : κ → ℂ => ∑ j, c j • value p (frame j)))
    (hzero : value p (frameCombination frame coefficient) = 0) :
    firstDerivative D (frameCombination frame coefficient) ∈ W :=
  firstDerivative_mem_of_coefficients_vanish p D frame coefficient W hframe
    (coefficients_vanish_of_value_zero p frame coefficient hinj hzero)

/-- Transport to the target fiber uses the stated linear coordinate map;
the subspace being tested remains a subspace of that original fiber. -/
theorem transported_firstDerivative_mem
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (p : A →ₐ[ℂ] ℂ) (D : Infinitesimal.Tangent A p)
    (frame : κ → ι → A) (coefficient : κ → A)
    (transport : (ι → ℂ) →ₗ[ℂ] V) (W : Submodule ℂ V)
    (hframe : ∀ j, transport (value p (frame j)) ∈ W)
    (hzero : ∀ j, p (coefficient j) = 0) :
    transport (firstDerivative D (frameCombination frame coefficient)) ∈ W :=
  firstDerivative_mem_of_coefficients_vanish p D frame coefficient
    (W.comap transport) hframe hzero

/-- The same calculation lands in the original endpoint-fixed section
space used by `SuitablePair`; it introduces no replacement definition of
the positive subspace. The transport and frame comparison are explicit. -/
theorem firstDerivative_mem_positiveNodeSpace
    {n : ℕ} {X : ContactFanoManifold n} (f : FreeLine X)
    (x : ComplexPoint X.variety) (hx : marking.map ≫ f.curve.map = x.map)
    (p : A →ₐ[ℂ] ℂ) (D : Infinitesimal.Tangent A p)
    (frame : κ → ι → A) (coefficient : κ → A)
    (transport : (ι → ℂ) →ₗ[ℂ] TangentFiber X.variety x)
    (hframe : ∀ j, transport (value p (frame j)) ∈ positiveNodeSpace f x hx)
    (hzero : ∀ j, p (coefficient j) = 0) :
    transport (firstDerivative D (frameCombination frame coefficient)) ∈
      positiveNodeSpace f x hx :=
  transported_firstDerivative_mem p D frame coefficient transport
    (positiveNodeSpace f x hx) hframe hzero

end LeBrunSalamon.Construction.Lines.PositiveVariation

end

import LSFormalTraitModel

/-!
# Global functions over a normal affine base

The input below is a generic published corollary, independently reviewed
against Stacks 0BCM, 0BUG(8), and 0AY8.  Flatness and integrality of the
generic fibre imply that the total space is integral.  Proper geometric
integrality gives only the base field as generic global functions.  The
normal-base Stein-factorization lemma then identifies the canonical map
on global functions.  No curve, contact form, or conic model occurs in
the statement.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace LeBrunSalamon.StandardInputs

/-- Stacks 0BCM, 0BUG(8), and 0AY8, specialized to the actual canonical
fraction-field point of an integrally closed domain. -/
theorem proper_flat_normal_generic_globalFunctions
    (R : CommRingCat) [IsDomain R] [IsIntegrallyClosed R]
    {C : Scheme} (pi : C ⟶ Spec R) [IsProper pi] [Flat pi]
    [GeometricallyIntegral (pullback.snd pi
      (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))] :
    Function.Bijective pi.appTop := by
  sorry

end LeBrunSalamon.StandardInputs

end

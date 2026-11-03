import RecompileBasePart04

/-!
# Exactness of tensoring with a locally free sheaf

The single input in this file is the generic theorem explicitly stated in
EGA I, chapitre 0, (5.4.1), printed page 48.  The fixed finite rank condition
is a specialization of the published locally free hypothesis.  The tensor
functor is the project's already-constructed sheaf tensor product, with
its proved bilinear universal property.  No thickening, family, curve,
contact structure, or Hom-vanishing conclusion occurs in this statement.

Primary source: A. Grothendieck, with J. Dieudonné, Éléments de géométrie
algébrique I, Publications Mathématiques de l'IHÉS 4 (1960), 5–228.
Original scan: https://www.numdam.org/item/PMIHES_1960__4__5_0.pdf
Primary scan mirror:
https://webusers.imj-prg.fr/~leila.schneps/grothendieckcircle/EGA/EGAI.pdf
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseTwentyFive

namespace LeBrunSalamon.PublishedInputs.TensorExactness

instance tensorLeft_preservesZeroMorphisms {X : Scheme} (E : OModule X) :
    (tensorLeftFunctor E).PreservesZeroMorphisms where
  map_zero F G := by
    change tensorMap (𝟙 E) (0 : F ⟶ G) = 0
    apply ((tensorPresentation E F).universal _).1
    apply sheafBilinearMap_ext
    intro U u v
    change (tensorMap (𝟙 E) (0 : F ⟶ G)).app U
      ((tensorPresentation E F).pair.apply U u v) = 0
    rw [tensorMap_apply]
    simp

/-- **Published input (exact generic specialization).** A locally free
sheaf tensored with a short exact sequence gives a short exact sequence.
EGA I, chapitre 0, (5.4.1), printed p. 48. -/
theorem locallyFree_tensor_shortExact {X : Scheme} {r : ℕ}
    (F : OModule X) (hF : IsLocallyFreeOfRank F r)
    (S : ShortComplex (OModule X)) (hS : S.ShortExact) :
    (S.map (tensorLeftFunctor F)).ShortExact := by
  sorry

end LeBrunSalamon.PublishedInputs.TensorExactness
end

import RecompileExtensionsPart01

/-!
# Transport of an actual affine frame along a sheaf isomorphism

The section calculation is proved for arbitrary sheaves before any concrete
projective-line or tensor-power construction is substituted.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.Core
open LeBrunSalamon.Core.ExternalTensorCoordinates

namespace LeBrunSalamon.FrameTransport

/-- The actual maps on sections induced by an isomorphism of module sheaves. -/
def sectionsLinearEquiv {Y : Scheme} {E F : OModule Y}
    (e : E ≅ F) (V : Y.Opens) :
    SectionsOn E V ≃ₗ[RingSections Y V] SectionsOn F V where
  toFun := Scheme.Modules.Hom.app e.hom V
  invFun := Scheme.Modules.Hom.app e.inv V
  left_inv v := congrArg (fun k : E ⟶ E => Scheme.Modules.Hom.app k V v) e.hom_inv_id
  right_inv v := congrArg (fun k : F ⟶ F => Scheme.Modules.Hom.app k V v) e.inv_hom_id
  map_add' v w := (Scheme.Modules.Hom.app e.hom V).hom.map_add v w
  map_smul' c v := Scheme.Modules.Hom.app_smul e.hom c v

/-- An affine frame transported through the specified sheaf isomorphism. -/
def frame {Y : Scheme} {L : LineBundle Y} {M : OModule Y}
    (e : L.sheaf ≅ M) (V : Y.Opens) (hV : IsAffineOpen V)
    (c : SectionsOn M V ≃ₗ[RingSections Y V] RingSections Y V) :
    AffineLineFrame L where
  openSet := V
  isAffine := hV
  coefficient := (sectionsLinearEquiv e V).trans c

/-- The transported coefficient is the coefficient of the same composed
section, restricted to the same open. -/
theorem frame_localCoefficient {Y : Scheme} {L : LineBundle Y} {M : OModule Y}
    (e : L.sheaf ≅ M) (V : Y.Opens) (hV : IsAffineOpen V)
    (c : SectionsOn M V ≃ₗ[RingSections Y V] RingSections Y V)
    (a : AlgebraicSection L.sheaf) :
    (frame e V hV c).localCoefficient a =
      c (M.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op
        (sectionValue (a ≫ e.hom))) := by
  change c (Scheme.Modules.Hom.app e.hom V
    (Scheme.Modules.Hom.app a V (1 : RingSections Y V))) = _
  exact congrArg c (section_app_one (a ≫ e.hom) V)

end LeBrunSalamon.FrameTransport

end

import LSPlaneQuadraticEquation
import LSPlaneConicPresentation

/-! The literal quadratic zero scheme represents the generating
three-tuples with the split conic equation.  The proof uses the normalized
projective quotient and the actual zero-scheme universal property.
No admission. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.Skeleton
open LeBrunSalamon.Refinement
open LeBrunSalamon.Construction

namespace LeBrunSalamon.PlaneConicZeroPresentation

variable (R : Type) [CommRing R] (a : R)

abbrev source := PlaneQuadratic.ZeroScheme R (PlaneQuadratic.split R a)
abbrev inclusion : source R a ⟶ PlaneQuadratic.Plane R :=
  PlaneQuadratic.inclusion R (PlaneQuadratic.split R a)
abbrev projection : source R a ⟶ Spec (CommRingCat.of R) :=
  PlaneQuadratic.projection R (PlaneQuadratic.split R a)

def line : LineBundle (source R a) :=
  pullbackLine (inclusion R a) (StandardTautological.line R 2)

def coordinate (i : Fin 3) : AlgebraicSection (line R a).sheaf :=
  pullSection (inclusion R a) (StandardTautological.coordinate R 2 i)

def parameter : RingSections (Spec (CommRingCat.of R)) ⊤ :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).inv a

theorem generates : TupleGenerates (line R a) (coordinate R a) :=
  StandardProjectiveBaseChange.pull_generates
    (StandardTautological.coordinate R 2) (StandardTautological.generates R 2) (inclusion R a)

theorem equation : PlaneConicPresentation.Equation (parameter R a)
    (projection R a) (line R a) (coordinate R a) := by
  exact (PlaneQuadraticEquation.split_zero_iff R (inclusion R a) (projection R a) rfl
    (line R a) (coordinate R a) (Iso.refl _) (fun i => Category.comp_id _) a).mp
      (PlaneQuadratic.zero_equation R (PlaneQuadratic.split R a))

/-- The map to P² determined by a tuple factors through the literal
quadratic ideal, and the selected hyperplane line is preserved. -/
def presentation : PlaneConicPresentation.Presentation
    (Spec (CommRingCat.of R)) (parameter R a) where
  source := source R a
  projection := projection R a
  line := line R a
  coordinate := coordinate R a
  generates := generates R a
  equation := equation R a
  universal := by
    intro T s L b hb heq
    obtain ⟨f, ⟨e, he⟩, funiq⟩ := (StandardTautological.chosen R 2).universal
      T s L.sheaf L.locallyFree b hb
    have hfzero : pullSection f.val
        (PlaneQuadratic.sectionOf R (PlaneQuadratic.split R a)) = 0 :=
      (PlaneQuadraticEquation.split_zero_iff R f.val s f.property L b e he a).mpr heq
    obtain ⟨g, hg, guniq⟩ := PlaneQuadratic.universal R (PlaneQuadratic.split R a) f.val hfzero
    have hgbase : g ≫ projection R a = s := by
      change g ≫ (inclusion R a ≫ StandardTautological.toSpec R 2) = s
      rw [← Category.assoc, hg]
      exact f.property
    let c : pullbackModule g (line R a).sheaf ≅ L.sheaf :=
      compositionPullback g (inclusion R a) f.val hg (StandardTautological.line R 2).sheaf ≪≫ e
    have hc (i : Fin 3) : pullSection g (coordinate R a i) ≫ c.hom = b i := by
      change pullSection g (pullSection (inclusion R a)
        (StandardTautological.coordinate R 2 i)) ≫
        ((compositionPullback g (inclusion R a) f.val hg
          (StandardTautological.line R 2).sheaf).hom ≫ e.hom) = _
      rw [← Category.assoc, compositionPullback_sections]
      exact he i
    refine ⟨⟨g, hgbase⟩, ⟨c, hc⟩, ?_⟩
    intro k hk
    obtain ⟨d, hd⟩ := hk
    have hkbase : (k.val ≫ inclusion R a) ≫ StandardTautological.toSpec R 2 = s := by
      rw [Category.assoc]
      exact k.property
    let v : pullbackModule (k.val ≫ inclusion R a)
        (StandardTautological.line R 2).sheaf ≅ L.sheaf :=
      (compositionPullback k.val (inclusion R a) (k.val ≫ inclusion R a) rfl
        (StandardTautological.line R 2).sheaf).symm ≪≫ d
    have hv (i : Fin 3) : pullSection (k.val ≫ inclusion R a)
        (StandardTautological.coordinate R 2 i) ≫ v.hom = b i := by
      rw [← compositionPullback_sections k.val (inclusion R a)
        (k.val ≫ inclusion R a) rfl]
      let z := compositionPullback k.val (inclusion R a) (k.val ≫ inclusion R a) rfl
        (StandardTautological.line R 2).sheaf
      change (pullSection k.val (coordinate R a i) ≫ z.hom) ≫ (z.inv ≫ d.hom) = _
      rw [Category.assoc, Iso.hom_inv_id_assoc]
      exact hd i
    have hf := congrArg Subtype.val (funiq ⟨k.val ≫ inclusion R a, hkbase⟩ ⟨v, hv⟩)
    apply Subtype.ext
    exact guniq k.val hf

end LeBrunSalamon.PlaneConicZeroPresentation
end

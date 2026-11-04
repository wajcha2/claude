import LSSectionRepresentability

/-! Affineness of the actual scheme representing sections of a finite
locally free sheaf. The generic published input provides an affine
representative. The given universal section is converted into a genuine
representation, and Yoneda constructs its isomorphism to that affine
representative over the same base. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.Skeleton
open LeBrunSalamon.Construction

namespace LeBrunSalamon.PublishedInputs.SectionRepresentability

/-- EGA IV(4), (18.5.1), printed p125 identifies the section functor
with V(E dual). The associated vector bundle is the relative spectrum
of the symmetric algebra (Stacks27.6.1, tag01M1); the relative spectrum
has affine inverse images of all affine base opens (Stacks27.3.4(1),
tag01LP), and represents the stated functor (Stacks Lemma27.4.4,
tag01LV, with Definition27.4.5,tag01LW).
This statement gives only an affine representing object for the generic
section functor. Its comparison with any project-chosen total space is
proved below, with the actual map over the base retained.
Primary sources:
https://numdam.org/item/10.1007/BF02732123.pdf
https://stacks.math.columbia.edu/tag/01M1
https://stacks.math.columbia.edu/tag/01LP
https://stacks.math.columbia.edu/tag/01LV
https://stacks.math.columbia.edu/tag/01LW -/
theorem finiteFree_affine
    {Z : Scheme.{0}} {E : OModule Z} {r : ℕ} (hE : IsLocallyFreeOfRank E r) :
    ∃ V : Over Z, IsAffineHom V.hom ∧
      Nonempty ((LeBrunSalamon.SectionRepresentability.sectionFunctor E).RepresentableBy V) := by
  sorry

end LeBrunSalamon.PublishedInputs.SectionRepresentability

namespace LeBrunSalamon.SectionRepresentability

/-- The literal all-test-scheme universal property supplies a natural
representation of the already defined section functor. -/
def representation_of_data
    {Z : Scheme.{0}} (E : OModule Z) {Y : Scheme.{0}} (p : Y ⟶ Z)
    (τ : AlgebraicSection (pullbackModule p E))
    (hτ : ∀ (T : Scheme.{0}) (f : T ⟶ Z),
      Function.Bijective (fun h : {h : T ⟶ Y // h ≫ p = f} =>
        pullSection h.val τ ≫ (compositionPullback h.val p f h.property E).hom)) :
    (sectionFunctor E).RepresentableBy (Over.mk p) where
  homEquiv {X} :=
    (overHomEquiv (Over.mk p) X.left X.hom).symm.trans
      (Equiv.ofBijective (fun h : {h : X.left ⟶ Y // h ≫ p = X.hom} =>
        pullSection h.val τ ≫ (compositionPullback h.val p X.hom h.property E).hom)
        (hτ X.left X.hom))
  homEquiv_comp f g := by
    change sectionPullback E (f ≫ g) τ =
      sectionPullback E f (sectionPullback E g τ)
    exact (sectionPullback_comp E f g τ).symm

/-- Affineness is transported through the actual over-base Yoneda
isomorphism. The conclusion concerns the original map p, not the newly
chosen affine representative. -/
theorem affine_of_data
    {Z : Scheme.{0}} {E : OModule Z} {r : ℕ} (hE : IsLocallyFreeOfRank E r)
    {Y : Scheme.{0}} (p : Y ⟶ Z)
    (τ : AlgebraicSection (pullbackModule p E))
    (hτ : ∀ (T : Scheme.{0}) (f : T ⟶ Z),
      Function.Bijective (fun h : {h : T ⟶ Y // h ≫ p = f} =>
        pullSection h.val τ ≫ (compositionPullback h.val p f h.property E).hom)) :
    IsAffineHom p := by
  obtain ⟨V, hV, ⟨repV⟩⟩ := PublishedInputs.SectionRepresentability.finiteFree_affine hE
  let rep := representation_of_data E p τ hτ
  let e : Over.mk p ≅ V := rep.uniqueUpToIso repV
  let s : Y ≅ V.left := (Over.forget Z).mapIso e
  letI : IsAffineHom V.hom := hV
  letI : IsIso s.hom := s.isIso_hom
  have h : IsAffineHom (s.hom ≫ V.hom) := inferInstance
  have he : s.hom ≫ V.hom = p := e.hom.w
  exact (congrArg IsAffineHom he).mp h

end LeBrunSalamon.SectionRepresentability
end

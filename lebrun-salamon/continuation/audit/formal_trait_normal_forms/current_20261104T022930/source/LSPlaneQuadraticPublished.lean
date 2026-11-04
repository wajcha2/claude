import LSPlaneQuadratic

/-! Generic published inputs for normalized plane quadratics.
No family embedding, chosen-line comparison, or formal-trait model is
included in these statements. The importing project translations must
construct the actual quadratic and all required fibre identifications.
These off-graph candidate signatures await native/source acceptance. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix LeBrunSalamon.PhaseTwentyEight

namespace LeBrunSalamon.PlaneQuadratic

def closedPoint (A : Type) [CommRing A] [IsLocalRing A] :
    Spec (CommRingCat.of (IsLocalRing.ResidueField A)) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)))

abbrev ClosedFibre (A : Type) [CommRing A] [IsLocalRing A] (q : Coefficients A) : Scheme :=
  pullback (projection A q) (closedPoint A)

def closedProjection (A : Type) [CommRing A] [IsLocalRing A] (q : Coefficients A) :
    ClosedFibre A q ⟶ Spec (CommRingCat.of (IsLocalRing.ResidueField A)) :=
  pullback.snd (projection A q) (closedPoint A)

end LeBrunSalamon.PlaneQuadratic

namespace LeBrunSalamon.PublishedInputs.ProjectiveSpace

/-- **Exact generic projective-space section computation.** Stacks30.8.1
(01XS) identifies H⁰(P²_A,O(2)) with the degree-two homogeneous polynomials
over every ring A. The paragraph preceding the lemma specifies the
monomial basis. For three variables that basis is x²,y²,z²,yz,zx,xy;
`sectionOf` is precisely their coefficient-to-section map. The tensor
realization O(1)⊗O(1)=O(2) is the normalized multiplication construction
of Stacks27.10.3 (01MM). Algebraic sections and H⁰ are identified by the
already proved `sectionValue_bijective` API.

No special-fibre geometry or family classification is asserted here.
Primary source: https://stacks.math.columbia.edu/tag/01XS . -/
theorem quadraticSections_bijective (A : Type) [CommRing A] :
    Function.Bijective (PlaneQuadratic.sectionOf A) := by
  sorry

end LeBrunSalamon.PublishedInputs.ProjectiveSpace

namespace LeBrunSalamon.PublishedInputs.ConicQuadratic

/-- **Generic reduced-fibre quadratic normal form.** Tanaka,
*Discriminant divisors for conic bundles*, QJM75(2024), Corollary2.13(2),
printed p12, with its primitive-coefficient criterion Proposition2.9(4),
printed p10. Algebraically closed residue field implies the separably
closed residue-field condition in “strictly henselian”. No regularity of
the total hypersurface is assumed. The conclusion is the actual GL₃
substitution of the defining polynomial and the exact singular-fibre
criterion, not an isomorphism class of unpolarized curves.

`ZeroScheme` is the literal normalized quadratic zero subscheme; its
graph-fibre-product construction already retains its nilpotents. The
three source hypotheses are: noetherian henselian local base, residue
characteristic different from2, and reduced closed fibre. `Primitive`
is exactly Proposition2.9(4)'s unit-coefficient characterization of a
conic on P²_A. The stronger algebraically-closed residue assumption is
a generic specialization of the published hypothesis.

Primary source: https://arxiv.org/pdf/2308.08119 . -/
theorem reduced_normalForm (A : Type) [CommRing A] [IsNoetherianRing A]
    [HenselianLocalRing A] [IsAlgClosed (IsLocalRing.ResidueField A)]
    (h2 : (2 : IsLocalRing.ResidueField A) ≠ 0)
    (q : PlaneQuadratic.Coefficients A) (hq : PlaneQuadratic.Primitive A q)
    (hreduced : AlgebraicGeometry.IsReduced (PlaneQuadratic.ClosedFibre A q)) :
    ∃ (M : (Matrix (Fin 3) (Fin 3) A)ˣ) (c : A),
      PlaneQuadratic.transformed A q M =
        PlaneQuadratic.polynomial A (PlaneQuadratic.diagonal A c) ∧
      (c ∈ IsLocalRing.maximalIdeal A ↔
        ¬ Smooth (PlaneQuadratic.closedProjection A q)) := by
  sorry

/-- **Generic smooth-fibre quadratic normal form.** The smooth case is
Tanaka Corollary2.13(3), with the same normalized polynomial and primitive
coefficient criterion as above. Its conclusion is the GL₃ substitution
giving x²+y²+z². The project-specific smooth P1 model is not asserted. -/
theorem smooth_normalForm (A : Type) [CommRing A] [IsNoetherianRing A]
    [HenselianLocalRing A] [IsAlgClosed (IsLocalRing.ResidueField A)]
    (h2 : (2 : IsLocalRing.ResidueField A) ≠ 0)
    (q : PlaneQuadratic.Coefficients A) (hq : PlaneQuadratic.Primitive A q)
    (hsmooth : Smooth (PlaneQuadratic.closedProjection A q)) :
    ∃ M : (Matrix (Fin 3) (Fin 3) A)ˣ,
      PlaneQuadratic.transformed A q M =
        PlaneQuadratic.polynomial A (PlaneQuadratic.diagonal A 1) := by
  sorry

/-- **Exact field discriminant criterion.** Tanaka Proposition3.12(1),
printed p23: a nonzero homogeneous ternary quadratic defines a smooth
conic precisely when its displayed discriminant is nonzero. This works
in arbitrary characteristic, with the same coefficient convention used
in Definition3.1. It is applied to the generic fibre only after the
actual equation/base-change comparison has been proved. -/
theorem smooth_iff_discriminant_ne_zero (K : Type) [Field K]
    (q : PlaneQuadratic.Coefficients K) (hq : PlaneQuadratic.polynomial K q ≠ 0) :
    Smooth (PlaneQuadratic.projection K q) ↔ PlaneQuadratic.discriminant K q ≠ 0 := by
  sorry

end LeBrunSalamon.PublishedInputs.ConicQuadratic
end

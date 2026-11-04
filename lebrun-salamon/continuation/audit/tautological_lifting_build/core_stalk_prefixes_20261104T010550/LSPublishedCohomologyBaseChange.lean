import LSCohomologyHypotheses
import LSCanonicalSectionBaseChange
import LSYonedaClassesRepresented
import LSResidueFieldPresentation
import RecompileExtensionCore

/-!
Exact published boundaries for the canonical H0 base-change theorem.

The three generic inputs are deliberately separated:
* coherence iff finite presentation on a locally Noetherian scheme
  (Stacks 30.9.1, 01XZ);
* Ext1(O,E) = H1(E) on a ringed space (Stacks 20.5.1, 0B3A);
* the canonical H0 base-change isomorphism when fibre H1 vanishes
  (Robert, Appendix A.1, Lemma A.1.1, third corollary bullet, p.81).

The public tuple lift below is a proof through the actual original section
map. Its relative-flatness hypothesis is explicitly a condition on actual
stalk modules; a local-frame proof is supplied in LSLineStalkFlat, not hidden in
the cohomology input. Off-graph candidate, native verification pending.
-/

noncomputable section
set_option autoImplicit false
set_option maxErrors 1
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirtyTwo

namespace LeBrunSalamon.PublishedInputs.Cohomology

/-- Stacks 30.9.1 (01XZ), equivalence of clauses (1) and (3). `Coherent`
is the actual local finite-kernel definition, and `IsFinitePresentation`
is Mathlib's local finite-generators-and-relations predicate.
https://stacks.math.columbia.edu/tag/01XZ -/
theorem coherent_iff_finitePresentation {X : Scheme} [IsLocallyNoetherian X]
    (E : OModule X) : CohomologyHypotheses.Coherent E ↔ E.IsFinitePresentation := by
  sorry

/-- Stacks 20.5.1 (0B3A): Ext1(O,E) is canonically H1(E). We retain only
the resulting bijection, since the application is subsingletonness;
no selected degree-zero restriction map is inferred from this equivalence.
Both sides are the actual derived Ext/sheaf-cohomology groups.
https://stacks.math.columbia.edu/tag/0B3A -/
theorem ext1_unit_h1 {X : Scheme} (E : OModule X) :
    Nonempty (Ext (structureModule X) E 1 ≃ CohomologyHypotheses.H1 E) := by
  sorry

/-- Damien Robert, Theory of abelian varieties and their moduli spaces,
Appendix A.1, Lemma A.1.1 and its third corollary bullet, printed p.81
(PDF p.87, proof p.82), draft stamp 2023-03-07. Proper morphism between
Noetherian schemes, coherent base-flat sheaf, and vanishing H1 of the
specified fibre imply the canonical beta0 is an isomorphism.

Here the base is the spectrum of an arbitrary Noetherian local ring and
the specified fibre is supplied by an actual cartesian square. The map
is defined before this input and normalized by `canonicalMap_tmul`; its
source is H0(E) tensor the literal residue field. This is the local affine
form of beta0, not an arbitrary equivalence between two section spaces.
https://www.math.u-bordeaux.fr/~damienrobert/pro/publications/books/avtheory.pdf -/
theorem h0_residue_baseChange_bijective
    {R : Type} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {X Y : Scheme} [IsNoetherian X]
    (sX : X ⟶ Spec (CommRingCat.of R)) [IsProper sX]
    (p : Y ⟶ X) (q : Y ⟶ Spec (CommRingCat.of (IsLocalRing.ResidueField R)))
    (hsq : IsPullback p q sX (Spec.map
      (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R)))))
    (E : OModule X) (hcoh : CohomologyHypotheses.Coherent E)
    (hflat : CohomologyHypotheses.RelativelyFlat sX E)
    (h1 : Subsingleton (CohomologyHypotheses.H1 (pullbackModule p E))) :
    Function.Bijective (CanonicalSectionBaseChange.canonicalMap sX p q hsq.w E) := by
  sorry

end LeBrunSalamon.PublishedInputs.Cohomology

namespace LeBrunSalamon.CohomologyBaseChange

/-- The project's original Yoneda condition agrees with actual H1
vanishing. Ext classes are represented by an actual pullback extension
using enough injectives, and that comparison is a Lean proof. -/
theorem firstCohomology_iff_h1 {X : Scheme} (E : OModule X) :
    HasVanishingFirstCohomology E ↔ Subsingleton (CohomologyHypotheses.H1 E) := by
  let e := (PublishedInputs.Cohomology.ext1_unit_h1 E).some
  constructor
  · intro h
    have hs : Subsingleton (Ext (structureModule X) E 1) :=
      (YonedaExtensionSplitting.allExtensionsSplit_iff_ext1_subsingleton
        (structureModule X) E).mp h
    exact ⟨fun a b => e.symm.injective (hs.elim _ _)⟩
  · intro h
    have hs : Subsingleton (Ext (structureModule X) E 1) :=
      ⟨fun a b => e.injective (h.elim _ _)⟩
    exact (YonedaExtensionSplitting.allExtensionsSplit_iff_ext1_subsingleton
      (structureModule X) E).mpr hs

/-- The actual finite-rank witness supplies coherence through the proved
finite presentation and the isolated exact Noetherian criterion. -/
theorem coherent_of_locallyFreeRank {X : Scheme} [IsLocallyNoetherian X]
    {E : OModule X} {r : ℕ} (hE : IsLocallyFreeOfRank E r) :
    CohomologyHypotheses.Coherent E :=
  (PublishedInputs.Cohomology.coherent_iff_finitePresentation E).mpr
    (CohomologyHypotheses.finitePresentation_of_locallyFreeRank hE)

variable {R : Type} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
variable {X Y : Scheme} (sX : X ⟶ Spec (CommRingCat.of R)) [IsProper sX]
  (p : Y ⟶ X) (q : Y ⟶ Spec (CommRingCat.of (IsLocalRing.ResidueField R)))
  (hsq : IsPullback p q sX (Spec.map
    (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R)))))

/-- Actual canonical H0 base change with the original rank and H1
hypotheses. Relative flatness remains an explicit actual-stalk hypothesis
until its local-frame adapter has been proved. -/
theorem bundle_residue_baseChange {r : ℕ} (E : AlgebraicVectorBundle X r)
    (hflat : CohomologyHypotheses.RelativelyFlat sX E.sheaf)
    (h1 : HasVanishingFirstCohomology (pullbackModule p E.sheaf)) :
    Function.Bijective
      (CanonicalSectionBaseChange.canonicalMap sX p q hsq.w E.sheaf) := by
  letI : IsNoetherian X := CohomologyHypotheses.noetherian_of_proper_to_spec sX
  exact PublishedInputs.Cohomology.h0_residue_baseChange_bijective sX p q hsq E.sheaf
    (coherent_of_locallyFreeRank E.locallyFree) hflat
    ((firstCohomology_iff_h1 _).mp h1)

/-- Lift the supplied finite tuple of actual algebraic-section morphisms.
The number of sections and their chosen special-fibre values are retained.
No embedding theorem is asserted or admitted by this adapter. -/
theorem lift_bundle_tuple {r : ℕ} (E : AlgebraicVectorBundle X r)
    (hflat : CohomologyHypotheses.RelativelyFlat sX E.sheaf)
    (h1 : HasVanishingFirstCohomology (pullbackModule p E.sheaf))
    (n : ℕ) (a : Fin n → AlgebraicSection (pullbackModule p E.sheaf)) :
    ∃ b : Fin n → AlgebraicSection E.sheaf, ∀ i, pullSection p (b i) = a i :=
  CanonicalSectionBaseChange.lift_finite_tuple sX p q hsq.w E.sheaf
    (bundle_residue_baseChange sX p q hsq E hflat h1).surjective n a

end LeBrunSalamon.CohomologyBaseChange

end

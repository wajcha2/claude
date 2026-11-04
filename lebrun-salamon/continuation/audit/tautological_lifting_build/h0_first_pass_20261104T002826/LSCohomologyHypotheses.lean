import RecompileBasePart05B

/-!
Explicit hypotheses for the cohomology-and-base-change theorem.
The Noetherian conclusion and finite presentation of a bundle are actual
proofs from the project's original finite-rank local generator data.
Relative flatness is stated on the actual module stalk with scalars
restricted through the actual scheme stalk morphism. No opaque name is
used in place of these hypotheses.

Off-graph candidate; no theorem is admitted.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree

namespace LeBrunSalamon.CohomologyHypotheses

/-- The scheme Noetherian hypothesis follows from properness over the
actual spectrum of a Noetherian ring. -/
theorem noetherian_of_proper_to_spec {R : Type} [CommRing R] [IsNoetherianRing R]
    {X : Scheme} (p : X ⟶ Spec (CommRingCat.of R)) [IsProper p] :
    IsNoetherian X := by
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  exact ⟨⟩

/-- The original rank witness supplies a finite presentation: the local
generators are finite and, in their free frames, there are no relations. -/
theorem finitePresentation_of_locallyFreeRank {X : Scheme} {E : OModule X} {r : ℕ}
    (hE : IsLocallyFreeOfRank E r) : E.IsFinitePresentation := by
  classical
  obtain ⟨q, hq, hr⟩ := hE
  letI := hq
  let d := q.quasiCoherentData
  have hd (i : d.I) : (d.presentation i).IsFinite := by
    have hfinite : Finite (q.generators i).I :=
      Finite.of_equiv (Fin r) (hr i).some.symm
    letI := hfinite
    refine { isFiniteType_generators := ?_, isFiniteType_relations := ?_ }
    · exact ⟨hfinite⟩
    · exact ⟨inferInstanceAs (Finite (ULift Empty))⟩
  refine ⟨⟨d.shrink, ?_⟩⟩
  exact ⟨fun i => hd i.2.choose⟩

/-- The literal underlying additive sheaf of the supplied O-module. -/
def abelianSheaf {X : Scheme} (E : OModule X) :=
  (SheafOfModules.toSheaf X.ringCatSheaf).obj E

/-- The usual coherence predicate: finite generation, and finite generation
of the kernel of every map from a finite free sheaf on every open. -/
def Coherent {X : Scheme} (E : OModule X) : Prop :=
  E.IsFiniteType ∧ ∀ (U : X.Opens) (n : ℕ)
    (f : SheafOfModules.free (R := X.ringCatSheaf.over U) (Fin n) ⟶ E.over U),
      (kernel f).IsFiniteType

/-- Actual derived sheaf cohomology, not a dimension token. -/
abbrev H1 {X : Scheme} (E : OModule X) : Type :=
  CategoryTheory.Sheaf.H (abelianSheaf E) 1

/-- Relative flatness at each actual stalk. The scalar action is exactly
the one induced by `p.stalkMap`; it is not an arbitrary chosen R-module. -/
def RelativelyFlat {X S : Scheme} (p : X ⟶ S) (E : OModule X) : Prop :=
  ∀ x : X,
    letI : Module (S.presheaf.stalk (p x)) (E.presheaf.stalk x) :=
      Module.compHom (E.presheaf.stalk x) (p.stalkMap x).hom
    Module.Flat (S.presheaf.stalk (p x)) (E.presheaf.stalk x)

end LeBrunSalamon.CohomologyHypotheses

end

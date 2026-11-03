import LSRelativeGenericSmoothness

/-!
## Bounded degree loci in the full Hom scheme

The degree locus is an actual open-and-closed subscheme of the already
supplied all-test-scheme Hom presentation. Freeness and a fixed marking
will be imposed by ordinary open restriction and scheme-theoretic fibre.

Source preparation only; compilation remains deferred to the final check.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseSeven LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentySix LeBrunSalamon.PhaseTwentySeven
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction

namespace LeBrunSalamon.Construction.Lines.HomDegree

/-- The actual open-and-closed degree piece in a full Hom scheme. -/
structure Open (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {d : ℕ} (X : SmoothProperComplexVariety d)
    (H : HomSpacePresentation P X) (L : LineBundle X.scheme) (e : ℤ) where
  openSet : H.parameter.Opens
  closed : IsClosed (openSet : Set H.parameter)
  finiteType : LocallyOfFiniteType (openSet.ι ≫ H.toC)
  quasiCompact : QuasiCompact (openSet.ι ≫ H.toC)
  membership : ∀ t : PointsOver ComplexBase (𝟙 ComplexBase) H.parameter H.toC,
    t.val (IsLocalRing.closedPoint ℂ) ∈ openSet ↔
      projectiveLineDegree P p (pullbackLine (H.mapAt P t) L) = e

namespace StandardInputs

/-- Fixed-degree Hom boundedness, as the graph-Hilbert-polynomial
corollary of Grothendieck, Bourbaki exp.221, Theorem 3.2 and Section 4(c).
The full all-test-scheme universal property is supplied by `H`.

The exposition first restricts to locally Noetherian tests for simplicity;
finite-presentation limit compatibility (Stacks 01ZM) extends the same
representation to arbitrary tests. For a very ample power L^m, the graph
polynomial for O(1) external-tensor L^m is (1+m*e)*t+1. Thus its fixed
polynomial piece is the claimed open-and-closed finite-type subscheme.
This input contains no contact, freeness, direction, or dominance claim. -/
theorem degree_open (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {d : ℕ} (X : SmoothProperComplexVariety d) (hX : HasProjectiveEmbedding X)
    (H : HomSpacePresentation P X) (L : LineBundle X.scheme)
    (hL : IsAmpleLine L) (e : ℤ) : Nonempty (Open P p X H L e) := by
  sorry

end StandardInputs

section FullHomPoints

variable (P : ProjectiveLineOverC) {d : ℕ} {X : SmoothProperComplexVariety d}
variable (H : HomSpacePresentation P X)

/-- The full universal property identifies actual complex Hom points
by their actual curve maps. Nilpotent test schemes remain in `H`. -/
theorem mapAt_injective : Function.Injective (H.mapAt P) := by
  let e : PointsOver ComplexBase (𝟙 ComplexBase) ComplexBase (𝟙 ComplexBase) :=
    ⟨𝟙 ComplexBase, Category.id_comp _⟩
  have hs : HomDeformation.sourceAtPoint P e ≫
      pullback.fst P.structureMap (𝟙 ComplexBase) = 𝟙 ProjectiveLine :=
    HomDeformation.sourceAtPoint_fst P e
  haveI : IsIso (HomDeformation.sourceAtPoint P e) := IsIso.of_isIso_fac_right hs
  have hn (t : PointsOver ComplexBase (𝟙 ComplexBase) H.parameter H.toC) :
      HomDeformation.sourceAtPoint P e ≫ rationalSourceMap P t =
        HomDeformation.sourceAtPoint P t := by
    simpa only [e, Category.id_comp] using HomDeformation.sourceAtPoint_naturality P e t
  intro a b hab
  apply (H.universal ComplexBase (𝟙 ComplexBase)).injective
  apply Subtype.ext
  apply (cancel_epi (HomDeformation.sourceAtPoint P e)).mp
  change HomDeformation.sourceAtPoint P e ≫ (rationalSourceMap P a ≫ H.evaluation) =
    HomDeformation.sourceAtPoint P e ≫ (rationalSourceMap P b ≫ H.evaluation)
  rw [← Category.assoc, hn a, ← Category.assoc, hn b]
  exact hab

/-- Restriction of an actual rational point to an open containing its
support. The full scheme map is retained. -/
def pointInOpen {Y : Scheme} {sY : Y ⟶ ComplexBase}
    (t : PointsOver ComplexBase (𝟙 ComplexBase) Y sY)
    (U : Y.Opens) (ht : t.val (IsLocalRing.closedPoint ℂ) ∈ U) :
    PointsOver ComplexBase (𝟙 ComplexBase) U.toScheme (U.ι ≫ sY) :=
  ⟨IsOpenImmersion.lift U.ι t.val (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    change t.val (IsLocalRing.closedPoint ℂ) ∈ (U : Set Y) at ht
    simpa only [Subsingleton.elim z (IsLocalRing.closedPoint ℂ)] using ht), by
      rw [← Category.assoc, IsOpenImmersion.lift_fac, t.property]⟩

@[reassoc] theorem pointInOpen_inclusion {Y : Scheme} {sY : Y ⟶ ComplexBase}
    (t : PointsOver ComplexBase (𝟙 ComplexBase) Y sY)
    (U : Y.Opens) (ht : t.val (IsLocalRing.closedPoint ℂ) ∈ U) :
    (pointInOpen t U ht).val ≫ U.ι = t.val :=
  IsOpenImmersion.lift_fac _ _ _

theorem fixed_curveAt_forget (p : ProjectiveLinePoint P) (x : ComplexPoint X)
    (t : PointsOver ComplexBase (𝟙 ComplexBase)
      (FixedNodeHom.parameter P p H x) (FixedNodeHom.toC P p H x)) :
    HomDeformation.curveAt P H p x t = H.mapAt P (FixedNodeHom.forget P p H x t) := by
  unfold HomDeformation.curveAt FixedNodeHom.evaluation
  rw [← Category.assoc, HomDeformation.sourceAtPoint_naturality]
  rfl

theorem fixed_curveAt_injective (p : ProjectiveLinePoint P) (x : ComplexPoint X) :
    Function.Injective (HomDeformation.curveAt P H p x) := by
  intro a b hab
  have he : FixedNodeHom.forget P p H x a = FixedNodeHom.forget P p H x b := by
    apply mapAt_injective P H
    simpa only [fixed_curveAt_forget] using hab
  apply Subtype.ext
  apply pullback.hom_ext
  · exact congrArg Subtype.val he
  · exact a.property.trans b.property.symm

theorem fixed_point_eq_center (p : ProjectiveLinePoint P) (x : ComplexPoint X)
    (t : PointsOver ComplexBase (𝟙 ComplexBase)
      (FixedNodeHom.parameter P p H x) (FixedNodeHom.toC P p H x))
    (f : RationalCurve P X) (hx : p.map ≫ f.map = x.map)
    (ht : HomDeformation.curveAt P H p x t = f.map) :
    t = HomDeformation.fixedCenter P H p x f.map f.overC hx := by
  apply fixed_curveAt_injective P H p x
  rw [HomDeformation.curveAt_fixedCenter]
  exact ht

end FullHomPoints

section FreeOpen

variable (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
variable {d : ℕ} (X : SmoothProperComplexVariety d) (hX : HasProjectiveEmbedding X)
variable (H : HomSpacePresentation P X) (L : LineBundle X.scheme)

abbrev FreeCurve :=
  {f : RationalCurve P X // IsFreeRationalCurve P X (intrinsicTangentBundle X) f}

def freeNeighborhood (f : FreeCurve P X) : HomNeighborhood.FreeOpen P p X H f.val L :=
  Classical.choice (HomNeighborhood.StandardInputs.free_neighborhood
    P p X hX H f.val f.property L)

/-- A genuine open of the full Hom scheme, formed as the union of the
classical neighborhoods of all actual free maps. -/
def freeOpen : H.parameter.Opens :=
  ⨆ f : FreeCurve P X, (freeNeighborhood P p X hX H L f).neighborhood

theorem freeOpen_point
    (t : PointsOver ComplexBase (𝟙 ComplexBase) H.parameter H.toC)
    (ht : t.val (IsLocalRing.closedPoint ℂ) ∈ freeOpen P p X hX H L) :
    ∃ f : RationalCurve P X,
      IsFreeRationalCurve P X (intrinsicTangentBundle X) f ∧ H.mapAt P t = f.map := by
  obtain ⟨f, hf⟩ := TopologicalSpace.Opens.mem_iSup.mp ht
  let O := freeNeighborhood P p X hX H L f
  let q := pointInOpen t O.neighborhood hf
  have hq : (⟨q.val ≫ O.neighborhood.ι, by
      simpa only [Category.assoc] using q.property⟩ :
        PointsOver ComplexBase (𝟙 ComplexBase) H.parameter H.toC) = t :=
    Subtype.ext (pointInOpen_inclusion t O.neighborhood hf)
  refine ⟨O.curveAt q, O.free q, ?_⟩
  rw [O.curveAt_spec, hq]

theorem center_mem_freeOpen (f : RationalCurve P X)
    (hf : IsFreeRationalCurve P X (intrinsicTangentBundle X) f) :
    (HomDeformation.center P H f.map f.overC).val (IsLocalRing.closedPoint ℂ) ∈
      freeOpen P p X hX H L := by
  let O := freeNeighborhood P p X hX H L ⟨f, hf⟩
  let t : PointsOver ComplexBase (𝟙 ComplexBase) H.parameter H.toC :=
    ⟨O.marked.val ≫ O.neighborhood.ι, by simpa only [Category.assoc] using O.marked.property⟩
  have ht : t = HomDeformation.center P H f.map f.overC := by
    apply mapAt_injective P H
    exact O.center.trans (HomDeformation.center_spec P H f.map f.overC).symm
  apply TopologicalSpace.Opens.mem_iSup.mpr
  refine ⟨⟨f, hf⟩, ?_⟩
  rw [← ht]
  exact (O.marked.val (IsLocalRing.closedPoint ℂ)).property

variable {e : ℤ} (D : Open P p X H L e)

/-- Boundedness and freeness are imposed by actual intersection of
opens; neither is stored as a condition on a renamed parameter set. -/
def boundedFreeOpen : H.parameter.Opens := D.openSet ⊓ freeOpen P p X hX H L

theorem boundedFreeOpen_finiteType :
    LocallyOfFiniteType ((boundedFreeOpen P p X hX H L D).ι ≫ H.toC) := by
  letI := D.finiteType
  have h : LocallyOfFiniteType
      (H.parameter.homOfLE (show boundedFreeOpen P p X hX H L D ≤ D.openSet from inf_le_left) ≫
        (D.openSet.ι ≫ H.toC)) := inferInstance
  simpa only [← Category.assoc, Scheme.homOfLE_ι] using h

theorem boundedFreeOpen_quasiCompact :
    QuasiCompact ((boundedFreeOpen P p X hX H L D).ι ≫ H.toC) := by
  letI := D.finiteType
  letI := D.quasiCompact
  letI : IsLocallyNoetherian D.openSet.toScheme :=
    LocallyOfFiniteType.isLocallyNoetherian (D.openSet.ι ≫ H.toC)
  letI : CompactSpace D.openSet.toScheme :=
    QuasiCompact.compactSpace_of_compactSpace (D.openSet.ι ≫ H.toC)
  letI : IsNoetherian D.openSet.toScheme := ⟨⟩
  let j := H.parameter.homOfLE
    (show boundedFreeOpen P p X hX H L D ≤ D.openSet from inf_le_left)
  letI : TopologicalSpace.NoetherianSpace (boundedFreeOpen P p X hX H L D).toScheme :=
    j.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  infer_instance

end FreeOpen

section ContactLines

open LeBrunSalamon.PhaseThirtyFive (contactFano_hasProjectiveEmbedding)

variable {n : ℕ} (X : ContactFanoManifold n)
variable (H : HomSpacePresentation P X.variety)
variable (D : Open P marking X.variety H X.contact.sequence.line 1)

abbrev contactOpen : H.parameter.Opens :=
  boundedFreeOpen P marking X.variety (contactFano_hasProjectiveEmbedding X)
    H X.contact.sequence.line D

theorem contactOpen_point
    (t : PointsOver ComplexBase (𝟙 ComplexBase) H.parameter H.toC)
    (ht : t.val (IsLocalRing.closedPoint ℂ) ∈ contactOpen X H D) :
    ∃ f : FreeLine X, H.mapAt P t = f.curve.map := by
  obtain ⟨f, hf, he⟩ := freeOpen_point P marking X.variety
    (contactFano_hasProjectiveEmbedding X) H X.contact.sequence.line t ht.2
  have hd : projectiveLineDegree P marking
      (pullbackLine f.map X.contact.sequence.line) = 1 := by
    rw [← he]
    exact (D.membership t).mp ht.1
  exact ⟨⟨f, hd, hf⟩, he⟩

theorem contact_center_mem (f : FreeLine X) :
    (HomDeformation.center P H f.curve.map f.curve.overC).val
        (IsLocalRing.closedPoint ℂ) ∈ contactOpen X H D := by
  constructor
  · apply (D.membership _).mpr
    rw [HomDeformation.center_spec]
    exact f.degreeOne
  · exact center_mem_freeOpen P marking X.variety
      (contactFano_hasProjectiveEmbedding X) H X.contact.sequence.line f.curve f.free

end ContactLines

end LeBrunSalamon.Construction.Lines.HomDegree

end

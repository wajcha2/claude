import LSHomDegree
import LSProductGeometry

/-!
## The actual bounded fixed-node parameter of free contact lines

Bounded degree and freeness define an actual open of the full Hom scheme.
Taking the scheme-theoretic fibre of marked evaluation preserves its
nonreduced test schemes. The finite-type proof uses base change, not a
replacement of this fibre by its set of complex points.

Source preparation only; compilation is deferred.
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

namespace LeBrunSalamon.Construction.Lines.FixedFreeParameter

variable {n : ℕ} (X : ContactFanoManifold n)
variable (H : HomSpacePresentation P X.variety)
variable (D : HomDegree.Open P marking X.variety H X.contact.sequence.line 1)
variable (x : ComplexPoint X.variety)

abbrev openSet : H.parameter.Opens := HomDegree.contactOpen X H D

def markedEvaluation : (openSet X H D).toScheme ⟶ X.variety.scheme :=
  (openSet X H D).ι ≫ FixedNodeHom.markedEvaluation P marking H

@[reassoc] theorem markedEvaluation_overC :
    markedEvaluation X H D ≫ X.variety.structureMap = (openSet X H D).ι ≫ H.toC := by
  rw [markedEvaluation, Category.assoc, FixedNodeHom.markedEvaluation_overC]

instance openSet_finiteType : LocallyOfFiniteType ((openSet X H D).ι ≫ H.toC) :=
  HomDegree.boundedFreeOpen_finiteType P marking X.variety
    (LeBrunSalamon.PhaseThirtyFive.contactFano_hasProjectiveEmbedding X) H X.contact.sequence.line D

instance openSet_quasiCompact : QuasiCompact ((openSet X H D).ι ≫ H.toC) :=
  HomDegree.boundedFreeOpen_quasiCompact P marking X.variety
    (LeBrunSalamon.PhaseThirtyFive.contactFano_hasProjectiveEmbedding X) H X.contact.sequence.line D

instance openSet_noetherian : IsNoetherian (openSet X H D).toScheme := by
  letI : IsLocallyNoetherian (openSet X H D).toScheme :=
    LocallyOfFiniteType.isLocallyNoetherian ((openSet X H D).ι ≫ H.toC)
  letI : CompactSpace (openSet X H D).toScheme :=
    QuasiCompact.compactSpace_of_compactSpace ((openSet X H D).ι ≫ H.toC)
  exact ⟨⟩

instance markedEvaluation_finiteType : LocallyOfFiniteType (markedEvaluation X H D) := by
  haveI : LocallyOfFiniteType (markedEvaluation X H D ≫ X.variety.structureMap) := by
    rw [markedEvaluation_overC]
    infer_instance
  exact locallyOfFiniteType_of_comp (markedEvaluation X H D) X.variety.structureMap

instance markedEvaluation_quasiCompact : QuasiCompact (markedEvaluation X H D) :=
  inferInstance

/-- The literal fibre, with its nilpotents and all its test maps. -/
abbrev parameter : Scheme := pullback (markedEvaluation X H D) x.map

def toC : parameter X H D x ⟶ ComplexBase := pullback.snd _ _

def toOpen : parameter X H D x ⟶ (openSet X H D).toScheme := pullback.fst _ _

def toFullHom : parameter X H D x ⟶ H.parameter := toOpen X H D x ≫ (openSet X H D).ι

@[reassoc] theorem toFullHom_overC : toFullHom X H D x ≫ H.toC = toC X H D x := by
  have h := congrArg (fun k => k ≫ X.variety.structureMap)
    (pullback.condition (f := markedEvaluation X H D) (g := x.map))
  simpa only [Category.assoc, markedEvaluation_overC, x.overC,
    Category.comp_id, toFullHom, toOpen, toC] using h

@[reassoc] theorem fixedEquation :
    toFullHom X H D x ≫ FixedNodeHom.markedEvaluation P marking H = toC X H D x ≫ x.map := by
  simpa only [toFullHom, toOpen, toC, markedEvaluation, Category.assoc] using
    (pullback.condition (f := markedEvaluation X H D) (g := x.map))

def asFixedHom : PointsOver (parameter X H D x) (toC X H D x)
    (FixedNodeHom.parameter P marking H x) (FixedNodeHom.toC P marking H x) :=
  FixedNodeHom.lift P marking H x
    ⟨toFullHom X H D x, toFullHom_overC X H D x⟩ (fixedEquation X H D x)

@[reassoc] theorem asFixedHom_inclusion :
    (asFixedHom X H D x).val ≫ FixedNodeHom.inclusion P marking H x = toFullHom X H D x :=
  FixedNodeHom.lift_inclusion P marking H x _ _

instance toC_finiteType : LocallyOfFiniteType (toC X H D x) :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd (markedEvaluation X H D) x.map))

instance toC_quasiCompact : QuasiCompact (toC X H D x) :=
  inferInstanceAs (QuasiCompact (pullback.snd (markedEvaluation X H D) x.map))

def fixedPoint (t : PointsOver ComplexBase (𝟙 ComplexBase) (parameter X H D x) (toC X H D x)) :
    PointsOver ComplexBase (𝟙 ComplexBase)
      (FixedNodeHom.parameter P marking H x) (FixedNodeHom.toC P marking H x) :=
  ⟨t.val ≫ (asFixedHom X H D x).val, by rw [Category.assoc, (asFixedHom X H D x).property, t.property]⟩

/-- Every complex point represents an actual original free degree-one
curve, and equality with its fixed Hom centre is equality of scheme maps. -/
theorem point_is_freeLine
    (t : PointsOver ComplexBase (𝟙 ComplexBase) (parameter X H D x) (toC X H D x)) :
    ∃ (f : FreeLine X) (hf : marking.map ≫ f.curve.map = x.map),
      t.val ≫ (asFixedHom X H D x).val =
        (HomDeformation.fixedCenter P H marking x f.curve.map f.curve.overC hf).val := by
  let q := FixedNodeHom.forget P marking H x (fixedPoint X H D x t)
  have hq : q.val = t.val ≫ toFullHom X H D x := by
    simp only [q, FixedNodeHom.forget, fixedPoint, Category.assoc, asFixedHom_inclusion]
  have hmem : q.val (IsLocalRing.closedPoint ℂ) ∈ openSet X H D := by
    rw [hq]
    exact (toOpen X H D x (t.val (IsLocalRing.closedPoint ℂ))).property
  obtain ⟨f, hcurve⟩ := HomDegree.contactOpen_point X H D q hmem
  have hfixed : HomDeformation.curveAt P H marking x (fixedPoint X H D x t) = f.curve.map := by
    rw [HomDegree.fixed_curveAt_forget]
    exact hcurve
  have hf : marking.map ≫ f.curve.map = x.map := by
    rw [← hfixed]
    exact HomDeformation.curveAt_marking P H marking x (fixedPoint X H D x t)
  exact ⟨f, hf, congrArg Subtype.val
    (HomDegree.fixed_point_eq_center P H marking x (fixedPoint X H D x t) f.curve hf hfixed)⟩

/-- Conversely every actual free line through x occurs in this bounded
scheme, using its original full Hom centre. -/
def center (f : FreeLine X) (hf : marking.map ≫ f.curve.map = x.map) :
    PointsOver ComplexBase (𝟙 ComplexBase) (parameter X H D x) (toC X H D x) := by
  let c := HomDeformation.center P H f.curve.map f.curve.overC
  let q := HomDegree.pointInOpen c (openSet X H D) (HomDegree.contact_center_mem X H D f)
  have hq : q.val ≫ markedEvaluation X H D = (𝟙 ComplexBase) ≫ x.map := by
    rw [markedEvaluation, ← Category.assoc, HomDegree.pointInOpen_inclusion,
      ← HomDeformation.mapAt_markedEvaluation, HomDeformation.center_spec, hf,
      Category.id_comp]
  exact ⟨pullback.lift q.val (𝟙 ComplexBase) hq, by simp only [toC, pullback.lift_snd]⟩

@[reassoc] theorem center_toFullHom (f : FreeLine X)
    (hf : marking.map ≫ f.curve.map = x.map) :
    (center X H D x f hf).val ≫ toFullHom X H D x =
      (HomDeformation.center P H f.curve.map f.curve.overC).val := by
  simp only [center, toFullHom, toOpen, ← Category.assoc, pullback.lift_fst,
    HomDegree.pointInOpen_inclusion]

@[reassoc] theorem center_asFixedHom (f : FreeLine X)
    (hf : marking.map ≫ f.curve.map = x.map) :
    (center X H D x f hf).val ≫ (asFixedHom X H D x).val =
      (HomDeformation.fixedCenter P H marking x f.curve.map f.curve.overC hf).val := by
  apply pullback.hom_ext
  · change (_ ≫ (asFixedHom X H D x).val) ≫ FixedNodeHom.inclusion P marking H x = _
    rw [Category.assoc, asFixedHom_inclusion, center_toFullHom]
    exact (FixedNodeHom.lift_inclusion P marking H x _ _).symm
  · change (_ ≫ (asFixedHom X H D x).val) ≫ FixedNodeHom.toC P marking H x = _
    rw [Category.assoc, (asFixedHom X H D x).property, (center X H D x f hf).property]
    exact (HomDeformation.fixedCenter P H marking x f.curve.map f.curve.overC hf).property.symm

end LeBrunSalamon.Construction.Lines.FixedFreeParameter

end

import LSStandardProjectiveBaseChange
import LSStandardTautologicalP1
import LSQuadraticVeronese
import LSSmoothFibreComparison

/-! Actual polarized projective embeddings and the degree-two rational
fibre.  The chosen line and its coordinates are transported through the
specified isomorphisms.  There are no admissions in this file. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.Skeleton

namespace LeBrunSalamon

structure PolarizedProjectiveEmbedding (R : Type) [CommRing R] (N : ℕ)
    (X : Scheme.{0}) (s : X ⟶ Spec (CommRingCat.of R)) (L : LineBundle X) where
  hom : X ⟶ StandardTautological.space R N
  over_base : hom ≫ StandardTautological.toSpec R N = s
  closed : IsClosedImmersion hom
  lineIso : pullbackModule hom (StandardTautological.line R N).sheaf ≅ L.sheaf

namespace PolarizedProjectiveEmbedding

variable {R : Type} [CommRing R] {N : ℕ} {X : Scheme.{0}}
  {s : X ⟶ Spec (CommRingCat.of R)} {L : LineBundle X}

def coordinate (j : PolarizedProjectiveEmbedding R N X s L) (i : Fin (N+1)) :
    AlgebraicSection L.sheaf :=
  pullSection j.hom (StandardTautological.coordinate R N i) ≫ j.lineIso.hom

theorem generates (j : PolarizedProjectiveEmbedding R N X s L) :
    TupleGenerates L j.coordinate := by
  let a := fun i => pullSection j.hom (StandardTautological.coordinate R N i)
  letI : Epi (Sigma.desc a) := StandardProjectiveBaseChange.pull_generates
    (StandardTautological.coordinate R N) (StandardTautological.generates R N) j.hom
  have h : Sigma.desc j.coordinate = Sigma.desc a ≫ j.lineIso.hom := by
    apply Sigma.hom_ext
    intro i
    simp only [Sigma.ι_comp_desc, Category.assoc, Sigma.ι_comp_desc_assoc,
      coordinate, a]
  change Epi (Sigma.desc j.coordinate)
  rw [h]
  infer_instance

/-- Transport an actual embedding along an actual polarized scheme
isomorphism.  Both its base map and its line isomorphism are retained. -/
def transport {Y : Scheme.{0}} {sY : Y ⟶ Spec (CommRingCat.of R)}
    {M : LineBundle Y} (j : PolarizedProjectiveEmbedding R N Y sY M)
    (e : X ≅ Y) (he : e.hom ≫ sY = s)
    (eL : L.sheaf ≅ pullbackModule e.hom M.sheaf) :
    PolarizedProjectiveEmbedding R N X s L where
  hom := e.hom ≫ j.hom
  over_base := by rw [Category.assoc, j.over_base, he]
  closed := by
    letI := j.closed
    infer_instance
  lineIso :=
    ((Scheme.Modules.pullbackComp e.hom j.hom).app (StandardTautological.line R N).sheaf).symm ≪≫
      (Scheme.Modules.pullback e.hom).mapIso j.lineIso ≪≫ eL.symm

end PolarizedProjectiveEmbedding

namespace SmoothFibreComparison

theorem standard_base (N : ℕ) :
    StandardTautological.toSpec ℂ N = projectiveBaseMap N := rfl

/-- A given smooth rational fibre with its given degree-two line has an
actual plane embedding.  Its line comparison is supplied by the proved
marked-degree classification and the standard Veronese construction. -/
theorem plane_embedding {Y : Scheme.{0}} (s : Y ⟶ ComplexBase)
    (i : ProjectiveLine ≅ Y) (hi : i.hom ≫ s = canonicalProjectiveLine.structureMap)
    (p : ProjectiveLinePoint canonicalProjectiveLine) (L : LineBundle Y)
    (hL : projectiveLineDegree canonicalProjectiveLine p (pullbackLine i.hom L) = 2) :
    Nonempty (PolarizedProjectiveEmbedding ℂ 2 Y s L) := by
  obtain ⟨eL⟩ := pullback_square_iso canonicalProjectiveLine p i L
    (StandardTautological.line ℂ 1) (StandardTautologicalP1.degree_one _ _) hL
  obtain ⟨v, hv, hvclosed, ev, _⟩ := PublishedInputs.ProjectiveSpace.quadraticVeronese ℂ
  letI : IsClosedImmersion v := hvclosed
  let j := i.inv ≫ v
  have hj : j ≫ StandardTautological.toSpec ℂ 2 = s := by
    rw [Category.assoc, hv]
    exact inverse_over canonicalProjectiveLine s i hi
  let e : pullbackModule j (StandardTautological.line ℂ 2).sheaf ≅ L.sheaf :=
    ((Scheme.Modules.pullbackComp i.inv v).app (StandardTautological.line ℂ 2).sheaf).symm ≪≫
      (Scheme.Modules.pullback i.inv).mapIso ev ≪≫ eL.symm
  exact ⟨⟨j, hj, inferInstance, e⟩⟩

/-- The original family-degree hypothesis is phrased on a composite
pullback. This wrapper supplies its explicit composition comparison. -/
theorem fibre_plane_embedding
    {C S : Scheme.{0}} (pi : C ⟶ S) (s : ComplexBase ⟶ S)
    (L : LineBundle C) (i : ProjectiveLine ≅ pullback pi s)
    (hi : i.hom ≫ pullback.snd pi s = canonicalProjectiveLine.structureMap)
    (p : ProjectiveLinePoint canonicalProjectiveLine)
    (hL : projectiveLineDegree canonicalProjectiveLine p
      (pullbackLine (i.hom ≫ pullback.fst pi s) L) = 2) :
    Nonempty (PolarizedProjectiveEmbedding ℂ 2 (pullback pi s) (pullback.snd pi s)
      (pullbackLine (pullback.fst pi s) L)) := by
  apply plane_embedding (pullback.snd pi s) i hi p
  exact (projectiveLineDegree_iso canonicalProjectiveLine p
    (pullbackLine i.hom (pullbackLine (pullback.fst pi s) L))
    (pullbackLine (i.hom ≫ pullback.fst pi s) L)
    ((Scheme.Modules.pullbackComp i.hom (pullback.fst pi s)).app L.sheaf)).trans hL

end SmoothFibreComparison
end LeBrunSalamon
end

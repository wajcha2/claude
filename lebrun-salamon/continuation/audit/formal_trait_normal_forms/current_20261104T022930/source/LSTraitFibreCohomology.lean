import LSNodalLineCohomology

/-! The actual H¹ hypothesis needed by closed-fibre section lifting.
These are translations from the original degree hypotheses, with every
pullback-composition isomorphism retained. No admission is introduced. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction

namespace LeBrunSalamon.TraitFibreCohomology

theorem smooth (P : ProjectiveLineOverC) (mark : ProjectiveLinePoint P)
    {C S T : Scheme.{0}} (pi : C ⟶ S) (s : T ⟶ S) (L : LineBundle C)
    (e : ProjectiveLine ≅ pullback pi s)
    (h : projectiveLineDegree P mark
      (pullbackLine (e.hom ≫ pullback.fst pi s) L) = 2) :
    HasVanishingFirstCohomology (pullbackModule (pullback.fst pi s) L.sheaf) := by
  apply FirstCohomology.fibre_line_of_degree P mark pi s L e
  rw [h]
  norm_num

theorem nodal (P : ProjectiveLineOverC) (mark p q : ProjectiveLinePoint P)
    {C S T : Scheme.{0}} (pi : C ⟶ S) (s : T ⟶ S) (L : LineBundle C)
    (i j : ProjectiveLine ⟶ pullback pi s) (hpush : IsPushout p.map q.map i j)
    (hi : projectiveLineDegree P mark (pullbackLine (i ≫ pullback.fst pi s) L) = 1)
    (hj : projectiveLineDegree P mark (pullbackLine (j ≫ pullback.fst pi s) L) = 1) :
    HasVanishingFirstCohomology (pullbackModule (pullback.fst pi s) L.sheaf) := by
  let M := pullbackLine (pullback.fst pi s) L
  have hdi : projectiveLineDegree P mark (pullbackLine i M) = 1 :=
    (projectiveLineDegree_iso P mark (pullbackLine i M)
      (pullbackLine (i ≫ pullback.fst pi s) L)
      ((Scheme.Modules.pullbackComp i (pullback.fst pi s)).app L.sheaf)).trans hi
  have hdj : projectiveLineDegree P mark (pullbackLine j M) = 1 :=
    (projectiveLineDegree_iso P mark (pullbackLine j M)
      (pullbackLine (j ≫ pullback.fst pi s) L)
      ((Scheme.Modules.pullbackComp j (pullback.fst pi s)).app L.sheaf)).trans hj
  apply NodalLineCohomology.line_of_degrees P mark p q i j hpush M
  · rw [hdi]; norm_num
  · rw [hdj]; norm_num

end LeBrunSalamon.TraitFibreCohomology

end

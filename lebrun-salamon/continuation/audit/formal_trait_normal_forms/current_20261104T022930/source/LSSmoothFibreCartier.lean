import LSVeroneseZeroModel
import LSPolarizedProjectiveEmbedding
import LSQuadraticFibreCartier

/-! Transport the explicit Veronese equation through the given rational
fibre and the given degree-two line. The resulting embedding has its
actual Cartier ideal and its actual positive divisor line identified. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.Skeleton

namespace LeBrunSalamon.SmoothFibreComparison

theorem cartier_plane_embedding {Y : Scheme.{0}} (s : Y ⟶ ComplexBase)
    (i : ProjectiveLine ≅ Y) (hi : i.hom ≫ s = canonicalProjectiveLine.structureMap)
    (p : ProjectiveLinePoint canonicalProjectiveLine) (L : LineBundle Y)
    (hL : projectiveLineDegree canonicalProjectiveLine p (pullbackLine i.hom L) = 2) :
    ∃ j : PolarizedProjectiveEmbedding ℂ 2 Y s L,
      ∃ h : IsLocallyFreeOfRank (EffectiveCartier.ideal j.hom) 1,
        Nonempty ((EffectiveCartier.line j.hom h).sheaf ≅ (PlaneQuadratic.quadraticLine ℂ).sheaf) := by
  obtain ⟨eL⟩ := pullback_square_iso canonicalProjectiveLine p i L
    (StandardTautological.line ℂ 1) (StandardTautologicalP1.degree_one _ _) hL
  obtain ⟨v, hv, dv, _⟩ := PublishedInputs.ProjectiveSpace.quadraticVeronese_zeroModel ℂ
  let q := QuadraticVeronese.equation ℂ
  let e : Y ≅ PlaneQuadratic.ZeroScheme ℂ q := i.symm ≪≫ v
  let f := e.hom ≫ PlaneQuadratic.inclusion ℂ q
  have hbase : f ≫ StandardTautological.toSpec ℂ 2 = s := by
    change (i.inv ≫ v.hom) ≫ PlaneQuadratic.projection ℂ q = s
    rw [Category.assoc, hv]
    exact inverse_over canonicalProjectiveLine s i hi
  let d : pullbackModule f (StandardTautological.line ℂ 2).sheaf ≅ L.sheaf :=
    ((Scheme.Modules.pullbackCongr (Category.assoc i.inv v.hom
      (PlaneQuadratic.inclusion ℂ q))).app (StandardTautological.line ℂ 2).sheaf) ≪≫
    ((Scheme.Modules.pullbackComp i.inv
      (v.hom ≫ PlaneQuadratic.inclusion ℂ q)).app (StandardTautological.line ℂ 2).sheaf).symm ≪≫
    (Scheme.Modules.pullback i.inv).mapIso dv ≪≫ eL.symm
  letI : IsIso e.hom := e.isIso_hom
  let j : PolarizedProjectiveEmbedding ℂ 2 Y s L := ⟨f, hbase, inferInstance, d⟩
  obtain ⟨h, hd⟩ := QuadraticFibreCartier.of_quadratic_iso ℂ f q
    (QuadraticVeronese.equation_ne_zero ℂ) e rfl
  exact ⟨j, h, hd⟩

theorem fibre_cartier_plane_embedding
    {C S : Scheme.{0}} (pi : C ⟶ S) (s : ComplexBase ⟶ S)
    (L : LineBundle C) (i : ProjectiveLine ≅ pullback pi s)
    (hi : i.hom ≫ pullback.snd pi s = canonicalProjectiveLine.structureMap)
    (p : ProjectiveLinePoint canonicalProjectiveLine)
    (hL : projectiveLineDegree canonicalProjectiveLine p
      (pullbackLine (i.hom ≫ pullback.fst pi s) L) = 2) :
    ∃ j : PolarizedProjectiveEmbedding ℂ 2 (pullback pi s) (pullback.snd pi s)
        (pullbackLine (pullback.fst pi s) L),
      ∃ h : IsLocallyFreeOfRank (EffectiveCartier.ideal j.hom) 1,
        Nonempty ((EffectiveCartier.line j.hom h).sheaf ≅ (PlaneQuadratic.quadraticLine ℂ).sheaf) := by
  apply cartier_plane_embedding (pullback.snd pi s) i hi p
  exact (projectiveLineDegree_iso canonicalProjectiveLine p
    (pullbackLine i.hom (pullbackLine (pullback.fst pi s) L))
    (pullbackLine (i.hom ≫ pullback.fst pi s) L)
    ((Scheme.Modules.pullbackComp i.hom (pullback.fst pi s)).app L.sheaf)).trans hL

end LeBrunSalamon.SmoothFibreComparison
end

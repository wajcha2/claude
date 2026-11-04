import RecompileExtensionsPart03

/-! Transport the actual Yoneda extension-splitting definition of H¹=0
along a scheme isomorphism. This file contains no admitted theorem. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.PhaseThirtyTwo

namespace LeBrunSalamon.FirstCohomology

theorem of_pullback_iso {X Y : Scheme.{0}} (e : X ≅ Y) (E : OModule Y)
    (h : HasVanishingFirstCohomology (pullbackModule e.hom E)) :
    HasVanishingFirstCohomology E := by
  intro M i q hz hex
  let A := PointBaseTransport.pullbackEquivalence e
  let F := A.functor
  let S := (ShortComplex.mk i q hz).map F
  let u := unitPullbackIso e.hom
  let q' := F.map q ≫ u.hom
  have hz' : F.map i ≫ q' = 0 := by
    dsimp [q']
    rw [← Category.assoc, ← Functor.map_comp, hz, Functor.map_zero, zero_comp]
  let T := ShortComplex.mk (F.map i) q' hz'
  let a : S ≅ T := ShortComplex.isoMk (Iso.refl _) (Iso.refl _) u
    (by simp [S, T]) (by simp [S, T, q'])
  have hT : T.ShortExact := ShortComplex.shortExact_of_iso a (hex.map_of_exact F)
  obtain ⟨s, hs⟩ := h (F.obj M) (F.map i) q' hz' hT
  let v : F.obj (structureModule Y) ⟶ F.obj M := u.hom ≫ s
  let he : (structureModule Y ⟶ M) ≃
      (F.obj (structureModule Y) ⟶ F.obj M) := A.fullyFaithfulFunctor.homEquiv
  let l : structureModule Y ⟶ M := he.symm v
  have hl : F.map l = v := he.apply_symm_apply v
  refine ⟨l, ?_⟩
  apply F.map_injective
  rw [F.map_comp, F.map_id, hl]
  apply (cancel_mono u.hom).mp
  change (u.hom ≫ s ≫ F.map q) ≫ u.hom = (𝟙 _) ≫ u.hom
  simp only [Category.assoc, Category.id_comp]
  change u.hom ≫ (s ≫ q') = u.hom
  rw [hs, Category.comp_id]

/-- The actual line classification and proved two-chart calculation imply
vanishing for any line of degree at least minus one. -/
theorem line_of_degree (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    (L : LineBundle ProjectiveLine) (h : -1 ≤ projectiveLineDegree P p L) :
    HasVanishingFirstCohomology L.sheaf := by
  obtain ⟨e⟩ := projectiveLineDegree_spec P p L
  exact (iso_iff e).mpr ((CechYoneda.twist_firstCohomology_iff P p _).mpr h)

/-- Application to the supplied identification of an actual closed fibre
with P¹. The given degree concerns the composite pullback, so its pullback
composition isomorphism is retained explicitly. -/
theorem fibre_line_of_degree
    (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {C S T : Scheme.{0}} (pi : C ⟶ S) (s : T ⟶ S) (L : LineBundle C)
    (e : ProjectiveLine ≅ pullback pi s)
    (h : -1 ≤ projectiveLineDegree P p
      (pullbackLine (e.hom ≫ pullback.fst pi s) L)) :
    HasVanishingFirstCohomology (pullbackModule (pullback.fst pi s) L.sheaf) := by
  apply of_pullback_iso e
  apply (iso_iff ((Scheme.Modules.pullbackComp e.hom (pullback.fst pi s)).app L.sheaf)).mpr
  exact line_of_degree P p (pullbackLine (e.hom ≫ pullback.fst pi s) L) h

end LeBrunSalamon.FirstCohomology

end

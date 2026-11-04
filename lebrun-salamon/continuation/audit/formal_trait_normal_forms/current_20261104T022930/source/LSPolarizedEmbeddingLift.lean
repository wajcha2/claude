import LSLiftedProjectiveTuple
import LSStandardProjectiveBaseChange
import LSStandardProjectiveProper
import LSClosedImmersionLocus
import LSPolarizedProjectiveEmbedding

/-! Lift the actual polarized closed-fibre embedding from its actual
coordinate sections.  The cartesian comparison is proved by the projective
universal property; the closed-immersion locus then gives the family
embedding.  This file introduces no admitted statement. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.Refinement LeBrunSalamon.Skeleton

namespace LeBrunSalamon.PolarizedEmbeddingLift

theorem exists_of_surjective_restriction
    (R K : Type) [CommRing R] [IsLocalRing R] [CommRing K]
    (φ : R →+* K) (t : Spec (CommRingCat.of K))
    (ht : (StandardProjectiveBaseChange.base φ).base t = IsLocalRing.closedPoint R)
    {X : Scheme.{0}} (pi : X ⟶ Spec (CommRingCat.of R)) [IsProper pi]
    (N : ℕ) (L : LineBundle X)
    (hsections : Function.Surjective (fun a : AlgebraicSection L.sheaf =>
      pullSection (pullback.fst pi (StandardProjectiveBaseChange.base φ)) a))
    (b : Fin (N+1) → AlgebraicSection
      (pullbackModule (pullback.fst pi (StandardProjectiveBaseChange.base φ)) L.sheaf))
    (hb : TupleGenerates (pullbackLine
      (pullback.fst pi (StandardProjectiveBaseChange.base φ)) L) b)
    (j : pullback pi (StandardProjectiveBaseChange.base φ) ⟶ StandardTautological.space K N)
    (hj : j ≫ StandardTautological.toSpec K N =
      pullback.snd pi (StandardProjectiveBaseChange.base φ))
    [IsClosedImmersion j]
    (e0 : pullbackModule j (StandardTautological.line K N).sheaf ≅
      pullbackModule (pullback.fst pi (StandardProjectiveBaseChange.base φ)) L.sheaf)
    (he0 : ∀ i, pullSection j (StandardTautological.coordinate K N i) ≫ e0.hom = b i) :
    ∃ a : Fin (N+1) → AlgebraicSection L.sheaf,
      (∀ i, pullSection (pullback.fst pi (StandardProjectiveBaseChange.base φ)) (a i) = b i) ∧
      TupleGenerates L a ∧
      ∃ f : {f : X ⟶ StandardTautological.space R N //
          f ≫ StandardTautological.toSpec R N = pi},
        IsClosedImmersion f.val ∧
        j ≫ StandardProjectiveBaseChange.map φ N =
          pullback.fst pi (StandardProjectiveBaseChange.base φ) ≫ f.val ∧
        ∃ e : pullbackModule f.val (StandardTautological.line R N).sheaf ≅ L.sheaf,
          ∀ i, pullSection f.val (StandardTautological.coordinate R N i) ≫ e.hom = a i := by
  let g := StandardProjectiveBaseChange.base φ
  let inc := pullback.fst pi g
  let p0 := pullback.snd pi g
  let β := StandardProjectiveBaseChange.map φ N
  let D := StandardTautological.chosen R N
  let E := StandardTautological.chosen K N
  let L0 := pullbackLine inc L
  obtain ⟨a, ha, hgen, f, e, hfe⟩ :=
    LiftedProjectiveTuple.exists_of_surjective_restriction R pi g t ht D L hsections b hb
  let c₁ : pullbackModule (j ≫ β) D.sheaf ≅ L0.sheaf :=
    ((Scheme.Modules.pullbackComp j β).app D.sheaf).symm ≪≫
      (Scheme.Modules.pullback j).mapIso (StandardProjectiveBaseChange.lineIso φ N) ≪≫ e0
  let c₂ : pullbackModule (inc ≫ f.val) D.sheaf ≅ L0.sheaf :=
    ((Scheme.Modules.pullbackComp inc f.val).app D.sheaf).symm ≪≫
      (Scheme.Modules.pullback inc).mapIso e
  have hc₁ (i : Fin (N+1)) : pullSection (j ≫ β) (D.coordinate i) ≫ c₁.hom = b i := by
    rw [StandardProjectiveBaseChange.composite_coordinate]
    have hcoord : pullSection β (D.coordinate i) ≫
        (StandardProjectiveBaseChange.lineIso φ N).hom = E.coordinate i :=
      StandardProjectiveBaseChange.coordinate φ N i
    exact (congrArg (fun z : AlgebraicSection E.sheaf => pullSection j z ≫ e0.hom)
      hcoord).trans (he0 i)
  have hc₂ (i : Fin (N+1)) :
      pullSection (inc ≫ f.val) (D.coordinate i) ≫ c₂.hom = b i := by
    have h := StandardProjectiveBaseChange.composite_coordinate inc f.val
      (D.coordinate i) e (Iso.refl L0.sheaf)
    simp only [Iso.trans_refl, Iso.refl_hom, Category.comp_id] at h
    exact h.trans ((congrArg (fun z : AlgebraicSection L.sheaf => pullSection inc z)
      (hfe i)).trans (ha i))
  have hbase₁ : (j ≫ β) ≫ StandardTautological.toSpec R N = p0 ≫ g := by
    rw [Category.assoc, (StandardProjectiveBaseChange.mapPoint φ N).property,
      ← Category.assoc, hj]
  have hbase₂ : (inc ≫ f.val) ≫ StandardTautological.toSpec R N = p0 ≫ g := by
    rw [Category.assoc, f.property]
    exact pullback.condition
  obtain ⟨u, _, hu⟩ := D.universal (pullback pi g) (p0 ≫ g) L0.sheaf L0.locallyFree b hb
  have hcompare : j ≫ β = inc ≫ f.val :=
    congrArg Subtype.val ((hu ⟨j ≫ β, hbase₁⟩ ⟨c₁, hc₁⟩).trans
      (hu ⟨inc ≫ f.val, hbase₂⟩ ⟨c₂, hc₂⟩).symm)
  letI : IsSeparated (StandardTautological.toSpec R N) := StandardProjectiveProper.separated R N
  have hclosed : IsClosedImmersion f.val :=
    ClosedImmersionLocus.of_local_closed_fibre R pi (StandardTautological.toSpec R N)
      f.val f.property g t ht p0 (StandardTautological.toSpec K N) inc β j
      (IsPullback.of_hasPullback pi g) (StandardProjectiveBaseChange.isPullback φ N)
      hcompare hj
  exact ⟨a, ha, hgen, f, hclosed, hcompare, e, hfe⟩

/-- Packaging of the preceding theorem for a specified polarized
closed-fibre embedding.  Its generating tuple is derived from the
standard tautological quotient, rather than postulated separately. -/
theorem of_closed_fibre
    (R K : Type) [CommRing R] [IsLocalRing R] [CommRing K]
    (φ : R →+* K) (t : Spec (CommRingCat.of K))
    (ht : (StandardProjectiveBaseChange.base φ).base t = IsLocalRing.closedPoint R)
    {X : Scheme.{0}} (pi : X ⟶ Spec (CommRingCat.of R)) [IsProper pi]
    (N : ℕ) (L : LineBundle X)
    (hsections : Function.Surjective (fun a : AlgebraicSection L.sheaf =>
      pullSection (pullback.fst pi (StandardProjectiveBaseChange.base φ)) a))
    (j : PolarizedProjectiveEmbedding K N
      (pullback pi (StandardProjectiveBaseChange.base φ))
      (pullback.snd pi (StandardProjectiveBaseChange.base φ))
      (pullbackLine (pullback.fst pi (StandardProjectiveBaseChange.base φ)) L)) :
    Nonempty (PolarizedProjectiveEmbedding R N X pi L) := by
  letI : IsClosedImmersion j.hom := j.closed
  obtain ⟨a, ha, hgen, f, hclosed, hcompare, e, he⟩ := exists_of_surjective_restriction
    R K φ t ht pi N L hsections j.coordinate j.generates j.hom j.over_base
      j.lineIso (fun _ => rfl)
  exact ⟨⟨f.val, f.property, hclosed, e⟩⟩

/-- Retain the exact closed-fibre map, so the subsequent Cartier-ideal
base change uses this same embedding, rather than a second choice. -/
theorem with_closed_fibre_comparison
    (R K : Type) [CommRing R] [IsLocalRing R] [CommRing K]
    (φ : R →+* K) (t : Spec (CommRingCat.of K))
    (ht : (StandardProjectiveBaseChange.base φ).base t = IsLocalRing.closedPoint R)
    {X : Scheme.{0}} (pi : X ⟶ Spec (CommRingCat.of R)) [IsProper pi]
    (N : ℕ) (L : LineBundle X)
    (hsections : Function.Surjective (fun a : AlgebraicSection L.sheaf =>
      pullSection (pullback.fst pi (StandardProjectiveBaseChange.base φ)) a))
    (j : PolarizedProjectiveEmbedding K N
      (pullback pi (StandardProjectiveBaseChange.base φ))
      (pullback.snd pi (StandardProjectiveBaseChange.base φ))
      (pullbackLine (pullback.fst pi (StandardProjectiveBaseChange.base φ)) L)) :
    ∃ f : PolarizedProjectiveEmbedding R N X pi L,
      j.hom ≫ StandardProjectiveBaseChange.map φ N =
        pullback.fst pi (StandardProjectiveBaseChange.base φ) ≫ f.hom := by
  letI : IsClosedImmersion j.hom := j.closed
  obtain ⟨a, ha, hgen, f, hclosed, hcompare, e, he⟩ := exists_of_surjective_restriction
    R K φ t ht pi N L hsections j.coordinate j.generates j.hom j.over_base
      j.lineIso (fun _ => rfl)
  exact ⟨⟨f.val, f.property, hclosed, e⟩, hcompare⟩

theorem cartesian_of_comparison
    (R K : Type) [CommRing R] [CommRing K] (φ : R →+* K)
    {X : Scheme.{0}} (pi : X ⟶ Spec (CommRingCat.of R))
    (N : ℕ) (L : LineBundle X) (f : PolarizedProjectiveEmbedding R N X pi L)
    (j : PolarizedProjectiveEmbedding K N
      (pullback pi (StandardProjectiveBaseChange.base φ))
      (pullback.snd pi (StandardProjectiveBaseChange.base φ))
      (pullbackLine (pullback.fst pi (StandardProjectiveBaseChange.base φ)) L))
    (hcompare : j.hom ≫ StandardProjectiveBaseChange.map φ N =
      pullback.fst pi (StandardProjectiveBaseChange.base φ) ≫ f.hom) :
    IsPullback (pullback.fst pi (StandardProjectiveBaseChange.base φ)) j.hom f.hom
      (StandardProjectiveBaseChange.map φ N) := by
  apply IsPullback.of_bot (t := StandardProjectiveBaseChange.isPullback φ N)
  · simpa only [j.over_base, f.over_base] using
      IsPullback.of_hasPullback pi (StandardProjectiveBaseChange.base φ)
  · exact hcompare.symm

end LeBrunSalamon.PolarizedEmbeddingLift
end

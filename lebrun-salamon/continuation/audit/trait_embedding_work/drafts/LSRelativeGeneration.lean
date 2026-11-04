import LSGeneratingUnitOpens
import LSVectorBundlePullback
import LSProperLocalTopology

/-! Lifted sections that generate on the actual closed fibre generate
globally over a proper local base. All locality, covering, and pullback
steps are proved; no embedding or cohomology input is admitted here. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.Skeleton

namespace LeBrunSalamon.RelativeGeneration

/-- Local epimorphy is tested on the original sheaf maps and all opens. -/
theorem epi_of_locally_epi {X : Scheme.{0}} {E F : OModule X} (q : E ⟶ F)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Epi ((Scheme.Modules.pullback U.ι).map q)) : Epi q := by
  choose U hxU hepi using h
  constructor
  intro Z a b hab
  have habU (x : X) :
      (Scheme.Modules.restrictFunctor (U x).ι).map a =
        (Scheme.Modules.restrictFunctor (U x).ι).map b := by
    apply VectorBundlePullback.restrict_map_eq_of_pullback_map_eq
    letI := hepi x
    apply (cancel_epi ((Scheme.Modules.pullback (U x).ι).map q)).mp
    simpa only [← Functor.map_comp] using
      congrArg (fun w => (Scheme.Modules.pullback (U x).ι).map w) hab
  apply Scheme.Modules.hom_ext
  intro W
  apply AddCommGrpCat.ext
  intro s
  apply (TwoChartSections.sectionSheaf Z).eq_of_locally_eq'
    (fun x => U x ⊓ W) W (fun _ => homOfLE inf_le_right)
    (by intro x hx; exact (le_iSup (fun y : X => U y ⊓ W) x) ⟨hxU x, hx⟩)
  intro x
  change Z.presheaf.map (homOfLE (inf_le_right : U x ⊓ W ≤ W)).op (a.app W s) =
    Z.presheaf.map (homOfLE (inf_le_right : U x ⊓ W ≤ W)).op (b.app W s)
  rw [sheafHom_naturality, sheafHom_naturality]
  have he := congrArg (fun f => f.app ((U x).ι ⁻¹ᵁ W)) (habU x)
  change a.app ((U x).ι ''ᵁ ((U x).ι ⁻¹ᵁ W)) =
    b.app ((U x).ι ''ᵁ ((U x).ι ⁻¹ᵁ W)) at he
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι] at he
  exact congrArg (fun f => f (F.presheaf.map (homOfLE inf_le_right).op s)) he

/-- The specified tuple generates if its actual unit opens cover. -/
theorem tupleGenerates_of_cover {X : Scheme.{0}} {N : ℕ}
    (L : LineBundle X) (a : Fin (N+1) → AlgebraicSection L.sheaf)
    (h : (⨆ i, nonvanishingOpen L (a i)) = ⊤) : TupleGenerates L a := by
  let q := Sigma.desc a
  apply epi_of_locally_epi q
  intro x
  have hx : x ∈ (⨆ i, nonvanishingOpen L (a i)) := by rw [h]; trivial
  obtain ⟨i, hxi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  let U := nonvanishingOpen L (a i)
  let F := Scheme.Modules.pullback U.ι
  letI : IsIso (F.map (a i)) := nonvanishingOpen_isIso L (a i)
  have he : F.map (Sigma.ι (fun _ : Fin (N+1) => structureModule X) i) ≫ F.map q =
      F.map (a i) := by rw [← F.map_comp, Sigma.ι_comp_desc]
  letI : Epi (F.map (Sigma.ι (fun _ : Fin (N+1) => structureModule X) i) ≫ F.map q) :=
    he.symm ▸ inferInstance
  exact ⟨U, hxi, epi_of_epi
    (F.map (Sigma.ι (fun _ : Fin (N+1) => structureModule X) i)) (F.map q)⟩

/-- Coverage after pullback to the actual closed fibre is enough over a
proper local base. This uses the proved nonvanishing pullback identity. -/
theorem tupleGenerates_of_closed_fibre
    (R : Type) [CommRing R] [IsLocalRing R]
    {X T : Scheme.{0}} (pi : X ⟶ Spec (CommRingCat.of R)) [IsProper pi]
    (s : T ⟶ Spec (CommRingCat.of R))
    (t : T) (ht : s t = IsLocalRing.closedPoint R)
    {N : ℕ} (L : LineBundle X) (a : Fin (N+1) → AlgebraicSection L.sheaf)
    (h : TupleGenerates (pullbackLine (pullback.fst pi s) L)
      (fun i => pullSection (pullback.fst pi s) (a i))) : TupleGenerates L a := by
  apply tupleGenerates_of_cover
  apply ProperLocalTopology.open_eq_top_of_closed_fibre R pi s t ht
  rintro x ⟨y, rfl⟩
  have hy : y ∈ (⨆ i, nonvanishingOpen (pullbackLine (pullback.fst pi s) L)
      (pullSection (pullback.fst pi s) (a i))) := by
    rw [GeneratingUnitOpens.generating_nonvanishing_cover _ _ h]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
  rw [← NonvanishingPullbackProof.nonvanishingOpen_pullback] at hi
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩

end LeBrunSalamon.RelativeGeneration

end

import RecompileBasePart05C

/-!
Actual section vanishing on an arbitrary open cover and the diagonal support
cover induced by any chosen cover of X.  In particular, this lets a two-chart
P1 calculation be used directly, without quantifying over all line frames.
No new geometric or published admission is used.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentyEight

namespace LeBrunSalamon.SectionCoverProof

theorem section_eq_zero_of_pullback_cover {X : Scheme} {E : OModule X}
    (a : AlgebraicSection E) {ι : Type*} (U : ι → X.Opens)
    (hU : iSup U = ⊤)
    (ha : ∀ i, (Scheme.Modules.pullback (U i).ι).map a = 0) : a = 0 := by
  apply (sectionValue_bijective E).injective
  rw [sectionValue_zero]
  let S : TopCat.Sheaf AddCommGrpCat X :=
    (SheafOfModules.toSheaf X.ringCatSheaf).obj E
  apply TopCat.Sheaf.eq_of_locally_eq' S U ⊤
    (fun i => (U i).leTop) (by rw [hU])
  intro i
  have ho := DominantSectionInjectivityProof.over_zero_of_pullback_zero (U i) a (ha i)
  have hv := congrArg
    (fun q : (structureModule X).over (U i) ⟶ E.over (U i) =>
      q.val.app (op (Over.mk (𝟙 (U i)))) (1 : RingSections X (U i))) ho
  change (Scheme.Modules.Hom.app a (U i)) (1 : RingSections X (U i)) = 0 at hv
  change E.presheaf.map (homOfLE le_top).op (sectionValue a) =
    E.presheaf.map (homOfLE le_top).op 0
  rw [sectionValue, sheafHom_naturality]
  change (Scheme.Modules.Hom.app a (U i))
    (X.presheaf.map (homOfLE le_top).op (1 : RingSections X ⊤)) =
    E.presheaf.map (homOfLE le_top).op 0
  rw [map_one, map_zero]
  exact hv

/-- Normalization by the unit pullback isomorphism does not change zero. -/
theorem pullSection_eq_zero_iff {X Y : Scheme} (f : X ⟶ Y)
    {E : OModule Y} (a : AlgebraicSection E) :
    pullSection f a = 0 ↔ (Scheme.Modules.pullback f).map a = 0 := by
  constructor
  · intro h
    have hv := unitPullbackMap_pullSection f a
    rw [h, comp_zero] at hv
    exact hv.symm
  · intro h
    dsimp [pullSection, restrictSection]
    rw [h, comp_zero]

/-- The same chosen open occurs in both factors.  These product opens cover
the diagonal support even though they need not cover the whole product. -/
def squareOpen {X : Scheme} (s : X ⟶ ComplexBase) (U : X.Opens) :
    (SelfProduct s).Opens :=
  firstProjection s ⁻¹ᵁ U ⊓ secondProjection s ⁻¹ᵁ U

theorem diagonalPower_squareOpens_cover {X : Scheme}
    (s : X ⟶ ComplexBase) [IsSeparated s] {ι : Type*}
    (U : ι → X.Opens) (hU : iSup U = ⊤) (k : ℕ) (hk : k ≠ 0) :
    (⨆ i, diagonalPowerInclusion s k ⁻¹ᵁ squareOpen s (U i)) = ⊤ := by
  apply top_unique
  intro z _
  have hz : diagonalPowerInclusion s k z ∈ Set.range (diagonal s) := by
    rw [← FatPointOpenFactorizationProof.kernelPowerInclusion_range (diagonal s) k hk]
    exact ⟨z, rfl⟩
  obtain ⟨x, hx⟩ := hz
  have hxU : x ∈ iSup U := by rw [hU]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hxU
  apply TopologicalSpace.Opens.mem_iSup.mpr
  refine ⟨i, ?_⟩
  change diagonalPowerInclusion s k z ∈ squareOpen s (U i)
  rw [← hx]
  constructor
  · change (diagonal s ≫ firstProjection s) x ∈ U i
    rw [pullback.diagonal_fst]
    exact hi
  · change (diagonal s ≫ secondProjection s) x ∈ U i
    rw [pullback.diagonal_snd]
    exact hi

/-- A chart-cover criterion for the original diagonal-order predicate.  Its
local tests are the actual pullbacks along the chosen opens of V(I_Δ^k).
The subsequent coordinate-ring comparison can therefore use only these
charts, including the standard two affine charts of P1. -/
theorem vanishes_iff_squareCover {X : Scheme}
    (s : X ⟶ ComplexBase) [IsSeparated s] {ι : Type*}
    (U : ι → X.Opens) (hU : iSup U = ⊤)
    (E : OModule (SelfProduct s)) (a : AlgebraicSection E)
    (k : ℕ) (hk : k ≠ 0) :
    VanishesToOrderAlongDiagonal s E a k ↔
      ∀ i, (Scheme.Modules.pullback
        ((diagonalPowerInclusion s k ⁻¹ᵁ squareOpen s (U i)).ι ≫
          diagonalPowerInclusion s k)).map a = 0 := by
  constructor
  · intro ha i
    apply (LeBrunSalamon.PhaseFourteen.SliceRestrictionProof.pullback_comp_zero_iff
      _ _ a).mpr
    change (Scheme.Modules.pullback _).map (restrictSection _ a) = 0
    rw [ha, Functor.map_zero]
  · intro ha
    apply (pullSection_eq_zero_iff (diagonalPowerInclusion s k) a).mp
    apply section_eq_zero_of_pullback_cover (pullSection (diagonalPowerInclusion s k) a)
      (fun i => diagonalPowerInclusion s k ⁻¹ᵁ squareOpen s (U i))
      (diagonalPower_squareOpens_cover s U hU k hk)
    intro i
    have hi := (LeBrunSalamon.PhaseFourteen.SliceRestrictionProof.pullback_comp_zero_iff
      _ _ a).mp (ha i)
    change (Scheme.Modules.pullback _).map
      ((unitPullbackIso (diagonalPowerInclusion s k)).inv ≫
        (Scheme.Modules.pullback (diagonalPowerInclusion s k)).map a) = 0
    rw [Functor.map_comp, hi, comp_zero]

end LeBrunSalamon.SectionCoverProof

end

import RecompileSections
import LSProperLocalTopology

/-! The effective-Cartier local criterion, with the defining ideal as
the actual kernel of O_Y -> i_*O_X.  Proper-local globalization is proved
separately, including the complement of the closed subscheme. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight

namespace LeBrunSalamon.EffectiveCartier

abbrev ideal {X Y : Scheme.{0}} (i : X ⟶ Y) : OModule Y :=
  kernel (structurePushforwardMap i)

def line {X Y : Scheme.{0}} (i : X ⟶ Y) (h : IsLocallyFreeOfRank (ideal i) 1) :
    LineBundle Y := dualLine ⟨ideal i, h⟩

def canonicalSection {X Y : Scheme.{0}} (i : X ⟶ Y)
    (h : IsLocallyFreeOfRank (ideal i) 1) : AlgebraicSection (line i h).sheaf :=
  TwoChartSections.homSection (kernel.ι (structurePushforwardMap i))

end LeBrunSalamon.EffectiveCartier

namespace LeBrunSalamon.PublishedInputs.RelativeCartier

/-- Stacks062Y, Lemma31.19.9(2), at a point above the closed point of
a local base.  The two cartesian squares specify the actual residue
fibre and its actual closed immersion.  Invertibility of its kernel is
exactly the definition of effective Cartier (01WQ, Definition31.14.1).
Finite presentation of i is local finite presentation together with the
quasi-compactness and quasi-separatedness already supplied by a closed
immersion.  No properness, projective plane, selected line, or normal
form occurs in this published local input.
https://stacks.math.columbia.edu/tag/062Y -/
theorem near_closed_point
    (R : Type) [CommRing R] [IsLocalRing R]
    {X Y X0 Y0 : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R))
    [Flat p] [LocallyOfFinitePresentation p]
    (i : X ⟶ Y) [IsClosedImmersion i] [LocallyOfFinitePresentation i] [Flat (i ≫ p)]
    (b : Y0 ⟶ Y) (q : Y0 ⟶ Spec (CommRingCat.of (IsLocalRing.ResidueField R)))
    (hb : IsPullback b q p (Spec.map
      (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R)))))
    (a : X0 ⟶ X) (i0 : X0 ⟶ Y0) (hi : IsPullback a i0 i b)
    (h0 : IsLocallyFreeOfRank (EffectiveCartier.ideal i0) 1)
    (x : X) (hx : (i ≫ p).base x = IsLocalRing.closedPoint R) :
    ∃ U : Y.Opens, i.base x ∈ U ∧
      Nonempty ((EffectiveCartier.ideal i).restrict U.ι ≅ structureModule U.toScheme) := by
  sorry

end LeBrunSalamon.PublishedInputs.RelativeCartier

namespace LeBrunSalamon.RelativeCartier

/-- A proper ambient scheme over a local ring promotes the local
Cartier property on the actual closed fibre to global Cartierness.
Points outside the subscheme are handled by the actual unit-ideal
trivialization, rather than an additional hypothesis or admission. -/
theorem of_closed_fibre
    (R : Type) [CommRing R] [IsLocalRing R]
    {X Y X0 Y0 : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R))
    [IsProper p] [Flat p] [LocallyOfFinitePresentation p]
    (i : X ⟶ Y) [IsClosedImmersion i] [LocallyOfFinitePresentation i] [Flat (i ≫ p)]
    (b : Y0 ⟶ Y) (q : Y0 ⟶ Spec (CommRingCat.of (IsLocalRing.ResidueField R)))
    (hb : IsPullback b q p (Spec.map
      (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R)))))
    (a : X0 ⟶ X) (i0 : X0 ⟶ Y0) (hi : IsPullback a i0 i b)
    (h0 : IsLocallyFreeOfRank (EffectiveCartier.ideal i0) 1) :
    IsLocallyFreeOfRank (EffectiveCartier.ideal i) 1 := by
  let I := EffectiveCartier.ideal i
  let J := { U : Y.Opens // Nonempty (I.restrict U.ι ≅ structureModule U.toScheme) }
  let W : Y.Opens := ⨆ u : J, u.val
  have hW : W = ⊤ := by
    apply ProperLocalTopology.open_eq_top_of_closed_point_fibre R p W
    intro y hy
    by_cases hmem : y ∈ Set.range i.base
    · obtain ⟨x, rfl⟩ := hmem
      obtain ⟨U, hx, eU⟩ := PublishedInputs.RelativeCartier.near_closed_point
        R p i b q hb a i0 hi h0 x hy
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨U, eU⟩, hx⟩
    · have hclosed : IsClosed (Set.range i.base) := by
        simpa only [Set.image_univ] using i.isClosedMap Set.univ isClosed_univ
      let U : Y.Opens := ⟨(Set.range i.base)ᶜ, hclosed.isOpen_compl⟩
      have hpre : i ⁻¹ᵁ U.ι.opensRange = ⊥ := by
        rw [Scheme.Opens.opensRange_ι]
        ext x
        change (i.base x ∉ Set.range i.base) ↔ False
        simp only [Set.mem_range_self, not_true_eq_false]
      let eU : I.restrict U.ι ≅ structureModule U.toScheme :=
        P1Ideal.structureKernel_restrict_disjoint i U.ι hpre
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨U, ⟨eU⟩⟩, hmem⟩
  exact P1Ideal.locallyFreeRankOne_of_restrictTrivial I (fun u : J => u.val)
    hW (fun u => Classical.choice u.property)

end LeBrunSalamon.RelativeCartier
end

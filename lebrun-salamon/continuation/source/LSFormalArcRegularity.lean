import LSOpenSectionTransport
import LSFormalArcSections

/-!
# Recovering whole-open regularity from the actual generic point

The fraction-field point is used only through its proved dominance.
Both sections on the actual inverse-image open belong to a locally free
sheaf on a reduced scheme.  Thus comparison at that generic point
recovers equality on the entire open, as required by FormalArcs.Regular.
This argument does not use complex closed points of the fraction field.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.Skeleton

namespace LeBrunSalamon.Construction.StableMaps.FormalArcs

open FamilyBivectors

theorem genericPoint_range_open (U : Trait.Opens) (hU : Dense (U : Set Trait)) :
    Set.range genericPoint ⊆ Set.range U.ι := by
  rw [Scheme.Opens.range_ι]
  obtain ⟨z, hz⟩ := TraitPullback.genericPoint_dense.exists_mem_open U.isOpen hU.nonempty
  rintro _ ⟨w, rfl⟩
  have hw : w = z := Subsingleton.elim w z
  subst w
  exact hz

def genericToOpen (U : Trait.Opens) (hU : Dense (U : Set Trait)) :
    GenericPoint ⟶ U.toScheme :=
  IsOpenImmersion.lift U.ι genericPoint (genericPoint_range_open U hU)

@[reassoc] theorem genericToOpen_inclusion (U : Trait.Opens)
    (hU : Dense (U : Set Trait)) :
    genericToOpen U hU ≫ U.ι = genericPoint :=
  IsOpenImmersion.lift_fac _ _ _

theorem genericToOpen_dense (U : Trait.Opens) (hU : Dense (U : Set Trait)) :
    DenseRange (genericToOpen U hU).base := by
  apply U.ι.isOpenEmbedding.isEmbedding.isInducing.dense_iff.mpr
  intro x
  rw [← Set.range_comp]
  change U.ι x ∈ closure (Set.range (genericToOpen U hU ≫ U.ι))
  rw [genericToOpen_inclusion]
  exact TraitPullback.genericPoint_dense (U.ι x)

/-- A whole-trait section extends a given rational section if the two
actual pullbacks to the fraction-field point agree.  The equality being
tested retains the full canonical open pullback, not only a coefficient
in a freely chosen frame. -/
theorem regular_of_generic_comparison {Y : Scheme} {r : ℕ}
    (E : AlgebraicVectorBundle Y r) (s : NormalExtension.RationalSection E.sheaf)
    (gamma : Trait ⟶ Y) (hU : Dense (gamma ⁻¹ᵁ s.domain : Set Trait))
    (w : AlgebraicSection (pullbackModule gamma E.sheaf))
    (h : pullSection (genericToOpen (gamma ⁻¹ᵁ s.domain) hU)
        (pullSection (gamma ⁻¹ᵁ s.domain).ι w) =
      pullSection (genericToOpen (gamma ⁻¹ᵁ s.domain) hU)
        (OpenSection.fromValue (gamma ⁻¹ᵁ s.domain)
          (pullLocalSection gamma E.sheaf s.domain s.value))) :
    Regular s gamma := by
  let U := gamma ⁻¹ᵁ s.domain
  let B := LeBrunSalamon.PhaseThirtyFive.pullbackBundle U.ι
    (LeBrunSalamon.PhaseThirtyFive.pullbackBundle gamma E)
  letI : IsReduced Trait := inferInstance
  letI : IsReduced U.toScheme := isReduced_of_isOpenImmersion U.ι
  have heq : pullSection U.ι w =
      OpenSection.fromValue U (pullLocalSection gamma E.sheaf s.domain s.value) :=
    dominant_pullSection_injective (genericToOpen U hU) (genericToOpen_dense U hU)
      (fun _ => inferInstance) B h
  have hs := congrArg (fun v => OpenSection.value U v) heq
  rw [OpenSection.value_pullSection, OpenSection.value_section] at hs
  exact ⟨sectionValue w, hs⟩

end LeBrunSalamon.Construction.StableMaps.FormalArcs

end

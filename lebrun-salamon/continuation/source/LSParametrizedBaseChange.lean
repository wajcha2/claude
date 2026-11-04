import LSFamilyBaseChange
import LSFieldParametrization

/-!
# Comparison with actual field-valued parametrizations

The normalized descended sections are first compared over every actual
point of the original parametrization cover, over an arbitrary scheme.
Field-valued alternative parametrizations are compared after the actual
residue-field extension of that cover. No complex-point argument is
applied to a fraction-field spectrum.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.PhaseThirty LeBrunSalamon.PhaseThirtyFive
open LeBrunSalamon.Core LeBrunSalamon.Skeleton LeBrunSalamon.Refinement

namespace LeBrunSalamon.Construction.FamilyBivectors

namespace RelativeSquare

/-- Cartesian source families have Cartesian complete relative squares.
The assertion includes coincident marked points. -/
theorem map_isPullback {C A D B : Scheme} (piA : C ⟶ A) (piB : D ⟶ B)
    (k : C ⟶ D) (b : A ⟶ B) (hk : IsPullback k piA piB b) :
    IsPullback (map piA piB k b hk.w) (left piA ≫ piA) (left piB ≫ piB) b := by
  have hbase : map piA piB k b hk.w ≫ (left piB ≫ piB) =
      (left piA ≫ piA) ≫ b := by
    rw [← Category.assoc, map_left, Category.assoc, hk.w, Category.assoc]
  apply IsPullback.mk' hbase
  · intro T a c ha hc
    apply pullback.hom_ext
    · apply hk.hom_ext
      · simpa only [Category.assoc, map_left] using
          congrArg (fun f => f ≫ left piB) ha
      · simpa only [Category.assoc] using hc
    · apply hk.hom_ext
      · simpa only [Category.assoc, map_right] using
          congrArg (fun f => f ≫ right piB) ha
      · simpa only [Category.assoc, pullback.condition] using hc
  · intro T a c hac
    have h₁ : (a ≫ left piB) ≫ piB = c ≫ b := by
      simpa only [Category.assoc] using hac
    have h₂ : (a ≫ right piB) ≫ piB = c ≫ b := by
      rw [Category.assoc, ← pullback.condition]
      simpa only [Category.assoc] using h₁
    let l₁ := hk.lift (a ≫ left piB) c h₁
    let l₂ := hk.lift (a ≫ right piB) c h₂
    let l := pullback.lift l₁ l₂ (by
      simp only [l₁, l₂, IsPullback.lift_snd])
    refine ⟨l, ?_, ?_⟩
    · apply pullback.hom_ext
      · simp only [l, Category.assoc, map_left, pullback.lift_fst_assoc,
          l₁, IsPullback.lift_fst]
      · simp only [l, Category.assoc, map_right, pullback.lift_snd_assoc,
          l₂, IsPullback.lift_fst]
    · simp only [l, Category.assoc, pullback.lift_fst_assoc, l₁, IsPullback.lift_snd]

end RelativeSquare

namespace Parametrized

variable (P : ProjectiveLineOverC)
variable {A B : Scheme} (sA : A ⟶ ComplexBase) (sB : B ⟶ ComplexBase)
variable (b : A ⟶ B) (hb : b ≫ sB = sA)

abbrev baseChangeSource : Source P sA ⟶ Source P sB :=
  rationalSourceMap P (⟨b, hb⟩ : PointsOver A sA B sB)

@[reassoc] theorem baseChangeSource_first :
    baseChangeSource P sA sB b hb ≫ projection P sB = projection P sA :=
  pullback.lift_fst _ _ _

@[reassoc] theorem baseChangeSource_parameter :
    baseChangeSource P sA sB b hb ≫ parameter P sB = parameter P sA ≫ b :=
  pullback.lift_snd _ _ _

theorem baseChangeSource_isPullback :
    IsPullback (baseChangeSource P sA sB b hb) (parameter P sA) (parameter P sB) b := by
  apply IsPullback.of_right (t := IsPullback.of_hasPullback P.structureMap sB)
  · simpa only [baseChangeSource_first, hb] using
      (IsPullback.of_hasPullback P.structureMap sA)
  · exact baseChangeSource_parameter P sA sB b hb

def baseChangeSquare : Square P sA ⟶ Square P sB :=
  RelativeSquare.map (parameter P sA) (parameter P sB)
    (baseChangeSource P sA sB b hb) b (baseChangeSource_parameter P sA sB b hb)

theorem baseChangeSquare_isPullback :
    IsPullback (baseChangeSquare P sA sB b hb)
      (RelativeSquare.left (parameter P sA) ≫ parameter P sA)
      (RelativeSquare.left (parameter P sB) ≫ parameter P sB) b :=
  RelativeSquare.map_isPullback (parameter P sA) (parameter P sB)
    (baseChangeSource P sA sB b hb) b (baseChangeSource_isPullback P sA sB b hb)

theorem baseChangeSquare_surjective [Surjective b] :
    Surjective (baseChangeSquare P sA sB b hb) :=
  MorphismProperty.of_isPullback (baseChangeSquare_isPullback P sA sB b hb).flip
    (show Surjective b from inferInstance)

theorem baseChangeSquare_flat [Flat b] : Flat (baseChangeSquare P sA sB b hb) :=
  MorphismProperty.of_isPullback (baseChangeSquare_isPullback P sA sB b hb).flip
    (show Flat b from inferInstance)

theorem baseChangeSquare_quasiCompact [QuasiCompact b] :
    QuasiCompact (baseChangeSquare P sA sB b hb) :=
  MorphismProperty.of_isPullback (baseChangeSquare_isPullback P sA sB b hb).flip
    (show QuasiCompact b from inferInstance)

/-- Faithfully flat quasi-compact base change detects an actual section
on the complete source square, including a field extension. -/
theorem baseChangeSquare_section_injective [Flat b] [Surjective b] [QuasiCompact b]
    {r : ℕ} (E : AlgebraicVectorBundle (Square P sB) r) :
    Function.Injective (fun a : AlgebraicSection E.sheaf =>
      pullSection (baseChangeSquare P sA sB b hb) a) := by
  letI := baseChangeSquare_surjective P sA sB b hb
  letI := baseChangeSquare_flat P sA sB b hb
  letI := baseChangeSquare_quasiCompact P sA sB b hb
  exact FlatSectionDescent.pullSection_injective_of_epi (baseChangeSquare P sA sB b hb) E

end Parametrized

end LeBrunSalamon.Construction.FamilyBivectors

end

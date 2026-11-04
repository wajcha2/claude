import LSFormalArcRegularity
import LSFamilyBaseChange
import LSFieldParametrization

/-!
# The two generic marked points in an actual model parametrization

Cartesian source comparisons carry the complete generic family and both
marked points together.  The final maps into the original source square
are equal as scheme morphisms; no equality of only geometric point sets
is substituted for them.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.Skeleton

namespace LeBrunSalamon.Construction.FormalArcSections.Generic

open StableMaps StableMaps.FormalArcs StableMaps.TraitPullback FamilyBivectors

variable {n : ℕ} {X : ContactFanoManifold n}
variable (F : ProjectiveNodalFamily Lines.P Lines.marking
  X.variety X.contact.sequence.line 2)
variable (gamma : PointsOver Trait toC F.Square (F.squareToBase ≫ F.toC))
variable {M : Scheme} (piM : M ⟶ Trait)
variable (u : Source F (baseArc F gamma) ≅ M)
variable (hu : u.hom ≫ piM = parameter F (baseArc F gamma))

abbrev P1 := Parametrized.Source Lines.P (genericPoint ≫ toC)
abbrev projection : P1 ⟶ GenericPoint :=
  Parametrized.parameter Lines.P (genericPoint ≫ toC)

def inverseSource : M ⟶ F.source :=
  u.inv ≫ pullback.fst F.parameter (baseArc F gamma).val

include hu in
theorem inverseSource_isPullback :
    IsPullback (inverseSource F gamma u) piM F.parameter (baseArc F gamma).val := by
  have h : IsPullback u.inv piM (parameter F (baseArc F gamma)) (𝟙 Trait) := by
    apply IsPullback.of_horiz_isIso
    exact ⟨by simpa only [Category.comp_id] using
      Transport.inverse_parameter F gamma piM u hu⟩
  simpa only [Category.id_comp, inverseSource] using
    h.paste_horiz (IsPullback.of_hasPullback F.parameter (baseArc F gamma).val)

variable (k : P1 ⟶ M)
variable (hk : IsPullback k projection piM genericPoint)

def toFamily : P1 ⟶ F.source := k ≫ inverseSource F gamma u

include hu hk in
theorem toFamily_isPullback :
    IsPullback (toFamily F gamma u k) projection F.parameter
      (genericPoint ≫ (baseArc F gamma).val) :=
  hk.paste_horiz (inverseSource_isPullback F gamma piM u hu)

include hu hk in
@[reassoc] theorem toFamily_parameter :
    toFamily F gamma u k ≫ F.parameter =
      projection ≫ (genericPoint ≫ (baseArc F gamma).val) :=
  (toFamily_isPullback F gamma piM u hu k hk).w

def first : GenericPoint ⟶ P1 :=
  hk.lift (genericPoint ≫ Transport.first F gamma u) (𝟙 GenericPoint) (by
    rw [Category.assoc, Transport.first_parameter F gamma piM u hu,
      Category.comp_id, Category.id_comp])

def second : GenericPoint ⟶ P1 :=
  hk.lift (genericPoint ≫ Transport.second F gamma u) (𝟙 GenericPoint) (by
    rw [Category.assoc, Transport.second_parameter F gamma piM u hu,
      Category.comp_id, Category.id_comp])

@[reassoc] theorem first_model : first F gamma piM u hu k hk ≫ k =
    genericPoint ≫ Transport.first F gamma u := IsPullback.lift_fst _ _ _ _

@[reassoc] theorem second_model : second F gamma piM u hu k hk ≫ k =
    genericPoint ≫ Transport.second F gamma u := IsPullback.lift_fst _ _ _ _

@[reassoc] theorem first_parameter : first F gamma piM u hu k hk ≫ projection =
    𝟙 GenericPoint := IsPullback.lift_snd _ _ _ _

@[reassoc] theorem second_parameter : second F gamma piM u hu k hk ≫ projection =
    𝟙 GenericPoint := IsPullback.lift_snd _ _ _ _

def pair : GenericPoint ⟶ RelativeSquare.Space projection :=
  pullback.lift (first F gamma piM u hu k hk) (second F gamma piM u hu k hk)
    ((first_parameter F gamma piM u hu k hk).trans
      (second_parameter F gamma piM u hu k hk).symm)

@[reassoc] theorem pair_first : pair F gamma piM u hu k hk ≫
    RelativeSquare.left projection = first F gamma piM u hu k hk :=
  pullback.lift_fst _ _ _

@[reassoc] theorem pair_second : pair F gamma piM u hu k hk ≫
    RelativeSquare.right projection = second F gamma piM u hu k hk :=
  pullback.lift_snd _ _ _

def toModelSquare : RelativeSquare.Space projection ⟶ RelativeSquare.Space piM :=
  RelativeSquare.map projection piM k genericPoint hk.w

@[reassoc] theorem pair_toModelSquare :
    pair F gamma piM u hu k hk ≫ toModelSquare piM k hk =
      genericPoint ≫ Transport.pair F gamma piM u hu := by
  apply pullback.hom_ext
  · simp only [Category.assoc, toModelSquare, RelativeSquare.map_left,
      pair_first_assoc, Transport.pair_first, first_model]
  · simp only [Category.assoc, toModelSquare, RelativeSquare.map_right,
      pair_second_assoc, Transport.pair_second, second_model]

def toFamilySquare : RelativeSquare.Space projection ⟶ F.Square :=
  RelativeSquare.map projection F.parameter (toFamily F gamma u k)
    (genericPoint ≫ (baseArc F gamma).val)
    (toFamily_parameter F gamma piM u hu k hk)

@[reassoc] theorem first_toFamily :
    first F gamma piM u hu k hk ≫ toFamily F gamma u k =
      (genericPoint ≫ gamma.val) ≫ pullback.fst F.parameter F.parameter := by
  rw [toFamily, ← Category.assoc, first_model]
  simp only [Transport.first, inverseSource, Category.assoc, u.hom_inv_id_assoc,
    firstSection, pullback.lift_fst, pullback.lift_fst_assoc]

@[reassoc] theorem second_toFamily :
    second F gamma piM u hu k hk ≫ toFamily F gamma u k =
      (genericPoint ≫ gamma.val) ≫ pullback.snd F.parameter F.parameter := by
  rw [toFamily, ← Category.assoc, second_model]
  simp only [Transport.second, inverseSource, Category.assoc, u.hom_inv_id_assoc,
    secondSection, pullback.lift_fst, pullback.lift_fst_assoc]

/-- The generic marked pair maps to the original generic arc exactly. -/
@[reassoc] theorem pair_toFamilySquare :
    pair F gamma piM u hu k hk ≫ toFamilySquare F gamma piM u hu k hk =
      genericPoint ≫ gamma.val := by
  apply pullback.hom_ext
  · simp only [Category.assoc, toFamilySquare, RelativeSquare.map_left,
      pair_first_assoc, first_toFamily]
  · simp only [Category.assoc, toFamilySquare, RelativeSquare.map_right,
      pair_second_assoc, second_toFamily]

@[reassoc] theorem toFamilySquare_base :
    toFamilySquare F gamma piM u hu k hk ≫ F.squareToBase =
      (RelativeSquare.left projection ≫ projection) ≫
        (genericPoint ≫ (baseArc F gamma).val) := by
  rw [ProjectiveNodalFamily.squareToBase, ← Category.assoc,
    toFamilySquare, RelativeSquare.map_left, Category.assoc,
    toFamily_parameter F gamma piM u hu k hk]
  simp only [Category.assoc]

variable (b : GenericPoint ⟶ F.smoothOpen.toScheme)
variable (hb : b ≫ F.smoothOpen.ι = genericPoint ≫ (baseArc F gamma).val)

include hb in
theorem toFamilySquare_range :
    Set.range (toFamilySquare F gamma piM u hu k hk) ⊆
      Set.range F.smoothSquareOpen.ι := by
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨z, rfl⟩
  change (toFamilySquare F gamma piM u hu k hk ≫ F.squareToBase) z ∈ F.smoothOpen
  rw [toFamilySquare_base, ← hb]
  exact (b ((RelativeSquare.left projection ≫ projection) z)).property

def toSmoothSquare : RelativeSquare.Space projection ⟶ F.smoothSquareOpen.toScheme :=
  IsOpenImmersion.lift F.smoothSquareOpen.ι (toFamilySquare F gamma piM u hu k hk)
    (toFamilySquare_range F gamma piM u hu k hk b hb)

@[reassoc] theorem toSmoothSquare_inclusion :
    toSmoothSquare F gamma piM u hu k hk b hb ≫ F.smoothSquareOpen.ι =
      toFamilySquare F gamma piM u hu k hk := IsOpenImmersion.lift_fac _ _ _

@[reassoc] theorem pair_toSmoothSquare_inclusion :
    pair F gamma piM u hu k hk ≫ toSmoothSquare F gamma piM u hu k hk b hb ≫
      F.smoothSquareOpen.ι = genericPoint ≫ gamma.val := by
  rw [toSmoothSquare_inclusion, pair_toFamilySquare]

end LeBrunSalamon.Construction.FormalArcSections.Generic

end

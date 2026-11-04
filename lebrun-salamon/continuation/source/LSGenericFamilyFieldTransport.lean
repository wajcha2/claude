import LSFamilyBaseChange
import LSParametrizedBaseChange
import LSFamilySmoothCoordinates
import LSFieldParametrization
import LSFamilyReparametrizationFibres

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

namespace FieldComparison

variable {P : ProjectiveLineOverC} {p : ProjectiveLinePoint P}
variable {n : ℕ} {X : ContactFanoManifold n} {g : VeryFreeContactConic P p X}
variable {N : FullConicNeighborhood P p X g}
variable {F : StableMaps.ProjectiveNodalFamily P p X.variety X.contact.sequence.line 2}
variable (Q : StableMaps.FullHomComparison P p X.variety N.homSpace N.neighborhood
  X.contact.sequence.line 2 F)

/-- A Cartesian parametrization has the original complex structure on
its evaluation map. -/
theorem evaluation_overC {T : Scheme} (sT : T ⟶ ComplexBase)
    (b : T ⟶ F.smoothOpen.toScheme) (hb : (b ≫ F.smoothOpen.ι) ≫ F.toC = sT)
    (k : Parametrized.Source P sT ⟶ F.source)
    (hk : IsPullback k (Parametrized.parameter P sT) F.parameter (b ≫ F.smoothOpen.ι)) :
    (k ≫ F.evaluation) ≫ X.variety.structureMap = Parametrized.parameter P sT ≫ sT := by
  rw [Category.assoc, F.overC, ← Category.assoc, hk.w, Category.assoc, hb]

theorem square_evaluation {T : Scheme} (sT : T ⟶ ComplexBase)
    (b : T ⟶ F.smoothOpen.toScheme) (hb : (b ≫ F.smoothOpen.ι) ≫ F.toC = sT)
    (k : Parametrized.Source P sT ⟶ F.source)
    (hk : IsPullback k (Parametrized.parameter P sT) F.parameter (b ≫ F.smoothOpen.ι))
    (a : Parametrized.Square P sT ⟶ F.smoothSquareOpen.toScheme)
    (ha : a ≫ F.smoothSquareOpen.ι = RelativeSquare.map (Parametrized.parameter P sT)
      F.parameter k (b ≫ F.smoothOpen.ι) hk.w) :
    a ≫ SmoothFamily.smoothEvaluation (F := F) =
      ParametrizedContact.evaluationSquare P sT X (k ≫ F.evaluation)
        (evaluation_overC sT b hb k hk) := by
  rw [SmoothFamily.smoothEvaluation, ← Category.assoc, ha]
  apply pullback.hom_ext
  · simp only [ParametrizedContact.evaluationSquare, Parametrized.evaluationSquare,
      Category.assoc, F.squareEvaluation_first, RelativeSquare.map_left_assoc,
      RelativeSquare.evaluation_left]
  · simp only [ParametrizedContact.evaluationSquare, Parametrized.evaluationSquare,
      Category.assoc, F.squareEvaluation_second, RelativeSquare.map_right_assoc,
      RelativeSquare.evaluation_right]

-- A field structure is chosen only from the actual bundled ring predicate.
variable (K : CommRingCat) [hK : Fact (IsField K)] (sK : Spec K ⟶ ComplexBase)

local instance : Field K := hK.out.toField
variable (b : Spec K ⟶ F.smoothOpen.toScheme)
variable (hb : (b ≫ F.smoothOpen.ι) ≫ F.toC = sK)
variable (k : Parametrized.Source P sK ⟶ F.source)
variable (hk : IsPullback k (Parametrized.parameter P sK) F.parameter (b ≫ F.smoothOpen.ι))

local instance : Surjective Q.toSmooth := Q.smoothSurjective

abbrev extensionToC : Spec (Q.parametrizingField K b) ⟶ ComplexBase :=
  Q.parametrizingExtension K b ≫ sK

def coverPoint : PointsOver (Spec (Q.parametrizingField K b)) (extensionToC Q K sK b)
    Q.cover Q.coverToC :=
  ⟨Q.parametrizingPoint K b, Q.parametrizingPoint_overC K b sK hb⟩

abbrev extendedBase : Spec (Q.parametrizingField K b) ⟶ F.smoothOpen.toScheme :=
  Q.parametrizingExtension K b ≫ b

@[reassoc] theorem coverPoint_base :
    (coverPoint Q K sK b hb).val ≫ Q.toSmooth = extendedBase Q K b :=
  Q.parametrizingPoint_base K b

include hb in
theorem extendedBase_overC :
    (extendedBase Q K b ≫ F.smoothOpen.ι) ≫ F.toC = extensionToC Q K sK b := by
  simp only [extendedBase, extensionToC, Category.assoc] at hb ⊢
  rw [hb]

abbrev sourceMap : Parametrized.Source P (extensionToC Q K sK b) ⟶ Parametrized.Source P sK :=
  Parametrized.baseChangeSource P (extensionToC Q K sK b) sK
    (Q.parametrizingExtension K b) rfl

abbrev squareMap : Parametrized.Square P (extensionToC Q K sK b) ⟶ Parametrized.Square P sK :=
  Parametrized.baseChangeSquare P (extensionToC Q K sK b) sK
    (Q.parametrizingExtension K b) rfl

abbrev extendedSource : Parametrized.Source P (extensionToC Q K sK b) ⟶ F.source :=
  sourceMap Q K sK b ≫ k

include hk in
theorem extendedSource_isPullback :
    IsPullback (extendedSource Q K sK b k)
      (Parametrized.parameter P (extensionToC Q K sK b)) F.parameter
      (extendedBase Q K b ≫ F.smoothOpen.ι) := by
  simpa only [extendedSource, sourceMap, extendedBase, Category.assoc] using
    (Parametrized.baseChangeSource_isPullback P (extensionToC Q K sK b) sK
      (Q.parametrizingExtension K b) rfl).paste_horiz hk

@[reassoc] theorem evaluationSquare_baseChange :
    squareMap Q K sK b ≫
        ParametrizedContact.evaluationSquare P sK X (k ≫ F.evaluation)
          (evaluation_overC sK b hb k hk) =
      ParametrizedContact.evaluationSquare P (extensionToC Q K sK b) X
        (extendedSource Q K sK b k ≫ F.evaluation)
        (evaluation_overC (extensionToC Q K sK b) (extendedBase Q K b)
          (extendedBase_overC Q K sK b hb) (extendedSource Q K sK b k)
          (extendedSource_isPullback Q K sK b k hk)) :=
  RelativeSquare.map_evaluation (Parametrized.parameter P (extensionToC Q K sK b))
    (Parametrized.parameter P sK) (sourceMap Q K sK b) (Q.parametrizingExtension K b)
    (Parametrized.baseChangeSource_parameter P (extensionToC Q K sK b) sK
      (Q.parametrizingExtension K b) rfl)
    X.variety.structureMap (extensionToC Q K sK b) sK
    (extendedSource Q K sK b k ≫ F.evaluation) (k ≫ F.evaluation)
    (evaluation_overC (extensionToC Q K sK b) (extendedBase Q K b)
      (extendedBase_overC Q K sK b hb) (extendedSource Q K sK b k)
      (extendedSource_isPullback Q K sK b k hk))
    (evaluation_overC sK b hb k hk) (Category.assoc _ _ _).symm

theorem left_baseChange :
    pullSection (squareMap Q K sK b)
        (ParametrizedContact.leftSection P sK X (k ≫ F.evaluation)
          (evaluation_overC sK b hb k hk)) ≫
      (compositionPullback (squareMap Q K sK b)
        (ParametrizedContact.evaluationSquare P sK X (k ≫ F.evaluation)
          (evaluation_overC sK b hb k hk))
        (ParametrizedContact.evaluationSquare P (extensionToC Q K sK b) X
          (extendedSource Q K sK b k ≫ F.evaluation)
          (evaluation_overC (extensionToC Q K sK b) (extendedBase Q K b)
            (extendedBase_overC Q K sK b hb) (extendedSource Q K sK b k)
            (extendedSource_isPullback Q K sK b k hk)))
        (evaluationSquare_baseChange Q K sK b hb k hk)
        (movingPairBundleLeft X.variety X.contact)).hom =
      ParametrizedContact.leftSection P (extensionToC Q K sK b) X
        (extendedSource Q K sK b k ≫ F.evaluation)
        (evaluation_overC (extensionToC Q K sK b) (extendedBase Q K b)
          (extendedBase_overC Q K sK b hb) (extendedSource Q K sK b k)
          (extendedSource_isPullback Q K sK b k hk)) :=
  ParametrizedContact.leftSection_baseChange P (extensionToC Q K sK b) sK
    (Q.parametrizingExtension K b) rfl (sourceMap Q K sK b)
    (Parametrized.baseChangeSource_first P (extensionToC Q K sK b) sK
      (Q.parametrizingExtension K b) rfl)
    (Parametrized.baseChangeSource_parameter P (extensionToC Q K sK b) sK
      (Q.parametrizingExtension K b) rfl)
    X (k ≫ F.evaluation) (evaluation_overC sK b hb k hk)
    (extendedSource Q K sK b k ≫ F.evaluation)
    (evaluation_overC (extensionToC Q K sK b) (extendedBase Q K b)
      (extendedBase_overC Q K sK b hb) (extendedSource Q K sK b k)
      (extendedSource_isPullback Q K sK b k hk))
    (Category.assoc _ _ _).symm (squareMap Q K sK b)
    (RelativeSquare.map_left _ _ _ _ _) (RelativeSquare.map_right _ _ _ _ _)
    (evaluationSquare_baseChange Q K sK b hb k hk)

theorem right_baseChange :
    pullSection (squareMap Q K sK b)
        (ParametrizedContact.rightSection P sK X (k ≫ F.evaluation)
          (evaluation_overC sK b hb k hk)) ≫
      (compositionPullback (squareMap Q K sK b)
        (ParametrizedContact.evaluationSquare P sK X (k ≫ F.evaluation)
          (evaluation_overC sK b hb k hk))
        (ParametrizedContact.evaluationSquare P (extensionToC Q K sK b) X
          (extendedSource Q K sK b k ≫ F.evaluation)
          (evaluation_overC (extensionToC Q K sK b) (extendedBase Q K b)
            (extendedBase_overC Q K sK b hb) (extendedSource Q K sK b k)
            (extendedSource_isPullback Q K sK b k hk)))
        (evaluationSquare_baseChange Q K sK b hb k hk)
        (movingPairBundleRight X.variety X.contact)).hom =
      ParametrizedContact.rightSection P (extensionToC Q K sK b) X
        (extendedSource Q K sK b k ≫ F.evaluation)
        (evaluation_overC (extensionToC Q K sK b) (extendedBase Q K b)
          (extendedBase_overC Q K sK b hb) (extendedSource Q K sK b k)
          (extendedSource_isPullback Q K sK b k hk)) :=
  ParametrizedContact.rightSection_baseChange P (extensionToC Q K sK b) sK
    (Q.parametrizingExtension K b) rfl (sourceMap Q K sK b)
    (Parametrized.baseChangeSource_first P (extensionToC Q K sK b) sK
      (Q.parametrizingExtension K b) rfl)
    (Parametrized.baseChangeSource_parameter P (extensionToC Q K sK b) sK
      (Q.parametrizingExtension K b) rfl)
    X (k ≫ F.evaluation) (evaluation_overC sK b hb k hk)
    (extendedSource Q K sK b k ≫ F.evaluation)
    (evaluation_overC (extensionToC Q K sK b) (extendedBase Q K b)
      (extendedBase_overC Q K sK b hb) (extendedSource Q K sK b k)
      (extendedSource_isPullback Q K sK b k hk))
    (Category.assoc _ _ _).symm (squareMap Q K sK b)
    (RelativeSquare.map_left _ _ _ _ _) (RelativeSquare.map_right _ _ _ _ _)
    (evaluationSquare_baseChange Q K sK b hb k hk)

variable (a : Parametrized.Square P sK ⟶ F.smoothSquareOpen.toScheme)
variable (ha : a ≫ F.smoothSquareOpen.ι = RelativeSquare.map (Parametrized.parameter P sK)
  F.parameter k (b ≫ F.smoothOpen.ι) hk.w)

abbrev extendedSquare : Parametrized.Square P (extensionToC Q K sK b) ⟶
    F.smoothSquareOpen.toScheme := squareMap Q K sK b ≫ a

@[reassoc] theorem extendedSquare_family :
    extendedSquare Q K sK b a ≫ F.smoothSquareOpen.ι =
      RelativeSquare.map (Parametrized.parameter P (extensionToC Q K sK b))
        F.parameter (extendedSource Q K sK b k) (extendedBase Q K b ≫ F.smoothOpen.ι)
        (extendedSource_isPullback Q K sK b k hk).w := by
  rw [extendedSquare, Category.assoc, ha]
  apply pullback.hom_ext
  · simp only [squareMap, Parametrized.baseChangeSquare, Category.assoc,
      RelativeSquare.map_left, RelativeSquare.map_left_assoc, extendedSource, sourceMap]
  · simp only [squareMap, Parametrized.baseChangeSquare, Category.assoc,
      RelativeSquare.map_right, RelativeSquare.map_right_assoc, extendedSource, sourceMap]

/-- The whole-square extension is a faithfully flat quasi-compact
cover, so the field comparison can descend without selecting a section. -/
theorem squareMap_section_injective {r : ℕ}
    (E : AlgebraicVectorBundle (Parametrized.Square P sK) r) :
    Function.Injective (fun s : AlgebraicSection E.sheaf =>
      pullSection (squareMap Q K sK b) s) := by
  letI : Surjective (Q.parametrizingExtension K b) := Q.parametrizingExtension_surjective K b
  letI : Flat (Q.parametrizingExtension K b) := inferInstance
  letI : QuasiCompact (Q.parametrizingExtension K b) := by
    apply (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).mpr
    infer_instance
  exact Parametrized.baseChangeSquare_section_injective P (extensionToC Q K sK b) sK
    (Q.parametrizingExtension K b) rfl E

end FieldComparison

end LeBrunSalamon.Construction.FamilyBivectors

end

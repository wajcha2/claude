import LSTraitContact
import LSFamilyBivectors
import LSConicModelSections
import LSModelGeometry

/-!
# Regular vector tensors on the complete two-component model

The contact scalar is divided by the actual smoothing element in the
base ring before forming either vector section.  No reciprocal of that
element occurs in these definitions.  The two contact images agree by
the equality of the two maps to the base of the relative square.

The comparison with the canonical bivector on the smooth generic fibre
is a separate geometric statement.  These constructions by themselves
do not assert that the global moving-pair construction is complete.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.PhaseThirtyFive LeBrunSalamon.Core LeBrunSalamon.Skeleton
open LeBrunSalamon.Refinement

namespace LeBrunSalamon.Construction.TraitContact

local notation "Model" => LeBrunSalamon.Construction.StableMaps.FormalArcs.Model

namespace ScalarTensor

/-- A scalar may be moved from one source tensor factor to the other.
This uses the actual tensor universal property, including on nonreduced
open sets. -/
theorem move {Y : Scheme} {E E' F F' : OModule Y}
    (a : RingSections Y ⊤) (f : E ⟶ E') (g : F ⟶ F') :
    tensorMap (GlobalScalars.scalarEnd E a ≫ f) g =
      tensorMap f (GlobalScalars.scalarEnd F a ≫ g) := by
  apply ((tensorPresentation E F).universal _).1
  apply sheafBilinearMap_ext
  intro U x y
  change (tensorMap (GlobalScalars.scalarEnd E a ≫ f) g).app U
      ((tensorPresentation E F).pair.apply U x y) =
    (tensorMap f (GlobalScalars.scalarEnd F a ≫ g)).app U
      ((tensorPresentation E F).pair.apply U x y)
  rw [tensorMap_apply, tensorMap_apply]
  change (tensorPresentation E' F').pair.apply U
      (f.app U ((GlobalScalars.scalarEnd E a).app U x)) (g.app U y) =
    (tensorPresentation E' F').pair.apply U (f.app U x)
      (g.app U ((GlobalScalars.scalarEnd F a).app U y))
  simp only [GlobalScalars.scalarEnd_app, map_smul, LinearMap.smul_apply]

/-- On the relative square, both appearances of a base function are
the same regular function.  This equality is the precise reason that
one contact factor suffices for either vector lift. -/
theorem relative_move {C B : Scheme} (pi : C ⟶ B)
    {E E' F F' : OModule C} (a : RingSections B ⊤)
    (f : E ⟶ E') (g : F ⟶ F') :
    FamilyBivectors.RelativeSquare.boxMap pi
        (GlobalScalars.scalarEnd E (pi.appTop a) ≫ f) g =
      FamilyBivectors.RelativeSquare.boxMap pi f
        (GlobalScalars.scalarEnd F (pi.appTop a) ≫ g) := by
  have ha : (pullback.fst pi pi).appTop (pi.appTop a) =
      (pullback.snd pi pi).appTop (pi.appTop a) := by
    exact congrArg (fun k : pullback pi pi ⟶ B => k.appTop a)
      (pullback.condition (f := pi) (g := pi))
  unfold FamilyBivectors.RelativeSquare.boxMap
  rw [Functor.map_comp, Functor.map_comp,
    LineEndomorphisms.scalarEnd_pullback, LineEndomorphisms.scalarEnd_pullback]
  rw [move, ha]

end ScalarTensor

namespace RegularModel

open StableMaps.FormalArcs FamilyBivectors

variable {n : ℕ} (X : ContactFanoManifold n)
    (F : Smoothing.StandardSource) (a : Coefficients)
    (e : Model F a ⟶ X.variety.scheme)
    (he : e ≫ X.variety.structureMap = modelProjection F a ≫ toC)

abbrev evaluationSquare : ModelNumerator.Square F a ⟶
    SelfProduct X.variety.structureMap :=
  RelativeSquare.evaluation (modelProjection F a) X.variety.structureMap toC e he

/-- The divided contact map is a regular morphism of the actual line
bundles on the entire model.  Its coefficient is a power series c. -/
def dividedContact
    (ell : (modelLine F a).sheaf ≅ pullbackModule e X.contact.sequence.line.sheaf)
    (c : Coefficients) :
    (modelLine F a).sheaf ⟶ pullbackModule e X.contact.sequence.line.sheaf :=
  GlobalScalars.scalarEnd (modelLine F a).sheaf
    ((modelProjection F a).appTop (coefficientSection c)) ≫ ell.hom

/-- All required hypotheses concern the actual source and contact map.
The divisibility test is on R/(a), so it retains the full thickness. -/
theorem dividedContact_exists
    (hfunctions : Function.Bijective (modelProjection F a).appTop)
    (ell : (modelLine F a).sheaf ≅ pullbackModule e X.contact.sequence.line.sheaf)
    (node : ComplexBase ⟶ F.source)
    (hnode : node ≫ F.parameter = Smoothing.scalarPoint 0)
    (hzero : (Scheme.Modules.pullback node).map
      (StandardConicDifferential.fundamentalClass F) = 0) :
    ∃ c : Coefficients, ContactScalar.morphism X F a e he =
      GlobalScalars.scalarEnd (modelLine F a).sheaf
        ((modelProjection F a).appTop (coefficientSection a)) ≫
          dividedContact X F a e ell c := by
  obtain ⟨h, hh, _⟩ := ContactScalar.existsUnique X F a e he hfunctions ell
  obtain ⟨c, hc⟩ := ThickenedNode.contact_coefficient_divisible
    F a node hnode X e he ell h hh hzero
  refine ⟨c, ?_⟩
  rw [hh, hc, dividedContact]
  have hm : coefficientSection (a * c) = coefficientSection a * coefficientSection c :=
    map_mul (Scheme.ΓSpecIso (CommRingCat.of Coefficients)).inv a c
  rw [hm, map_mul, GlobalScalars.scalarEnd_mul, Category.assoc]

variable (ell : (modelLine F a).sheaf ≅ pullbackModule e X.contact.sequence.line.sheaf)
    (c : Coefficients)

/-- A global vector tensor defined without division, including over
the nodal locus and the diagonal of the complete source square. -/
def leftRaw : AlgebraicSection
    (RelativeSquare.box (modelProjection F a)
      (pullbackModule e (tangentSheaf X.variety.structureMap))
      (pullbackModule e X.contact.sequence.line.sheaf)) :=
  ModelNumerator.numerator F a ≫
    RelativeSquare.boxMap (modelProjection F a)
      (LogarithmicSource.velocity F a X.variety e he)
      (dividedContact X F a e ell c)

def rightRaw : AlgebraicSection
    (RelativeSquare.box (modelProjection F a)
      (pullbackModule e X.contact.sequence.line.sheaf)
      (pullbackModule e (tangentSheaf X.variety.structureMap))) :=
  ModelNumerator.numerator F a ≫
    RelativeSquare.boxMap (modelProjection F a)
      (dividedContact X F a e ell c)
      (LogarithmicSource.velocity F a X.variety e he)

/-- Both vector sections use the original intrinsic target bundles. -/
def leftSection : AlgebraicSection
    (pullbackModule (evaluationSquare X F a e he)
      (movingPairBundleLeft X.variety X.contact)) :=
  leftRaw X F a e he ell c ≫
    RelativeSquare.comparison (modelProjection F a)
      X.variety.structureMap toC e he
      (tangentSheaf X.variety.structureMap) X.contact.sequence.line.sheaf

def rightSection : AlgebraicSection
    (pullbackModule (evaluationSquare X F a e he)
      (movingPairBundleRight X.variety X.contact)) :=
  rightRaw X F a e he ell c ≫
    RelativeSquare.comparison (modelProjection F a)
      X.variety.structureMap toC e he
      X.contact.sequence.line.sheaf (tangentSheaf X.variety.structureMap)

/-- The two actual contact values are equal on the entire square.
No generic-fibre injection or cancellation by a possibly vanishing
function is used to prove this equality. -/
theorem commonContact
    (hc : ContactScalar.morphism X F a e he =
      GlobalScalars.scalarEnd (modelLine F a).sheaf
        ((modelProjection F a).appTop (coefficientSection a)) ≫
          dividedContact X F a e ell c) :
    leftSection X F a e he ell c ≫
        (Scheme.Modules.pullback (evaluationSquare X F a e he)).map
          (movingPairContactLeft X.variety X.contact) =
      rightSection X F a e he ell c ≫
        (Scheme.Modules.pullback (evaluationSquare X F a e he)).map
          (movingPairContactRight X.variety X.contact) := by
  change (ModelNumerator.numerator F a ≫
    RelativeSquare.boxMap (modelProjection F a)
      (LogarithmicSource.velocity F a X.variety e he)
      (dividedContact X F a e ell c) ≫
    RelativeSquare.comparison (modelProjection F a)
      X.variety.structureMap toC e he
      (tangentSheaf X.variety.structureMap) X.contact.sequence.line.sheaf) ≫
      (Scheme.Modules.pullback (evaluationSquare X F a e he)).map
        (externalTensorMap X.variety.structureMap X.contact.sequence.form (𝟙 _)) =
    (ModelNumerator.numerator F a ≫
      RelativeSquare.boxMap (modelProjection F a)
        (dividedContact X F a e ell c)
        (LogarithmicSource.velocity F a X.variety e he) ≫
      RelativeSquare.comparison (modelProjection F a)
        X.variety.structureMap toC e he
        X.contact.sequence.line.sheaf (tangentSheaf X.variety.structureMap)) ≫
      (Scheme.Modules.pullback (evaluationSquare X F a e he)).map
        (externalTensorMap X.variety.structureMap (𝟙 _) X.contact.sequence.form)
  simp only [Category.assoc]
  rw [← RelativeSquare.comparison_naturality,
    ← RelativeSquare.comparison_naturality]
  simp only [← Category.assoc, RelativeSquare.boxMap_comp,
    CategoryTheory.Functor.map_id, Category.comp_id]
  change ModelNumerator.numerator F a ≫
      RelativeSquare.boxMap (modelProjection F a)
        (ContactScalar.morphism X F a e he)
        (dividedContact X F a e ell c) ≫ _ =
    ModelNumerator.numerator F a ≫
      RelativeSquare.boxMap (modelProjection F a)
        (dividedContact X F a e ell c)
        (ContactScalar.morphism X F a e he) ≫ _
  rw [hc, ScalarTensor.relative_move]

/-- The exact scalar required by the vector construction exists for
every nonzero smoothing series.  The node and global-functions
hypotheses of the intermediate lemma are now discharged by proofs. -/
theorem dividedContact_exists_of_nonzero (ha : a ≠ 0) :
    ∃ c : Coefficients, ContactScalar.morphism X F a e he =
      GlobalScalars.scalarEnd (modelLine F a).sheaf
        ((modelProjection F a).appTop (coefficientSection a)) ≫
          dividedContact X F a e ell c :=
  dividedContact_exists X F a e he
    (StableMaps.FormalArcs.ModelGeometry.model_globalFunctions F a ha) ell
    (ConicModelSections.node F) (ConicModelSections.node_parameter F)
    (ConicModelSections.fundamentalClass_node_zero F)

/-- Both tensors are actual globally regular sections on the full
model square.  The common contact value uses the original intrinsic
target maps.  Normalization on the generic fibre is separate. -/
theorem regularPair_exists (ha : a ≠ 0) :
    ∃ c : Coefficients,
      ContactScalar.morphism X F a e he =
        GlobalScalars.scalarEnd (modelLine F a).sheaf
          ((modelProjection F a).appTop (coefficientSection a)) ≫
            dividedContact X F a e ell c ∧
      leftSection X F a e he ell c ≫
          (Scheme.Modules.pullback (evaluationSquare X F a e he)).map
            (movingPairContactLeft X.variety X.contact) =
        rightSection X F a e he ell c ≫
          (Scheme.Modules.pullback (evaluationSquare X F a e he)).map
            (movingPairContactRight X.variety X.contact) := by
  obtain ⟨c, hc⟩ := dividedContact_exists_of_nonzero X F a e he ell ha
  exact ⟨c, hc, commonContact X F a e he ell c hc⟩

end RegularModel

end LeBrunSalamon.Construction.TraitContact

end

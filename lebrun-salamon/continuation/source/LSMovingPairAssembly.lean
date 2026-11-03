import RecompileExtensionsPart04

/-!
# Extension and assembly of the two actual moving-pair sections

The target sheaves are fixed by the intrinsic contact structure. Both
rational sections are extended separately from their actual height-one
regularity. Their contact images agree globally because they agree on
the same dense open. The resulting object has exactly the original
`ProperPair` data, including the canonical unit pullback convention.
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
open LeBrunSalamon.Construction.Descent

namespace LeBrunSalamon.Construction.MovingPair

variable {n : ℕ} {X : ContactFanoManifold n} {Y : Scheme}

/-- The first actual tensor target, with its local freeness proved. -/
def leftBundle (p : Y ⟶ SelfProduct X.variety.structureMap) :
    AlgebraicVectorBundle Y (2 * n + 1) where
  sheaf := pullbackModule p (movingPairBundleLeft X.variety X.contact)
  locallyFree := by
    apply pullback_locallyFree p
    change IsLocallyFreeOfRank
      (tensorSheaf
        (pullbackModule (firstProjection X.variety.structureMap)
          (tangentSheaf X.variety.structureMap))
        (pullbackModule (secondProjection X.variety.structureMap)
          X.contact.sequence.line.sheaf)) (2 * n + 1)
    simpa only [intrinsicTangentBundle, Nat.mul_one] using tensorSheaf_locallyFree
      (pullback_locallyFree (firstProjection X.variety.structureMap)
        (intrinsicTangentBundle X.variety).locallyFree)
      (pullback_locallyFree (secondProjection X.variety.structureMap)
        X.contact.sequence.line.locallyFree)

/-- The second actual tensor target; its factors occur in the other order. -/
def rightBundle (p : Y ⟶ SelfProduct X.variety.structureMap) :
    AlgebraicVectorBundle Y (2 * n + 1) where
  sheaf := pullbackModule p (movingPairBundleRight X.variety X.contact)
  locallyFree := by
    apply pullback_locallyFree p
    change IsLocallyFreeOfRank
      (tensorSheaf
        (pullbackModule (firstProjection X.variety.structureMap)
          X.contact.sequence.line.sheaf)
        (pullbackModule (secondProjection X.variety.structureMap)
          (tangentSheaf X.variety.structureMap))) (2 * n + 1)
    simpa only [intrinsicTangentBundle, Nat.one_mul] using tensorSheaf_locallyFree
      (pullback_locallyFree (firstProjection X.variety.structureMap)
        X.contact.sequence.line.locallyFree)
      (pullback_locallyFree (secondProjection X.variety.structureMap)
        (intrinsicTangentBundle X.variety).locallyFree)

def valueBundle (p : Y ⟶ SelfProduct X.variety.structureMap) : LineBundle Y :=
  pullbackLine p (externalSquareLine X.variety.structureMap X.contact.sequence.line)

abbrev leftContact (p : Y ⟶ SelfProduct X.variety.structureMap) :
    (leftBundle p).sheaf ⟶ (valueBundle p).sheaf :=
  (Scheme.Modules.pullback p).map (movingPairContactLeft X.variety X.contact)

abbrev rightContact (p : Y ⟶ SelfProduct X.variety.structureMap) :
    (rightBundle p).sheaf ⟶ (valueBundle p).sheaf :=
  (Scheme.Modules.pullback p).map (movingPairContactRight X.variety X.contact)

/-- Actual rational sections with an actual dense-open contact equality.
There is no regularity or extension assumption in these data. -/
structure RationalVectorPair (p : Y ⟶ SelfProduct X.variety.structureMap) where
  domain : Y.Opens
  dense : Dense (domain : Set Y)
  leftSection : SectionsOn (leftBundle p).sheaf domain
  rightSection : SectionsOn (rightBundle p).sheaf domain
  common : (leftContact p).app domain leftSection =
    (rightContact p).app domain rightSection

namespace RationalVectorPair

variable {p : Y ⟶ SelfProduct X.variety.structureMap} (R : RationalVectorPair p)

def leftRational : NormalExtension.RationalSection (leftBundle p).sheaf :=
  ⟨R.domain, R.dense, R.leftSection⟩

def rightRational : NormalExtension.RationalSection (rightBundle p).sheaf :=
  ⟨R.domain, R.dense, R.rightSection⟩

/-- Both genuine global sections and their restrictions to the rational
domain. The common image uses the original intrinsic contact maps. -/
structure Extension where
  leftSection : AlgebraicSection (leftBundle p).sheaf
  rightSection : AlgebraicSection (rightBundle p).sheaf
  extendsLeft : NormalExtension.Extends R.leftRational (sectionValue leftSection)
  extendsRight : NormalExtension.Extends R.rightRational (sectionValue rightSection)
  common : leftSection ≫ leftContact p = rightSection ≫ rightContact p

/-- The published normal extension theorem is applied to each locally
free vector target. Equality of contact values is an ordinary consequence
of dense restriction injectivity for the actual pulled-back line. -/
theorem extension_exists
    (hI : IntegralScheme Y) (hN : NormalScheme Y)
    (hNoeth : NormalExtension.NoetherianOnAffines Y)
    (hl : ∀ y : Y, ringKrullDim (Y.presheaf.stalk y) = 1 →
      NormalExtension.RegularAt R.leftRational y)
    (hr : ∀ y : Y, ringKrullDim (Y.presheaf.stalk y) = 1 →
      NormalExtension.RegularAt R.rightRational y) :
    Nonempty R.Extension := by
  obtain ⟨a, ha, _⟩ := NormalExtension.extend_from_heightOne
    (leftBundle p) hI hN hNoeth R.leftRational hl
  obtain ⟨b, hb, _⟩ := NormalExtension.extend_from_heightOne
    (rightBundle p) hI hN hNoeth R.rightRational hr
  have hc : (leftContact p).app ⊤ a = (rightContact p).app ⊤ b := by
    apply NormalExtension.morphism_values_agree_from_dense
      (leftBundle p) (rightBundle p) (valueBundle p) hI a b
      (leftContact p) (rightContact p) R.domain R.dense
    rw [sheafHom_naturality, sheafHom_naturality]
    change (leftContact p).app R.domain
        ((leftBundle p).sheaf.presheaf.map (homOfLE le_top).op a) =
      (rightContact p).app R.domain
        ((rightBundle p).sheaf.presheaf.map (homOfLE le_top).op b)
    rw [show (leftBundle p).sheaf.presheaf.map (homOfLE le_top).op a =
      R.leftSection from ha]
    rw [show (rightBundle p).sheaf.presheaf.map (homOfLE le_top).op b =
      R.rightSection from hb]
    exact R.common
  refine ⟨{
    leftSection := sectionFromValue a
    rightSection := sectionFromValue b
    extendsLeft := ?_
    extendsRight := ?_
    common := ?_ }⟩
  · simpa only [sectionFromValue_spec] using ha
  · simpa only [sectionFromValue_spec] using hb
  · apply (sectionValue_bijective (valueBundle p).sheaf).injective
    simpa only [sectionValue_comp, sectionFromValue_spec] using hc

namespace Extension

variable {R : RationalVectorPair p} (E : R.Extension)

/-- Convert ordinary global sections into the original pulled-unit
morphisms. Properness, dominance and integrality concern this same Y. -/
def properPair (hp : IsProper p) (hd : DenseRange (fun y : Y => p y))
    (hI : IntegralScheme Y) : ProperPair X where
  pair := {
    data := {
      source := Y
      projection := p
      proper := hp
      dominant := hd
      map12 := movingPairContactLeft X.variety X.contact
      map21 := movingPairContactRight X.variety X.contact
      vectorLift12 := (unitPullbackIso p).hom ≫ E.leftSection
      vectorLift21 := (unitPullbackIso p).hom ≫ E.rightSection
      commonContactValue := by
        simpa only [Category.assoc] using
          congrArg (fun q => (unitPullbackIso p).hom ≫ q) E.common }
    mapLeft := rfl
    mapRight := rfl }
  irreducible := hI.1
  reduced := hI.2

/-- The normalized common value is precisely the contact image of the
extended first section, with no arbitrary frame or scalar factor. -/
theorem properPair_value (hp : IsProper p) (hd : DenseRange (fun y : Y => p y))
    (hI : IntegralScheme Y) :
    (E.properPair hp hd hI).value = E.leftSection ≫ leftContact p := by
  change (unitPullbackIso p).inv ≫
      (((unitPullbackIso p).hom ≫ E.leftSection) ≫ leftContact p) =
    E.leftSection ≫ leftContact p
  exact (congrArg (fun q => (unitPullbackIso p).inv ≫ q)
    (Category.assoc (unitPullbackIso p).hom E.leftSection (leftContact p))).trans
      (Iso.inv_hom_id_assoc (unitPullbackIso p) (E.leftSection ≫ leftContact p))

theorem properPair_value_right (hp : IsProper p)
    (hd : DenseRange (fun y : Y => p y)) (hI : IntegralScheme Y) :
    (E.properPair hp hd hI).value = E.rightSection ≫ rightContact p :=
  (E.properPair_value hp hd hI).trans E.common

end Extension
end RationalVectorPair

end LeBrunSalamon.Construction.MovingPair

end

#print axioms LeBrunSalamon.Construction.MovingPair.RationalVectorPair.extension_exists

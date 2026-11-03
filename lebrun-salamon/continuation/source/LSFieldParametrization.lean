import LSStableMapFamily

/-!
# Actual parametrizations after a field extension

Surjectivity of the parametrization cover gives a point of its literal
pullback to any field-valued base point.  The residue field of that point
then supplies an actual lift.  The extension is allowed to be larger
than the original field; no complex point is presumed to exist.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.Skeleton

namespace LeBrunSalamon.Construction.FieldLift

variable {Y B : Scheme} (q : Y ⟶ B) [Surjective q]
-- The field predicate refers to the bundled ring actually used by Spec K.
variable (K : CommRingCat) [hK : Fact (IsField K)] (b : Spec K ⟶ B)

private theorem canonicalField_commRing :
    (hK.out.toField).toCommRing = K.commRing := rfl

local instance : Field K := hK.out.toField

abbrev Cover := pullback q b

def point : Cover q K b :=
  Classical.choose ((pullback.snd q b).surjective (Classical.choice inferInstance))

def field : CommRingCat := (Cover q K b).residueField (point q K b)

instance field_isField : Field (field q K b) := by
  unfold field
  infer_instance

/-- The residue field has its actual canonical ring structure. -/
instance field_isFieldFact : Fact (IsField (field q K b)) := by
  change Fact (IsField (IsLocalRing.ResidueField
    ((Cover q K b).presheaf.stalk (point q K b))))
  exact ⟨Field.toIsField _⟩

def extension : Spec (field q K b) ⟶ Spec K :=
  (Cover q K b).fromSpecResidueField (point q K b) ≫ pullback.snd q b

def lift : Spec (field q K b) ⟶ Y :=
  (Cover q K b).fromSpecResidueField (point q K b) ≫ pullback.fst q b

@[reassoc] theorem lift_base : lift q K b ≫ q = extension q K b ≫ b := by
  simp only [lift, extension, Category.assoc, pullback.condition]

/-- Every map of spectra of fields is surjective.  This is the actual
field extension map just constructed, not a map chosen from cardinality. -/
theorem extension_surjective : Surjective (extension q K b) := by
  refine ⟨fun x => ⟨Classical.choice inferInstance, ?_⟩⟩
  exact Subsingleton.elim (α := PrimeSpectrum K) _ _

theorem extension_dense : DenseRange (extension q K b).base := by
  letI : Surjective (extension q K b) := extension_surjective q K b
  exact (extension q K b).surjective.denseRange

/-- Pulling back a locally free section through this field extension
is injective.  It therefore suffices to compare the actual lifted pair. -/
theorem pullSection_injective {r : ℕ} (E : AlgebraicVectorBundle (Spec K) r) :
    Function.Injective (pullSection (extension q K b) (E := E.sheaf)) :=
  dominant_pullSection_injective (extension q K b) (extension_dense q K b)
    (fun U => AlgebraicGeometry.IsReduced.component_reduced (X := Spec K) U) E

end LeBrunSalamon.Construction.FieldLift

namespace LeBrunSalamon.Construction.StableMaps.FullHomComparison

variable {P : ProjectiveLineOverC} {p : ProjectiveLinePoint P}
variable {d : ℕ} {X : SmoothProperComplexVariety d}
variable {H : HomSpacePresentation P X} {U : H.parameter.Opens}
variable {L : LineBundle X.scheme} {degree : ℕ}
variable {F : ProjectiveNodalFamily P p X L degree}
variable (Q : FullHomComparison P p X H U L degree F)

section ArbitraryBase

variable {T : Scheme} (sT : T ⟶ ComplexBase)
variable (q : PointsOver T sT Q.cover Q.coverToC)

def atPointSource : RationalSourceOver P T sT ⟶ Q.parametrizedSource :=
  rationalSourceMap P q

@[reassoc] theorem atPointSource_first :
    Q.atPointSource sT q ≫ pullback.fst P.structureMap Q.coverToC =
      pullback.fst P.structureMap sT := pullback.lift_fst _ _ _

@[reassoc] theorem atPointSource_parameter :
    Q.atPointSource sT q ≫ Q.parametrizedParameter =
      pullback.snd P.structureMap sT ≫ q.val := pullback.lift_snd _ _ _

theorem atPointSource_isPullback :
    IsPullback (Q.atPointSource sT q) (pullback.snd P.structureMap sT)
      Q.parametrizedParameter q.val := by
  apply IsPullback.of_right
    (t := IsPullback.of_hasPullback P.structureMap Q.coverToC)
  · simpa only [atPointSource_first, q.property] using
      (IsPullback.of_hasPullback P.structureMap sT)
  · exact Q.atPointSource_parameter sT q

def atPointMap : RationalSourceOver P T sT ⟶ F.source :=
  Q.atPointSource sT q ≫ Q.sourceMap

@[reassoc] theorem atPointMap_parameter :
    Q.atPointMap sT q ≫ F.parameter =
      pullback.snd P.structureMap sT ≫ (q.val ≫ Q.coverToBase) := by
  rw [atPointMap, Category.assoc, Q.sourceMap_parameter,
    ← Category.assoc, Q.atPointSource_parameter, Category.assoc]

theorem atPointMap_isPullback :
    IsPullback (Q.atPointMap sT q) (pullback.snd P.structureMap sT)
      F.parameter (q.val ≫ Q.coverToBase) :=
  (Q.atPointSource_isPullback sT q).paste_horiz Q.sourceMap_isPullback

/-- The same source identification holds over every actual test base,
including spectra of extension fields. -/
def atPointIso : RationalSourceOver P T sT ≅
    pullback F.parameter (q.val ≫ Q.coverToBase) :=
  (Q.atPointMap_isPullback sT q).isoPullback

@[reassoc] theorem atPointIso_source :
    (Q.atPointIso sT q).hom ≫ pullback.fst F.parameter (q.val ≫ Q.coverToBase) =
      Q.atPointMap sT q := (Q.atPointMap_isPullback sT q).isoPullback_hom_fst

@[reassoc] theorem atPointIso_parameter :
    (Q.atPointIso sT q).hom ≫ pullback.snd F.parameter (q.val ≫ Q.coverToBase) =
      pullback.snd P.structureMap sT :=
  (Q.atPointMap_isPullback sT q).isoPullback_hom_snd

end ArbitraryBase

variable (K : CommRingCat) [Fact (IsField K)]
variable (b : Spec K ⟶ F.smoothOpen.toScheme)

local instance : Surjective Q.toSmooth := Q.smoothSurjective

abbrev parametrizingField : CommRingCat := FieldLift.field Q.toSmooth K b

abbrev parametrizingExtension : Spec (Q.parametrizingField K b) ⟶ Spec K :=
  FieldLift.extension Q.toSmooth K b

abbrev parametrizingPoint : Spec (Q.parametrizingField K b) ⟶ Q.cover :=
  FieldLift.lift Q.toSmooth K b

@[reassoc] theorem parametrizingPoint_base :
    Q.parametrizingPoint K b ≫ Q.toSmooth = Q.parametrizingExtension K b ≫ b :=
  FieldLift.lift_base Q.toSmooth K b

theorem parametrizingExtension_surjective : Surjective (Q.parametrizingExtension K b) :=
  FieldLift.extension_surjective Q.toSmooth K b

/-- The lifted point uses exactly the complex structure inherited from
the original field point. -/
@[reassoc] theorem parametrizingPoint_overC (sK : Spec K ⟶ ComplexBase)
    (hb : (b ≫ F.smoothOpen.ι) ≫ F.toC = sK) :
    Q.parametrizingPoint K b ≫ Q.coverToC = Q.parametrizingExtension K b ≫ sK := by
  have hc : (Q.toSmooth ≫ F.smoothOpen.ι) ≫ F.toC = Q.coverToC := Q.overC
  calc
    Q.parametrizingPoint K b ≫ Q.coverToC =
        Q.parametrizingPoint K b ≫ ((Q.toSmooth ≫ F.smoothOpen.ι) ≫ F.toC) :=
      congrArg (fun k : Q.cover ⟶ ComplexBase => Q.parametrizingPoint K b ≫ k)
        hc.symm
    _ = ((Q.parametrizingPoint K b ≫ Q.toSmooth) ≫ F.smoothOpen.ι) ≫ F.toC := by
      simp only [Category.assoc]
    _ = ((Q.parametrizingExtension K b ≫ b) ≫ F.smoothOpen.ι) ≫ F.toC :=
      congrArg
        (fun k : Spec (Q.parametrizingField K b) ⟶ F.smoothOpen.toScheme =>
          (k ≫ F.smoothOpen.ι) ≫ F.toC)
        (Q.parametrizingPoint_base K b)
    _ = Q.parametrizingExtension K b ≫ ((b ≫ F.smoothOpen.ι) ≫ F.toC) := by
      simp only [Category.assoc]
    _ = Q.parametrizingExtension K b ≫ sK :=
      congrArg (fun k : Spec K ⟶ ComplexBase => Q.parametrizingExtension K b ≫ k) hb

end LeBrunSalamon.Construction.StableMaps.FullHomComparison

end

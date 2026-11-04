import LSNormalizedSegreQuotients
import LSStandardProjectiveBaseChange

/-! The Segre coordinates of two actual projective-line maps.  The
tensor line, its generating four-tuple, and its determinant equation are
transported through the specified pullbacks. No admission is introduced. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.Skeleton LeBrunSalamon.Refinement
open LeBrunSalamon.Construction

namespace LeBrunSalamon.NormalizedSegrePairs

variable (R : Type) [CommRing R] {T : Scheme}
  (u v : T ⟶ StandardTautological.space R 1)
  (h : u ≫ StandardTautological.toSpec R 1 = v ≫ StandardTautological.toSpec R 1)

def pair : T ⟶ NormalizedSegre.Product R := pullback.lift u v h

@[reassoc] theorem pair_left : pair R u v h ≫ NormalizedSegre.left R = u :=
  pullback.lift_fst _ _ _

@[reassoc] theorem pair_right : pair R u v h ≫ NormalizedSegre.right R = v :=
  pullback.lift_snd _ _ _

def line : LineBundle T :=
  tensorLine (pullbackLine u (StandardTautological.line R 1))
    (pullbackLine v (StandardTautological.line R 1))

def coordinate (i j : Fin 2) : AlgebraicSection (line R u v).sheaf :=
  tensorSection (pullSection u (StandardTautological.coordinate R 1 i))
    (pullSection v (StandardTautological.coordinate R 1 j))

def tuple (i : Fin 4) : AlgebraicSection (line R u v).sheaf :=
  coordinate R u v (NormalizedSegre.firstIndex i) (NormalizedSegre.secondIndex i)

def lineIso : pullbackModule (pair R u v h) (NormalizedSegre.productLine R).sheaf ≅
    (line R u v).sheaf := by
  let H := (StandardTautological.line R 1).sheaf
  let g := pair R u v h
  letI := tensorPullbackComparison_isIso g
    (pullbackModule (NormalizedSegre.left R) H) (pullbackModule (NormalizedSegre.right R) H)
  exact (asIso (tensorPullbackComparison g
    (pullbackModule (NormalizedSegre.left R) H) (pullbackModule (NormalizedSegre.right R) H))).symm ≪≫
    tensorIso
      (compositionPullback g (NormalizedSegre.left R) u (pair_left R u v h) H)
      (compositionPullback g (NormalizedSegre.right R) v (pair_right R u v h) H)

theorem lineIso_coordinate (i : Fin 4) :
    pullSection (pair R u v h) (NormalizedSegre.productCoordinate R i) ≫
      (lineIso R u v h).hom = tuple R u v i := by
  let H := (StandardTautological.line R 1).sheaf
  let g := pair R u v h
  letI := tensorPullbackComparison_isIso g
    (pullbackModule (NormalizedSegre.left R) H) (pullbackModule (NormalizedSegre.right R) H)
  letI := tensorPullbackComparison_isIso g
    (pullbackLine (NormalizedSegre.left R) (StandardTautological.line R 1)).sheaf
    (pullbackLine (NormalizedSegre.right R) (StandardTautological.line R 1)).sheaf
  rw [NormalizedSegre.productCoordinate, ← tensorPullbackComparison_onSections]
  change (tensorSection _ _ ≫ tensorPullbackComparison g _ _) ≫
    ((asIso (tensorPullbackComparison g _ _)).inv ≫ tensorMap _ _) = _
  change (tensorSection _ _ ≫ (asIso (tensorPullbackComparison g _ _)).hom) ≫
    ((asIso (tensorPullbackComparison g _ _)).inv ≫ tensorMap _ _) = _
  rw [Category.assoc, Iso.hom_inv_id_assoc, tensorSection_map,
    compositionPullback_sections, compositionPullback_sections]
  rfl

def mapLine :
    pullbackModule (pair R u v h ≫ NormalizedSegre.map R)
      (StandardTautological.line R 3).sheaf ≅ (line R u v).sheaf :=
  NormalizedSegreQuotients.projectiveLine R (pair R u v h) (lineIso R u v h)

theorem mapLine_coordinate (i : Fin 4) :
    pullSection (pair R u v h ≫ NormalizedSegre.map R)
        (StandardTautological.coordinate R 3 i) ≫ (mapLine R u v h).hom = tuple R u v i :=
  NormalizedSegreQuotients.projectiveLine_coordinates R (pair R u v h)
    (tuple R u v) (lineIso R u v h) (lineIso_coordinate R u v h) i

/-- The four literal pair products generate the original tensor line. -/
theorem tuple_generates
    (h : u ≫ StandardTautological.toSpec R 1 = v ≫ StandardTautological.toSpec R 1) :
    TupleGenerates (line R u v) (tuple R u v) := by
  let f := pair R u v h ≫ NormalizedSegre.map R
  let a := fun i => pullSection f (StandardTautological.coordinate R 3 i)
  letI : Epi (Sigma.desc a) := StandardProjectiveBaseChange.pull_generates
    (StandardTautological.coordinate R 3) (StandardTautological.generates R 3) f
  have hfac : Sigma.desc a ≫ (mapLine R u v h).hom = Sigma.desc (tuple R u v) := by
    apply Sigma.hom_ext
    intro i
    simpa only [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc, a] using
      mapLine_coordinate R u v h i
  change Epi (Sigma.desc (tuple R u v))
  rw [← hfac]
  infer_instance

theorem pull_equation {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    {L : OModule Z} (a b : AlgebraicSection L)
    (hab : pullSection g a = pullSection g b) :
    pullSection (f ≫ g) a = pullSection (f ≫ g) b := by
  rw [← CanonicalPullbackSectionProof.pullSection_comp,
    ← CanonicalPullbackSectionProof.pullSection_comp, hab]

/-- The determinant vanishes as a sheaf-section equation, through the
actual defining ideal of the Segre image. -/
theorem determinant
    (h : u ≫ StandardTautological.toSpec R 1 = v ≫ StandardTautological.toSpec R 1) :
    tensorSection (tuple R u v 0) (tuple R u v 3) =
      tensorSection (tuple R u v 1) (tuple R u v 2) := by
  have heq := Construction.Smoothing.StandardSourceProof.SectionEquality.equation
    (NormalizedSegre.quadraticTotal R) (NormalizedSegre.determinantLeft R)
    (NormalizedSegre.determinantRight R)
  have hp := pull_equation (pair R u v h ≫ (NormalizedSegre.chosen R).iso.hom)
    (NormalizedSegre.inclusion R) _ _ heq
  have hp' : pullSection (pair R u v h ≫ NormalizedSegre.map R)
      (NormalizedSegre.determinantLeft R) =
    pullSection (pair R u v h ≫ NormalizedSegre.map R)
      (NormalizedSegre.determinantRight R) := by
    exact Eq.mp (congrArg
      (fun f : T ⟶ StandardTautological.space R 3 =>
        pullSection f (NormalizedSegre.determinantLeft R) =
          pullSection f (NormalizedSegre.determinantRight R))
      (Category.assoc (pair R u v h) (NormalizedSegre.chosen R).iso.hom
        (NormalizedSegre.inclusion R))) hp
  let e := NormalizedSegreQuotients.tensorComparison
    (pair R u v h ≫ NormalizedSegre.map R)
    (StandardTautological.line R 3).sheaf (mapLine R u v h)
  have hs := congrArg (fun s => s ≫ e.hom) hp'
  change pullSection _ (tensorSection _ _) ≫ e.hom =
    pullSection _ (tensorSection _ _) ≫ e.hom at hs
  simpa only [e, NormalizedSegreQuotients.tensorComparison_sections,
    mapLine_coordinate] using hs

end LeBrunSalamon.NormalizedSegrePairs
end

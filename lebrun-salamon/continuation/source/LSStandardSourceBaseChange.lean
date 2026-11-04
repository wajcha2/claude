import RecompileExtensionsPart04Geometry

/-! The original homogeneous conic presentation after an arbitrary actual
base change. All four coordinates, the O(1,1) line comparison, and the
all-test-scheme universal property retain the canonical pullback maps.
This is a transport lemma, not a classification of an arbitrary family.
No admission. -/

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
open LeBrunSalamon.Construction.Smoothing

namespace LeBrunSalamon.StandardSourceBaseChange

def line {Y : Scheme} (u v : Y ⟶ ProjectiveLine) : LineBundle Y :=
  tensorLine (pullbackLine u (projectiveCoordinates 1).hyperplane)
    (pullbackLine v (projectiveCoordinates 1).hyperplane)

def coordinate {Y : Scheme} (u v : Y ⟶ ProjectiveLine) (i j : Fin 2) :
    AlgebraicSection (line u v).sheaf :=
  tensorSection (pullSection u ((projectiveCoordinates 1).coordinate i))
    (pullSection v ((projectiveCoordinates 1).coordinate j))

/-- The selected tensor line after composing the two maps is compared with
the pullback of the original tensor line by the canonical comparisons. -/
def lineComparison {X Y : Scheme} (f : X ⟶ Y) (u v : Y ⟶ ProjectiveLine) :
    (line (f ≫ u) (f ≫ v)).sheaf ≅ pullbackModule f (line u v).sheaf := by
  letI := tensorPullbackComparison_isIso f
    (pullbackModule u (projectiveCoordinates 1).hyperplane.sheaf)
    (pullbackModule v (projectiveCoordinates 1).hyperplane.sheaf)
  exact (tensorIso
    (compositionPullback f u (f ≫ u) rfl (projectiveCoordinates 1).hyperplane.sheaf)
    (compositionPullback f v (f ≫ v) rfl (projectiveCoordinates 1).hyperplane.sheaf)).symm ≪≫
    asIso (tensorPullbackComparison f
      (pullbackModule u (projectiveCoordinates 1).hyperplane.sheaf)
      (pullbackModule v (projectiveCoordinates 1).hyperplane.sheaf))

theorem lineComparison_coordinate {X Y : Scheme}
    (f : X ⟶ Y) (u v : Y ⟶ ProjectiveLine) (i j : Fin 2) :
    coordinate (f ≫ u) (f ≫ v) i j ≫ (lineComparison f u v).hom =
      pullSection f (coordinate u v i j) := by
  let e := tensorIso
    (compositionPullback f u (f ≫ u) rfl (projectiveCoordinates 1).hyperplane.sheaf)
    (compositionPullback f v (f ≫ v) rfl (projectiveCoordinates 1).hyperplane.sheaf)
  have h : tensorSection
      (pullSection f (pullSection u ((projectiveCoordinates 1).coordinate i)))
      (pullSection f (pullSection v ((projectiveCoordinates 1).coordinate j))) ≫ e.hom =
      coordinate (f ≫ u) (f ≫ v) i j := by
    change tensorSection _ _ ≫ tensorMap _ _ = _
    rw [tensorSection_map, compositionPullback_sections, compositionPullback_sections]
    rfl
  rw [← h]
  change (_ ≫ e.hom) ≫ (e.inv ≫ tensorPullbackComparison f _ _) = _
  rw [Category.assoc, Iso.hom_inv_id_assoc]
  exact tensorPullbackComparison_onSections f _ _

/-- The same line-valued homogeneous equation holds after every base change,
including base changes from nonreduced test schemes. -/
theorem equation_pullback {X Y : Scheme} (f : X ⟶ Y)
    (t : Y ⟶ AffineLine) (u v : Y ⟶ ProjectiveLine)
    (h : ConicEquation t u v) : ConicEquation (f ≫ t) (f ≫ u) (f ≫ v) := by
  change coordinate (f ≫ u) (f ≫ v) 1 1 =
    sectionFromValue ((f ≫ t).appTop parameterFunction •
      sectionValue (coordinate (f ≫ u) (f ≫ v) 0 0))
  apply (cancel_mono (lineComparison f u v).hom).mp
  rw [lineComparison_coordinate, StandardSourceProof.scalarSection_comp,
    lineComparison_coordinate]
  have hh := congrArg (fun s : AlgebraicSection (line u v).sheaf => pullSection f s) h
  rw [StandardSourceProof.pullSection_scalar] at hh
  simpa only [coordinate, Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using hh

/-- Literal base change of the original representing scheme. No isomorphism
class of abstract genus-zero curves is substituted for this universal property. -/
theorem universal (F : StandardSource) {S : Scheme} (t : S ⟶ AffineLine)
    (T : Scheme) (s : T ⟶ S) (u v : T ⟶ ProjectiveLine)
    (hu : u ≫ Lines.P.structureMap = (s ≫ t) ≫ affineLineToC)
    (hv : v ≫ Lines.P.structureMap = (s ≫ t) ≫ affineLineToC)
    (heq : ConicEquation (s ≫ t) u v) :
    ∃! h : T ⟶ SourceOver F t,
      h ≫ pullback.snd F.parameter t = s ∧
      (h ≫ pullback.fst F.parameter t) ≫ F.left = u ∧
      (h ≫ pullback.fst F.parameter t) ≫ F.right = v := by
  obtain ⟨g, hg, unique⟩ := F.universal T ((s ≫ t) ≫ affineLineToC)
    ⟨s ≫ t, rfl⟩ ⟨u, hu⟩ ⟨v, hv⟩ heq
  let h : T ⟶ SourceOver F t := pullback.lift g s hg.1
  refine ⟨h, ?_, ?_⟩
  · exact ⟨pullback.lift_snd _ _ _, by simpa [h] using hg.2.1,
      by simpa [h] using hg.2.2⟩
  · intro h' hh'
    apply pullback.hom_ext
    · rw [show h ≫ pullback.fst F.parameter t = g from pullback.lift_fst _ _ _]
      apply unique
      refine ⟨?_, hh'.2.1, hh'.2.2⟩
      rw [Category.assoc, pullback.condition, ← Category.assoc, hh'.1]
    · exact hh'.1.trans (pullback.lift_snd g s hg.1).symm

/-- The original parameter and the two original projective maps detect
equality of actual maps to the standard source. -/
theorem source_hom_ext (F : StandardSource) {T : Scheme} {f g : T ⟶ F.source}
    (ht : f ≫ F.parameter = g ≫ F.parameter)
    (hu : f ≫ F.left = g ≫ F.left) (hv : f ≫ F.right = g ≫ F.right) : f = g := by
  obtain ⟨a, ha, huniq⟩ := F.universal T ((f ≫ F.parameter) ≫ affineLineToC)
    ⟨f ≫ F.parameter, rfl⟩
    ⟨f ≫ F.left, by rw [Category.assoc, F.left_over, Category.assoc]⟩
    ⟨f ≫ F.right, by rw [Category.assoc, F.right_over, Category.assoc]⟩
    (equation_pullback f F.parameter F.left F.right F.equation)
  exact (huniq f ⟨rfl, rfl, rfl⟩).trans (huniq g ⟨ht.symm, hu.symm, hv.symm⟩).symm

/-- Equality in the actual base-changed source retains the base map as
well as both projective factors. -/
theorem hom_ext (F : StandardSource) {S T : Scheme} (t : S ⟶ AffineLine)
    {f g : T ⟶ SourceOver F t}
    (hs : f ≫ pullback.snd F.parameter t = g ≫ pullback.snd F.parameter t)
    (hu : (f ≫ pullback.fst F.parameter t) ≫ F.left =
      (g ≫ pullback.fst F.parameter t) ≫ F.left)
    (hv : (f ≫ pullback.fst F.parameter t) ≫ F.right =
      (g ≫ pullback.fst F.parameter t) ≫ F.right) : f = g := by
  apply pullback.hom_ext
  · apply source_hom_ext F
    · rw [Category.assoc, pullback.condition, ← Category.assoc, hs,
        Category.assoc, ← pullback.condition, ← Category.assoc]
    · exact hu
    · exact hv
  · exact hs

end LeBrunSalamon.StandardSourceBaseChange
end

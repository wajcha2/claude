import LSPlaneQuadratic
import LSStandardProjectiveBaseChange

/-! The normalized quadratic section commutes with the actual projective
base-change map and the actual tensor-square comparison.  This is proved
term by term from the coefficient map and the tautological coordinates;
no cohomological or geometric base-change input is added. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.Skeleton LeBrunSalamon.Refinement

namespace LeBrunSalamon.PlaneQuadraticBaseChange

def squarePullbackIso {T Y : Scheme} (f : T ⟶ Y) (E : OModule Y)
    {G : OModule T} (e : pullbackModule f E ≅ G) :
    pullbackModule f (tensorSheaf E E) ≅ tensorSheaf G G := by
  letI := tensorPullbackComparison_isIso f E E
  exact (asIso (tensorPullbackComparison f E E)).symm ≪≫ tensorIso e e

theorem squarePullbackIso_sections {T Y : Scheme} (f : T ⟶ Y) (E : OModule Y)
    {G : OModule T} (e : pullbackModule f E ≅ G)
    (a b : AlgebraicSection E) :
    pullSection f (tensorSection a b) ≫ (squarePullbackIso f E e).hom =
      tensorSection (pullSection f a ≫ e.hom) (pullSection f b ≫ e.hom) := by
  letI := tensorPullbackComparison_isIso f E E
  rw [← tensorPullbackComparison_onSections]
  change (tensorSection _ _ ≫ tensorPullbackComparison f E E) ≫
    ((asIso (tensorPullbackComparison f E E)).inv ≫ tensorMap e.hom e.hom) = _
  change (tensorSection _ _ ≫ (asIso (tensorPullbackComparison f E E)).hom) ≫
    ((asIso (tensorPullbackComparison f E E)).inv ≫ tensorMap e.hom e.hom) = _
  rw [Category.assoc, Iso.hom_inv_id_assoc, tensorSection_map]

variable {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)

/-- The comparison is the canonical tensor pullback comparison followed
by the two actual normalized tautological-line comparisons. -/
def squareLineIso (N : ℕ) :
    pullbackModule (StandardProjectiveBaseChange.map φ N)
      (tensorLine (StandardTautological.line R N) (StandardTautological.line R N)).sheaf ≅
    (tensorLine (StandardTautological.line S N) (StandardTautological.line S N)).sheaf :=
  squarePullbackIso (StandardProjectiveBaseChange.map φ N)
    (StandardTautological.line R N).sheaf (StandardProjectiveBaseChange.lineIso φ N)

theorem coefficient (a : R) :
    (StandardProjectiveBaseChange.map φ 2).appTop (PlaneQuadratic.coefficient R a) =
      PlaneQuadratic.coefficient S (φ a) := by
  change ((StandardTautological.toSpec R 2).appTop ≫
      (StandardProjectiveBaseChange.map φ 2).appTop)
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a) = _
  rw [← Scheme.Hom.comp_appTop, (StandardProjectiveBaseChange.mapPoint φ 2).property,
    Scheme.Hom.comp_appTop]
  change (StandardTautological.toSpec S 2).appTop
    ((Spec.map (CommRingCat.ofHom φ)).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a)) = _
  have h := congrArg
    (fun k : CommRingCat.of R ⟶ Γ(Spec (CommRingCat.of S), ⊤) => k a)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  exact congrArg (fun b => (StandardTautological.toSpec S 2).appTop b) h.symm

theorem monomial (i : Fin 6) :
    pullSection (StandardProjectiveBaseChange.map φ 2) (PlaneQuadratic.monomial R i) ≫
      (squareLineIso φ 2).hom = PlaneQuadratic.monomial S i := by
  change pullSection _ (tensorSection _ _) ≫ (squarePullbackIso _ _ _).hom = _
  rw [squarePullbackIso_sections, StandardProjectiveBaseChange.coordinate,
    StandardProjectiveBaseChange.coordinate]
  rfl

/-- Exact coefficientwise reduction (or extension) of the six quadratic
coefficients.  The comparison retains the prescribed O(1)-tensor-O(1)
normalization, rather than identifying the two lines by an arbitrary unit. -/
theorem sectionOf (q : PlaneQuadratic.Coefficients R) :
    pullSection (StandardProjectiveBaseChange.map φ 2) (PlaneQuadratic.sectionOf R q) ≫
      (squareLineIso φ 2).hom =
        PlaneQuadratic.sectionOf S (fun i => φ (q i)) := by
  simp only [PlaneQuadratic.sectionOf, pullSection, restrictSection,
    Functor.map_sum, Preadditive.comp_sum, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro i hi
  change pullSection (StandardProjectiveBaseChange.map φ 2)
      (sectionFromValue (PlaneQuadratic.coefficient R (q i) •
        sectionValue (PlaneQuadratic.monomial R i))) ≫ (squareLineIso φ 2).hom = _
  rw [LeBrunSalamon.Construction.Smoothing.StandardSourceProof.pullSection_scalar,
    LeBrunSalamon.Construction.Smoothing.StandardSourceProof.scalarSection_comp,
    coefficient, monomial]

end LeBrunSalamon.PlaneQuadraticBaseChange
end

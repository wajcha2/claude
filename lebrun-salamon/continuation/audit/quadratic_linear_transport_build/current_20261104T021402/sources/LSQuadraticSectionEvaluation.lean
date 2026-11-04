import LSProjectiveLinearAction
import LSPlaneQuadraticBaseChange
import LSAffineFrame
import LSStandardProjectiveSmooth

/-!
Polynomial coordinate changes act on the actual quadratic section.  The
translation is proved in genuine rank-one sheaf frames and then glued.
All polynomial and sheaf maps are explicit; there is no new input.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.Refinement

namespace LeBrunSalamon.QuadraticSectionEvaluation

open ProjectiveLinearAction ConicTupleChange
open Construction.Smoothing.CoordinateCharts

theorem section_app_one {Y : Scheme} {E : OModule Y}
    (a : AlgebraicSection E) (U : Y.Opens) :
    Scheme.Modules.Hom.app a U (1 : RingSections Y U) =
      E.presheaf.map (homOfLE le_top).op (sectionValue a) := by
  have h := sheafHom_naturality a (homOfLE (show U ≤ ⊤ from le_top))
    (1 : RingSections Y ⊤)
  change E.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (sectionValue a) =
    Scheme.Modules.Hom.app a U
      (Y.presheaf.map (homOfLE le_top).op (1 : RingSections Y ⊤)) at h
  simpa only [map_one] using h.symm

def frameCoefficient {Y : Scheme} {E : OModule Y} {U : Y.Opens}
    (e : LocalFrames.OverFrame E U) : AlgebraicSection E →+ RingSections Y U where
  toFun a := LocalFrames.coordinates e (Scheme.Modules.Hom.app a U (1 : RingSections Y U))
  map_zero' := (LocalFrames.coordinates e).map_zero
  map_add' a b := (LocalFrames.coordinates e).map_add _ _

theorem frameCoefficient_smul {Y : Scheme} {E : OModule Y} {U : Y.Opens}
    (e : LocalFrames.OverFrame E U) (r : RingSections Y ⊤) (a : AlgebraicSection E) :
    frameCoefficient e (sectionFromValue (r • sectionValue a)) =
      Y.presheaf.map (homOfLE le_top).op r * frameCoefficient e a := by
  change LocalFrames.coordinates e
    (Scheme.Modules.Hom.app (sectionFromValue (E := E) (r • sectionValue a)) U
      (1 : RingSections Y U)) = _
  rw [section_app_one, sectionFromValue_spec]
  change LocalFrames.coordinates e
    (E.val.map (homOfLE (show U ≤ ⊤ from le_top)).op (r • sectionValue a)) = _
  rw [E.val.map_smul, (LocalFrames.coordinates e).map_smul]
  change Y.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op r *
    LocalFrames.coordinates e
      (E.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (sectionValue a)) =
    Y.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op r * frameCoefficient e a
  rw [← section_app_one]
  all_goals rfl

theorem frameCoefficient_tensor {Y : Scheme} {E F : OModule Y} {U : Y.Opens}
    (e : LocalFrames.OverFrame E U) (f : LocalFrames.OverFrame F U)
    (a : AlgebraicSection E) (b : AlgebraicSection F) :
    frameCoefficient (LocalFrames.tensorFrame e f) (tensorSection a b) =
      frameCoefficient e a * frameCoefficient f b := by
  change LocalFrames.coordinates (LocalFrames.tensorFrame e f)
    (Scheme.Modules.Hom.app (tensorSection a b) U (1 : RingSections Y U)) = _
  rw [section_app_one, sectionValue_tensorSection,
    (tensorPresentation E F).pair.naturality,
    ← section_app_one, ← section_app_one]
  exact AffineFrameProof.tensorFrame_coordinates_pair e f _ _

/-- Coefficients in actual frames on a cover detect equality of global sections. -/
theorem section_ext {Y : Scheme} {E : OModule Y} {ι : Type}
    (U : ι → Y.Opens) (hU : iSup U = ⊤)
    (e : ∀ i, LocalFrames.OverFrame E (U i))
    (a b : AlgebraicSection E)
    (h : ∀ i, frameCoefficient (e i) a = frameCoefficient (e i) b) : a = b := by
  apply (sectionValue_bijective E).injective
  let S : TopCat.Sheaf AddCommGrpCat Y :=
    (SheafOfModules.toSheaf Y.ringCatSheaf).obj E
  apply TopCat.Sheaf.eq_of_locally_eq' S U ⊤ (fun i => (U i).leTop) (by rw [hU])
  intro i
  change E.presheaf.map (homOfLE le_top).op (sectionValue a) =
    E.presheaf.map (homOfLE le_top).op (sectionValue b)
  rw [← section_app_one, ← section_app_one]
  exact (LocalFrames.coordinates (e i)).injective (h i)

variable {R : Type} [CommRing R]

def localCoefficientHom {Y : Scheme} (p : Y ⟶ Spec (CommRingCat.of R)) (U : Y.Opens) :
    R →+* RingSections Y U :=
  (Y.presheaf.map (homOfLE le_top).op).hom.comp (coefficientHom p)

def quadratic {Y : Scheme} (p : Y ⟶ Spec (CommRingCat.of R)) {E : OModule Y}
    (q : PlaneQuadratic.Coefficients R) (a : Fin 3 → AlgebraicSection E) :
    AlgebraicSection (tensorSheaf E E) :=
  ∑ i : Fin 6, scalarSection (coefficientHom p (q i)) ≫
    tensorSection (a (PlaneQuadratic.firstIndex i)) (a (PlaneQuadratic.secondIndex i))

theorem eval_polynomial {S : Type} [CommRing S] (r : R →+* S) (v : Fin 3 → S)
    (q : PlaneQuadratic.Coefficients R) :
    MvPolynomial.eval₂Hom r v (PlaneQuadratic.polynomial R q) =
      ∑ i : Fin 6, r (q i) * (v (PlaneQuadratic.firstIndex i) *
        v (PlaneQuadratic.secondIndex i)) := by
  simp [PlaneQuadratic.polynomial, PlaneQuadratic.firstIndex,
    PlaneQuadratic.secondIndex, Fin.sum_univ_succ, pow_two, mul_assoc, add_assoc]

theorem frameCoefficient_quadratic {Y : Scheme} (p : Y ⟶ Spec (CommRingCat.of R))
    {E : OModule Y} {U : Y.Opens} (e : LocalFrames.OverFrame E U)
    (q : PlaneQuadratic.Coefficients R) (a : Fin 3 → AlgebraicSection E) :
    frameCoefficient (LocalFrames.tensorFrame e e) (quadratic p q a) =
      MvPolynomial.eval₂Hom (localCoefficientHom p U) (fun i => frameCoefficient e (a i))
        (PlaneQuadratic.polynomial R q) := by
  rw [eval_polynomial]
  simp only [quadratic, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [scalar_comp, frameCoefficient_smul, frameCoefficient_tensor]
  all_goals rfl

theorem frameCoefficient_combine {Y : Scheme} (p : Y ⟶ Spec (CommRingCat.of R))
    {E : OModule Y} {U : Y.Opens} (e : LocalFrames.OverFrame E U)
    {m n : ℕ} (M : Matrix (Fin m) (Fin n) R) (a : Fin n → AlgebraicSection E) (i : Fin m) :
    frameCoefficient e (combine (coefficientMatrix p M) a i) =
      ∑ j, localCoefficientHom p U (M i j) * frameCoefficient e (a j) := by
  simp only [combine, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [scalar_comp, frameCoefficient_smul]
  all_goals rfl

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
theorem eval_matrixRow {S : Type} [CommRing S] {m n : ℕ}
    (r : R →+* S) (v : Fin n → S) (M : Matrix (Fin m) (Fin n) R) (i : Fin m) :
    MvPolynomial.eval₂Hom r v
      (∑ j : Fin n, MvPolynomial.C (M i j) * MvPolynomial.X j) =
        ∑ j, r (M i j) * v j := by
  trans ∑ j : Fin n, MvPolynomial.eval₂Hom r v
    (MvPolynomial.C (M i j) * MvPolynomial.X j)
  · exact map_sum (MvPolynomial.eval₂Hom r v)
      (fun j : Fin n => MvPolynomial.C (M i j) * MvPolynomial.X j) Finset.univ
  apply Finset.sum_congr rfl
  intro j hj
  calc
    _ = MvPolynomial.eval₂Hom r v (MvPolynomial.C (M i j)) *
        MvPolynomial.eval₂Hom r v (MvPolynomial.X j) :=
      map_mul (MvPolynomial.eval₂Hom r v) _ _
    _ = _ := by rw [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X']

theorem eval_linearCoordinate {S : Type} [CommRing S] (r : R →+* S) (v : Fin 3 → S)
    (M : (Matrix (Fin 3) (Fin 3) R)ˣ) (i : Fin 3) :
    MvPolynomial.eval₂Hom r v (PlaneQuadratic.linearCoordinate R M i) =
      ∑ j, r (M.val i j) * v j :=
  eval_matrixRow r v M.val i

/-- The literal polynomial substitution identity implies equality of the actual
quadratic sections for arbitrary rank-one frame covers. -/
theorem quadratic_transformed {Y : Scheme} (p : Y ⟶ Spec (CommRingCat.of R))
    {E : OModule Y} {ι : Type} (U : ι → Y.Opens) (hU : iSup U = ⊤)
    (e : ∀ i, LocalFrames.OverFrame E (U i))
    (q q' : PlaneQuadratic.Coefficients R) (M : (Matrix (Fin 3) (Fin 3) R)ˣ)
    (hq : PlaneQuadratic.transformed R q M = PlaneQuadratic.polynomial R q')
    (a : Fin 3 → AlgebraicSection E) :
    quadratic p q (combine (coefficientMatrix p M.val) a) = quadratic p q' a := by
  apply section_ext U hU (fun i => LocalFrames.tensorFrame (e i) (e i))
  intro i
  rw [frameCoefficient_quadratic, frameCoefficient_quadratic]
  have h := congrArg
    (MvPolynomial.eval₂Hom (localCoefficientHom p (U i))
      (fun j => frameCoefficient (e i) (a j))) hq
  rw [PlaneQuadratic.transformed, MvPolynomial.eval₂Hom_bind₁] at h
  simpa only [frameCoefficient_combine, eval_linearCoordinate] using h

theorem sectionOf_eq_quadratic (q : PlaneQuadratic.Coefficients R) :
    PlaneQuadratic.sectionOf R q =
      quadratic (StandardTautological.toSpec R 2) q (StandardTautological.coordinate R 2) := by
  unfold PlaneQuadratic.sectionOf quadratic
  apply Finset.sum_congr rfl
  intro i hi
  exact (scalar_comp (coefficientHom (StandardTautological.toSpec R 2) (q i))
    (PlaneQuadratic.monomial R i)).symm

/-- The quadratic expression commutes with the actual pullback and tensor
comparison on arbitrary schemes, before specializing to projective space. -/
theorem pull_quadratic_generic {X Y : Scheme}
    (p : Y ⟶ Spec (CommRingCat.of R)) (s : X ⟶ Spec (CommRingCat.of R))
    (f : X ⟶ Y) (hf : f ≫ p = s) {E : OModule Y} {G : OModule X}
    (e : pullbackModule f E ≅ G) (q : PlaneQuadratic.Coefficients R)
    (a : Fin 3 → AlgebraicSection E) :
    pullSection f (quadratic p q a) ≫
      (PlaneQuadraticBaseChange.squarePullbackIso f E e).hom =
    quadratic s q (fun i => pullSection f (a i) ≫ e.hom) := by
  simp only [quadratic, pullSection, restrictSection,
    Functor.map_sum, Preadditive.comp_sum, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro i hi
  change pullSection f (scalarSection (coefficientHom p (q i)) ≫
      tensorSection (a (PlaneQuadratic.firstIndex i)) (a (PlaneQuadratic.secondIndex i))) ≫
      (PlaneQuadraticBaseChange.squarePullbackIso f E e).hom =
    scalarSection (coefficientHom s (q i)) ≫
      tensorSection (pullSection f (a (PlaneQuadratic.firstIndex i)) ≫ e.hom)
        (pullSection f (a (PlaneQuadratic.secondIndex i)) ≫ e.hom)
  rw [scalar_comp, scalar_comp,
    Construction.Smoothing.StandardSourceProof.pullSection_scalar,
    Construction.Smoothing.StandardSourceProof.scalarSection_comp,
    coefficient_pull p s f hf, PlaneQuadraticBaseChange.squarePullbackIso_sections]

def actionSquareIso (M : (Matrix (Fin 3) (Fin 3) R)ˣ) :
    pullbackModule (ProjectiveLinearAction.map R 2 M) (PlaneQuadratic.quadraticLine R).sheaf ≅
      (PlaneQuadratic.quadraticLine R).sheaf :=
  PlaneQuadraticBaseChange.squarePullbackIso (ProjectiveLinearAction.map R 2 M)
    (StandardTautological.line R 2).sheaf (ProjectiveLinearAction.lineIso R 2 M)

theorem pull_quadratic (M : (Matrix (Fin 3) (Fin 3) R)ˣ)
    (q : PlaneQuadratic.Coefficients R) :
    pullSection (ProjectiveLinearAction.map R 2 M) (PlaneQuadratic.sectionOf R q) ≫
      (actionSquareIso M).hom =
        quadratic (StandardTautological.toSpec R 2) q (ProjectiveLinearAction.tuple R 2 M) := by
  rw [sectionOf_eq_quadratic]
  have h := pull_quadratic_generic (StandardTautological.toSpec R 2)
    (StandardTautological.toSpec R 2) (ProjectiveLinearAction.map R 2 M)
    (ProjectiveLinearAction.mapPoint R 2 M).property
    (ProjectiveLinearAction.lineIso R 2 M) q (StandardTautological.coordinate R 2)
  simpa only [ProjectiveLinearAction.coordinate, actionSquareIso] using h

/-- The normalized section comparison attached to an invertible coordinate
change. It is equality of sheaf maps, so it retains nonreduced test schemes. -/
theorem section_transformed (q q' : PlaneQuadratic.Coefficients R)
    (M : (Matrix (Fin 3) (Fin 3) R)ˣ)
    (hq : PlaneQuadratic.transformed R q M = PlaneQuadratic.polynomial R q') :
    pullSection (ProjectiveLinearAction.map R 2 M) (PlaneQuadratic.sectionOf R q) ≫
      (actionSquareIso M).hom = PlaneQuadratic.sectionOf R q' := by
  rw [pull_quadratic, sectionOf_eq_quadratic]
  exact quadratic_transformed (StandardTautological.toSpec R 2)
    (StandardTautological.chart R 2)
    (PublishedInputs.ProjectiveSpace.standardAffineCharts R 2).1
    (StandardTautological.chosen R 2).frame q q' M hq
    (StandardTautological.coordinate R 2)

end LeBrunSalamon.QuadraticSectionEvaluation
end

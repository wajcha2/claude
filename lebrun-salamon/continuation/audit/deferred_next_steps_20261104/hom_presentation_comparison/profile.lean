import RecompileExtensionsPart01
import Lean

/-! Canonical comparison of supplied all-test Hom presentations.
The construction uses their actual universal evaluations on parameter schemes.
It makes no representability existence or finite-presentation assumption. -/

noncomputable section

set_option autoImplicit false
set_option stderrAsMessages false
set_option profiler true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.Skeleton

namespace LeBrunSalamon.HomPresentationComparison

#eval (do let err ← IO.getStderr; err.putStrLn "HOM_PRESENTATION_STAGE ENTER_01"; err.flush : IO Unit)

/-! ## Maps of test schemes -/

def identityPoint (T : Scheme) (sT : T ⟶ ComplexBase) :
    PointsOver T sT T sT :=
  ⟨𝟙 T, Category.id_comp sT⟩

def composePoint {T U V : Scheme} {sT : T ⟶ ComplexBase}
    {sU : U ⟶ ComplexBase} {sV : V ⟶ ComplexBase}
    (a : PointsOver T sT U sU) (b : PointsOver U sU V sV) :
    PointsOver T sT V sV :=
  ⟨a.val ≫ b.val, by rw [Category.assoc, b.property, a.property]⟩

@[simp]
theorem sourceMap_identity (P : ProjectiveLineOverC)
    (T : Scheme) (sT : T ⟶ ComplexBase) :
    rationalSourceMap P (identityPoint T sT) = 𝟙 (RationalSourceOver P T sT) := by
  apply pullback.hom_ext <;> simp [rationalSourceMap, identityPoint]

theorem sourceMap_comp (P : ProjectiveLineOverC)
    {T U V : Scheme} {sT : T ⟶ ComplexBase}
    {sU : U ⟶ ComplexBase} {sV : V ⟶ ComplexBase}
    (a : PointsOver T sT U sU) (b : PointsOver U sU V sV) :
    rationalSourceMap P (composePoint a b) =
      rationalSourceMap P a ≫ rationalSourceMap P b := by
  apply pullback.hom_ext <;> simp [rationalSourceMap, composePoint, Category.assoc]

#eval (do let err ← IO.getStderr; err.putStrLn "HOM_PRESENTATION_STAGE ENTER_02"; err.flush : IO Unit)

/-! ## The evaluation-preserving comparison -/

def comparison (P : ProjectiveLineOverC) {d : ℕ}
    {X : SmoothProperComplexVariety d} (H K : HomSpacePresentation P X) :
    PointsOver H.parameter H.toC K.parameter K.toC :=
  Classical.choose ((K.universal H.parameter H.toC).surjective
    ⟨H.evaluation, H.overC⟩)

@[reassoc]
theorem comparison_toC (P : ProjectiveLineOverC) {d : ℕ}
    {X : SmoothProperComplexVariety d} (H K : HomSpacePresentation P X) :
    (comparison P H K).val ≫ K.toC = H.toC :=
  (comparison P H K).property

theorem comparison_evaluation (P : ProjectiveLineOverC) {d : ℕ}
    {X : SmoothProperComplexVariety d} (H K : HomSpacePresentation P X) :
    rationalSourceMap P (comparison P H K) ≫ K.evaluation = H.evaluation := by
  exact congrArg Subtype.val (Classical.choose_spec
    ((K.universal H.parameter H.toC).surjective ⟨H.evaluation, H.overC⟩))

theorem comparison_unique (P : ProjectiveLineOverC) {d : ℕ}
    {X : SmoothProperComplexVariety d} (H K : HomSpacePresentation P X)
    (a : PointsOver H.parameter H.toC K.parameter K.toC)
    (ha : rationalSourceMap P a ≫ K.evaluation = H.evaluation) :
    a = comparison P H K := by
  apply (K.universal H.parameter H.toC).injective
  apply Subtype.ext
  exact ha.trans (comparison_evaluation P H K).symm

#eval (do let err ← IO.getStderr; err.putStrLn "HOM_PRESENTATION_STAGE ENTER_03"; err.flush : IO Unit)

/-! ## Identity and composition from the full universal property -/

@[simp]
theorem comparison_self (P : ProjectiveLineOverC) {d : ℕ}
    {X : SmoothProperComplexVariety d} (H : HomSpacePresentation P X) :
    comparison P H H = identityPoint H.parameter H.toC := by
  symm
  apply comparison_unique
  rw [sourceMap_identity, Category.id_comp]

theorem comparison_comp (P : ProjectiveLineOverC) {d : ℕ}
    {X : SmoothProperComplexVariety d} (H K L : HomSpacePresentation P X) :
    composePoint (comparison P H K) (comparison P K L) = comparison P H L := by
  apply comparison_unique
  rw [sourceMap_comp, Category.assoc, comparison_evaluation, comparison_evaluation]

#eval (do let err ← IO.getStderr; err.putStrLn "HOM_PRESENTATION_STAGE ENTER_04"; err.flush : IO Unit)

/-! ## The actual scheme isomorphism -/

def canonicalIso (P : ProjectiveLineOverC) {d : ℕ}
    {X : SmoothProperComplexVariety d} (H K : HomSpacePresentation P X) :
    H.parameter ≅ K.parameter where
  hom := (comparison P H K).val
  inv := (comparison P K H).val
  hom_inv_id := congrArg Subtype.val
    ((comparison_comp P H K H).trans (comparison_self P H))
  inv_hom_id := congrArg Subtype.val
    ((comparison_comp P K H K).trans (comparison_self P K))

@[reassoc]
theorem canonicalIso_toC (P : ProjectiveLineOverC) {d : ℕ}
    {X : SmoothProperComplexVariety d} (H K : HomSpacePresentation P X) :
    (canonicalIso P H K).hom ≫ K.toC = H.toC :=
  comparison_toC P H K

@[reassoc]
theorem canonicalIso_inv_toC (P : ProjectiveLineOverC) {d : ℕ}
    {X : SmoothProperComplexVariety d} (H K : HomSpacePresentation P X) :
    (canonicalIso P H K).inv ≫ H.toC = K.toC :=
  comparison_toC P K H

theorem canonicalIso_evaluation (P : ProjectiveLineOverC) {d : ℕ}
    {X : SmoothProperComplexVariety d} (H K : HomSpacePresentation P X) :
    rationalSourceMap P
      ⟨(canonicalIso P H K).hom, canonicalIso_toC P H K⟩ ≫ K.evaluation =
      H.evaluation :=
  comparison_evaluation P H K

theorem canonicalIso_inv_evaluation (P : ProjectiveLineOverC) {d : ℕ}
    {X : SmoothProperComplexVariety d} (H K : HomSpacePresentation P X) :
    rationalSourceMap P
      ⟨(canonicalIso P H K).inv, canonicalIso_inv_toC P H K⟩ ≫ H.evaluation =
      K.evaluation :=
  comparison_evaluation P K H

theorem canonicalIso_unique (P : ProjectiveLineOverC) {d : ℕ}
    {X : SmoothProperComplexVariety d} (H K : HomSpacePresentation P X)
    (e : H.parameter ≅ K.parameter) (he : e.hom ≫ K.toC = H.toC)
    (hev : rationalSourceMap P ⟨e.hom, he⟩ ≫ K.evaluation = H.evaluation) :
    e = canonicalIso P H K := by
  apply Iso.ext
  exact congrArg Subtype.val (comparison_unique P H K ⟨e.hom, he⟩ hev)

#eval (do let err ← IO.getStderr; err.putStrLn "HOM_PRESENTATION_STAGE ENTER_05"; err.flush : IO Unit)

/-! ## Evaluation on every test scheme and on actual curve points -/

theorem comparison_family (P : ProjectiveLineOverC) {d : ℕ}
    {X : SmoothProperComplexVariety d} (H K : HomSpacePresentation P X)
    {T : Scheme} {sT : T ⟶ ComplexBase}
    (t : PointsOver T sT H.parameter H.toC) :
    rationalSourceMap P (composePoint t (comparison P H K)) ≫ K.evaluation =
      rationalSourceMap P t ≫ H.evaluation := by
  rw [sourceMap_comp, Category.assoc, comparison_evaluation]

theorem comparison_mapAt (P : ProjectiveLineOverC) {d : ℕ}
    {X : SmoothProperComplexVariety d} (H K : HomSpacePresentation P X)
    (t : PointsOver ComplexBase (𝟙 ComplexBase) H.parameter H.toC) :
    K.mapAt P (composePoint t (comparison P H K)) = H.mapAt P t := by
  unfold HomSpacePresentation.mapAt
  rw [← comparison_evaluation P H K, ← Category.assoc]
  congr 1
  apply pullback.hom_ext <;> simp [rationalSourceMap, composePoint, Category.assoc]

theorem canonicalIso_mapAt (P : ProjectiveLineOverC) {d : ℕ}
    {X : SmoothProperComplexVariety d} (H K : HomSpacePresentation P X)
    (t : PointsOver ComplexBase (𝟙 ComplexBase) H.parameter H.toC) :
    K.mapAt P ⟨t.val ≫ (canonicalIso P H K).hom, by
      rw [Category.assoc, canonicalIso_toC, t.property]⟩ = H.mapAt P t :=
  comparison_mapAt P H K t

#print axioms canonicalIso
#print axioms canonicalIso_evaluation
#print axioms canonicalIso_mapAt
#eval (do let err ← IO.getStderr; err.putStrLn "HOM_PRESENTATION_COMPLETE"; err.flush : IO Unit)

end LeBrunSalamon.HomPresentationComparison

end

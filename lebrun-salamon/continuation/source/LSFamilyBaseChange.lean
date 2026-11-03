import LSFamilyBivectorDescent

/-!
# Arbitrary base change of parametrized-family derivatives

The parameter scheme is arbitrary.  In particular, the statements apply
to a fraction-field point without using complex-point detection there.
Every comparison is the fixed composition isomorphism of actual sheaf
pullbacks, and every differential is induced by the universal derivation.
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
open LeBrunSalamon.Skeleton.ContactDerivativeIsoProof

namespace LeBrunSalamon.Construction.FamilyBivectors

namespace BaseChange

/-- Dual base change with a separately named composite morphism. -/
theorem dual_composition {T Y Z : Scheme}
    (k : T ⟶ Y) (p : Y ⟶ Z) (q : T ⟶ Z) (h : k ≫ p = q)
    (E : OModule Z) :
    (compositionPullback k p q h (dualSheaf E)).hom ≫ dualBaseChange q E =
      (Scheme.Modules.pullback k).map (dualBaseChange p E) ≫
        dualBaseChange k (pullbackModule p E) ≫
          dualMap (compositionPullback k p q h E).inv := by
  subst q
  simpa only [compositionPullback, Iso.trans_hom, Iso.trans_inv, Iso.app_hom,
    Iso.app_inv, eqToIso_refl, Iso.refl_hom, Iso.refl_inv,
    Category.comp_id, Category.id_comp] using dualBaseChange_comp k p E

theorem dual_composition_normalized {T Y Z : Scheme}
    (k : T ⟶ Y) (p : Y ⟶ Z) (q : T ⟶ Z) (h : k ≫ p = q)
    (E : OModule Z) :
    (Scheme.Modules.pullback k).map (dualBaseChange p E) ≫
        dualBaseChange k (pullbackModule p E) =
      (compositionPullback k p q h (dualSheaf E)).hom ≫ dualBaseChange q E ≫
        dualMap (compositionPullback k p q h E).hom := by
  rw [← Category.assoc, dual_composition]
  simp only [Category.assoc, ← dualMap_comp, Iso.hom_inv_id,
    dualMap_id, Category.comp_id]

end BaseChange

namespace RelativeSquare

/-- The actual map of complete relative source squares. -/
def map {C A D B : Scheme} (piA : C ⟶ A) (piB : D ⟶ B)
    (k : C ⟶ D) (b : A ⟶ B) (hk : k ≫ piB = piA ≫ b) :
    Space piA ⟶ Space piB :=
  pullback.lift (left piA ≫ k) (right piA ≫ k) (by
    simp only [Category.assoc, hk]
    simpa only [Category.assoc] using congrArg (fun f => f ≫ b)
      (pullback.condition (f := piA) (g := piA)))

@[reassoc] theorem map_left {C A D B : Scheme} (piA : C ⟶ A) (piB : D ⟶ B)
    (k : C ⟶ D) (b : A ⟶ B) (hk : k ≫ piB = piA ≫ b) :
    map piA piB k b hk ≫ left piB = left piA ≫ k := pullback.lift_fst _ _ _

@[reassoc] theorem map_right {C A D B : Scheme} (piA : C ⟶ A) (piB : D ⟶ B)
    (k : C ⟶ D) (b : A ⟶ B) (hk : k ≫ piB = piA ≫ b) :
    map piA piB k b hk ≫ right piB = right piA ≫ k := pullback.lift_snd _ _ _

@[reassoc] theorem map_evaluation {C A D B X : Scheme}
    (piA : C ⟶ A) (piB : D ⟶ B)
    (k : C ⟶ D) (b : A ⟶ B) (hk : k ≫ piB = piA ≫ b)
    (sX : X ⟶ ComplexBase) (sA : A ⟶ ComplexBase) (sB : B ⟶ ComplexBase)
    (eA : C ⟶ X) (eB : D ⟶ X)
    (heA : eA ≫ sX = piA ≫ sA) (heB : eB ≫ sX = piB ≫ sB)
    (he : k ≫ eB = eA) :
    map piA piB k b hk ≫ evaluation piB sX sB eB heB =
      evaluation piA sX sA eA heA := by
  apply pullback.hom_ext
  · simp only [Category.assoc, evaluation_left, map_left_assoc, he]
  · simp only [Category.assoc, evaluation_right, map_right_assoc, he]

/-- Tensor specialization along an arbitrary source-family map.  The
proof is canonical tensor coherence on both actual endpoint bundles. -/
theorem product_baseChange {C A D B X : Scheme}
    (piA : C ⟶ A) (piB : D ⟶ B)
    (sX : X ⟶ ComplexBase) (sA : A ⟶ ComplexBase) (sB : B ⟶ ComplexBase)
    (eA : C ⟶ X) (eB : D ⟶ X)
    (heA : eA ≫ sX = piA ≫ sA) (heB : eB ≫ sX = piB ≫ sB)
    (k : C ⟶ D) (hke : k ≫ eB = eA)
    (q : Space piA ⟶ Space piB)
    (hq₁ : q ≫ left piB = left piA ≫ k)
    (hq₂ : q ≫ right piB = right piA ≫ k)
    (hq : q ≫ evaluation piB sX sB eB heB = evaluation piA sX sA eA heA)
    {E F : OModule X}
    (aB : AlgebraicSection (pullbackModule eB E))
    (bB : AlgebraicSection (pullbackModule eB F))
    (aA : AlgebraicSection (pullbackModule eA E))
    (bA : AlgebraicSection (pullbackModule eA F))
    (ha : pullSection k aB ≫ (compositionPullback k eB eA hke E).hom = aA)
    (hb : pullSection k bB ≫ (compositionPullback k eB eA hke F).hom = bA) :
    pullSection q (productSection piB aB bB ≫ comparison piB sX sB eB heB E F) ≫
        (compositionPullback q (evaluation piB sX sB eB heB)
          (evaluation piA sX sA eA heA) hq (externalTensor sX E F)).hom =
      productSection piA aA bA ≫ comparison piA sX sA eA heA E F := by
  let D := Descent.LineValue.externalAlongIso sX (evaluation piA sX sA eA heA)
    (left piA ≫ eA) (right piA ≫ eA)
    (evaluation_left piA sX sA eA heA) (evaluation_right piA sX sA eA heA) E F
  have hqe₁ : (q ≫ left piB) ≫ eB = left piA ≫ eA := by
    rw [hq₁, Category.assoc, hke]
  have hqe₂ : (q ≫ right piB) ≫ eB = right piA ≫ eA := by
    rw [hq₂, Category.assoc, hke]
  apply (cancel_mono D.inv).mp
  rw [Category.assoc]
  rw [product_pullback piB sX sB eB heB q (evaluation piA sX sA eA heA) hq
    (left piA ≫ eA) (right piA ≫ eA)
    (evaluation_left piA sX sA eA heA) (evaluation_right piA sX sA eA heA)
    hqe₁ hqe₂ aB bB]
  have ha' := SectionTransport.pull_specialization (left piA) k eB
    (q ≫ left piB) eA (left piA ≫ eA) hq₁.symm hke rfl hqe₁ aB aA ha
  have hb' := SectionTransport.pull_specialization (right piA) k eB
    (q ≫ right piB) eA (right piA ≫ eA) hq₂.symm hke rfl hqe₂ bB bA hb
  rw [ha', hb']
  exact (product_normalize piA sX sA eA heA aA bA).symm

end RelativeSquare

namespace Parametrized

variable (P : ProjectiveLineOverC)
variable {A B : Scheme} (sA : A ⟶ ComplexBase) (sB : B ⟶ ComplexBase)
variable (b : A ⟶ B) (hb : b ≫ sB = sA)
variable (k : Source P sA ⟶ Source P sB)
variable (hk₁ : k ≫ projection P sB = projection P sA)
variable (hk₂ : k ≫ parameter P sB = parameter P sA ≫ b)

include hb in
/-- The two canonical cotangent base-change maps commute with an
arbitrary further base change. -/
theorem canonicalMap_baseChange :
    (Scheme.Modules.pullback k).map (CotangentBaseChange.canonicalMap P.structureMap sB) ≫
        RelativeDifferential.cotangent (parameter P sA) (parameter P sB) k b hk₂ =
      (compositionPullback k (projection P sB) (projection P sA) hk₁
        (cotangentSheaf P.structureMap)).hom ≫
          CotangentBaseChange.canonicalMap P.structureMap sA := by
  have hcomp : (k ≫ projection P sB) ≫ P.structureMap =
      parameter P sA ≫ (b ≫ sB) := by
    rw [hk₁, hb]
    exact pullback.condition
  have hc := RelativeDifferential.cotangent_comp (parameter P sA)
    (parameter P sB) P.structureMap k b (projection P sB) sB hk₂
    (pullback.condition (f := P.structureMap) (g := sB)) hcomp
  rw [RelativeDifferential.cotangent_baseChange] at hc
  rw [RelativeDifferential.cotangent_congr (parameter P sA) P.structureMap
    hk₁ hb hcomp (pullback.condition (f := P.structureMap) (g := sA))] at hc
  simpa only [RelativeDifferential.cotangent_baseChange, compositionPullback,
    Iso.trans_hom, Iso.app_hom, eqToIso.hom, Category.assoc] using hc.symm

variable {d : ℕ} (X : SmoothProperComplexVariety d)
variable (eB : Source P sB ⟶ X.scheme)
variable (heB : eB ≫ X.structureMap = parameter P sB ≫ sB)
variable (eA : Source P sA ⟶ X.scheme)
variable (heA : eA ≫ X.structureMap = parameter P sA ≫ sA)
variable (hke : k ≫ eB = eA)

include hb in
theorem relativeCotangentMap_baseChange :
    (Scheme.Modules.pullback k).map (relativeCotangentMap P sB X eB heB) ≫
        RelativeDifferential.cotangent (parameter P sA) (parameter P sB) k b hk₂ =
      (compositionPullback k eB eA hke (cotangentSheaf X.structureMap)).hom ≫
        relativeCotangentMap P sA X eA heA := by
  have hcomp : (k ≫ eB) ≫ X.structureMap = parameter P sA ≫ (b ≫ sB) := by
    rw [hke, hb]
    exact heA
  have hc := RelativeDifferential.cotangent_comp (parameter P sA)
    (parameter P sB) X.structureMap k b eB sB hk₂ heB hcomp
  rw [RelativeDifferential.cotangent_congr (parameter P sA) X.structureMap
    hke hb hcomp heA] at hc
  simpa only [RelativeDifferential.cotangent, relativeCotangentMap,
    compositionPullback, Iso.trans_hom, Iso.app_hom, eqToIso.hom,
    Category.assoc] using hc.symm

@[reassoc] theorem relativeCotangent_normalized :
    relativeCotangent P sB X eB heB ≫
        CotangentBaseChange.canonicalMap P.structureMap sB =
      relativeCotangentMap P sB X eB heB := by
  letI := LeBrunSalamon.StandardInputs.cotangentPullback_isIso P.structureMap sB
  simp only [relativeCotangent, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

include hb hk₂ in
/-- Relative derivatives commute with arbitrary base change before
duality, with the source coordinate and the actual evaluation map fixed. -/
theorem relativeCotangent_baseChange :
    (Scheme.Modules.pullback k).map (relativeCotangent P sB X eB heB) ≫
        (compositionPullback k (projection P sB) (projection P sA) hk₁
          (cotangentSheaf P.structureMap)).hom =
      (compositionPullback k eB eA hke (cotangentSheaf X.structureMap)).hom ≫
        relativeCotangent P sA X eA heA := by
  letI := LeBrunSalamon.StandardInputs.cotangentPullback_isIso P.structureMap sA
  apply (cancel_mono (CotangentBaseChange.canonicalMap P.structureMap sA)).mp
  simp only [Category.assoc]
  rw [← canonicalMap_baseChange P sA sB b hb k hk₁ hk₂]
  rw [← Category.assoc, ← Functor.map_comp, relativeCotangent_normalized]
  rw [relativeCotangentMap_baseChange P sA sB b hb k hk₂ X eB heB eA heA hke]
  rw [relativeCotangent_normalized]

include hb hk₂ in
/-- The exact tangent map has the same arbitrary-base compatibility.
The proof uses evaluation-normalized duality; it introduces no scalar. -/
theorem differential_baseChange :
    (Scheme.Modules.pullback k).map (differential P sB X eB heB) ≫
        (compositionPullback k eB eA hke (tangentSheaf X.structureMap)).hom =
      (compositionPullback k (projection P sB) (projection P sA) hk₁
        (tangentSheaf P.structureMap)).hom ≫ differential P sA X eA heA := by
  letI := dualBaseChange_isIso eA (smooth_cotangent_rank X.structureMap d X.smooth)
  letI := dualBaseChange_isIso eB (smooth_cotangent_rank X.structureMap d X.smooth)
  apply (cancel_mono (dualBaseChange eA (cotangentSheaf X.structureMap))).mp
  simp only [Category.assoc]
  rw [BaseChange.dual_composition k eB eA hke (cotangentSheaf X.structureMap)]
  rw [← Category.assoc, ← Functor.map_comp, differential_normalized]
  simp only [Functor.map_comp, Category.assoc]
  rw [dualBaseChange_naturality_assoc]
  rw [← Category.assoc,
    BaseChange.dual_composition_normalized k (projection P sB) (projection P sA)
      hk₁ (cotangentSheaf P.structureMap)]
  simp only [Category.assoc, ← dualMap_comp]
  have hc := relativeCotangent_baseChange P sA sB b hb k hk₁ hk₂
    X eB heB eA heA hke
  have ht := congrArg (fun m =>
    (compositionPullback k eB eA hke (cotangentSheaf X.structureMap)).inv ≫ m) hc
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] at ht
  rw [ht, differential_normalized]

include hb hk₁ hk₂ in
/-- Every fixed global source field specializes along an arbitrary
base map to its actual relative derivative in the pulled family. -/
theorem vector_baseChange (v : AlgebraicSection (tangentSheaf P.structureMap)) :
    pullSection k (vector P sB X eB heB v) ≫
        (compositionPullback k eB eA hke (tangentSheaf X.structureMap)).hom =
      vector P sA X eA heA v := by
  rw [vector, pullSection_naturality, Category.assoc,
    differential_baseChange P sA sB b hb k hk₁ hk₂ X eB heB eA heA hke,
    ← Category.assoc, compositionPullback_sections]
  rfl

end Parametrized

namespace ParametrizedContact

variable (P : ProjectiveLineOverC)
variable {A B : Scheme} (sA : A ⟶ ComplexBase) (sB : B ⟶ ComplexBase)
variable (b : A ⟶ B) (hb : b ≫ sB = sA)
variable (k : Parametrized.Source P sA ⟶ Parametrized.Source P sB)
variable (hk₁ : k ≫ Parametrized.projection P sB = Parametrized.projection P sA)
variable (hk₂ : k ≫ Parametrized.parameter P sB = Parametrized.parameter P sA ≫ b)
variable {n : ℕ} (X : ContactFanoManifold n)
variable (eB : Parametrized.Source P sB ⟶ X.variety.scheme)
variable (heB : eB ≫ X.variety.structureMap = Parametrized.parameter P sB ≫ sB)
variable (eA : Parametrized.Source P sA ⟶ X.variety.scheme)
variable (heA : eA ≫ X.variety.structureMap = Parametrized.parameter P sA ≫ sA)
variable (hke : k ≫ eB = eA)

include hb hk₁ hk₂ in
theorem contactVector_baseChange (v : AlgebraicSection (tangentSheaf P.structureMap)) :
    pullSection k (contactVector P sB X eB heB v) ≫
        (compositionPullback k eB eA hke X.contact.sequence.line.sheaf).hom =
      contactVector P sA X eA heA v := by
  have hv : contactVector P sB X eB heB v =
      Parametrized.vector P sB X.variety eB heB v ≫
        (Scheme.Modules.pullback eB).map X.contact.sequence.form := by
    simp only [contactVector, velocity, Parametrized.vector, Category.assoc]
  rw [hv]
  rw [pullSection_naturality, Category.assoc,
    Normalization.BundleGluing.compositionPullback_naturality, ← Category.assoc,
    Parametrized.vector_baseChange P sA sB b hb k hk₁ hk₂ X.variety eB heB eA heA hke]
  simp only [contactVector, velocity, Parametrized.vector, Category.assoc]

variable (q : Parametrized.Square P sA ⟶ Parametrized.Square P sB)
variable (hq₁ : q ≫ RelativeSquare.left (Parametrized.parameter P sB) =
  RelativeSquare.left (Parametrized.parameter P sA) ≫ k)
variable (hq₂ : q ≫ RelativeSquare.right (Parametrized.parameter P sB) =
  RelativeSquare.right (Parametrized.parameter P sA) ≫ k)
variable (hq : q ≫ evaluationSquare P sB X eB heB = evaluationSquare P sA X eA heA)

include hb hk₁ hk₂ hke hq₁ hq₂ in
/-- The complete first mixed tensor commutes with arbitrary base
change, including a field extension or a formal generic-point map. -/
theorem leftSection_baseChange :
    pullSection q (leftSection P sB X eB heB) ≫
        (compositionPullback q (evaluationSquare P sB X eB heB)
          (evaluationSquare P sA X eA heA) hq
          (movingPairBundleLeft X.variety X.contact)).hom =
      leftSection P sA X eA heA := by
  obtain ⟨E⟩ := externalExpansion_exists (projectiveLineVariety P)
    (identityCurveContact P).sequence.line (sourceBivector P)
  rw [leftSection_expansion P sB X eB heB E, leftSection_expansion P sA X eA heA E,
    SectionTransport.pull_sum, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro i hi
  exact RelativeSquare.product_baseChange (Parametrized.parameter P sA)
    (Parametrized.parameter P sB) X.variety.structureMap sA sB eA eB heA heB k hke
    q hq₁ hq₂ hq
    (Parametrized.vector P sB X.variety eB heB (E.left i))
    (contactVector P sB X eB heB (E.right i))
    (Parametrized.vector P sA X.variety eA heA (E.left i))
    (contactVector P sA X eA heA (E.right i))
    (Parametrized.vector_baseChange P sA sB b hb k hk₁ hk₂ X.variety
      eB heB eA heA hke (E.left i))
    (contactVector_baseChange P sA sB b hb k hk₁ hk₂ X eB heB eA heA hke (E.right i))

include hb hk₁ hk₂ hke hq₁ hq₂ in
theorem rightSection_baseChange :
    pullSection q (rightSection P sB X eB heB) ≫
        (compositionPullback q (evaluationSquare P sB X eB heB)
          (evaluationSquare P sA X eA heA) hq
          (movingPairBundleRight X.variety X.contact)).hom =
      rightSection P sA X eA heA := by
  obtain ⟨E⟩ := externalExpansion_exists (projectiveLineVariety P)
    (identityCurveContact P).sequence.line (sourceBivector P)
  rw [rightSection_expansion P sB X eB heB E, rightSection_expansion P sA X eA heA E,
    SectionTransport.pull_sum, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro i hi
  exact RelativeSquare.product_baseChange (Parametrized.parameter P sA)
    (Parametrized.parameter P sB) X.variety.structureMap sA sB eA eB heA heB k hke
    q hq₁ hq₂ hq
    (contactVector P sB X eB heB (E.left i))
    (Parametrized.vector P sB X.variety eB heB (E.right i))
    (contactVector P sA X eA heA (E.left i))
    (Parametrized.vector P sA X.variety eA heA (E.right i))
    (contactVector_baseChange P sA sB b hb k hk₁ hk₂ X eB heB eA heA hke (E.left i))
    (Parametrized.vector_baseChange P sA sB b hb k hk₁ hk₂ X.variety
      eB heB eA heA hke (E.right i))

end ParametrizedContact

end LeBrunSalamon.Construction.FamilyBivectors

end

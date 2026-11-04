import RecompileExtensionsPart04Geometry

/-! Changing an actual generating quotient tuple by a matrix of global
functions. The proof uses explicit maps between finite free sheaves; it
does not replace generation by a pointwise condition. No admission. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.Skeleton
open LeBrunSalamon.Construction.Smoothing.CoordinateCharts

namespace LeBrunSalamon.ConicTupleChange

@[simp] theorem scalar_zero {Y : Scheme} :
    scalarSection (0 : RingSections Y ⊤) = 0 :=
  sectionFromValue_zero _

theorem scalar_sum {Y : Scheme} {ι : Type} (s : Finset ι)
    (a : ι → RingSections Y ⊤) :
    scalarSection (∑ i ∈ s, a i) = ∑ i ∈ s, scalarSection (a i) := by
  change (sectionAddEquiv (structureModule Y)).symm (∑ i ∈ s, a i) =
    ∑ i ∈ s, (sectionAddEquiv (structureModule Y)).symm (a i)
  exact map_sum (sectionAddEquiv (structureModule Y)).symm a s

def combine {Y : Scheme} {E : OModule Y} {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) (RingSections Y ⊤))
    (a : Fin n → AlgebraicSection E) (i : Fin m) : AlgebraicSection E :=
  ∑ j, scalarSection (A i j) ≫ a j

/-- The scalar endomorphism acts by the original module action on sections. -/
theorem scalar_comp {Y : Scheme} {E : OModule Y}
    (r : RingSections Y ⊤) (a : AlgebraicSection E) :
    scalarSection r ≫ a = sectionFromValue (r • sectionValue a) := by
  apply (sectionValue_bijective E).injective
  rw [sectionValue_comp, scalarSection, sectionFromValue_spec, sectionFromValue_spec]
  change Scheme.Modules.Hom.app a ⊤ r =
    r • Scheme.Modules.Hom.app a ⊤ (1 : RingSections Y ⊤)
  simpa only [smul_eq_mul, mul_one] using
    (Scheme.Modules.Hom.app_smul a r (1 : RingSections Y ⊤))

theorem combine_post {Y : Scheme} {E F : OModule Y} {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) (RingSections Y ⊤))
    (a : Fin n → AlgebraicSection E) (h : E ⟶ F) (i : Fin m) :
    combine A a i ≫ h = combine A (fun j => a j ≫ h) i := by
  simp only [combine, Preadditive.sum_comp, Category.assoc]

theorem combine_mul {Y : Scheme} {E : OModule Y} {l m n : ℕ}
    (B : Matrix (Fin l) (Fin m) (RingSections Y ⊤))
    (A : Matrix (Fin m) (Fin n) (RingSections Y ⊤))
    (a : Fin n → AlgebraicSection E) :
    combine B (combine A a) = combine (B * A) a := by
  funext i
  simp only [combine, Preadditive.comp_sum, ← Category.assoc,
    ← Construction.Smoothing.SourceAffineCharts.scalarSection_mul, Matrix.mul_apply,
    scalar_sum, Preadditive.sum_comp]
  exact Finset.sum_comm

theorem combine_one {Y : Scheme} {E : OModule Y} {n : ℕ}
    (a : Fin n → AlgebraicSection E) :
    combine (1 : Matrix (Fin n) (Fin n) (RingSections Y ⊤)) a = a := by
  classical
  funext i
  unfold combine
  rw [Finset.sum_eq_single i]
  · simp [Matrix.one_apply, scalarSection_one]
  · intro j hj hji
    simp [Matrix.one_apply, Ne.symm hji]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

theorem combine_inverse {Y : Scheme} {E : OModule Y} {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) (RingSections Y ⊤))
    (hBA : B * A = 1) (a : Fin n → AlgebraicSection E) :
    combine B (combine A a) = a := by
  rw [combine_mul, hBA, combine_one]

/-- If the original generating tuple is recovered by a linear combination
of a new tuple, the new tuple generates the same actual sheaf. -/
theorem generates_of_combine {Y : Scheme} (L : LineBundle Y) {m n : ℕ}
    (a : Fin (m + 1) → AlgebraicSection L.sheaf)
    (b : Fin (n + 1) → AlgebraicSection L.sheaf)
    (ha : TupleGenerates L a)
    (A : Matrix (Fin (m + 1)) (Fin (n + 1)) (RingSections Y ⊤))
    (h : ∀ i, combine A b i = a i) : TupleGenerates L b := by
  let u : (∐ fun _ : Fin (m + 1) => structureModule Y) ⟶
      (∐ fun _ : Fin (n + 1) => structureModule Y) :=
    Sigma.desc (fun i => ∑ j, scalarSection (A i j) ≫
      Sigma.ι (fun _ : Fin (n + 1) => structureModule Y) j)
  have hfac : u ≫ Sigma.desc b = Sigma.desc a := by
    apply Sigma.hom_ext
    intro i
    simpa only [u, Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc,
      Preadditive.sum_comp, Category.assoc, combine] using h i
  letI : Epi (Sigma.desc a) := ha
  exact epi_of_epi_fac hfac

/-- Applying a matrix and a specified inverse preserves quotient generation.
The inverse identities can subsequently be supplied by a GL matrix. -/
theorem generates_change {Y : Scheme} (L : LineBundle Y) {n : ℕ}
    (a : Fin (n + 1) → AlgebraicSection L.sheaf)
    (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) (RingSections Y ⊤))
    (ha : TupleGenerates L a) (hBA : B * A = 1) :
    TupleGenerates L (combine A a) :=
  generates_of_combine L a (combine A a) ha B (congrFun (combine_inverse A B hBA a))

end LeBrunSalamon.ConicTupleChange
end

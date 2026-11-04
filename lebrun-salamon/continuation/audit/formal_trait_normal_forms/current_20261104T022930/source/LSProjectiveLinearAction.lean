import LSConicTupleChange
import LSStandardProjectiveBaseChange

/-!
Actual projective automorphisms defined by invertible matrices, with the
tautological line and every homogeneous coordinate normalized.  The proof
uses the existing standard quotient universal property.  No additional
published input is introduced.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.Refinement

namespace LeBrunSalamon.ProjectiveLinearAction

open ConicTupleChange

variable {R : Type} [CommRing R]

/-- Actual coefficients as global functions, for any scheme over Spec R. -/
def coefficientHom {Y : Scheme} (p : Y ⟶ Spec (CommRingCat.of R)) :
    R →+* RingSections Y ⊤ :=
  p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

def coefficientMatrix {Y : Scheme} (p : Y ⟶ Spec (CommRingCat.of R))
    {m n : ℕ} (M : Matrix (Fin m) (Fin n) R) :
    Matrix (Fin m) (Fin n) (RingSections Y ⊤) :=
  fun i j => coefficientHom p (M i j)

theorem coefficientMatrix_mul {Y : Scheme} (p : Y ⟶ Spec (CommRingCat.of R))
    {l m n : ℕ} (B : Matrix (Fin l) (Fin m) R) (A : Matrix (Fin m) (Fin n) R) :
    coefficientMatrix p (B * A) = coefficientMatrix p B * coefficientMatrix p A := by
  ext i j
  simp only [coefficientMatrix, Matrix.mul_apply, map_sum, map_mul]

theorem coefficientMatrix_one {Y : Scheme} (p : Y ⟶ Spec (CommRingCat.of R))
    (n : ℕ) : coefficientMatrix p (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  classical
  ext i j
  simp [coefficientMatrix, Matrix.one_apply]

theorem coefficient_pull {X Y : Scheme} (p : Y ⟶ Spec (CommRingCat.of R))
    (s : X ⟶ Spec (CommRingCat.of R)) (f : X ⟶ Y) (hf : f ≫ p = s) (a : R) :
    f.appTop (coefficientHom p a) = coefficientHom s a := by
  change (p.appTop ≫ f.appTop) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a) = _
  rw [← Scheme.Hom.comp_appTop, hf]
  rfl

/-- Pulling a matrix combination uses the actual coefficient map on functions. -/
theorem pull_combine {X Y : Scheme} (p : Y ⟶ Spec (CommRingCat.of R))
    (s : X ⟶ Spec (CommRingCat.of R)) (f : X ⟶ Y) (hf : f ≫ p = s)
    {E : OModule Y} {F : OModule X} {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) R) (a : Fin n → AlgebraicSection E)
    (e : pullbackModule f E ≅ F) (i : Fin m) :
    pullSection f (combine (coefficientMatrix p A) a i) ≫ e.hom =
      combine (coefficientMatrix s A) (fun j => pullSection f (a j) ≫ e.hom) i := by
  simp only [combine, pullSection, restrictSection, Functor.map_sum,
    Preadditive.comp_sum, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro j hj
  change pullSection f
      (Construction.Smoothing.CoordinateCharts.scalarSection (coefficientHom p (A i j)) ≫ a j) ≫
      e.hom = Construction.Smoothing.CoordinateCharts.scalarSection
        (coefficientHom s (A i j)) ≫ (pullSection f (a j) ≫ e.hom)
  rw [scalar_comp, scalar_comp,
    Construction.Smoothing.StandardSourceProof.pullSection_scalar,
    Construction.Smoothing.StandardSourceProof.scalarSection_comp,
    coefficient_pull p s f hf]

variable (R) (N : ℕ)

abbrev Space := StandardTautological.space R N

def tuple (M : (Matrix (Fin (N+1)) (Fin (N+1)) R)ˣ) :
    Fin (N+1) → AlgebraicSection (StandardTautological.line R N).sheaf :=
  combine (coefficientMatrix (StandardTautological.toSpec R N) M.val)
    (StandardTautological.coordinate R N)

theorem tuple_generates (M : (Matrix (Fin (N+1)) (Fin (N+1)) R)ˣ) :
    Epi (Sigma.desc (tuple R N M)) := by
  apply generates_change (StandardTautological.line R N)
    (StandardTautological.coordinate R N)
    (coefficientMatrix (StandardTautological.toSpec R N) M.val)
    (coefficientMatrix (StandardTautological.toSpec R N) M.inv)
    (StandardTautological.generates R N)
  rw [← coefficientMatrix_mul, M.inv_val, coefficientMatrix_one]

def mapPoint (M : (Matrix (Fin (N+1)) (Fin (N+1)) R)ˣ) :
    {f : Space R N ⟶ Space R N //
      f ≫ StandardTautological.toSpec R N = StandardTautological.toSpec R N} :=
  Classical.choose ((StandardTautological.chosen R N).universal
    (Space R N) (StandardTautological.toSpec R N)
    (StandardTautological.line R N).sheaf (StandardTautological.line R N).locallyFree
    (tuple R N M) (tuple_generates R N M))

abbrev map (M : (Matrix (Fin (N+1)) (Fin (N+1)) R)ˣ) : Space R N ⟶ Space R N :=
  (mapPoint R N M).val

theorem map_spec (M : (Matrix (Fin (N+1)) (Fin (N+1)) R)ˣ) :
    ∃ e : pullbackModule (map R N M) (StandardTautological.line R N).sheaf ≅
        (StandardTautological.line R N).sheaf,
      ∀ i, pullSection (map R N M) (StandardTautological.coordinate R N i) ≫ e.hom =
        tuple R N M i :=
  (Classical.choose_spec ((StandardTautological.chosen R N).universal
    (Space R N) (StandardTautological.toSpec R N)
    (StandardTautological.line R N).sheaf (StandardTautological.line R N).locallyFree
    (tuple R N M) (tuple_generates R N M))).1

def lineIso (M : (Matrix (Fin (N+1)) (Fin (N+1)) R)ˣ) :
    pullbackModule (map R N M) (StandardTautological.line R N).sheaf ≅
      (StandardTautological.line R N).sheaf := Classical.choose (map_spec R N M)

theorem coordinate (M : (Matrix (Fin (N+1)) (Fin (N+1)) R)ˣ) (i : Fin (N+1)) :
    pullSection (map R N M) (StandardTautological.coordinate R N i) ≫
      (lineIso R N M).hom = tuple R N M i := Classical.choose_spec (map_spec R N M) i

/-- The universal quotient identifies the inverse-coordinate composite with
the actual identity map, including its standard line normalization. -/
theorem map_inv_map (M : (Matrix (Fin (N+1)) (Fin (N+1)) R)ˣ) :
    map R N M ≫ map R N M⁻¹ = 𝟙 (Space R N) := by
  let D := StandardTautological.chosen R N
  let f := map R N M
  let g := map R N M⁻¹
  let c : pullbackModule (f ≫ g) D.sheaf ≅ D.sheaf :=
    ((Scheme.Modules.pullbackComp f g).app D.sheaf).symm ≪≫
      (Scheme.Modules.pullback f).mapIso (lineIso R N M⁻¹) ≪≫ lineIso R N M
  have hc (i : Fin (N+1)) : pullSection (f ≫ g) (D.coordinate i) ≫ c.hom = D.coordinate i := by
    rw [StandardProjectiveBaseChange.composite_coordinate]
    have hg : pullSection g (D.coordinate i) ≫ (lineIso R N M⁻¹).hom = tuple R N M⁻¹ i :=
      coordinate R N M⁻¹ i
    rw [hg]
    rw [tuple, pull_combine (StandardTautological.toSpec R N)
      (StandardTautological.toSpec R N) f (mapPoint R N M).property]
    have hcoords : (fun j => pullSection f (StandardTautological.coordinate R N j) ≫
        (lineIso R N M).hom) = tuple R N M := funext (coordinate R N M)
    rw [hcoords]
    change combine (coefficientMatrix (StandardTautological.toSpec R N) M.inv)
      (combine (coefficientMatrix (StandardTautological.toSpec R N) M.val)
        (StandardTautological.coordinate R N)) i = _
    rw [combine_mul, ← coefficientMatrix_mul, M.inv_val, coefficientMatrix_one, combine_one]
    rfl
  have hb : (f ≫ g) ≫ StandardTautological.toSpec R N = StandardTautological.toSpec R N := by
    rw [Category.assoc, (mapPoint R N M⁻¹).property, (mapPoint R N M).property]
  obtain ⟨u, _, hu⟩ := D.universal (Space R N) (StandardTautological.toSpec R N)
    D.sheaf D.locallyFree D.coordinate D.generates
  exact congrArg Subtype.val ((hu ⟨f ≫ g, hb⟩ ⟨c, hc⟩).trans
    (hu ⟨𝟙 _, Category.id_comp _⟩
      ⟨(Scheme.Modules.pullbackId _).app D.sheaf,
        fun i => ExternalExchangeCoherenceProof.pullSection_id (D.coordinate i)⟩).symm)

def iso (M : (Matrix (Fin (N+1)) (Fin (N+1)) R)ˣ) : Space R N ≅ Space R N where
  hom := map R N M
  inv := map R N M⁻¹
  hom_inv_id := map_inv_map R N M
  inv_hom_id := by simpa only [inv_inv] using map_inv_map R N M⁻¹

theorem over_base (M : (Matrix (Fin (N+1)) (Fin (N+1)) R)ˣ) :
    (iso R N M).hom ≫ StandardTautological.toSpec R N = StandardTautological.toSpec R N :=
  (mapPoint R N M).property

end LeBrunSalamon.ProjectiveLinearAction
end

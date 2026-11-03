import LSContactCompletion
import LSNilpotentTopology
import LSDualThickeningNormalForm

/-!
## Canonical functions on the actual trivial first-order thickening

The only proposed generic inputs are the topology of the nilpotent
thickening and the canonical two-coefficient normal form of its functions.
All coefficients are normalized by the actual projection and the actual
epsilon from Spec(C[epsilon]/epsilon²). No family or contact assertion is
part of either generic boundary.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction

namespace LeBrunSalamon.Construction.Lines.DualThickening

/-- The reduction point of the actual dual-number spectrum lies over C.
This is proved by Spec functoriality, avoiding the historical admission. -/
theorem origin_overC : Infinitesimal.origin ≫ Infinitesimal.dualToC =
    𝟙 ComplexBase := by
  change Spec.map (CommRingCat.ofHom Infinitesimal.residue.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap ℂ Infinitesimal.Dual)) = _
  rw [← Spec.map_comp]
  convert Spec.map_id (CommRingCat.of ℂ) using 1
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  exact Infinitesimal.residue.commutes c

/-- The residue map of the actual dual numbers has nilpotent kernel.
This uses their proved two-coefficient normal form. -/
theorem residue_kernel_nilpotent (z : Infinitesimal.Dual)
    (hz : Infinitesimal.residue z = 0) : IsNilpotent z := by
  obtain ⟨⟨a, b⟩, hab, _⟩ := Infinitesimal.dual_normalForm z
  have ha : a = 0 := by
    simpa only [hab, Infinitesimal.residue_normalForm] using hz
  subst a
  refine ⟨2, ?_⟩
  rw [hab, map_zero, zero_add, mul_pow, Infinitesimal.epsilon_square, zero_mul]

/-- Every point of the actual dual-number spectrum is a reduction point.
The proof uses the nilpotent kernel, not an admitted project wrapper. -/
theorem origin_surjective : Function.Surjective Infinitesimal.origin := by
  apply LeBrunSalamon.NilpotentTopology.specMap_surjective_of_nilpotent_ker
    Infinitesimal.residue.toRingHom
  · intro c
    exact ⟨algebraMap ℂ Infinitesimal.Dual c, Infinitesimal.residue.commutes c⟩
  · exact residue_kernel_nilpotent

abbrev space {Y : Scheme} (sY : Y ⟶ ComplexBase) : Scheme :=
  pullback sY Infinitesimal.dualToC

def projection {Y : Scheme} (sY : Y ⟶ ComplexBase) : space sY ⟶ Y :=
  pullback.fst sY Infinitesimal.dualToC

def parameter {Y : Scheme} (sY : Y ⟶ ComplexBase) :
    space sY ⟶ Infinitesimal.DualScheme :=
  pullback.snd sY Infinitesimal.dualToC

def toC {Y : Scheme} (sY : Y ⟶ ComplexBase) : space sY ⟶ ComplexBase :=
  projection sY ≫ sY

theorem parameter_overC {Y : Scheme} (sY : Y ⟶ ComplexBase) :
    parameter sY ≫ Infinitesimal.dualToC = toC sY :=
  (pullback.condition (f := sY) (g := Infinitesimal.dualToC)).symm

def zeroSection {Y : Scheme} (sY : Y ⟶ ComplexBase) : Y ⟶ space sY :=
  pullback.lift (𝟙 Y) (sY ≫ Infinitesimal.origin)
    (by simp [Category.assoc, origin_overC])

@[simp] theorem zeroSection_projection {Y : Scheme} (sY : Y ⟶ ComplexBase) :
    zeroSection sY ≫ projection sY = 𝟙 Y := by
  simp [zeroSection, projection]

@[simp] theorem zeroSection_parameter {Y : Scheme} (sY : Y ⟶ ComplexBase) :
    zeroSection sY ≫ parameter sY = sY ≫ Infinitesimal.origin := by
  simp [zeroSection, parameter]

theorem zeroSection_overC {Y : Scheme} (sY : Y ⟶ ComplexBase) :
    zeroSection sY ≫ toC sY = sY := by
  simp [toC, ← Category.assoc]

/-- Actual base change of a source morphism, retaining the same epsilon. -/
def map {Y Z : Scheme} {sY : Y ⟶ ComplexBase} {sZ : Z ⟶ ComplexBase}
    (g : Y ⟶ Z) (hg : g ≫ sZ = sY) : space sY ⟶ space sZ :=
  pullback.lift (projection sY ≫ g) (parameter sY) (by
    rw [Category.assoc, hg]
    exact pullback.condition)

@[simp] theorem map_projection {Y Z : Scheme}
    {sY : Y ⟶ ComplexBase} {sZ : Z ⟶ ComplexBase}
    (g : Y ⟶ Z) (hg : g ≫ sZ = sY) :
    map g hg ≫ projection sZ = projection sY ≫ g := by
  simp [map, projection]

@[simp] theorem map_parameter {Y Z : Scheme}
    {sY : Y ⟶ ComplexBase} {sZ : Z ⟶ ComplexBase}
    (g : Y ⟶ Z) (hg : g ≫ sZ = sY) :
    map g hg ≫ parameter sZ = parameter sY := by
  simp [map, parameter]

theorem zeroSection_naturality {Y Z : Scheme}
    {sY : Y ⟶ ComplexBase} {sZ : Z ⟶ ComplexBase}
    (g : Y ⟶ Z) (hg : g ≫ sZ = sY) :
    zeroSection sY ≫ map g hg = g ≫ zeroSection sZ := by
  apply pullback.hom_ext
  · change (zeroSection sY ≫ map g hg) ≫ projection sZ =
      (g ≫ zeroSection sZ) ≫ projection sZ
    simp only [Category.assoc, map_projection, zeroSection_projection, Category.comp_id]
    rw [← Category.assoc, zeroSection_projection, Category.id_comp]
  · change (zeroSection sY ≫ map g hg) ≫ parameter sZ =
      (g ≫ zeroSection sZ) ≫ parameter sZ
    simp only [Category.assoc, map_parameter, zeroSection_parameter]
    rw [← Category.assoc, hg]

/-- Restrict the actual globally pulled-back epsilon, without choosing a
trivialization of the conormal line. -/
def epsilonOn {Y : Scheme} (sY : Y ⟶ ComplexBase) (U : Y.Opens) :
    RingSections (space sY) ((projection sY) ⁻¹ᵁ U) :=
  (space sY).presheaf.map (homOfLE le_top).op
    ((parameter sY).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).inv Infinitesimal.epsilon))

/-- The section formula used by the standard normal-form input. -/
def normalForm {Y : Scheme} (sY : Y ⟶ ComplexBase) (U : Y.Opens)
    (a b : RingSections Y U) : RingSections (space sY) ((projection sY) ⁻¹ᵁ U) :=
  (projection sY).app U a + epsilonOn sY U * (projection sY).app U b

theorem epsilonOn_square {Y : Scheme} (sY : Y ⟶ ComplexBase) (U : Y.Opens) :
    (epsilonOn sY U)^2 = 0 := by
  unfold epsilonOn
  rw [← map_pow, ← map_pow, ← map_pow, Infinitesimal.epsilon_square]
  simp

end LeBrunSalamon.Construction.Lines.DualThickening

namespace LeBrunSalamon.Construction.StandardInputs.InfinitesimalGeometry

/-- DT-01. The canonical nilpotent thickening has the same underlying
points as its reduction. This is proved from the actual dual-number
normal form and mathlib's pullback carrier theorem. -/
theorem _root_.LeBrunSalamon.PublishedInputs.Step3f.dualThickening_zeroSection_surjective
    {Y : Scheme} (sY : Y ⟶ ComplexBase) :
    Function.Surjective (Lines.DualThickening.zeroSection sY) := by
  exact LeBrunSalamon.NilpotentTopology.splitSection_surjective
    sY Infinitesimal.dualToC Infinitesimal.origin
    Lines.DualThickening.origin_overC Lines.DualThickening.origin_surjective

/-- Project-facing form of the proved nilpotent base-change theorem. -/
theorem dualThickening_zeroSection_surjective
    {Y : Scheme} (sY : Y ⟶ ComplexBase) :
    Function.Surjective (Lines.DualThickening.zeroSection sY) := by
  exact LeBrunSalamon.PublishedInputs.Step3f.dualThickening_zeroSection_surjective sY

/-- DT-02. The actual two-coefficient formula on every open is proved
from finite free degree-zero base change (Stacks 0CKW). The tensor basis
uses the original quotient epsilon, and the restriction-square proof
retains the actual projection and parameter maps. -/
theorem _root_.LeBrunSalamon.PublishedInputs.Step3f.dualThickening_normalForm_unique
    {Y : Scheme} (sY : Y ⟶ ComplexBase) (U : Y.Opens)
    (z : RingSections (Lines.DualThickening.space sY)
      ((Lines.DualThickening.projection sY) ⁻¹ᵁ U)) :
    ∃! ab : RingSections Y U × RingSections Y U,
      z = Lines.DualThickening.normalForm sY U ab.1 ab.2 := by
  exact LeBrunSalamon.DualBaseChangeAlgebra.open_normalForm_unique sY
    (Lines.DualThickening.projection sY) (Lines.DualThickening.parameter sY)
    (IsPullback.of_hasPullback sY Infinitesimal.dualToC) U z

/-- Project-facing alias of the canonical relative-Spec normal form. -/
theorem dualThickening_normalForm_unique
    {Y : Scheme} (sY : Y ⟶ ComplexBase) (U : Y.Opens)
    (z : RingSections (Lines.DualThickening.space sY)
      ((Lines.DualThickening.projection sY) ⁻¹ᵁ U)) :
    ∃! ab : RingSections Y U × RingSections Y U,
      z = Lines.DualThickening.normalForm sY U ab.1 ab.2 := by
  exact LeBrunSalamon.PublishedInputs.Step3f.dualThickening_normalForm_unique sY U z

end LeBrunSalamon.Construction.StandardInputs.InfinitesimalGeometry

namespace LeBrunSalamon.Construction.Lines.DualThickening

open StandardInputs.InfinitesimalGeometry

/-- The two coefficients are determined by the actual projection and
epsilon. The first is the reduction coefficient, the second the variation. -/
def coefficients {Y : Scheme} (sY : Y ⟶ ComplexBase) (U : Y.Opens)
    (z : RingSections (space sY) ((projection sY) ⁻¹ᵁ U)) :
    RingSections Y U × RingSections Y U :=
  Classical.choose (dualThickening_normalForm_unique sY U z)

def reductionCoefficient {Y : Scheme} (sY : Y ⟶ ComplexBase) (U : Y.Opens)
    (z : RingSections (space sY) ((projection sY) ⁻¹ᵁ U)) : RingSections Y U :=
  (coefficients sY U z).1

def coefficient {Y : Scheme} (sY : Y ⟶ ComplexBase) (U : Y.Opens)
    (z : RingSections (space sY) ((projection sY) ⁻¹ᵁ U)) : RingSections Y U :=
  (coefficients sY U z).2

theorem reconstruct {Y : Scheme} (sY : Y ⟶ ComplexBase) (U : Y.Opens)
    (z : RingSections (space sY) ((projection sY) ⁻¹ᵁ U)) :
    z = normalForm sY U (reductionCoefficient sY U z) (coefficient sY U z) :=
  (Classical.choose_spec (dualThickening_normalForm_unique sY U z)).1

@[simp] theorem coefficients_normalForm {Y : Scheme}
    (sY : Y ⟶ ComplexBase) (U : Y.Opens) (a b : RingSections Y U) :
    coefficients sY U (normalForm sY U a b) = (a,b) :=
  ((Classical.choose_spec (dualThickening_normalForm_unique sY U
    (normalForm sY U a b))).2 (a,b) rfl).symm

@[simp] theorem reductionCoefficient_normalForm {Y : Scheme}
    (sY : Y ⟶ ComplexBase) (U : Y.Opens) (a b : RingSections Y U) :
    reductionCoefficient sY U (normalForm sY U a b) = a := by
  simp [reductionCoefficient]

@[simp] theorem coefficient_normalForm {Y : Scheme}
    (sY : Y ⟶ ComplexBase) (U : Y.Opens) (a b : RingSections Y U) :
    coefficient sY U (normalForm sY U a b) = b := by
  simp [coefficient]

theorem coefficients_ext {Y : Scheme} (sY : Y ⟶ ComplexBase) (U : Y.Opens)
    {z w : RingSections (space sY) ((projection sY) ⁻¹ᵁ U)}
    (h₀ : reductionCoefficient sY U z = reductionCoefficient sY U w)
    (h₁ : coefficient sY U z = coefficient sY U w) : z = w := by
  rw [reconstruct sY U z, reconstruct sY U w, h₀, h₁]

theorem normalForm_zero {Y : Scheme} (sY : Y ⟶ ComplexBase) (U : Y.Opens) :
    normalForm sY U 0 0 = 0 := by simp [normalForm]

theorem normalForm_add {Y : Scheme} (sY : Y ⟶ ComplexBase) (U : Y.Opens)
    (a b c d : RingSections Y U) :
    normalForm sY U a b + normalForm sY U c d =
      normalForm sY U (a+c) (b+d) := by
  simp only [normalForm, map_add]
  ring

theorem normalForm_mul {Y : Scheme} (sY : Y ⟶ ComplexBase) (U : Y.Opens)
    (a b c d : RingSections Y U) :
    normalForm sY U a b * normalForm sY U c d =
      normalForm sY U (a*c) (a*d+c*b) := by
  simp only [normalForm, map_add, map_mul]
  ring_nf
  simp [epsilonOn_square]

@[simp] theorem coefficient_zero {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (U : Y.Opens) : coefficient sY U 0 = 0 := by
  rw [← normalForm_zero sY U]
  exact coefficient_normalForm sY U 0 0

@[simp] theorem reductionCoefficient_zero {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (U : Y.Opens) : reductionCoefficient sY U 0 = 0 := by
  rw [← normalForm_zero sY U]
  exact reductionCoefficient_normalForm sY U 0 0

theorem coefficient_add {Y : Scheme} (sY : Y ⟶ ComplexBase) (U : Y.Opens)
    (z w : RingSections (space sY) ((projection sY) ⁻¹ᵁ U)) :
    coefficient sY U (z+w) = coefficient sY U z + coefficient sY U w := by
  conv_lhs => rw [reconstruct sY U z, reconstruct sY U w, normalForm_add]
  exact coefficient_normalForm sY U _ _

theorem reductionCoefficient_add {Y : Scheme} (sY : Y ⟶ ComplexBase) (U : Y.Opens)
    (z w : RingSections (space sY) ((projection sY) ⁻¹ᵁ U)) :
    reductionCoefficient sY U (z+w) =
      reductionCoefficient sY U z + reductionCoefficient sY U w := by
  conv_lhs => rw [reconstruct sY U z, reconstruct sY U w, normalForm_add]
  exact reductionCoefficient_normalForm sY U _ _

theorem coefficient_mul {Y : Scheme} (sY : Y ⟶ ComplexBase) (U : Y.Opens)
    (z w : RingSections (space sY) ((projection sY) ⁻¹ᵁ U)) :
    coefficient sY U (z*w) =
      reductionCoefficient sY U z * coefficient sY U w +
        reductionCoefficient sY U w * coefficient sY U z := by
  conv_lhs => rw [reconstruct sY U z, reconstruct sY U w, normalForm_mul]
  exact coefficient_normalForm sY U _ _

theorem reductionCoefficient_mul {Y : Scheme} (sY : Y ⟶ ComplexBase) (U : Y.Opens)
    (z w : RingSections (space sY) ((projection sY) ⁻¹ᵁ U)) :
    reductionCoefficient sY U (z*w) =
      reductionCoefficient sY U z * reductionCoefficient sY U w := by
  conv_lhs => rw [reconstruct sY U z, reconstruct sY U w, normalForm_mul]
  exact reductionCoefficient_normalForm sY U _ _

@[simp] theorem coefficient_projection {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (U : Y.Opens) (a : RingSections Y U) :
    coefficient sY U ((projection sY).app U a) = 0 := by
  have h : normalForm sY U a 0 = (projection sY).app U a := by simp [normalForm]
  rw [← h, coefficient_normalForm]

@[simp] theorem reductionCoefficient_projection {Y : Scheme}
    (sY : Y ⟶ ComplexBase) (U : Y.Opens) (a : RingSections Y U) :
    reductionCoefficient sY U ((projection sY).app U a) = a := by
  have h : normalForm sY U a 0 = (projection sY).app U a := by simp [normalForm]
  rw [← h, reductionCoefficient_normalForm]

theorem coefficient_neg {Y : Scheme} (sY : Y ⟶ ComplexBase) (U : Y.Opens)
    (z : RingSections (space sY) ((projection sY) ⁻¹ᵁ U)) :
    coefficient sY U (-z) = -coefficient sY U z := by
  have h := coefficient_add sY U z (-z)
  rw [add_neg_cancel, coefficient_zero] at h
  calc
    coefficient sY U (-z) =
        (coefficient sY U z + coefficient sY U (-z)) - coefficient sY U z := by ring
    _ = -coefficient sY U z := by rw [← h]; simp

def coefficientAddHom {Y : Scheme} (sY : Y ⟶ ComplexBase) (U : Y.Opens) :
    RingSections (space sY) ((projection sY) ⁻¹ᵁ U) →+ RingSections Y U where
  toFun := coefficient sY U
  map_zero' := coefficient_zero sY U
  map_add' := coefficient_add sY U

/-- Epsilon restriction follows from its global definition. -/
theorem epsilonOn_restrict {Y : Scheme} (sY : Y ⟶ ComplexBase)
    {U V : Y.Opens} (i : U ⟶ V) :
    (space sY).presheaf.map
      (((TopologicalSpace.Opens.map (projection sY).base).map i).op)
      (epsilonOn sY V) = epsilonOn sY U := by
  unfold epsilonOn
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

theorem projection_restrict {Y : Scheme} (sY : Y ⟶ ComplexBase)
    {U V : Y.Opens} (i : U ⟶ V) (a : RingSections Y V) :
    (space sY).presheaf.map
      (((TopologicalSpace.Opens.map (projection sY).base).map i).op)
      ((projection sY).app V a) =
        (projection sY).app U (Y.presheaf.map i.op a) :=
  (congrArg (fun k => k a) ((projection sY).naturality i.op)).symm

theorem normalForm_restrict {Y : Scheme} (sY : Y ⟶ ComplexBase)
    {U V : Y.Opens} (i : U ⟶ V) (a b : RingSections Y V) :
    (space sY).presheaf.map
      (((TopologicalSpace.Opens.map (projection sY).base).map i).op)
      (normalForm sY V a b) =
        normalForm sY U (Y.presheaf.map i.op a) (Y.presheaf.map i.op b) := by
  simp only [normalForm, map_add, map_mul, epsilonOn_restrict, projection_restrict]

/-- Uniqueness of normal form proves restriction compatibility; this is
not an additional admitted naturality statement. -/
theorem coefficient_restrict {Y : Scheme} (sY : Y ⟶ ComplexBase)
    {U V : Y.Opens} (i : U ⟶ V)
    (z : RingSections (space sY) ((projection sY) ⁻¹ᵁ V)) :
    coefficient sY U ((space sY).presheaf.map
      (((TopologicalSpace.Opens.map (projection sY).base).map i).op) z) =
        Y.presheaf.map i.op (coefficient sY V z) := by
  conv_lhs => rw [reconstruct sY V z, normalForm_restrict, coefficient_normalForm]

theorem reductionCoefficient_restrict {Y : Scheme} (sY : Y ⟶ ComplexBase)
    {U V : Y.Opens} (i : U ⟶ V)
    (z : RingSections (space sY) ((projection sY) ⁻¹ᵁ V)) :
    reductionCoefficient sY U ((space sY).presheaf.map
      (((TopologicalSpace.Opens.map (projection sY).base).map i).op) z) =
        Y.presheaf.map i.op (reductionCoefficient sY V z) := by
  conv_lhs => rw [reconstruct sY V z, normalForm_restrict, reductionCoefficient_normalForm]

end LeBrunSalamon.Construction.Lines.DualThickening

end


/-!
## Function pullbacks for actual dual-number families

DT-01 is used only to identify underlying points and inverse-image opens.
No scheme identity `projection ≫ zeroSection = 𝟙` is asserted. The morphism
on functions remains the actual family morphism, so its epsilon coefficient
retains the deformation. Every family keeps its specified central morphism.

Unchecked continuation. Insert after the two standard dual-thickening inputs.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction

namespace LeBrunSalamon.Construction.Lines.DualThickening

/-- Compare actual function pullbacks on fixed opens without rewriting
through a proof-dependent inverse-image inclusion. -/
theorem appLE_of_map_eq {Y X : Scheme} {F G : Y ⟶ X}
    (h : F = G) (U : X.Opens) (V : Y.Opens)
    (eF : V ≤ F ⁻¹ᵁ U) (eG : V ≤ G ⁻¹ᵁ U) :
    F.appLE U V eF = G.appLE U V eG := by
  subst G
  rfl

@[simp] theorem projection_zeroSection_apply {Y : Scheme}
    (sY : Y ⟶ ComplexBase) (y : Y) :
    projection sY (zeroSection sY y) = y := by
  change (zeroSection sY ≫ projection sY) y = y
  rw [zeroSection_projection]
  rfl

/-- The reverse identity is only an identity of underlying points. -/
@[simp] theorem zeroSection_projection_apply {Y : Scheme}
    (sY : Y ⟶ ComplexBase) (y : space sY) :
    zeroSection sY (projection sY y) = y := by
  obtain ⟨x, rfl⟩ :=
    StandardInputs.InfinitesimalGeometry.dualThickening_zeroSection_surjective sY y
  rw [projection_zeroSection_apply]

@[simp] theorem zeroSection_preimage_projection {Y : Scheme}
    (sY : Y ⟶ ComplexBase) (U : Y.Opens) :
    zeroSection sY ⁻¹ᵁ (projection sY ⁻¹ᵁ U) = U := by
  change (zeroSection sY ≫ projection sY) ⁻¹ᵁ U = U
  rw [zeroSection_projection]
  rfl

/-- The family and its central map agree on underlying topological points.
Their pullbacks of functions need not agree. -/
theorem family_apply_eq_centre {Y X : Scheme} (sY : Y ⟶ ComplexBase)
    (F : space sY ⟶ X) (f : Y ⟶ X)
    (hf : zeroSection sY ≫ F = f) (y : space sY) :
    F y = f (projection sY y) := by
  have h := congrArg (fun g : Y ⟶ X => g (projection sY y)) hf
  simpa only [Scheme.Hom.comp_apply, zeroSection_projection_apply] using h

/-- The open on which the actual pullback of a function is defined is the
full inverse image of the corresponding central-map open. -/
theorem preimage_eq {Y X : Scheme} (sY : Y ⟶ ComplexBase)
    (F : space sY ⟶ X) (f : Y ⟶ X)
    (hf : zeroSection sY ≫ F = f) (V : X.Opens) :
    F ⁻¹ᵁ V = projection sY ⁻¹ᵁ (f ⁻¹ᵁ V) := by
  ext y
  change F y ∈ V ↔ f (projection sY y) ∈ V
  rw [family_apply_eq_centre sY F f hf y]

/-- The actual family pullback, on the canonical thickened central-map open.
The use of `appLE` transports only the open; it does not replace the family. -/
def functionPullback {Y X : Scheme} (sY : Y ⟶ ComplexBase)
    (F : space sY ⟶ X) (f : Y ⟶ X)
    (hf : zeroSection sY ≫ F = f) (V : X.Opens) :
    X.presheaf.obj (op V) ⟶
      (space sY).presheaf.obj (op (projection sY ⁻¹ᵁ (f ⁻¹ᵁ V))) :=
  F.appLE V (projection sY ⁻¹ᵁ (f ⁻¹ᵁ V))
    (preimage_eq sY F f hf V).ge

/-- Restriction naturality of the actual family pullback. -/
theorem functionPullback_naturality {Y X : Scheme} (sY : Y ⟶ ComplexBase)
    (F : space sY ⟶ X) (f : Y ⟶ X)
    (hf : zeroSection sY ≫ F = f) {U V : X.Opens} (i : U ⟶ V) :
    X.presheaf.map i.op ≫ functionPullback sY F f hf U =
      functionPullback sY F f hf V ≫
        (space sY).presheaf.map
          (((TopologicalSpace.Opens.map (projection sY).base).map
            ((TopologicalSpace.Opens.map f.base).map i)).op) := by
  unfold functionPullback
  rw [Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

theorem functionPullback_restrict {Y X : Scheme} (sY : Y ⟶ ComplexBase)
    (F : space sY ⟶ X) (f : Y ⟶ X)
    (hf : zeroSection sY ≫ F = f) {U V : X.Opens} (i : U ⟶ V)
    (a : RingSections X V) :
    (space sY).presheaf.map
        (((TopologicalSpace.Opens.map (projection sY).base).map
          ((TopologicalSpace.Opens.map f.base).map i)).op)
        (functionPullback sY F f hf V a) =
      functionPullback sY F f hf U (X.presheaf.map i.op a) := by
  exact (congrArg (fun q => q a)
    (functionPullback_naturality sY F f hf i)).symm

/-- Restricting the actual family to epsilon = 0 recovers the specified f.
This is a morphism identity, not a statement about underlying points. -/
theorem functionPullback_reduction {Y X : Scheme} (sY : Y ⟶ ComplexBase)
    (F : space sY ⟶ X) (f : Y ⟶ X)
    (hf : zeroSection sY ≫ F = f) (V : X.Opens) :
    functionPullback sY F f hf V ≫
        (zeroSection sY).appLE (projection sY ⁻¹ᵁ (f ⁻¹ᵁ V)) (f ⁻¹ᵁ V)
          (by rw [zeroSection_preimage_projection]) = f.app V := by
  subst f
  unfold functionPullback
  rw [Scheme.Hom.appLE_comp_appLE]
  exact Scheme.Hom.appLE_eq_app _

/-- A constant family has exactly the usual pullback through the projection.
Consequently any nonzero epsilon coefficient comes from the actual family. -/
theorem functionPullback_constant {Y X : Scheme} (sY : Y ⟶ ComplexBase)
    (f : Y ⟶ X) (V : X.Opens) :
    functionPullback sY (projection sY ≫ f) f
        (by rw [← Category.assoc, zeroSection_projection, Category.id_comp]) V =
      f.app V ≫ (projection sY).app (f ⁻¹ᵁ V) := by
  unfold functionPullback
  rw [Scheme.Hom.comp_appLE, Scheme.Hom.appLE_eq_app]

end LeBrunSalamon.Construction.Lines.DualThickening

end

/-!
## Source change of the actual infinitesimal coefficient

The source-change map is the actual base change over the same dual-number
parameter. It preserves the actual epsilon and projection. Uniqueness of the
canonical normal form therefore proves coefficient naturality. This gives the
marked-point restriction needed for vanishing of a fixed-node deformation.

Unchecked continuation. Insert after dual_thickening and dual_topology.
No new standard input or arbitrary tangent comparison is introduced.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction

namespace LeBrunSalamon.Construction.Lines.DualThickening

theorem map_projection_preimage {Y Z : Scheme}
    {sY : Y ⟶ ComplexBase} {sZ : Z ⟶ ComplexBase}
    (g : Y ⟶ Z) (hg : g ≫ sZ = sY) (U : Z.Opens) :
    map g hg ⁻¹ᵁ (projection sZ ⁻¹ᵁ U) =
      projection sY ⁻¹ᵁ (g ⁻¹ᵁ U) := by
  change (map g hg ≫ projection sZ) ⁻¹ᵁ U = (projection sY ≫ g) ⁻¹ᵁ U
  rw [map_projection]

/-- The actual pullback of functions along the base-changed source map. -/
def sourcePullback {Y Z : Scheme}
    {sY : Y ⟶ ComplexBase} {sZ : Z ⟶ ComplexBase}
    (g : Y ⟶ Z) (hg : g ≫ sZ = sY) (U : Z.Opens) :
    (space sZ).presheaf.obj (op (projection sZ ⁻¹ᵁ U)) ⟶
      (space sY).presheaf.obj (op (projection sY ⁻¹ᵁ (g ⁻¹ᵁ U))) :=
  (map g hg).appLE (projection sZ ⁻¹ᵁ U) (projection sY ⁻¹ᵁ (g ⁻¹ᵁ U))
    (map_projection_preimage g hg U).ge

theorem sourcePullback_projection {Y Z : Scheme}
    {sY : Y ⟶ ComplexBase} {sZ : Z ⟶ ComplexBase}
    (g : Y ⟶ Z) (hg : g ≫ sZ = sY) (U : Z.Opens) :
    (projection sZ).app U ≫ sourcePullback g hg U =
      g.app U ≫ (projection sY).app (g ⁻¹ᵁ U) := by
  rw [(projection sZ).app_eq_appLE]
  unfold sourcePullback
  rw [Scheme.Hom.appLE_comp_appLE]
  calc
    _ = (projection sY ≫ g).appLE U (projection sY ⁻¹ᵁ (g ⁻¹ᵁ U))
        (by rw [Scheme.Hom.comp_preimage]) :=
      appLE_of_map_eq (map_projection g hg) U _ _ _
    _ = _ := by rw [Scheme.Hom.comp_appLE, Scheme.Hom.appLE_eq_app]

theorem sourcePullback_projection_apply {Y Z : Scheme}
    {sY : Y ⟶ ComplexBase} {sZ : Z ⟶ ComplexBase}
    (g : Y ⟶ Z) (hg : g ≫ sZ = sY) (U : Z.Opens)
    (a : RingSections Z U) :
    sourcePullback g hg U ((projection sZ).app U a) =
      (projection sY).app (g ⁻¹ᵁ U) (g.app U a) :=
  congrArg (fun q => q a) (sourcePullback_projection g hg U)

/-- Source change keeps the given infinitesimal parameter, not a rescaling. -/
theorem sourcePullback_epsilon {Y Z : Scheme}
    {sY : Y ⟶ ComplexBase} {sZ : Z ⟶ ComplexBase}
    (g : Y ⟶ Z) (hg : g ≫ sZ = sY) (U : Z.Opens) :
    sourcePullback g hg U (epsilonOn sZ U) = epsilonOn sY (g ⁻¹ᵁ U) := by
  have hres : (space sZ).presheaf.map (homOfLE le_top).op ≫
      sourcePullback g hg U =
        (map g hg).appLE ⊤ (projection sY ⁻¹ᵁ (g ⁻¹ᵁ U)) (by simp) := by
    unfold sourcePullback
    rw [Scheme.Hom.map_appLE]
  have hparam : (parameter sZ).appTop ≫
      (map g hg).appLE ⊤ (projection sY ⁻¹ᵁ (g ⁻¹ᵁ U)) (by simp) =
        (parameter sY).appLE ⊤ (projection sY ⁻¹ᵁ (g ⁻¹ᵁ U)) (by simp) := by
    calc
      _ = (map g hg ≫ parameter sZ).appLE ⊤
          (projection sY ⁻¹ᵁ (g ⁻¹ᵁ U)) (by simp) := by
        simpa only [Scheme.Hom.preimage_top] using
          (Scheme.Hom.comp_appLE (map g hg) (parameter sZ) ⊤
            (projection sY ⁻¹ᵁ (g ⁻¹ᵁ U)) (by simp)).symm
      _ = _ := appLE_of_map_eq (map_parameter g hg) ⊤ _ _ _
  unfold epsilonOn
  exact (congrArg (fun q => q
    ((parameter sZ).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).inv Infinitesimal.epsilon))) hres).trans
    (congrArg (fun q => q
      ((Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).inv Infinitesimal.epsilon)) hparam)

theorem sourcePullback_normalForm {Y Z : Scheme}
    {sY : Y ⟶ ComplexBase} {sZ : Z ⟶ ComplexBase}
    (g : Y ⟶ Z) (hg : g ≫ sZ = sY) (U : Z.Opens)
    (a b : RingSections Z U) :
    sourcePullback g hg U (normalForm sZ U a b) =
      normalForm sY (g ⁻¹ᵁ U) (g.app U a) (g.app U b) := by
  simp only [normalForm, map_add, map_mul,
    sourcePullback_projection_apply, sourcePullback_epsilon]

/-- Actual coefficient naturality, derived from uniqueness of normal form. -/
theorem coefficient_sourcePullback {Y Z : Scheme}
    {sY : Y ⟶ ComplexBase} {sZ : Z ⟶ ComplexBase}
    (g : Y ⟶ Z) (hg : g ≫ sZ = sY) (U : Z.Opens)
    (z : RingSections (space sZ) (projection sZ ⁻¹ᵁ U)) :
    coefficient sY (g ⁻¹ᵁ U) (sourcePullback g hg U z) =
      g.app U (coefficient sZ U z) := by
  conv_lhs => rw [reconstruct sZ U z, sourcePullback_normalForm, coefficient_normalForm]

theorem reductionCoefficient_sourcePullback {Y Z : Scheme}
    {sY : Y ⟶ ComplexBase} {sZ : Z ⟶ ComplexBase}
    (g : Y ⟶ Z) (hg : g ≫ sZ = sY) (U : Z.Opens)
    (z : RingSections (space sZ) (projection sZ ⁻¹ᵁ U)) :
    reductionCoefficient sY (g ⁻¹ᵁ U) (sourcePullback g hg U z) =
      g.app U (reductionCoefficient sZ U z) := by
  conv_lhs => rw [reconstruct sZ U z, sourcePullback_normalForm,
    reductionCoefficient_normalForm]

/-- The changed source family has its specified, original central map. -/
theorem sourceChange_reduces {Y Z X : Scheme}
    {sY : Y ⟶ ComplexBase} {sZ : Z ⟶ ComplexBase}
    (g : Y ⟶ Z) (hg : g ≫ sZ = sY)
    (F : space sZ ⟶ X) (f : Z ⟶ X) (hf : zeroSection sZ ≫ F = f) :
    zeroSection sY ≫ (map g hg ≫ F) = g ≫ f := by
  rw [← Category.assoc, zeroSection_naturality, Category.assoc, hf]

/-- The pullback of the changed family is the composite of the two actual
function pullbacks, on the canonical thickened central-map open. -/
theorem functionPullback_sourceChange {Y Z X : Scheme}
    {sY : Y ⟶ ComplexBase} {sZ : Z ⟶ ComplexBase}
    (g : Y ⟶ Z) (hg : g ≫ sZ = sY)
    (F : space sZ ⟶ X) (f : Z ⟶ X) (hf : zeroSection sZ ≫ F = f)
    (V : X.Opens) :
    functionPullback sY (map g hg ≫ F) (g ≫ f)
        (sourceChange_reduces g hg F f hf) V =
      functionPullback sZ F f hf V ≫ sourcePullback g hg (f ⁻¹ᵁ V) := by
  unfold functionPullback sourcePullback
  rw [Scheme.Hom.appLE_comp_appLE]
  rfl

theorem functionPullback_sourceChange_apply {Y Z X : Scheme}
    {sY : Y ⟶ ComplexBase} {sZ : Z ⟶ ComplexBase}
    (g : Y ⟶ Z) (hg : g ≫ sZ = sY)
    (F : space sZ ⟶ X) (f : Z ⟶ X) (hf : zeroSection sZ ≫ F = f)
    (V : X.Opens) (a : RingSections X V) :
    functionPullback sY (map g hg ≫ F) (g ≫ f)
        (sourceChange_reduces g hg F f hf) V a =
      sourcePullback g hg (f ⁻¹ᵁ V) (functionPullback sZ F f hf V a) :=
  congrArg (fun q => q a) (functionPullback_sourceChange g hg F f hf V)

/-- Restricting the actual deformation coefficient to a source subspace
agrees with the coefficient of the actual restricted family. -/
theorem coefficient_functionPullback_sourceChange {Y Z X : Scheme}
    {sY : Y ⟶ ComplexBase} {sZ : Z ⟶ ComplexBase}
    (g : Y ⟶ Z) (hg : g ≫ sZ = sY)
    (F : space sZ ⟶ X) (f : Z ⟶ X) (hf : zeroSection sZ ≫ F = f)
    (V : X.Opens) (a : RingSections X V) :
    coefficient sY ((g ≫ f) ⁻¹ᵁ V)
        (functionPullback sY (map g hg ≫ F) (g ≫ f)
          (sourceChange_reduces g hg F f hf) V a) =
      g.app (f ⁻¹ᵁ V) (coefficient sZ (f ⁻¹ᵁ V)
        (functionPullback sZ F f hf V a)) := by
  rw [functionPullback_sourceChange_apply]
  exact coefficient_sourcePullback g hg (f ⁻¹ᵁ V)
    (functionPullback sZ F f hf V a)

end LeBrunSalamon.Construction.Lines.DualThickening

end

/-!
## Actual two-parameter first jets and the derivative of velocity

The source first jet over an arbitrary parameter algebra B is the actual
tensor product (C[z]/z²) tensor B. For B = C[epsilon]/epsilon² this is the
coordinate ring of the product of the two infinitesimal schemes. The mixed
term z*epsilon is retained and proved nonzero.

Coefficient extraction is constructed from the existing normalized dual
numbers. Its two orders agree as actual linear maps. For an actual algebra
map into the mixed jet ring satisfying the fixed-node equation, the mixed
coefficient is a point derivation. This is the affine normalization needed
to compare variation of source velocity with source differentiation of the
deformation section. It does not assert that the global Hom velocity map or
the sheaf comparison has already been constructed.

STATUS: source continuation; compilation is controlled by the 40,000-line
project gate. No new admission occurs in this fragment.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct
open CategoryTheory AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.Construction

namespace LeBrunSalamon.Construction.Lines.MixedJet

abbrev Dual := Infinitesimal.Dual

/-- The normalized coefficient of epsilon, as an actual complex linear map. -/
def dualCoefficient : Dual →ₗ[ℂ] ℂ where
  toFun := Infinitesimal.linearCoefficient
  map_add' := Infinitesimal.linearCoefficient_add
  map_smul' := by
    intro c a
    simpa using Infinitesimal.linearCoefficient_smul c a

@[simp] theorem dualCoefficient_constant (c : ℂ) :
    dualCoefficient (algebraMap ℂ Dual c) = 0 :=
  Infinitesimal.linearCoefficient_algebraMap c

@[simp] theorem dualCoefficient_one : dualCoefficient (1 : Dual) = 0 := by
  simpa using dualCoefficient_constant 1

@[simp] theorem dualCoefficient_epsilon :
    dualCoefficient Infinitesimal.epsilon = 1 := by
  simpa [dualCoefficient] using Infinitesimal.linearCoefficient_normalForm 0 1

@[simp] theorem residue_epsilon :
    Infinitesimal.residue Infinitesimal.epsilon = 0 := by
  change Polynomial.eval 0 Polynomial.X = (0 : ℂ)
  simp

theorem dualCoefficient_mul (a b : Dual) :
    dualCoefficient (a * b) = Infinitesimal.residue a * dualCoefficient b +
      Infinitesimal.residue b * dualCoefficient a :=
  Infinitesimal.linearCoefficient_mul a b

/-! ### A source first jet over any actual parameter algebra -/

section Source

variable {B : Type*} [CommRing B] [Algebra ℂ B]

-- Pin the standard tensor algebra instances before elaborating coefficient
-- maps; this keeps algebraMap and distributivity on the same ring instance.
local instance sourceJetCommRing : CommRing (Dual ⊗[ℂ] B) :=
  Algebra.TensorProduct.instCommRing

local instance sourceJetAlgebra : Algebra ℂ (Dual ⊗[ℂ] B) :=
  Algebra.TensorProduct.instAlgebra

/-- Set the source parameter z to zero, retaining the parameter algebra B. -/
def sourceZero : Dual ⊗[ℂ] B →ₐ[ℂ] B :=
  Algebra.TensorProduct.lift
    ((Algebra.ofId ℂ B).comp Infinitesimal.residue) (AlgHom.id ℂ B)
    (fun _ _ => Commute.all _ _)

/-- Extract the coefficient of the source parameter z over B. -/
def sourceDerivative : Dual ⊗[ℂ] B →ₗ[ℂ] B :=
  (TensorProduct.lid ℂ B).toLinearMap.comp
    (TensorProduct.map dualCoefficient (LinearMap.id : B →ₗ[ℂ] B))

@[simp] theorem sourceZero_tmul (a : Dual) (b : B) :
    sourceZero (a ⊗ₜ[ℂ] b) = Infinitesimal.residue a • b := by
  simp [sourceZero, Algebra.smul_def]

@[simp] theorem sourceDerivative_tmul (a : Dual) (b : B) :
    sourceDerivative (a ⊗ₜ[ℂ] b) = dualCoefficient a • b := by
  simp [sourceDerivative]

@[simp] theorem sourceZero_constant (b : B) :
    sourceZero ((1 : Dual) ⊗ₜ[ℂ] b) = b := by simp

@[simp] theorem sourceDerivative_constant (b : B) :
    sourceDerivative ((1 : Dual) ⊗ₜ[ℂ] b) = 0 := by simp

@[simp] theorem sourceZero_linear (b : B) :
    sourceZero (Infinitesimal.epsilon ⊗ₜ[ℂ] b) = 0 := by simp

@[simp] theorem sourceDerivative_linear (b : B) :
    sourceDerivative (Infinitesimal.epsilon ⊗ₜ[ℂ] b) = b := by simp

@[simp] theorem sourceDerivative_one :
    sourceDerivative (1 : Dual ⊗[ℂ] B) = 0 := by
  rw [Algebra.TensorProduct.one_def]
  simp

@[simp] theorem sourceDerivative_algebraMap (c : ℂ) :
    sourceDerivative (B := B) (algebraMap ℂ (Dual ⊗[ℂ] B) c) = 0 := by
  rw [Algebra.TensorProduct.algebraMap_apply' (R := ℂ) (A := Dual) (B := B) c]
  exact sourceDerivative_constant _

/-- The exact coefficient decomposition; no mixed terms are discarded. -/
theorem source_reconstruct (w : Dual ⊗[ℂ] B) :
    w = (1 : Dual) ⊗ₜ[ℂ] sourceZero w +
      Infinitesimal.epsilon ⊗ₜ[ℂ] sourceDerivative w := by
  induction w using TensorProduct.inductionOn with
  | tmul a b =>
    rw [sourceZero_tmul, sourceDerivative_tmul]
    have ha : a = Infinitesimal.residue a • (1 : Dual) +
        dualCoefficient a • Infinitesimal.epsilon := by
      rw [Algebra.smul_def (Infinitesimal.residue a) (1 : Dual),
        Algebra.smul_def (dualCoefficient a) Infinitesimal.epsilon]
      change a = algebraMap ℂ Dual (Infinitesimal.residue a) * 1 +
        algebraMap ℂ Dual (Infinitesimal.linearCoefficient a) * Infinitesimal.epsilon
      simpa only [mul_one, one_mul, mul_comm]
        using Infinitesimal.dual_normalForm_reconstruct a
    calc
      a ⊗ₜ[ℂ] b =
          (Infinitesimal.residue a • (1 : Dual) +
            dualCoefficient a • Infinitesimal.epsilon) ⊗ₜ[ℂ] b :=
        congrArg (fun u : Dual => u ⊗ₜ[ℂ] b) ha
      _ = (1 : Dual) ⊗ₜ[ℂ] (Infinitesimal.residue a • b) +
          Infinitesimal.epsilon ⊗ₜ[ℂ] (dualCoefficient a • b) := by
        rw [TensorProduct.add_tmul, TensorProduct.smul_tmul, TensorProduct.smul_tmul]
  | add u v hu hv =>
    calc
      u + v =
          ((1 : Dual) ⊗ₜ[ℂ] sourceZero u + Infinitesimal.epsilon ⊗ₜ[ℂ] sourceDerivative u) +
          ((1 : Dual) ⊗ₜ[ℂ] sourceZero v + Infinitesimal.epsilon ⊗ₜ[ℂ] sourceDerivative v) :=
        congrArg₂ (· + ·) hu hv
      _ = (1 : Dual) ⊗ₜ[ℂ] sourceZero (u + v) +
          Infinitesimal.epsilon ⊗ₜ[ℂ] sourceDerivative (u + v) := by
        rw [map_add, map_add, TensorProduct.tmul_add, TensorProduct.tmul_add]
        abel

/-- Equality of actual first jets is equality of their two coefficients. -/
theorem source_ext {u v : Dual ⊗[ℂ] B}
    (h0 : sourceZero u = sourceZero v)
    (h1 : sourceDerivative u = sourceDerivative v) : u = v := by
  calc
    u = (1 : Dual) ⊗ₜ[ℂ] sourceZero u +
        Infinitesimal.epsilon ⊗ₜ[ℂ] sourceDerivative u := source_reconstruct u
    _ = (1 : Dual) ⊗ₜ[ℂ] sourceZero v +
        Infinitesimal.epsilon ⊗ₜ[ℂ] sourceDerivative v := by rw [h0, h1]
    _ = v := (source_reconstruct v).symm

/-- Source differentiation satisfies Leibniz over the actual parameter ring. -/
theorem sourceDerivative_mul (u v : Dual ⊗[ℂ] B) :
    sourceDerivative (u * v) =
      sourceZero u * sourceDerivative v + sourceZero v * sourceDerivative u := by
  induction u using TensorProduct.inductionOn with
  | tmul a b =>
    induction v using TensorProduct.inductionOn with
    | tmul c d =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, sourceDerivative_tmul,
        sourceZero_tmul, dualCoefficient_mul, Algebra.smul_def, map_add, map_mul]
      ring
    | add v w hv hw =>
      rw [mul_add, map_add, hv, hw, map_add, map_add]
      ring
  | add u w hu hw =>
    rw [add_mul, map_add, hu, hw, map_add, map_add]
    ring

/-- A genuine square-zero first jet is recovered from any B-valued
derivation along its constant term; the map is on actual functions. -/
def fromDerivation {A : Type*} [CommRing A] [Algebra ℂ A]
    (f : A →ₐ[ℂ] B) (D : A →ₗ[ℂ] B)
    (hD : ∀ a b, D (a * b) = f a * D b + f b * D a) :
    A →ₐ[ℂ] (Dual ⊗[ℂ] B) where
  toFun a := (1 : Dual) ⊗ₜ[ℂ] f a + Infinitesimal.epsilon ⊗ₜ[ℂ] D a
  map_zero' := by simp
  map_one' := by
    have h1 : D 1 = 0 := by
      have h := hD 1 1
      simp only [one_mul, map_one] at h
      linear_combination -h
    simp [h1, Algebra.TensorProduct.one_def]
  map_add' := by
    intro a b
    simp only [map_add, TensorProduct.tmul_add]
    abel
  map_mul' := by
    intro a b
    apply source_ext
    · simp only [map_mul, map_add, sourceZero_constant, sourceZero_linear, add_zero]
    · simp only [sourceDerivative_mul, map_add, sourceDerivative_constant,
        sourceDerivative_linear, zero_add, sourceZero_constant, sourceZero_linear, add_zero]
      exact hD a b
  commutes' := by
    intro c
    have h1 : D 1 = 0 := by
      have h := hD 1 1
      simp only [one_mul, map_one] at h
      linear_combination -h
    have hC : D (algebraMap ℂ A c) = 0 := by
      rw [Algebra.algebraMap_eq_smul_one, map_smul, h1, smul_zero]
    simp only [hC, AlgHom.commutes, TensorProduct.tmul_zero, add_zero]
    exact (Algebra.TensorProduct.algebraMap_apply' c).symm

@[simp] theorem sourceZero_fromDerivation {A : Type*} [CommRing A] [Algebra ℂ A]
    (f : A →ₐ[ℂ] B) (D : A →ₗ[ℂ] B)
    (hD : ∀ a b, D (a * b) = f a * D b + f b * D a) (a : A) :
    sourceZero (fromDerivation f D hD a) = f a := by
  simp [fromDerivation]

@[simp] theorem sourceDerivative_fromDerivation {A : Type*}
    [CommRing A] [Algebra ℂ A] (f : A →ₐ[ℂ] B) (D : A →ₗ[ℂ] B)
    (hD : ∀ a b, D (a * b) = f a * D b + f b * D a) (a : A) :
    sourceDerivative (fromDerivation f D hD a) = D a := by
  simp [fromDerivation]

/-- Reconstruction applies to the actual pullback of target functions. -/
theorem fromDerivation_reconstruct {A : Type*} [CommRing A] [Algebra ℂ A]
    (F : A →ₐ[ℂ] (Dual ⊗[ℂ] B)) :
    fromDerivation (sourceZero.comp F)
      (sourceDerivative.comp F.toLinearMap)
      (fun a b => by simpa using sourceDerivative_mul (F a) (F b)) = F := by
  ext a
  exact (source_reconstruct (F a)).symm

/-- Actual parameter change on the tensor-product ring. -/
def parameterChange {C : Type*} [CommRing C] [Algebra ℂ C]
    (k : B →ₐ[ℂ] C) : (Dual ⊗[ℂ] B) →ₐ[ℂ] (Dual ⊗[ℂ] C) :=
  Algebra.TensorProduct.map (AlgHom.id ℂ Dual) k

@[simp] theorem parameterChange_tmul {C : Type*} [CommRing C] [Algebra ℂ C]
    (k : B →ₐ[ℂ] C) (a : Dual) (b : B) :
    parameterChange k (a ⊗ₜ[ℂ] b) = a ⊗ₜ[ℂ] k b := by
  simp [parameterChange]

/-- Source restriction commutes with the actual change of parameter algebra. -/
theorem sourceZero_parameterChange {C : Type*} [CommRing C] [Algebra ℂ C]
    (k : B →ₐ[ℂ] C) (w : Dual ⊗[ℂ] B) :
    sourceZero (parameterChange k w) = k (sourceZero w) := by
  induction w using TensorProduct.inductionOn with
  | tmul a b => simp
  | add u v hu hv => simp only [map_add, hu, hv]

/-- This is the coefficient normalization used after a tangent vector
pulls a family parameter back to the actual dual numbers. -/
theorem sourceDerivative_parameterChange {C : Type*} [CommRing C] [Algebra ℂ C]
    (k : B →ₐ[ℂ] C) (w : Dual ⊗[ℂ] B) :
    sourceDerivative (parameterChange k w) = k (sourceDerivative w) := by
  induction w using TensorProduct.inductionOn with
  | tmul a b => simp
  | add u v hu hv => simp only [map_add, hu, hv]

end Source

/-! ### The actual product of the two infinitesimal parameters -/

abbrev Mixed := Dual ⊗[ℂ] Dual

/-- Set the family parameter epsilon to zero, retaining the source first jet. -/
def parameterZero : Mixed →ₐ[ℂ] Dual :=
  Algebra.TensorProduct.lift (AlgHom.id ℂ Dual)
    ((Algebra.ofId ℂ Dual).comp Infinitesimal.residue)
    (fun _ _ => Commute.all _ _)

/-- Extract the family-parameter coefficient, as a source-first-jet function. -/
def parameterDerivative : Mixed →ₗ[ℂ] Dual :=
  (TensorProduct.rid ℂ Dual).toLinearMap.comp
    (TensorProduct.map (LinearMap.id : Dual →ₗ[ℂ] Dual) dualCoefficient)

@[simp] theorem parameterZero_tmul (a b : Dual) :
    parameterZero (a ⊗ₜ[ℂ] b) = Infinitesimal.residue b • a := by
  unfold parameterZero
  rw [Algebra.TensorProduct.lift_tmul]
  change a * algebraMap ℂ Dual (Infinitesimal.residue b) =
    Infinitesimal.residue b • a
  rw [Algebra.smul_def (Infinitesimal.residue b) a]
  exact mul_comm _ _

@[simp] theorem parameterDerivative_tmul (a b : Dual) :
    parameterDerivative (a ⊗ₜ[ℂ] b) = dualCoefficient b • a := by
  simp [parameterDerivative]

def value : Mixed →ₐ[ℂ] ℂ := Infinitesimal.residue.comp sourceZero
def sourceCoeff : Mixed →ₗ[ℂ] ℂ :=
  Infinitesimal.residue.toLinearMap.comp sourceDerivative
def parameterCoeff : Mixed →ₗ[ℂ] ℂ := dualCoefficient.comp sourceZero.toLinearMap
def mixedCoeff : Mixed →ₗ[ℂ] ℂ := dualCoefficient.comp sourceDerivative

@[simp] theorem value_tmul (a b : Dual) :
    value (a ⊗ₜ[ℂ] b) = Infinitesimal.residue a * Infinitesimal.residue b := by
  simp [value, smul_eq_mul]

@[simp] theorem sourceCoeff_tmul (a b : Dual) :
    sourceCoeff (a ⊗ₜ[ℂ] b) = dualCoefficient a * Infinitesimal.residue b := by
  simp [sourceCoeff, smul_eq_mul]

@[simp] theorem parameterCoeff_tmul (a b : Dual) :
    parameterCoeff (a ⊗ₜ[ℂ] b) = Infinitesimal.residue a * dualCoefficient b := by
  simp [parameterCoeff, smul_eq_mul]

@[simp] theorem mixedCoeff_tmul (a b : Dual) :
    mixedCoeff (a ⊗ₜ[ℂ] b) = dualCoefficient a * dualCoefficient b := by
  simp [mixedCoeff, smul_eq_mul]

/-- Both orders of taking the two first coefficients are the same actual
linear map on the full tensor-product ring. -/
theorem mixedCoeff_eq_parameterDerivative :
    mixedCoeff = dualCoefficient.comp parameterDerivative := by
  ext a b
  simp [smul_eq_mul, mul_comm]

theorem derivative_exchange (w : Mixed) :
    dualCoefficient (sourceDerivative w) =
      dualCoefficient (parameterDerivative w) :=
  LinearMap.congr_fun mixedCoeff_eq_parameterDerivative w

theorem parameterDerivative_residue (w : Mixed) :
    Infinitesimal.residue (parameterDerivative w) = parameterCoeff w := by
  have h : Infinitesimal.residue.toLinearMap.comp parameterDerivative = parameterCoeff := by
    ext a b
    simp [smul_eq_mul, mul_comm]
  exact LinearMap.congr_fun h w

theorem parameterZero_value (w : Mixed) :
    Infinitesimal.residue (parameterZero w) = value w := by
  have h : Infinitesimal.residue.comp parameterZero = value := by
    apply Algebra.TensorProduct.ext'
    intro a b
    simp [smul_eq_mul, mul_comm]
  exact AlgHom.congr_fun h w

theorem parameterZero_sourceCoeff (w : Mixed) :
    dualCoefficient (parameterZero w) = sourceCoeff w := by
  have h : dualCoefficient.comp parameterZero.toLinearMap = sourceCoeff := by
    ext a b
    simp [smul_eq_mul, mul_comm]
  exact LinearMap.congr_fun h w

/-- Four coefficients determine every two-parameter first jet. -/
theorem four_coefficients_ext {u v : Mixed}
    (h00 : value u = value v) (h10 : sourceCoeff u = sourceCoeff v)
    (h01 : parameterCoeff u = parameterCoeff v) (h11 : mixedCoeff u = mixedCoeff v) :
    u = v := by
  apply source_ext
  · calc
      sourceZero u = algebraMap ℂ Dual (value u) +
          Infinitesimal.epsilon * algebraMap ℂ Dual (parameterCoeff u) :=
        Infinitesimal.dual_normalForm_reconstruct (sourceZero u)
      _ = algebraMap ℂ Dual (value v) +
          Infinitesimal.epsilon * algebraMap ℂ Dual (parameterCoeff v) := by rw [h00, h01]
      _ = sourceZero v := (Infinitesimal.dual_normalForm_reconstruct (sourceZero v)).symm
  · calc
      sourceDerivative u = algebraMap ℂ Dual (sourceCoeff u) +
          Infinitesimal.epsilon * algebraMap ℂ Dual (mixedCoeff u) :=
        Infinitesimal.dual_normalForm_reconstruct (sourceDerivative u)
      _ = algebraMap ℂ Dual (sourceCoeff v) +
          Infinitesimal.epsilon * algebraMap ℂ Dual (mixedCoeff v) := by rw [h10, h11]
      _ = sourceDerivative v := (Infinitesimal.dual_normalForm_reconstruct (sourceDerivative v)).symm

def sourceVariable : Mixed := Infinitesimal.epsilon ⊗ₜ[ℂ] (1 : Dual)
def parameterVariable : Mixed := (1 : Dual) ⊗ₜ[ℂ] Infinitesimal.epsilon

theorem sourceVariable_square : sourceVariable ^ 2 = 0 := by
  have he : Infinitesimal.epsilon * Infinitesimal.epsilon = 0 := by
    simpa only [pow_two] using Infinitesimal.epsilon_square
  simp [sourceVariable, pow_two, Algebra.TensorProduct.tmul_mul_tmul, he]

theorem parameterVariable_square : parameterVariable ^ 2 = 0 := by
  have he : Infinitesimal.epsilon * Infinitesimal.epsilon = 0 := by
    simpa only [pow_two] using Infinitesimal.epsilon_square
  simp [parameterVariable, pow_two, Algebra.TensorProduct.tmul_mul_tmul, he]

/-- The coefficient that carries variation of velocity has not been killed. -/
theorem mixed_term_ne_zero : sourceVariable * parameterVariable ≠ 0 := by
  intro h
  have hc := congrArg mixedCoeff h
  simpa [sourceVariable, parameterVariable, Algebra.TensorProduct.tmul_mul_tmul] using hc

theorem sourceCoeff_mul (u v : Mixed) :
    sourceCoeff (u * v) = value u * sourceCoeff v + value v * sourceCoeff u := by
  change Infinitesimal.residue (sourceDerivative (u * v)) = _
  rw [sourceDerivative_mul, map_add, map_mul, map_mul]
  rfl

theorem parameterCoeff_mul (u v : Mixed) :
    parameterCoeff (u * v) = value u * parameterCoeff v + value v * parameterCoeff u := by
  change dualCoefficient (sourceZero (u * v)) = _
  rw [map_mul, dualCoefficient_mul]
  rfl

/-- The two cross terms are retained before the fixed-node equation is used. -/
theorem mixedCoeff_mul (u v : Mixed) :
    mixedCoeff (u * v) = value u * mixedCoeff v + value v * mixedCoeff u +
      sourceCoeff u * parameterCoeff v + parameterCoeff u * sourceCoeff v := by
  change dualCoefficient (sourceDerivative (u * v)) = _
  rw [sourceDerivative_mul, map_add, dualCoefficient_mul, dualCoefficient_mul]
  change value u * mixedCoeff v + sourceCoeff v * parameterCoeff u +
      (value v * mixedCoeff u + sourceCoeff u * parameterCoeff v) = _
  ring

/-! ### Actual two-parameter maps on target functions -/

section Families

variable {A : Type*} [CommRing A] [Algebra ℂ A]

def basePoint (F : A →ₐ[ℂ] Mixed) : A →ₐ[ℂ] ℂ := value.comp F

/-- The source tangent of an actual two-parameter map. -/
def sourceTangent (F : A →ₐ[ℂ] Mixed) : Infinitesimal.Tangent A (basePoint F) :=
  ⟨sourceCoeff.comp F.toLinearMap, by
    intro a b
    change sourceCoeff (F (a * b)) =
      value (F a) * sourceCoeff (F b) + value (F b) * sourceCoeff (F a)
    rw [map_mul]
    exact sourceCoeff_mul (F a) (F b)⟩

/-- The parameter tangent of an actual two-parameter map. -/
def parameterTangent (F : A →ₐ[ℂ] Mixed) : Infinitesimal.Tangent A (basePoint F) :=
  ⟨parameterCoeff.comp F.toLinearMap, by
    intro a b
    change parameterCoeff (F (a * b)) =
      value (F a) * parameterCoeff (F b) + value (F b) * parameterCoeff (F a)
    rw [map_mul]
    exact parameterCoeff_mul (F a) (F b)⟩

/-- Source velocity with its first-order dependence on the family parameter. -/
def velocityOverParameter (F : A →ₐ[ℂ] Mixed) : A →ₗ[ℂ] Dual :=
  sourceDerivative.comp F.toLinearMap

/-- Parameter deformation with its first-order dependence on the source. -/
def deformationOverSource (F : A →ₐ[ℂ] Mixed) : A →ₗ[ℂ] Dual :=
  parameterDerivative.comp F.toLinearMap

/-- The actual mixed-derivative comparison on target functions, with no
comparison equality supplied as a hypothesis. -/
theorem velocity_derivative_eq_deformation_derivative (F : A →ₐ[ℂ] Mixed) :
    dualCoefficient.comp (velocityOverParameter F) =
      dualCoefficient.comp (deformationOverSource F) := by
  ext a
  exact derivative_exchange (F a)

/-- The equation expressing that the marked point stays equal to p on
the entire dual-number parameter, not only at its reduced origin. -/
def IsFixedNode (F : A →ₐ[ℂ] Mixed) (p : A →ₐ[ℂ] ℂ) : Prop :=
  sourceZero.comp F = (Algebra.ofId ℂ Dual).comp p

theorem fixedNode_sourceZero (F : A →ₐ[ℂ] Mixed) (p : A →ₐ[ℂ] ℂ)
    (h : IsFixedNode F p) (a : A) :
    sourceZero (F a) = algebraMap ℂ Dual (p a) :=
  AlgHom.congr_fun h a

theorem fixedNode_value (F : A →ₐ[ℂ] Mixed) (p : A →ₐ[ℂ] ℂ)
    (h : IsFixedNode F p) (a : A) : value (F a) = p a := by
  change Infinitesimal.residue (sourceZero (F a)) = p a
  rw [fixedNode_sourceZero F p h]
  exact Infinitesimal.residue.commutes (p a)

theorem fixedNode_parameterCoeff_zero (F : A →ₐ[ℂ] Mixed)
    (p : A →ₐ[ℂ] ℂ) (h : IsFixedNode F p) (a : A) :
    parameterCoeff (F a) = 0 := by
  change dualCoefficient (sourceZero (F a)) = 0
  rw [fixedNode_sourceZero F p h, dualCoefficient_constant]

/-- The deformation coefficient vanishes at the fixed source marking. -/
theorem fixedNode_deformation_value_zero (F : A →ₐ[ℂ] Mixed)
    (p : A →ₐ[ℂ] ℂ) (h : IsFixedNode F p) (a : A) :
    Infinitesimal.residue (deformationOverSource F a) = 0 := by
  exact (parameterDerivative_residue (F a)).trans (fixedNode_parameterCoeff_zero F p h a)

/-- The whole dual-number family of source velocities is a derivation
along the constant marked point p. -/
theorem fixedNode_velocity_leibniz (F : A →ₐ[ℂ] Mixed)
    (p : A →ₐ[ℂ] ℂ) (h : IsFixedNode F p) (a b : A) :
    velocityOverParameter F (a * b) =
      algebraMap ℂ Dual (p a) * velocityOverParameter F b +
        algebraMap ℂ Dual (p b) * velocityOverParameter F a := by
  change sourceDerivative (F (a * b)) = _
  rw [map_mul, sourceDerivative_mul,
    fixedNode_sourceZero F p h, fixedNode_sourceZero F p h]
  rfl

/-- Variation of the actual source velocity is a genuine tangent vector
at the fixed target point. The mixed Leibniz cross terms vanish because
of the scheme-theoretic fixed-node equation. -/
def mixedTangent (F : A →ₐ[ℂ] Mixed) (p : A →ₐ[ℂ] ℂ)
    (h : IsFixedNode F p) : Infinitesimal.Tangent A p :=
  ⟨mixedCoeff.comp F.toLinearMap, by
    intro a b
    change mixedCoeff (F (a * b)) = p a * mixedCoeff (F b) + p b * mixedCoeff (F a)
    rw [map_mul, mixedCoeff_mul,
      fixedNode_value F p h, fixedNode_value F p h,
      fixedNode_parameterCoeff_zero F p h, fixedNode_parameterCoeff_zero F p h]
    ring⟩

theorem mixedTangent_apply (F : A →ₐ[ℂ] Mixed) (p : A →ₐ[ℂ] ℂ)
    (h : IsFixedNode F p) (a : A) :
    (mixedTangent F p h).val a = mixedCoeff (F a) := rfl

/-- The normalized tangent variation is the source derivative of the
actual deformation coefficient, not an independently chosen linear map. -/
theorem mixedTangent_eq_deformation_derivative (F : A →ₐ[ℂ] Mixed)
    (p : A →ₐ[ℂ] ℂ) (h : IsFixedNode F p) :
    (mixedTangent F p h).val = dualCoefficient.comp (deformationOverSource F) := by
  ext a
  exact derivative_exchange (F a)

theorem fixedNode_precompose {C : Type*} [CommRing C] [Algebra ℂ C]
    (F : A →ₐ[ℂ] Mixed) (p : A →ₐ[ℂ] ℂ) (h : IsFixedNode F p)
    (g : C →ₐ[ℂ] A) : IsFixedNode (F.comp g) (p.comp g) := by
  apply AlgHom.ext
  intro c
  exact fixedNode_sourceZero F p h (g c)

/-- The mixed tangent obeys the actual chain rule under restriction of
target coordinates or an actual target morphism. -/
theorem mixedTangent_precompose {C : Type*} [CommRing C] [Algebra ℂ C]
    (F : A →ₐ[ℂ] Mixed) (p : A →ₐ[ℂ] ℂ) (h : IsFixedNode F p)
    (g : C →ₐ[ℂ] A) :
    mixedTangent (F.comp g) (p.comp g) (fixedNode_precompose F p h g) =
      Infinitesimal.tangentMap g p (mixedTangent F p h) := by
  apply Subtype.ext
  ext c
  rfl

end Families

/-! ### Compatibility with the existing normalized dual-number tangent -/

theorem dualCoefficient_scaleDual (c : ℂ) (a : Dual) :
    dualCoefficient (Infinitesimal.scaleDual c a) = c * dualCoefficient a := by
  exact Infinitesimal.linearCoefficient_normalForm
    (Infinitesimal.residue a) (c * Infinitesimal.linearCoefficient a)

/-- Rescaling the actual parameter scales the mixed derivative. -/
theorem mixedCoeff_parameter_scale (c : ℂ) (w : Mixed) :
    mixedCoeff (parameterChange (Infinitesimal.scaleDual c) w) = c * mixedCoeff w := by
  change dualCoefficient (sourceDerivative (parameterChange (Infinitesimal.scaleDual c) w)) = _
  rw [sourceDerivative_parameterChange, dualCoefficient_scaleDual]
  rfl

/-- The coefficient obtained after pullback along an actual parameter
tangent is its action on the actual source-velocity function. -/
theorem mixedCoeff_parameter_tangent
    {B : Type*} [CommRing B] [Algebra ℂ B]
    (s : B →ₐ[ℂ] ℂ) (D : Infinitesimal.Tangent B s)
    (w : Dual ⊗[ℂ] B) :
    mixedCoeff (parameterChange (Infinitesimal.tangentToDual s D) w) =
      D.val (sourceDerivative w) := by
  change dualCoefficient
    (sourceDerivative (parameterChange (Infinitesimal.tangentToDual s D) w)) = _
  rw [sourceDerivative_parameterChange]
  exact Infinitesimal.linearCoefficient_normalForm
    (s (sourceDerivative w)) (D.val (sourceDerivative w))

/-- Functional form of the same normalization for an actual source-jet
family map. This identifies the mixed coefficient with differentiation
of its regular velocity coordinate at the actual parameter tangent. -/
theorem velocity_function_differential
    {A B : Type*} [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B]
    (F : A →ₐ[ℂ] (Dual ⊗[ℂ] B))
    (s : B →ₐ[ℂ] ℂ) (D : Infinitesimal.Tangent B s) (a : A) :
    mixedCoeff ((parameterChange (Infinitesimal.tangentToDual s D)).comp F a) =
      D.val (sourceDerivative (F a)) :=
  mixedCoeff_parameter_tangent s D (F a)

end LeBrunSalamon.Construction.Lines.MixedJet

end

/-!
## The actual affine velocity morphism and its mixed differential

An affine first-jet family is an actual algebra map A -> C[z]/z² tensor B.
Its fixed-node equation makes the z coefficient a B-valued point derivation.
The symmetric algebra of the explicit point-differential relations represents
these derivations. Thus the coefficient defines an actual morphism of affine
schemes, rather than just a pointwise assignment of vectors.

The final comparison differentiates this very morphism and identifies its
coordinate differential with the mixed coefficient of the pulled-back family.
The point-derivation representation is proved by its universal property;
identification with the global tangent-sheaf fiber is a separate geometric
comparison. No new admission is used here.

STATUS: source continuation; compile at the 40,000-line project gate.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct
open CategoryTheory AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.Construction

namespace LeBrunSalamon.Construction.Lines.AffineVelocity

section PointDifferentials

variable {A : Type} [CommRing A] [Algebra ℂ A]

/-- The actual linear relations for a derivation at the specified point.
The relation with a=b=1 also forces constants to vanish. -/
def relations (p : A →ₐ[ℂ] ℂ) : Submodule ℂ A :=
  Submodule.span ℂ (Set.range (fun ab : A × A =>
    ab.1 * ab.2 - p ab.1 • ab.2 - p ab.2 • ab.1))

abbrev PointDifferentials (p : A →ₐ[ℂ] ℂ) := A ⧸ relations p

def pointDifferential (p : A →ₐ[ℂ] ℂ) : A →ₗ[ℂ] PointDifferentials p :=
  (relations p).mkQ

theorem pointDifferential_mul (p : A →ₐ[ℂ] ℂ) (a b : A) :
    pointDifferential p (a*b) =
      p a • pointDifferential p b + p b • pointDifferential p a := by
  have hmem : a*b - p a • b - p b • a ∈ relations p :=
    Submodule.subset_span ⟨(a,b), rfl⟩
  have hz : pointDifferential p (a*b - p a • b - p b • a) = 0 :=
    (Submodule.Quotient.mk_eq_zero (relations p)).mpr hmem
  rw [map_sub, map_sub, map_smul, map_smul, sub_sub] at hz
  exact sub_eq_zero.mp hz

variable {M : Type} [AddCommGroup M] [Module ℂ M]

theorem relations_le_ker (p : A →ₐ[ℂ] ℂ) (D : A →ₗ[ℂ] M)
    (hD : ∀ a b, D (a*b) = p a • D b + p b • D a) :
    relations p ≤ LinearMap.ker D := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨a,b⟩, rfl⟩
  change D (a*b - p a • b - p b • a) = 0
  rw [map_sub, map_sub, map_smul, map_smul, hD]
  abel

/-- The unique map on point differentials induced by the actual derivation. -/
def descend (p : A →ₐ[ℂ] ℂ) (D : A →ₗ[ℂ] M)
    (hD : ∀ a b, D (a*b) = p a • D b + p b • D a) :
    PointDifferentials p →ₗ[ℂ] M :=
  (relations p).liftQ D (relations_le_ker p D hD)

@[simp] theorem descend_pointDifferential (p : A →ₐ[ℂ] ℂ)
    (D : A →ₗ[ℂ] M) (hD : ∀ a b, D (a*b) = p a • D b + p b • D a)
    (a : A) : descend p D hD (pointDifferential p a) = D a := rfl

theorem pointDifferential_surjective (p : A →ₐ[ℂ] ℂ) :
    Function.Surjective (pointDifferential p) := (relations p).mkQ_surjective

theorem descend_unique (p : A →ₐ[ℂ] ℂ) (D : A →ₗ[ℂ] M)
    (hD : ∀ a b, D (a*b) = p a • D b + p b • D a)
    (q : PointDifferentials p →ₗ[ℂ] M)
    (hq : q.comp (pointDifferential p) = D) : q = descend p D hD := by
  apply LinearMap.ext
  intro u
  obtain ⟨a, rfl⟩ := pointDifferential_surjective p u
  exact congrArg (fun k : A →ₗ[ℂ] M => k a) hq

end PointDifferentials

section RepresentingAlgebra

variable {A B : Type} [CommRing A] [Algebra ℂ A]
variable [CommRing B] [Algebra ℂ B]

/-- This is a concrete representing algebra, with all point-Leibniz
relations imposed. No independent choice of a set of vectors occurs. -/
abbrev CoordinateRing (p : A →ₐ[ℂ] ℂ) := SymmetricAlgebra ℂ (PointDifferentials p)

def coordinate (p : A →ₐ[ℂ] ℂ) : A →ₗ[ℂ] CoordinateRing p :=
  (SymmetricAlgebra.ι ℂ (PointDifferentials p)).comp (pointDifferential p)

theorem coordinate_mul (p : A →ₐ[ℂ] ℂ) (a b : A) :
    coordinate p (a*b) = p a • coordinate p b + p b • coordinate p a := by
  change SymmetricAlgebra.ι ℂ (PointDifferentials p) (pointDifferential p (a*b)) = _
  rw [pointDifferential_mul, map_add, map_smul, map_smul]
  rfl

def coordinateLift (p : A →ₐ[ℂ] ℂ) (D : A →ₗ[ℂ] B)
    (hD : ∀ a b, D (a*b) = p a • D b + p b • D a) :
    CoordinateRing p →ₐ[ℂ] B := SymmetricAlgebra.lift (descend p D hD)

@[simp] theorem coordinateLift_coordinate (p : A →ₐ[ℂ] ℂ)
    (D : A →ₗ[ℂ] B) (hD : ∀ a b, D (a*b) = p a • D b + p b • D a)
    (a : A) : coordinateLift p D hD (coordinate p a) = D a := by
  exact SymmetricAlgebra.lift_ι_apply (descend p D hD) (pointDifferential p a)

theorem coordinate_ext (p : A →ₐ[ℂ] ℂ) {q r : CoordinateRing p →ₐ[ℂ] B}
    (h : ∀ a : A, q (coordinate p a) = r (coordinate p a)) : q = r := by
  apply SymmetricAlgebra.algHom_ext
  apply LinearMap.ext
  intro u
  obtain ⟨a, rfl⟩ := pointDifferential_surjective p u
  exact h a

/-- Exact functor of points: maps from the coordinate algebra are precisely
the B-valued derivations at p. This also works for nonreduced B. -/
def derivationEquiv (p : A →ₐ[ℂ] ℂ) :
    (CoordinateRing p →ₐ[ℂ] B) ≃
      {D : A →ₗ[ℂ] B // ∀ a b, D (a*b) = p a • D b + p b • D a} where
  toFun q := ⟨q.toLinearMap.comp (coordinate p), by
    intro a b
    change q (coordinate p (a*b)) = _
    rw [coordinate_mul, map_add, map_smul, map_smul]
    rfl⟩
  invFun D := coordinateLift p D.val D.property
  left_inv q := by
    apply coordinate_ext p
    intro a
    exact coordinateLift_coordinate p _ _ a
  right_inv D := by
    apply Subtype.ext
    ext a
    exact coordinateLift_coordinate p D.val D.property a

/-- On complex points the representing algebra gives exactly the existing
point-derivation tangent space, with its original normalization. -/
def tangentPointEquiv (p : A →ₐ[ℂ] ℂ) :
    (CoordinateRing p →ₐ[ℂ] ℂ) ≃ Infinitesimal.Tangent A p where
  toFun q := ⟨q.toLinearMap.comp (coordinate p), by
    intro a b
    change q (coordinate p (a*b)) = p a * q (coordinate p b) + p b * q (coordinate p a)
    rw [coordinate_mul, map_add, map_smul, map_smul]
    rfl⟩
  invFun D := coordinateLift p D.val (by
    intro a b
    simpa only [smul_eq_mul] using D.property a b)
  left_inv q := by
    apply coordinate_ext p
    intro a
    exact coordinateLift_coordinate p _ _ a
  right_inv D := by
    apply Subtype.ext
    ext a
    exact coordinateLift_coordinate p D.val _ a

abbrev tangentScheme (p : A →ₐ[ℂ] ℂ) : Scheme :=
  Spec (CommRingCat.of (CoordinateRing p))

def tangentSchemeToC (p : A →ₐ[ℂ] ℂ) : tangentScheme p ⟶ ComplexBase :=
  DirectionCones.affineBaseMap (CoordinateRing p)

end RepresentingAlgebra

section ActualVelocity

variable {A B C : Type} [CommRing A] [Algebra ℂ A]
variable [CommRing B] [Algebra ℂ B] [CommRing C] [Algebra ℂ C]

def constantValue (p : A →ₐ[ℂ] ℂ) : A →ₐ[ℂ] B := (Algebra.ofId ℂ B).comp p

@[simp] theorem constantValue_apply (p : A →ₐ[ℂ] ℂ) (a : A) :
    (constantValue p : A →ₐ[ℂ] B) a = algebraMap ℂ B (p a) := rfl

/-- The fixed source marking is the specified constant target point as a
morphism over the entire parameter algebra, not just at complex points. -/
def IsFixedNode (F : A →ₐ[ℂ] (MixedJet.Dual ⊗[ℂ] B)) (p : A →ₐ[ℂ] ℂ) : Prop :=
  MixedJet.sourceZero.comp F = constantValue p

theorem fixedNode_apply (F : A →ₐ[ℂ] (MixedJet.Dual ⊗[ℂ] B))
    (p : A →ₐ[ℂ] ℂ) (hF : IsFixedNode F p) (a : A) :
    MixedJet.sourceZero (F a) = algebraMap ℂ B (p a) := AlgHom.congr_fun hF a

/-- Regular velocity functions, extracted from the actual first-jet map. -/
def velocityFunctions (F : A →ₐ[ℂ] (MixedJet.Dual ⊗[ℂ] B)) : A →ₗ[ℂ] B :=
  MixedJet.sourceDerivative.comp F.toLinearMap

theorem velocityFunctions_leibniz (F : A →ₐ[ℂ] (MixedJet.Dual ⊗[ℂ] B))
    (p : A →ₐ[ℂ] ℂ) (hF : IsFixedNode F p) (a b : A) :
    velocityFunctions F (a*b) =
      p a • velocityFunctions F b + p b • velocityFunctions F a := by
  change MixedJet.sourceDerivative (F (a*b)) = _
  rw [map_mul, MixedJet.sourceDerivative_mul,
    fixedNode_apply F p hF, fixedNode_apply F p hF]
  change algebraMap ℂ B (p a) * MixedJet.sourceDerivative (F b) +
      algebraMap ℂ B (p b) * MixedJet.sourceDerivative (F a) =
    p a • MixedJet.sourceDerivative (F b) + p b • MixedJet.sourceDerivative (F a)
  simp only [Algebra.smul_def]

/-- The comorphism of the velocity map is forced by its values on all
target differential coordinates. -/
def velocityComorphism (F : A →ₐ[ℂ] (MixedJet.Dual ⊗[ℂ] B))
    (p : A →ₐ[ℂ] ℂ) (hF : IsFixedNode F p) : CoordinateRing p →ₐ[ℂ] B :=
  coordinateLift p (velocityFunctions F) (velocityFunctions_leibniz F p hF)

@[simp] theorem velocityComorphism_coordinate
    (F : A →ₐ[ℂ] (MixedJet.Dual ⊗[ℂ] B))
    (p : A →ₐ[ℂ] ℂ) (hF : IsFixedNode F p) (a : A) :
    velocityComorphism F p hF (coordinate p a) = MixedJet.sourceDerivative (F a) :=
  coordinateLift_coordinate p _ _ a

/-- An actual scheme morphism of the parameter scheme to the represented
affine tangent space. Its algebraicity is built into this construction. -/
def velocityMorphism (F : A →ₐ[ℂ] (MixedJet.Dual ⊗[ℂ] B))
    (p : A →ₐ[ℂ] ℂ) (hF : IsFixedNode F p) :
    Spec (CommRingCat.of B) ⟶ tangentScheme p :=
  DirectionCones.affineMap (velocityComorphism F p hF)

theorem velocityMorphism_overC (F : A →ₐ[ℂ] (MixedJet.Dual ⊗[ℂ] B))
    (p : A →ₐ[ℂ] ℂ) (hF : IsFixedNode F p) :
    velocityMorphism F p hF ≫ tangentSchemeToC p = DirectionCones.affineBaseMap B :=
  DirectionCones.affineMap_overC (velocityComorphism F p hF)

theorem parameterChange_fixedNode (F : A →ₐ[ℂ] (MixedJet.Dual ⊗[ℂ] B))
    (p : A →ₐ[ℂ] ℂ) (hF : IsFixedNode F p) (q : B →ₐ[ℂ] C) :
    IsFixedNode ((MixedJet.parameterChange q).comp F) p := by
  apply AlgHom.ext
  intro a
  change MixedJet.sourceZero (MixedJet.parameterChange q (F a)) = algebraMap ℂ C (p a)
  rw [MixedJet.sourceZero_parameterChange, fixedNode_apply F p hF, q.commutes]

/-- Parameter base change commutes with the actual velocity comorphism. -/
theorem velocityComorphism_parameterChange
    (F : A →ₐ[ℂ] (MixedJet.Dual ⊗[ℂ] B))
    (p : A →ₐ[ℂ] ℂ) (hF : IsFixedNode F p) (q : B →ₐ[ℂ] C) :
    velocityComorphism ((MixedJet.parameterChange q).comp F) p
        (parameterChange_fixedNode F p hF q) =
      q.comp (velocityComorphism F p hF) := by
  apply coordinate_ext p
  intro a
  simp only [velocityComorphism_coordinate, AlgHom.comp_apply,
    MixedJet.sourceDerivative_parameterChange]

theorem velocityMorphism_parameterChange
    (F : A →ₐ[ℂ] (MixedJet.Dual ⊗[ℂ] B))
    (p : A →ₐ[ℂ] ℂ) (hF : IsFixedNode F p) (q : B →ₐ[ℂ] C) :
    DirectionCones.affineMap q ≫ velocityMorphism F p hF =
      velocityMorphism ((MixedJet.parameterChange q).comp F) p
        (parameterChange_fixedNode F p hF q) := by
  change Spec.map (CommRingCat.ofHom q.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (velocityComorphism F p hF).toRingHom) = _
  rw [← Spec.map_comp]
  exact congrArg (fun k : CoordinateRing p →ₐ[ℂ] C => DirectionCones.affineMap k)
    (velocityComorphism_parameterChange F p hF q).symm

/-- On each actual complex parameter point, the morphism gives the
source derivative of precisely the represented family. -/
theorem velocity_point_value (F : A →ₐ[ℂ] (MixedJet.Dual ⊗[ℂ] B))
    (p : A →ₐ[ℂ] ℂ) (hF : IsFixedNode F p) (s : B →ₐ[ℂ] ℂ) (a : A) :
    (tangentPointEquiv p (s.comp (velocityComorphism F p hF))).val a =
      s (MixedJet.sourceDerivative (F a)) := by
  change s (velocityComorphism F p hF (coordinate p a)) = _
  rw [velocityComorphism_coordinate]

end ActualVelocity

section VelocityDifferential

variable {A B : Type} [CommRing A] [Algebra ℂ A]
variable [CommRing B] [Algebra ℂ B]

/-- Canonical tangent trivialization on the represented vector space:
differentiate its linear coordinate functions. The base velocity q is kept. -/
def tangentTrivialization (p : A →ₐ[ℂ] ℂ) (q : CoordinateRing p →ₐ[ℂ] ℂ) :
    Infinitesimal.Tangent (CoordinateRing p) q →ₗ[ℂ] Infinitesimal.Tangent A p where
  toFun D := ⟨D.val.comp (coordinate p), by
    intro a b
    change D.val (coordinate p (a*b)) = p a * D.val (coordinate p b) + p b * D.val (coordinate p a)
    rw [coordinate_mul, map_add, map_smul, map_smul]
    rfl⟩
  map_add' := by intro D E; apply Subtype.ext; ext a; rfl
  map_smul' := by intro c D; apply Subtype.ext; ext a; rfl

@[simp] theorem tangentTrivialization_apply (p : A →ₐ[ℂ] ℂ)
    (q : CoordinateRing p →ₐ[ℂ] ℂ)
    (D : Infinitesimal.Tangent (CoordinateRing p) q) (a : A) :
    (tangentTrivialization p q D).val a = D.val (coordinate p a) := rfl

theorem tangentTrivialization_injective (p : A →ₐ[ℂ] ℂ)
    (q : CoordinateRing p →ₐ[ℂ] ℂ) : Function.Injective (tangentTrivialization p q) := by
  intro D E h
  apply (Infinitesimal.tangentToDual_bijective q).1
  apply Subtype.ext
  apply coordinate_ext p
  intro a
  have he : D.val (coordinate p a) = E.val (coordinate p a) :=
    congrArg (fun v : Infinitesimal.Tangent A p => v.val a) h
  change algebraMap ℂ Infinitesimal.Dual (q (coordinate p a)) +
      Infinitesimal.epsilon * algebraMap ℂ Infinitesimal.Dual (D.val (coordinate p a)) = _
  rw [he]
  rfl

/-- The actual affine scheme differential, followed by its canonical
linear-coordinate map. Neither linear map is supplied by the caller. -/
def velocityDifferential (F : A →ₐ[ℂ] (MixedJet.Dual ⊗[ℂ] B))
    (p : A →ₐ[ℂ] ℂ) (hF : IsFixedNode F p) (s : B →ₐ[ℂ] ℂ) :
    Infinitesimal.Tangent B s →ₗ[ℂ] Infinitesimal.Tangent A p :=
  (tangentTrivialization p (s.comp (velocityComorphism F p hF))).comp
    (Infinitesimal.tangentMap (velocityComorphism F p hF) s)

theorem velocityDifferential_apply (F : A →ₐ[ℂ] (MixedJet.Dual ⊗[ℂ] B))
    (p : A →ₐ[ℂ] ℂ) (hF : IsFixedNode F p) (s : B →ₐ[ℂ] ℂ)
    (D : Infinitesimal.Tangent B s) (a : A) :
    (velocityDifferential F p hF s D).val a = D.val (MixedJet.sourceDerivative (F a)) := by
  change D.val (velocityComorphism F p hF (coordinate p a)) = _
  rw [velocityComorphism_coordinate]

def parameterJet (F : A →ₐ[ℂ] (MixedJet.Dual ⊗[ℂ] B))
    (s : B →ₐ[ℂ] ℂ) (D : Infinitesimal.Tangent B s) : A →ₐ[ℂ] MixedJet.Mixed :=
  (MixedJet.parameterChange (Infinitesimal.tangentToDual s D)).comp F

theorem parameterJet_fixedNode (F : A →ₐ[ℂ] (MixedJet.Dual ⊗[ℂ] B))
    (p : A →ₐ[ℂ] ℂ) (hF : IsFixedNode F p) (s : B →ₐ[ℂ] ℂ)
    (D : Infinitesimal.Tangent B s) : MixedJet.IsFixedNode (parameterJet F s D) p :=
  parameterChange_fixedNode F p hF (Infinitesimal.tangentToDual s D)

/-- The derivative of the constructed scheme velocity morphism is the
mixed coefficient of the actual family pulled back along D. -/
theorem velocityDifferential_eq_mixedTangent
    (F : A →ₐ[ℂ] (MixedJet.Dual ⊗[ℂ] B))
    (p : A →ₐ[ℂ] ℂ) (hF : IsFixedNode F p) (s : B →ₐ[ℂ] ℂ)
    (D : Infinitesimal.Tangent B s) :
    velocityDifferential F p hF s D =
      MixedJet.mixedTangent (parameterJet F s D) p (parameterJet_fixedNode F p hF s D) := by
  apply Subtype.ext
  ext a
  exact (velocityDifferential_apply F p hF s D a).trans
    (MixedJet.velocity_function_differential F s D a).symm

/-- The same actual differential is source differentiation of the
deformation coefficient. This is the required mixed-derivative exchange. -/
theorem velocityDifferential_eq_deformationDerivative
    (F : A →ₐ[ℂ] (MixedJet.Dual ⊗[ℂ] B))
    (p : A →ₐ[ℂ] ℂ) (hF : IsFixedNode F p) (s : B →ₐ[ℂ] ℂ)
    (D : Infinitesimal.Tangent B s) :
    (velocityDifferential F p hF s D).val =
      MixedJet.dualCoefficient.comp (MixedJet.deformationOverSource (parameterJet F s D)) := by
  rw [velocityDifferential_eq_mixedTangent]
  exact MixedJet.mixedTangent_eq_deformation_derivative
    (parameterJet F s D) p (parameterJet_fixedNode F p hF s D)

end VelocityDifferential

end LeBrunSalamon.Construction.Lines.AffineVelocity

end

/-!
## The canonical tangent trivialization is an actual linear equivalence

The represented affine tangent space is the spectrum of the symmetric
algebra of the explicit point differentials. At any actual point q, an
arbitrary tangent vector at p defines a dual-number point by translating
the linear generators of q. The existing dual-number/derivation bijection
then proves surjectivity of the actual tangentTrivialization.

This also shows that surjectivity of the constructed velocityDifferential
is exactly surjectivity of the actual affine scheme differential before
trivialization. No assumed identification of tangent spaces is used.

STATUS: source continuation; compilation follows the 40,000-line gate.
No new admission occurs in this fragment.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct
open LeBrunSalamon.Construction

namespace LeBrunSalamon.Construction.Lines.AffineVelocity

section CanonicalTangentEquivalence

variable {A : Type} [CommRing A] [Algebra ℂ A]

/-- Translate each actual linear coordinate of q by epsilon times the
specified point derivation, descended through the point-Leibniz relations. -/
def infinitesimalTranslationGenerator (p : A →ₐ[ℂ] ℂ)
    (q : CoordinateRing p →ₐ[ℂ] ℂ) (w : Infinitesimal.Tangent A p) :
    PointDifferentials p →ₗ[ℂ] Infinitesimal.Dual :=
  (Algebra.ofId ℂ Infinitesimal.Dual).toLinearMap.comp
      (q.toLinearMap.comp (SymmetricAlgebra.ι ℂ (PointDifferentials p))) +
    (LinearMap.mul ℂ Infinitesimal.Dual Infinitesimal.epsilon).comp
      ((Algebra.ofId ℂ Infinitesimal.Dual).toLinearMap.comp
        (descend p w.val (by
          intro a b
          simpa only [smul_eq_mul] using w.property a b)))

/-- The actual dual-number algebra point of the representing scheme. -/
def infinitesimalTranslation (p : A →ₐ[ℂ] ℂ)
    (q : CoordinateRing p →ₐ[ℂ] ℂ) (w : Infinitesimal.Tangent A p) :
    CoordinateRing p →ₐ[ℂ] Infinitesimal.Dual :=
  SymmetricAlgebra.lift (infinitesimalTranslationGenerator p q w)

theorem infinitesimalTranslation_coordinate (p : A →ₐ[ℂ] ℂ)
    (q : CoordinateRing p →ₐ[ℂ] ℂ) (w : Infinitesimal.Tangent A p) (a : A) :
    infinitesimalTranslation p q w (coordinate p a) =
      algebraMap ℂ Infinitesimal.Dual (q (coordinate p a)) +
        Infinitesimal.epsilon * algebraMap ℂ Infinitesimal.Dual (w.val a) := by
  change SymmetricAlgebra.lift (infinitesimalTranslationGenerator p q w)
    (SymmetricAlgebra.ι ℂ (PointDifferentials p) (pointDifferential p a)) = _
  rw [SymmetricAlgebra.lift_ι_apply]
  rfl

/-- The translated infinitesimal point has precisely the original q as
its reduced point. The equality is an equality of algebra morphisms. -/
theorem infinitesimalTranslation_residue (p : A →ₐ[ℂ] ℂ)
    (q : CoordinateRing p →ₐ[ℂ] ℂ) (w : Infinitesimal.Tangent A p) :
    Infinitesimal.residue.comp (infinitesimalTranslation p q w) = q := by
  apply coordinate_ext p
  intro a
  change Infinitesimal.residue
    (infinitesimalTranslation p q w (coordinate p a)) = q (coordinate p a)
  rw [infinitesimalTranslation_coordinate]
  exact Infinitesimal.residue_normalForm _ _

/-- Every point derivation at p is the differential of an actual
dual-number point at q of the represented affine tangent scheme. -/
theorem tangentTrivialization_surjective (p : A →ₐ[ℂ] ℂ)
    (q : CoordinateRing p →ₐ[ℂ] ℂ) :
    Function.Surjective (tangentTrivialization p q) := by
  intro w
  let lift : {f : CoordinateRing p →ₐ[ℂ] Infinitesimal.Dual //
      Infinitesimal.residue.comp f = q} :=
    ⟨infinitesimalTranslation p q w, infinitesimalTranslation_residue p q w⟩
  obtain ⟨D, hD⟩ := (Infinitesimal.tangentToDual_bijective q).2 lift
  refine ⟨D, ?_⟩
  apply Subtype.ext
  ext a
  have hc := congrArg
    (fun f : {f : CoordinateRing p →ₐ[ℂ] Infinitesimal.Dual //
      Infinitesimal.residue.comp f = q} =>
        Infinitesimal.linearCoefficient (f.val (coordinate p a))) hD
  change Infinitesimal.linearCoefficient
      (algebraMap ℂ Infinitesimal.Dual (q (coordinate p a)) +
        Infinitesimal.epsilon * algebraMap ℂ Infinitesimal.Dual (D.val (coordinate p a))) =
    Infinitesimal.linearCoefficient (infinitesimalTranslation p q w (coordinate p a)) at hc
  rw [infinitesimalTranslation_coordinate,
    Infinitesimal.linearCoefficient_normalForm,
    Infinitesimal.linearCoefficient_normalForm] at hc
  exact hc

/-- Canonical linear trivialization of the tangent space at q of the
actual represented affine vector space. -/
def tangentTrivializationEquiv (p : A →ₐ[ℂ] ℂ)
    (q : CoordinateRing p →ₐ[ℂ] ℂ) :
    Infinitesimal.Tangent (CoordinateRing p) q ≃ₗ[ℂ] Infinitesimal.Tangent A p :=
  LinearEquiv.ofBijective (tangentTrivialization p q)
    ⟨tangentTrivialization_injective p q, tangentTrivialization_surjective p q⟩

@[simp] theorem tangentTrivializationEquiv_apply (p : A →ₐ[ℂ] ℂ)
    (q : CoordinateRing p →ₐ[ℂ] ℂ)
    (D : Infinitesimal.Tangent (CoordinateRing p) q) :
    tangentTrivializationEquiv p q D = tangentTrivialization p q D := rfl

/-- The inverse equivalence has the prescribed actual infinitesimal
translation on every target coordinate, not merely an abstract inverse. -/
theorem tangentTrivializationEquiv_symm_normalized (p : A →ₐ[ℂ] ℂ)
    (q : CoordinateRing p →ₐ[ℂ] ℂ) (w : Infinitesimal.Tangent A p) :
    Infinitesimal.tangentToDual q ((tangentTrivializationEquiv p q).symm w) =
      infinitesimalTranslation p q w := by
  apply coordinate_ext p
  intro a
  have hc : ((tangentTrivializationEquiv p q).symm w).val (coordinate p a) = w.val a :=
    congrArg (fun v : Infinitesimal.Tangent A p => v.val a)
      ((tangentTrivializationEquiv p q).apply_symm_apply w)
  change algebraMap ℂ Infinitesimal.Dual (q (coordinate p a)) +
    Infinitesimal.epsilon * algebraMap ℂ Infinitesimal.Dual
      (((tangentTrivializationEquiv p q).symm w).val (coordinate p a)) = _
  rw [hc, infinitesimalTranslation_coordinate]

end CanonicalTangentEquivalence

section ActualSchemeDifferential

variable {A B : Type} [CommRing A] [Algebra ℂ A]
variable [CommRing B] [Algebra ℂ B]

/-- The previously constructed differential is composed with this proved
linear equivalence, preserving its original parameter point and morphism. -/
theorem velocityDifferential_eq_equiv_comp
    (F : A →ₐ[ℂ] (MixedJet.Dual ⊗[ℂ] B))
    (p : A →ₐ[ℂ] ℂ) (hF : IsFixedNode F p) (s : B →ₐ[ℂ] ℂ) :
    velocityDifferential F p hF s =
      (tangentTrivializationEquiv p (s.comp (velocityComorphism F p hF))).toLinearMap.comp
        (Infinitesimal.tangentMap (velocityComorphism F p hF) s) := rfl

/-- Surjectivity after the normalized tangent identification is exactly
surjectivity of the actual affine scheme differential. This is the
comparison needed before applying generic smoothness to velocity maps. -/
theorem velocityDifferential_surjective_iff
    (F : A →ₐ[ℂ] (MixedJet.Dual ⊗[ℂ] B))
    (p : A →ₐ[ℂ] ℂ) (hF : IsFixedNode F p) (s : B →ₐ[ℂ] ℂ) :
    Function.Surjective (velocityDifferential F p hF s) ↔
      Function.Surjective (Infinitesimal.tangentMap (velocityComorphism F p hF) s) := by
  constructor
  · intro h v
    obtain ⟨D, hD⟩ := h (tangentTrivialization p (s.comp (velocityComorphism F p hF)) v)
    refine ⟨D, ?_⟩
    exact tangentTrivialization_injective p (s.comp (velocityComorphism F p hF)) hD
  · intro h
    exact (tangentTrivialization_surjective p (s.comp (velocityComorphism F p hF))).comp h

end ActualSchemeDifferential

end LeBrunSalamon.Construction.Lines.AffineVelocity

end

/-!
## The actual infinitesimal section of a specified family

The epsilon coefficient is extracted from the actual pullback of target
functions, on the full inverse-image open. It produces an actual relative
derivation, an actual map from pulled-back cotangent sheaves, and then a
section of the original pulled-back tangent bundle using its normalized
dual-base-change morphism. The central curve remains an explicit morphism.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirty
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction

namespace LeBrunSalamon.Construction.Lines.DualThickening

/-- The actual zero-section pullback on functions of a thickened open. -/
def reductionHom {Y : Scheme} (sY : Y ⟶ ComplexBase) (U : Y.Opens) :
    (space sY).presheaf.obj (op ((projection sY) ⁻¹ᵁ U)) ⟶ Y.presheaf.obj (op U) :=
  (zeroSection sY).appLE ((projection sY) ⁻¹ᵁ U) U
    (by rw [zeroSection_preimage_projection])

theorem reductionHom_projection {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (U : Y.Opens) (a : RingSections Y U) :
    reductionHom sY U ((projection sY).app U a) = a := by
  have h : (projection sY).app U ≫ reductionHom sY U = 𝟙 (Y.presheaf.obj (op U)) := by
    rw [(projection sY).app_eq_appLE]
    unfold reductionHom
    rw [Scheme.Hom.appLE_comp_appLE]
    rw [appLE_of_map_eq (zeroSection_projection sY) U U _ (by simp)]
    simp [Scheme.Hom.appLE]
    exact Y.presheaf.map_id (op U)
  exact congrArg (fun k : Y.presheaf.obj (op U) ⟶ Y.presheaf.obj (op U) => k a) h

theorem origin_epsilon :
    Infinitesimal.origin.appTop
      ((Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).inv Infinitesimal.epsilon) = 0 := by
  have h := congrArg (fun k : CommRingCat.of Infinitesimal.Dual ⟶
      (Spec (CommRingCat.of ℂ)).presheaf.obj (op ⊤) => k Infinitesimal.epsilon)
    (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom Infinitesimal.residue.toRingHom))
  have he : Infinitesimal.residue Infinitesimal.epsilon = 0 := by
    change Polynomial.eval 0 Polynomial.X = (0 : ℂ)
    simp
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv
    (Infinitesimal.residue Infinitesimal.epsilon) = _ at h
  rw [he, map_zero] at h
  exact h.symm

/-- The actual epsilon section vanishes on the actual zero section. -/
theorem reductionHom_epsilon {Y : Scheme} (sY : Y ⟶ ComplexBase) (U : Y.Opens) :
    reductionHom sY U (epsilonOn sY U) = 0 := by
  have hres : (space sY).presheaf.map (homOfLE le_top).op ≫ reductionHom sY U =
      (zeroSection sY).appLE ⊤ U (by simp) := by
    unfold reductionHom
    rw [Scheme.Hom.map_appLE]
  have hcomp : (parameter sY).appTop ≫ (zeroSection sY).appLE ⊤ U (by simp) =
      (zeroSection sY ≫ parameter sY).appLE ⊤ U (by simp) := by
    simpa only [Scheme.Hom.preimage_top] using
      (Scheme.Hom.comp_appLE (zeroSection sY) (parameter sY) ⊤ U (by simp)).symm
  have hz : (zeroSection sY ≫ parameter sY).appLE ⊤ U (by simp)
      ((Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).inv Infinitesimal.epsilon) = 0 := by
    rw [appLE_of_map_eq (zeroSection_parameter sY) ⊤ U _ (by simp),
      Scheme.Hom.comp_appLE]
    change (sY.appLE ⊤ U (by simp))
      (Infinitesimal.origin.appTop
        ((Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).inv Infinitesimal.epsilon)) = 0
    rw [origin_epsilon, map_zero]
  unfold epsilonOn
  exact (congrArg (fun k => k
    ((parameter sY).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).inv Infinitesimal.epsilon))) hres).trans
    ((congrArg (fun k => k
      ((Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).inv Infinitesimal.epsilon)) hcomp).trans hz)

theorem reductionHom_normalForm {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (U : Y.Opens) (a b : RingSections Y U) :
    reductionHom sY U (normalForm sY U a b) = a := by
  simp only [normalForm, map_add, map_mul, reductionHom_projection,
    reductionHom_epsilon, zero_mul, add_zero]

/-- The algebraic constant coefficient is exactly scheme-theoretic reduction. -/
theorem reductionCoefficient_eq_reductionHom {Y : Scheme}
    (sY : Y ⟶ ComplexBase) (U : Y.Opens)
    (z : RingSections (space sY) ((projection sY) ⁻¹ᵁ U)) :
    reductionCoefficient sY U z = reductionHom sY U z := by
  conv_rhs => rw [reconstruct sY U z, reductionHom_normalForm]

theorem reductionCoefficient_functionPullback {Y X : Scheme}
    (sY : Y ⟶ ComplexBase) (F : space sY ⟶ X) (f : Y ⟶ X)
    (hf : zeroSection sY ≫ F = f) (V : X.Opens) (a : RingSections X V) :
    reductionCoefficient sY (f ⁻¹ᵁ V) (functionPullback sY F f hf V a) = f.app V a := by
  rw [reductionCoefficient_eq_reductionHom]
  exact congrArg (fun k => k a) (functionPullback_reduction sY F f hf V)

/-- Composition on the target acts by the actual pullback of functions.
The inverse-image open is kept at the specified central morphism. -/
theorem functionPullback_postcompose {Y X Z : Scheme}
    (sY : Y ⟶ ComplexBase) (F : space sY ⟶ X) (f : Y ⟶ X)
    (hf : zeroSection sY ≫ F = f) (g : X ⟶ Z) (W : Z.Opens) :
    functionPullback sY (F ≫ g) (f ≫ g)
        (by rw [← Category.assoc, hf]) W =
      g.app W ≫ functionPullback sY F f hf (g ⁻¹ᵁ W) := by
  unfold functionPullback
  rw [Scheme.Hom.comp_appLE]
  rfl

/-- Equality of actual family maps preserves the normalized function
pullback, with the central morphism and its inverse-image open fixed. -/
theorem functionPullback_of_map_eq {Y X : Scheme} (sY : Y ⟶ ComplexBase)
    {F G : space sY ⟶ X} (h : F = G) (f : Y ⟶ X)
    (hf : zeroSection sY ≫ F = f) (hg : zeroSection sY ≫ G = f) (V : X.Opens) :
    functionPullback sY F f hf V = functionPullback sY G f hg V := by
  subst G
  rfl

end LeBrunSalamon.Construction.Lines.DualThickening

namespace LeBrunSalamon.Construction.Lines.FamilyVariation

open DualThickening

theorem relativeDerivation_ext {T S : Scheme} {s : T ⟶ S}
    {E : OModule T} {D₁ D₂ : RelativeSheafDerivation s E}
    (h : ∀ (U : T.Opens) (a : RingSections T U), D₁.apply U a = D₂.apply U a) :
    D₁ = D₂ := by
  cases D₁ with
  | mk d₁ z₁ a₁ l₁ n₁ b₁ =>
    cases D₂ with
    | mk d₂ z₂ a₂ l₂ n₂ b₂ =>
      have hd : d₁ = d₂ := funext (fun U => funext (fun a => h U a))
      subst d₂
      rfl

/-- Only geometric data: an actual first-order family with its actual
central morphism. No tangent comparison or positive-space property is a field. -/
structure Deformation {Y X : Scheme} (sY : Y ⟶ ComplexBase)
    (sX : X ⟶ ComplexBase) (f : Y ⟶ X) where
  map : DualThickening.space sY ⟶ X
  overC : map ≫ sX = DualThickening.toC sY
  reduces : DualThickening.zeroSection sY ≫ map = f

theorem Deformation.centre_overC {Y X : Scheme}
    {sY : Y ⟶ ComplexBase} {sX : X ⟶ ComplexBase} {f : Y ⟶ X}
    (D : Deformation sY sX f) : f ≫ sX = sY := by
  rw [← D.reduces, Category.assoc, D.overC, DualThickening.zeroSection_overC]

/-- The constant first-order family is constructed directly; it does not
use the historical admitted origin-over-C wrapper. -/
def constant {Y X : Scheme} {sY : Y ⟶ ComplexBase} {sX : X ⟶ ComplexBase}
    (f : Y ⟶ X) (hf : f ≫ sX = sY) : Deformation sY sX f where
  map := DualThickening.projection sY ≫ f
  overC := by rw [Category.assoc, hf]; rfl
  reduces := by simp only [← Category.assoc, DualThickening.zeroSection_projection,
    Category.id_comp]

/-- The variation on a target function is the normalized epsilon coefficient
of its actual family pullback, on the full central inverse-image open. -/
def Deformation.onFunction {Y X : Scheme}
    {sY : Y ⟶ ComplexBase} {sX : X ⟶ ComplexBase} {f : Y ⟶ X}
    (D : Deformation sY sX f) (V : X.Opens) (a : RingSections X V) :
    RingSections Y (f ⁻¹ᵁ V) :=
  coefficient sY (f ⁻¹ᵁ V) (functionPullback sY D.map f D.reduces V a)

theorem Deformation.onFunction_zero {Y X : Scheme}
    {sY : Y ⟶ ComplexBase} {sX : X ⟶ ComplexBase} {f : Y ⟶ X}
    (D : Deformation sY sX f) (V : X.Opens) : D.onFunction V 0 = 0 := by
  simp [Deformation.onFunction]

theorem Deformation.onFunction_add {Y X : Scheme}
    {sY : Y ⟶ ComplexBase} {sX : X ⟶ ComplexBase} {f : Y ⟶ X}
    (D : Deformation sY sX f) (V : X.Opens) (a b : RingSections X V) :
    D.onFunction V (a+b) = D.onFunction V a + D.onFunction V b := by
  simp only [Deformation.onFunction, map_add, coefficient_add]

theorem Deformation.onFunction_leibniz {Y X : Scheme}
    {sY : Y ⟶ ComplexBase} {sX : X ⟶ ComplexBase} {f : Y ⟶ X}
    (D : Deformation sY sX f) (V : X.Opens) (a b : RingSections X V) :
    D.onFunction V (a*b) = f.app V a * D.onFunction V b +
      f.app V b * D.onFunction V a := by
  simp only [Deformation.onFunction, map_mul, coefficient_mul,
    reductionCoefficient_functionPullback]

theorem Deformation.onFunction_restrict {Y X : Scheme}
    {sY : Y ⟶ ComplexBase} {sX : X ⟶ ComplexBase} {f : Y ⟶ X}
    (D : Deformation sY sX f) {U V : X.Opens} (i : U ⟶ V)
    (a : RingSections X V) :
    Y.presheaf.map (((TopologicalSpace.Opens.map f.base).map i).op)
      (D.onFunction V a) = D.onFunction U (X.presheaf.map i.op a) := by
  unfold Deformation.onFunction
  rw [← coefficient_restrict, functionPullback_restrict]

theorem constant_onFunction {Y X : Scheme}
    {sY : Y ⟶ ComplexBase} {sX : X ⟶ ComplexBase}
    (f : Y ⟶ X) (hf : f ≫ sX = sY) (V : X.Opens) (a : RingSections X V) :
    (constant f hf).onFunction V a = 0 := by
  unfold Deformation.onFunction constant
  rw [functionPullback_constant]
  exact coefficient_projection sY (f ⁻¹ᵁ V) (f.app V a)

/-- Because the family is over C, every actual base function is constant
in the deformation parameter. This is the relative, rather than absolute,
derivation condition. -/
theorem Deformation.onFunction_killsBase {Y X : Scheme}
    {sY : Y ⟶ ComplexBase} {sX : X ⟶ ComplexBase} {f : Y ⟶ X}
    (D : Deformation sY sX f) (W : ComplexBase.Opens)
    (a : RingSections ComplexBase W) :
    D.onFunction (sX ⁻¹ᵁ W) (sX.app W a) = 0 := by
  have hbase : D.map ≫ sX = projection sY ≫ (f ≫ sX) := by
    rw [D.centre_overC]
    exact D.overC
  have hp : sX.app W ≫ functionPullback sY D.map f D.reduces (sX ⁻¹ᵁ W) =
      (f ≫ sX).app W ≫ (projection sY).app ((f ≫ sX) ⁻¹ᵁ W) := by
    have hnorm := functionPullback_of_map_eq sY hbase (f ≫ sX)
      (by rw [← Category.assoc, D.reduces])
      (by rw [← Category.assoc, zeroSection_projection, Category.id_comp]) W
    exact (functionPullback_postcompose sY D.map f D.reduces sX W).symm.trans
      (hnorm.trans (functionPullback_constant sY (f ≫ sX) W))
  unfold Deformation.onFunction
  have ha := congrArg (fun k => k a) hp
  change coefficient sY ((f ≫ sX) ⁻¹ᵁ W)
    ((sX.app W ≫ functionPullback sY D.map f D.reduces (sX ⁻¹ᵁ W)) a) = 0
  rw [ha]
  exact coefficient_projection sY ((f ≫ sX) ⁻¹ᵁ W) ((f ≫ sX).app W a)

/-- The actual variation on functions, assembled on every target open.
Its target is f_*O_Y with the genuine f-induced scalar action. -/
def Deformation.derivation {Y X : Scheme}
    {sY : Y ⟶ ComplexBase} {sX : X ⟶ ComplexBase} {f : Y ⟶ X}
    (D : Deformation sY sX f) :
    RelativeSheafDerivation sX ((Scheme.Modules.pushforward f).obj (structureModule Y)) where
  apply := D.onFunction
  zero := D.onFunction_zero
  add := D.onFunction_add
  leibniz := by
    intro V a b
    exact D.onFunction_leibniz V a b
  naturality := D.onFunction_restrict
  killsBase := D.onFunction_killsBase

/-- The normalized cotangent functional of the actual family. It is
constructed through the universal derivation and the actual pullback
adjunction; no tangent-comparison existence theorem is used. -/
def Deformation.cotangentHom {Y X : Scheme}
    {sY : Y ⟶ ComplexBase} {sX : X ⟶ ComplexBase} {f : Y ⟶ X}
    (D : Deformation sY sX f) :
    pullbackModule f (cotangentSheaf sX) ⟶ structureModule Y :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm
    (differentialLift D.derivation)

theorem Deformation.cotangentHom_adjoint {Y X : Scheme}
    {sY : Y ⟶ ComplexBase} {sX : X ⟶ ComplexBase} {f : Y ⟶ X}
    (D : Deformation sY sX f) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ D.cotangentHom =
      differentialLift D.derivation := by
  exact ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).apply_symm_apply _

/-- The defining normalization on a genuine local differential da.
This equality prevents changing the family variation by an arbitrary
automorphism of the pulled-back tangent bundle. -/
theorem Deformation.cotangentHom_differential {Y X : Scheme}
    {sY : Y ⟶ ComplexBase} {sX : X ⟶ ComplexBase} {f : Y ⟶ X}
    (D : Deformation sY sX f) (V : X.Opens) (a : RingSections X V) :
    D.cotangentHom.app (f ⁻¹ᵁ V)
      (pullLocalSection f (cotangentSheaf sX) V
        ((cotangentPresentation sX).differential.apply V a)) = D.onFunction V a := by
  have h := congrArg (fun q : RelativeSheafDerivation sX
      ((Scheme.Modules.pushforward f).obj (structureModule Y)) => q.apply V a)
    (differentialLift_spec D.derivation)
  rw [← D.cotangentHom_adjoint] at h
  exact h

/-- Cotangent functionals are determined by their values on actual local
differentials. This is the universal property, with no affine cover chosen. -/
theorem Deformation.cotangentHom_unique {Y X : Scheme}
    {sY : Y ⟶ ComplexBase} {sX : X ⟶ ComplexBase} {f : Y ⟶ X}
    (D : Deformation sY sX f)
    (h : pullbackModule f (cotangentSheaf sX) ⟶ structureModule Y)
    (hh : ∀ (V : X.Opens) (a : RingSections X V),
      h.app (f ⁻¹ᵁ V) (pullLocalSection f (cotangentSheaf sX) V
        ((cotangentPresentation sX).differential.apply V a)) = D.onFunction V a) :
    h = D.cotangentHom := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  rw [D.cotangentHom_adjoint]
  apply differentialLift_unique
  apply relativeDerivation_ext
  intro V a
  exact hh V a

theorem constant_cotangentHom {Y X : Scheme}
    {sY : Y ⟶ ComplexBase} {sX : X ⟶ ComplexBase}
    (f : Y ⟶ X) (hf : f ≫ sX = sY) :
    (constant f hf).cotangentHom = 0 := by
  symm
  apply (constant f hf).cotangentHom_unique
  intro V a
  change (0 : RingSections Y (f ⁻¹ᵁ V)) = _
  exact (constant_onFunction f hf V a).symm

/-- The actual family section in the original pulled-back tangent sheaf.
The only dual transport is the canonical map normalized by evaluation. -/
def Deformation.section {Y : Scheme} {d : ℕ}
    (X : SmoothProperComplexVariety d) {sY : Y ⟶ ComplexBase}
    {f : Y ⟶ X.scheme} (D : Deformation sY X.structureMap f) :
    AlgebraicSection (pullbackModule f (tangentSheaf X.structureMap)) := by
  letI := dualBaseChange_isIso f (smooth_cotangent_rank X.structureMap d X.smooth)
  exact TwoChartSections.homSection D.cotangentHom ≫
    (asIso (dualBaseChange f (cotangentSheaf X.structureMap))).inv

/-- Global-section form of the actual infinitesimal variation. -/
def Deformation.variation {Y : Scheme} {d : ℕ}
    (X : SmoothProperComplexVariety d) {sY : Y ⟶ ComplexBase}
    {f : Y ⟶ X.scheme} (D : Deformation sY X.structureMap f) :
    CSections sY (pullbackModule f (tangentSheaf X.structureMap)) :=
  sectionValue (D.section X)

theorem Deformation.section_normalized {Y : Scheme} {d : ℕ}
    (X : SmoothProperComplexVariety d) {sY : Y ⟶ ComplexBase}
    {f : Y ⟶ X.scheme} (D : Deformation sY X.structureMap f) :
    D.section X ≫ dualBaseChange f (cotangentSheaf X.structureMap) =
      TwoChartSections.homSection D.cotangentHom := by
  letI := dualBaseChange_isIso f (smooth_cotangent_rank X.structureMap d X.smooth)
  change TwoChartSections.homSection D.cotangentHom ≫
    (asIso (dualBaseChange f (cotangentSheaf X.structureMap))).inv ≫
      (asIso (dualBaseChange f (cotangentSheaf X.structureMap))).hom = _
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Converting the actual variation back through the normalized Hom
identification recovers the very cotangent functional of the family. -/
theorem Deformation.variation_normalized {Y : Scheme} {d : ℕ}
    (X : SmoothProperComplexVariety d) {sY : Y ⟶ ComplexBase}
    {f : Y ⟶ X.scheme} (D : Deformation sY X.structureMap f) :
    TwoChartSections.internalHomSectionAddEquiv _ _
      (sectionFromValue (D.variation X) ≫
        dualBaseChange f (cotangentSheaf X.structureMap)) = D.cotangentHom := by
  have hs : sectionFromValue (D.variation X) = D.section X :=
    (sectionEquiv _).symm_apply_apply (D.section X)
  rw [hs, D.section_normalized, TwoChartSections.internalHomSectionAddEquiv_homSection]

theorem constant_section {Y : Scheme} {d : ℕ}
    (X : SmoothProperComplexVariety d) {sY : Y ⟶ ComplexBase}
    (f : Y ⟶ X.scheme) (hf : f ≫ X.structureMap = sY) :
    (constant f hf).section X = 0 := by
  letI := dualBaseChange_isIso f (smooth_cotangent_rank X.structureMap d X.smooth)
  apply (cancel_mono (dualBaseChange f (cotangentSheaf X.structureMap))).mp
  rw [(constant f hf).section_normalized, constant_cotangentHom,
    TwoChartSections.homSection_zero, zero_comp]

theorem constant_variation {Y : Scheme} {d : ℕ}
    (X : SmoothProperComplexVariety d) {sY : Y ⟶ ComplexBase}
    (f : Y ⟶ X.scheme) (hf : f ≫ X.structureMap = sY) :
    (constant f hf).variation X = 0 := by
  rw [Deformation.variation, constant_section, sectionValue_zero]

/-! ### Restriction to an actual source subspace -/

/-- Change the source by its actual base change over the same parameter.
The central morphism remains the composite g followed by f. -/
def Deformation.pullback {Z Y X : Scheme}
    {sZ : Z ⟶ ComplexBase} {sY : Y ⟶ ComplexBase} {sX : X ⟶ ComplexBase}
    {f : Y ⟶ X} (D : Deformation sY sX f)
    (g : Z ⟶ Y) (hg : g ≫ sY = sZ) : Deformation sZ sX (g ≫ f) where
  map := DualThickening.map g hg ≫ D.map
  overC := by
    rw [Category.assoc, D.overC]
    change DualThickening.map g hg ≫ (projection sY ≫ sY) = projection sZ ≫ sZ
    rw [← Category.assoc, map_projection, Category.assoc, hg]
  reduces := sourceChange_reduces g hg D.map f D.reduces

theorem Deformation.pullback_onFunction {Z Y X : Scheme}
    {sZ : Z ⟶ ComplexBase} {sY : Y ⟶ ComplexBase} {sX : X ⟶ ComplexBase}
    {f : Y ⟶ X} (D : Deformation sY sX f)
    (g : Z ⟶ Y) (hg : g ≫ sY = sZ)
    (V : X.Opens) (a : RingSections X V) :
    (D.pullback g hg).onFunction V a = g.app (f ⁻¹ᵁ V) (D.onFunction V a) :=
  coefficient_functionPullback_sourceChange g hg D.map f D.reduces V a

/-- The canonical map from g*O_Y evaluates pulled local functions by g#. -/
theorem unitPullbackMap_pullLocalSection {Z Y : Scheme} (g : Z ⟶ Y)
    (U : Y.Opens) (a : RingSections Y U) :
    (unitPullbackMap g).app (g ⁻¹ᵁ U)
      (pullLocalSection g (structureModule Y) U a) = g.app U a := by
  exact congrArg (fun h : structureModule Y ⟶
    (Scheme.Modules.pushforward g).obj (structureModule Z) => h.app U a)
      (unitPullbackMap_adjoint g)

/-- Cotangent naturality for the actual source restriction. The
composition isomorphism and the structure-sheaf comparison are canonical. -/
theorem Deformation.pullback_cotangentHom {Z Y X : Scheme}
    {sZ : Z ⟶ ComplexBase} {sY : Y ⟶ ComplexBase} {sX : X ⟶ ComplexBase}
    {f : Y ⟶ X} (D : Deformation sY sX f)
    (g : Z ⟶ Y) (hg : g ≫ sY = sZ) :
    (D.pullback g hg).cotangentHom =
      (Scheme.Modules.pullbackComp g f).inv.app (cotangentSheaf sX) ≫
        (Scheme.Modules.pullback g).map D.cotangentHom ≫ unitPullbackMap g := by
  symm
  apply (D.pullback g hg).cotangentHom_unique
  intro V a
  change (unitPullbackMap g).app ((g ≫ f) ⁻¹ᵁ V)
    (((Scheme.Modules.pullback g).map D.cotangentHom).app ((g ≫ f) ⁻¹ᵁ V)
      (((Scheme.Modules.pullbackComp g f).inv.app (cotangentSheaf sX)).app
        ((g ≫ f) ⁻¹ᵁ V)
        (pullLocalSection (g ≫ f) (cotangentSheaf sX) V
          ((cotangentPresentation sX).differential.apply V a)))) = _
  rw [ContactPositiveIsotropy.pullbackComp_inv_pullLocalSection]
  change (unitPullbackMap g).app (g ⁻¹ᵁ (f ⁻¹ᵁ V))
    (((Scheme.Modules.pullback g).map D.cotangentHom).app (g ⁻¹ᵁ (f ⁻¹ᵁ V))
      (pullLocalSection g (pullbackModule f (cotangentSheaf sX)) (f ⁻¹ᵁ V)
        (pullLocalSection f (cotangentSheaf sX) V
          ((cotangentPresentation sX).differential.apply V a)))) = _
  rw [← LeviFiberGeometry.pullLocalSection_map, D.cotangentHom_differential,
    unitPullbackMap_pullLocalSection, D.pullback_onFunction]

theorem Deformation.ext {Y X : Scheme}
    {sY : Y ⟶ ComplexBase} {sX : X ⟶ ComplexBase} {f : Y ⟶ X}
    {D₁ D₂ : Deformation sY sX f} (h : D₁.map = D₂.map) : D₁ = D₂ := by
  cases D₁
  cases D₂
  cases h
  rfl

/-- The fixed-source condition is an equality of actual maps on the
whole thickening, hence includes the infinitesimal coefficient. -/
def Deformation.IsFixedAlong {Z Y X : Scheme}
    {sZ : Z ⟶ ComplexBase} {sY : Y ⟶ ComplexBase} {sX : X ⟶ ComplexBase}
    {f : Y ⟶ X} (D : Deformation sY sX f)
    (g : Z ⟶ Y) (hg : g ≫ sY = sZ) : Prop :=
  DualThickening.map g hg ≫ D.map = projection sZ ≫ (g ≫ f)

theorem Deformation.pullback_eq_constant_of_fixed {Z Y X : Scheme}
    {sZ : Z ⟶ ComplexBase} {sY : Y ⟶ ComplexBase} {sX : X ⟶ ComplexBase}
    {f : Y ⟶ X} (D : Deformation sY sX f)
    (g : Z ⟶ Y) (hg : g ≫ sY = sZ) (hfixed : D.IsFixedAlong g hg) :
    D.pullback g hg = constant (g ≫ f)
      (by rw [Category.assoc, D.centre_overC, hg]) := by
  apply Deformation.ext
  exact hfixed

/-- Fixed-source vanishing first holds on every actual target function. -/
theorem Deformation.fixed_onFunction {Z Y X : Scheme}
    {sZ : Z ⟶ ComplexBase} {sY : Y ⟶ ComplexBase} {sX : X ⟶ ComplexBase}
    {f : Y ⟶ X} (D : Deformation sY sX f)
    (g : Z ⟶ Y) (hg : g ≫ sY = sZ) (hfixed : D.IsFixedAlong g hg)
    (V : X.Opens) (a : RingSections X V) :
    g.app (f ⁻¹ᵁ V) (D.onFunction V a) = 0 := by
  rw [← D.pullback_onFunction g hg, D.pullback_eq_constant_of_fixed g hg hfixed,
    constant_onFunction]

/-- The corresponding actual pulled-back cotangent functional vanishes.
This is stronger than checking only the values of global functions. -/
theorem Deformation.fixed_cotangentHom {Z Y X : Scheme}
    {sZ : Z ⟶ ComplexBase} {sY : Y ⟶ ComplexBase} {sX : X ⟶ ComplexBase}
    {f : Y ⟶ X} (D : Deformation sY sX f)
    (g : Z ⟶ Y) (hg : g ≫ sY = sZ) (hfixed : D.IsFixedAlong g hg) :
    (Scheme.Modules.pullback g).map D.cotangentHom ≫ unitPullbackMap g = 0 := by
  apply (cancel_epi ((Scheme.Modules.pullbackComp g f).inv.app
    (cotangentSheaf sX))).mp
  rw [comp_zero, ← D.pullback_cotangentHom g hg,
    D.pullback_eq_constant_of_fixed g hg hfixed, constant_cotangentHom]

end LeBrunSalamon.Construction.Lines.FamilyVariation

end

/-!
## Infinitesimal deformations from the actual fixed-node Hom family

The family used here is the scheme-theoretic marked-evaluation fiber of
HomSpacePresentation. A curve through the marked target point supplies an
actual center of that fiber by the full Hom universal property. Every
dual-number lift of this center then supplies an actual curve deformation.
Its restriction to the source marking is proved constant as a scheme map.
There is no supplied tangent-to-section identification in this construction.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction

namespace LeBrunSalamon.Construction.Lines.HomDeformation

/-- Include the curve over an actual complex parameter point. -/
def sourceAtPoint (P : ProjectiveLineOverC) {T : Scheme}
    {sT : T ⟶ ComplexBase} (t : PointsOver ComplexBase (𝟙 ComplexBase) T sT) :
    ProjectiveLine ⟶ RationalSourceOver P T sT :=
  pullback.lift (𝟙 ProjectiveLine) (P.structureMap ≫ t.val)
    (by simp [Category.assoc, t.property])

@[simp] theorem sourceAtPoint_fst (P : ProjectiveLineOverC) {T : Scheme}
    {sT : T ⟶ ComplexBase} (t : PointsOver ComplexBase (𝟙 ComplexBase) T sT) :
    sourceAtPoint P t ≫ pullback.fst P.structureMap sT = 𝟙 ProjectiveLine := by
  simp [sourceAtPoint]

@[simp] theorem sourceAtPoint_snd (P : ProjectiveLineOverC) {T : Scheme}
    {sT : T ⟶ ComplexBase} (t : PointsOver ComplexBase (𝟙 ComplexBase) T sT) :
    sourceAtPoint P t ≫ pullback.snd P.structureMap sT = P.structureMap ≫ t.val := by
  simp [sourceAtPoint]

/-- The canonical identification in the source direction uses actual
pullback projections, rather than a chosen isomorphism of curves. -/
theorem sourceAtPoint_naturality (P : ProjectiveLineOverC)
    {T S : Scheme} {sT : T ⟶ ComplexBase} {sS : S ⟶ ComplexBase}
    (t : PointsOver ComplexBase (𝟙 ComplexBase) T sT)
    (g : PointsOver T sT S sS) :
    sourceAtPoint P t ≫ rationalSourceMap P g =
      sourceAtPoint P ⟨t.val ≫ g.val, by rw [Category.assoc, g.property, t.property]⟩ := by
  apply pullback.hom_ext
  · simp only [Category.assoc, rationalSourceMap, pullback.lift_fst, sourceAtPoint_fst]
  · simp only [Category.assoc, rationalSourceMap, pullback.lift_snd, sourceAtPoint_snd]
    rw [← Category.assoc, sourceAtPoint_snd, Category.assoc]

theorem sourceAtPoint_marking (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {T : Scheme} {sT : T ⟶ ComplexBase}
    (t : PointsOver ComplexBase (𝟙 ComplexBase) T sT) :
    p.map ≫ sourceAtPoint P t = t.val ≫ FixedNodeHom.markingSection P p sT := by
  apply pullback.hom_ext
  · simp only [Category.assoc, sourceAtPoint_fst, Category.comp_id,
      FixedNodeHom.markingSection_fst]
    rw [← Category.assoc, t.property, Category.id_comp]
  · simp only [Category.assoc, sourceAtPoint_snd, FixedNodeHom.markingSection_snd,
      Category.comp_id]
    rw [← Category.assoc, p.overC, Category.id_comp]

section Centers

variable (P : ProjectiveLineOverC) {d : ℕ} {X : SmoothProperComplexVariety d}
variable (H : HomSpacePresentation P X)

/-- The full Hom functor represents the actual curve pulled back along
the projection P1 times Spec(C) -> P1. -/
theorem center_exists (f : ProjectiveLine ⟶ X.scheme)
    (hf : f ≫ X.structureMap = P.structureMap) :
    ∃ t : PointsOver ComplexBase (𝟙 ComplexBase) H.parameter H.toC,
      H.mapAt P t = f := by
  let family : PointsOver (RationalSourceOver P ComplexBase (𝟙 ComplexBase))
      (pullback.fst P.structureMap (𝟙 ComplexBase) ≫ P.structureMap)
      X.scheme X.structureMap :=
    ⟨pullback.fst P.structureMap (𝟙 ComplexBase) ≫ f, by rw [Category.assoc, hf]⟩
  obtain ⟨t, ht⟩ := (H.universal ComplexBase (𝟙 ComplexBase)).2 family
  refine ⟨t, ?_⟩
  have he := congrArg Subtype.val ht
  let e : PointsOver ComplexBase (𝟙 ComplexBase) ComplexBase (𝟙 ComplexBase) :=
    ⟨𝟙 ComplexBase, Category.id_comp _⟩
  have hp := congrArg (fun k => sourceAtPoint P e ≫ k) he
  have hs : sourceAtPoint P e ≫ rationalSourceMap P t = sourceAtPoint P t := by
    simpa only [e, Category.id_comp] using sourceAtPoint_naturality P e t
  change sourceAtPoint P t ≫ H.evaluation = f
  calc
    sourceAtPoint P t ≫ H.evaluation =
        sourceAtPoint P e ≫ (rationalSourceMap P t ≫ H.evaluation) := by
      rw [← Category.assoc, hs]
    _ = sourceAtPoint P e ≫ (pullback.fst P.structureMap (𝟙 ComplexBase) ≫ f) := hp
    _ = f := by rw [← Category.assoc, sourceAtPoint_fst, Category.id_comp]

def center (f : ProjectiveLine ⟶ X.scheme)
    (hf : f ≫ X.structureMap = P.structureMap) :
    PointsOver ComplexBase (𝟙 ComplexBase) H.parameter H.toC :=
  Classical.choose (center_exists P H f hf)

theorem center_spec (f : ProjectiveLine ⟶ X.scheme)
    (hf : f ≫ X.structureMap = P.structureMap) :
    H.mapAt P (center P H f hf) = f :=
  Classical.choose_spec (center_exists P H f hf)

theorem mapAt_markedEvaluation (p : ProjectiveLinePoint P)
    (t : PointsOver ComplexBase (𝟙 ComplexBase) H.parameter H.toC) :
    p.map ≫ H.mapAt P t = t.val ≫ FixedNodeHom.markedEvaluation P p H := by
  change p.map ≫ (sourceAtPoint P t ≫ H.evaluation) = _
  rw [← Category.assoc, sourceAtPoint_marking, Category.assoc]
  rfl

def fixedCenter (p : ProjectiveLinePoint P) (x : ComplexPoint X)
    (f : ProjectiveLine ⟶ X.scheme)
    (hf : f ≫ X.structureMap = P.structureMap) (hx : p.map ≫ f = x.map) :
    PointsOver ComplexBase (𝟙 ComplexBase)
      (FixedNodeHom.parameter P p H x) (FixedNodeHom.toC P p H x) :=
  FixedNodeHom.lift P p H x (center P H f hf) (by
    rw [← mapAt_markedEvaluation, center_spec, hx, Category.id_comp])

/-- The central curve of the actual fixed-node family. -/
def curveAt (p : ProjectiveLinePoint P) (x : ComplexPoint X)
    (t : PointsOver ComplexBase (𝟙 ComplexBase)
      (FixedNodeHom.parameter P p H x) (FixedNodeHom.toC P p H x)) :
    ProjectiveLine ⟶ X.scheme :=
  sourceAtPoint P t ≫ FixedNodeHom.evaluation P p H x

theorem curveAt_overC (p : ProjectiveLinePoint P) (x : ComplexPoint X)
    (t : PointsOver ComplexBase (𝟙 ComplexBase)
      (FixedNodeHom.parameter P p H x) (FixedNodeHom.toC P p H x)) :
    curveAt P H p x t ≫ X.structureMap = P.structureMap := by
  rw [curveAt, Category.assoc, FixedNodeHom.evaluation_overC, ← Category.assoc,
    sourceAtPoint_fst, Category.id_comp]

theorem curveAt_marking (p : ProjectiveLinePoint P) (x : ComplexPoint X)
    (t : PointsOver ComplexBase (𝟙 ComplexBase)
      (FixedNodeHom.parameter P p H x) (FixedNodeHom.toC P p H x)) :
    p.map ≫ curveAt P H p x t = x.map := by
  rw [curveAt, ← Category.assoc, sourceAtPoint_marking, Category.assoc,
    FixedNodeHom.fixedNode, ← Category.assoc, t.property, Category.id_comp]

theorem curveAt_fixedCenter (p : ProjectiveLinePoint P) (x : ComplexPoint X)
    (f : ProjectiveLine ⟶ X.scheme)
    (hf : f ≫ X.structureMap = P.structureMap) (hx : p.map ≫ f = x.map) :
    curveAt P H p x (fixedCenter P H p x f hf hx) = f := by
  unfold curveAt FixedNodeHom.evaluation
  rw [← Category.assoc, sourceAtPoint_naturality]
  have hpt :
      (⟨(fixedCenter P H p x f hf hx).val ≫
          (FixedNodeHom.asHomPoint P p H x).val, by
          rw [Category.assoc, (FixedNodeHom.asHomPoint P p H x).property,
            (fixedCenter P H p x f hf hx).property]⟩ :
        PointsOver ComplexBase (𝟙 ComplexBase) H.parameter H.toC) = center P H f hf := by
    apply Subtype.ext
    exact FixedNodeHom.lift_inclusion P p H x _ _
  rw [hpt]
  exact center_spec P H f hf

end Centers

section InfinitesimalFamilies

variable (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
variable {d : ℕ} {X : SmoothProperComplexVariety d}
variable (H : HomSpacePresentation P X) (x : ComplexPoint X)
variable (t : PointsOver ComplexBase (𝟙 ComplexBase)
  (FixedNodeHom.parameter P p H x) (FixedNodeHom.toC P p H x))
variable (v : Infinitesimal.PointLift (FixedNodeHom.parameter P p H x)
  (FixedNodeHom.toC P p H x) t)

theorem zeroSection_parameterChange :
    DualThickening.zeroSection P.structureMap ≫
      rationalSourceMap P (⟨v.map, v.overC⟩ :
        PointsOver Infinitesimal.DualScheme Infinitesimal.dualToC
          (FixedNodeHom.parameter P p H x) (FixedNodeHom.toC P p H x)) =
      sourceAtPoint P t := by
  apply pullback.hom_ext
  · change _ ≫ pullback.fst P.structureMap (FixedNodeHom.toC P p H x) = _
    simp only [Category.assoc, rationalSourceMap, pullback.lift_fst, sourceAtPoint_fst]
    exact DualThickening.zeroSection_projection P.structureMap
  · simp only [Category.assoc, rationalSourceMap, pullback.lift_snd, sourceAtPoint_snd]
    rw [← Category.assoc]
    change (DualThickening.zeroSection P.structureMap ≫
      DualThickening.parameter P.structureMap) ≫ v.map = _
    rw [DualThickening.zeroSection_parameter, Category.assoc, v.reduces]

/-- The actual universal family pulled back along the actual infinitesimal
parameter. Its central curve is proved, not supplied as a separate field. -/
def deformation : FamilyVariation.Deformation P.structureMap X.structureMap
    (curveAt P H p x t) where
  map := rationalSourceMap P (⟨v.map, v.overC⟩ :
      PointsOver Infinitesimal.DualScheme Infinitesimal.dualToC
        (FixedNodeHom.parameter P p H x) (FixedNodeHom.toC P p H x)) ≫
    FixedNodeHom.evaluation P p H x
  overC := by
    rw [Category.assoc, FixedNodeHom.evaluation_overC, ← Category.assoc]
    change (rationalSourceMap P _ ≫
      pullback.fst P.structureMap (FixedNodeHom.toC P p H x)) ≫ P.structureMap = _
    rw [show rationalSourceMap P _ ≫
        pullback.fst P.structureMap (FixedNodeHom.toC P p H x) =
        pullback.fst P.structureMap Infinitesimal.dualToC from pullback.lift_fst _ _ _]
    rfl
  reduces := by
    rw [← Category.assoc, zeroSection_parameterChange]
    rfl

/-- Fixing the node is an equality on the entire infinitesimal test scheme,
including its nilpotents; it is not merely equality at the closed point. -/
theorem deformation_fixedMarking :
    FixedNodeHom.markingSection P p Infinitesimal.dualToC ≫
      (deformation P p H x t v).map = Infinitesimal.dualToC ≫ x.map := by
  change FixedNodeHom.markingSection P p Infinitesimal.dualToC ≫
    (rationalSourceMap P _ ≫ FixedNodeHom.evaluation P p H x) = _
  rw [← Category.assoc, FixedNodeHom.markingSection_naturality,
    Category.assoc, FixedNodeHom.fixedNode, ← Category.assoc, v.overC]

/-- Source base change of the marked point is exactly its section in the
dual-number family, after the canonical parameter projection. -/
theorem thickenedMarking_eq :
    DualThickening.map p.map p.overC =
      DualThickening.parameter (𝟙 ComplexBase) ≫
        FixedNodeHom.markingSection P p Infinitesimal.dualToC := by
  apply pullback.hom_ext
  · change DualThickening.map p.map p.overC ≫
        DualThickening.projection P.structureMap = _
    rw [DualThickening.map_projection, Category.assoc, FixedNodeHom.markingSection_fst,
      ← Category.assoc, DualThickening.parameter_overC]
    simp only [DualThickening.toC, Category.comp_id]
  · change DualThickening.map p.map p.overC ≫
        DualThickening.parameter P.structureMap = _
    rw [DualThickening.map_parameter, Category.assoc, FixedNodeHom.markingSection_snd,
      Category.comp_id]

/-- This exact constant-deformation equation feeds the normalized
cotangent construction of the zero value of the deformation section. -/
theorem deformation_fixedSource :
    DualThickening.map p.map p.overC ≫ (deformation P p H x t v).map =
      DualThickening.projection (𝟙 ComplexBase) ≫ (p.map ≫ curveAt P H p x t) := by
  rw [thickenedMarking_eq, Category.assoc, deformation_fixedMarking,
    ← Category.assoc, DualThickening.parameter_overC, curveAt_marking]
  simp only [DualThickening.toC, Category.comp_id]

/-- The same construction centered at the original specified curve. -/
def deformationOfCurve (f : ProjectiveLine ⟶ X.scheme)
    (hf : f ≫ X.structureMap = P.structureMap) (hx : p.map ≫ f = x.map)
    (w : Infinitesimal.PointLift (FixedNodeHom.parameter P p H x)
      (FixedNodeHom.toC P p H x) (fixedCenter P H p x f hf hx)) :
    FamilyVariation.Deformation P.structureMap X.structureMap f where
  map := (deformation P p H x (fixedCenter P H p x f hf hx) w).map
  overC := (deformation P p H x (fixedCenter P H p x f hf hx) w).overC
  reduces := (deformation P p H x (fixedCenter P H p x f hf hx) w).reduces.trans
    (curveAt_fixedCenter P H p x f hf hx)

theorem deformationOfCurve_fixedSource (f : ProjectiveLine ⟶ X.scheme)
    (hf : f ≫ X.structureMap = P.structureMap) (hx : p.map ≫ f = x.map)
    (w : Infinitesimal.PointLift (FixedNodeHom.parameter P p H x)
      (FixedNodeHom.toC P p H x) (fixedCenter P H p x f hf hx)) :
    DualThickening.map p.map p.overC ≫ (deformationOfCurve P p H x f hf hx w).map =
      DualThickening.projection (𝟙 ComplexBase) ≫ (p.map ≫ f) := by
  simpa only [deformationOfCurve, curveAt_fixedCenter] using
    deformation_fixedSource P p H x (fixedCenter P H p x f hf hx) w

end InfinitesimalFamilies

end LeBrunSalamon.Construction.Lines.HomDeformation

end

/-!
## The source first jet of the actual universal Hom family

The velocity construction must begin with an actual source tangent lift.
Keeping this lift fixed and allowing the entire Hom parameter scheme to
vary gives a genuine dual-number family over that parameter scheme. The
fixed-node equation makes its reduction the constant target point. Its
normalized coefficient is consequently a regular, globally defined
section of the pullback of the target tangent bundle along that point.

This does not assume that a Zariski neighborhood in a product contains a
product of neighborhoods. The first-jet restriction is constructed by
actual scheme pullbacks over the entire fixed-node parameter scheme.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentySix LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirty
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction

namespace LeBrunSalamon.Construction.Lines.HomFirstJet

variable (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)

/-- A genuine source tangent lift at the specified marking. -/
abbrev SourceLift := Infinitesimal.PointLift ProjectiveLine P.structureMap
  (⟨p.map, p.overC⟩ : PointsOver ComplexBase (𝟙 ComplexBase) ProjectiveLine P.structureMap)

/-- Restrict only the source coordinate to its first jet. The parameter
scheme is arbitrary and may be nonreduced. -/
def sourceMap {T : Scheme} (sT : T ⟶ ComplexBase) (τ : SourceLift P p) :
    DualThickening.space sT ⟶ RationalSourceOver P T sT :=
  pullback.lift (DualThickening.parameter sT ≫ τ.map) (DualThickening.projection sT)
    (by rw [Category.assoc, τ.overC]; exact DualThickening.parameter_overC sT)

@[simp] theorem sourceMap_fst {T : Scheme} (sT : T ⟶ ComplexBase)
    (τ : SourceLift P p) :
    sourceMap P p sT τ ≫ pullback.fst P.structureMap sT =
      DualThickening.parameter sT ≫ τ.map := by
  simp [sourceMap]

@[simp] theorem sourceMap_snd {T : Scheme} (sT : T ⟶ ComplexBase)
    (τ : SourceLift P p) :
    sourceMap P p sT τ ≫ pullback.snd P.structureMap sT =
      DualThickening.projection sT := by
  simp [sourceMap]

/-- Reduction of the source jet is exactly the marked section of the
original family over the whole parameter scheme. -/
theorem sourceMap_reduces {T : Scheme} (sT : T ⟶ ComplexBase)
    (τ : SourceLift P p) :
    DualThickening.zeroSection sT ≫ sourceMap P p sT τ =
      FixedNodeHom.markingSection P p sT := by
  apply pullback.hom_ext
  · rw [Category.assoc, sourceMap_fst, ← Category.assoc,
      DualThickening.zeroSection_parameter, Category.assoc, τ.reduces,
      FixedNodeHom.markingSection_fst]
  · rw [Category.assoc, sourceMap_snd, DualThickening.zeroSection_projection,
      FixedNodeHom.markingSection_snd]

/-- Changing the family parameter commutes with the actual source-jet
restriction. This includes infinitesimal changes of parameter. -/
theorem sourceMap_naturality {S T : Scheme}
    {sS : S ⟶ ComplexBase} {sT : T ⟶ ComplexBase}
    (g : PointsOver S sS T sT) (τ : SourceLift P p) :
    sourceMap P p sS τ ≫ rationalSourceMap P g =
      DualThickening.map g.val g.property ≫ sourceMap P p sT τ := by
  apply pullback.hom_ext
  · simp only [Category.assoc, rationalSourceMap, pullback.lift_fst, sourceMap_fst]
    rw [← Category.assoc, DualThickening.map_parameter]
  · simp only [Category.assoc, rationalSourceMap, pullback.lift_snd, sourceMap_snd]
    rw [← Category.assoc, sourceMap_snd, DualThickening.map_projection]

section ActualHomFamily

variable {d : ℕ} {X : SmoothProperComplexVariety d}
variable (H : HomSpacePresentation P X) (x : ComplexPoint X)
variable (τ : SourceLift P p)

/-- The actual first-jet deformation over the entire fixed-node Hom
parameter scheme, centered at the constant target point. -/
def deformation : FamilyVariation.Deformation (FixedNodeHom.toC P p H x)
    X.structureMap (FixedNodeHom.toC P p H x ≫ x.map) where
  map := sourceMap P p (FixedNodeHom.toC P p H x) τ ≫ FixedNodeHom.evaluation P p H x
  overC := by
    rw [Category.assoc, FixedNodeHom.evaluation_overC, ← Category.assoc,
      sourceMap_fst, Category.assoc, τ.overC]
    exact DualThickening.parameter_overC (FixedNodeHom.toC P p H x)
  reduces := by
    rw [← Category.assoc, sourceMap_reduces, FixedNodeHom.fixedNode]

/-- The regular velocity section is constructed from the actual family
and its fixed source lift. It is a section of the original tangent sheaf
pulled back along the constant-node map, not a supplied function on points. -/
def velocitySection : CSections (FixedNodeHom.toC P p H x)
    (pullbackModule (FixedNodeHom.toC P p H x ≫ x.map) (tangentSheaf X.structureMap)) :=
  (deformation P p H x τ).variation X

/-- Its value on any local target differential is the actual source-jet
coefficient. This normalization will identify the affine scheme morphism. -/
theorem velocitySection_normalized :
    TwoChartSections.internalHomSectionAddEquiv _ _
      (sectionFromValue (velocitySection P p H x τ) ≫
        dualBaseChange (FixedNodeHom.toC P p H x ≫ x.map)
          (cotangentSheaf X.structureMap)) =
      (deformation P p H x τ).cotangentHom :=
  (deformation P p H x τ).variation_normalized X

/-- Restricting the actual family to any parameter test scheme gives
the same first-jet map as restricting its global velocity deformation. -/
theorem deformation_parameterChange {T : Scheme} {sT : T ⟶ ComplexBase}
    (g : PointsOver T sT (FixedNodeHom.parameter P p H x) (FixedNodeHom.toC P p H x)) :
    ((deformation P p H x τ).pullback g.val g.property).map =
      sourceMap P p sT τ ≫ rationalSourceMap P g ≫ FixedNodeHom.evaluation P p H x := by
  change DualThickening.map g.val g.property ≫
    (sourceMap P p (FixedNodeHom.toC P p H x) τ ≫ FixedNodeHom.evaluation P p H x) = _
  rw [← Category.assoc, ← sourceMap_naturality, Category.assoc]

/-- At an actual complex parameter point, the source-jet family is the
source lift followed by the central curve already constructed from Hom. -/
theorem deformation_atPoint
    (t : PointsOver ComplexBase (𝟙 ComplexBase)
      (FixedNodeHom.parameter P p H x) (FixedNodeHom.toC P p H x)) :
    ((deformation P p H x τ).pullback t.val t.property).map =
      DualThickening.parameter (𝟙 ComplexBase) ≫ τ.map ≫ HomDeformation.curveAt P H p x t := by
  rw [deformation_parameterChange]
  change sourceMap P p (𝟙 ComplexBase) τ ≫ rationalSourceMap P t ≫
      FixedNodeHom.evaluation P p H x =
    DualThickening.parameter (𝟙 ComplexBase) ≫ τ.map ≫
      (HomDeformation.sourceAtPoint P t ≫ FixedNodeHom.evaluation P p H x)
  have hsource : sourceMap P p (𝟙 ComplexBase) τ ≫ rationalSourceMap P t =
      (DualThickening.parameter (𝟙 ComplexBase) ≫ τ.map) ≫ HomDeformation.sourceAtPoint P t := by
    apply pullback.hom_ext
    · simp only [Category.assoc, rationalSourceMap, pullback.lift_fst,
        sourceMap_fst, HomDeformation.sourceAtPoint_fst, Category.comp_id]
    · simp only [Category.assoc, rationalSourceMap, pullback.lift_snd,
        HomDeformation.sourceAtPoint_snd]
      rw [← Category.assoc, sourceMap_snd]
      rw [← Category.assoc τ.map, τ.overC, ← Category.assoc,
        DualThickening.parameter_overC]
      simp only [DualThickening.toC, Category.comp_id]
  rw [← Category.assoc, hsource]
  simp only [Category.assoc]

end ActualHomFamily

end LeBrunSalamon.Construction.Lines.HomFirstJet

end

/-!
## Actual dual sections commute with normalized pullback

The internal-Hom section corresponding to a sheaf morphism evaluates by
that morphism on every open. Pullback preserves this normalization through
the canonical structure-sheaf comparison. The proof uses uniqueness of the
normalized pulled-back bilinear pairing, so it does not require that global
sections generate an arbitrary sheaf.

This is the source-restriction comparison used for the infinitesimal
section of an actual family and its vanishing at a fixed node.
No new admission occurs in this fragment.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction
open LeBrunSalamon.Construction.Lines.LeviFiberGeometry

namespace LeBrunSalamon.Construction.Lines.FamilyVariation

/-- On each open, the value at one of the actual Hom section is exactly
the restriction of the original sheaf morphism. -/
theorem homSection_localHomOne {Y : Scheme} {E F : OModule Y}
    (h : E ⟶ F) (U : Y.Opens) :
    (internalHomConstructionIso E F).hom.app U
      (Scheme.Modules.Hom.app (TwoChartSections.homSection h) U (1 : RingSections Y U)) =
        P1Ideal.localSectionOfHom h U := by
  change Scheme.Modules.Hom.app (TwoChartSections.homSection h ≫
    (internalHomConstructionIso E F).hom) U (1 : RingSections Y U) = _
  rw [ScalarSections.section_app_one, sectionValue_comp,
    TwoChartSections.homSection_localHomValue]
  exact P1Ideal.localSectionOfHom_restrict h (homOfLE le_top)

/-- Evaluation is normalized at one using the actual local-Hom comparison. -/
theorem homSection_evaluate_one {Y : Scheme} {E F : OModule Y}
    (h : E ⟶ F) (U : Y.Opens) (e : SectionsOn E U) :
    (sheafEvaluationPair E F).apply U
      (Scheme.Modules.Hom.app (TwoChartSections.homSection h) U (1 : RingSections Y U)) e = h.app U e := by
  change (internalHomPresentation E F).evaluate.app U
    ((tensorPresentation (internalHomSheaf E F) E).pair.apply U
      (Scheme.Modules.Hom.app (TwoChartSections.homSection h) U (1 : RingSections Y U)) e) = _
  rw [← internalHomGenericIso_evaluate_pair]
  change HomConstruction.evaluationAt E F U
    ((internalHomConstructionIso E F).hom.app U
      (Scheme.Modules.Hom.app (TwoChartSections.homSection h) U (1 : RingSections Y U))) e = _
  rw [homSection_localHomOne]
  rfl

/-- The same normalization on every scalar, retaining sheaf-linearity. -/
theorem homSection_evaluate {Y : Scheme} {E F : OModule Y}
    (h : E ⟶ F) (U : Y.Opens) (r : RingSections Y U) (e : SectionsOn E U) :
    (sheafEvaluationPair E F).apply U
      (Scheme.Modules.Hom.app (TwoChartSections.homSection h) U r) e = r • h.app U e := by
  have hr : Scheme.Modules.Hom.app (TwoChartSections.homSection h) U r =
      r • Scheme.Modules.Hom.app (TwoChartSections.homSection h) U (1 : RingSections Y U) := by
    simpa only [smul_eq_mul, mul_one] using
      (Scheme.Modules.Hom.app_smul (TwoChartSections.homSection h) r
        (1 : RingSections Y U))
  rw [hr, map_smul, LinearMap.smul_apply, homSection_evaluate_one]

/-- Uncurrying the actual Hom section gives scalar multiplication
followed by the original morphism. This is an equality of sheaf pairings. -/
theorem homSection_evaluationPair {Y : Scheme} {E F : OModule Y}
    (h : E ⟶ F) :
    (sheafEvaluationPair E F).precompose (TwoChartSections.homSection h) (𝟙 E) =
      (TensorConstruction.scalarPair E).postcompose h := by
  apply sheafBilinearMap_ext
  intro U r e
  change RingSections Y U at r
  change (sheafEvaluationPair E F).apply U
    (Scheme.Modules.Hom.app (TwoChartSections.homSection h) U r) e = h.app U (r • e)
  rw [homSection_evaluate, Scheme.Modules.Hom.app_smul]

/-- Pulling the scalar pairing uses precisely the actual unit comparison.
The adjunction unit supplies its semilinearity on all pulled local sections. -/
theorem pullbackPair_scalarHom {T Y : Scheme} (g : T ⟶ Y)
    {E F : OModule Y} (h : E ⟶ F) :
    pullbackPair g ((TensorConstruction.scalarPair E).postcompose h) =
      (TensorConstruction.scalarPair (pullbackModule g F)).precompose
        (unitPullbackMap g) ((Scheme.Modules.pullback g).map h) := by
  have hn : IsPullbackPair g ((TensorConstruction.scalarPair E).postcompose h)
      ((TensorConstruction.scalarPair (pullbackModule g F)).precompose
        (unitPullbackMap g) ((Scheme.Modules.pullback g).map h)) := by
    intro U r e
    change RingSections Y U at r
    change (show RingSections T (g ⁻¹ᵁ U) from
        (unitPullbackMap g).app (g ⁻¹ᵁ U)
          (pullLocalSection g (structureModule Y) U r)) •
          ((Scheme.Modules.pullback g).map h).app (g ⁻¹ᵁ U)
            (pullLocalSection g E U e) =
      pullLocalSection g F U (h.app U (r • e))
    have hu : (unitPullbackMap g).app (g ⁻¹ᵁ U)
        (pullLocalSection g (structureModule Y) U r) = g.app U r := by
      exact congrArg (fun k : structureModule Y ⟶
        (Scheme.Modules.pushforward g).obj (structureModule T) => k.app U r)
          (unitPullbackMap_adjoint g)
    rw [hu, ← pullLocalSection_map g h U e, Scheme.Modules.Hom.app_smul]
    exact (Scheme.Modules.Hom.app_smul
      ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app F)
        r (h.app U e)).symm
  exact ((Classical.choose_spec
    (pullbackPair_existsUnique g ((TensorConstruction.scalarPair E).postcompose h))).2
      _ hn).symm

/-- The canonical dual comparison preserves the original evaluation,
with the prescribed structure-sheaf comparison as its scalar map. -/
theorem dualBaseChange_evaluate {T Y : Scheme} (g : T ⟶ Y)
    (E : OModule Y) (U : T.Opens)
    (φ : SectionsOn (pullbackModule g (dualSheaf E)) U)
    (e : SectionsOn (pullbackModule g E) U) :
    (dualEvaluation (pullbackModule g E)).apply U
      ((dualBaseChange g E).app U φ) e =
        (unitPullbackMap g).app U ((pullbackPair g (dualEvaluation E)).apply U φ e) := by
  exact congrArg (fun b : SheafBilinearMap (pullbackModule g (dualSheaf E))
    (pullbackModule g E) (structureModule T) => b.apply U φ e)
      (sheafEvaluationPair_curry
        ((pullbackPair g (dualEvaluation E)).postcompose (unitPullbackMap g)))

/-- Pulling the actual section of a dual sheaf and applying the canonical
dual-base-change morphism gives the actual pulled-back morphism's section.
No isomorphism of fibers is supplied as a hypothesis. -/
theorem homSection_pullback {T Y : Scheme} (g : T ⟶ Y)
    {E : OModule Y} (h : E ⟶ structureModule Y) :
    pullSection g (TwoChartSections.homSection h) ≫ dualBaseChange g E =
      TwoChartSections.homSection ((Scheme.Modules.pullback g).map h ≫ unitPullbackMap g) := by
  have hp := pullbackPair_precompose g (dualEvaluation E)
    (TwoChartSections.homSection h) (𝟙 E)
  have he : (dualEvaluation E).precompose (TwoChartSections.homSection h) (𝟙 E) =
      (TensorConstruction.scalarPair E).postcompose h := homSection_evaluationPair h
  rw [he, pullbackPair_scalarHom] at hp
  simp only [CategoryTheory.Functor.map_id] at hp
  apply (cancel_epi (unitPullbackIso g).hom).mp
  change unitPullbackMap g ≫
      (pullSection g (TwoChartSections.homSection h) ≫ dualBaseChange g E) =
    unitPullbackMap g ≫
      TwoChartSections.homSection ((Scheme.Modules.pullback g).map h ≫ unitPullbackMap g)
  rw [← Category.assoc, unitPullbackMap_pullSection]
  apply (internalHomPresentation (pullbackModule g E) (structureModule T)).hom_ext
  apply ((tensorPresentation (pullbackModule g (structureModule Y))
    (pullbackModule g E)).universal _).1
  apply sheafBilinearMap_ext
  intro U r e
  change (internalHomPresentation (pullbackModule g E) (structureModule T)).evaluate.app U
      ((tensorMap (((Scheme.Modules.pullback g).map (TwoChartSections.homSection h)) ≫
        dualBaseChange g E) (𝟙 (pullbackModule g E))).app U
          ((tensorPresentation (pullbackModule g (structureModule Y))
            (pullbackModule g E)).pair.apply U r e)) =
    (internalHomPresentation (pullbackModule g E) (structureModule T)).evaluate.app U
      ((tensorMap (unitPullbackMap g ≫ TwoChartSections.homSection
        ((Scheme.Modules.pullback g).map h ≫ unitPullbackMap g))
          (𝟙 (pullbackModule g E))).app U
            ((tensorPresentation (pullbackModule g (structureModule Y))
              (pullbackModule g E)).pair.apply U r e))
  rw [tensorMap_apply, tensorMap_apply]
  change (dualEvaluation (pullbackModule g E)).apply U
      ((dualBaseChange g E).app U
        (((Scheme.Modules.pullback g).map (TwoChartSections.homSection h)).app U r)) e =
    (sheafEvaluationPair (pullbackModule g E) (structureModule T)).apply U
      (Scheme.Modules.Hom.app (TwoChartSections.homSection
        ((Scheme.Modules.pullback g).map h ≫ unitPullbackMap g)) U
          ((unitPullbackMap g).app U r)) e
  rw [dualBaseChange_evaluate, homSection_evaluate]
  have hpv := congrArg (fun b : SheafBilinearMap
    (pullbackModule g (structureModule Y)) (pullbackModule g E)
      (pullbackModule g (structureModule Y)) => b.apply U r e) hp
  change (show RingSections T U from (unitPullbackMap g).app U r) •
      ((Scheme.Modules.pullback g).map h).app U e =
    (pullbackPair g (dualEvaluation E)).apply U
      (((Scheme.Modules.pullback g).map (TwoChartSections.homSection h)).app U r) e at hpv
  rw [← hpv, Scheme.Modules.Hom.app_smul]
  rfl

end LeBrunSalamon.Construction.Lines.FamilyVariation

end

/-!
## Fixed-node vanishing and the actual positive lift

This completes the actual family variation construction. It uses the
proved normalized Hom-section pullback identity, obtains vanishing of
its original tangent-bundle section at the fixed point, and applies the
previous positive-part exact sequence to that constructed section.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirty
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction

namespace LeBrunSalamon.Construction.Lines.FamilyVariation

/-- The actual family section restricts to zero on any source subspace
held fixed by the family. Both dual transports below are the normalized
canonical maps, and finite local freeness supplies their inverses. -/
theorem Deformation.fixed_section {Z Y : Scheme} {d : ℕ}
    (X : SmoothProperComplexVariety d)
    {sZ : Z ⟶ ComplexBase} {sY : Y ⟶ ComplexBase}
    {f : Y ⟶ X.scheme} (D : Deformation sY X.structureMap f)
    (g : Z ⟶ Y) (hg : g ≫ sY = sZ) (hfixed : D.IsFixedAlong g hg) :
    pullSection g (D.section X) = 0 := by
  let hΩ := smooth_cotangent_rank X.structureMap d X.smooth
  letI := dualBaseChange_isIso f hΩ
  letI := dualBaseChange_isIso g (pullback_locallyFree f hΩ)
  have hhom : pullSection g (TwoChartSections.homSection D.cotangentHom) = 0 := by
    apply (cancel_mono (dualBaseChange g (pullbackModule f
      (cotangentSheaf X.structureMap)))).mp
    rw [homSection_pullback, D.fixed_cotangentHom g hg hfixed,
      TwoChartSections.homSection_zero, zero_comp]
  apply (cancel_mono ((Scheme.Modules.pullback g).map
    (dualBaseChange f (cotangentSheaf X.structureMap)))).mp
  rw [zero_comp, ← pullSection_naturality, D.section_normalized, hhom]

/-- Global-section evaluation at an actual fixed complex point is zero.
This proves node vanishing for the constructed variation, rather than
assuming a node-zero tangent-to-section map. -/
theorem Deformation.fixed_variation_evaluation {Y : Scheme} {d : ℕ}
    (X : SmoothProperComplexVariety d) {sY : Y ⟶ ComplexBase}
    {f : Y ⟶ X.scheme} (D : Deformation sY X.structureMap f)
    (p : ComplexBase ⟶ Y) (hp : p ≫ sY = 𝟙 ComplexBase)
    (hfixed : D.IsFixedAlong p hp) :
    evaluateSection sY (pullbackModule f (tangentSheaf X.structureMap)) p hp
      (D.variation X) = 0 := by
  have hs : sectionFromValue (D.variation X) = D.section X :=
    (sectionEquiv _).symm_apply_apply (D.section X)
  change sectionValue (pullSection p (sectionFromValue (D.variation X))) = 0
  rw [hs, D.fixed_section X p hp hfixed, sectionValue_zero]

/-! ### Actual fixed-node curve deformations lift to the positive bundle -/

theorem Deformation.nodeEvaluation_zero {n : ℕ} {X : ContactFanoManifold n}
    (f : FreeLine X) (x : ComplexPoint X.variety)
    (hx : marking.map ≫ f.curve.map = x.map)
    (D : Deformation P.structureMap X.variety.structureMap f.curve.map)
    (hfixed : D.IsFixedAlong marking.map marking.overC) :
    nodeEvaluation f x hx (D.variation X.variety) = 0 := by
  change fiberComposition f.curve.map marking.map x.map hx
    (tangentSheaf X.variety.structureMap)
    (evaluateSection P.structureMap _ marking.map marking.overC
      (D.variation X.variety)) = 0
  rw [D.fixed_variation_evaluation X.variety marking.map marking.overC hfixed, map_zero]

/-- The unique positive lift is now obtained from the actual dual-number
family. Its inputs contain only that family and the fixed-node equation;
they do not contain a supplied section or its vanishing. -/
theorem Deformation.positiveLift_existsUnique {n : ℕ} {X : ContactFanoManifold n}
    (f : FreeLine X) (x : ComplexPoint X.variety)
    (hx : marking.map ≫ f.curve.map = x.map)
    (D : Deformation P.structureMap X.variety.structureMap f.curve.map)
    (hfixed : D.IsFixedAlong marking.map marking.overC) :
    ∃! t : CSections P.structureMap (PositivePart.freeLinePositiveBundle f).sheaf,
      onCSections P.structureMap (PositivePart.freeLinePositiveInclusion f) t =
        D.variation X.variety ∧
      evaluateSection P.structureMap (PositivePart.freeLinePositiveBundle f).sheaf
        marking.map marking.overC t = 0 := by
  exact PositiveQuotient.fixedNodeCurveSection_lifts f x hx
    (PositivePart.freeLinePositiveBundle f) (PositivePart.freeLineZeroBundle f)
    (PositivePart.freeLinePositiveInclusion f) (PositivePart.freeLineZeroProjection f)
    (PositivePart.freeLine_positive_zero f) (PositivePart.freeLine_shortExact f)
    (PositivePart.freeLineZeroTrivialization f) (D.variation X.variety)
    (D.nodeEvaluation_zero f x hx hfixed)

def Deformation.positiveLift {n : ℕ} {X : ContactFanoManifold n}
    (f : FreeLine X) (x : ComplexPoint X.variety)
    (hx : marking.map ≫ f.curve.map = x.map)
    (D : Deformation P.structureMap X.variety.structureMap f.curve.map)
    (hfixed : D.IsFixedAlong marking.map marking.overC) :
    CSections P.structureMap (PositivePart.freeLinePositiveBundle f).sheaf :=
  Classical.choose (D.positiveLift_existsUnique f x hx hfixed)

theorem Deformation.positiveLift_inclusion {n : ℕ} {X : ContactFanoManifold n}
    (f : FreeLine X) (x : ComplexPoint X.variety)
    (hx : marking.map ≫ f.curve.map = x.map)
    (D : Deformation P.structureMap X.variety.structureMap f.curve.map)
    (hfixed : D.IsFixedAlong marking.map marking.overC) :
    onCSections P.structureMap (PositivePart.freeLinePositiveInclusion f)
      (D.positiveLift f x hx hfixed) = D.variation X.variety :=
  (Classical.choose_spec (D.positiveLift_existsUnique f x hx hfixed)).1.1

theorem Deformation.positiveLift_node_zero {n : ℕ} {X : ContactFanoManifold n}
    (f : FreeLine X) (x : ComplexPoint X.variety)
    (hx : marking.map ≫ f.curve.map = x.map)
    (D : Deformation P.structureMap X.variety.structureMap f.curve.map)
    (hfixed : D.IsFixedAlong marking.map marking.overC) :
    evaluateSection P.structureMap (PositivePart.freeLinePositiveBundle f).sheaf
      marking.map marking.overC (D.positiveLift f x hx hfixed) = 0 :=
  (Classical.choose_spec (D.positiveLift_existsUnique f x hx hfixed)).1.2

/-- The positive lift retains the normalization against actual target
functions after its inclusion into the original pulled-back tangent sheaf. -/
theorem Deformation.positiveLift_normalized {n : ℕ} {X : ContactFanoManifold n}
    (f : FreeLine X) (x : ComplexPoint X.variety)
    (hx : marking.map ≫ f.curve.map = x.map)
    (D : Deformation P.structureMap X.variety.structureMap f.curve.map)
    (hfixed : D.IsFixedAlong marking.map marking.overC) :
    TwoChartSections.internalHomSectionAddEquiv _ _
      (sectionFromValue (onCSections P.structureMap
        (PositivePart.freeLinePositiveInclusion f) (D.positiveLift f x hx hfixed)) ≫
          dualBaseChange f.curve.map (cotangentSheaf X.variety.structureMap)) =
      D.cotangentHom := by
  rw [D.positiveLift_inclusion f x hx hfixed]
  exact D.variation_normalized X.variety

end LeBrunSalamon.Construction.Lines.FamilyVariation

namespace LeBrunSalamon.Construction.Lines.HomDeformation

section FixedFreeLine

variable {n : ℕ} {X : ContactFanoManifold n}
variable (H : HomSpacePresentation P X.variety) (f : FreeLine X)
variable (x : ComplexPoint X.variety) (hx : marking.map ≫ f.curve.map = x.map)

/-- Actual dual-number points of the actual fixed-node Hom fiber, centered
at the specified original free line by the full Hom universal property. -/
abbrev FixedLineLift :=
  Infinitesimal.PointLift (FixedNodeHom.parameter P marking H x)
    (FixedNodeHom.toC P marking H x)
    (fixedCenter P H marking x f.curve.map f.curve.overC hx)

/-- The section is constructed from the actual universal evaluation and
the supplied infinitesimal parameter; it is not extra deformation data. -/
def fixedLineVariation (v : FixedLineLift H f x hx) :
    CSections P.structureMap
      (pullbackModule f.curve.map (tangentSheaf X.variety.structureMap)) :=
  (deformationOfCurve P marking H x f.curve.map f.curve.overC hx v).variation X.variety

theorem fixedLineVariation_node_zero (v : FixedLineLift H f x hx) :
    nodeEvaluation f x hx (fixedLineVariation H f x hx v) = 0 := by
  exact (deformationOfCurve P marking H x f.curve.map f.curve.overC hx v).nodeEvaluation_zero
    f x hx (deformationOfCurve_fixedSource P marking H x f.curve.map f.curve.overC hx v)

/-- Direct end-to-end form: each actual infinitesimal fixed-node Hom
parameter yields a unique vanishing section of the actual positive bundle. -/
theorem fixedLine_positiveLift_existsUnique (v : FixedLineLift H f x hx) :
    ∃! t : CSections P.structureMap (PositivePart.freeLinePositiveBundle f).sheaf,
      onCSections P.structureMap (PositivePart.freeLinePositiveInclusion f) t =
        fixedLineVariation H f x hx v ∧
      evaluateSection P.structureMap (PositivePart.freeLinePositiveBundle f).sheaf
        marking.map marking.overC t = 0 := by
  exact (deformationOfCurve P marking H x f.curve.map f.curve.overC hx v).positiveLift_existsUnique
    f x hx (deformationOfCurve_fixedSource P marking H x f.curve.map f.curve.overC hx v)

def fixedLinePositiveVariation (v : FixedLineLift H f x hx) :
    CSections P.structureMap (PositivePart.freeLinePositiveBundle f).sheaf :=
  (deformationOfCurve P marking H x f.curve.map f.curve.overC hx v).positiveLift
    f x hx (deformationOfCurve_fixedSource P marking H x f.curve.map f.curve.overC hx v)

theorem fixedLinePositiveVariation_inclusion (v : FixedLineLift H f x hx) :
    onCSections P.structureMap (PositivePart.freeLinePositiveInclusion f)
      (fixedLinePositiveVariation H f x hx v) = fixedLineVariation H f x hx v := by
  exact (deformationOfCurve P marking H x f.curve.map f.curve.overC hx v).positiveLift_inclusion
    f x hx (deformationOfCurve_fixedSource P marking H x f.curve.map f.curve.overC hx v)

theorem fixedLinePositiveVariation_node_zero (v : FixedLineLift H f x hx) :
    evaluateSection P.structureMap (PositivePart.freeLinePositiveBundle f).sheaf
      marking.map marking.overC (fixedLinePositiveVariation H f x hx v) = 0 := by
  exact (deformationOfCurve P marking H x f.curve.map f.curve.overC hx v).positiveLift_node_zero
    f x hx (deformationOfCurve_fixedSource P marking H x f.curve.map f.curve.overC hx v)

/-- The final positive lift is still normalized by the actual difference
on target functions. In particular no chosen tangent-space identification
has entered between the Hom parameter and the positive section. -/
theorem fixedLinePositiveVariation_on_differential (v : FixedLineLift H f x hx)
    (V : X.variety.scheme.Opens) (a : RingSections X.variety.scheme V) :
    (TwoChartSections.internalHomSectionAddEquiv _ _
      (sectionFromValue (onCSections P.structureMap
        (PositivePart.freeLinePositiveInclusion f) (fixedLinePositiveVariation H f x hx v)) ≫
          dualBaseChange f.curve.map (cotangentSheaf X.variety.structureMap))).app
      (f.curve.map ⁻¹ᵁ V)
      (pullLocalSection f.curve.map (cotangentSheaf X.variety.structureMap) V
        ((cotangentPresentation X.variety.structureMap).differential.apply V a)) =
      (deformationOfCurve P marking H x f.curve.map f.curve.overC hx v).onFunction V a := by
  rw [fixedLinePositiveVariation_inclusion]
  unfold fixedLineVariation
  rw [FamilyVariation.Deformation.variation_normalized]
  exact FamilyVariation.Deformation.cotangentHom_differential _ V a

end FixedFreeLine

end LeBrunSalamon.Construction.Lines.HomDeformation

end

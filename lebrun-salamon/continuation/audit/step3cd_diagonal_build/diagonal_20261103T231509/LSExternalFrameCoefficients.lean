import LSOpenProductCoordinates

/-!
Coefficient normalization for the original external tensor map.  Together
with the actual affine diagonal quotient, this proves diagonal vanishing on
any specified affine frame cover.  This draft adds no admitted theorem.
Native verification is pending; the file remains outside source/.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.Skeleton
open scoped TensorProduct

namespace LeBrunSalamon.ExternalFrameCoefficients

open OpenProductCoordinates AffineFrameProof

theorem section_app_one {X : Scheme} {E : OModule X}
    (a : AlgebraicSection E) (U : X.Opens) :
    Scheme.Modules.Hom.app a U (1 : RingSections X U) =
      E.presheaf.map (homOfLE le_top).op (sectionValue a) := by
  have h := sheafHom_naturality a (homOfLE (show U ≤ ⊤ from le_top))
    (1 : RingSections X ⊤)
  change E.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (sectionValue a) =
    Scheme.Modules.Hom.app a U (X.presheaf.map (homOfLE le_top).op (1 : RingSections X ⊤)) at h
  simpa only [map_one] using h.symm

theorem section_app_one_restrict {X : Scheme} {E : OModule X}
    (a : AlgebraicSection E) {U V : X.Opens} (i : V ⟶ U) :
    Scheme.Modules.Hom.app a V (1 : RingSections X V) =
      E.presheaf.map i.op (Scheme.Modules.Hom.app a U (1 : RingSections X U)) := by
  have h := sheafHom_naturality a i (1 : RingSections X U)
  change E.presheaf.map i.op
    (Scheme.Modules.Hom.app a U (1 : RingSections X U)) =
      Scheme.Modules.Hom.app a V (X.presheaf.map i.op (1 : RingSections X U)) at h
  simpa only [map_one] using h.symm

theorem tensorSection_app_one {X : Scheme} {E F : OModule X}
    (a : AlgebraicSection E) (b : AlgebraicSection F) (U : X.Opens) :
    Scheme.Modules.Hom.app (tensorSection a b) U (1 : RingSections X U) =
      (tensorPresentation E F).pair.apply U
        (Scheme.Modules.Hom.app a U (1 : RingSections X U)) (Scheme.Modules.Hom.app b U (1 : RingSections X U)) := by
  rw [section_app_one, sectionValue_tensorSection,
    (tensorPresentation E F).pair.naturality,
    ← section_app_one, ← section_app_one]

def firstFrame {X : Scheme} (s : X ⟶ ComplexBase) {E : OModule X} {U : X.Opens}
    (e : LocalFrames.OverFrame E U) :
    LocalFrames.OverFrame (pullbackModule (firstProjection s) E) (productOpen s U) :=
  LocalFrames.restrict (homOfLE (productOpen_le_fst s U))
    (pullFrame (firstProjection s) e)

def secondFrame {X : Scheme} (s : X ⟶ ComplexBase) {E : OModule X} {U : X.Opens}
    (e : LocalFrames.OverFrame E U) :
    LocalFrames.OverFrame (pullbackModule (secondProjection s) E) (productOpen s U) :=
  LocalFrames.restrict (homOfLE (productOpen_le_snd s U))
    (pullFrame (secondProjection s) e)

def externalFrame {X : Scheme} (s : X ⟶ ComplexBase)
    {E F : OModule X} {U : X.Opens}
    (e : LocalFrames.OverFrame E U) (f : LocalFrames.OverFrame F U) :
    LocalFrames.OverFrame (externalTensor s E F) (productOpen s U) :=
  LocalFrames.tensorFrame (firstFrame s e) (secondFrame s f)

theorem firstFrame_coefficient {X : Scheme} (s : X ⟶ ComplexBase)
    {E : OModule X} {U : X.Opens} (e : LocalFrames.OverFrame E U)
    (a : AlgebraicSection E) :
    LocalFrames.coordinates (firstFrame s e)
      (Scheme.Modules.Hom.app (pullSection (firstProjection s) a) (productOpen s U)
        (1 : RingSections (SelfProduct s) (productOpen s U))) =
      firstFunctionMap s U (LocalFrames.coordinates e (Scheme.Modules.Hom.app a U (1 : RingSections X U))) := by
  rw [section_app_one_restrict (pullSection (firstProjection s) a)
    (homOfLE (productOpen_le_fst s U))]
  unfold firstFrame
  erw [LocalFrames.coordinates_restrict, pullSection_local, pullFrame_coordinates]
  rfl

theorem secondFrame_coefficient {X : Scheme} (s : X ⟶ ComplexBase)
    {E : OModule X} {U : X.Opens} (e : LocalFrames.OverFrame E U)
    (a : AlgebraicSection E) :
    LocalFrames.coordinates (secondFrame s e)
      (Scheme.Modules.Hom.app (pullSection (secondProjection s) a) (productOpen s U)
        (1 : RingSections (SelfProduct s) (productOpen s U))) =
      secondFunctionMap s U (LocalFrames.coordinates e (Scheme.Modules.Hom.app a U (1 : RingSections X U))) := by
  rw [section_app_one_restrict (pullSection (secondProjection s) a)
    (homOfLE (productOpen_le_snd s U))]
  unfold secondFrame
  erw [LocalFrames.coordinates_restrict, pullSection_local, pullFrame_coordinates]
  rfl

theorem externalProduct_coefficient {X : Scheme} (s : X ⟶ ComplexBase)
    {E F : OModule X} {U : X.Opens}
    (e : LocalFrames.OverFrame E U) (f : LocalFrames.OverFrame F U)
    (a : AlgebraicSection E) (b : AlgebraicSection F) :
    LocalFrames.coordinates (externalFrame s e f)
      (Scheme.Modules.Hom.app (externalProductSection s a b) (productOpen s U)
        (1 : RingSections (SelfProduct s) (productOpen s U))) =
      firstFunctionMap s U (LocalFrames.coordinates e (Scheme.Modules.Hom.app a U (1 : RingSections X U))) *
        secondFunctionMap s U (LocalFrames.coordinates f (Scheme.Modules.Hom.app b U (1 : RingSections X U))) := by
  change LocalFrames.coordinates
    (LocalFrames.tensorFrame (firstFrame s e) (secondFrame s f))
      (Scheme.Modules.Hom.app (tensorSection (pullSection (firstProjection s) a)
        (pullSection (secondProjection s) b)) (productOpen s U)
          (1 : RingSections (SelfProduct s) (productOpen s U))) = _
  rw [tensorSection_app_one, tensorFrame_coordinates_pair,
    firstFrame_coefficient, secondFrame_coefficient]

theorem constants_restrict {X : Scheme} (s : X ⟶ ComplexBase)
    {U V : X.Opens} (i : V ⟶ U) (c : ℂ) :
    X.presheaf.map i.op (KunnethDegreeZero.constants s U c) =
      KunnethDegreeZero.constants s V c := by
  change X.presheaf.map i.op
    (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
      (s.appTop ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c))) =
    X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op
      (s.appTop ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c))
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

def coefficientLinear {X : Scheme} (s : X ⟶ ComplexBase)
    {E : OModule X} {U : X.Opens} (e : LocalFrames.OverFrame E U) :
    KunnethDegreeZero.Sections s E →ₗ[ℂ] Coefficients s U where
  toFun a := LocalFrames.coordinates e (E.presheaf.map (homOfLE le_top).op a)
  map_add' := by intro a b; simp only [map_add]
  map_smul' := by
    intro c a
    change GlobalSections E at a
    change LocalFrames.coordinates e (E.val.map
      (homOfLE (show U ≤ ⊤ from le_top)).op (KunnethDegreeZero.constants s ⊤ c • a)) =
      KunnethDegreeZero.constants s U c *
        LocalFrames.coordinates e (E.val.map (homOfLE le_top).op a)
    rw [E.val.map_smul, (LocalFrames.coordinates e).map_smul]
    change X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
      (KunnethDegreeZero.constants s ⊤ c) *
      LocalFrames.coordinates e (E.val.map (homOfLE le_top).op a) = _
    rw [constants_restrict]

def coefficientTensorMap {X : Scheme} (s : X ⟶ ComplexBase)
    {E F : OModule X} {U : X.Opens}
    (e : LocalFrames.OverFrame E U) (f : LocalFrames.OverFrame F U) :
    (KunnethDegreeZero.Sections s E ⊗[ℂ] KunnethDegreeZero.Sections s F) →ₗ[ℂ]
      (Coefficients s U ⊗[ℂ] Coefficients s U) :=
  TensorProduct.map (coefficientLinear s e) (coefficientLinear s f)

theorem coefficientLinear_sectionValue {X : Scheme} (s : X ⟶ ComplexBase)
    {E : OModule X} {U : X.Opens} (e : LocalFrames.OverFrame E U)
    (a : AlgebraicSection E) :
    coefficientLinear s e (sectionValue a) =
      LocalFrames.coordinates e (Scheme.Modules.Hom.app a U (1 : RingSections X U)) := by
  rw [section_app_one]
  rfl

@[simp] theorem coefficientTensorMap_tmul {X : Scheme} (s : X ⟶ ComplexBase)
    {E F : OModule X} {U : X.Opens}
    (e : LocalFrames.OverFrame E U) (f : LocalFrames.OverFrame F U)
    (a : KunnethDegreeZero.Sections s E) (b : KunnethDegreeZero.Sections s F) :
    coefficientTensorMap s e f (a ⊗ₜ[ℂ] b) =
      coefficientLinear s e a ⊗ₜ[ℂ] coefficientLinear s f b := rfl

/-- Pure tensor normalization and additive induction identify the entire
original external-product map, rather than a replacement map of equal rank. -/
theorem canonicalMap_coefficient {X : Scheme} (s : X ⟶ ComplexBase)
    {E F : OModule X} {U : X.Opens}
    (e : LocalFrames.OverFrame E U) (f : LocalFrames.OverFrame F U)
    (t : KunnethDegreeZero.Sections s E ⊗[ℂ] KunnethDegreeZero.Sections s F) :
    LocalFrames.coordinates (externalFrame s e f)
      ((externalTensor s E F).presheaf.map (homOfLE le_top).op
        (KunnethDegreeZero.canonicalMap s s E F t)) =
      ringMap s U (coefficientTensorMap s e f t) := by
  refine TensorProduct.inductionOn t ?_ ?_
  · intro a b
    rw [KunnethDegreeZero.canonicalMap_tmul]
    change LocalFrames.coordinates (externalFrame s e f)
      ((externalTensor s E F).presheaf.map (homOfLE le_top).op
        (sectionValue (externalProductSection s (sectionFromValue a) (sectionFromValue b)))) = _
    rw [← section_app_one, externalProduct_coefficient]
    change _ = ringMap s U (coefficientLinear s e a ⊗ₜ[ℂ] coefficientLinear s f b)
    rw [ringMap_tmul]
    congr 1 <;> rw [section_app_one, sectionFromValue_spec] <;> rfl
  · intro a b ha hb
    simp only [map_add, ha, hb]

theorem local_diagonal_zero_iff {X : Scheme} (s : X ⟶ ComplexBase) [IsSeparated s]
    {E F : OModule X} (U : X.Opens) (hU : IsAffineOpen U)
    (e : LocalFrames.OverFrame E U) (f : LocalFrames.OverFrame F U)
    (t : KunnethDegreeZero.Sections s E ⊗[ℂ] KunnethDegreeZero.Sections s F) (k : ℕ) :
    (Scheme.Modules.pullback
      ((diagonalPowerInclusion s k ⁻¹ᵁ productOpen s U).ι ≫ diagonalPowerInclusion s k)).map
      (sectionFromValue (KunnethDegreeZero.canonicalMap s s E F t)) = 0 ↔
    Ideal.Quotient.mk ((KaehlerDifferential.ideal ℂ (Coefficients s U)) ^ k)
      (coefficientTensorMap s e f t) = 0 := by
  rw [ClosedIdealCoefficients.section_zero_iff_quotient (diagonal s)
    (productOpen s U) (productOpen_isAffine s U hU) (externalFrame s e f)]
  rw [section_app_one, sectionFromValue_spec, canonicalMap_coefficient]
  exact diagonalPower_quotient_eq_zero_iff s U hU k _

theorem vanishes_order_zero {X : Scheme} (s : X ⟶ ComplexBase) [IsSeparated s]
    (E : OModule (SelfProduct s)) (a : AlgebraicSection E) :
    VanishesToOrderAlongDiagonal s E a 0 := by
  letI : IsEmpty (diagonalPowerSubscheme s 0) := by
    change IsEmpty (((diagonal s).ker ^ 0).subscheme)
    rw [pow_zero, Scheme.IdealSheafData.one_eq_top]
    infer_instance
  apply (SectionCoverProof.pullSection_eq_zero_iff (diagonalPowerInclusion s 0) a).mp
  apply SectionCoverProof.section_eq_zero_of_pullback_cover
    (pullSection (diagonalPowerInclusion s 0) a)
    (fun _ : Empty => (⊥ : (diagonalPowerSubscheme s 0).Opens))
  · ext x
    exact isEmptyElim x
  · intro i
    exact isEmptyElim i

/-- Any supplied affine frame cover is sufficient; in particular, the two
standard P1 tangent frames can be used directly for the source bivector. -/
theorem vanishes_iff_cover_coefficients {X : Scheme} (s : X ⟶ ComplexBase) [IsSeparated s]
    {ι : Type*} (U : ι → X.Opens) (hU : iSup U = ⊤) (hA : ∀ i, IsAffineOpen (U i))
    {E F : OModule X} (e : ∀ i, LocalFrames.OverFrame E (U i))
    (f : ∀ i, LocalFrames.OverFrame F (U i))
    (t : KunnethDegreeZero.Sections s E ⊗[ℂ] KunnethDegreeZero.Sections s F) (k : ℕ) :
    VanishesToOrderAlongDiagonal s (externalTensor s E F)
      (sectionFromValue (KunnethDegreeZero.canonicalMap s s E F t)) k ↔
    ∀ i, Ideal.Quotient.mk ((KaehlerDifferential.ideal ℂ (Coefficients s (U i))) ^ k)
      (coefficientTensorMap s (e i) (f i) t) = 0 := by
  by_cases hk : k = 0
  · subst k
    constructor
    · intro _ i
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      simp
    · intro _
      exact vanishes_order_zero s _ _
  · rw [SectionCoverProof.vanishes_iff_squareCover s U hU _ _ k hk]
    apply forall_congr'
    intro i
    rw [← productOpen_eq]
    exact local_diagonal_zero_iff s (U i) (hA i) (e i) (f i) t k

/-- Convenient membership form for an explicit external-product tensor. -/
theorem vanishes_of_cover_coefficients_mem {X : Scheme}
    (s : X ⟶ ComplexBase) [IsSeparated s]
    {ι : Type*} (U : ι → X.Opens) (hU : iSup U = ⊤) (hA : ∀ i, IsAffineOpen (U i))
    {E F : OModule X} (e : ∀ i, LocalFrames.OverFrame E (U i))
    (f : ∀ i, LocalFrames.OverFrame F (U i))
    (t : KunnethDegreeZero.Sections s E ⊗[ℂ] KunnethDegreeZero.Sections s F) (k : ℕ)
    (ht : ∀ i, coefficientTensorMap s (e i) (f i) t ∈
      (KaehlerDifferential.ideal ℂ (Coefficients s (U i))) ^ k) :
    VanishesToOrderAlongDiagonal s (externalTensor s E F)
      (sectionFromValue (KunnethDegreeZero.canonicalMap s s E F t)) k :=
  (vanishes_iff_cover_coefficients s U hU hA e f t k).mpr
    (fun i => Ideal.Quotient.eq_zero_iff_mem.mpr (ht i))

/-- The same criterion for an already constructed actual global section;
its equality with the explicit finite external tensor is a proved input. -/
theorem section_vanishes_of_cover_coefficients_mem {X : Scheme}
    (s : X ⟶ ComplexBase) [IsSeparated s]
    {ι : Type*} (U : ι → X.Opens) (hU : iSup U = ⊤) (hA : ∀ i, IsAffineOpen (U i))
    {E F : OModule X} (e : ∀ i, LocalFrames.OverFrame E (U i))
    (f : ∀ i, LocalFrames.OverFrame F (U i))
    (B : AlgebraicSection (externalTensor s E F))
    (t : KunnethDegreeZero.Sections s E ⊗[ℂ] KunnethDegreeZero.Sections s F)
    (hB : sectionValue B = KunnethDegreeZero.canonicalMap s s E F t) (k : ℕ)
    (ht : ∀ i, coefficientTensorMap s (e i) (f i) t ∈
      (KaehlerDifferential.ideal ℂ (Coefficients s (U i))) ^ k) :
    VanishesToOrderAlongDiagonal s (externalTensor s E F) B k := by
  have h := vanishes_of_cover_coefficients_mem s U hU hA e f t k ht
  rwa [← hB, sectionFromValue_sectionValue] at h

end LeBrunSalamon.ExternalFrameCoefficients

end

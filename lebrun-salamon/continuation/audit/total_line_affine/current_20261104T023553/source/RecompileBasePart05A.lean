import RecompileBasePart04

noncomputable section

set_option autoImplicit false
open Bundle
open scoped Bundle ContDiff ENNReal
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance 100] LieRing.ofAssociativeRing
open CategoryTheory
open AlgebraicGeometry
open CategoryTheory.Limits


/-!
# Phase 27 -- intrinsic contact structures and actual contact Fano data

This phase supersedes `ContactCandidate` for statements claiming to concern contact manifolds. Its tangent
bundle is dual to the UNIVERSAL cotangent sheaf. Its Levi pairing is induced by the intrinsic bracket. The
Fano condition refers to the determinant of that cotangent sheaf. Existence/construction proofs of those
foundations remain admitted.
-/

namespace LeBrunSalamon.PhaseTwentySeven

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseThree LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentySix

abbrev IntrinsicContactSequence {n : ℕ}
    (X : SmoothProperComplexVariety (2 * n + 1)) :=
  ContactSequence X.scheme n (intrinsicTangentBundle X)

def intrinsicLeviValue {n : ℕ}
    {X : SmoothProperComplexVariety (2 * n + 1)}
    (C : IntrinsicContactSequence X) (U : X.scheme.Opens)
    (u v : SectionsOn C.distribution.sheaf U) : SectionsOn C.line.sheaf U :=
  C.form.app U (tangentBracket X.structureMap U
    (C.inclusion.app U u) (C.inclusion.app U v))

noncomputable section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive

namespace LeviProof

open LeBrunSalamon.PhaseTwentySeven

theorem form_inclusion_apply_zero {n : ℕ}
    {X : SmoothProperComplexVariety (2 * n + 1)}
    (C : IntrinsicContactSequence X) (U : X.scheme.Opens)
    (u : SectionsOn C.distribution.sheaf U) :
    C.form.app U (C.inclusion.app U u) = 0 := by
  have h := congrArg
    (fun f : C.distribution.sheaf ⟶ C.line.sheaf => f.app U u) C.comp_zero
  change C.form.app U (C.inclusion.app U u) = 0 at h
  exact h

theorem alternating {n : ℕ}
    {X : SmoothProperComplexVariety (2 * n + 1)}
    (C : IntrinsicContactSequence X) (U : X.scheme.Opens)
    (u : SectionsOn C.distribution.sheaf U) :
    intrinsicLeviValue C U u u = 0 := by
  unfold intrinsicLeviValue
  rw [TangentBracketProof.self_eq_zero]
  exact map_zero _

theorem smul_right {n : ℕ}
    {X : SmoothProperComplexVariety (2 * n + 1)}
    (C : IntrinsicContactSequence X) (U : X.scheme.Opens)
    (a : RingSections X.scheme U) (u v : SectionsOn C.distribution.sheaf U) :
    intrinsicLeviValue C U u (a • v) = a • intrinsicLeviValue C U u v := by
  let inclusion : SectionsOn C.distribution.sheaf U →ₗ[RingSections X.scheme U]
      SectionsOn (tangentSheaf X.structureMap) U := (C.inclusion.val.app (Opposite.op U)).hom
  let form : SectionsOn (tangentSheaf X.structureMap) U →ₗ[RingSections X.scheme U]
      SectionsOn C.line.sheaf U := (C.form.val.app (Opposite.op U)).hom
  have hz : form (inclusion v) = 0 := form_inclusion_apply_zero C U v
  change form (tangentBracket X.structureMap U (inclusion u) (inclusion (a • v))) =
    a • form (tangentBracket X.structureMap U (inclusion u) (inclusion v))
  rw [map_smul, TangentBracketProof.leibniz, map_add, map_smul, map_smul,
    hz, smul_zero, zero_add]

theorem skew {n : ℕ}
    {X : SmoothProperComplexVariety (2 * n + 1)}
    (C : IntrinsicContactSequence X) (U : X.scheme.Opens)
    (u v : SectionsOn C.distribution.sheaf U) :
    intrinsicLeviValue C U u v = -intrinsicLeviValue C U v u := by
  unfold intrinsicLeviValue
  rw [TangentBracketProof.skew]
  exact map_neg _ _

theorem smul_left {n : ℕ}
    {X : SmoothProperComplexVariety (2 * n + 1)}
    (C : IntrinsicContactSequence X) (U : X.scheme.Opens)
    (a : RingSections X.scheme U) (u v : SectionsOn C.distribution.sheaf U) :
    intrinsicLeviValue C U (a • u) v = a • intrinsicLeviValue C U u v := by
  calc
    intrinsicLeviValue C U (a • u) v = -intrinsicLeviValue C U v (a • u) :=
      skew C U (a • u) v
    _ = -(a • intrinsicLeviValue C U v u) := by rw [smul_right]
    _ = a • intrinsicLeviValue C U u v := by rw [← smul_neg, ← skew C U u v]

end LeviProof

end

theorem intrinsicLevi_alternating {n : ℕ}
    {X : SmoothProperComplexVariety (2 * n + 1)}
    (C : IntrinsicContactSequence X) (U : X.scheme.Opens)
    (u : SectionsOn C.distribution.sheaf U) :
    intrinsicLeviValue C U u u = 0 := by
  exact LeviProof.alternating C U u

theorem intrinsicLevi_smul_left {n : ℕ}
    {X : SmoothProperComplexVariety (2 * n + 1)}
    (C : IntrinsicContactSequence X) (U : X.scheme.Opens)
    (a : RingSections X.scheme U) (u v : SectionsOn C.distribution.sheaf U) :
    intrinsicLeviValue C U (a • u) v = a • intrinsicLeviValue C U u v := by
  exact LeviProof.smul_left C U a u v

theorem intrinsicLevi_smul_right {n : ℕ}
    {X : SmoothProperComplexVariety (2 * n + 1)}
    (C : IntrinsicContactSequence X) (U : X.scheme.Opens)
    (a : RingSections X.scheme U) (u v : SectionsOn C.distribution.sheaf U) :
    intrinsicLeviValue C U u (a • v) = a • intrinsicLeviValue C U u v := by
  exact LeviProof.smul_right C U a u v

set_option backward.isDefEq.respectTransparency false in
def intrinsicLeviPair {n : ℕ}
    {X : SmoothProperComplexVariety (2 * n + 1)}
    (C : IntrinsicContactSequence X) :
    SheafBilinearMap C.distribution.sheaf C.distribution.sheaf C.line.sheaf where
  apply U :=
    { toFun := fun u =>
        { toFun := fun v => intrinsicLeviValue C U u v
          map_add' := by
            intro v w
            simp only [intrinsicLeviValue, map_add]
            erw [tangentBracket_add_right]
            exact map_add _ _ _
          map_smul' := by
            intro a v
            exact intrinsicLevi_smul_right C U a u v }
      map_add' := by
        intro u v
        apply LinearMap.ext
        intro w
        change intrinsicLeviValue C U (u + v) w =
          intrinsicLeviValue C U u w + intrinsicLeviValue C U v w
        simp only [intrinsicLeviValue, map_add]
        erw [tangentBracket_add_left]
        exact map_add _ _ _
      map_smul' := by
        intro a u
        apply LinearMap.ext
        intro v
        exact intrinsicLevi_smul_left C U a u v }
  naturality := by
    intro U V i u v
    change C.line.sheaf.presheaf.map i.op
        (C.form.app V (tangentBracket X.structureMap V (C.inclusion.app V u) (C.inclusion.app V v))) =
      C.form.app U (tangentBracket X.structureMap U
        (C.inclusion.app U (C.distribution.sheaf.presheaf.map i.op u))
        (C.inclusion.app U (C.distribution.sheaf.presheaf.map i.op v)))
    erw [sheafHom_naturality, tangentBracket_restrict,
      sheafHom_naturality, sheafHom_naturality]
    rfl

/-- The Levi morphism is fixed by the bracket, not supplied separately. -/
def intrinsicLeviMorphism {n : ℕ}
    {X : SmoothProperComplexVariety (2 * n + 1)}
    (C : IntrinsicContactSequence X) :
    tensorSheaf C.distribution.sheaf C.distribution.sheaf ⟶ C.line.sheaf :=
  tensorLift (intrinsicLeviPair C)

/-- Perfectness is an actual sheaf-isomorphism condition F ≅ Hom(F,L). -/
def IsIntrinsicContact {n : ℕ}
    {X : SmoothProperComplexVariety (2 * n + 1)}
    (C : IntrinsicContactSequence X) : Prop :=
  IsIso (currySheaf (intrinsicLeviMorphism C))

structure IntrinsicContactStructure {n : ℕ}
    (X : SmoothProperComplexVariety (2 * n + 1)) where
  sequence : IntrinsicContactSequence X
  nondegenerate : IsIntrinsicContact sequence

/-- Smooth proper complex contact Fano geometry, no tangent candidate.
The n≥1 requirement excludes the vacuous rank-zero contact plane. -/
structure ContactFanoManifold (n : ℕ) where
  positiveContactDimension : 1 ≤ n
  variety : SmoothProperComplexVariety (2 * n + 1)
  contact : IntrinsicContactStructure variety
  fano : IsFano variety

def ContactFanoManifold.toLegacyCandidate {n : ℕ}
    (X : ContactFanoManifold n) : ContactCandidate n where
  variety := X.variety
  tangent := intrinsicTangentBundle X.variety
  contactSequence := X.contact.sequence

/-- Underlying-line consequence of Asher Auel, *Cohomological invariants of
line bundle-valued symmetric bilinear forms* (Penn dissertation, 2009),
Proposition 1.10, printed p. 15. Definition 1.7, printed p. 13, identifies
the discriminant line as (L^dual)^n tensor det(E); Proposition 1.10 gives
an isometry with the trivial discriminant form, hence this line is trivial.

Source: https://math.dartmouth.edu/~auel/papers/docs/AUEL_thesisSS.pdf .
The standing assumptions (printed p. 5 and section 1.2, p. 12) are
noetherian, separated, connected, with 2 invertible. We specialize to a
smooth proper connected scheme over C, so all these assumptions hold:
proper implies finite type and separated, C is noetherian, and 1/2 is a
complex scalar. The source's bilinear-space condition is exactly that
the adjoint map is an isomorphism (p. 7). Alternation is explicit below.
The étale formulation has the same underlying locally free module and
global module isomorphism as the Zariski formulation used here.

This published leaf remains admitted. Its sheaf-level specialization
and the proved determinant conversion below await kernel replay. -/
theorem _root_.LeBrunSalamon.PublishedInputs.Step3e.alternatingDiscriminantTrivial
    {X : Scheme} {n : ℕ} (s : X ⟶ ComplexBase)
    [Smooth s] [IsProper s] [ConnectedSpace X]
    (E : AlgebraicVectorBundle X (2 * n)) (L : LineBundle X)
    (b : tensorSheaf E.sheaf E.sheaf ⟶ L.sheaf)
    (hperfect : IsIso (currySheaf b))
    (hAlt : ∀ (U : X.Opens) (u : SectionsOn E.sheaf U),
      b.app U ((tensorPresentation E.sheaf E.sheaf).pair.apply U u u) = 0) :
    Nonempty ((tensorLine (linePower (dualLine L) n) (determinantLine E)).sheaf ≅
      (trivialLine X).sheaf) := by
  sorry

namespace SymplecticDeterminantProof

/-- Evaluation of inverse tensor powers, proved from the actual line-dual
evaluation and tensor associativity. No determinant theorem is used here. -/
theorem dualPower_evaluation {X : Scheme} (L : LineBundle X) (n : ℕ) :
    Nonempty (tensorSheaf (linePower (dualLine L) n).sheaf (linePower L n).sheaf ≅
      structureModule X) := by
  induction n with
  | zero => exact ⟨TensorConstruction.leftUnitIso (structureModule X)⟩
  | succ n ih =>
    obtain ⟨e⟩ := ih
    obtain ⟨ev⟩ := line_dual_evaluation L
    let D := (linePower (dualLine L) n).sheaf
    let P := (linePower L n).sheaf
    let Q := (dualLine L).sheaf
    let R := L.sheaf
    change Nonempty (tensorSheaf (tensorSheaf D Q) (tensorSheaf P R) ≅
      structureModule X)
    exact ⟨SheafTensor.associativityIso D Q (tensorSheaf P R) ≪≫
      tensorIso (Iso.refl D) (SheafTensor.associativityIso Q P R).symm ≪≫
      tensorIso (Iso.refl D)
        (tensorIso (TensorConstruction.commIso Q P) (Iso.refl R)) ≪≫
      tensorIso (Iso.refl D) (SheafTensor.associativityIso P Q R) ≪≫
      (SheafTensor.associativityIso D P (tensorSheaf Q R)).symm ≪≫
      tensorIso e ev ≪≫ TensorConstruction.leftUnitIso (structureModule X)⟩

/-- Tensor cancellation converts the trivial discriminant line to the
determinant identity. This conversion is proved, rather than admitted as
another version of the published theorem. -/
theorem determinant_of_discriminantTrivial {X : Scheme} {n : ℕ}
    (E : AlgebraicVectorBundle X (2 * n)) (L : LineBundle X)
    (h : Nonempty ((tensorLine (linePower (dualLine L) n) (determinantLine E)).sheaf ≅
      (trivialLine X).sheaf)) :
    Nonempty ((determinantLine E).sheaf ≅ (linePower L n).sheaf) := by
  obtain ⟨q⟩ := h
  obtain ⟨ev⟩ := dualPower_evaluation L n
  let D := (linePower (dualLine L) n).sheaf
  let P := (linePower L n).sheaf
  let A := (determinantLine E).sheaf
  exact ⟨(TensorConstruction.leftUnitIso A).symm ≪≫
    tensorIso ev.symm (Iso.refl A) ≪≫
    tensorIso (TensorConstruction.commIso D P) (Iso.refl A) ≪≫
    SheafTensor.associativityIso P D A ≪≫
    tensorIso (Iso.refl P) q ≪≫ TensorConstruction.rightUnitIso P⟩

end SymplecticDeterminantProof

/-- The determinant identity on the actual class of bases used in the
contact argument. Properness, smoothness and connectedness are the proved
projections of X; no unrestricted all-scheme statement is assumed. -/
theorem symplecticDeterminant {d n : ℕ} (X : SmoothProperComplexVariety d)
    (E : AlgebraicVectorBundle X.scheme (2 * n)) (L : LineBundle X.scheme)
    (b : tensorSheaf E.sheaf E.sheaf ⟶ L.sheaf)
    (hperfect : IsIso (currySheaf b))
    (hAlt : ∀ (U : X.scheme.Opens) (u : SectionsOn E.sheaf U),
      b.app U ((tensorPresentation E.sheaf E.sheaf).pair.apply U u u) = 0) :
    Nonempty ((determinantLine E).sheaf ≅ (linePower L n).sheaf) := by
  exact SymplecticDeterminantProof.determinant_of_discriminantTrivial E L
    (LeBrunSalamon.PublishedInputs.Step3e.alternatingDiscriminantTrivial
      X.structureMap E L b hperfect hAlt)

/-- The contact distribution determinant follows from the alternating-form
identity. Its alternation premise is supplied by the already proved Levi
bracket identity, transported through the actual tensor universal pairing.
The amended proof below is a candidate awaiting kernel replay. -/
theorem contact_distribution_determinant {n : ℕ}
    (X : SmoothProperComplexVariety (2 * n + 1))
    (C : IntrinsicContactStructure X) :
    Nonempty ((determinantLine C.sequence.distribution).sheaf ≅
      (linePower C.sequence.line n).sheaf) := by
  refine symplecticDeterminant X
    C.sequence.distribution C.sequence.line (intrinsicLeviMorphism C.sequence)
    C.nondegenerate ?_
  intro U u
  calc
    _ = intrinsicLeviValue C.sequence U u u :=
      congrArg
        (fun p : SheafBilinearMap C.sequence.distribution.sheaf
          C.sequence.distribution.sheaf C.sequence.line.sheaf => p.apply U u u)
        (tensorLift_pair (intrinsicLeviPair C.sequence))
    _ = 0 := intrinsicLevi_alternating C.sequence U u

theorem contact_anticanonical {n : ℕ}
    (X : SmoothProperComplexVariety (2 * n + 1))
    (C : IntrinsicContactStructure X) :
    Nonempty ((anticanonicalLine X).sheaf ≅
      (linePower C.sequence.line (n + 1)).sheaf) := by
  obtain ⟨eT⟩ := tangentDeterminant_anticanonical X
  obtain ⟨eS⟩ := determinant_shortExact C.sequence.distribution
    (intrinsicTangentBundle X) C.sequence.line
    C.sequence.inclusion C.sequence.form C.sequence.comp_zero C.sequence.shortExact
  obtain ⟨eF⟩ := contact_distribution_determinant X C
  obtain ⟨eL⟩ := exteriorSheaf_one C.sequence.line.sheaf
  change Nonempty ((anticanonicalLine X).sheaf ≅
    tensorSheaf (linePower C.sequence.line n).sheaf C.sequence.line.sheaf)
  exact ⟨eT.symm ≪≫ eS ≪≫ tensorIso eF eL⟩

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseFour LeBrunSalamon.PhaseSeven LeBrunSalamon.PhaseTen
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven

namespace ContactAmpleConsequenceProof

theorem contact_fano_iff_contactLine_ample {n : ℕ}
    (X : SmoothProperComplexVariety (2 * n + 1))
    (C : IntrinsicContactStructure X) :
    IsFano X ↔ IsAmpleLine C.sequence.line := by
  obtain ⟨e⟩ := contact_anticanonical X C
  change IsAmpleLine (anticanonicalLine X) ↔ IsAmpleLine C.sequence.line
  exact (ample_iso (anticanonicalLine X) (linePower C.sequence.line (n + 1)) e).trans
    (ample_positivePower_iff C.sequence.line (n + 1) (Nat.succ_pos n))

theorem contactFano_contactLine_ample {n : ℕ} (X : ContactFanoManifold n) :
    IsAmpleLine X.contact.sequence.line := by
  exact (contact_fano_iff_contactLine_ample X.variety X.contact).mp X.fano

end ContactAmpleConsequenceProof

end

theorem contact_fano_iff_contactLine_ample {n : ℕ}
    (X : SmoothProperComplexVariety (2 * n + 1))
    (C : IntrinsicContactStructure X) :
    IsFano X ↔ IsAmpleLine C.sequence.line := by
  exact LeBrunSalamon.PhaseTwentySeven.ContactAmpleConsequenceProof.contact_fano_iff_contactLine_ample (n := n) (X := X) (C := C)

theorem contactFano_contactLine_ample {n : ℕ} (X : ContactFanoManifold n) :
    IsAmpleLine X.contact.sequence.line := by
  exact LeBrunSalamon.PhaseTwentySeven.ContactAmpleConsequenceProof.contactFano_contactLine_ample (n := n) (X := X)

/-- Contact preservation is tested on local sections of F on every
subopen. Only the global vector field is required to be global. -/
def IsGlobalContactField {n : ℕ}
    {X : SmoothProperComplexVariety (2 * n + 1)}
    (C : IntrinsicContactStructure X)
    (v : GlobalSections (tangentSheaf X.structureMap)) : Prop :=
  ∀ (U : X.scheme.Opens) (i : U ⟶ ⊤)
    (u : SectionsOn C.sequence.distribution.sheaf U),
    C.sequence.form.app U
      (tangentBracket X.structureMap U
        ((tangentSheaf X.structureMap).presheaf.map i.op v)
        (C.sequence.inclusion.app U u)) = 0

def GlobalContactField {n : ℕ}
    {X : SmoothProperComplexVariety (2 * n + 1)}
    (C : IntrinsicContactStructure X) :=
  {v : GlobalSections (tangentSheaf X.structureMap) // IsGlobalContactField C v}

def intrinsicHamiltonian {n : ℕ}
    {X : SmoothProperComplexVariety (2 * n + 1)}
    (C : IntrinsicContactStructure X) (v : GlobalContactField C) :
    GlobalSections C.sequence.line.sheaf :=
  C.sequence.form.app ⊤ v.val

/- Source-only Phase 3 integration: intrinsic_injectivity. -/
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
set_option backward.isDefEq.respectTransparency false

namespace IntrinsicHamiltonianInjectivityProof

theorem iso_app_injective {Y : Scheme} {E F : OModule Y}
    (e : E ≅ F) (U : Y.Opens) : Function.Injective (e.hom.app U) := by
  intro a b h
  have hinv (z : SectionsOn E U) : e.inv.app U (e.hom.app U z) = z := by
    change (e.hom ≫ e.inv).app U z = z
    rw [e.hom_inv_id]
    rfl
  exact (hinv a).symm.trans
    ((congrArg (fun z => e.inv.app U z) h).trans (hinv b))

theorem chosenHom_restricted_apply {Y : Scheme} (E F : OModule Y)
    (U : Y.Opens) (φ : SectionsOn (internalHomSheaf E F) U)
    (V : Y.Opens) (i : V ⟶ U) (v : SectionsOn E V) :
    (((internalHomGenericIso E F).hom.app U φ).app (op (Over.mk i))) v =
      (internalHomPresentation E F).evaluate.app V
        ((tensorPresentation (internalHomSheaf E F) E).pair.apply V
          ((internalHomSheaf E F).presheaf.map i.op φ) v) := by
  let e := internalHomGenericIso E F
  have hn := sheafHom_naturality e.hom i φ
  change HomConstruction.Generic.restrictSection i (e.hom.app U φ) =
    e.hom.app V ((internalHomSheaf E F).presheaf.map i.op φ) at hn
  calc
    _ = HomConstruction.Generic.evaluationAt (R := Y.sheaf) E F V
        (HomConstruction.Generic.restrictSection i (e.hom.app U φ)) v := by
      exact (HomConstruction.Generic.evaluationAt_restrict (R := Y.sheaf)
        i (e.hom.app U φ) v).symm
    _ = HomConstruction.Generic.evaluationAt (R := Y.sheaf) E F V
        (e.hom.app V ((internalHomSheaf E F).presheaf.map i.op φ)) v := by
      rw [hn]
    _ = _ := internalHomGenericIso_evaluate_pair E F V
      ((internalHomSheaf E F).presheaf.map i.op φ) v

theorem chosenHom_section_ext {Y : Scheme} (E F : OModule Y)
    (U : Y.Opens) (φ ψ : SectionsOn (internalHomSheaf E F) U)
    (h : ∀ (V : Y.Opens) (i : V ⟶ U) (v : SectionsOn E V),
      (internalHomPresentation E F).evaluate.app V
          ((tensorPresentation (internalHomSheaf E F) E).pair.apply V
            ((internalHomSheaf E F).presheaf.map i.op φ) v) =
        (internalHomPresentation E F).evaluate.app V
          ((tensorPresentation (internalHomSheaf E F) E).pair.apply V
            ((internalHomSheaf E F).presheaf.map i.op ψ) v)) :
    φ = ψ := by
  apply iso_app_injective (internalHomGenericIso E F) U
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  exact (chosenHom_restricted_apply E F U φ W.unop.left W.unop.hom v).trans
    ((h W.unop.left W.unop.hom v).trans
      (chosenHom_restricted_apply E F U ψ W.unop.left W.unop.hom v).symm)

theorem currySheaf_evaluate_pair {Y : Scheme} {Z E F : OModule Y}
    (f : tensorSheaf Z E ⟶ F) (U : Y.Opens)
    (z : SectionsOn Z U) (v : SectionsOn E U) :
    (internalHomPresentation E F).evaluate.app U
        ((tensorPresentation (internalHomSheaf E F) E).pair.apply U
          ((currySheaf f).app U z) v) =
      f.app U ((tensorPresentation Z E).pair.apply U z v) := by
  have h := congrArg (fun g : tensorSheaf Z E ⟶ F =>
      g.app U ((tensorPresentation Z E).pair.apply U z v)) (currySheaf_evaluate f)
  change (internalHomPresentation E F).evaluate.app U
      ((tensorMap (currySheaf f) (𝟙 E)).app U
        ((tensorPresentation Z E).pair.apply U z v)) = _ at h
  rw [tensorMap_apply] at h
  exact h

theorem exists_kernelSection {Y : Scheme} {E F G : OModule Y}
    (i : E ⟶ F) (p : F ⟶ G) (hz : i ≫ p = 0)
    (hex : (ShortComplex.mk i p hz).ShortExact) (U : Y.Opens)
    (w : SectionsOn F U) (hw : p.app U w = 0) :
    ∃ a : SectionsOn E U, i.app U a = w := by
  let ev := SheafOfModules.evaluation Y.ringCatSheaf (op U)
  letI : ev.Additive := by
    dsimp [ev, SheafOfModules.evaluation]
    infer_instance
  letI : PreservesFiniteLimits ev :=
    inferInstanceAs (PreservesFiniteLimits
      (SheafOfModules.evaluation Y.ringCatSheaf (op U)))
  have he : ((ShortComplex.mk i p hz).map ev).Exact :=
    ((ShortComplex.mk i p hz).map ev).exact_of_f_is_kernel
      (KernelFork.mapIsLimit _ hex.fIsKernel ev)
  exact (((ShortComplex.mk i p hz).map ev).moduleCat_exact_iff.mp he) w hw

theorem intrinsicLevi_curry_evaluate {n : ℕ}
    {X : SmoothProperComplexVariety (2 * n + 1)}
    (C : IntrinsicContactSequence X) (U : X.scheme.Opens)
    (a b : SectionsOn C.distribution.sheaf U) :
    (internalHomPresentation C.distribution.sheaf C.line.sheaf).evaluate.app U
        ((tensorPresentation
          (internalHomSheaf C.distribution.sheaf C.line.sheaf) C.distribution.sheaf).pair.apply U
          ((currySheaf (intrinsicLeviMorphism C)).app U a) b) =
      intrinsicLeviValue C U a b := by
  calc
    _ = (intrinsicLeviMorphism C).app U
        ((tensorPresentation C.distribution.sheaf C.distribution.sheaf).pair.apply U a b) :=
      currySheaf_evaluate_pair (intrinsicLeviMorphism C) U a b
    _ = _ := congrArg
      (fun p : SheafBilinearMap C.distribution.sheaf C.distribution.sheaf C.line.sheaf =>
        p.apply U a b) (tensorLift_pair (intrinsicLeviPair C))

theorem levi_section_eq_zero {n : ℕ}
    {X : SmoothProperComplexVariety (2 * n + 1)}
    (C : IntrinsicContactStructure X) (U : X.scheme.Opens)
    (a : SectionsOn C.sequence.distribution.sheaf U)
    (h : ∀ (V : X.scheme.Opens) (i : V ⟶ U)
      (b : SectionsOn C.sequence.distribution.sheaf V),
      intrinsicLeviValue C.sequence V
        (C.sequence.distribution.sheaf.presheaf.map i.op a) b = 0) :
    a = 0 := by
  let κ := currySheaf (intrinsicLeviMorphism C.sequence)
  have hκ : κ.app U a = 0 := by
    apply chosenHom_section_ext C.sequence.distribution.sheaf C.sequence.line.sheaf U
    intro V i b
    have hn := sheafHom_naturality κ i a
    calc
      _ = (internalHomPresentation C.sequence.distribution.sheaf C.sequence.line.sheaf).evaluate.app V
          ((tensorPresentation
            (internalHomSheaf C.sequence.distribution.sheaf C.sequence.line.sheaf)
            C.sequence.distribution.sheaf).pair.apply V
            (κ.app V (C.sequence.distribution.sheaf.presheaf.map i.op a)) b) := by
        rw [hn]
      _ = intrinsicLeviValue C.sequence V
          (C.sequence.distribution.sheaf.presheaf.map i.op a) b :=
        intrinsicLevi_curry_evaluate C.sequence V _ b
      _ = 0 := h V i b
      _ = _ := by simp only [map_zero, LinearMap.zero_apply]
  letI : IsIso κ := C.nondegenerate
  apply iso_app_injective (asIso κ) U
  change κ.app U a = κ.app U 0
  simpa only [map_zero] using hκ

theorem local_contactField_eq_zero {n : ℕ}
    {X : SmoothProperComplexVariety (2 * n + 1)}
    (C : IntrinsicContactStructure X) (U : X.scheme.Opens)
    (v : SectionsOn (tangentSheaf X.structureMap) U)
    (hv : ∀ (V : X.scheme.Opens) (i : V ⟶ U)
      (b : SectionsOn C.sequence.distribution.sheaf V),
      C.sequence.form.app V (tangentBracket X.structureMap V
        ((tangentSheaf X.structureMap).presheaf.map i.op v)
        (C.sequence.inclusion.app V b)) = 0)
    (hzero : C.sequence.form.app U v = 0) : v = 0 := by
  obtain ⟨a, ha⟩ := exists_kernelSection C.sequence.inclusion C.sequence.form
    C.sequence.comp_zero C.sequence.shortExact U v hzero
  have ha0 : a = 0 := by
    apply levi_section_eq_zero C U a
    intro V i b
    have hrest : C.sequence.inclusion.app V
        (C.sequence.distribution.sheaf.presheaf.map i.op a) =
        (tangentSheaf X.structureMap).presheaf.map i.op v := by
      calc
        _ = (tangentSheaf X.structureMap).presheaf.map i.op
            (C.sequence.inclusion.app U a) :=
          (sheafHom_naturality C.sequence.inclusion i a).symm
        _ = _ := congrArg
          (fun z : SectionsOn (tangentSheaf X.structureMap) U =>
            (tangentSheaf X.structureMap).presheaf.map i.op z) ha
    change C.sequence.form.app V (tangentBracket X.structureMap V
      (C.sequence.inclusion.app V (C.sequence.distribution.sheaf.presheaf.map i.op a))
      (C.sequence.inclusion.app V b)) = 0
    rw [hrest]
    exact hv V i b
  calc
    v = C.sequence.inclusion.app U a := ha.symm
    _ = 0 := by rw [ha0, map_zero]

theorem local_contactField_unique {n : ℕ}
    {X : SmoothProperComplexVariety (2 * n + 1)}
    (C : IntrinsicContactStructure X) (U : X.scheme.Opens)
    (v w : SectionsOn (tangentSheaf X.structureMap) U)
    (hv : ∀ (V : X.scheme.Opens) (i : V ⟶ U)
      (b : SectionsOn C.sequence.distribution.sheaf V),
      C.sequence.form.app V (tangentBracket X.structureMap V
        ((tangentSheaf X.structureMap).presheaf.map i.op v)
        (C.sequence.inclusion.app V b)) = 0)
    (hw : ∀ (V : X.scheme.Opens) (i : V ⟶ U)
      (b : SectionsOn C.sequence.distribution.sheaf V),
      C.sequence.form.app V (tangentBracket X.structureMap V
        ((tangentSheaf X.structureMap).presheaf.map i.op w)
        (C.sequence.inclusion.app V b)) = 0)
    (hvalue : C.sequence.form.app U v = C.sequence.form.app U w) : v = w := by
  apply sub_eq_zero.mp
  apply local_contactField_eq_zero C U (v - w)
  · intro V i b
    have h := congrArg (fun z : SectionsOn (tangentSheaf X.structureMap) V =>
        C.sequence.form.app V z)
      (tangentBracket_add_left X.structureMap V
        ((tangentSheaf X.structureMap).presheaf.map i.op v -
          (tangentSheaf X.structureMap).presheaf.map i.op w)
        ((tangentSheaf X.structureMap).presheaf.map i.op w)
        (C.sequence.inclusion.app V b))
    simp only [sub_add_cancel, map_add, hv V i b, hw V i b, add_zero] at h
    simpa only [map_sub] using h.symm
  · rw [map_sub, hvalue, sub_self]

theorem intrinsicHamiltonian_injective {n : ℕ}
    (X : SmoothProperComplexVariety (2 * n + 1))
    (C : IntrinsicContactStructure X) :
    Function.Injective (intrinsicHamiltonian C) := by
  intro v w h
  apply Subtype.ext
  change C.sequence.form.app ⊤ v.val = C.sequence.form.app ⊤ w.val at h
  exact local_contactField_unique C ⊤ v.val w.val v.property w.property h

end IntrinsicHamiltonianInjectivityProof
end


/- Source-only Phase 3 integration: intrinsic_local_lifts. -/
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
set_option backward.isDefEq.respectTransparency false

namespace SheafModuleLocalLiftsProof

theorem epi_isLocallySurjective {Y : Scheme} {E F : OModule Y}
    (p : E ⟶ F) [Epi p] :
    PresheafOfModules.IsLocallySurjective (_root_.Opens.grothendieckTopology Y)
      p.val := by
  let J := _root_.Opens.grothendieckTopology Y
  let R := Y.ringCatSheaf
  let L := PresheafOfModules.sheafification (𝟙 R.obj)
  let ε := (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit
  let e := factorThruImage p.val
  let j := image.ι p.val
  let q := L.map j ≫ ε.app F
  have hfac : L.map e ≫ q = ε.app E ≫ p := by
    calc
      L.map e ≫ q = L.map (e ≫ j) ≫ ε.app F := by
        dsimp only [q]
        rw [Functor.map_comp, Category.assoc]
      _ = L.map p.val ≫ ε.app F := by rw [image.fac]
      _ = ε.app E ≫ p := ε.naturality p
  letI : Mono j := by
    dsimp only [j]
    infer_instance
  letI : PreservesFiniteLimits L := by
    dsimp only [L]
    infer_instance
  letI : Mono (L.map j) := L.map_mono j
  letI : IsIso (ε.app F) := by
    dsimp only [ε]
    infer_instance
  letI : Mono (ε.app F) :=
    SplitMono.mono (f := ε.app F)
      { retraction := inv (ε.app F)
        id := IsIso.hom_inv_id (ε.app F) }
  letI : Mono q := by
    dsimp only [q]
    exact mono_comp (L.map j) (ε.app F)
  letI : Epi q := epi_of_epi_fac hfac
  letI : IsIso q := isIso_of_mono_of_epi q
  have he : Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf R).map (L.map e)) := by
    change Sheaf.IsLocallySurjective
      ((presheafToSheaf J AddCommGrpCat).map ((PresheafOfModules.toPresheaf R.obj).map e))
    apply (Presheaf.isLocallySurjective_presheafToSheaf_map_iff
      (J := J) ((PresheafOfModules.toPresheaf R.obj).map e)).mpr
    apply Presheaf.isLocallySurjective_of_surjective
    intro W
    exact PresheafOfModules.surjective_of_epi e W
  letI : Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf R).map (L.map e)) := he
  have hp : p = inv (ε.app E) ≫ L.map e ≫ q := by
    apply (cancel_epi (ε.app E)).1
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    exact hfac.symm
  change Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf R).map p)
  rw [hp, Functor.map_comp, Functor.map_comp]
  infer_instance

theorem epi_local_lift {Y : Scheme} {E F : OModule Y}
    (p : E ⟶ F) [Epi p] (U : Y.Opens) (s : SectionsOn F U)
    (x : Y) (hx : x ∈ U) :
    ∃ (V : Y.Opens) (i : V ⟶ U), x ∈ V ∧
      ∃ v : SectionsOn E V, p.app V v = F.presheaf.map i.op s := by
  letI : PresheafOfModules.IsLocallySurjective
      (_root_.Opens.grothendieckTopology Y) p.val :=
    epi_isLocallySurjective p
  obtain ⟨V, hVU, ⟨v, hv⟩, hxV⟩ :=
    (TopCat.Presheaf.isLocallySurjective_iff
      ((PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map p.val)).mp
        inferInstance U s x hx
  exact ⟨V, homOfLE hVU, hxV, v, hv⟩

theorem contact_form_local_lift {n : ℕ}
    {X : SmoothProperComplexVariety (2 * n + 1)}
    (C : IntrinsicContactStructure X) (U : X.scheme.Opens)
    (s : SectionsOn C.sequence.line.sheaf U) (x : X.scheme) (hx : x ∈ U) :
    ∃ (V : X.scheme.Opens) (i : V ⟶ U), x ∈ V ∧
      ∃ v : SectionsOn (tangentSheaf X.structureMap) V,
        C.sequence.form.app V v = C.sequence.line.sheaf.presheaf.map i.op s := by
  letI : Epi C.sequence.form := C.sequence.shortExact.epi_g
  exact epi_local_lift C.sequence.form U s x hx

end SheafModuleLocalLiftsProof
end


/- Source-only Phase 3 integration: intrinsic_local_correction. -/
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
set_option backward.isDefEq.respectTransparency false

namespace IntrinsicHamiltonianSurjectivityProof

theorem tangentBracket_sub_left {Y S : Scheme} (s : Y ⟶ S)
    (U : Y.Opens) (v w z : SectionsOn (tangentSheaf s) U) :
    tangentBracket s U (v - w) z =
      tangentBracket s U v z - tangentBracket s U w z := by
  apply eq_sub_of_add_eq
  rw [← tangentBracket_add_left, sub_add_cancel]

def defectLinear {n : ℕ}
    {X : SmoothProperComplexVariety (2 * n + 1)}
    (C : IntrinsicContactSequence X) (U : X.scheme.Opens)
    (v : SectionsOn (tangentSheaf X.structureMap) U) :
    SectionsOn C.distribution.sheaf U →ₗ[RingSections X.scheme U]
      SectionsOn C.line.sheaf U where
  toFun u := C.form.app U
    (tangentBracket X.structureMap U v (C.inclusion.app U u))
  map_add' := by
    intro u w
    change C.form.app U
        (tangentBracket X.structureMap U v (C.inclusion.app U (u + w))) = _
    rw [map_add, tangentBracket_add_right, map_add]
  map_smul' := by
    intro a u
    let inclusion : SectionsOn C.distribution.sheaf U →ₗ[RingSections X.scheme U]
        SectionsOn (tangentSheaf X.structureMap) U :=
      (C.inclusion.val.app (op U)).hom
    let form : SectionsOn (tangentSheaf X.structureMap) U →ₗ[RingSections X.scheme U]
        SectionsOn C.line.sheaf U := (C.form.val.app (op U)).hom
    have hz : form (inclusion u) = 0 := LeviProof.form_inclusion_apply_zero C U u
    change form (tangentBracket X.structureMap U v (inclusion (a • u))) =
      a • form (tangentBracket X.structureMap U v (inclusion u))
    rw [map_smul, tangentBracket_leibniz, map_add, map_smul, map_smul,
      hz, smul_zero, zero_add]

theorem defectLinear_restrict {n : ℕ}
    {X : SmoothProperComplexVariety (2 * n + 1)}
    (C : IntrinsicContactSequence X) {U V : X.scheme.Opens} (i : V ⟶ U)
    (v : SectionsOn (tangentSheaf X.structureMap) U)
    (u : SectionsOn C.distribution.sheaf U) :
    C.line.sheaf.presheaf.map i.op (defectLinear C U v u) =
      defectLinear C V ((tangentSheaf X.structureMap).presheaf.map i.op v)
        (C.distribution.sheaf.presheaf.map i.op u) := by
  change C.line.sheaf.presheaf.map i.op
      (C.form.app U (tangentBracket X.structureMap U v (C.inclusion.app U u))) =
    C.form.app V (tangentBracket X.structureMap V
      ((tangentSheaf X.structureMap).presheaf.map i.op v)
      (C.inclusion.app V (C.distribution.sheaf.presheaf.map i.op u)))
  erw [sheafHom_naturality, tangentBracket_restrict, sheafHom_naturality]
  rfl

def defectGenericSection {n : ℕ}
    {X : SmoothProperComplexVariety (2 * n + 1)}
    (C : IntrinsicContactSequence X) (U : X.scheme.Opens)
    (v : SectionsOn (tangentSheaf X.structureMap) U) :
    HomConstruction.Generic.Section (R := X.scheme.sheaf)
      C.distribution.sheaf C.line.sheaf U where
  app W := ModuleCat.ofHom
    (defectLinear C W.unop.left
      ((tangentSheaf X.structureMap).presheaf.map W.unop.hom.op v))
  naturality := by
    intro V W i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro u
    change defectLinear C W.unop.left
        ((tangentSheaf X.structureMap).presheaf.map W.unop.hom.op v)
        (C.distribution.sheaf.presheaf.map i.unop.left.op u) =
      C.line.sheaf.presheaf.map i.unop.left.op
        (defectLinear C V.unop.left
          ((tangentSheaf X.structureMap).presheaf.map V.unop.hom.op v) u)
    have hc : (tangentSheaf X.structureMap).presheaf.map i.unop.left.op
        ((tangentSheaf X.structureMap).presheaf.map V.unop.hom.op v) =
        (tangentSheaf X.structureMap).presheaf.map W.unop.hom.op v :=
      (LocalDerivationProof.moduleRestrict_comp (tangentSheaf X.structureMap)
        i.unop.left V.unop.hom v).trans
        (congrArg (fun f => (tangentSheaf X.structureMap).presheaf.map f.op v)
          (Over.w i.unop))
    exact (congrArg (fun z => defectLinear C W.unop.left z
      (C.distribution.sheaf.presheaf.map i.unop.left.op u)) hc.symm).trans
      (defectLinear_restrict C i.unop.left
        ((tangentSheaf X.structureMap).presheaf.map V.unop.hom.op v) u).symm

def defectSection {n : ℕ}
    {X : SmoothProperComplexVariety (2 * n + 1)}
    (C : IntrinsicContactSequence X) (U : X.scheme.Opens)
    (v : SectionsOn (tangentSheaf X.structureMap) U) :
    SectionsOn (internalHomSheaf C.distribution.sheaf C.line.sheaf) U :=
  (internalHomGenericIso C.distribution.sheaf C.line.sheaf).inv.app U
    (defectGenericSection C U v)

theorem defectSection_generic {n : ℕ}
    {X : SmoothProperComplexVariety (2 * n + 1)}
    (C : IntrinsicContactSequence X) (U : X.scheme.Opens)
    (v : SectionsOn (tangentSheaf X.structureMap) U) :
    (internalHomGenericIso C.distribution.sheaf C.line.sheaf).hom.app U
        (defectSection C U v) = defectGenericSection C U v := by
  let e := internalHomGenericIso C.distribution.sheaf C.line.sheaf
  have h := congrArg
    (fun f : HomConstruction.Generic.object (R := X.scheme.sheaf)
        C.distribution.sheaf C.line.sheaf ⟶
        HomConstruction.Generic.object (R := X.scheme.sheaf)
          C.distribution.sheaf C.line.sheaf => f.val.app (op U) (defectGenericSection C U v))
    e.inv_hom_id
  change e.hom.app U (e.inv.app U (defectGenericSection C U v)) =
    defectGenericSection C U v at h
  exact h

theorem chosenHom_restricted_apply {Y : Scheme} (E F : OModule Y)
    (U : Y.Opens) (φ : SectionsOn (internalHomSheaf E F) U)
    (V : Y.Opens) (i : V ⟶ U) (u : SectionsOn E V) :
    (((internalHomGenericIso E F).hom.app U φ).app (op (Over.mk i))) u =
      (internalHomPresentation E F).evaluate.app V
        ((tensorPresentation (internalHomSheaf E F) E).pair.apply V
          ((internalHomSheaf E F).presheaf.map i.op φ) u) := by
  let e := internalHomGenericIso E F
  have hn := sheafHom_naturality e.hom i φ
  change HomConstruction.Generic.restrictSection i (e.hom.app U φ) =
    e.hom.app V ((internalHomSheaf E F).presheaf.map i.op φ) at hn
  calc
    _ = HomConstruction.Generic.evaluationAt (R := Y.sheaf) E F V
        (HomConstruction.Generic.restrictSection i (e.hom.app U φ)) u :=
      (HomConstruction.Generic.evaluationAt_restrict (R := Y.sheaf)
        i (e.hom.app U φ) u).symm
    _ = HomConstruction.Generic.evaluationAt (R := Y.sheaf) E F V
        (e.hom.app V ((internalHomSheaf E F).presheaf.map i.op φ)) u := by
      rw [hn]
    _ = _ := internalHomGenericIso_evaluate_pair E F V
      ((internalHomSheaf E F).presheaf.map i.op φ) u

theorem defectSection_evaluate {n : ℕ}
    {X : SmoothProperComplexVariety (2 * n + 1)}
    (C : IntrinsicContactSequence X) (U : X.scheme.Opens)
    (v : SectionsOn (tangentSheaf X.structureMap) U)
    (V : X.scheme.Opens) (i : V ⟶ U) (u : SectionsOn C.distribution.sheaf V) :
    (internalHomPresentation C.distribution.sheaf C.line.sheaf).evaluate.app V
        ((tensorPresentation
          (internalHomSheaf C.distribution.sheaf C.line.sheaf) C.distribution.sheaf).pair.apply V
          ((internalHomSheaf C.distribution.sheaf C.line.sheaf).presheaf.map i.op
            (defectSection C U v)) u) =
      defectLinear C V ((tangentSheaf X.structureMap).presheaf.map i.op v) u := by
  calc
    _ = (((internalHomGenericIso C.distribution.sheaf C.line.sheaf).hom.app U
        (defectSection C U v)).app (op (Over.mk i))) u :=
      (chosenHom_restricted_apply C.distribution.sheaf C.line.sheaf U
        (defectSection C U v) V i u).symm
    _ = _ := by rw [defectSection_generic]; rfl

theorem currySheaf_evaluate_pair {Y : Scheme} {Z E F : OModule Y}
    (f : tensorSheaf Z E ⟶ F) (U : Y.Opens)
    (z : SectionsOn Z U) (u : SectionsOn E U) :
    (internalHomPresentation E F).evaluate.app U
        ((tensorPresentation (internalHomSheaf E F) E).pair.apply U
          ((currySheaf f).app U z) u) =
      f.app U ((tensorPresentation Z E).pair.apply U z u) := by
  have h := congrArg (fun g : tensorSheaf Z E ⟶ F =>
      g.app U ((tensorPresentation Z E).pair.apply U z u)) (currySheaf_evaluate f)
  change (internalHomPresentation E F).evaluate.app U
      ((tensorMap (currySheaf f) (𝟙 E)).app U
        ((tensorPresentation Z E).pair.apply U z u)) = _ at h
  rw [tensorMap_apply] at h
  exact h

theorem intrinsicLevi_curry_evaluate {n : ℕ}
    {X : SmoothProperComplexVariety (2 * n + 1)}
    (C : IntrinsicContactSequence X) (U : X.scheme.Opens)
    (a b : SectionsOn C.distribution.sheaf U) :
    (internalHomPresentation C.distribution.sheaf C.line.sheaf).evaluate.app U
        ((tensorPresentation
          (internalHomSheaf C.distribution.sheaf C.line.sheaf) C.distribution.sheaf).pair.apply U
          ((currySheaf (intrinsicLeviMorphism C)).app U a) b) =
      intrinsicLeviValue C U a b := by
  calc
    _ = (intrinsicLeviMorphism C).app U
        ((tensorPresentation C.distribution.sheaf C.distribution.sheaf).pair.apply U a b) :=
      currySheaf_evaluate_pair (intrinsicLeviMorphism C) U a b
    _ = _ := congrArg
      (fun p : SheafBilinearMap C.distribution.sheaf C.distribution.sheaf C.line.sheaf =>
        p.apply U a b) (tensorLift_pair (intrinsicLeviPair C))

def leviIso {n : ℕ} {X : SmoothProperComplexVariety (2 * n + 1)}
    (C : IntrinsicContactStructure X) :
    C.sequence.distribution.sheaf ≅
      internalHomSheaf C.sequence.distribution.sheaf C.sequence.line.sheaf :=
  letI : IsIso (currySheaf (intrinsicLeviMorphism C.sequence)) := C.nondegenerate
  asIso (currySheaf (intrinsicLeviMorphism C.sequence))

def correction {n : ℕ} {X : SmoothProperComplexVariety (2 * n + 1)}
    (C : IntrinsicContactStructure X) (U : X.scheme.Opens)
    (v : SectionsOn (tangentSheaf X.structureMap) U) :
    SectionsOn C.sequence.distribution.sheaf U :=
  (leviIso C).inv.app U (defectSection C.sequence U v)

theorem correction_spec {n : ℕ} {X : SmoothProperComplexVariety (2 * n + 1)}
    (C : IntrinsicContactStructure X) (U : X.scheme.Opens)
    (v : SectionsOn (tangentSheaf X.structureMap) U) :
    (currySheaf (intrinsicLeviMorphism C.sequence)).app U (correction C U v) =
      defectSection C.sequence U v := by
  have h := congrArg
    (fun f : internalHomSheaf C.sequence.distribution.sheaf C.sequence.line.sheaf ⟶
        internalHomSheaf C.sequence.distribution.sheaf C.sequence.line.sheaf =>
      f.app U (defectSection C.sequence U v)) (leviIso C).inv_hom_id
  change (currySheaf (intrinsicLeviMorphism C.sequence)).app U (correction C U v) =
    defectSection C.sequence U v at h
  exact h

theorem correction_levi {n : ℕ} {X : SmoothProperComplexVariety (2 * n + 1)}
    (C : IntrinsicContactStructure X) (U : X.scheme.Opens)
    (v : SectionsOn (tangentSheaf X.structureMap) U)
    (V : X.scheme.Opens) (i : V ⟶ U)
    (u : SectionsOn C.sequence.distribution.sheaf V) :
    intrinsicLeviValue C.sequence V
        (C.sequence.distribution.sheaf.presheaf.map i.op (correction C U v)) u =
      defectLinear C.sequence V ((tangentSheaf X.structureMap).presheaf.map i.op v) u := by
  let κ := currySheaf (intrinsicLeviMorphism C.sequence)
  let ev : SectionsOn
      (internalHomSheaf C.sequence.distribution.sheaf C.sequence.line.sheaf) V →
      SectionsOn C.sequence.line.sheaf V := fun φ =>
    (internalHomPresentation C.sequence.distribution.sheaf C.sequence.line.sheaf).evaluate.app V
      ((tensorPresentation
        (internalHomSheaf C.sequence.distribution.sheaf C.sequence.line.sheaf)
        C.sequence.distribution.sheaf).pair.apply V φ u)
  calc
    _ = ev (κ.app V (C.sequence.distribution.sheaf.presheaf.map i.op
        (correction C U v))) :=
      (intrinsicLevi_curry_evaluate C.sequence V _ u).symm
    _ = ev ((internalHomSheaf C.sequence.distribution.sheaf C.sequence.line.sheaf).presheaf.map
        i.op (κ.app U (correction C U v))) :=
      congrArg ev (sheafHom_naturality κ i (correction C U v)).symm
    _ = ev ((internalHomSheaf C.sequence.distribution.sheaf C.sequence.line.sheaf).presheaf.map
        i.op (defectSection C.sequence U v)) :=
      congrArg (fun φ => ev
        ((internalHomSheaf C.sequence.distribution.sheaf C.sequence.line.sheaf).presheaf.map
          i.op φ)) (correction_spec C U v)
    _ = _ := defectSection_evaluate C.sequence U v V i u

def correctedLift {n : ℕ} {X : SmoothProperComplexVariety (2 * n + 1)}
    (C : IntrinsicContactStructure X) (U : X.scheme.Opens)
    (v : SectionsOn (tangentSheaf X.structureMap) U) :
    SectionsOn (tangentSheaf X.structureMap) U :=
  @Sub.sub (SectionsOn (tangentSheaf X.structureMap) U) inferInstance
    v (C.sequence.inclusion.app U (correction C U v))

theorem correctedLift_value {n : ℕ} {X : SmoothProperComplexVariety (2 * n + 1)}
    (C : IntrinsicContactStructure X) (U : X.scheme.Opens)
    (v : SectionsOn (tangentSheaf X.structureMap) U) :
    C.sequence.form.app U (correctedLift C U v) = C.sequence.form.app U v := by
  change C.sequence.form.app U
    (@Sub.sub (SectionsOn (tangentSheaf X.structureMap) U) inferInstance
      v (C.sequence.inclusion.app U (correction C U v))) = C.sequence.form.app U v
  erw [map_sub, LeviProof.form_inclusion_apply_zero, sub_zero]

theorem correctedLift_isContact {n : ℕ} {X : SmoothProperComplexVariety (2 * n + 1)}
    (C : IntrinsicContactStructure X) (U : X.scheme.Opens)
    (v : SectionsOn (tangentSheaf X.structureMap) U)
    (V : X.scheme.Opens) (i : V ⟶ U)
    (u : SectionsOn C.sequence.distribution.sheaf V) :
    C.sequence.form.app V (tangentBracket X.structureMap V
      ((tangentSheaf X.structureMap).presheaf.map i.op (correctedLift C U v))
      (C.sequence.inclusion.app V u)) = 0 := by
  change C.sequence.form.app V (tangentBracket X.structureMap V
    ((tangentSheaf X.structureMap).presheaf.map i.op
      (@Sub.sub (SectionsOn (tangentSheaf X.structureMap) U) inferInstance
        v (C.sequence.inclusion.app U (correction C U v))))
    (C.sequence.inclusion.app V u)) = 0
  erw [map_sub, sheafHom_naturality, tangentBracket_sub_left, map_sub]
  change defectLinear C.sequence V ((tangentSheaf X.structureMap).presheaf.map i.op v) u -
    intrinsicLeviValue C.sequence V
      (C.sequence.distribution.sheaf.presheaf.map i.op (correction C U v)) u = 0
  rw [correction_levi, sub_self]

end IntrinsicHamiltonianSurjectivityProof
end


/- Source-only Phase 3 integration: intrinsic_gluing. -/
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
set_option backward.isDefEq.respectTransparency false
open LeBrunSalamon.PhaseTwentySeven.IntrinsicHamiltonianSurjectivityProof
open LeBrunSalamon.PhaseTwentySeven.SheafModuleLocalLiftsProof

namespace IntrinsicHamiltonianGluingProof

theorem local_contactField_restrict {n : ℕ}
    {X : SmoothProperComplexVariety (2 * n + 1)}
    (C : IntrinsicContactStructure X) {U V : X.scheme.Opens} (i : V ⟶ U)
    (v : SectionsOn (tangentSheaf X.structureMap) U)
    (hv : ∀ (W : X.scheme.Opens) (j : W ⟶ U)
      (u : SectionsOn C.sequence.distribution.sheaf W),
      C.sequence.form.app W (tangentBracket X.structureMap W
        ((tangentSheaf X.structureMap).presheaf.map j.op v)
        (C.sequence.inclusion.app W u)) = 0) :
    ∀ (W : X.scheme.Opens) (j : W ⟶ V)
      (u : SectionsOn C.sequence.distribution.sheaf W),
      C.sequence.form.app W (tangentBracket X.structureMap W
        ((tangentSheaf X.structureMap).presheaf.map j.op
          ((tangentSheaf X.structureMap).presheaf.map i.op v))
        (C.sequence.inclusion.app W u)) = 0 := by
  intro W j u
  exact (congrArg (fun z => C.sequence.form.app W
    (tangentBracket X.structureMap W z (C.sequence.inclusion.app W u)))
    (LocalDerivationProof.moduleRestrict_comp (tangentSheaf X.structureMap) j i v)).trans
    (hv W (j ≫ i) u)

theorem intrinsicHamiltonian_surjective {n : ℕ}
    (X : SmoothProperComplexVariety (2 * n + 1))
    (C : IntrinsicContactStructure X) :
    Function.Surjective (intrinsicHamiltonian C) := by
  classical
  intro s
  have hlocal (x : X.scheme) := contact_form_local_lift C ⊤ s x (by trivial)
  choose V i hx v hv using hlocal
  let c : ∀ x : X.scheme, SectionsOn (tangentSheaf X.structureMap) (V x) :=
    fun x => correctedLift C (V x) (v x)
  have hcvalue (x : X.scheme) :
      C.sequence.form.app (V x) (c x) =
        C.sequence.line.sheaf.presheaf.map (i x).op s :=
    (correctedLift_value C (V x) (v x)).trans (hv x)
  have hcover : (⊤ : X.scheme.Opens) ≤ iSup V := by
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩
  let T : TopCat.Sheaf AddCommGrpCat X.scheme :=
    (SheafOfModules.toSheaf X.scheme.ringCatSheaf).obj (tangentSheaf X.structureMap)
  let L : TopCat.Sheaf AddCommGrpCat X.scheme :=
    (SheafOfModules.toSheaf X.scheme.ringCatSheaf).obj C.sequence.line.sheaf
  have hc : TopCat.Presheaf.IsCompatible T.obj V c := by
    intro x y
    let W := V x ⊓ V y
    let a : W ⟶ V x := TopologicalSpace.Opens.infLELeft (V x) (V y)
    let b : W ⟶ V y := TopologicalSpace.Opens.infLERight (V x) (V y)
    change (tangentSheaf X.structureMap).presheaf.map a.op (c x) =
      (tangentSheaf X.structureMap).presheaf.map b.op (c y)
    apply IntrinsicHamiltonianInjectivityProof.local_contactField_unique C W
    · exact local_contactField_restrict C a (c x)
        (correctedLift_isContact C (V x) (v x))
    · exact local_contactField_restrict C b (c y)
        (correctedLift_isContact C (V y) (v y))
    · calc
        C.sequence.form.app W ((tangentSheaf X.structureMap).presheaf.map a.op (c x)) =
            C.sequence.line.sheaf.presheaf.map a.op (C.sequence.form.app (V x) (c x)) :=
          (sheafHom_naturality C.sequence.form a (c x)).symm
        _ = C.sequence.line.sheaf.presheaf.map a.op
            (C.sequence.line.sheaf.presheaf.map (i x).op s) :=
          congrArg (fun z => C.sequence.line.sheaf.presheaf.map a.op z) (hcvalue x)
        _ = C.sequence.line.sheaf.presheaf.map (a ≫ i x).op s :=
          LocalDerivationProof.moduleRestrict_comp C.sequence.line.sheaf a (i x) s
        _ = C.sequence.line.sheaf.presheaf.map (b ≫ i y).op s :=
          congrArg (fun j : W ⟶ ⊤ => C.sequence.line.sheaf.presheaf.map j.op s)
            (Subsingleton.elim _ _)
        _ = C.sequence.line.sheaf.presheaf.map b.op
            (C.sequence.line.sheaf.presheaf.map (i y).op s) :=
          (LocalDerivationProof.moduleRestrict_comp C.sequence.line.sheaf b (i y) s).symm
        _ = C.sequence.line.sheaf.presheaf.map b.op (C.sequence.form.app (V y) (c y)) :=
          congrArg (fun z => C.sequence.line.sheaf.presheaf.map b.op z) (hcvalue y).symm
        _ = C.sequence.form.app W ((tangentSheaf X.structureMap).presheaf.map b.op (c y)) :=
          sheafHom_naturality C.sequence.form b (c y)
  obtain ⟨g, hg, _⟩ := TopCat.Sheaf.existsUnique_gluing' T V ⊤ i hcover c hc
  have hgvalue : C.sequence.form.app ⊤ g = s := by
    apply TopCat.Sheaf.eq_of_locally_eq' L V ⊤ i hcover
    intro x
    calc
      C.sequence.line.sheaf.presheaf.map (i x).op (C.sequence.form.app ⊤ g) =
          C.sequence.form.app (V x) ((tangentSheaf X.structureMap).presheaf.map (i x).op g) :=
        sheafHom_naturality C.sequence.form (i x) g
      _ = C.sequence.form.app (V x) (c x) :=
        congrArg (fun z => C.sequence.form.app (V x) z) (hg x)
      _ = C.sequence.line.sheaf.presheaf.map (i x).op s := hcvalue x
  have hgcontact : IsGlobalContactField C g := by
    intro U j u
    apply TopCat.Presheaf.IsSheaf.section_ext C.sequence.line.sheaf.isSheaf
    intro x hxU
    let W := U ⊓ V x
    let a : W ⟶ U := TopologicalSpace.Opens.infLELeft U (V x)
    let b : W ⟶ V x := TopologicalSpace.Opens.infLERight U (V x)
    refine ⟨W, inf_le_left, ⟨hxU, hx x⟩, ?_⟩
    have hr : (tangentSheaf X.structureMap).presheaf.map a.op
        ((tangentSheaf X.structureMap).presheaf.map j.op g) =
        (tangentSheaf X.structureMap).presheaf.map b.op (c x) := by
      calc
        _ = (tangentSheaf X.structureMap).presheaf.map (a ≫ j).op g :=
          LocalDerivationProof.moduleRestrict_comp (tangentSheaf X.structureMap) a j g
        _ = (tangentSheaf X.structureMap).presheaf.map (b ≫ i x).op g :=
          congrArg (fun k : W ⟶ ⊤ => (tangentSheaf X.structureMap).presheaf.map k.op g)
            (Subsingleton.elim _ _)
        _ = (tangentSheaf X.structureMap).presheaf.map b.op
            ((tangentSheaf X.structureMap).presheaf.map (i x).op g) :=
          (LocalDerivationProof.moduleRestrict_comp (tangentSheaf X.structureMap) b (i x) g).symm
        _ = _ := congrArg (fun z => (tangentSheaf X.structureMap).presheaf.map b.op z) (hg x)
    change C.sequence.line.sheaf.presheaf.map a.op
        (defectLinear C.sequence U ((tangentSheaf X.structureMap).presheaf.map j.op g) u) =
      C.sequence.line.sheaf.presheaf.map a.op 0
    calc
      _ = defectLinear C.sequence W
          ((tangentSheaf X.structureMap).presheaf.map a.op
            ((tangentSheaf X.structureMap).presheaf.map j.op g))
          (C.sequence.distribution.sheaf.presheaf.map a.op u) :=
        defectLinear_restrict C.sequence a
          ((tangentSheaf X.structureMap).presheaf.map j.op g) u
      _ = defectLinear C.sequence W
          ((tangentSheaf X.structureMap).presheaf.map b.op (c x))
          (C.sequence.distribution.sheaf.presheaf.map a.op u) :=
        congrArg (fun z => defectLinear C.sequence W z
          (C.sequence.distribution.sheaf.presheaf.map a.op u)) hr
      _ = 0 := correctedLift_isContact C (V x) (v x) W b
        (C.sequence.distribution.sheaf.presheaf.map a.op u)
      _ = _ := (map_zero _).symm
  exact ⟨⟨g, hgcontact⟩, hgvalue⟩

theorem intrinsicHamiltonian_bijective {n : ℕ}
    (X : SmoothProperComplexVariety (2 * n + 1))
    (C : IntrinsicContactStructure X) :
    Function.Bijective (intrinsicHamiltonian C) := by
  exact ⟨IntrinsicHamiltonianInjectivityProof.intrinsicHamiltonian_injective X C,
    intrinsicHamiltonian_surjective X C⟩

end IntrinsicHamiltonianGluingProof
end


theorem intrinsicHamiltonian_bijective {n : ℕ}
    (X : SmoothProperComplexVariety (2 * n + 1))
    (C : IntrinsicContactStructure X) :
    Function.Bijective (intrinsicHamiltonian C) := by
  exact LeBrunSalamon.PhaseTwentySeven.IntrinsicHamiltonianGluingProof.intrinsicHamiltonian_bijective (X := X) (C := C)

def intrinsicHamiltonianEquiv {n : ℕ}
    (X : SmoothProperComplexVariety (2 * n + 1))
    (C : IntrinsicContactStructure X) :
    GlobalContactField C ≃ GlobalSections C.sequence.line.sheaf :=
  Equiv.ofBijective _ (intrinsicHamiltonian_bijective X C)

def intrinsicHamiltonianField {n : ℕ}
    (X : SmoothProperComplexVariety (2 * n + 1))
    (C : IntrinsicContactStructure X)
    (s : GlobalSections C.sequence.line.sheaf) : GlobalContactField C :=
  (intrinsicHamiltonianEquiv X C).symm s

theorem intrinsicHamiltonianField_value {n : ℕ}
    (X : SmoothProperComplexVariety (2 * n + 1))
    (C : IntrinsicContactStructure X)
    (s : GlobalSections C.sequence.line.sheaf) :
    intrinsicHamiltonian C (intrinsicHamiltonianField X C s) = s := by
  set_option backward.isDefEq.respectTransparency false in
    exact (intrinsicHamiltonianEquiv X C).apply_symm_apply s

theorem globalContactField_zero {n : ℕ}
    {X : SmoothProperComplexVariety (2 * n + 1)}
    (C : IntrinsicContactStructure X) : IsGlobalContactField C 0 := by
  set_option backward.isDefEq.respectTransparency false in
    intro U i u
    rw [map_zero, LeBrunSalamon.PhaseTwentyFive.TangentBracketProof.zero_left, map_zero]

theorem globalContactField_add {n : ℕ}
    {X : SmoothProperComplexVariety (2 * n + 1)}
    (C : IntrinsicContactStructure X)
    (v w : GlobalSections (tangentSheaf X.structureMap))
    (hv : IsGlobalContactField C v) (hw : IsGlobalContactField C w) :
    IsGlobalContactField C (v + w) := by
  set_option backward.isDefEq.respectTransparency false in
    intro U i u
    rw [map_add, tangentBracket_add_left, map_add, hv U i u, hw U i u, add_zero]

section ContactClosureProofSection

open Opposite

set_option backward.isDefEq.respectTransparency false

namespace ContactClosureProof

/-- Evaluation preserves the actual kernel, so its sections lift on the same open. -/
theorem exists_kernelSection {Y : Scheme} {E F G : OModule Y}
    (i : E ⟶ F) (p : F ⟶ G) (hz : i ≫ p = 0)
    (hex : (ShortComplex.mk i p hz).ShortExact) (U : Y.Opens)
    (w : SectionsOn F U) (hw : p.app U w = 0) :
    ∃ a : SectionsOn E U, i.app U a = w := by
  let ev := SheafOfModules.evaluation Y.ringCatSheaf (op U)
  letI : ev.Additive := by
    dsimp [ev, SheafOfModules.evaluation]
    infer_instance
  letI : PreservesFiniteLimits ev :=
    inferInstanceAs (PreservesFiniteLimits
      (SheafOfModules.evaluation Y.ringCatSheaf (op U)))
  have he : ((ShortComplex.mk i p hz).map ev).Exact :=
    ((ShortComplex.mk i p hz).map ev).exact_of_f_is_kernel
      (KernelFork.mapIsLimit _ hex.fIsKernel ev)
  exact (((ShortComplex.mk i p hz).map ev).moduleCat_exact_iff.mp he) w hw

/-- The local vector fields preserving the actual distribution are closed under bracket. -/
theorem local_bracket {n : ℕ}
    {X : SmoothProperComplexVariety (2 * n + 1)}
    (C : IntrinsicContactSequence X) (U : X.scheme.Opens)
    (v w : SectionsOn (tangentSheaf X.structureMap) U)
    (hv : ∀ u : SectionsOn C.distribution.sheaf U,
      C.form.app U (tangentBracket X.structureMap U v (C.inclusion.app U u)) = 0)
    (hw : ∀ u : SectionsOn C.distribution.sheaf U,
      C.form.app U (tangentBracket X.structureMap U w (C.inclusion.app U u)) = 0)
    (u : SectionsOn C.distribution.sheaf U) :
    C.form.app U (tangentBracket X.structureMap U
      (tangentBracket X.structureMap U v w) (C.inclusion.app U u)) = 0 := by
  obtain ⟨a, ha⟩ := exists_kernelSection C.inclusion C.form C.comp_zero
    C.shortExact U (tangentBracket X.structureMap U w (C.inclusion.app U u)) (hw u)
  have huv : C.form.app U
      (tangentBracket X.structureMap U (C.inclusion.app U u) v) = 0 := by
    rw [LeBrunSalamon.PhaseTwentyFive.TangentBracketProof.skew,
      map_neg, hv u, neg_zero]
  obtain ⟨b, hb⟩ := exists_kernelSection C.inclusion C.form C.comp_zero
    C.shortExact U (tangentBracket X.structureMap U (C.inclusion.app U u) v) huv
  have hfirst : C.form.app U (tangentBracket X.structureMap U v
      (tangentBracket X.structureMap U w (C.inclusion.app U u))) = 0 := by
    rw [← ha]
    exact hv a
  have hsecond : C.form.app U (tangentBracket X.structureMap U w
      (tangentBracket X.structureMap U (C.inclusion.app U u) v)) = 0 := by
    rw [← hb]
    exact hw b
  have hthird := congrArg (fun z : SectionsOn (tangentSheaf X.structureMap) U =>
      C.form.app U z)
    (LeBrunSalamon.PhaseTwentyFive.TangentBracketProof.jacobi X.structureMap U
      v w (C.inclusion.app U u))
  simp only [map_add, map_zero, hfirst, hsecond, zero_add] at hthird
  rw [LeBrunSalamon.PhaseTwentyFive.TangentBracketProof.skew,
    map_neg, hthird, neg_zero]

/-- Restriction and the same-open kernel argument prove the actual global closure law. -/
theorem global_bracket {n : ℕ}
    {X : SmoothProperComplexVariety (2 * n + 1)}
    (C : IntrinsicContactStructure X)
    (v w : GlobalSections (tangentSheaf X.structureMap))
    (hv : IsGlobalContactField C v) (hw : IsGlobalContactField C w) :
    IsGlobalContactField C (tangentBracket X.structureMap ⊤ v w) := by
  intro U i u
  rw [LeBrunSalamon.PhaseTwentyFive.TangentBracketProof.tangentBracket_restrict]
  exact local_bracket C.sequence U
    ((tangentSheaf X.structureMap).presheaf.map i.op v)
    ((tangentSheaf X.structureMap).presheaf.map i.op w)
    (fun a => hv U i a) (fun a => hw U i a) u

end ContactClosureProof

end ContactClosureProofSection

theorem globalContactField_bracket {n : ℕ}
    {X : SmoothProperComplexVariety (2 * n + 1)}
    (C : IntrinsicContactStructure X)
    (v w : GlobalSections (tangentSheaf X.structureMap))
    (hv : IsGlobalContactField C v) (hw : IsGlobalContactField C w) :
    IsGlobalContactField C (tangentBracket X.structureMap ⊤ v w) :=
  ContactClosureProof.global_bracket C v w hv hw

/-- Global contact fields are generally NOT an O_X-module: multiplying by arbitrary functions does not
preserve contact vector fields. Their Hamiltonian correspondence is complex-linear, not O_X-linear. -/
def intrinsicJacobiBracket {n : ℕ}
    (X : SmoothProperComplexVariety (2 * n + 1))
    (C : IntrinsicContactStructure X)
    (a b : GlobalSections C.sequence.line.sheaf) :
    GlobalSections C.sequence.line.sheaf :=
  C.sequence.form.app ⊤
    (tangentBracket X.structureMap ⊤
      (intrinsicHamiltonianField X C a).val
      (intrinsicHamiltonianField X C b).val)

theorem intrinsicJacobi_skew {n : ℕ}
    (X : SmoothProperComplexVariety (2 * n + 1))
    (C : IntrinsicContactStructure X)
    (a b : GlobalSections C.sequence.line.sheaf) :
    intrinsicJacobiBracket X C a b = -intrinsicJacobiBracket X C b a := by
  set_option backward.isDefEq.respectTransparency false in
    unfold intrinsicJacobiBracket
    rw [LeBrunSalamon.PhaseTwentyFive.TangentBracketProof.skew]
    exact map_neg _ _

section ContactClosureHamiltonianProofSection

set_option backward.isDefEq.respectTransparency false

namespace ContactClosureProof

/-- The existing Hamiltonian equivalence identifies the closed actual vector bracket. -/
theorem hamiltonianField_bracket_val {n : ℕ}
    (X : SmoothProperComplexVariety (2 * n + 1))
    (C : IntrinsicContactStructure X)
    (a b : GlobalSections C.sequence.line.sheaf) :
    (intrinsicHamiltonianField X C (intrinsicJacobiBracket X C a b)).val =
      tangentBracket X.structureMap ⊤
        (intrinsicHamiltonianField X C a).val
        (intrinsicHamiltonianField X C b).val := by
  let h : GlobalContactField C :=
    ⟨tangentBracket X.structureMap ⊤
        (intrinsicHamiltonianField X C a).val
        (intrinsicHamiltonianField X C b).val,
      global_bracket C
        (intrinsicHamiltonianField X C a).val
        (intrinsicHamiltonianField X C b).val
        (intrinsicHamiltonianField X C a).property
        (intrinsicHamiltonianField X C b).property⟩
  have he : intrinsicHamiltonianField X C (intrinsicJacobiBracket X C a b) = h :=
    (intrinsicHamiltonianEquiv X C).symm_apply_apply h
  exact congrArg (fun v : GlobalContactField C => v.val) he

end ContactClosureProof

end ContactClosureHamiltonianProofSection

theorem intrinsicJacobi_identity {n : ℕ}
    (X : SmoothProperComplexVariety (2 * n + 1))
    (C : IntrinsicContactStructure X)
    (a b c : GlobalSections C.sequence.line.sheaf) :
    intrinsicJacobiBracket X C a (intrinsicJacobiBracket X C b c) +
      intrinsicJacobiBracket X C b (intrinsicJacobiBracket X C c a) +
      intrinsicJacobiBracket X C c (intrinsicJacobiBracket X C a b) = 0 := by
  set_option backward.isDefEq.respectTransparency false in
    change C.sequence.form.app ⊤ (tangentBracket X.structureMap ⊤
        (intrinsicHamiltonianField X C a).val
        (intrinsicHamiltonianField X C (intrinsicJacobiBracket X C b c)).val) +
      C.sequence.form.app ⊤ (tangentBracket X.structureMap ⊤
        (intrinsicHamiltonianField X C b).val
        (intrinsicHamiltonianField X C (intrinsicJacobiBracket X C c a)).val) +
      C.sequence.form.app ⊤ (tangentBracket X.structureMap ⊤
        (intrinsicHamiltonianField X C c).val
        (intrinsicHamiltonianField X C (intrinsicJacobiBracket X C a b)).val) = 0
    rw [ContactClosureProof.hamiltonianField_bracket_val X C b c,
      ContactClosureProof.hamiltonianField_bracket_val X C c a,
      ContactClosureProof.hamiltonianField_bracket_val X C a b]
    have hJ := congrArg
      (fun v : GlobalSections (tangentSheaf X.structureMap) => C.sequence.form.app ⊤ v)
      (LeBrunSalamon.PhaseTwentyFive.TangentBracketProof.jacobi X.structureMap ⊤
        (intrinsicHamiltonianField X C a).val
        (intrinsicHamiltonianField X C b).val
        (intrinsicHamiltonianField X C c).val)
    simpa only [map_add, map_zero] using hJ

end LeBrunSalamon.PhaseTwentySeven

end

import LSTangentComparison

/-!
# Intrinsic Hamiltonians and actual first jets

The point tangent comparison uses the original tangent-sheaf fiber and
its actual action on local functions. The Hamiltonian point value is
then recovered from the contact covector and Levi form. No first-jet
surjectivity of global sections is assumed in this construction.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseFour LeBrunSalamon.PhaseSeven LeBrunSalamon.PhaseTen
open LeBrunSalamon.PhaseSeventeen LeBrunSalamon.PhaseNineteen LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentySix LeBrunSalamon.PhaseTwentySeven
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirtyFive
open LeBrunSalamon.Core LeBrunSalamon.Skeleton
open LeBrunSalamon.Refinement LeBrunSalamon.Refinement.Jets
open LeBrunSalamon.Construction LeBrunSalamon.Construction.Lines

namespace LeBrunSalamon.Refinement.Jets.PointFrame

variable {d : ℕ} {X : SmoothProperComplexVariety d} {L : LineBundle X.scheme}
  {x : ComplexPoint X} (F : PointFrame X L x)

def pointSupport : (⊤ : ComplexBase.Opens) ≤ x.map ⁻¹ᵁ F.frame.openSet := by
  rw [F.point_preimage_frame]

/-- The frame's evaluation is the actual scalar value along the original point. -/
theorem evaluation_eq_localRingValue (a : F.ChartRing) :
    F.evaluation a = PositiveFrame.localRingValue x.map F.frame.openSet F.pointSupport a := by
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
      (F.pointLift.appTop (F.frame.openSet.topIso.inv a)) =
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
      (x.map.appLE F.frame.openSet ⊤ F.pointSupport a)
  rw [PositiveFrame.pointFactor_appLE F.frame.openSet F.pointLift x.map F.overPoint]
  rfl

/-- The original tangent fiber acts on the actual affine coefficient ring. -/
def fiberDerivation : TangentFiber X x →ₗ[ℂ] F.Tangent where
  toFun v :=
    ⟨{ toFun := fun a => IntrinsicTangent.localAction X.structureMap x.map
          F.frame.openSet F.pointSupport a v
       map_add' a b := IntrinsicTangent.localAction_add_function X.structureMap x.map
         F.frame.openSet F.pointSupport a b v
       map_smul' c a := IntrinsicTangent.localAction_smul_function X.structureMap x.map
         x.overC F.frame.openSet F.pointSupport c a v }, by
      intro a b
      change IntrinsicTangent.localAction X.structureMap x.map F.frame.openSet
        F.pointSupport (a*b) v = _
      rw [IntrinsicTangent.localAction_mul_function,
        ← F.evaluation_eq_localRingValue a, ← F.evaluation_eq_localRingValue b]
      rfl⟩
  map_add' v w := by
    apply Subtype.ext
    apply LinearMap.ext
    intro a
    exact (IntrinsicTangent.localAction X.structureMap x.map
      F.frame.openSet F.pointSupport a).map_add v w
  map_smul' c v := by
    apply Subtype.ext
    apply LinearMap.ext
    intro a
    exact (IntrinsicTangent.localAction X.structureMap x.map
      F.frame.openSet F.pointSupport a).map_smul c v

/-- The map is normalized on every local intrinsic tangent section. -/
theorem fiberDerivation_local
    (v : SectionsOn (tangentSheaf X.structureMap) F.frame.openSet) :
    F.fiberDerivation (PositiveFrame.localFiberValue x.map
      (tangentSheaf X.structureMap) F.frame.openSet F.pointSupport v) =
        F.evaluateVector v := by
  apply Subtype.ext
  apply LinearMap.ext
  intro a
  change PositiveFrame.localScalarPairing x.map
      (dualEvaluation (cotangentSheaf X.structureMap)) F.frame.openSet F.pointSupport
      ((cotangentPresentation X.structureMap).differential.apply F.frame.openSet a)
      (PositiveFrame.localFiberValue x.map (tangentSheaf X.structureMap)
        F.frame.openSet F.pointSupport v) =
    F.evaluation (tangentActs X.structureMap F.frame.openSet v a)
  rw [PositiveFrame.localScalarPairing_value]
  exact (F.evaluation_eq_localRingValue
    (tangentActs X.structureMap F.frame.openSet v a)).symm

theorem fiberDerivation_injective : Function.Injective F.fiberDerivation := by
  intro v w h
  apply IntrinsicTangent.eq_of_affine_localAction X.structureMap x.map
    (smooth_cotangent_rank X.structureMap d X.smooth)
    F.frame.openSet F.frame.isAffine F.pointSupport v w
  intro a
  exact congrArg (fun D : F.Tangent => D.val a) h

theorem fiberDerivation_surjective : Function.Surjective F.fiberDerivation := by
  intro D
  obtain ⟨v, hv⟩ := F.evaluateVector_surjective D
  exact ⟨PositiveFrame.localFiberValue x.map (tangentSheaf X.structureMap)
    F.frame.openSet F.pointSupport v, (F.fiberDerivation_local v).trans hv⟩

/-- A canonical equivalence, whose function is the actual differential pairing. -/
def fiberEquiv : TangentFiber X x ≃ₗ[ℂ] F.Tangent :=
  LinearEquiv.ofBijective F.fiberDerivation
    ⟨F.fiberDerivation_injective, F.fiberDerivation_surjective⟩

theorem fiberEquiv_local
    (v : SectionsOn (tangentSheaf X.structureMap) F.frame.openSet) :
    F.fiberEquiv (PositiveFrame.localFiberValue x.map
      (tangentSheaf X.structureMap) F.frame.openSet F.pointSupport v) =
        F.evaluateVector v := F.fiberDerivation_local v

/-- Evaluation of a global vector has the same local normalization. -/
theorem fiberEquiv_global (v : CSections X.structureMap (tangentSheaf X.structureMap)) :
    F.fiberEquiv (evaluateSection X.structureMap (tangentSheaf X.structureMap)
      x.map x.overC v) =
      F.evaluateVector (TwoChartSections.restrictValue (tangentSheaf X.structureMap) le_top v) := by
  rw [← PositiveFrame.localFiberValue_global X.structureMap x.map x.overC
    (tangentSheaf X.structureMap) F.frame.openSet F.pointSupport v]
  exact F.fiberEquiv_local _

end LeBrunSalamon.Refinement.Jets.PointFrame

namespace LeBrunSalamon.PhaseThirtyFive.HamiltonianJetProof

/-- The original Hom-valued tangent evaluation and the actual tangent
fiber differ only by the canonical unit comparison and section equivalence. -/
def tangentEvaluationEquiv {n : ℕ} (X : SmoothProperComplexVariety (2*n+1))
    (C : IntrinsicContactStructure X) (x : ComplexPoint X) :
    TangentEvaluationAt n (intrinsicAsCandidate X C) x ≃ TangentFiber X x :=
  (Iso.homCongr (unitPullbackIso x.map)
    (Iso.refl (pullbackModule x.map (tangentSheaf X.structureMap)))).trans
      (sectionEquiv (pullbackModule x.map (tangentSheaf X.structureMap)))

theorem tangentEvaluationEquiv_restrict {n : ℕ} (X : SmoothProperComplexVariety (2*n+1))
    (C : IntrinsicContactStructure X) (x : ComplexPoint X)
    (v : AlgebraicSection (tangentSheaf X.structureMap)) :
    tangentEvaluationEquiv X C x (restrictSection x.map v) =
      evaluateSection X.structureMap (tangentSheaf X.structureMap)
        x.map x.overC (sectionValue v) := by
  simp only [tangentEvaluationEquiv, Equiv.trans_apply, Iso.homCongr_apply,
    Iso.refl_hom, Category.comp_id]
  change sectionValue ((unitPullbackIso x.map).inv ≫ restrictSection x.map v) =
    sectionValue (pullSection x.map (sectionFromValue (sectionValue v)))
  rw [sectionFromValue_sectionValue]
  rfl

variable {n : ℕ} {X : SmoothProperComplexVariety (2*n+1)}
  (C : IntrinsicContactStructure X) {x : ComplexPoint X}
  (F : PointFrame X C.sequence.line x) (A : ContactAtPoint C F)

/-- The actual tangent evaluation, now expressed in the specified point frame. -/
def pointTangentEquiv : TangentEvaluationAt n (intrinsicAsCandidate X C) x ≃ F.Tangent :=
  (tangentEvaluationEquiv X C x).trans F.fiberEquiv.toEquiv

/-- The point Hamiltonian is defined for every genuine first-jet coordinate,
using the finite-dimensional perfect Levi pairing. -/
def pointHamiltonian (j : TrivializedFirstJet F.Tangent) : F.Tangent :=
  (Classical.choice (contactHamiltonianValue_exists F.Tangent
    (KernelTaylorProof.contactOneJet C F A) j.1 j.2)).vector

theorem pointHamiltonian_unique (j : TrivializedFirstJet F.Tangent)
    (H : ContactHamiltonianValue F.Tangent (KernelTaylorProof.contactOneJet C F A) j.1 j.2) :
    pointHamiltonian C F A j = H.vector :=
  contactHamiltonianValue_unique F.Tangent (KernelTaylorProof.contactOneJet C F A) j.1 j.2
    (Classical.choice (contactHamiltonianValue_exists F.Tangent
      (KernelTaylorProof.contactOneJet C F A) j.1 j.2)) H

/-- Every point vector is the Hamiltonian of some first jet. The local
function realizing that jet is furnished separately by `jetCoordinates`. -/
theorem pointHamiltonian_surjective : Function.Surjective (pointHamiltonian C F A) := by
  intro v
  let j : TrivializedFirstJet F.Tangent := (A.theta v, -(A.exterior v))
  let H : ContactHamiltonianValue F.Tangent (KernelTaylorProof.contactOneJet C F A) j.1 j.2 :=
    { vector := v
      contactValue := rfl
      horizontalEquation := by
        intro w hw
        change -A.exterior v w + (KernelTaylorProof.contactOneJet C F A).exteriorValue v w = 0
        rw [KernelTaylorProof.contactOneJet_exterior]
        ring }
  exact ⟨j, pointHamiltonian_unique C F A j H⟩

/-- Cartan's formula for an actual local contact field gives exactly the
point Hamiltonian equations, including the sign of the exterior derivative. -/
theorem pointHamiltonian_local (f : F.ChartRing)
    (v : SectionsOn (tangentSheaf X.structureMap) F.frame.openSet)
    (hv : localContactValue C F.frame v = f)
    (hcontact : ∀ w : SectionsOn (tangentSheaf X.structureMap) F.frame.openSet,
      localContactValue C F.frame w = 0 →
        localContactValue C F.frame (tangentBracket X.structureMap F.frame.openSet v w) = 0) :
    pointHamiltonian C F A (F.localJet f) = F.evaluateVector v := by
  apply pointHamiltonian_unique C F A (F.localJet f)
    (H := { vector := F.evaluateVector v
            contactValue := ?_
            horizontalEquation := ?_ })
  · change A.theta (F.evaluateVector v) = F.evaluation f
    rw [A.theta_normalized, hv]
  · intro w hw
    obtain ⟨u, hu, hθu⟩ := KernelTaylorProof.horizontal_representative C F A w hw
    rw [KernelTaylorProof.contactOneJet_exterior, ← hu, A.exterior_normalized]
    change F.evaluation (tangentActs X.structureMap F.frame.openSet u f) +
      F.evaluation (scalarExterior C F v u) = 0
    rw [scalarExterior, hθu, hv, TangentActionProof.zero_function,
      hcontact u hθu, sub_zero, zero_sub, map_neg]
    ring

/-- Restrict the actual global Hamiltonian field to the selected frame. -/
def localHamiltonian (s : AlgebraicSection C.sequence.line.sheaf) :
    SectionsOn (tangentSheaf X.structureMap) F.frame.openSet :=
  (tangentSheaf X.structureMap).presheaf.map (homOfLE le_top).op
    (intrinsicHamiltonianField X C (sectionValue s)).val

theorem localHamiltonian_value (s : AlgebraicSection C.sequence.line.sheaf) :
    localContactValue C F.frame (localHamiltonian C F s) = F.coefficient s := by
  have hv := intrinsicHamiltonianField_value X C (sectionValue s)
  change C.sequence.form.app ⊤ (intrinsicHamiltonianField X C (sectionValue s)).val =
    sectionValue s at hv
  change F.frame.coefficient (C.sequence.form.app F.frame.openSet
      ((tangentSheaf X.structureMap).presheaf.map (homOfLE le_top).op
        (intrinsicHamiltonianField X C (sectionValue s)).val)) = _
  have hnat := sheafHom_naturality C.sequence.form
    (homOfLE (show F.frame.openSet ≤ ⊤ from le_top))
    (intrinsicHamiltonianField X C (sectionValue s)).val
  calc
    F.frame.coefficient (C.sequence.form.app F.frame.openSet
        ((tangentSheaf X.structureMap).presheaf.map (homOfLE le_top).op
          (intrinsicHamiltonianField X C (sectionValue s)).val)) =
        F.frame.coefficient (C.sequence.line.sheaf.presheaf.map (homOfLE le_top).op
          (C.sequence.form.app ⊤ (intrinsicHamiltonianField X C (sectionValue s)).val)) :=
      congrArg F.frame.coefficient hnat.symm
    _ = F.frame.coefficient (C.sequence.line.sheaf.presheaf.map
        (homOfLE le_top).op (sectionValue s)) :=
      congrArg (fun z : GlobalSections C.sequence.line.sheaf =>
        F.frame.coefficient (C.sequence.line.sheaf.presheaf.map
          (homOfLE le_top).op z)) hv
    _ = F.coefficient s := by
      change F.frame.coefficient
          (C.sequence.line.sheaf.presheaf.map (homOfLE le_top).op (sectionValue s)) =
        F.frame.coefficient (Scheme.Modules.Hom.app s F.frame.openSet
          (1 : RingSections X.scheme F.frame.openSet))
      rw [ScalarSections.section_app_one]

theorem localHamiltonian_contact (s : AlgebraicSection C.sequence.line.sheaf)
    (w : SectionsOn (tangentSheaf X.structureMap) F.frame.openSet)
    (hw : localContactValue C F.frame w = 0) :
    localContactValue C F.frame
      (tangentBracket X.structureMap F.frame.openSet (localHamiltonian C F s) w) = 0 := by
  have hform : C.sequence.form.app F.frame.openSet w = 0 := by
    apply F.frame.coefficient.injective
    change F.frame.coefficient (C.sequence.form.app F.frame.openSet w) = 0 at hw
    simpa only [map_zero] using hw
  obtain ⟨u, hu⟩ := ContactClosureProof.exists_kernelSection C.sequence.inclusion
    C.sequence.form C.sequence.comp_zero C.sequence.shortExact F.frame.openSet w hform
  have hc := (intrinsicHamiltonianField X C (sectionValue s)).property
    F.frame.openSet (homOfLE le_top) u
  change C.sequence.form.app F.frame.openSet (tangentBracket X.structureMap F.frame.openSet
    (localHamiltonian C F s) (C.sequence.inclusion.app F.frame.openSet u)) = 0 at hc
  rw [hu] at hc
  change F.frame.coefficient (C.sequence.form.app F.frame.openSet
    (tangentBracket X.structureMap F.frame.openSet (localHamiltonian C F s) w)) = 0
  rw [hc, map_zero]

/-- The intrinsic global Hamiltonian has exactly the point value obtained
from its scalar first jet in the actual line frame. -/
theorem pointTangentEquiv_Hamiltonian (s : AlgebraicSection C.sequence.line.sheaf) :
    pointTangentEquiv C F (restrictSection x.map (intrinsicHamiltonianSectionField X C s)) =
      pointHamiltonian C F A (F.localJet (F.coefficient s)) := by
  change F.fiberEquiv
    (tangentEvaluationEquiv X C x (restrictSection x.map (intrinsicHamiltonianSectionField X C s))) = _
  rw [tangentEvaluationEquiv_restrict, F.fiberEquiv_global]
  simp only [intrinsicHamiltonianSectionField, sectionFromValue_spec]
  change F.evaluateVector (localHamiltonian C F s) = _
  exact (pointHamiltonian_local C F A (F.coefficient s) (localHamiltonian C F s)
    (localHamiltonian_value C F s) (localHamiltonian_contact C F s)).symm

end LeBrunSalamon.PhaseThirtyFive.HamiltonianJetProof

namespace LeBrunSalamon.PhaseThirtyFive

open HamiltonianJetProof

theorem intrinsicHamiltonian_depends_on_firstJet {n : ℕ}
    (X : SmoothProperComplexVariety (2 * n + 1))
    (C : IntrinsicContactStructure X) (x : ComplexPoint X)
    (s t : AlgebraicSection C.sequence.line.sheaf)
    (h : jetRestrictionAt x C.sequence.line.sheaf 1 s =
      jetRestrictionAt x C.sequence.line.sheaf 1 t) :
    restrictSection x.map (intrinsicHamiltonianSectionField X C s) =
      restrictSection x.map (intrinsicHamiltonianSectionField X C t) := by
  obtain ⟨F⟩ := pointFrame_exists X C.sequence.line x
  obtain ⟨A⟩ := contactAtPoint_exists C F
  apply (pointTangentEquiv C F).injective
  rw [pointTangentEquiv_Hamiltonian C F A, pointTangentEquiv_Hamiltonian C F A,
    ← F.jetCoordinates_global s, h, F.jetCoordinates_global t]

/-- The earlier jet-to-tangent certificate now has a nontrivial existence obligation for actual contact
manifolds, with its global Hamiltonian lifting map fixed, rather than arbitrary. -/
theorem intrinsicHamiltonianJetCompatibility_exists {n : ℕ}
    (X : SmoothProperComplexVariety (2 * n + 1))
    (C : IntrinsicContactStructure X) :
    ∃ J : HamiltonianFirstJetCompatibility n (intrinsicAsCandidate X C),
      ∀ s, J.fieldOfSection s = intrinsicHamiltonianSectionField X C s := by
  classical
  let F (x : ComplexPoint X) : PointFrame X C.sequence.line x :=
    Classical.choice (pointFrame_exists X C.sequence.line x)
  let A (x : ComplexPoint X) : ContactAtPoint C (F x) :=
    Classical.choice (contactAtPoint_exists C (F x))
  refine ⟨{
    fieldOfSection := intrinsicHamiltonianSectionField X C
    hamiltonian_rightInverse := ?_
    jetToTangent := fun x j => (pointTangentEquiv C (F x)).symm
      (pointHamiltonian C (F x) (A x) ((F x).jetCoordinates j))
    jetToTangent_surjective := ?_
    commutes := ?_ }, fun s => rfl⟩
  · intro s
    exact intrinsicHamiltonianSectionField_rightInverse X C s
  · intro x v
    change ComplexPoint X at x
    obtain ⟨j, hj⟩ := pointHamiltonian_surjective C (F x) (A x)
      (pointTangentEquiv C (F x) v)
    refine ⟨(F x).jetCoordinates.symm j, ?_⟩
    change (pointTangentEquiv C (F x)).symm
        (pointHamiltonian C (F x) (A x)
          ((F x).jetCoordinates ((F x).jetCoordinates.symm j))) = v
    calc
      (pointTangentEquiv C (F x)).symm
          (pointHamiltonian C (F x) (A x)
            ((F x).jetCoordinates ((F x).jetCoordinates.symm j))) =
          (pointTangentEquiv C (F x)).symm (pointHamiltonian C (F x) (A x) j) :=
        congrArg (fun k : TrivializedFirstJet (F x).Tangent =>
          (pointTangentEquiv C (F x)).symm (pointHamiltonian C (F x) (A x) k))
          ((F x).jetCoordinates.apply_symm_apply j)
      _ = (pointTangentEquiv C (F x)).symm (pointTangentEquiv C (F x) v) :=
        congrArg (pointTangentEquiv C (F x)).symm hj
      _ = v := (pointTangentEquiv C (F x)).symm_apply_apply v
  · intro x s
    change ComplexPoint X at x
    change AlgebraicSection C.sequence.line.sheaf at s
    change (pointTangentEquiv C (F x)).symm
        (pointHamiltonian C (F x) (A x)
          ((F x).jetCoordinates (jetRestrictionAt x C.sequence.line.sheaf 1 s))) =
      restrictSection x.map (intrinsicHamiltonianSectionField X C s)
    apply (pointTangentEquiv C (F x)).injective
    calc
      pointTangentEquiv C (F x) ((pointTangentEquiv C (F x)).symm
          (pointHamiltonian C (F x) (A x)
            ((F x).jetCoordinates (jetRestrictionAt x C.sequence.line.sheaf 1 s)))) =
          pointHamiltonian C (F x) (A x)
            ((F x).jetCoordinates (jetRestrictionAt x C.sequence.line.sheaf 1 s)) :=
        (pointTangentEquiv C (F x)).apply_symm_apply _
      _ = pointHamiltonian C (F x) (A x) ((F x).localJet ((F x).coefficient s)) :=
        congrArg (pointHamiltonian C (F x) (A x)) ((F x).jetCoordinates_global s)
      _ = pointTangentEquiv C (F x)
          (restrictSection x.map (intrinsicHamiltonianSectionField X C s)) :=
        (pointTangentEquiv_Hamiltonian C (F x) (A x) s).symm

namespace IntrinsicConsequenceProof

theorem intrinsicFirstJets_imply_HamiltonianSpanning {n : ℕ}
    (X : SmoothProperComplexVariety (2 * n + 1))
    (C : IntrinsicContactStructure X)
    (h : SeparatesFirstJets X C.sequence.line)
    (x : ComplexPoint X)
    (v : TangentEvaluationAt n (intrinsicAsCandidate X C) x) :
    ∃ s : AlgebraicSection C.sequence.line.sheaf,
      restrictSection x.map (intrinsicHamiltonianSectionField X C s) = v := by
  obtain ⟨J, hJ⟩ := intrinsicHamiltonianJetCompatibility_exists X C
  obtain ⟨j, hj⟩ := J.jetToTangent_surjective x v
  obtain ⟨s, hs⟩ := h x j
  refine ⟨s, ?_⟩
  calc
    restrictSection x.map (intrinsicHamiltonianSectionField X C s) =
        restrictSection x.map (J.fieldOfSection s) := by rw [hJ s]
    _ = J.jetToTangent x (jetRestrictionAt x C.sequence.line.sheaf 1 s) :=
      (J.commutes x s).symm
    _ = J.jetToTangent x j := by rw [hs]
    _ = v := hj

end IntrinsicConsequenceProof

theorem intrinsicFirstJets_imply_HamiltonianSpanning {n : ℕ}
    (X : SmoothProperComplexVariety (2 * n + 1))
    (C : IntrinsicContactStructure X)
    (h : SeparatesFirstJets X C.sequence.line)
    (x : ComplexPoint X)
    (v : TangentEvaluationAt n (intrinsicAsCandidate X C) x) :
    ∃ s : AlgebraicSection C.sequence.line.sheaf,
      restrictSection x.map (intrinsicHamiltonianSectionField X C s) = v := by
  exact LeBrunSalamon.PhaseThirtyFive.IntrinsicConsequenceProof.intrinsicFirstJets_imply_HamiltonianSpanning (n := n) (X := X) (C := C) (h := h) (x := x) (v := v)

/- The original unconditional Hamiltonian target follows the original
first-jet target in LSCompletedTargets. The conditional intrinsic
Hamiltonian theorem above remains available to the construction. -/

end LeBrunSalamon.PhaseThirtyFive

namespace LeBrunSalamon.Core

namespace NormalizedContactKernel

variable {n : ℕ} {X : SmoothProperComplexVariety (2*n+1)}
  {C : IntrinsicContactStructure X}

/-- This consequence is assembled from two distinct obligations: jet:criterion and the intrinsic contact-
Hamiltonian correspondence. It does not assert that affine vector fields are globally defined. -/
theorem globalHamiltonians_span (K : NormalizedContactKernel X C)
    (x : ComplexPoint X)
    (v : TangentEvaluationAt n (intrinsicAsCandidate X C) x) :
    ∃ a : AlgebraicSection C.sequence.line.sheaf,
      restrictSection x.map (intrinsicHamiltonianSectionField X C a) = v :=
  intrinsicFirstJets_imply_HamiltonianSpanning X C K.separatesFirstJets x v


end NormalizedContactKernel

/-- The last deduction of the algebraic core, before integration of vector fields and homogeneous contact
classification. This remains a conditional theorem until ManuscriptCoreInputs is actually constructed. -/
theorem manuscriptCore_HamiltonianSpanning (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (H : ManuscriptCoreInputs P p)
    {n : ℕ} (X : ContactFanoManifold n) (x : ComplexPoint X.variety)
    (v : TangentEvaluationAt n (intrinsicAsCandidate X.variety X.contact) x) :
    ∃ a : AlgebraicSection X.contact.sequence.line.sheaf,
      restrictSection x.map
        (intrinsicHamiltonianSectionField X.variety X.contact a) = v :=
  intrinsicFirstJets_imply_HamiltonianSpanning X.variety X.contact
    (manuscriptCore_firstJets P p H X) x v


end LeBrunSalamon.Core


namespace LeBrunSalamon.Refinement.Jets.PointFrame

variable {d : ℕ} {X : SmoothProperComplexVariety d} {L : LineBundle X.scheme}
  {x : ComplexPoint X} (F : PointFrame X L x)

/-- The actual pulled coefficient frame is global on the complex point. -/
def lineFiberCoefficient :
    GlobalSections (pullbackModule x.map L.sheaf) ≃ₗ[RingSections ComplexBase ⊤]
      RingSections ComplexBase ⊤ :=
  show SectionsOn (pullbackModule x.map L.sheaf) ⊤ ≃ₗ[RingSections ComplexBase ⊤]
      RingSections ComplexBase ⊤ from
    F.point_preimage_frame ▸ LocalFrameJetProof.pulledCoefficient F.frame x.map

private theorem coefficient_transport_top {Y : Scheme} (E : OModule Y)
    {V : Y.Opens} (hV : V = ⊤) (h : ⊤ ≤ V)
    (e : SectionsOn E V ≃ₗ[RingSections Y V] RingSections Y V)
    (a : SectionsOn E V) :
    (show SectionsOn E ⊤ ≃ₗ[RingSections Y ⊤] RingSections Y ⊤ from hV ▸ e)
      (E.presheaf.map (homOfLE h).op a) =
        Y.presheaf.map (homOfLE h).op (e a) := by
  subst V
  have hi : homOfLE h = 𝟙 (⊤ : Y.Opens) := Subsingleton.elim _ _
  rw [hi]
  simp only [op_id, CategoryTheory.Functor.map_id] <;> rfl

theorem lineFiberCoefficient_local (a : F.ChartRing) :
    F.lineFiberCoefficient (PositiveFrame.localFiberValue x.map L.sheaf
      F.frame.openSet F.pointSupport (F.frame.coefficient.symm a)) =
        x.map.appLE F.frame.openSet ⊤ F.pointSupport a := by
  change (show SectionsOn (pullbackModule x.map L.sheaf) ⊤ ≃ₗ[RingSections ComplexBase ⊤]
      RingSections ComplexBase ⊤ from
      F.point_preimage_frame ▸ LocalFrameJetProof.pulledCoefficient F.frame x.map)
    ((pullbackModule x.map L.sheaf).presheaf.map (homOfLE F.pointSupport).op
      (pullLocalSection x.map L.sheaf F.frame.openSet (F.frame.coefficient.symm a))) = _
  rw [coefficient_transport_top, LocalFrameJetProof.pulledCoefficient_local]
  rfl

theorem lineFiberCoefficient_global (a : AlgebraicSection L.sheaf) :
    F.lineFiberCoefficient (sectionValue (pullSection x.map a)) =
      x.map.appLE F.frame.openSet ⊤ F.pointSupport (F.coefficient a) := by
  have hc := F.lineFiberCoefficient_local (F.coefficient a)
  have hf : F.frame.coefficient.symm (F.coefficient a) =
      L.sheaf.presheaf.map (homOfLE le_top).op (sectionValue a) := by
    rw [PointFrame.coefficient, AffineLineFrame.localCoefficient,
      F.frame.coefficient.symm_apply_apply, ScalarSections.section_app_one]
  have hlocal := congrArg
    (fun s : SectionsOn L.sheaf F.frame.openSet =>
      PositiveFrame.localFiberValue x.map L.sheaf F.frame.openSet F.pointSupport s) hf
  have hglobal := PositiveFrame.localFiberValue_global X.structureMap x.map x.overC
    L.sheaf F.frame.openSet F.pointSupport (sectionValue a)
  have he : evaluateSection X.structureMap L.sheaf x.map x.overC (sectionValue a) =
      sectionValue (pullSection x.map a) := by
    change sectionValue (pullSection x.map (sectionFromValue (sectionValue a))) = _
    rw [sectionFromValue_sectionValue]
  have hvalue : PositiveFrame.localFiberValue x.map L.sheaf
      F.frame.openSet F.pointSupport (F.frame.coefficient.symm (F.coefficient a)) =
        sectionValue (pullSection x.map a) := hlocal.trans (hglobal.trans he)
  exact (congrArg
    (fun v : GlobalSections (pullbackModule x.map L.sheaf) => F.lineFiberCoefficient v)
    hvalue).symm.trans hc

/-- The local frame at one gives a genuine section of the original line fiber. -/
def lineFiberFrameSection : AlgebraicSection (pullbackModule x.map L.sheaf) :=
  sectionFromValue (F.lineFiberCoefficient.symm 1)

/-- The section Hom and the scheme-module Hom have the same actual components. -/
private abbrev _root_.SheafOfModules.Hom.app
    {Y : Scheme} {E G : Y.Modules}
    (φ : SheafOfModules.Hom E G) (U : Y.Opens) :
    (Scheme.Modules.presheaf E).obj (op U) ⟶
      (Scheme.Modules.presheaf G).obj (op U) :=
  AlgebraicGeometry.Scheme.Modules.Hom.app φ U

theorem lineFiberFrameSection_apply (a : RingSections ComplexBase ⊤) :
    F.lineFiberFrameSection.app ⊤ a = F.lineFiberCoefficient.symm a := by
  have h1 : Scheme.Modules.Hom.app F.lineFiberFrameSection ⊤
      (1 : RingSections ComplexBase ⊤) =
        F.lineFiberCoefficient.symm 1 := sectionFromValue_spec _
  calc
    _ = a • Scheme.Modules.Hom.app F.lineFiberFrameSection ⊤
        (1 : RingSections ComplexBase ⊤) := by
      simpa only [smul_eq_mul, mul_one] using
        (Scheme.Modules.Hom.app_smul F.lineFiberFrameSection a
          (1 : RingSections ComplexBase ⊤))
    _ = a • F.lineFiberCoefficient.symm 1 :=
      congrArg
        (fun v : GlobalSections (pullbackModule x.map L.sheaf) => a • v) h1
    _ = F.lineFiberCoefficient.symm (a • (1 : RingSections ComplexBase ⊤)) :=
      (F.lineFiberCoefficient.symm.map_smul a (1 : RingSections ComplexBase ⊤)).symm
    _ = F.lineFiberCoefficient.symm a :=
      congrArg F.lineFiberCoefficient.symm (mul_one a)

theorem lineFiberFrameSection_isIso : IsIso F.lineFiberFrameSection := by
  letI : (structureModule ComplexBase).IsQuasicoherent :=
    LocalExtensionSplitting.quasicoherent_of_locallyFreeRank (structureModule_rank ComplexBase)
  letI : (pullbackModule x.map L.sheaf).IsQuasicoherent :=
    LocalExtensionSplitting.quasicoherent_of_locallyFreeRank (pullbackLine x.map L).locallyFree
  apply LocalFrameJetProof.spec_isIso_of_appTop_bijective
  constructor
  · intro a b h
    exact F.lineFiberCoefficient.symm.injective
      ((F.lineFiberFrameSection_apply a).symm.trans
        (h.trans (F.lineFiberFrameSection_apply b)))
  · intro b
    exact ⟨F.lineFiberCoefficient b, by
      rw [F.lineFiberFrameSection_apply, F.lineFiberCoefficient.symm_apply_apply]⟩

/-- This fiber trivialization is fixed by the supplied affine line frame. -/
def lineFiberFrameIso : pullbackModule x.map L.sheaf ≅ structureModule ComplexBase := by
  letI := F.lineFiberFrameSection_isIso
  exact (asIso F.lineFiberFrameSection).symm

theorem lineFiberFrameIso_hom_apply
    (a : GlobalSections (pullbackModule x.map L.sheaf)) :
    F.lineFiberFrameIso.hom.app ⊤ a = F.lineFiberCoefficient a := by
  letI := F.lineFiberFrameSection_isIso
  have h := congrArg (fun q : structureModule ComplexBase ⟶ structureModule ComplexBase =>
    q.app ⊤ (F.lineFiberCoefficient a)) (asIso F.lineFiberFrameSection).hom_inv_id
  change F.lineFiberFrameIso.hom.app ⊤
    (Scheme.Modules.Hom.app F.lineFiberFrameSection ⊤
      (F.lineFiberCoefficient a)) = F.lineFiberCoefficient a at h
  rw [F.lineFiberFrameSection_apply, F.lineFiberCoefficient.symm_apply_apply] at h
  exact h

/-- The chosen fiber frame sends each actual pulled section to its specified
scalar value, rather than to an unspecified scalar multiple of that value. -/
theorem lineFiberFrameIso_section (a : AlgebraicSection L.sheaf) :
    pullSection x.map a ≫ F.lineFiberFrameIso.hom =
      scalarUnitSection (F.evaluation (F.coefficient a)) := by
  apply (sectionValue_bijective (structureModule ComplexBase)).injective
  rw [sectionValue_comp, F.lineFiberFrameIso_hom_apply, F.lineFiberCoefficient_global]
  change x.map.appLE F.frame.openSet ⊤ F.pointSupport (F.coefficient a) =
    sectionValue (sectionFromValue (E := structureModule ComplexBase)
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv (F.evaluation (F.coefficient a))))
  rw [sectionFromValue_spec]
  let e : RingSections ComplexBase ⊤ ≃+* ℂ :=
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv
  let b : RingSections ComplexBase ⊤ :=
    x.map.appLE F.frame.openSet ⊤ F.pointSupport (F.frame.localCoefficient a)
  have h : F.evaluation (F.coefficient a) = e b :=
    F.evaluation_eq_localRingValue (F.coefficient a)
  exact (e.symm_apply_apply b).symm.trans (congrArg e.symm h.symm)

end LeBrunSalamon.Refinement.Jets.PointFrame

namespace LeBrunSalamon.Core.SliceNonzeroProof

open LeBrunSalamon.PhaseFourteen

variable {d : ℕ} {X : SmoothProperComplexVariety d} {L : LineBundle X.scheme}
  {x : ComplexPoint X}

def firstIso (S : TwoPointSliceAt X x) (L : LineBundle X.scheme) :
    pullbackModule S.map (pullbackModule (firstProjection X.structureMap) L.sheaf) ≅
      L.sheaf :=
  (Scheme.Modules.pullbackComp S.map (firstProjection X.structureMap)).app L.sheaf ≪≫
    (Scheme.Modules.pullbackCongr S.firstLaw).app L.sheaf ≪≫
      (Scheme.Modules.pullbackId X.scheme).app L.sheaf

theorem firstIso_section (S : TwoPointSliceAt X x) (a : AlgebraicSection L.sheaf) :
    pullSection S.map (pullSection (firstProjection X.structureMap) a) ≫
      (firstIso S L).hom = a := by
  simp only [firstIso, Iso.trans_hom, Iso.app_hom]
  rw [← Category.assoc, ← Category.assoc,
    CanonicalPullbackSectionProof.pullSection_comp,
    ExternalExchangeCoherenceProof.pullSection_congr,
    ExternalExchangeCoherenceProof.pullSection_id]

def secondIso (S : TwoPointSliceAt X x) (L : LineBundle X.scheme) :
    pullbackModule S.map (pullbackModule (secondProjection X.structureMap) L.sheaf) ≅
      pullbackModule X.structureMap (pullbackModule x.map L.sheaf) :=
  pullbackSquareIso S.map (secondProjection X.structureMap)
    X.structureMap x.map S.secondLaw L.sheaf

theorem secondIso_section (S : TwoPointSliceAt X x) (a : AlgebraicSection L.sheaf) :
    pullSection S.map (pullSection (secondProjection X.structureMap) a) ≫
      (secondIso S L).hom = pullSection X.structureMap (pullSection x.map a) :=
  pullbackSquareIso_onSections S.map (secondProjection X.structureMap)
    X.structureMap x.map S.secondLaw a

/-- Tensor pullback, both actual slice projection laws, and the fixed point
frame give a specified isomorphism from the sliced external line to L. -/
def lineIso (S : TwoPointSliceAt X x)
    (e : pullbackModule x.map L.sheaf ≅ structureModule ComplexBase) :
    pullbackModule S.map (externalSquareLine X.structureMap L).sheaf ≅ L.sheaf := by
  letI := tensorPullbackComparison_isIso S.map
    (pullbackModule (firstProjection X.structureMap) L.sheaf)
    (pullbackModule (secondProjection X.structureMap) L.sheaf)
  exact (asIso (tensorPullbackComparison S.map
      (pullbackModule (firstProjection X.structureMap) L.sheaf)
      (pullbackModule (secondProjection X.structureMap) L.sheaf))).symm ≪≫
    tensorIso (firstIso S L)
      (secondIso S L ≪≫ (Scheme.Modules.pullback X.structureMap).mapIso e ≪≫
        unitPullbackIso X.structureMap) ≪≫
      TensorConstruction.rightUnitIso L.sheaf

section ScalarUnitSectionNotation

local notation "sectionFromValue" =>
  LeBrunSalamon.PhaseTwentyEight.sectionFromValue (E := structureModule X.scheme)

theorem pull_scalarUnitSection (c : ℂ) :
    pullSection X.structureMap (scalarUnitSection c) ≫
      (unitPullbackIso X.structureMap).hom =
        sectionFromValue (complexConstant X.structureMap ⊤ c) := by
  apply (sectionValue_bijective (structureModule X.scheme)).injective
  simp only [sectionValue_comp, pullSection_value, scalarUnitSection,
    sectionFromValue_spec]
  change (unitPullbackMap X.structureMap).app (X.structureMap ⁻¹ᵁ ⊤)
    (pullLocalSection X.structureMap (structureModule ComplexBase) ⊤
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c)) = complexConstant X.structureMap ⊤ c
  rw [PointFrame.LocalFrameJetProof.unitPullbackMap_local]
  simp [complexConstant]

theorem tensor_scalar_section (a : AlgebraicSection L.sheaf) (c : ℂ) :
    tensorSection a (sectionFromValue (complexConstant X.structureMap ⊤ c)) ≫
      (TensorConstruction.rightUnitIso L.sheaf).hom = scaleSection X c a := by
  apply (sectionValue_bijective L.sheaf).injective
  rw [sectionValue_comp, sectionValue_tensorSection,
    TensorConstruction.rightUnitIso_hom_pair, sectionFromValue_spec]
  exact (sectionFromValue_spec _).symm

end ScalarUnitSectionNotation

/-- The comparison is normalized on every actual pure external section. -/
theorem lineIso_product (S : TwoPointSliceAt X x) (F : PointFrame X L x)
    (a b : AlgebraicSection L.sheaf) :
    pullSection S.map (externalProductSection X.structureMap a b) ≫
      (lineIso S F.lineFiberFrameIso).hom =
        scaleSection X (F.evaluation (F.coefficient b)) a := by
  letI := tensorPullbackComparison_isIso S.map
    (pullbackModule (firstProjection X.structureMap) L.sheaf)
    (pullbackModule (secondProjection X.structureMap) L.sheaf)
  simp only [lineIso, Iso.trans_hom, Iso.symm_hom, tensorIso,
    Functor.mapIso_hom, Iso.app_hom]
  rw [externalProductSection, ← tensorPullbackComparison_onSections]
  simp only [Category.assoc, asIso_inv, IsIso.hom_inv_id_assoc]
  rw [← Category.assoc, tensorSection_map, firstIso_section]
  rw [← Category.assoc, ← Category.assoc, secondIso_section,
    ← ExternalExchangeCoherenceProof.pullSection_map,
    F.lineFiberFrameIso_section, pull_scalarUnitSection, tensor_scalar_section]

/-- Canonical slice transport is additive; no independence of an expansion
or its coefficient families is built into the construction. -/
def sectionMap (S : TwoPointSliceAt X x)
    (e : pullbackModule x.map L.sheaf ≅ structureModule ComplexBase) :
    ExternalSquareSections X L →+ AlgebraicSection L.sheaf where
  toFun B := pullSection S.map B ≫ (lineIso S e).hom
  map_zero' := by
    simp only [pullSection, restrictSection, Functor.map_zero, comp_zero, zero_comp]
  map_add' a b := by
    simp only [pullSection, restrictSection, Functor.map_add,
      Preadditive.comp_add, Preadditive.add_comp]

theorem contraction_zero_of_slice_zero {B : ExternalSquareSections X L}
    (E : ExternalExpansion X L B) (S : TwoPointSliceAt X x)
    (F : PointFrame X L x) (hzero : restrictSection S.map B = 0) :
    (∑ i, scaleSection X (F.evaluation (F.coefficient (E.right i))) (E.left i)) = 0 := by
  let m := sectionMap S F.lineFiberFrameIso
  calc
    _ = ∑ i, m (externalProductSection X.structureMap (E.left i) (E.right i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (lineIso_product S F (E.left i) (E.right i)).symm
    _ = m (∑ i, externalProductSection X.structureMap (E.left i) (E.right i)) :=
      (map_sum m _ _).symm
    _ = m B := congrArg m E.equation.symm
    _ = 0 := by
      change ((unitPullbackIso S.map).inv ≫ restrictSection S.map B) ≫ _ = 0
      rw [hzero, comp_zero, zero_comp]

theorem scalar_contraction_zero_of_slice_zero {B : ExternalSquareSections X L}
    (E : ExternalExpansion X L B) (S : TwoPointSliceAt X x)
    (F : PointFrame X L x) (hzero : restrictSection S.map B = 0) :
    (∑ i, F.evaluation (F.coefficient (E.right i)) • F.coefficient (E.left i)) = 0 := by
  have h := congrArg (ScalarSections.coefficientAddHom F.frame)
    (contraction_zero_of_slice_zero E S F hzero)
  rw [map_sum, map_zero] at h
  change (∑ i, F.frame.localCoefficient
    (scaleSection X (F.evaluation (F.coefficient (E.right i))) (E.left i))) = 0 at h
  simp_rw [scaleSection_local] at h
  exact h

/-- Twice differentiating the actual zero contraction kills the evaluated
Hessian in the interchanged expansion. Redundant summands are harmless. -/
theorem hessian_zero_of_slice_zero {B : ExternalSquareSections X L}
    (E : ExternalExpansion X L B) (hB : IsSymmetricExternalSection X.structureMap L B)
    (S : TwoPointSliceAt X x) (F : PointFrame X L x)
    (hzero : restrictSection S.map B = 0)
    (v : SectionsOn (tangentSheaf X.structureMap) F.frame.openSet) :
    F.evaluation ((KernelTaylorProof.flippedExpansion E hB).secondSlotSecond
      F.frame v v) = 0 := by
  let D := F.affineVectorEquiv v
  have h := congrArg (fun a : F.ChartRing => D (D a))
    (scalar_contraction_zero_of_slice_zero E S F hzero)
  simp only [map_sum, Derivation.map_smul, map_zero] at h
  have he := congrArg F.evaluation h
  simp only [map_sum, map_smul, map_zero, smul_eq_mul] at he
  change F.evaluation (∑ i, F.coefficient (E.right i) *
    D (D (F.coefficient (E.left i)))) = 0
  simpa only [map_sum, map_mul] using he

end LeBrunSalamon.Core.SliceNonzeroProof

namespace LeBrunSalamon.Core.NormalizedContactKernel

open LeBrunSalamon.PhaseFourteen

variable {n : ℕ} {X : SmoothProperComplexVariety (2*n+1)}
  {C : IntrinsicContactStructure X}

/-- Source: nonvanishing of B_x in the proof of jet:criterion.
This is nonvanishing of an actual restricted section, not of a label.
The canonical slice here is y |-> (y,x); symmetry treats the other slot. -/
theorem slice_nonzero (K : NormalizedContactKernel X C) (x : ComplexPoint X) :
    restrictSection (canonicalTwoPointSlice X x).map K.twoPointSection ≠ 0 := by
  intro hzero
  obtain ⟨F⟩ := pointFrame_exists X C.sequence.line x
  obtain ⟨v, hv⟩ := localContactValue_unit C F.frame
  have hz := SliceNonzeroProof.hessian_zero_of_slice_zero K.expansion K.symmetric
    (canonicalTwoPointSlice X x) F hzero v
  have hn := normalizedSymbol_on_any_expansion C K.normalized
    (KernelTaylorProof.flippedExpansion K.expansion K.symmetric) F.frame v v
  rw [hn, hv] at hz
  simp only [mul_one, map_ofNat] at hz
  norm_num at hz

end LeBrunSalamon.Core.NormalizedContactKernel


namespace LeBrunSalamon.Refinement.Jets.PointFrame.LocalFrameJetProof

/-- The specified affine line frame pulled back to any open contained in
its inverse image. The coefficient map includes the canonical unit map. -/
def coefficientOn {Y Z : Scheme} {M : LineBundle Y}
    (H : AffineLineFrame M) (f : Z ⟶ Y) (V : Z.Opens)
    (hV : V ≤ f ⁻¹ᵁ H.openSet) :
    SectionsOn (pullbackModule f M.sheaf) V ≃ₗ[RingSections Z V] RingSections Z V :=
  (((SheafOfModules.evaluation (Z.ringCatSheaf.over (f ⁻¹ᵁ H.openSet))
    (op (Over.mk (homOfLE hV)))).mapIso
      (pullOverIso f H.openSet (frameIso H))).symm ≪≫
    ((SheafOfModules.evaluation Z.ringCatSheaf (op V)).mapIso
      (unitPullbackIso f))).toLinearEquiv

/-- Restriction commutes with the actual pulled frame. -/
theorem coefficientOn_restrict {Y Z : Scheme} {M : LineBundle Y}
    (H : AffineLineFrame M) (f : Z ⟶ Y) {V W : Z.Opens}
    (hV : V ≤ f ⁻¹ᵁ H.openSet) (hW : W ≤ f ⁻¹ᵁ H.openSet) (hVW : V ≤ W)
    (a : SectionsOn (pullbackModule f M.sheaf) W) :
    coefficientOn H f V hV
      ((pullbackModule f M.sheaf).presheaf.map (homOfLE hVW).op a) =
        Z.presheaf.map (homOfLE hVW).op (coefficientOn H f W hW a) := by
  let q : (pullbackModule f M.sheaf).over (f ⁻¹ᵁ H.openSet) ⟶
      (structureModule Z).over (f ⁻¹ᵁ H.openSet) :=
    (pullOverIso f H.openSet (frameIso H)).inv ≫
      (unitPullbackMap f).over (f ⁻¹ᵁ H.openSet)
  let j : Over.mk (homOfLE hV) ⟶ Over.mk (homOfLE hW) :=
    Over.homMk (homOfLE hVW) (Subsingleton.elim _ _)
  exact PresheafOfModules.naturality_apply q.val j.op a

/-- The coefficient of a restricted actual local pullback is the actual
structure-sheaf map on that same source open. -/
theorem coefficientOn_local {Y Z : Scheme} {M : LineBundle Y}
    (H : AffineLineFrame M) (f : Z ⟶ Y) (V : Z.Opens)
    (hV : V ≤ f ⁻¹ᵁ H.openSet) (a : RingSections Y H.openSet) :
    coefficientOn H f V hV
      ((pullbackModule f M.sheaf).presheaf.map (homOfLE hV).op
        (pullLocalSection f M.sheaf H.openSet (H.coefficient.symm a))) =
          f.appLE H.openSet V hV a := by
  have h := coefficientOn_restrict H f hV le_rfl hV
    (pullLocalSection f M.sheaf H.openSet (H.coefficient.symm a))
  change coefficientOn H f V hV
      ((pullbackModule f M.sheaf).presheaf.map (homOfLE hV).op
        (pullLocalSection f M.sheaf H.openSet (H.coefficient.symm a))) =
    Z.presheaf.map (homOfLE hV).op
      (pulledCoefficient H f (pullLocalSection f M.sheaf H.openSet
        (H.coefficient.symm a))) at h
  rw [pulledCoefficient_local] at h
  exact h

/-- Normalization for actual global sections, restricted only after their
pullback. No global extension of the chosen local frame is required. -/
theorem coefficientOn_global {Y Z : Scheme} {M : LineBundle Y}
    (H : AffineLineFrame M) (f : Z ⟶ Y) (V : Z.Opens)
    (hV : V ≤ f ⁻¹ᵁ H.openSet) (a : AlgebraicSection M.sheaf) :
    coefficientOn H f V hV
      ((pullbackModule f M.sheaf).presheaf.map (homOfLE le_top).op
        (sectionValue (pullSection f a))) =
          f.appLE H.openSet V hV (H.localCoefficient a) := by
  have hs : H.coefficient.symm (H.localCoefficient a) =
      M.sheaf.presheaf.map (homOfLE le_top).op (sectionValue a) := by
    rw [AffineLineFrame.localCoefficient, H.coefficient.symm_apply_apply,
      ScalarSections.section_app_one]
  have hn := (sheafHom_naturality
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M.sheaf)
    (homOfLE (show H.openSet ≤ ⊤ from le_top)) (sectionValue a)).symm
  change pullLocalSection f M.sheaf H.openSet
      (M.sheaf.presheaf.map (homOfLE le_top).op (sectionValue a)) =
    (pullbackModule f M.sheaf).presheaf.map (homOfLE le_top).op
      (pullLocalSection f M.sheaf ⊤ (sectionValue a)) at hn
  have hp : (pullLocalSection f M.sheaf ⊤ (sectionValue a) :
      GlobalSections (pullbackModule f M.sheaf)) =
      sectionValue (pullSection f a) :=
    (pullSection_value f a).symm
  have hg : pullLocalSection f M.sheaf H.openSet
      (H.coefficient.symm (H.localCoefficient a)) =
      (pullbackModule f M.sheaf).presheaf.map (homOfLE le_top).op
        (sectionValue (pullSection f a)) :=
    (congrArg (pullLocalSection f M.sheaf H.openSet) hs).trans
      (hn.trans (congrArg
        (fun b : GlobalSections (pullbackModule f M.sheaf) =>
          (pullbackModule f M.sheaf).presheaf.map
            (homOfLE (show f ⁻¹ᵁ H.openSet ≤ ⊤ from le_top)).op b) hp))
  have hr (b : GlobalSections (pullbackModule f M.sheaf)) :
      (pullbackModule f M.sheaf).presheaf.map (homOfLE hV).op
        ((pullbackModule f M.sheaf).presheaf.map (homOfLE le_top).op b) =
      (pullbackModule f M.sheaf).presheaf.map (homOfLE le_top).op b := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  have hk :
      (pullbackModule f M.sheaf).presheaf.map (homOfLE hV).op
        (pullLocalSection f M.sheaf H.openSet
          (H.coefficient.symm (H.localCoefficient a))) =
      (pullbackModule f M.sheaf).presheaf.map (homOfLE le_top).op
        (sectionValue (pullSection f a)) :=
    (congrArg
      (fun b : SectionsOn (pullbackModule f M.sheaf) (f ⁻¹ᵁ H.openSet) =>
        (pullbackModule f M.sheaf).presheaf.map (homOfLE hV).op b) hg).trans
      (hr (sectionValue (pullSection f a)))
  exact (congrArg (coefficientOn H f V hV) hk).symm.trans
    (coefficientOn_local H f V hV (H.localCoefficient a))

end LeBrunSalamon.Refinement.Jets.PointFrame.LocalFrameJetProof

namespace LeBrunSalamon.Skeleton.AdjointContactTransportProof

open AdjointComparisonProof Core.ExternalTensorCoordinates
open PointFrame.LocalFrameJetProof

/-- Pullback along a scheme isomorphism is an actual equivalence of
module-sheaf categories, with the original canonical composition maps. -/
def pullbackEquivalence {Y Z : Scheme} (e : Y ≅ Z) : OModule Z ≌ OModule Y :=
  CategoryTheory.Equivalence.mk (Scheme.Modules.pullback e.hom) (Scheme.Modules.pullback e.inv)
    (Scheme.Modules.pullbackComp e.inv e.hom ≪≫
      Scheme.Modules.pullbackCongr e.inv_hom_id ≪≫ Scheme.Modules.pullbackId Z).symm
    (Scheme.Modules.pullbackComp e.hom e.inv ≪≫
      Scheme.Modules.pullbackCongr e.hom_inv_id ≪≫ Scheme.Modules.pullbackId Y)

/-- Every section on the inverse image of an open comes from a unique
section of the original sheaf when the scheme map is an isomorphism. -/
theorem pullLocalSection_bijective {Y Z : Scheme} (e : Y ≅ Z)
    (E : OModule Z) (U : Z.Opens) :
    Function.Bijective (pullLocalSection e.hom E U) := by
  letI : (Scheme.Modules.pullback e.hom).IsEquivalence :=
    (pullbackEquivalence e).isEquivalence_functor
  letI : IsIso (Scheme.Modules.pullbackPushforwardAdjunction e.hom).unit := inferInstance
  exact ConcreteCategory.bijective_of_isIso
    (((Scheme.Modules.pullbackPushforwardAdjunction e.hom).unit.app E).app U)

theorem constants_pull {Y Z : Scheme} (f : Y ⟶ Z)
    (sY : Y ⟶ ComplexBase) (sZ : Z ⟶ ComplexBase)
    (hf : f ≫ sZ = sY) (U : Z.Opens) (c : ℂ) :
    f.app U (constants sZ U c) = constants sY (f ⁻¹ᵁ U) c := by
  have h := congrArg (fun q : Z.presheaf.obj (op ⊤) ⟶ Y.presheaf.obj (op (f ⁻¹ᵁ U)) =>
    q (constants sZ ⊤ c)) (f.naturality (homOfLE (show U ≤ ⊤ from le_top)).op)
  change f.app U (Z.presheaf.map (homOfLE le_top).op (constants sZ ⊤ c)) =
    Y.presheaf.map (homOfLE le_top).op (f.appTop (constants sZ ⊤ c)) at h
  rw [constants_restrict, constants_naturality f sY sZ hf, constants_restrict] at h
  exact h

def coefficientRingIso {Y Z : Scheme} (e : Y ≅ Z)
    (sY : Y ⟶ ComplexBase) (sZ : Z ⟶ ComplexBase)
    (he : e.hom ≫ sZ = sY) (U : Z.Opens) :
    Coefficients sZ U ≃ₐ[ℂ] Coefficients sY (e.hom ⁻¹ᵁ U) where
  __ := (asIso (e.hom.app U)).commRingCatIsoToRingEquiv
  commutes' := constants_pull e.hom sY sZ he U

theorem coefficientRingIso_apply {Y Z : Scheme} (e : Y ≅ Z)
    (sY : Y ⟶ ComplexBase) (sZ : Z ⟶ ComplexBase)
    (he : e.hom ≫ sZ = sY) (U : Z.Opens) (a : Coefficients sZ U) :
    coefficientRingIso e sY sZ he U a = e.hom.app U a := rfl

/-- The original derivative of a scheme isomorphism is the pullback
of a genuine local target vector, and it differentiates every pulled
function by the normalized chain rule. -/
theorem differential_local_vector {d r : ℕ}
    (X : SmoothProperComplexVariety d) (Y : SmoothProperComplexVariety r)
    (e : X.scheme ≅ Y.scheme) (he : e.hom ≫ Y.structureMap = X.structureMap)
    (U : Y.scheme.Opens)
    (u : SectionsOn (tangentSheaf X.structureMap) (e.hom ⁻¹ᵁ U)) :
    ∃ v : SectionsOn (tangentSheaf Y.structureMap) U,
      pullLocalSection e.hom (tangentSheaf Y.structureMap) U v =
        (differentialOver X Y e.hom he).app (e.hom ⁻¹ᵁ U) u ∧
      ∀ a : RingSections Y.scheme U,
        tangentActs X.structureMap (e.hom ⁻¹ᵁ U) u (e.hom.app U a) =
          e.hom.app U (tangentActs Y.structureMap U v a) := by
  obtain ⟨v, hv⟩ := (pullLocalSection_bijective e (tangentSheaf Y.structureMap) U).surjective
    ((differentialOver X Y e.hom he).app (e.hom ⁻¹ᵁ U) u)
  refine ⟨v, hv, ?_⟩
  intro a
  have h := SourceTangent.differentialOver_local_function X Y e.hom he U a u
  rw [← hv] at h
  change (unitPullbackMap e.hom).app (e.hom ⁻¹ᵁ U)
      ((pullbackPair e.hom (dualEvaluation (cotangentSheaf Y.structureMap))).apply
        (e.hom ⁻¹ᵁ U) (pullLocalSection e.hom (tangentSheaf Y.structureMap) U v)
        (pullLocalSection e.hom (cotangentSheaf Y.structureMap) U
          ((cotangentPresentation Y.structureMap).differential.apply U a))) = _ at h
  rw [pullbackPair_normalized, unitPullbackMap_local] at h
  exact h.symm

def pulledFrame {Y Z : Scheme} {L : LineBundle Y} {M : LineBundle Z}
    (e : Y ≅ Z) (l : pullbackModule e.hom M.sheaf ≅ L.sheaf)
    (G : AffineLineFrame M) : AffineLineFrame L where
  openSet := e.hom ⁻¹ᵁ G.openSet
  isAffine := G.isAffine.preimage_of_isIso e.hom
  coefficient :=
    (((SheafOfModules.evaluation Y.ringCatSheaf (op (e.hom ⁻¹ᵁ G.openSet))).mapIso
      l.symm).toLinearEquiv) ≪≫ₗ (pulledCoefficient G e.hom)

theorem pulledFrame_global {Y Z : Scheme} {L : LineBundle Y} {M : LineBundle Z}
    (e : Y ≅ Z) (l : pullbackModule e.hom M.sheaf ≅ L.sheaf)
    (G : AffineLineFrame M) (a : AlgebraicSection M.sheaf) :
    (pulledFrame e l G).localCoefficient (pullSection e.hom a ≫ l.hom) =
      e.hom.app G.openSet (G.localCoefficient a) := by
  change pulledCoefficient G e.hom
    (l.inv.app (e.hom ⁻¹ᵁ G.openSet)
      (l.hom.app (e.hom ⁻¹ᵁ G.openSet)
        (Scheme.Modules.Hom.app (pullSection e.hom a) (e.hom ⁻¹ᵁ G.openSet)
          (1 : RingSections Y (e.hom ⁻¹ᵁ G.openSet))))) = _
  calc
    _ = pulledCoefficient G e.hom
        (Scheme.Modules.Hom.app (pullSection e.hom a) (e.hom ⁻¹ᵁ G.openSet)
          (1 : RingSections Y (e.hom ⁻¹ᵁ G.openSet))) :=
      congrArg (pulledCoefficient G e.hom)
        (ExternalExchangeCoherenceProof.iso_inv_hom_app l (e.hom ⁻¹ᵁ G.openSet)
          (Scheme.Modules.Hom.app (pullSection e.hom a) (e.hom ⁻¹ᵁ G.openSet)
            (1 : RingSections Y (e.hom ⁻¹ᵁ G.openSet))))
    _ = pulledCoefficient G e.hom
        ((pullbackModule e.hom M.sheaf).presheaf.map (homOfLE le_top).op
          (sectionValue (pullSection e.hom a))) :=
      congrArg (pulledCoefficient G e.hom)
        (ScalarSections.section_app_one (pullSection e.hom a) (e.hom ⁻¹ᵁ G.openSet))
    _ = e.hom.app G.openSet (G.localCoefficient a) := by
      change coefficientOn G e.hom (e.hom ⁻¹ᵁ G.openSet) le_rfl
        ((pullbackModule e.hom M.sheaf).presheaf.map (homOfLE le_top).op
          (sectionValue (pullSection e.hom a))) = _
      simpa only [Scheme.Hom.appLE, homOfLE_refl, op_id,
        CategoryTheory.Functor.map_id, Category.comp_id] using
        coefficientOn_global G e.hom (e.hom ⁻¹ᵁ G.openSet) le_rfl a

section FrameCoefficientTransformElaboration

theorem frame_coefficient_transform {Y : Scheme} (s : Y ⟶ ComplexBase)
    {L : LineBundle Y} (F : AffineLineFrame L) {N M : ℕ}
    (T : (Fin (N+1) → ℂ) →ₗ[ℂ] (Fin (M+1) → ℂ))
    (a : Fin (N+1) → AlgebraicSection L.sheaf) (j : Fin (M+1)) :
    F.localCoefficient (transformSections s T a j) =
      transformValues (V := Coefficients s F.openSet) T
        (fun i => (F.localCoefficient (a i) : Coefficients s F.openSet)) j := by
  calc
    _ = coefficientLinear s L F (sectionValue (transformSections s T a j)) :=
      (coefficientLinear_sectionValue s L F (transformSections s T a j)).symm
    _ = coefficientLinear s L F
        (transformValues (V := ComplexSections s L.sheaf) T
          (fun i => (sectionValue (a i) : ComplexSections s L.sheaf)) j) :=
      congrArg (coefficientLinear s L F) (transformSections_value s T a j)
    _ = transformValues (V := Coefficients s F.openSet) T
        (fun i => coefficientLinear s L F (sectionValue (a i))) j :=
      transformValues_map (V := ComplexSections s L.sheaf)
        (W := Coefficients s F.openSet) T (coefficientLinear s L F)
        (fun i => (sectionValue (a i) : ComplexSections s L.sheaf)) j
    _ = _ :=
      congrArg
        (fun b : Fin (N+1) → Coefficients s F.openSet =>
          transformValues (V := Coefficients s F.openSet) T b j)
        (funext (fun i => coefficientLinear_sectionValue s L F (a i)))

end FrameCoefficientTransformElaboration

theorem canonicalContact_scalar {n : ℕ} {X : ContactFanoManifold n}
    (A : AdjointContactPresentation X) (F : AffineLineFrame X.contact.sequence.line)
    (u : SectionsOn (tangentSheaf X.variety.structureMap) F.openSet) :
    localContactValue X.contact F u = 0 ↔
      scalarCanonicalCondition A.algebra A.basis (Coefficients X.variety.structureMap F.openSet)
        (coefficientDerivation X.variety.structureMap F.openSet u)
        (fun i => F.localCoefficient (coordinateSection A i)) := by
  exact A.canonicalContact F u

/-- The canonical-contact predicates agree on every actual inverse
image of a target affine line frame. Both derivative and form maps are
the original sheaf morphisms from the contact sequences. -/
theorem local_kernel_iff {n : ℕ} {X Y : ContactFanoManifold n}
    (A : AdjointContactPresentation X) (B : AdjointContactPresentation Y)
    (e : A.algebra.carrier ≃ₗ⁅ℂ⁆ B.algebra.carrier)
    (f : X.variety.scheme ≅ Y.variety.scheme)
    (hf : f.hom ≫ Y.variety.structureMap = X.variety.structureMap)
    (l : pullbackModule f.hom Y.contact.sequence.line.sheaf ≅ X.contact.sequence.line.sheaf)
    (hl : ∀ j, pullSection f.hom (coordinateSection B j) ≫ l.hom =
      transformSections X.variety.structureMap (coordinateEquiv A B e).toLinearMap
        (coordinateSection A) j)
    (G : AffineLineFrame Y.contact.sequence.line)
    (u : SectionsOn (tangentSheaf X.variety.structureMap) (f.hom ⁻¹ᵁ G.openSet)) :
    X.contact.sequence.form.app (f.hom ⁻¹ᵁ G.openSet) u = 0 ↔
      ((Scheme.Modules.pullback f.hom).map Y.contact.sequence.form).app (f.hom ⁻¹ᵁ G.openSet)
        ((differentialOver X.variety Y.variety f.hom hf).app (f.hom ⁻¹ᵁ G.openSet) u) = 0 := by
  let F := pulledFrame f l G
  let R := Coefficients X.variety.structureMap F.openSet
  let S := Coefficients Y.variety.structureMap G.openSet
  let q := coefficientRingIso f X.variety.structureMap Y.variety.structureMap hf G.openSet
  let w := fun i => (F.localCoefficient (coordinateSection A i) : R)
  let z := fun j => (G.localCoefficient (coordinateSection B j) : S)
  obtain ⟨v, hv, hD⟩ := differential_local_vector X.variety Y.variety f hf G.openSet u
  have hw : (fun j => q (z j)) =
      transformValues (V := Coefficients X.variety.structureMap F.openSet)
        (coordinateEquiv A B e).toLinearMap w := by
    funext j
    change f.hom.app G.openSet (G.localCoefficient (coordinateSection B j)) = _
    exact (pulledFrame_global f l G (coordinateSection B j)).symm.trans
      ((congrArg
        (fun a : AlgebraicSection X.contact.sequence.line.sheaf => F.localCoefficient a)
        (hl j)).trans
          (frame_coefficient_transform X.variety.structureMap F _ _ j))
  have hforms : localContactValue X.contact F u = 0 ↔ localContactValue Y.contact G v = 0 := by
    rw [canonicalContact_scalar A F u, canonicalContact_scalar B G v]
    change scalarCanonicalCondition A.algebra A.basis R
        (coefficientDerivation X.variety.structureMap F.openSet u) w ↔
      scalarCanonicalCondition B.algebra B.basis S
        (coefficientDerivation Y.variety.structureMap G.openSet v) z
    rw [← scalarCanonicalCondition_equiv A B e R, ← hw]
    exact scalarCanonicalCondition_ringEquiv B.basis q
      (coefficientDerivation Y.variety.structureMap G.openSet v)
      (coefficientDerivation X.variety.structureMap F.openSet u) hD z
  have hmap : ((Scheme.Modules.pullback f.hom).map Y.contact.sequence.form).app
      (f.hom ⁻¹ᵁ G.openSet)
      ((differentialOver X.variety Y.variety f.hom hf).app (f.hom ⁻¹ᵁ G.openSet) u) =
      pullLocalSection f.hom Y.contact.sequence.line.sheaf G.openSet
        (Y.contact.sequence.form.app G.openSet v) := by
    have hn : ((Scheme.Modules.pullback f.hom).map Y.contact.sequence.form).app
        (f.hom ⁻¹ᵁ G.openSet)
        (pullLocalSection f.hom (tangentSheaf Y.variety.structureMap) G.openSet v) =
        pullLocalSection f.hom Y.contact.sequence.line.sheaf G.openSet
          (Y.contact.sequence.form.app G.openSet v) :=
      ExternalExchangeCoherenceProof.pullLocalSection_map
        f.hom Y.contact.sequence.form G.openSet v
    exact (congrArg
      (fun a : SectionsOn (pullbackModule f.hom (tangentSheaf Y.variety.structureMap))
          (f.hom ⁻¹ᵁ G.openSet) =>
        ((Scheme.Modules.pullback f.hom).map Y.contact.sequence.form).app
          (f.hom ⁻¹ᵁ G.openSet) a) hv.symm).trans hn
  rw [hmap]
  have hzero : pullLocalSection f.hom Y.contact.sequence.line.sheaf G.openSet
      (0 : SectionsOn Y.contact.sequence.line.sheaf G.openSet) = 0 := by
    exact map_zero ((((Scheme.Modules.pullbackPushforwardAdjunction f.hom).unit.app
      Y.contact.sequence.line.sheaf).app G.openSet).hom)
  constructor
  · intro hu
    have hc : localContactValue X.contact F u = 0 := by
      change F.coefficient (X.contact.sequence.form.app F.openSet u) = 0
      exact (congrArg F.coefficient
        (show X.contact.sequence.form.app F.openSet u = 0 from hu)).trans
          F.coefficient.map_zero
    have hd := hforms.mp hc
    have hv0 : Y.contact.sequence.form.app G.openSet v = 0 := by
      apply G.coefficient.injective
      simpa only [localContactValue, map_zero] using hd
    rw [hv0, hzero]
  · intro hu
    have hv0 : Y.contact.sequence.form.app G.openSet v = 0 :=
      (pullLocalSection_bijective f Y.contact.sequence.line.sheaf G.openSet).injective
        (hu.trans hzero.symm)
    have hd : localContactValue Y.contact G v = 0 := by
      simp only [localContactValue, hv0, map_zero]
    have hc := hforms.mpr hd
    apply F.coefficient.injective
    exact (show F.coefficient
      (X.contact.sequence.form.app (f.hom ⁻¹ᵁ G.openSet) u) = 0 from hc).trans
        F.coefficient.map_zero.symm

end LeBrunSalamon.Skeleton.AdjointContactTransportProof

namespace LeBrunSalamon.Skeleton.AdjointContactTransportProof

open AdjointComparisonProof

/-- On a spectrum, faithful affine global sections detect actual
quasi-coherent sheaf morphisms. -/
theorem spec_hom_ext {R : CommRingCat}
    {E G : OModule (Spec R)} [E.IsQuasicoherent] [G.IsQuasicoherent]
    (p q : E ⟶ G) (h : ∀ a, p.app ⊤ a = q.app ⊤ a) : p = q := by
  let Q := SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf
  let E' : Q.FullSubcategory := ⟨E, inferInstance⟩
  let G' : Q.FullSubcategory := ⟨G, inferInstance⟩
  let p' : E' ⟶ G' := ObjectProperty.homMk p
  let q' : E' ⟶ G' := ObjectProperty.homMk q
  have hs : (tildeEquiv (R := R)).inverse.map p' = (tildeEquiv (R := R)).inverse.map q' := by
    ext a
    exact h a
  exact congrArg (fun r : E' ⟶ G' => Q.ι.map r)
    ((tildeEquiv (R := R)).inverse.map_injective hs)

theorem affine_hom_ext {Y : Scheme} [IsAffine Y]
    {E G : OModule Y} [E.IsQuasicoherent] [G.IsQuasicoherent]
    (p q : E ⟶ G) (h : ∀ a, p.app ⊤ a = q.app ⊤ a) : p = q := by
  let e := Y.isoSpec
  let A := Scheme.Modules.restrictFunctor e.inv
  let B := Scheme.Modules.restrictFunctor e.hom
  have hA : A.map p = A.map q := by
    apply spec_hom_ext
    change ∀ a, p.app (e.inv ''ᵁ ⊤) a = q.app (e.inv ''ᵁ ⊤) a
    have htop : e.inv ''ᵁ ⊤ = ⊤ :=
      (Scheme.Hom.image_top_eq_opensRange e.inv).trans
        (Scheme.Hom.opensRange_of_isIso e.inv)
    erw [htop]
    exact h
  let c : A ⋙ B ≅ 𝟭 (OModule Y) :=
    (Scheme.Modules.restrictFunctorComp e.hom e.inv).symm ≪≫
      Scheme.Modules.restrictFunctorCongr e.hom_inv_id ≪≫ Scheme.Modules.restrictFunctorId
  have recover (r : E ⟶ G) : r = c.inv.app E ≫ B.map (A.map r) ≫ c.hom.app G := by
    have hr := c.hom.naturality r
    simpa only [Functor.id_obj, Functor.id_map, Functor.comp_map,
      ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp] using
      congrArg (fun a => c.inv.app E ≫ a) hr.symm
  rw [recover p, hA, ← recover q]

private theorem over_eq_terminal {Y : Scheme} {U : Y.Opens}
    (W : Over U) (h : W.left = U) : W = Over.mk (𝟙 U) := by
  obtain ⟨V, i, rfl⟩ := Over.mk_surjective W
  change V = U at h
  subst V
  exact congrArg (fun i : U ⟶ U => Over.mk i) (Subsingleton.elim _ _)

theorem affine_over_hom_ext {Y : Scheme} {E G : OModule Y}
    [E.IsQuasicoherent] [G.IsQuasicoherent] (U : Y.Opens) (hU : IsAffineOpen U)
    (p q : E.over U ⟶ G.over U)
    (h : ∀ a, p.val.app (op (Over.mk (𝟙 U))) a =
      q.val.app (op (Over.mk (𝟙 U))) a) : p = q := by
  let A := (Scheme.Modules.overEquiv U).functor
  letI : IsAffine U.toScheme := hU
  letI : (A.obj (E.over U)).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).prop_of_iso
      ((Scheme.Modules.overFunctorEquiv U).app E).symm inferInstance
  letI : (A.obj (G.over U)).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).prop_of_iso
      ((Scheme.Modules.overFunctorEquiv U).app G).symm inferInstance
  have htop : U.overEquivalence.inverse.obj ⊤ = Over.mk (𝟙 U) := by
    apply over_eq_terminal
    change U.ι ''ᵁ ⊤ = U
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι]
  apply A.map_injective
  apply affine_hom_ext
  change ∀ a, p.val.app (op (U.overEquivalence.inverse.obj ⊤)) a =
    q.val.app (op (U.overEquivalence.inverse.obj ⊤)) a
  rw [htop]
  exact h

theorem hom_zero_on_affine_cover {Y : Scheme} {E G : OModule Y}
    [E.IsQuasicoherent] [G.IsQuasicoherent]
    {I : Type} (U : I → Y.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hcover : iSup U = ⊤)
    (p : E ⟶ G) (h : ∀ i a, p.app (U i) a = 0) : p = 0 := by
  apply P1Ideal.hom_ext_of_localSections U hcover
  intro i
  have ho : p.over (U i) = (0 : E ⟶ G).over (U i) := by
    apply affine_over_hom_ext (U i) (hU i)
    intro a
    exact h i a
  exact congrArg (fun q : E.over (U i) ⟶ G.over (U i) => q.val) ho

/-- Agreement of the actual local contact-form kernels yields the
required distribution isomorphism by the two genuine kernel universal
properties. No chosen replacement for the derivative is used. -/
theorem contactIso_of_local_kernel_iff {n : ℕ}
    {X Y : SmoothProperComplexVariety (2*n+1)}
    (C : IntrinsicContactStructure X) (D : IntrinsicContactStructure Y)
    (e : X.scheme ≅ Y.scheme) (he : e.hom ≫ Y.structureMap = X.structureMap)
    (h : ∀ (G : AffineLineFrame D.sequence.line)
      (u : SectionsOn (tangentSheaf X.structureMap) (e.hom ⁻¹ᵁ G.openSet)),
      C.sequence.form.app (e.hom ⁻¹ᵁ G.openSet) u = 0 ↔
        ((Scheme.Modules.pullback e.hom).map D.sequence.form).app (e.hom ⁻¹ᵁ G.openSet)
          ((differentialOver X Y e.hom he).app (e.hom ⁻¹ᵁ G.openSet) u) = 0) :
    Nonempty (ContactIso X Y C D) := by
  let F := Scheme.Modules.pullback e.hom
  letI : F.IsEquivalence := (pullbackEquivalence e).isEquivalence_functor
  let d := differentialOver X Y e.hom he
  letI : IsIso d := ContactDerivativeIsoProof.differentialOver_isIso X Y e.hom he
  letI : Mono C.sequence.inclusion := C.sequence.shortExact.mono_f
  letI : Mono D.sequence.inclusion := D.sequence.shortExact.mono_f
  letI : C.sequence.distribution.sheaf.IsQuasicoherent :=
    LocalExtensionSplitting.quasicoherent_of_locallyFreeRank C.sequence.distribution.locallyFree
  letI : C.sequence.line.sheaf.IsQuasicoherent :=
    LocalExtensionSplitting.quasicoherent_of_locallyFreeRank C.sequence.line.locallyFree
  letI : (F.obj D.sequence.distribution.sheaf).IsQuasicoherent :=
    LocalExtensionSplitting.quasicoherent_of_locallyFreeRank
      (pullback_locallyFree e.hom D.sequence.distribution.locallyFree)
  letI : (F.obj D.sequence.line.sheaf).IsQuasicoherent :=
    LocalExtensionSplitting.quasicoherent_of_locallyFreeRank
      (pullback_locallyFree e.hom D.sequence.line.locallyFree)
  let U := fun G : AffineLineFrame D.sequence.line => e.hom ⁻¹ᵁ G.openSet
  have hU (G : AffineLineFrame D.sequence.line) : IsAffineOpen (U G) :=
    G.isAffine.preimage_of_isIso e.hom
  have hcover : iSup U = ⊤ := by
    apply top_unique
    intro x hx
    obtain ⟨G, hG⟩ := affineLineFrames_cover D.sequence.line (e.hom x)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨G, hG⟩
  have hz : (C.sequence.inclusion ≫ d) ≫ F.map D.sequence.form = 0 := by
    apply hom_zero_on_affine_cover U hU hcover
    intro G a
    apply (h G (C.sequence.inclusion.app (U G) a)).mp
    exact congrArg (fun q : C.sequence.distribution.sheaf ⟶ C.sequence.line.sheaf =>
      q.app (U G) a) C.sequence.comp_zero
  let KD := KernelFork.ofι D.sequence.inclusion D.sequence.comp_zero
  have hKD : IsLimit (KD.map F) :=
    KernelFork.mapIsLimit KD D.sequence.shortExact.fIsKernel F
  obtain ⟨m, hm⟩ := KernelFork.IsLimit.lift' hKD (C.sequence.inclusion ≫ d) hz
  change m ≫ F.map D.sequence.inclusion = C.sequence.inclusion ≫ d at hm
  let r := F.map D.sequence.inclusion ≫ inv d
  have hrd : r ≫ d = F.map D.sequence.inclusion := by
    simp only [r, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hr : r ≫ C.sequence.form = 0 := by
    apply hom_zero_on_affine_cover U hU hcover
    intro G a
    apply (h G (r.app (U G) a)).mpr
    change ((r ≫ d) ≫ F.map D.sequence.form).app (U G) a = 0
    rw [hrd, ← Functor.map_comp, D.sequence.comp_zero, Functor.map_zero] <;> rfl
  obtain ⟨m', hm'⟩ := KernelFork.IsLimit.lift' C.sequence.shortExact.fIsKernel r hr
  change m' ≫ C.sequence.inclusion = r at hm'
  have hmm' : m ≫ m' = 𝟙 C.sequence.distribution.sheaf := by
    apply (cancel_mono C.sequence.inclusion).1
    calc
      _ = m ≫ r := by rw [Category.assoc, hm']
      _ = (m ≫ F.map D.sequence.inclusion) ≫ inv d := by
        simp only [r, Category.assoc]
      _ = (C.sequence.inclusion ≫ d) ≫ inv d := by rw [hm]
      _ = (𝟙 C.sequence.distribution.sheaf) ≫ C.sequence.inclusion := by
        simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id, Category.id_comp]
  have hm'm : m' ≫ m = 𝟙 (F.obj D.sequence.distribution.sheaf) := by
    apply (cancel_mono (F.map D.sequence.inclusion)).1
    calc
      _ = m' ≫ (C.sequence.inclusion ≫ d) := by rw [Category.assoc, hm]
      _ = r ≫ d := by rw [← Category.assoc, hm']
      _ = (𝟙 (F.obj D.sequence.distribution.sheaf)) ≫ F.map D.sequence.inclusion := by
        rw [hrd, Category.id_comp]
  exact ⟨{ schemeIso := e
           overC := he
           distributionIso := ⟨m, m', hmm', hm'm⟩
           preserves := hm.symm }⟩

end LeBrunSalamon.Skeleton.AdjointContactTransportProof

namespace LeBrunSalamon.Skeleton

/-- Comparison obligation with the conventional adjoint-variety notation: any two such polarized models
for the SAME Lie algebra give contact-isomorphic varieties. No merely set-theoretic identification is used
in the project theorem. Root and orbit theory enters this lemma. -/
theorem adjointPresentations_contactIso {n : ℕ} {X Y : ContactFanoManifold n}
    (A : AdjointContactPresentation X) (B : AdjointContactPresentation Y)
    (e : A.algebra.carrier ≃ₗ⁅ℂ⁆ B.algebra.carrier) :
    Nonempty (ContactIso X.variety Y.variety X.contact Y.contact) := by
  obtain ⟨j, l, f, hj, hl, hf, hC⟩ := AdjointComparisonProof.adjointSchemeIso A B e
  exact AdjointContactTransportProof.contactIso_of_local_kernel_iff X.contact Y.contact f hC
    (AdjointContactTransportProof.local_kernel_iff A B e f hC
      (AdjointComparisonProof.polarizationComparison A B j l f hf)
      (AdjointComparisonProof.polarizationComparison_coordinate A B e j l hl f hf))

end LeBrunSalamon.Skeleton

end

#check LeBrunSalamon.Core.manuscriptCore_HamiltonianSpanning

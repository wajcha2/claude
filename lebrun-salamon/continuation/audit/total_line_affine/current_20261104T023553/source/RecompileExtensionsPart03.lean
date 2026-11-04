import LSHomFiberInjectivity
import RecompileExtensionsPart02

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


/-! Existing actual-bundle proofs are placed before the original
positive-node declarations so those declarations can use the proofs
without a cyclic module import. This relocation is source-only and
awaits the user's deferred final compilation. -/

/- BEGIN RELOCATED POSITIVE-NODE DEPENDENCY: RecompileTail -/
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

/- BEGIN UNCOMPILED continuation scalar_rebase.lean.txt -/
/-!
The field automorphism induced by a change of the actual complex-base map.

Uncompiled continuation. Integrate after Construction.complexConstants and
its section-module instances. All equations use the original structure maps.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction

namespace LeBrunSalamon.ScalarTransport

/-- Contravariant action of an actual base automorphism on global functions. -/
def complexBaseSectionIso (e : ComplexBase ≅ ComplexBase) :
    Γ(ComplexBase, ⊤) ≅ Γ(ComplexBase, ⊤) where
  hom := e.hom.appTop
  inv := e.inv.appTop
  hom_inv_id := by rw [← Scheme.Hom.comp_appTop, e.inv_hom_id]; rfl
  inv_hom_id := by rw [← Scheme.Hom.comp_appTop, e.hom_inv_id]; rfl

/-- The induced field automorphism, conjugating actual global functions by
the canonical Spec/global-section comparison. -/
def complexBaseCoefficientEquiv (e : ComplexBase ≅ ComplexBase) : ℂ ≃+* ℂ :=
  ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).symm ≪≫ complexBaseSectionIso e ≪≫
    Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv

theorem complexBaseCoefficientEquiv_apply (e : ComplexBase ≅ ComplexBase) (c : ℂ) :
    complexBaseCoefficientEquiv e c =
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
        (e.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c)) := rfl

theorem complexBaseCoefficientEquiv_spec (e : ComplexBase ≅ ComplexBase) (c : ℂ) :
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv (complexBaseCoefficientEquiv e c) =
      e.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c) := by
  rw [complexBaseCoefficientEquiv_apply, Iso.hom_inv_id_apply]

theorem complexConstants_comp_baseIso {X : Scheme} (s : X ⟶ ComplexBase)
    (e : ComplexBase ≅ ComplexBase) (c : ℂ) :
    complexConstants (s ≫ e.hom) c = complexConstants s (complexBaseCoefficientEquiv e c) := by
  rw [complexConstants_apply_top, complexConstants_apply_top,
    complexBaseCoefficientEquiv_spec, Scheme.Hom.comp_appTop] <;> rfl

/-- Base change affects constants on every open, not just global sections. -/
theorem complexConstant_comp_baseIso {X : Scheme} (s : X ⟶ ComplexBase)
    (e : ComplexBase ≅ ComplexBase) (U : X.Opens) (c : ℂ) :
    complexConstant (s ≫ e.hom) U c =
      complexConstant s U (complexBaseCoefficientEquiv e c) := by
  unfold complexConstant
  rw [complexBaseCoefficientEquiv_spec, Scheme.Hom.comp_appTop] <;> rfl

/-- The actual difference between the canonical and supplied zero-degree
identifications. This is a scheme automorphism, with no continuity assumption
on its induced field automorphism. -/
def projectiveBaseIso (P : ProjectiveLineOverC) : ComplexBase ≅ ComplexBase :=
  canonicalProjectiveLine.zeroDegreeIso.symm ≪≫ P.zeroDegreeIso

theorem projective_structureMap_factor (P : ProjectiveLineOverC) :
    canonicalProjectiveLine.structureMap ≫ (projectiveBaseIso P).hom = P.structureMap := by
  simp [ProjectiveLineOverC.structureMap, projectiveBaseIso, Category.assoc]

def projectiveCoefficientEquiv (P : ProjectiveLineOverC) : ℂ ≃+* ℂ :=
  complexBaseCoefficientEquiv (projectiveBaseIso P)

theorem projectiveConstants_rebase (P : ProjectiveLineOverC) (c : ℂ) :
    complexConstants P.structureMap c =
      complexConstants canonicalProjectiveLine.structureMap (projectiveCoefficientEquiv P c) := by
  rw [← projective_structureMap_factor P]
  exact complexConstants_comp_baseIso canonicalProjectiveLine.structureMap (projectiveBaseIso P) c

theorem projectiveConstant_rebase (P : ProjectiveLineOverC) (U : ProjectiveLine.Opens)
    (c : ℂ) :
    complexConstant P.structureMap U c =
      complexConstant canonicalProjectiveLine.structureMap U (projectiveCoefficientEquiv P c) := by
  rw [← projective_structureMap_factor P]
  exact complexConstant_comp_baseIso canonicalProjectiveLine.structureMap (projectiveBaseIso P) U c

/-- Underlying sections do not change when the complex-base map is changed;
their scalar action does. -/
def cSectionsRebase {X : Scheme} (s : X ⟶ ComplexBase)
    (e : ComplexBase ≅ ComplexBase) (E : OModule X) :
    CSections (s ≫ e.hom) E ≃+ CSections s E :=
  AddEquiv.refl (GlobalSections E)

theorem cSectionsRebase_smul {X : Scheme} (s : X ⟶ ComplexBase)
    (e : ComplexBase ≅ ComplexBase) (E : OModule X) (c : ℂ)
    (a : CSections (s ≫ e.hom) E) :
    cSectionsRebase s e E (c • a) =
      complexBaseCoefficientEquiv e c • cSectionsRebase s e E a := by
  let a' : GlobalSections E := a
  change complexConstants (s ≫ e.hom) c • a' =
    complexConstants s (complexBaseCoefficientEquiv e c) • a'
  rw [complexConstants_comp_baseIso]

def projectiveSectionsRebase (P : ProjectiveLineOverC) (E : OModule ProjectiveLine) :
    CSections P.structureMap E ≃+ CSections canonicalProjectiveLine.structureMap E :=
  AddEquiv.refl (GlobalSections E)

theorem projectiveSectionsRebase_smul (P : ProjectiveLineOverC)
    (E : OModule ProjectiveLine) (c : ℂ) (a : CSections P.structureMap E) :
    projectiveSectionsRebase P E (c • a) =
      projectiveCoefficientEquiv P c • projectiveSectionsRebase P E a := by
  let a' : GlobalSections E := a
  change complexConstants P.structureMap c • a' =
    complexConstants canonicalProjectiveLine.structureMap (projectiveCoefficientEquiv P c) • a'
  rw [projectiveConstants_rebase]

/-- A canonical-base linear coordinate calculation can be transported to any
original base identification by a specified inverse coefficient automorphism.
The canonical comparison remains an input until it is constructed geometrically. -/
def projectiveMatchingCoordinates (P : ProjectiveLineOverC)
    (E : OModule ProjectiveLine) (d : ℤ)
    (canonical : CSections canonicalProjectiveLine.structureMap E ≃ₗ[ℂ]
      P1Overlap.matchingSpace (K := ℂ) d) :
    CSections P.structureMap E ≃ₗ[ℂ] P1Overlap.matchingSpace (K := ℂ) d :=
  P1Overlap.untwistMatchingCoordinates (projectiveCoefficientEquiv P) d
    ((projectiveSectionsRebase P E).trans canonical.toAddEquiv) (by
      intro c a
      change canonical (projectiveSectionsRebase P E (c • a)) =
        projectiveCoefficientEquiv P c • canonical (projectiveSectionsRebase P E a)
      rw [projectiveSectionsRebase_smul, map_smul])

theorem projectiveMatchingCoordinates_finrank (P : ProjectiveLineOverC)
    (E : OModule ProjectiveLine) (d : ℤ)
    (canonical : CSections canonicalProjectiveLine.structureMap E ≃ₗ[ℂ]
      P1Overlap.matchingSpace (K := ℂ) d) :
    Module.finrank ℂ (CSections P.structureMap E) = (d + 1).toNat := by
  rw [(projectiveMatchingCoordinates P E d canonical).finrank_eq]
  exact P1Overlap.matchingSpace_finrank_all d

end LeBrunSalamon.ScalarTransport

end
/- END UNCOMPILED continuation scalar_rebase.lean.txt -/

/- BEGIN UNCOMPILED continuation actual_twist_scalars.lean.txt -/
/-!
Complex-linear section coordinates for every original O(d).

Uncompiled continuation. Insert after ScalarTransport. The canonical chart
constant formula is proved from the actual scheme maps; arbitrary choices of
the complex base identification are handled by the induced coefficient
automorphism. No linearity of raw polynomial coordinates is assumed.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.PhaseThirtyTwo LeBrunSalamon.P1Charts
open LeBrunSalamon.P1TwistFrames LeBrunSalamon.TwoChartSections
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction

namespace LeBrunSalamon.P1TwistSections

/-- The canonical complex scalar on global sections has constant polynomial
coordinate on every chart. The sheaf itself may be the twist constructed
using any P and p; only the scalar action in this statement is canonical. -/
theorem polynomialCoordinates_restrict_canonical_smul
    (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P) (d : ℤ) (i : Fin 2)
    (c : ℂ)
    (s : CSections canonicalProjectiveLine.structureMap (projectiveTwist P p d).sheaf) :
    polynomialCoordinates P p d i
        (restrictValue (projectiveTwist P p d).sheaf le_top (c • s)) =
      c • polynomialCoordinates P p d i
        (restrictValue (projectiveTwist P p d).sheaf le_top s) := by
  let s' : GlobalSections (projectiveTwist P p d).sheaf := s
  change polynomialCoordinates P p d i
    ((projectiveTwist P p d).sheaf.val.map (homOfLE le_top).op
      (complexConstants canonicalProjectiveLine.structureMap c • s')) =
    c • polynomialCoordinates P p d i
      ((projectiveTwist P p d).sheaf.val.map (homOfLE le_top).op s')
  rw [(projectiveTwist P p d).sheaf.val.map_smul, polynomialCoordinates_smul]
  change polynomialChartRingEquiv i
    (lineScheme.presheaf.map (homOfLE le_top).op
      (complexConstants canonicalProjectiveLine.structureMap c)) *
    polynomialCoordinates P p d i
      ((projectiveTwist P p d).sheaf.val.map (homOfLE le_top).op s') = _
  rw [complexConstants_apply_top, polynomialChartRingEquiv_canonical_constant,
    Polynomial.smul_eq_C_mul]

/-- Genuine global sections with the canonical complex scalar action are
linearly isomorphic to the computed matching space. -/
def canonicalMatchingLinearEquiv (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ) :
    CSections canonicalProjectiveLine.structureMap (projectiveTwist P p d).sheaf ≃ₗ[ℂ]
      P1Overlap.matchingSpace (K := ℂ) d where
  toAddEquiv := globalMatchingEquiv P p d
  map_smul' c s := by
    apply P1Overlap.matchingSpace_ext
    change (globalMatchingEquiv P p d (c • s)).val.1 =
      c • (globalMatchingEquiv P p d s).val.1
    rw [globalMatchingEquiv_fst, globalMatchingEquiv_fst]
    exact polynomialCoordinates_restrict_canonical_smul P p d 0 c s

/-- The linear comparison for the actual supplied complex-base map. Its
coordinate correction is the inverse of that base's coefficient automorphism. -/
def cMatchingEquiv (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ) :
    CSections P.structureMap (projectiveTwist P p d).sheaf ≃ₗ[ℂ]
      P1Overlap.matchingSpace (K := ℂ) d :=
  ScalarTransport.projectiveMatchingCoordinates P (projectiveTwist P p d).sheaf d
    (canonicalMatchingLinearEquiv P p d)

/-- The correction is visible in the first coordinate, so the linear
comparison is not mistaken for the raw coordinate map for arbitrary P. -/
theorem cMatchingEquiv_fst (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ)
    (s : CSections P.structureMap (projectiveTwist P p d).sheaf) :
    (cMatchingEquiv P p d s).val.1 =
      Polynomial.mapEquiv (ScalarTransport.projectiveCoefficientEquiv P).symm
        (polynomialCoordinates P p d 0
          (restrictValue (projectiveTwist P p d).sheaf le_top s)) := by
  change Polynomial.mapEquiv (ScalarTransport.projectiveCoefficientEquiv P).symm
    (globalMatchingEquiv P p d s).val.1 = _
  rw [globalMatchingEquiv_fst]

theorem cMatchingEquiv_snd (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ)
    (s : CSections P.structureMap (projectiveTwist P p d).sheaf) :
    (cMatchingEquiv P p d s).val.2 =
      Polynomial.mapEquiv (ScalarTransport.projectiveCoefficientEquiv P).symm
        (polynomialCoordinates P p d 1
          (restrictValue (projectiveTwist P p d).sheaf le_top s)) := by
  change Polynomial.mapEquiv (ScalarTransport.projectiveCoefficientEquiv P).symm
    (globalMatchingEquiv P p d s).val.2 = _
  rw [globalMatchingEquiv_snd]

instance twistCSections_finite (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ) :
    Module.Finite ℂ (CSections P.structureMap (projectiveTwist P p d).sheaf) :=
  Module.Finite.equiv (cMatchingEquiv P p d).symm

/-- The actual complex dimension of global sections for every integer twist. -/
theorem cSections_finrank (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ) :
    Module.finrank ℂ (CSections P.structureMap (projectiveTwist P p d).sheaf) =
      (d + 1).toNat := by
  rw [(cMatchingEquiv P p d).finrank_eq]
  exact P1Overlap.matchingSpace_finrank_all d

/-- A nonnegative twist is concretely the space of polynomials of degree
at most n, with the supplied complex scalar action respected. -/
def cSectionsDegreeLTEquiv (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (n : ℕ) :
    CSections P.structureMap (projectiveTwist P p (n : ℤ)).sheaf ≃ₗ[ℂ]
      Polynomial.degreeLT ℂ (n + 1) :=
  (cMatchingEquiv P p (n : ℤ)).trans (P1Overlap.matchingSpaceEquiv n)

/-- The transported monomial basis consists of actual global sections. -/
def cSectionsBasis (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (n : ℕ) :
    Module.Basis (Fin (n + 1)) ℂ
      (CSections P.structureMap (projectiveTwist P p (n : ℤ)).sheaf) :=
  (Polynomial.degreeLT.basis ℂ (n + 1)).map (cSectionsDegreeLTEquiv P p n).symm

/-- C-linear transport along a genuine sheaf isomorphism. -/
def cSectionsIso {X : Scheme} (sX : X ⟶ ComplexBase)
    {E F : OModule X} (e : E ≅ F) : CSections sX E ≃ₗ[ℂ] CSections sX F :=
  LinearEquiv.ofBijective (onCSections sX e.hom) (onCSections_bijective_of_iso sX e)

/-- The actual internal Hom has the expected section space in degree b-a.
This construction does not identify multiplication of Hom coordinates with
composition; that additional law is needed for scalar endomorphism arguments. -/
def internalHomCMatchingEquiv (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (a b : ℤ) :
    CSections P.structureMap
      (internalHomSheaf (projectiveTwist P p a).sheaf (projectiveTwist P p b).sheaf) ≃ₗ[ℂ]
        P1Overlap.matchingSpace (K := ℂ) (b - a) :=
  (cSectionsIso P.structureMap (Classical.choice (projectiveTwist_internalHom P p a b))).trans
    (cMatchingEquiv P p (b - a))

instance internalHomCSections_finite (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (a b : ℤ) :
    Module.Finite ℂ (CSections P.structureMap
      (internalHomSheaf (projectiveTwist P p a).sheaf (projectiveTwist P p b).sheaf)) :=
  Module.Finite.equiv (internalHomCMatchingEquiv P p a b).symm

theorem internalHomCSections_finrank (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (a b : ℤ) :
    Module.finrank ℂ (CSections P.structureMap
      (internalHomSheaf (projectiveTwist P p a).sheaf (projectiveTwist P p b).sheaf)) =
        (b - a + 1).toNat := by
  rw [(internalHomCMatchingEquiv P p a b).finrank_eq]
  exact P1Overlap.matchingSpace_finrank_all (b - a)

end LeBrunSalamon.P1TwistSections

end
/- END UNCOMPILED continuation actual_twist_scalars.lean.txt -/

/- BEGIN UNCOMPILED continuation point_evaluation.lean.txt -/
/-!
Actual twist fibers and polynomial point evaluation.

Uncompiled continuation. Insert after Construction's pullback-composition
and CSections APIs and after the normalized P1TwistSections comparison.
The fiber coordinates below are built from actual pulled-back sheaves and
unit comparisons; they are not assumed as compatibility data.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.PhaseThirtyTwo LeBrunSalamon.Construction

namespace LeBrunSalamon.FrameEvaluation

/-- Open restriction with the source unit normalized by the actual
structure-sheaf restriction isomorphism. -/
def restrictedSection {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f]
    {E : OModule Y} (s : AlgebraicSection E) : AlgebraicSection (E.restrict f) :=
  (Scheme.Modules.restrictUnitIso f).inv ≫ (Scheme.Modules.restrictFunctor f).map s

/-- The restriction unit comparison is adjoint to the actual structure map. -/
theorem restrictUnitIso_adjoint {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f] :
    (Scheme.Modules.restrictAdjunction f).homEquiv _ _
      (Scheme.Modules.restrictUnitIso f).hom = structurePushforwardMap f := by
  apply Scheme.Modules.hom_ext
  intro U
  ext r
  change (f.appIso (f ⁻¹ᵁ U)).hom
      (Y.presheaf.map (homOfLE (f.image_preimage_le U)).op r) = f.app U r
  have h : Y.presheaf.map (homOfLE (f.image_preimage_le U)).op ≫
      (f.appIso (f ⁻¹ᵁ U)).hom = f.app U := by
    rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE, Scheme.Hom.appLE_eq_app]
  exact congrArg (fun k => k r) h

/-- The actual restriction/pullback comparison respects the specified
structure-sheaf unit, by uniqueness of left adjoints. -/
theorem restrictionPullback_unit {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f] :
    (Scheme.Modules.restrictFunctorIsoPullback f).hom.app (structureModule Y) ≫
        unitPullbackMap f = (Scheme.Modules.restrictUnitIso f).hom := by
  apply ((Scheme.Modules.restrictAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, restrictUnitIso_adjoint]
  change (Scheme.Modules.restrictAdjunction f).homEquiv _ _
      ((Scheme.Modules.restrictFunctorIsoPullback f).hom.app (structureModule Y)) ≫
        (Scheme.Modules.pushforward f).map (unitPullbackMap f) = _
  rw [show (Scheme.Modules.restrictAdjunction f).homEquiv _ _
      ((Scheme.Modules.restrictFunctorIsoPullback f).hom.app (structureModule Y)) =
        (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (structureModule Y) from
    Adjunction.homEquiv_leftAdjointUniq_hom_app _ _ _]
  exact unitPullbackMap_adjoint f

theorem restrictionPullback_unit_inverse {X Y : Scheme} (f : X ⟶ Y)
    [IsOpenImmersion f] :
    (Scheme.Modules.restrictUnitIso f).inv ≫
        (Scheme.Modules.restrictFunctorIsoPullback f).hom.app (structureModule Y) =
      (unitPullbackIso f).inv := by
  apply (cancel_mono (unitPullbackIso f).hom).mp
  rw [Category.assoc]
  change (Scheme.Modules.restrictUnitIso f).inv ≫
      (Scheme.Modules.restrictFunctorIsoPullback f).hom.app (structureModule Y) ≫
      unitPullbackMap f = _
  rw [restrictionPullback_unit] <;> simp only [Iso.inv_hom_id]

/-- Open restriction and genuine pullback give the same normalized section
under their actual adjunction comparison. -/
theorem restrictedSection_to_pullSection {X Y : Scheme} (f : X ⟶ Y)
    [IsOpenImmersion f] {E : OModule Y} (s : AlgebraicSection E) :
    restrictedSection f s ≫ (Scheme.Modules.restrictFunctorIsoPullback f).hom.app E =
      pullSection f s := by
  unfold restrictedSection
  rw [Category.assoc, (Scheme.Modules.restrictFunctorIsoPullback f).hom.naturality,
    ← Category.assoc, restrictionPullback_unit_inverse] <;> rfl

/-- Evaluation of an actual restricted section is ordinary presheaf
restriction of the original section value. -/
theorem restrictedSection_value {X Y : Scheme} (f : X ⟶ Y)
    [IsOpenImmersion f] {E : OModule Y} (s : AlgebraicSection E) :
    sectionValue (restrictedSection f s) =
      E.presheaf.map (homOfLE (show f ''ᵁ ⊤ ≤ ⊤ from le_top)).op (sectionValue s) := by
  change Scheme.Modules.Hom.app s (f ''ᵁ ⊤) ((f.appIso ⊤).inv 1) = _
  rw [map_one]
  exact LeBrunSalamon.ScalarSections.section_app_one s (f ''ᵁ ⊤)

/-- Pullback of a specified global line frame, retaining the actual unit
isomorphism instead of identifying the two unit objects definitionally. -/
def pullbackFrame {X Y : Scheme} (f : X ⟶ Y) {E : OModule Y}
    (e : structureModule Y ≅ E) : structureModule X ≅ pullbackModule f E :=
  (unitPullbackIso f).symm ≪≫ (Scheme.Modules.pullback f).mapIso e

theorem unit_pullSection_value {X Y : Scheme} (f : X ⟶ Y)
    (s : AlgebraicSection (structureModule Y)) :
    Scheme.Modules.Hom.app (unitPullbackMap f) ⊤ (sectionValue (pullSection f s)) =
      f.appTop (sectionValue s) := by
  rw [pullSection_value]
  have h := unitPullbackMap_adjoint f
  change (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (structureModule Y) ≫
    (Scheme.Modules.pushforward f).map (unitPullbackMap f) = structurePushforwardMap f at h
  exact congrArg (fun k => Scheme.Modules.Hom.app k ⊤ (sectionValue s)) h

/-- Coordinates of a genuinely pulled-back section are pulled-back regular
functions. This is the generic evaluation law used by the point calculation. -/
theorem pullbackFrame_coordinates {X Y : Scheme} (f : X ⟶ Y)
    {E : OModule Y} (e : structureModule Y ≅ E) (s : AlgebraicSection E) :
    LocalFrames.Generic.coordinates (R := X.sheaf) (pullbackFrame f e) ⊤
        (sectionValue (pullSection f s)) =
      f.appTop (LocalFrames.Generic.coordinates (R := Y.sheaf) e ⊤ (sectionValue s)) := by
  calc
    _ = Scheme.Modules.Hom.app (unitPullbackMap f) ⊤
        (sectionValue (pullSection f (s ≫ e.inv))) := by
      rw [pullSection_naturality, sectionValue_comp] <;> rfl
    _ = f.appTop (sectionValue (s ≫ e.inv)) := unit_pullSection_value f _
    _ = _ := rfl

/-- Coordinate transport through a specified sheaf isomorphism cancels
that same isomorphism on the actual section. -/
theorem coordinates_iso_transport {X : Scheme} {E F : OModule X}
    (e : structureModule X ≅ E) (h : E ≅ F) (s : AlgebraicSection E) :
    LocalFrames.Generic.coordinates (R := X.sheaf) (e ≪≫ h) ⊤
        (sectionValue (s ≫ h.hom)) =
      LocalFrames.Generic.coordinates (R := X.sheaf) e ⊤ (sectionValue s) := by
  change sectionValue ((s ≫ h.hom) ≫ (e ≪≫ h).inv) = sectionValue (s ≫ e.inv)
  simp only [Iso.trans_inv, Category.assoc, Iso.hom_inv_id_assoc]

/-- The over-site frame regarded as a frame of the actual open pullback. -/
def openPullbackFrame {X : Scheme} {E : OModule X} {U : X.Opens}
    (e : LocalFrames.OverFrame E U) :
    structureModule U.toScheme ≅ pullbackModule U.ι E :=
  LocalFrames.toOpenFrame e ≪≫ (Scheme.Modules.restrictFunctorIsoPullback U.ι).app E

/-- Conversion from the over site to the open subscheme preserves the
coefficient of the restriction of a genuine global section. -/
theorem toOpenFrame_restricted_coordinates {X : Scheme} {E : OModule X}
    {U : X.Opens} (e : LocalFrames.OverFrame E U) (s : AlgebraicSection E) :
    LocalFrames.Generic.coordinates (R := U.toScheme.sheaf)
        (LocalFrames.toOpenFrame e) ⊤ (sectionValue (restrictedSection U.ι s)) =
      U.topIso.inv (LocalFrames.coordinates e
        (TwoChartSections.restrictValue E le_top (sectionValue s))) := by
  rw [restrictedSection_value]
  simp only [LocalFrames.Generic.coordinates_apply, LocalFrames.toOpenFrame,
    Iso.trans_inv, Iso.symm_inv, Iso.app_inv, Iso.app_hom, Functor.mapIso_inv,
    Scheme.Modules.Hom.comp_app, ModuleGluing.overFunctorEquiv_inv_app,
    ModuleGluing.overFunctorEquiv_hom_app, AddCommGrpCat.comp_apply,
    AddCommGrpCat.id_apply]
  change (U.ι.appIso ⊤).hom
    (e.inv.val.app (op (Over.mk (homOfLE (U.ι_image_le ⊤))))
      (E.presheaf.map (homOfLE le_top).op (sectionValue s))) = _
  rw [Scheme.Opens.ι_appIso]
  let i : U.ι ''ᵁ ⊤ ⟶ U := homOfLE (U.ι_image_le ⊤)
  let j : Over.mk i ⟶ Over.mk (𝟙 U) := Over.homMk i
  have h := PresheafOfModules.naturality_apply e.inv.val j.op
    (TwoChartSections.restrictValue E le_top (sectionValue s))
  change e.inv.val.app (op (Over.mk i))
      (E.presheaf.map i.op (E.presheaf.map (homOfLE le_top).op (sectionValue s))) =
    X.presheaf.map i.op (LocalFrames.coordinates e
      (TwoChartSections.restrictValue E le_top (sectionValue s))) at h
  rw [← ConcreteCategory.comp_apply, ← CategoryTheory.Functor.map_comp] at h
  change e.inv.val.app (op (Over.mk i))
      (E.presheaf.map
        (homOfLE (show U.ι ''ᵁ ⊤ ≤ ⊤ from le_top)).op (sectionValue s)) =
    X.presheaf.map i.op (LocalFrames.coordinates e
      (TwoChartSections.restrictValue E le_top (sectionValue s))) at h
  have htop : U.topIso.inv = X.presheaf.map i.op := by
    rw [Scheme.Opens.topIso_inv]
    exact congrArg
      (fun q : op U ⟶ op (U.ι ''ᵁ ⊤) => X.presheaf.map q)
      (Subsingleton.elim _ _)
  change e.inv.val.app (op (Over.mk i))
      (E.presheaf.map
        (homOfLE (show U.ι ''ᵁ ⊤ ≤ ⊤ from le_top)).op (sectionValue s)) =
    U.topIso.inv (LocalFrames.coordinates e
      (TwoChartSections.restrictValue E le_top (sectionValue s)))
  rw [htop]
  exact h

theorem openPullbackFrame_coordinates {X : Scheme} {E : OModule X}
    {U : X.Opens} (e : LocalFrames.OverFrame E U) (s : AlgebraicSection E) :
    LocalFrames.Generic.coordinates (R := U.toScheme.sheaf) (openPullbackFrame e) ⊤
        (sectionValue (pullSection U.ι s)) =
      U.topIso.inv (LocalFrames.coordinates e
        (TwoChartSections.restrictValue E le_top (sectionValue s))) := by
  rw [← restrictedSection_to_pullSection U.ι s]
  change LocalFrames.Generic.coordinates
      (LocalFrames.toOpenFrame e ≪≫ (Scheme.Modules.restrictFunctorIsoPullback U.ι).app E) ⊤
      (sectionValue (restrictedSection U.ι s ≫
        (Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app E)) = _
  exact (coordinates_iso_transport
    (LocalFrames.toOpenFrame e)
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app E)
    (restrictedSection U.ι s)).trans
    (toOpenFrame_restricted_coordinates e s)

/-- A frame of the actual pullback at a point factoring through its open.
The given factorization is used by the canonical composition comparison. -/
def fiberFrame {X : Scheme} {E : OModule X} (U : X.Opens)
    (q : ComplexBase ⟶ U.toScheme) (x : ComplexBase ⟶ X)
    (h : q ≫ U.ι = x) (e : LocalFrames.OverFrame E U) :
    structureModule ComplexBase ≅ pullbackModule x E :=
  pullbackFrame q (openPullbackFrame e) ≪≫ compositionPullback q U.ι x h E

theorem fiberFrame_coordinates_pullSection {X : Scheme} {E : OModule X}
    (U : X.Opens) (q : ComplexBase ⟶ U.toScheme) (x : ComplexBase ⟶ X)
    (h : q ≫ U.ι = x) (e : LocalFrames.OverFrame E U) (s : AlgebraicSection E) :
    LocalFrames.Generic.coordinates (R := ComplexBase.sheaf) (fiberFrame U q x h e) ⊤
        (sectionValue (pullSection x s)) =
      q.appTop (U.topIso.inv (LocalFrames.coordinates e
        (TwoChartSections.restrictValue E le_top (sectionValue s)))) := by
  rw [← compositionPullback_sections q U.ι x h s]
  change LocalFrames.Generic.coordinates
    (pullbackFrame q (openPullbackFrame e) ≪≫ compositionPullback q U.ι x h E) ⊤ _ = _
  rw [coordinates_iso_transport, pullbackFrame_coordinates, openPullbackFrame_coordinates]

/-- Coordinates of an actual framed module on Spec(C), with the frame
kept abstract while its scalar structure is checked. -/
def complexFrameCoordinates {E : OModule ComplexBase}
    (e : structureModule ComplexBase ≅ E) :
    CSections (𝟙 ComplexBase) E ≃+ ℂ :=
  (LocalFrames.Generic.coordinates (R := ComplexBase.sheaf) e ⊤).toAddEquiv.trans
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv.toAddEquiv

/-- Computation of the actual coefficient map before frame specialization. -/
theorem complexFrameCoordinates_apply {E : OModule ComplexBase}
    (e : structureModule ComplexBase ≅ E) (a : GlobalSections E) :
    complexFrameCoordinates e a =
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
        (LocalFrames.Generic.coordinates (R := ComplexBase.sheaf) e ⊤ a) := rfl

/-- The actual frame coefficient is complex-linear for the canonical
complex structure on sections of a module over Spec(C). -/
def complexFrameCoordinatesLinearEquiv {E : OModule ComplexBase}
    (e : structureModule ComplexBase ≅ E) :
    CSections (𝟙 ComplexBase) E ≃ₗ[ℂ] ℂ where
  toAddEquiv := complexFrameCoordinates e
  map_smul' a s := by
    let s' : GlobalSections E := s
    change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
      (LocalFrames.Generic.coordinates (R := ComplexBase.sheaf) e ⊤
        (complexConstants (𝟙 ComplexBase) a • s')) = _
    rw [(LocalFrames.Generic.coordinates (R := ComplexBase.sheaf) e ⊤).map_smul]
    let q : RingSections ComplexBase ⊤ :=
      LocalFrames.Generic.coordinates (R := ComplexBase.sheaf) e ⊤ s'
    change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
      (complexConstants (𝟙 ComplexBase) a * q) =
      a * (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom q
    rw [map_mul, complexConstants_apply_top]
    change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv a) * _ = _
    rw [Iso.inv_hom_id_apply]

/-- The complete frame/value comparison is checked with abstract geometric
data before specializing to a twist and a concrete polynomial chart. -/
theorem complexFiberFrameCoordinates_pullSection
    {X : Scheme} {E : OModule X} (U : X.Opens)
    (q : ComplexBase ⟶ U.toScheme) (x : ComplexBase ⟶ X)
    (h : q ≫ U.ι = x) (e : LocalFrames.OverFrame E U)
    {R : Type} [CommRing R]
    (φ : RingSections X U ≃+* R) (ev : R → ℂ)
    (hvalue : ∀ r : RingSections X U,
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
        (q.appTop (U.topIso.inv r)) = ev (φ r))
    (s : AlgebraicSection E) :
    complexFrameCoordinates (fiberFrame U q x h e)
        (sectionValue (pullSection x s)) =
      ev (((LocalFrames.coordinates e).toAddEquiv.trans φ.toAddEquiv)
        (TwoChartSections.restrictValue E le_top (sectionValue s))) := by
  exact (complexFrameCoordinates_apply
    (fiberFrame U q x h e) (sectionValue (pullSection x s))).trans
    ((congrArg
      (fun a : RingSections ComplexBase ⊤ =>
        (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom a)
      (fiberFrame_coordinates_pullSection U q x h e s)).trans
      (hvalue (LocalFrames.coordinates e
        (TwoChartSections.restrictValue E le_top (sectionValue s)))))

/-- Normalize the honest source f*O of a restricted morphism, then read its
actual global section value. This identifies the original restriction API
with the fiber-value API without changing its target Hom type. -/
def restrictedSectionValueEquiv {X Y : Scheme} (f : X ⟶ Y) (E : OModule Y) :
    (pullbackModule f (structureModule Y) ⟶ pullbackModule f E) ≃+
      GlobalSections (pullbackModule f E) :=
  ({ toFun := fun s => (unitPullbackIso f).inv ≫ s
     invFun := fun s => (unitPullbackIso f).hom ≫ s
     left_inv := by intro s; simp
     right_inv := by intro s; simp
     map_add' := by intro s t; simp only [Preadditive.comp_add] } :
    (pullbackModule f (structureModule Y) ⟶ pullbackModule f E) ≃+
      AlgebraicSection (pullbackModule f E)).trans
    (sectionAddEquiv (pullbackModule f E))

@[simp]
theorem restrictedSectionValueEquiv_apply {X Y : Scheme} (f : X ⟶ Y)
    (E : OModule Y) (s : AlgebraicSection E) :
    restrictedSectionValueEquiv f E (LeBrunSalamon.PhaseThree.restrictSection f s) =
      sectionValue (pullSection f s) := rfl

/-- Postcompose the restriction-value comparison through an arbitrary
coordinate equivalence before specializing the scheme, sheaf or coordinates. -/
theorem restrictedSectionValueEquiv_trans_apply {X Y : Scheme}
    (f : X ⟶ Y) (E : OModule Y) {V : Type*}
    (q : GlobalSections (pullbackModule f E) ≃ V)
    (s : AlgebraicSection E) :
    ((restrictedSectionValueEquiv f E).toEquiv.trans q)
        (LeBrunSalamon.PhaseThree.restrictSection f s) =
      q (sectionValue (pullSection f s)) := by
  exact congrArg q (restrictedSectionValueEquiv_apply f E s)

end LeBrunSalamon.FrameEvaluation

namespace LeBrunSalamon.P1TwistEvaluation

open LeBrunSalamon.P1Charts LeBrunSalamon.P1TwistFrames
open LeBrunSalamon.P1TwistSections LeBrunSalamon.FrameEvaluation
open LeBrunSalamon.Skeleton

/-- The actual point in the open subscheme corresponding to the scalar c
in polynomial chart i. -/
def pointInOpen (i : Fin 2) (c : ℂ) : ComplexBase ⟶ (chartOpen i).toScheme :=
  Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom c)) ≫ (polynomialChartIso i).inv

theorem pointInOpen_ι (i : Fin 2) (c : ℂ) :
    pointInOpen i c ≫ (chartOpen i).ι = pointMap i c := by
  simp only [pointMap_eq_polynomialChart, pointInOpen, polynomialChartInclusion,
    Category.assoc]

/-- The regular-function value at this genuine point is ordinary polynomial
evaluation in the already normalized chart ring. -/
theorem pointInOpen_ring_value (i : Fin 2) (c : ℂ)
    (r : RingSections lineScheme (chartOpen i)) :
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
        ((pointInOpen i c).appTop ((chartOpen i).topIso.inv r)) =
      (polynomialChartRingEquiv i r).eval c := by
  have hchart := polynomialChartRingEquiv_eq_appLE i
  change CommRingCat.ofHom (polynomialChartRingEquiv i).toRingHom =
    ((polynomialChartIso i).inv ≫ (chartOpen i).ι).appLE (chartOpen i) ⊤ _ ≫
      (Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℂ))).hom at hchart
  rw [isoChart_appLE] at hchart
  have heval := Scheme.ΓSpecIso_naturality
    (CommRingCat.ofHom (Polynomial.evalRingHom c))
  have he := congrArg (fun f => f ((polynomialChartIso i).inv.appTop
    ((chartOpen i).topIso.inv r))) heval
  have hc := congrArg (fun f => f r) hchart
  change (polynomialChartRingEquiv i r) =
    (Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℂ))).hom
      ((polynomialChartIso i).inv.appTop ((chartOpen i).topIso.inv r)) at hc
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
      ((Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom c))).appTop
        ((polynomialChartIso i).inv.appTop ((chartOpen i).topIso.inv r))) = _
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
      ((Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom c))).appTop
        ((polynomialChartIso i).inv.appTop ((chartOpen i).topIso.inv r))) =
    Polynomial.eval c
      ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℂ))).hom
        ((polynomialChartIso i).inv.appTop ((chartOpen i).topIso.inv r))) at he
  exact he.trans (congrArg (Polynomial.eval c) hc.symm)

/-- The chosen frame of the real pulled-back twist at a standard coordinate
point. It is constructed using the original twist and its actual chart frame. -/
def twistFiberFrame (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    (d : ℤ) (i : Fin 2) (c : ℂ) :
    structureModule ComplexBase ≅ pullbackModule (pointMap i c) (projectiveTwist P p d).sheaf :=
  fiberFrame (chartOpen i) (pointInOpen i c) (pointMap i c) (pointInOpen_ι i c)
    (twistOverFrame P p d i)

/-- Coordinates on the actual fiber, obtained from the actual pulled-back
frame and the canonical global functions of Spec(C). -/
def fiberCoordinates (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    (d : ℤ) (i : Fin 2) (c : ℂ) :
    Fiber (projectiveTwist P p d).sheaf (pointMap i c) ≃+ ℂ :=
  complexFrameCoordinates (twistFiberFrame P p d i c)

/-- The fiber always has the scalar structure of Spec(C) itself, so the
constructed fiber coordinates are C-linear, independently of P's base map. -/
def fiberCoordinatesLinearEquiv (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    (d : ℤ) (i : Fin 2) (c : ℂ) :
    Fiber (projectiveTwist P p d).sheaf (pointMap i c) ≃ₗ[ℂ] ℂ :=
  complexFrameCoordinatesLinearEquiv (twistFiberFrame P p d i c)

/-- Genuine section pullback to the point, expressed in the constructed
fiber frame, is evaluation of its actual chart polynomial. -/
theorem fiberCoordinates_pullSection (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ) (i : Fin 2) (c : ℂ)
    (s : AlgebraicSection (projectiveTwist P p d).sheaf) :
    fiberCoordinates P p d i c (sectionValue (pullSection (pointMap i c) s)) =
      (polynomialCoordinates P p d i
        (TwoChartSections.restrictValue (projectiveTwist P p d).sheaf
          le_top (sectionValue s))).eval c := by
  exact FrameEvaluation.complexFiberFrameCoordinates_pullSection
    (chartOpen i) (pointInOpen i c) (pointMap i c) (pointInOpen_ι i c)
    (twistOverFrame P p d i) (polynomialChartRingEquiv i)
    (Polynomial.eval c) (pointInOpen_ring_value i c) s

/-- The existing actual linear evaluation map for the canonical base has
the same polynomial value. The twist itself may use any P and any p. -/
theorem fiberCoordinates_evaluateSection (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ) (i : Fin 2) (c : ℂ)
    (s : CSections canonicalProjectiveLine.structureMap (projectiveTwist P p d).sheaf) :
    fiberCoordinates P p d i c
        (evaluateSection canonicalProjectiveLine.structureMap
          (projectiveTwist P p d).sheaf (pointMap i c) (pointMap_overC i c) s) =
      (polynomialCoordinates P p d i
        (TwoChartSections.restrictValue (projectiveTwist P p d).sheaf le_top s)).eval c := by
  change fiberCoordinates P p d i c
    (sectionValue (pullSection (pointMap i c) (sectionFromValue s))) = _
  rw [fiberCoordinates_pullSection, sectionFromValue_spec]

/-- At infinity the actual value is the highest allowed coefficient in
the first-chart polynomial, including lower-degree sections. -/
theorem fiberCoordinates_infinity (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (n : ℕ)
    (s : AlgebraicSection (projectiveTwist P p (n : ℤ)).sheaf) :
    fiberCoordinates P p (n : ℤ) 1 0 (sectionValue (pullSection (pointMap 1 0) s)) =
      (algebraicMatchingEquiv P p (n : ℤ) s).val.1.coeff n := by
  rw [fiberCoordinates_pullSection]
  exact P1Overlap.matching_evaluation_at_infinity
    (algebraicMatchingEquiv P p (n : ℤ) s).property

/-- Actual one-point evaluation at a finite coordinate point is surjective
exactly in nonnegative degree. The scalar action on the source is canonical. -/
theorem finiteEvaluation_surjective_iff (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ) (c : ℂ) :
    Function.Surjective
      (evaluateSection canonicalProjectiveLine.structureMap (projectiveTwist P p d).sheaf
        (pointMap 0 c) (pointMap_overC 0 c)) ↔ 0 ≤ d := by
  rw [← P1Overlap.finitePointEvaluation_surjective_iff (K := ℂ) d c]
  constructor
  · intro hs a
    obtain ⟨s, hs⟩ := hs ((fiberCoordinates P p d 0 c).symm a)
    refine ⟨globalMatchingEquiv P p d s, ?_⟩
    have h := congrArg (fiberCoordinates P p d 0 c) hs
    rw [fiberCoordinates_evaluateSection, AddEquiv.apply_symm_apply] at h
    change ((globalMatchingEquiv P p d s).val.1).eval c = a
    rw [globalMatchingEquiv_fst]
    exact h
  · intro hs a
    obtain ⟨pq, hpq⟩ := hs (fiberCoordinates P p d 0 c a)
    refine ⟨(globalMatchingEquiv P p d).symm pq, ?_⟩
    apply (fiberCoordinates P p d 0 c).injective
    rw [fiberCoordinates_evaluateSection]
    have he := congrArg (fun q : P1Overlap.matchingSpace (K := ℂ) d => q.val.1)
      ((globalMatchingEquiv P p d).apply_symm_apply pq)
    rw [globalMatchingEquiv_fst] at he
    rw [he]
    exact hpq

/-- A top-degree monomial realizes an arbitrary value in the genuine
fiber at infinity, including degree zero. -/
theorem infinityEvaluation_surjective (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (n : ℕ) :
    Function.Surjective
      (evaluateSection canonicalProjectiveLine.structureMap
        (projectiveTwist P p (n : ℤ)).sheaf (pointMap 1 0) (pointMap_overC 1 0)) := by
  intro a
  let z : ℂ := fiberCoordinates P p (n : ℤ) 1 0 a
  let q : Polynomial ℂ := Polynomial.monomial n z
  have hq : q.natDegree ≤ n := Polynomial.natDegree_monomial_le z
  let pq : P1Overlap.matchingSpace (K := ℂ) (n : ℤ) :=
    ⟨(q, q.reflect n), P1Overlap.matching_reflect n q hq⟩
  refine ⟨(globalMatchingEquiv P p (n : ℤ)).symm pq, ?_⟩
  apply (fiberCoordinates P p (n : ℤ) 1 0).injective
  rw [fiberCoordinates_evaluateSection]
  have he := congrArg
    (fun t : P1Overlap.matchingSpace (K := ℂ) (n : ℤ) => t.val.2)
    ((globalMatchingEquiv P p (n : ℤ)).apply_symm_apply pq)
  rw [globalMatchingEquiv_snd] at he
  rw [he]
  change (q.reflect n).eval 0 = z
  rw [P1Overlap.matching_evaluation_at_infinity (P1Overlap.matching_reflect n q hq)]
  exact Polynomial.coeff_monomial_same n z

theorem infinityEvaluation_surjective_iff (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ) :
    Function.Surjective
      (evaluateSection canonicalProjectiveLine.structureMap (projectiveTwist P p d).sheaf
        (pointMap 1 0) (pointMap_overC 1 0)) ↔ 0 ≤ d := by
  constructor
  · intro hs
    by_contra hd
    obtain ⟨s, hs⟩ := hs ((fiberCoordinates P p d 1 0).symm 1)
    have h := congrArg (fiberCoordinates P p d 1 0) hs
    rw [fiberCoordinates_evaluateSection, AddEquiv.apply_symm_apply] at h
    have hz := (P1Overlap.matching_negative (lt_of_not_ge hd)
      (globalMatchingEquiv P p d s).property).2
    rw [globalMatchingEquiv_snd] at hz
    rw [hz, Polynomial.eval_zero] at h
    exact zero_ne_one h
  · intro hd
    rw [← Int.toNat_of_nonneg hd]
    exact infinityEvaluation_surjective P p d.toNat

/-- Every actual complex point of the canonical projective line satisfies
the one-point evaluation criterion. This is a fiber statement; the original
sheaf-epimorphism definition of global generation is a separate target. -/
theorem evaluation_surjective_iff (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ) (x : ComplexBase ⟶ ProjectiveLine)
    (hx : x ≫ canonicalProjectiveLine.structureMap = 𝟙 ComplexBase) :
    Function.Surjective
      (evaluateSection canonicalProjectiveLine.structureMap (projectiveTwist P p d).sheaf
        x hx) ↔ 0 ≤ d := by
  rcases canonicalPoint_finite_or_infinity x hx with ⟨c, rfl⟩ | rfl
  · exact finiteEvaluation_surjective_iff P p d c
  · exact infinityEvaluation_surjective_iff P p d

/-- The original section-restriction map, with its actual pulled-back
unit as source, has the same criterion at every canonical complex point. -/
theorem restrictSection_surjective_iff (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ) (x : ComplexBase ⟶ ProjectiveLine)
    (hx : x ≫ canonicalProjectiveLine.structureMap = 𝟙 ComplexBase) :
    Function.Surjective
      (LeBrunSalamon.PhaseThree.restrictSection x
        (E := (projectiveTwist P p d).sheaf)) ↔ 0 ≤ d := by
  rw [← evaluation_surjective_iff P p d x hx]
  constructor
  · intro hs a
    obtain ⟨s, hs⟩ := hs
      ((restrictedSectionValueEquiv x (projectiveTwist P p d).sheaf).symm a)
    refine ⟨sectionValue s, ?_⟩
    have h := congrArg (restrictedSectionValueEquiv x (projectiveTwist P p d).sheaf) hs
    rw [restrictedSectionValueEquiv_apply, AddEquiv.apply_symm_apply] at h
    change sectionValue (pullSection x (sectionFromValue (sectionValue s))) = a
    rw [sectionFromValue_sectionValue]
    exact h
  · intro hs a
    obtain ⟨s, hs⟩ := hs (restrictedSectionValueEquiv x (projectiveTwist P p d).sheaf a)
    refine ⟨sectionFromValue s, ?_⟩
    apply (restrictedSectionValueEquiv x (projectiveTwist P p d).sheaf).injective
    rw [restrictedSectionValueEquiv_apply]
    exact hs

/-- The pair of the existing actual fiber evaluation maps at zero and
infinity. The codomain consists of the two genuine pulled-back fibers. -/
def canonicalMarkedEvaluation (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ) :
    CSections canonicalProjectiveLine.structureMap (projectiveTwist P p d).sheaf →ₗ[ℂ]
      (Fiber (projectiveTwist P p d).sheaf (pointMap 0 0) ×
        Fiber (projectiveTwist P p d).sheaf (pointMap 1 0)) :=
  (evaluateSection canonicalProjectiveLine.structureMap (projectiveTwist P p d).sheaf
      (pointMap 0 0) (pointMap_overC 0 0)).prod
    (evaluateSection canonicalProjectiveLine.structureMap (projectiveTwist P p d).sheaf
      (pointMap 1 0) (pointMap_overC 1 0))

def markedFiberCoordinates (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ) :
    (Fiber (projectiveTwist P p d).sheaf (pointMap 0 0) ×
      Fiber (projectiveTwist P p d).sheaf (pointMap 1 0)) ≃+ (ℂ × ℂ) :=
  (fiberCoordinates P p d 0 0).prodCongr (fiberCoordinates P p d 1 0)

theorem markedFiberCoordinates_evaluate (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ)
    (s : CSections canonicalProjectiveLine.structureMap (projectiveTwist P p d).sheaf) :
    markedFiberCoordinates P p d (canonicalMarkedEvaluation P p d s) =
      P1Overlap.markedEvaluation d (globalMatchingEquiv P p d s) := by
  apply Prod.ext
  · change fiberCoordinates P p d 0 0
      (evaluateSection canonicalProjectiveLine.structureMap (projectiveTwist P p d).sheaf
        (pointMap 0 0) (pointMap_overC 0 0) s) = _
    rw [fiberCoordinates_evaluateSection]
    change _ = ((globalMatchingEquiv P p d s).val.1).eval 0
    rw [globalMatchingEquiv_fst]
  · change fiberCoordinates P p d 1 0
      (evaluateSection canonicalProjectiveLine.structureMap (projectiveTwist P p d).sheaf
        (pointMap 1 0) (pointMap_overC 1 0) s) = _
    rw [fiberCoordinates_evaluateSection]
    change _ = ((globalMatchingEquiv P p d s).val.2).eval 0
    rw [globalMatchingEquiv_snd]

/-- Actual simultaneous evaluation at the two standard marked points is
surjective exactly for positive twist degree. -/
theorem canonicalMarkedEvaluation_surjective_iff (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ) :
    Function.Surjective (canonicalMarkedEvaluation P p d) ↔ 1 ≤ d := by
  rw [← P1Overlap.markedEvaluation_surjective_iff (K := ℂ) d]
  constructor
  · intro hs a
    obtain ⟨s, hs⟩ := hs ((markedFiberCoordinates P p d).symm a)
    refine ⟨globalMatchingEquiv P p d s, ?_⟩
    have h := congrArg (markedFiberCoordinates P p d) hs
    rw [markedFiberCoordinates_evaluate, AddEquiv.apply_symm_apply] at h
    exact h
  · intro hs a
    obtain ⟨pq, hpq⟩ := hs (markedFiberCoordinates P p d a)
    refine ⟨(globalMatchingEquiv P p d).symm pq, ?_⟩
    apply (markedFiberCoordinates P p d).injective
    rw [markedFiberCoordinates_evaluate, AddEquiv.apply_symm_apply]
    exact hpq

/-- The two honest restricted Hom spaces in the original API are the two
genuine fiber-value spaces after the specified unit normalization. -/
def markedRestrictionValues (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ) :
    ((pullbackModule (pointMap 0 0) (structureModule ProjectiveLine) ⟶
        pullbackModule (pointMap 0 0) (projectiveTwist P p d).sheaf) ×
      (pullbackModule (pointMap 1 0) (structureModule ProjectiveLine) ⟶
        pullbackModule (pointMap 1 0) (projectiveTwist P p d).sheaf)) ≃+
      (Fiber (projectiveTwist P p d).sheaf (pointMap 0 0) ×
        Fiber (projectiveTwist P p d).sheaf (pointMap 1 0)) :=
  (restrictedSectionValueEquiv (pointMap 0 0) (projectiveTwist P p d).sheaf).prodCongr
    (restrictedSectionValueEquiv (pointMap 1 0) (projectiveTwist P p d).sheaf)

theorem markedRestrictionValues_apply (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ)
    (s : AlgebraicSection (projectiveTwist P p d).sheaf) :
    markedRestrictionValues P p d
      (twoPointBundleEvaluation canonicalProjectiveLine (markedPoint 0 0) (markedPoint 1 0)
        (projectiveTwist P p d).sheaf s) =
      canonicalMarkedEvaluation P p d (sectionValue s) := by
  change (sectionValue (pullSection (pointMap 0 0) s),
    sectionValue (pullSection (pointMap 1 0) s)) =
      (sectionValue (pullSection (pointMap 0 0) (sectionFromValue (sectionValue s))),
        sectionValue (pullSection (pointMap 1 0) (sectionFromValue (sectionValue s))))
  rw [sectionFromValue_sectionValue]

/-- The original twoPointBundleEvaluation map, with its original pullback
Hom codomain, has the expected criterion at the standard marked points. -/
theorem marked_twoPointBundleEvaluation_surjective_iff (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ) :
    Function.Surjective
      (twoPointBundleEvaluation canonicalProjectiveLine (markedPoint 0 0) (markedPoint 1 0)
        (projectiveTwist P p d).sheaf) ↔ 1 ≤ d := by
  rw [← canonicalMarkedEvaluation_surjective_iff P p d]
  constructor
  · intro hs a
    obtain ⟨s, hs⟩ := hs ((markedRestrictionValues P p d).symm a)
    refine ⟨sectionValue s, ?_⟩
    have h := congrArg (markedRestrictionValues P p d) hs
    rw [markedRestrictionValues_apply, AddEquiv.apply_symm_apply] at h
    exact h
  · intro hs a
    obtain ⟨s, hs⟩ := hs (markedRestrictionValues P p d a)
    refine ⟨sectionFromValue s, ?_⟩
    apply (markedRestrictionValues P p d).injective
    rw [markedRestrictionValues_apply, sectionFromValue_spec]
    exact hs

end LeBrunSalamon.P1TwistEvaluation

end
/- END UNCOMPILED continuation point_evaluation.lean.txt -/

/- BEGIN UNCOMPILED continuation endomorphism_scalars.lean.txt -/
/-!
The actual endomorphism ring and the supplied complex scalar structure.

Uncompiled continuation. Insert after ScalarTransport and the actual twist
scalar-section comparison. CategoryTheory.End is the pinned mathlib structure
with an asHom field; its multiplication is reverse categorical composition.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.PhaseThirtyTwo LeBrunSalamon.P1Charts
open LeBrunSalamon.Construction LeBrunSalamon.Skeleton

namespace LeBrunSalamon.P1Endomorphisms

/-- The actual endomorphism ring of an original twist is C. The coefficient
respects composition because it was computed from the original sheaf maps. -/
def canonicalEndRingEquiv (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    (a : ℤ) : CategoryTheory.End (projectiveTwist P p a).sheaf ≃+* ℂ where
  toFun f := endomorphismScalar P p a f.asHom
  invFun c := .of (complexScalarEnd (projectiveTwist P p a).sheaf c)
  left_inv f := by
    apply CategoryTheory.End.ext
    exact (endomorphism_eq_scalar P p a f.asHom).symm
  right_inv c := endomorphismScalar_complexScalarEnd P p a c
  map_add' f g := endomorphismScalar_add P p a f.asHom g.asHom
  map_mul' f g := by
    change endomorphismScalar P p a (g.asHom ≫ f.asHom) =
      endomorphismScalar P p a f.asHom * endomorphismScalar P p a g.asHom
    rw [endomorphismScalar_comp, mul_comm]

/-- Multiplication by a constant for the actual supplied base map, as an
endomorphism of any actual projective-line module sheaf. -/
def suppliedScalarEnd (P : ProjectiveLineOverC) (E : OModule ProjectiveLine)
    (c : ℂ) : E ⟶ E :=
  GlobalScalars.scalarEnd E (complexConstants P.structureMap c)

/-- Changing the base identification changes the canonical coefficient by
the already constructed automorphism of the complex field. -/
theorem suppliedScalarEnd_eq_canonical (P : ProjectiveLineOverC)
    (E : OModule ProjectiveLine) (c : ℂ) :
    suppliedScalarEnd P E c =
      complexScalarEnd E (ScalarTransport.projectiveCoefficientEquiv P c) := by
  unfold suppliedScalarEnd complexScalarEnd
  congr 1
  rw [ScalarTransport.projectiveConstants_rebase, complexConstants_apply_top] <;> rfl

/-- The endomorphism-ring coordinate for the supplied complex scalar action.
The inverse automorphism corrects the raw canonical scalar. -/
def suppliedEndRingEquiv (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    (a : ℤ) : CategoryTheory.End (projectiveTwist P p a).sheaf ≃+* ℂ :=
  (canonicalEndRingEquiv P p a).trans (ScalarTransport.projectiveCoefficientEquiv P).symm

theorem suppliedEndRingEquiv_apply (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (a : ℤ)
    (f : CategoryTheory.End (projectiveTwist P p a).sheaf) :
    suppliedEndRingEquiv P p a f =
      (ScalarTransport.projectiveCoefficientEquiv P).symm
        (endomorphismScalar P p a f.asHom) := rfl

@[simp]
theorem suppliedEndRingEquiv_scalar (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (a : ℤ) (c : ℂ) :
    suppliedEndRingEquiv P p a
        (.of (suppliedScalarEnd P (projectiveTwist P p a).sheaf c)) = c := by
  rw [suppliedEndRingEquiv_apply, suppliedScalarEnd_eq_canonical]
  change (ScalarTransport.projectiveCoefficientEquiv P).symm
    (endomorphismScalar P p a
      (complexScalarEnd (projectiveTwist P p a).sheaf
        (ScalarTransport.projectiveCoefficientEquiv P c))) = c
  rw [endomorphismScalar_complexScalarEnd, RingEquiv.symm_apply_apply]

/-- Equality of actual morphisms, with the scalar measured using P's own
structure map. This is stronger than an equality of their dimensions. -/
theorem endomorphism_eq_supplied_scalar (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (a : ℤ)
    (f : (projectiveTwist P p a).sheaf ⟶ (projectiveTwist P p a).sheaf) :
    f = suppliedScalarEnd P (projectiveTwist P p a).sheaf
      (suppliedEndRingEquiv P p a (.of f)) := by
  rw [suppliedScalarEnd_eq_canonical]
  change f = complexScalarEnd (projectiveTwist P p a).sheaf
    (ScalarTransport.projectiveCoefficientEquiv P
      ((ScalarTransport.projectiveCoefficientEquiv P).symm
        (endomorphismScalar P p a f)))
  rw [RingEquiv.apply_symm_apply]
  exact endomorphism_eq_scalar P p a f

/-- The scalar endomorphism acts on genuine C-sections by precisely their
defined complex module action. -/
theorem suppliedScalarEnd_onCSections (P : ProjectiveLineOverC)
    (E : OModule ProjectiveLine) (c : ℂ) (s : CSections P.structureMap E) :
    onCSections P.structureMap (suppliedScalarEnd P E c) s = c • s := by
  let s' : GlobalSections E := s
  change Scheme.Modules.Hom.app
      (GlobalScalars.scalarEnd E (complexConstants P.structureMap c)) ⊤ s' =
    complexConstants P.structureMap c • s'
  rw [GlobalScalars.scalarEnd_app]
  change (ProjectiveLine.presheaf.map (𝟙 _)) (complexConstants P.structureMap c) • s' = _
  rw [CategoryTheory.Functor.map_id] <;> rfl

/-- Every actual twist endomorphism acts on all genuine complex sections
by its supplied-base scalar, including the zero-dimensional section cases. -/
theorem onCSections_eq_scalar (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (a : ℤ)
    (f : (projectiveTwist P p a).sheaf ⟶ (projectiveTwist P p a).sheaf)
    (s : CSections P.structureMap (projectiveTwist P p a).sheaf) :
    onCSections P.structureMap f s = suppliedEndRingEquiv P p a (.of f) • s := by
  conv_lhs => rw [endomorphism_eq_supplied_scalar P p a f]
  exact suppliedScalarEnd_onCSections P (projectiveTwist P p a).sheaf _ s

end LeBrunSalamon.P1Endomorphisms

end
/- END UNCOMPILED continuation endomorphism_scalars.lean.txt -/

/- BEGIN UNCOMPILED continuation point_base_transport.lean.txt -/
/-!
Actual point restriction under a change of the complex base, and arbitrary
distinct-pair interpolation for the original twist sheaves.

Uncompiled continuation of v26. Insert after P1TwistEvaluation and the
Construction pullback-composition APIs. All restriction targets retain the
honest pulled-back unit. No complex-linearity of a field automorphism is
assumed; the arbitrary-base transport is an equivalence of actual Hom sets.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.PhaseThirtyTwo LeBrunSalamon.Construction
open LeBrunSalamon.Skeleton LeBrunSalamon.P1Charts

namespace LeBrunSalamon.PointBaseTransport

/-- Pullback by an actual scheme isomorphism is an equivalence, using the
specified pullback composition and identity comparisons. -/
def pullbackEquivalence {X Y : Scheme} (e : X ≅ Y) : Y.Modules ≌ X.Modules :=
  CategoryTheory.Equivalence.mk (Scheme.Modules.pullback e.hom)
    (Scheme.Modules.pullback e.inv)
    ((Scheme.Modules.pullbackComp e.inv e.hom ≪≫
      Scheme.Modules.pullbackCongr e.inv_hom_id ≪≫ Scheme.Modules.pullbackId Y).symm)
    (Scheme.Modules.pullbackComp e.hom e.inv ≪≫
      Scheme.Modules.pullbackCongr e.hom_inv_id ≪≫ Scheme.Modules.pullbackId X)

/-- Reparametrizing the source of a point gives an equivalence between the
original pullback Hom spaces. Its two composition comparisons are explicit. -/
def restrictedHomPrecomposeEquiv {T Y X : Scheme} (e : T ≅ Y) (x : Y ⟶ X)
    (A E : OModule X) :
    (pullbackModule x A ⟶ pullbackModule x E) ≃
      (pullbackModule (e.hom ≫ x) A ⟶ pullbackModule (e.hom ≫ x) E) :=
  (pullbackEquivalence e).fullyFaithfulFunctor.homEquiv.trans
    (Iso.homCongr ((Scheme.Modules.pullbackComp e.hom x).app A)
      ((Scheme.Modules.pullbackComp e.hom x).app E))

theorem restrictedHomPrecomposeEquiv_apply {T Y X : Scheme} (e : T ≅ Y)
    (x : Y ⟶ X) (A E : OModule X)
    (h : pullbackModule x A ⟶ pullbackModule x E) :
    restrictedHomPrecomposeEquiv e x A E h =
      (Scheme.Modules.pullbackComp e.hom x).inv.app A ≫
        (Scheme.Modules.pullback e.hom).map h ≫
          (Scheme.Modules.pullbackComp e.hom x).hom.app E := rfl

/-- The above equivalence carries the actual restricted global morphism
to its restriction at the reparametrized point. -/
theorem restrictedHomPrecomposeEquiv_map {T Y X : Scheme} (e : T ≅ Y)
    (x : Y ⟶ X) {A E : OModule X} (s : A ⟶ E) :
    restrictedHomPrecomposeEquiv e x A E ((Scheme.Modules.pullback x).map s) =
      (Scheme.Modules.pullback (e.hom ≫ x)).map s := by
  rw [restrictedHomPrecomposeEquiv_apply]
  have h := (Scheme.Modules.pullbackComp e.hom x).hom.naturality s
  change (Scheme.Modules.pullback e.hom).map ((Scheme.Modules.pullback x).map s) ≫
      (Scheme.Modules.pullbackComp e.hom x).hom.app E =
    (Scheme.Modules.pullbackComp e.hom x).hom.app A ≫
      (Scheme.Modules.pullback (e.hom ≫ x)).map s at h
  rw [h, Iso.inv_hom_id_app_assoc]

theorem restrictedHomPrecomposeEquiv_restrictSection {T Y X : Scheme}
    (e : T ≅ Y) (x : Y ⟶ X) {E : OModule X} (s : AlgebraicSection E) :
    restrictedHomPrecomposeEquiv e x (structureModule X) E
      (LeBrunSalamon.PhaseThree.restrictSection x s) =
      LeBrunSalamon.PhaseThree.restrictSection (e.hom ≫ x) s :=
  restrictedHomPrecomposeEquiv_map e x s

/-- Transport a specified actual fiber frame through a source
automorphism, retaining both the unit and composition comparisons. -/
def precomposeFiberFrame {X : Scheme} (e : ComplexBase ≅ ComplexBase)
    (x : ComplexBase ⟶ X) (E : OModule X)
    (f : structureModule ComplexBase ≅ pullbackModule x E) :
    structureModule ComplexBase ≅ pullbackModule (e.hom ≫ x) E :=
  FrameEvaluation.pullbackFrame e.hom f ≪≫ (Scheme.Modules.pullbackComp e.hom x).app E

/-- The exact semilinear evaluation law under a genuine base
automorphism. The coefficient automorphism is the one induced by its
actual map on global functions, rather than an assumed scalar action. -/
theorem precomposeFiberFrame_evaluation {X : Scheme} (e : ComplexBase ≅ ComplexBase)
    (x : ComplexBase ⟶ X) (E : OModule X)
    (f : structureModule ComplexBase ≅ pullbackModule x E) (s : AlgebraicSection E) :
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
        (LocalFrames.Generic.coordinates (R := ComplexBase.sheaf) (precomposeFiberFrame e x E f) ⊤
          (sectionValue (pullSection (e.hom ≫ x) s))) =
      ScalarTransport.complexBaseCoefficientEquiv e
        ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
          (LocalFrames.Generic.coordinates (R := ComplexBase.sheaf) f ⊤
            (sectionValue (pullSection x s)))) := by
  rw [← pullSection_comp e.hom x s]
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
    (LocalFrames.Generic.coordinates (R := ComplexBase.sheaf)
      (FrameEvaluation.pullbackFrame e.hom f ≪≫ (Scheme.Modules.pullbackComp e.hom x).app E)
      ⊤ (sectionValue (pullSection e.hom (pullSection x s) ≫
        (Scheme.Modules.pullbackComp e.hom x).hom.app E))) = _
  calc
    _ = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
        (e.hom.appTop
          (LocalFrames.Generic.coordinates (R := ComplexBase.sheaf) f ⊤
            (sectionValue (pullSection x s)))) := by
      exact congrArg
        (fun a : RingSections ComplexBase ⊤ =>
          (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom a)
        ((FrameEvaluation.coordinates_iso_transport
          (FrameEvaluation.pullbackFrame e.hom f)
          ((Scheme.Modules.pullbackComp e.hom x).app E)
          (pullSection e.hom (pullSection x s))).trans
          (FrameEvaluation.pullbackFrame_coordinates e.hom f (pullSection x s)))
    _ = _ := by
      rw [ScalarTransport.complexBaseCoefficientEquiv_apply, Iso.hom_inv_id_apply]

/-- Specialization to the existing projective-base automorphism: rebasing
a marked point to the canonical base changes its actual frame value by
the already constructed projective coefficient automorphism. -/
theorem canonicalRebase_evaluation (P : ProjectiveLineOverC)
    (x : ProjectiveLinePoint P) (E : OModule ProjectiveLine)
    (f : structureModule ComplexBase ≅ pullbackModule x.map E) (s : AlgebraicSection E) :
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
        (LocalFrames.Generic.coordinates (R := ComplexBase.sheaf)
          (precomposeFiberFrame (ScalarTransport.projectiveBaseIso P) x.map E f) ⊤
          (sectionValue (pullSection (ProjectiveLinePoint.rebase canonicalProjectiveLine x).map s))) =
      ScalarTransport.projectiveCoefficientEquiv P
        ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
          (LocalFrames.Generic.coordinates (R := ComplexBase.sheaf) f ⊤
            (sectionValue (pullSection x.map s)))) :=
  precomposeFiberFrame_evaluation (ScalarTransport.projectiveBaseIso P) x.map E f s

/-- Surjectivity transports through a commuting square of genuine
equivalences. This helper has no geometric assumptions. -/
theorem surjective_iff_of_coordinates {A B C D : Type*}
    (f : A → B) (g : C → D) (a : A ≃ C) (b : B ≃ D)
    (h : ∀ s, b (f s) = g (a s)) :
    Function.Surjective f ↔ Function.Surjective g := by
  calc
    Function.Surjective f ↔ Function.Surjective (b ∘ f) :=
      (Equiv.comp_surjective f b).symm
    _ ↔ Function.Surjective (g ∘ a) := by rw [show b ∘ f = g ∘ a from funext h]
    _ ↔ Function.Surjective g := Equiv.surjective_comp a g

/-- The original point-restriction pair with the point maps exposed. For
marked points this is definitionally twoPointBundleEvaluation. -/
def pointPairRestriction {X : Scheme} (E : OModule X)
    (x y : ComplexBase ⟶ X) :=
  fun s : AlgebraicSection E =>
    (LeBrunSalamon.PhaseThree.restrictSection x s,
      LeBrunSalamon.PhaseThree.restrictSection y s)

/-- Changing the supplied degree-zero identification acts by the actual
base automorphism on the original restricted Hom space. -/
def rebaseRestrictionEquiv {P : ProjectiveLineOverC} (Q : ProjectiveLineOverC)
    (x : ProjectiveLinePoint P) (E : OModule ProjectiveLine) :
    (pullbackModule x.map (structureModule ProjectiveLine) ⟶ pullbackModule x.map E) ≃
      (pullbackModule (ProjectiveLinePoint.rebase Q x).map (structureModule ProjectiveLine) ⟶
        pullbackModule (ProjectiveLinePoint.rebase Q x).map E) :=
  restrictedHomPrecomposeEquiv (Q.zeroDegreeIso.symm ≪≫ P.zeroDegreeIso)
    x.map (structureModule ProjectiveLine) E

theorem rebaseRestrictionEquiv_apply {P : ProjectiveLineOverC}
    (Q : ProjectiveLineOverC) (x : ProjectiveLinePoint P) (E : OModule ProjectiveLine)
    (s : AlgebraicSection E) :
    rebaseRestrictionEquiv Q x E (LeBrunSalamon.PhaseThree.restrictSection x.map s) =
      LeBrunSalamon.PhaseThree.restrictSection (ProjectiveLinePoint.rebase Q x).map s :=
  restrictedHomPrecomposeEquiv_restrictSection _ _ s

theorem restrictSection_rebase_surjective_iff {P : ProjectiveLineOverC}
    (Q : ProjectiveLineOverC) (x : ProjectiveLinePoint P) (E : OModule ProjectiveLine) :
    Function.Surjective
        (LeBrunSalamon.PhaseThree.restrictSection (ProjectiveLinePoint.rebase Q x).map
          (E := E)) ↔
      Function.Surjective (LeBrunSalamon.PhaseThree.restrictSection x.map (E := E)) := by
  exact (surjective_iff_of_coordinates _ _ (Equiv.refl _) (rebaseRestrictionEquiv Q x E)
    (rebaseRestrictionEquiv_apply Q x E)).symm

/-- The original two-point evaluation criterion is invariant under a
change of the supplied complex-base identification. The source sections are
unchanged; each original target Hom space is transported explicitly. -/
theorem twoPointBundleEvaluation_rebase_surjective_iff {P : ProjectiveLineOverC}
    (Q : ProjectiveLineOverC) (x y : ProjectiveLinePoint P) (E : OModule ProjectiveLine) :
    Function.Surjective
        (twoPointBundleEvaluation Q (ProjectiveLinePoint.rebase Q x)
          (ProjectiveLinePoint.rebase Q y) E) ↔
      Function.Surjective (twoPointBundleEvaluation P x y E) := by
  apply (surjective_iff_of_coordinates _ _ (Equiv.refl _)
    ((rebaseRestrictionEquiv Q x E).prodCongr (rebaseRestrictionEquiv Q y E)) ?_).symm
  intro s
  apply Prod.ext
  · exact rebaseRestrictionEquiv_apply Q x E s
  · exact rebaseRestrictionEquiv_apply Q y E s

/-- Exchanging the two marked targets does not change surjectivity of the
actual simultaneous restriction map. -/
theorem pointPairRestriction_swap {X : Scheme} (E : OModule X)
    (x y : ComplexBase ⟶ X) :
    Function.Surjective (pointPairRestriction E x y) ↔
      Function.Surjective (pointPairRestriction E y x) :=
  surjective_iff_of_coordinates _ _ (Equiv.refl _) (Equiv.prodComm _ _) (fun _ => rfl)

end LeBrunSalamon.PointBaseTransport

namespace LeBrunSalamon.P1Overlap

variable {K : Type*} [Field K]

/-- Two finite-coordinate values of the established matching-polynomial
space; the geometric transport below supplies its relation to actual fibers. -/
def twoFiniteEvaluation (d : ℤ) (x y : K) : matchingSpace (K := K) d →ₗ[K] K × K :=
  (finitePointEvaluation d x).prod (finitePointEvaluation d y)

/-- One finite-coordinate value and the value at infinity. -/
def finiteInfinityEvaluation (d : ℤ) (x : K) : matchingSpace (K := K) d →ₗ[K] K × K where
  toFun s := (s.val.1.eval x, s.val.2.eval 0)
  map_add' s t := by ext <;> simp
  map_smul' c s := by ext <;> simp

/-- The actual interpolation polynomial is linear; its reflected partner
satisfies the original Laurent matching equation for every positive degree. -/
theorem twoFiniteEvaluation_surjective (n : ℕ) (hn : 1 ≤ n)
    (x y : K) (hxy : x ≠ y) :
    Function.Surjective (twoFiniteEvaluation (K := K) (n : ℤ) x y) := by
  rintro ⟨a, b⟩
  let m : K := (b - a) / (y - x)
  let f : Polynomial K := Polynomial.C (a - m * x) + Polynomial.monomial 1 m
  have hf : f.natDegree ≤ n := by
    apply Polynomial.natDegree_add_le_of_degree_le
    · simpa only [Polynomial.natDegree_C] using (Nat.zero_le n)
    · exact (Polynomial.natDegree_monomial_le m).trans hn
  refine ⟨⟨(f, f.reflect n), matching_reflect n f hf⟩, ?_⟩
  apply Prod.ext
  · change f.eval x = a
    simp only [f, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_monomial, pow_one]
    ring
  · change f.eval y = b
    have hyx : y - x ≠ 0 := sub_ne_zero.mpr hxy.symm
    simp only [f, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_monomial, pow_one]
    dsimp [m]
    field_simp [hyx] <;> ring

theorem twoFiniteEvaluation_surjective_iff (d : ℤ) (x y : K) (hxy : x ≠ y) :
    Function.Surjective (twoFiniteEvaluation (K := K) d x y) ↔ 1 ≤ d := by
  constructor
  · intro hs
    by_contra hd
    have hd' : d ≤ 0 := by omega
    obtain ⟨s, hs⟩ := hs (1, 0)
    have ha := congrArg Prod.fst hs
    have hb := congrArg Prod.snd hs
    change s.val.1.eval x = 1 at ha
    change s.val.1.eval y = 0 at hb
    rcases lt_or_eq_of_le hd' with hneg | rfl
    · rw [(matching_negative hneg s.property).1, Polynomial.eval_zero] at ha
      exact zero_ne_one ha
    · have hc := Polynomial.eq_C_of_natDegree_le_zero (matching_degree_le (d := 0) s.property)
      rw [hc, Polynomial.eval_C] at ha hb
      exact one_ne_zero (ha.symm.trans hb)
  · intro hd
    have hd0 : 0 ≤ d := by omega
    rw [← Int.toNat_of_nonneg hd0]
    exact twoFiniteEvaluation_surjective d.toNat (by omega) x y hxy

/-- A constant correction of the top monomial interpolates a finite value
and the coefficient which gives the actual value at infinity. -/
theorem finiteInfinityEvaluation_surjective (n : ℕ) (hn : 1 ≤ n) (x : K) :
    Function.Surjective (finiteInfinityEvaluation (K := K) (n : ℤ) x) := by
  rintro ⟨a, b⟩
  let f : Polynomial K := Polynomial.C (a - b * x ^ n) + Polynomial.monomial n b
  have hf : f.natDegree ≤ n := by
    apply Polynomial.natDegree_add_le_of_degree_le
    · simpa only [Polynomial.natDegree_C] using (Nat.zero_le n)
    · exact Polynomial.natDegree_monomial_le b
  refine ⟨⟨(f, f.reflect n), matching_reflect n f hf⟩, ?_⟩
  apply Prod.ext
  · change f.eval x = a
    simp only [f, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_monomial]
    ring
  · change (f.reflect n).eval 0 = b
    rw [matching_evaluation_at_infinity (matching_reflect n f hf)]
    simp only [f, Polynomial.coeff_add, Polynomial.coeff_C,
      if_neg (show n ≠ 0 by omega), Polynomial.coeff_monomial_same, zero_add]

theorem finiteInfinityEvaluation_surjective_iff (d : ℤ) (x : K) :
    Function.Surjective (finiteInfinityEvaluation (K := K) d x) ↔ 1 ≤ d := by
  constructor
  · intro hs
    by_contra hd
    have hd' : d ≤ 0 := by omega
    obtain ⟨s, hs⟩ := hs (1, 0)
    have ha := congrArg Prod.fst hs
    have hb := congrArg Prod.snd hs
    change s.val.1.eval x = 1 at ha
    change s.val.2.eval 0 = 0 at hb
    rcases lt_or_eq_of_le hd' with hneg | rfl
    · rw [(matching_negative hneg s.property).1, Polynomial.eval_zero] at ha
      exact zero_ne_one ha
    · have hc := Polynomial.eq_C_of_natDegree_le_zero (matching_degree_le (d := 0) s.property)
      rw [hc, Polynomial.eval_C] at ha
      rw [matching_evaluation_at_infinity (d := 0) s.property] at hb
      exact one_ne_zero (ha.symm.trans hb)
  · intro hd
    have hd0 : 0 ≤ d := by omega
    rw [← Int.toNat_of_nonneg hd0]
    exact finiteInfinityEvaluation_surjective d.toNat (by omega) x

end LeBrunSalamon.P1Overlap

namespace LeBrunSalamon.P1TwistEvaluation

open LeBrunSalamon.FrameEvaluation LeBrunSalamon.P1TwistSections
open LeBrunSalamon.PointBaseTransport

/-- Read the actual restricted morphism in the already constructed fiber
frame, retaining its pulled-back structure sheaf as the source. -/
def restrictedPointCoordinates (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ) (i : Fin 2) (c : ℂ) :
    (pullbackModule (pointMap i c) (structureModule ProjectiveLine) ⟶
      pullbackModule (pointMap i c) (projectiveTwist P p d).sheaf) ≃ ℂ :=
  (restrictedSectionValueEquiv (pointMap i c) (projectiveTwist P p d).sheaf).toEquiv.trans
    (fiberCoordinates P p d i c).toEquiv

theorem restrictedPointCoordinates_apply (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ) (i : Fin 2) (c : ℂ)
    (s : AlgebraicSection (projectiveTwist P p d).sheaf) :
    restrictedPointCoordinates P p d i c
        (LeBrunSalamon.PhaseThree.restrictSection (pointMap i c) s) =
      (P1TwistFrames.polynomialCoordinates P p d i
        (TwoChartSections.restrictValue (projectiveTwist P p d).sheaf
          le_top (sectionValue s))).eval c := by
  exact
    (restrictedSectionValueEquiv_trans_apply
      (pointMap i c) (projectiveTwist P p d).sheaf
      (fiberCoordinates P p d i c).toEquiv s).trans
      (fiberCoordinates_pullSection P p d i c s)

/-- The original restriction pair at distinct finite points is conjugate
to the computed two-finite-polynomial evaluation, through actual frames. -/
theorem finitePairRestriction_surjective_iff (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ) (a b : ℂ) (hab : a ≠ b) :
    Function.Surjective
      (pointPairRestriction (projectiveTwist P p d).sheaf (pointMap 0 a) (pointMap 0 b)) ↔
      1 ≤ d := by
  apply (surjective_iff_of_coordinates _ (P1Overlap.twoFiniteEvaluation d a b)
    (algebraicMatchingEquiv P p d).toEquiv
    ((restrictedPointCoordinates P p d 0 a).prodCongr
      (restrictedPointCoordinates P p d 0 b)) ?_).trans
      (P1Overlap.twoFiniteEvaluation_surjective_iff d a b hab)
  intro s
  apply Prod.ext
  · change restrictedPointCoordinates P p d 0 a
      (LeBrunSalamon.PhaseThree.restrictSection (pointMap 0 a) s) =
        (algebraicMatchingEquiv P p d s).val.1.eval a
    rw [restrictedPointCoordinates_apply, algebraicMatchingEquiv_fst]
  · change restrictedPointCoordinates P p d 0 b
      (LeBrunSalamon.PhaseThree.restrictSection (pointMap 0 b) s) =
        (algebraicMatchingEquiv P p d s).val.1.eval b
    rw [restrictedPointCoordinates_apply, algebraicMatchingEquiv_fst]

/-- A finite point and infinity give the same positive-degree criterion
for the original pair of restricted sheaf morphisms. -/
theorem finiteInfinityRestriction_surjective_iff (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ) (a : ℂ) :
    Function.Surjective
      (pointPairRestriction (projectiveTwist P p d).sheaf (pointMap 0 a) (pointMap 1 0)) ↔
      1 ≤ d := by
  apply (surjective_iff_of_coordinates _ (P1Overlap.finiteInfinityEvaluation d a)
    (algebraicMatchingEquiv P p d).toEquiv
    ((restrictedPointCoordinates P p d 0 a).prodCongr
      (restrictedPointCoordinates P p d 1 0)) ?_).trans
      (P1Overlap.finiteInfinityEvaluation_surjective_iff d a)
  intro s
  apply Prod.ext
  · change restrictedPointCoordinates P p d 0 a
      (LeBrunSalamon.PhaseThree.restrictSection (pointMap 0 a) s) =
        (algebraicMatchingEquiv P p d s).val.1.eval a
    rw [restrictedPointCoordinates_apply, algebraicMatchingEquiv_fst]
  · change restrictedPointCoordinates P p d 1 0
      (LeBrunSalamon.PhaseThree.restrictSection (pointMap 1 0) s) =
        (algebraicMatchingEquiv P p d s).val.2.eval 0
    rw [restrictedPointCoordinates_apply, algebraicMatchingEquiv_snd]

/-- The complete actual two-point statement over the canonical base.
All pairs are covered by actual point classification, including either
ordering of a finite point and infinity. -/
theorem canonicalPairRestriction_surjective_iff (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ) (x y : ComplexBase ⟶ ProjectiveLine)
    (hx : x ≫ canonicalProjectiveLine.structureMap = 𝟙 ComplexBase)
    (hy : y ≫ canonicalProjectiveLine.structureMap = 𝟙 ComplexBase) (hxy : x ≠ y) :
    Function.Surjective (pointPairRestriction (projectiveTwist P p d).sheaf x y) ↔
      1 ≤ d := by
  rcases canonicalPoint_finite_or_infinity x hx with ⟨a, rfl⟩ | rfl
  · rcases canonicalPoint_finite_or_infinity y hy with ⟨b, rfl⟩ | rfl
    · exact finitePairRestriction_surjective_iff P p d a b
        (fun h => hxy (congrArg (pointMap 0) h))
    · exact finiteInfinityRestriction_surjective_iff P p d a
  · rcases canonicalPoint_finite_or_infinity y hy with ⟨b, rfl⟩ | rfl
    · exact (pointPairRestriction_swap (projectiveTwist P p d).sheaf
        (pointMap 1 0) (pointMap 0 b)).trans
          (finiteInfinityRestriction_surjective_iff P p d b)
    · exact (hxy rfl).elim

/-- Original one-point restriction at any rational point for any supplied
complex-base identification, with the original Hom codomain retained. -/
theorem suppliedRestriction_surjective_iff (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ) (Q : ProjectiveLineOverC)
    (x : ProjectiveLinePoint Q) :
    Function.Surjective
      (LeBrunSalamon.PhaseThree.restrictSection x.map
        (E := (projectiveTwist P p d).sheaf)) ↔ 0 ≤ d := by
  rw [← restrictSection_rebase_surjective_iff canonicalProjectiveLine x
    (projectiveTwist P p d).sheaf]
  exact restrictSection_surjective_iff P p d
    (ProjectiveLinePoint.rebase canonicalProjectiveLine x).map
    (ProjectiveLinePoint.rebase canonicalProjectiveLine x).overC

/-- The original line-bundle two-point evaluation map at every pair of
distinct rational points, for every supplied complex-base identification.
Neither its source nor its original pullback Hom codomain is replaced. -/
theorem twoPointBundleEvaluation_surjective_iff (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ) (Q : ProjectiveLineOverC)
    (x y : ProjectiveLinePoint Q) (hxy : x.map ≠ y.map) :
    Function.Surjective (twoPointBundleEvaluation Q x y (projectiveTwist P p d).sheaf) ↔
      1 ≤ d := by
  rw [← twoPointBundleEvaluation_rebase_surjective_iff canonicalProjectiveLine x y
    (projectiveTwist P p d).sheaf]
  exact canonicalPairRestriction_surjective_iff P p d
    (ProjectiveLinePoint.rebase canonicalProjectiveLine x).map
    (ProjectiveLinePoint.rebase canonicalProjectiveLine y).map
    (ProjectiveLinePoint.rebase canonicalProjectiveLine x).overC
    (ProjectiveLinePoint.rebase canonicalProjectiveLine y).overC
    (fun h => hxy ((ProjectiveLinePoint.rebase_map_eq_iff canonicalProjectiveLine x y).mp h))

/-- The existing original two-point global-generation predicate now has
its exact line-bundle criterion, including its nonvacuity requirement. -/
theorem projectiveTwist_twoPointGloballyGenerated_iff (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ) (Q : ProjectiveLineOverC) :
    PhaseSeven.IsTwoPointGloballyGenerated Q (projectiveTwist P p d).sheaf ↔ 1 ≤ d := by
  constructor
  · intro h
    obtain ⟨x, y, hxy⟩ := h.1
    exact (twoPointBundleEvaluation_surjective_iff P p d Q x y hxy).mp (h.2 x y hxy)
  · intro hd
    refine ⟨projectiveLine_hasDistinctPoints Q, ?_⟩
    intro x y hxy
    exact (twoPointBundleEvaluation_surjective_iff P p d Q x y hxy).mpr hd

/-- Actual one-point fiber evaluation for the supplied base satisfies the
same criterion. Its linearity comes from the original overC equation. -/
theorem suppliedEvaluation_surjective_iff (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ) (Q : ProjectiveLineOverC)
    (x : ProjectiveLinePoint Q) :
    Function.Surjective
      (evaluateSection Q.structureMap (projectiveTwist P p d).sheaf x.map x.overC) ↔ 0 ≤ d := by
  have h := surjective_iff_of_coordinates
    (LeBrunSalamon.PhaseThree.restrictSection x.map (E := (projectiveTwist P p d).sheaf))
    (evaluateSection Q.structureMap (projectiveTwist P p d).sheaf x.map x.overC)
    (sectionAddEquiv (projectiveTwist P p d).sheaf).toEquiv
    (restrictedSectionValueEquiv x.map (projectiveTwist P p d).sheaf).toEquiv (by
      intro s
      change sectionValue (pullSection x.map s) =
        sectionValue (pullSection x.map (sectionFromValue (sectionValue s)))
      rw [sectionFromValue_sectionValue])
  exact h.symm.trans (suppliedRestriction_surjective_iff P p d Q x)

/-- Pair the existing actual C-linear fiber evaluation maps for the
supplied base. The codomain consists of the two genuine pulled-back fibers. -/
def suppliedPairEvaluation (Q : ProjectiveLineOverC) (E : OModule ProjectiveLine)
    (x y : ProjectiveLinePoint Q) : CSections Q.structureMap E →ₗ[ℂ]
      (Fiber E x.map × Fiber E y.map) :=
  (evaluateSection Q.structureMap E x.map x.overC).prod
    (evaluateSection Q.structureMap E y.map y.overC)

theorem suppliedPairEvaluation_surjective_iff (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ) (Q : ProjectiveLineOverC)
    (x y : ProjectiveLinePoint Q) (hxy : x.map ≠ y.map) :
    Function.Surjective (suppliedPairEvaluation Q (projectiveTwist P p d).sheaf x y) ↔
      1 ≤ d := by
  have h := surjective_iff_of_coordinates
    (twoPointBundleEvaluation Q x y (projectiveTwist P p d).sheaf)
    (suppliedPairEvaluation Q (projectiveTwist P p d).sheaf x y)
    (sectionAddEquiv (projectiveTwist P p d).sheaf).toEquiv
    ((restrictedSectionValueEquiv x.map (projectiveTwist P p d).sheaf).toEquiv.prodCongr
      (restrictedSectionValueEquiv y.map (projectiveTwist P p d).sheaf).toEquiv) (by
      intro s
      change (sectionValue (pullSection x.map s), sectionValue (pullSection y.map s)) =
        (sectionValue (pullSection x.map (sectionFromValue (sectionValue s))),
          sectionValue (pullSection y.map (sectionFromValue (sectionValue s))))
      rw [sectionFromValue_sectionValue])
  exact h.symm.trans (twoPointBundleEvaluation_surjective_iff P p d Q x y hxy)

end LeBrunSalamon.P1TwistEvaluation

end
/- END UNCOMPILED continuation point_base_transport.lean.txt -/

/- BEGIN UNCOMPILED continuation split_sections.lean.txt -/
/-!
Actual section coordinates and dimensions for finite direct sums.

Uncompiled continuation. Insert after Construction, P1TwistSections, and
DirectSumGeometry.
The comparison is built from the actual coproduct inclusions and projections,
with the complex action determined by the supplied structure map.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseEighteen LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.Construction
open scoped BigOperators

namespace LeBrunSalamon.DirectSumSections

/-- Actual complex section maps preserve identity and composition. -/
@[simp]
theorem onCSections_id {X : Scheme} (sX : X ⟶ ComplexBase) (E : OModule X) :
    onCSections sX (𝟙 E) = LinearMap.id := rfl

theorem onCSections_comp {X : Scheme} (sX : X ⟶ ComplexBase)
    {E F G : OModule X} (f : E ⟶ F) (g : F ⟶ G) :
    onCSections sX (f ≫ g) = (onCSections sX g).comp (onCSections sX f) := rfl

/-- Additivity in the actual sheaf map, not merely in the input section. -/
def onCSectionsAddHom {X : Scheme} (sX : X ⟶ ComplexBase) (E F : OModule X) :
    (E ⟶ F) →+ (CSections sX E →ₗ[ℂ] CSections sX F) where
  toFun := onCSections sX
  map_zero' := by ext x; rfl
  map_add' f g := by ext x; rfl

@[simp]
theorem onCSections_zero {X : Scheme} (sX : X ⟶ ComplexBase) (E F : OModule X) :
    onCSections sX (0 : E ⟶ F) = 0 := (onCSectionsAddHom sX E F).map_zero

theorem onCSections_sum {X : Scheme} (sX : X ⟶ ComplexBase)
    {E F : OModule X} {I : Type} (s : Finset I) (f : I → (E ⟶ F)) :
    onCSections sX (∑ i ∈ s, f i) = ∑ i ∈ s, onCSections sX (f i) :=
  map_sum (onCSectionsAddHom sX E F) f s

/-- Coordinates on genuine sections of the actual finite coproduct. The
inverse takes the finite sum of the actual inclusion maps on sections. -/
def cSectionsCoproductEquiv {X : Scheme} (sX : X ⟶ ComplexBase)
    {I : Type} [Fintype I] (E : I → OModule X) :
    CSections sX (∐ E) ≃ₗ[ℂ] (∀ i, CSections sX (E i)) := by
  classical
  exact
    { toFun := fun x i => onCSections sX (Sigma.π E i) x
      invFun := fun x => ∑ i, onCSections sX (Sigma.ι E i) (x i)
      left_inv := by
        intro x
        have h := congrArg (fun f : (∐ E) ⟶ ∐ E => onCSections sX f x)
          (DirectSumGeometry.coproduct_total E)
        rw [onCSections_sum] at h
        simpa only [LinearMap.sum_apply, onCSections_comp, LinearMap.comp_apply,
          onCSections_id, LinearMap.id_apply] using h
      right_inv := by
        intro x
        funext j
        change onCSections sX (Sigma.π E j)
          (∑ i, onCSections sX (Sigma.ι E i) (x i)) = x j
        rw [map_sum, Finset.sum_eq_single j]
        · change onCSections sX (Sigma.ι E j ≫ Sigma.π E j) (x j) = x j
          rw [Sigma.ι_π_eq_id, onCSections_id] <;> rfl
        · intro i _ hij
          change onCSections sX (Sigma.ι E i ≫ Sigma.π E j) (x i) = 0
          rw [Sigma.ι_π_of_ne E hij, onCSections_zero] <;> rfl
        · simp
      map_add' := by
        intro x y
        funext i
        exact map_add (onCSections sX (Sigma.π E i)) x y
      map_smul' := by
        intro c x
        funext i
        exact map_smul (onCSections sX (Sigma.π E i)) c x }

theorem cSectionsCoproduct_finrank {X : Scheme} (sX : X ⟶ ComplexBase)
    {I : Type} [Fintype I] (E : I → OModule X)
    [∀ i, Module.Finite ℂ (CSections sX (E i))] :
    Module.finrank ℂ (CSections sX (∐ E)) =
      ∑ i, Module.finrank ℂ (CSections sX (E i)) := by
  rw [(cSectionsCoproductEquiv sX E).finrank_eq, Module.finrank_pi_fintype]

end LeBrunSalamon.DirectSumSections

namespace LeBrunSalamon.P1SplitBundles

/-- The actual C-section space of the original split sheaf has explicit
coordinates in the section spaces of its original twist summands. -/
def splitCSectionsEquiv (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {r : ℕ} (a : TangentSplittingProfile r) :
    CSections P.structureMap (splitSheaf P p a) ≃ₗ[ℂ]
      (∀ i : Fin r, CSections P.structureMap (projectiveTwist P p (a.degree i)).sheaf) :=
  DirectSumSections.cSectionsCoproductEquiv P.structureMap
    (fun i : Fin r => (projectiveTwist P p (a.degree i)).sheaf)

instance splitCSections_finite (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {r : ℕ} (a : TangentSplittingProfile r) :
    Module.Finite ℂ (CSections P.structureMap (splitSheaf P p a)) :=
  Module.Finite.equiv (splitCSectionsEquiv P p a).symm

/-- The previously numerical h0 profile equals the dimension of the actual
complex section space for every integer degree profile, including rank zero. -/
theorem splitCSections_finrank (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {r : ℕ} (a : TangentSplittingProfile r) :
    Module.finrank ℂ (CSections P.structureMap (splitSheaf P p a)) = a.predictedHZero := by
  rw [(splitCSectionsEquiv P p a).finrank_eq, Module.finrank_pi_fintype]
  simp only [P1TwistSections.cSections_finrank, TangentSplittingProfile.predictedHZero]

/-- The original supplied splitting transports actual section coordinates. -/
def realizedCSectionsEquiv (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {r : ℕ} (E : AlgebraicVectorBundle ProjectiveLine r) (a : TangentSplittingProfile r)
    (ha : RealizesSplitting P p E a) :
    CSections P.structureMap E.sheaf ≃ₗ[ℂ]
      (∀ i : Fin r, CSections P.structureMap (projectiveTwist P p (a.degree i)).sheaf) :=
  (P1TwistSections.cSectionsIso P.structureMap (Classical.choice ha)).trans
    (splitCSectionsEquiv P p a)

theorem realizedCSections_finite (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {r : ℕ} (E : AlgebraicVectorBundle ProjectiveLine r) (a : TangentSplittingProfile r)
    (ha : RealizesSplitting P p E a) : Module.Finite ℂ (CSections P.structureMap E.sheaf) :=
  Module.Finite.equiv (realizedCSectionsEquiv P p E a ha).symm

theorem realizedCSections_finrank (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {r : ℕ} (E : AlgebraicVectorBundle ProjectiveLine r) (a : TangentSplittingProfile r)
    (ha : RealizesSplitting P p E a) :
    Module.finrank ℂ (CSections P.structureMap E.sheaf) = a.predictedHZero := by
  rw [(realizedCSectionsEquiv P p E a ha).finrank_eq, Module.finrank_pi_fintype]
  simp only [P1TwistSections.cSections_finrank, TangentSplittingProfile.predictedHZero]

end LeBrunSalamon.P1SplitBundles

end
/- END UNCOMPILED continuation split_sections.lean.txt -/

/- BEGIN UNCOMPILED continuation split_evaluation.lean.txt -/
/-!
Actual simultaneous point evaluation for finite split bundles.

Uncompiled continuation. Insert after DirectSumGeometry.coproduct_total,
PointBaseTransport, and P1TwistEvaluation's arbitrary-pair criterion.
The original restriction codomains remain Hom sets out of the pulled-back
structure sheaf throughout. All finite-sum comparisons use actual sheaf
inclusions, projections, and the additive pullback functors.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseEighteen LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.PointBaseTransport
open scoped BigOperators

namespace LeBrunSalamon.DirectSumEvaluation

/-- The actual finite-sum Hom coordinates survive every additive functor.
No chosen identification of the image with a different coproduct is needed:
the projections and inclusions are mapped by the specified functor itself. -/
def mappedCoproductHomEquiv {X Y : Scheme}
    (F : OModule X ⥤ OModule Y) [F.Additive] (A : OModule Y)
    {I : Type} [Fintype I] [DecidableEq I] (E : I → OModule X) :
    (A ⟶ F.obj (∐ E)) ≃+ (∀ i, A ⟶ F.obj (E i)) where
  toFun s i := s ≫ F.map (Sigma.π E i)
  invFun s := ∑ i, s i ≫ F.map (Sigma.ι E i)
  left_inv s := by
    have h := congrArg (fun k : (∐ E) ⟶ ∐ E => s ≫ F.map k)
      (DirectSumGeometry.coproduct_total E)
    simpa only [F.map_sum, Preadditive.comp_sum, F.map_comp,
      Category.assoc, F.map_id, Category.comp_id] using h
  right_inv s := by
    funext j
    change (∑ i, s i ≫ F.map (Sigma.ι E i)) ≫ F.map (Sigma.π E j) = s j
    rw [Preadditive.sum_comp, Finset.sum_eq_single j]
    · rw [Category.assoc, ← F.map_comp, Sigma.ι_π_eq_id,
        F.map_id, Category.comp_id]
    · intro i _ hij
      rw [Category.assoc, ← F.map_comp, Sigma.ι_π_of_ne E hij,
        F.map_zero, comp_zero]
    · simp
  map_add' s t := by
    funext i
    simp only [Preadditive.add_comp, Pi.add_apply]

/-- A map into the image of the actual coproduct is reconstructed from
its projected coordinates, even when that image is a pullback sheaf. -/
theorem map_coproduct_sum_eq {X Y : Scheme}
    (F : OModule X ⥤ OModule Y) [F.Additive] (A : OModule X)
    {I : Type} [Fintype I] [DecidableEq I] (E : I → OModule X)
    (s : ∀ i, A ⟶ E i) (v : F.obj A ⟶ F.obj (∐ E))
    (h : ∀ i, F.map (s i) = v ≫ F.map (Sigma.π E i)) :
    F.map (∑ i, s i ≫ Sigma.ι E i) = v := by
  rw [F.map_sum]
  calc
    _ = ∑ i, (v ≫ F.map (Sigma.π E i)) ≫ F.map (Sigma.ι E i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [F.map_comp, h i]
    _ = v := (mappedCoproductHomEquiv F (F.obj A) E).left_inv v

/-- Simultaneous restriction surjectivity passes to an actual retract.
The target pair is first included into the larger pulled-back sheaves,
and the lifted global section is then projected back. -/
theorem pointPairRestriction_surjective_of_retract {X : Scheme}
    {E F : OModule X} (j : E ⟶ F) (r : F ⟶ E) (hjr : j ≫ r = 𝟙 E)
    (x y : ComplexBase ⟶ X)
    (hF : Function.Surjective (pointPairRestriction F x y)) :
    Function.Surjective (pointPairRestriction E x y) := by
  rintro ⟨a, b⟩
  obtain ⟨s, hs⟩ := hF
    (a ≫ (Scheme.Modules.pullback x).map j,
      b ≫ (Scheme.Modules.pullback y).map j)
  have hx := congrArg Prod.fst hs
  have hy := congrArg Prod.snd hs
  change (Scheme.Modules.pullback x).map s =
    a ≫ (Scheme.Modules.pullback x).map j at hx
  change (Scheme.Modules.pullback y).map s =
    b ≫ (Scheme.Modules.pullback y).map j at hy
  refine ⟨s ≫ r, Prod.ext ?_ ?_⟩
  · change (Scheme.Modules.pullback x).map (s ≫ r) = a
    rw [CategoryTheory.Functor.map_comp, hx, Category.assoc, ← CategoryTheory.Functor.map_comp, hjr,
      CategoryTheory.Functor.map_id, Category.comp_id]
  · change (Scheme.Modules.pullback y).map (s ≫ r) = b
    rw [CategoryTheory.Functor.map_comp, hy, Category.assoc, ← CategoryTheory.Functor.map_comp, hjr,
      CategoryTheory.Functor.map_id, Category.comp_id]

/-- An actual sheaf isomorphism preserves surjectivity of the original
pair of restriction maps and its original pulled-back Hom targets. -/
theorem pointPairRestriction_iso_iff {X : Scheme} {E F : OModule X}
    (e : E ≅ F) (x y : ComplexBase ⟶ X) :
    Function.Surjective (pointPairRestriction E x y) ↔
      Function.Surjective (pointPairRestriction F x y) :=
  ⟨pointPairRestriction_surjective_of_retract e.inv e.hom e.inv_hom_id x y,
    pointPairRestriction_surjective_of_retract e.hom e.inv e.hom_inv_id x y⟩

/-- The actual pair evaluation for a finite coproduct is onto exactly
when the pair evaluation of every summand is onto. The empty family is
included; finite reconstruction also proves that its target is trivial. -/
theorem pointPairRestriction_coproduct_surjective_iff {X : Scheme}
    {I : Type} [Fintype I] (E : I → OModule X) (x y : ComplexBase ⟶ X) :
    Function.Surjective (pointPairRestriction (∐ E) x y) ↔
      ∀ i, Function.Surjective (pointPairRestriction (E i) x y) := by
  classical
  constructor
  · intro h i
    exact pointPairRestriction_surjective_of_retract (Sigma.ι E i) (Sigma.π E i)
      (Sigma.ι_π_eq_id E i) x y h
  · intro h
    rintro ⟨a, b⟩
    choose s hs using fun i => h i
      (a ≫ (Scheme.Modules.pullback x).map (Sigma.π E i),
        b ≫ (Scheme.Modules.pullback y).map (Sigma.π E i))
    refine ⟨∑ i, s i ≫ Sigma.ι E i, Prod.ext ?_ ?_⟩
    · exact map_coproduct_sum_eq (Scheme.Modules.pullback x) (structureModule X)
        E s a (fun i => congrArg Prod.fst (hs i))
    · exact map_coproduct_sum_eq (Scheme.Modules.pullback y) (structureModule X)
        E s b (fun i => congrArg Prod.snd (hs i))

/-- The finite-coproduct criterion expressed directly with the original
Phase 32 evaluation function, without changing either target Hom space. -/
theorem twoPointBundleEvaluation_coproduct_surjective_iff (P : ProjectiveLineOverC)
    (p q : ProjectiveLinePoint P) {I : Type} [Fintype I]
    (E : I → OModule ProjectiveLine) :
    Function.Surjective (twoPointBundleEvaluation P p q (∐ E)) ↔
      ∀ i, Function.Surjective (twoPointBundleEvaluation P p q (E i)) :=
  pointPairRestriction_coproduct_surjective_iff E p.map q.map

theorem twoPointBundleEvaluation_iso_iff (P : ProjectiveLineOverC)
    (p q : ProjectiveLinePoint P) {E F : OModule ProjectiveLine} (e : E ≅ F) :
    Function.Surjective (twoPointBundleEvaluation P p q E) ↔
      Function.Surjective (twoPointBundleEvaluation P p q F) :=
  pointPairRestriction_iso_iff e p.map q.map

end LeBrunSalamon.DirectSumEvaluation

namespace LeBrunSalamon.P1SplitBundles

/-- Every supplied degree profile has the exact simultaneous-evaluation
criterion at every distinct pair over every supplied projective-line base.
The summand criterion is the actual arbitrary-pair twist theorem. -/
theorem splitSheaf_twoPointEvaluation_iff (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) {r : ℕ} (a : TangentSplittingProfile r)
    (Q : ProjectiveLineOverC) (x y : ProjectiveLinePoint Q) (hxy : x.map ≠ y.map) :
    Function.Surjective (twoPointBundleEvaluation Q x y (splitSheaf P p a)) ↔
      a.IsVeryFree := by
  rw [splitSheaf, DirectSumEvaluation.twoPointBundleEvaluation_coproduct_surjective_iff]
  exact forall_congr' (fun i =>
    P1TwistEvaluation.twoPointBundleEvaluation_surjective_iff P p (a.degree i) Q x y hxy)

/-- The original split-bundle pair-evaluation criterion follows from the
given actual splitting. No existence or uniqueness theorem for splittings,
and no identification of the original target with linear fibers, is used. -/
theorem splitBundle_twoPointEvaluation_iff (P : ProjectiveLineOverC)
    (p q : ProjectiveLinePoint P) (hpq : p.map ≠ q.map) {r : ℕ}
    (E : AlgebraicVectorBundle ProjectiveLine r) (a : TangentSplittingProfile r)
    (ha : RealizesSplitting P p E a) :
    Function.Surjective (twoPointBundleEvaluation P p q E.sheaf) ↔
      a.IsVeryFree :=
  (DirectSumEvaluation.twoPointBundleEvaluation_iso_iff P p q (Classical.choice ha)).trans
    (splitSheaf_twoPointEvaluation_iff P p a P p q hpq)

end LeBrunSalamon.P1SplitBundles

end
/- END UNCOMPILED continuation split_evaluation.lean.txt -/

namespace LeBrunSalamon.PhaseThirtyTwo

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseThree LeBrunSalamon.PhaseEighteen
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven LeBrunSalamon.PhaseTwentyEight

theorem splitBundle_twoPointEvaluation_iff (P : ProjectiveLineOverC)
    (p q : ProjectiveLinePoint P) (hpq : p.map ≠ q.map) {r : ℕ}
    (E : AlgebraicVectorBundle ProjectiveLine r) (a : TangentSplittingProfile r)
    (ha : RealizesSplitting P p E a) :
    Function.Surjective (twoPointBundleEvaluation P p q E.sheaf) ↔
      a.IsVeryFree := by
  exact LeBrunSalamon.P1SplitBundles.splitBundle_twoPointEvaluation_iff P p q hpq E a ha

end LeBrunSalamon.PhaseThirtyTwo


end
/- END RELOCATED POSITIVE-NODE DEPENDENCY: RecompileTail -/

/- BEGIN RELOCATED POSITIVE-NODE DEPENDENCY: LSSuitableLinear -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseThree LeBrunSalamon.PhaseSeven
open LeBrunSalamon.PhaseEight LeBrunSalamon.PhaseTen
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.PhaseThirty LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.PhaseThirtyFour LeBrunSalamon.PhaseThirtyFive
open LeBrunSalamon.Core LeBrunSalamon.Skeleton

namespace LeBrunSalamon.Construction.Lines.SuitablePairAlgebra

section ActualContactFibers

variable {n : ℕ} (X : ContactFanoManifold n) (x : ComplexPoint X.variety)

theorem inclusionFiber_injective :
    Function.Injective (fiberMap X.contact.sequence.inclusion x.map) :=
  (vectorBundle_fiber_exact X.contact.sequence.distribution
    (intrinsicTangentBundle X.variety) X.contact.sequence.line
    X.contact.sequence.inclusion X.contact.sequence.form
    X.contact.sequence.comp_zero X.contact.sequence.shortExact x.map).1

theorem inclusionFiber_range :
    LinearMap.range (fiberMap X.contact.sequence.inclusion x.map) = contactPlane X x :=
  (vectorBundle_fiber_exact X.contact.sequence.distribution
    (intrinsicTangentBundle X.variety) X.contact.sequence.line
    X.contact.sequence.inclusion X.contact.sequence.form
    X.contact.sequence.comp_zero X.contact.sequence.shortExact x.map).2.2

/-- The inclusion of the actual distribution identifies its fiber with the
kernel of the actual contact-form fiber map. This is not a freely chosen
identification of two vector spaces of the same dimension. -/
def distributionContactEquiv :
    Fiber X.contact.sequence.distribution.sheaf x.map ≃ₗ[ℂ] contactPlane X x :=
  (LinearEquiv.ofInjective (fiberMap X.contact.sequence.inclusion x.map)
    (inclusionFiber_injective X x)).trans
      (LinearEquiv.ofEq _ _ (inclusionFiber_range X x))

@[simp]
theorem distributionContactEquiv_coe
    (u : Fiber X.contact.sequence.distribution.sheaf x.map) :
    (distributionContactEquiv X x u : TangentFiber X.variety x) =
      fiberMap X.contact.sequence.inclusion x.map u := rfl

@[simp]
theorem inclusion_distributionContactEquiv_symm (v : contactPlane X x) :
    fiberMap X.contact.sequence.inclusion x.map
      ((distributionContactEquiv X x).symm v) = (v : TangentFiber X.variety x) := by
  exact congrArg (fun z : contactPlane X x => (z : TangentFiber X.variety x))
    ((distributionContactEquiv X x).apply_symm_apply v)

theorem leviFiberValue_add_left
    (u v w : Fiber X.contact.sequence.distribution.sheaf x.map) :
    leviFiberValue X x (u + v) w = leviFiberValue X x u w + leviFiberValue X x v w := by
  change (pullbackPair x.map (intrinsicLeviPair X.contact.sequence)).apply ⊤ (u + v) w = _
  rw [map_add, LinearMap.add_apply]
  rfl

theorem leviFiberValue_add_right
    (u v w : Fiber X.contact.sequence.distribution.sheaf x.map) :
    leviFiberValue X x u (v + w) = leviFiberValue X x u v + leviFiberValue X x u w := by
  change (pullbackPair x.map (intrinsicLeviPair X.contact.sequence)).apply ⊤ u (v + w) = _
  exact map_add _ v w

theorem leviFiberValue_smul_left (c : ℂ)
    (u v : Fiber X.contact.sequence.distribution.sheaf x.map) :
    leviFiberValue X x (c • u) v = c • leviFiberValue X x u v := by
  simpa only [one_smul] using leviFiberValue_smul_smul X x c 1 u v

theorem leviFiberValue_smul_right (c : ℂ)
    (u v : Fiber X.contact.sequence.distribution.sheaf x.map) :
    leviFiberValue X x u (c • v) = c • leviFiberValue X x u v := by
  simpa only [one_smul] using leviFiberValue_smul_smul X x 1 c u v

theorem leviFiberValue_zero_left
    (v : Fiber X.contact.sequence.distribution.sheaf x.map) :
    leviFiberValue X x 0 v = 0 := by
  change (pullbackPair x.map (intrinsicLeviPair X.contact.sequence)).apply ⊤ 0 v = 0
  rw [map_zero, LinearMap.zero_apply]

theorem leviFiberValue_zero_right
    (u : Fiber X.contact.sequence.distribution.sheaf x.map) :
    leviFiberValue X x u 0 = 0 := by
  change (pullbackPair x.map (intrinsicLeviPair X.contact.sequence)).apply ⊤ u 0 = 0
  exact map_zero _

/-- Scalar restriction of the intrinsic pulled-back Levi pairing. -/
def leviFiberBilinear :
    Fiber X.contact.sequence.distribution.sheaf x.map →ₗ[ℂ]
      Fiber X.contact.sequence.distribution.sheaf x.map →ₗ[ℂ]
        Fiber X.contact.sequence.line.sheaf x.map where
  toFun u :=
    { toFun := leviFiberValue X x u
      map_add' := leviFiberValue_add_right X x u
      map_smul' := fun c v => leviFiberValue_smul_right X x c u v }
  map_add' := by
    intro u v
    ext w
    exact leviFiberValue_add_left X x u v w
  map_smul' := by
    intro c u
    ext v
    exact leviFiberValue_smul_left X x c u v

@[simp]
theorem leviFiberBilinear_apply
    (u v : Fiber X.contact.sequence.distribution.sheaf x.map) :
    leviFiberBilinear X x u v = leviFiberValue X x u v := rfl

/-- The pairing on the contact kernel is obtained solely by inverse image
under the actual inclusion. Its target remains the original contact-line fiber. -/
def contactLevi : contactPlane X x →ₗ[ℂ] contactPlane X x →ₗ[ℂ]
    Fiber X.contact.sequence.line.sheaf x.map :=
  (leviFiberBilinear X x).compl₁₂ (distributionContactEquiv X x).symm.toLinearMap
    (distributionContactEquiv X x).symm.toLinearMap

@[simp]
theorem contactLevi_apply (a b : contactPlane X x) :
    contactLevi X x a b = leviFiberValue X x
      ((distributionContactEquiv X x).symm a)
      ((distributionContactEquiv X x).symm b) := rfl

/-- Exact agreement with the previously defined, witness-based Levi test. -/
theorem nonzeroLeviPair_iff_contactLevi (a b : contactPlane X x) :
    NonzeroLeviPair X x (a : TangentFiber X.variety x) (b : TangentFiber X.variety x) ↔
      contactLevi X x a b ≠ 0 := by
  constructor
  · rintro ⟨u, v, hu, hv, huv⟩
    have heu : distributionContactEquiv X x u = a := Subtype.ext hu
    have hev : distributionContactEquiv X x v = b := Subtype.ext hv
    have hu' : (distributionContactEquiv X x).symm a = u := by
      rw [← heu, LinearEquiv.symm_apply_apply]
    have hv' : (distributionContactEquiv X x).symm b = v := by
      rw [← hev, LinearEquiv.symm_apply_apply]
    simpa only [contactLevi_apply, hu', hv'] using huv
  · intro hab
    exact ⟨(distributionContactEquiv X x).symm a,
      (distributionContactEquiv X x).symm b,
      inclusion_distributionContactEquiv_symm X x a,
      inclusion_distributionContactEquiv_symm X x b, hab⟩

theorem nonzeroLeviPair_left_ne_zero {a b : TangentFiber X.variety x}
    (h : NonzeroLeviPair X x a b) : a ≠ 0 := by
  rintro ha
  obtain ⟨u, v, hu, _hv, huv⟩ := h
  have hu0 : u = 0 := inclusionFiber_injective X x (by rw [hu, ha, map_zero])
  apply huv
  rw [hu0, leviFiberValue_zero_left]

theorem nonzeroLeviPair_right_ne_zero {a b : TangentFiber X.variety x}
    (h : NonzeroLeviPair X x a b) : b ≠ 0 := by
  rintro hb
  obtain ⟨u, v, _hu, hv, huv⟩ := h
  have hv0 : v = 0 := inclusionFiber_injective X x (by rw [hv, hb, map_zero])
  apply huv
  rw [hv0, leviFiberValue_zero_right]

/-- Alternation can be transported once its intrinsic fiber theorem is supplied.
This lemma does not presume that a bare bilinear pairing is alternating. -/
theorem contactLevi_alternating_of_fiber
    (halt : ∀ u : Fiber X.contact.sequence.distribution.sheaf x.map,
      leviFiberValue X x u u = 0) :
    ∀ a : contactPlane X x, contactLevi X x a a = 0 := by
  intro a
  exact halt ((distributionContactEquiv X x).symm a)

theorem contactLevi_leftNondegenerate_of_fiber
    (hnd : ∀ u : Fiber X.contact.sequence.distribution.sheaf x.map,
      (∀ v, leviFiberValue X x u v = 0) → u = 0) :
    ∀ a : contactPlane X x, (∀ b, contactLevi X x a b = 0) → a = 0 := by
  intro a ha
  have hzero : (distributionContactEquiv X x).symm a = 0 := by
    apply hnd
    intro v
    have h := ha (distributionContactEquiv X x v)
    simpa only [contactLevi_apply, LinearEquiv.symm_apply_apply] using h
  apply (distributionContactEquiv X x).symm.injective
  exact hzero.trans (map_zero (distributionContactEquiv X x).symm).symm

end ActualContactFibers

end LeBrunSalamon.Construction.Lines.SuitablePairAlgebra

end
/- END RELOCATED POSITIVE-NODE DEPENDENCY: LSSuitableLinear -/

/- BEGIN RELOCATED POSITIVE-NODE DEPENDENCY: LSLeviFiber -/
/-!
## The actual Levi form on the contact fiber and its cone coordinates

SOURCE: the symplectic contact fiber in `lines:suitable-pair` and the
cross-pairing function in the cone-addition argument.

The alternating form below is the pullback of the bracket-defined sheaf
pairing. Its coordinates use a frame of the original contact-line fiber
and a basis of the actual contact kernel. No arbitrary symplectic form is
substituted for it. The remaining nondegeneracy bridge is stated as the
injectivity of a specified canonical Hom-fiber evaluation map.

STATUS: new source, statically reviewed; no compiler invocation. Existing
foundation admissions, notably normalized pullback-pair uniqueness and
finite-dimensional bundle fibers, remain inherited dependencies.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.Skeleton
open scoped BigOperators

namespace LeBrunSalamon.Construction.Lines.LeviFiberGeometry

/-! ### Alternation follows from the defining commutator -/

/-- The self-commutator vanishes on every subopen, so the characterized
bracket is zero. This does not use the admitted bracket-skew theorem. -/
theorem tangentBracket_self_eq_zero {Y S : Scheme} (s : Y ⟶ S)
    (U : Y.Opens) (v : SectionsOn (tangentSheaf s) U) :
    tangentBracket s U v v = 0 := by
  unfold tangentBracket
  symm
  apply (Classical.choose_spec (tangentBracket_existsUnique s U v v)).2
  intro V i a
  simp [tangentActs]

/-- Alternation of the specified intrinsic sheaf pairing, before pullback. -/
theorem intrinsicLeviPair_alternating {n : ℕ}
    {Y : SmoothProperComplexVariety (2 * n + 1)}
    (C : IntrinsicContactSequence Y) (U : Y.scheme.Opens)
    (u : SectionsOn C.distribution.sheaf U) :
    (intrinsicLeviPair C).apply U u u = 0 := by
  change C.form.app U (tangentBracket Y.structureMap U
    (C.inclusion.app U u) (C.inclusion.app U u)) = 0
  rw [tangentBracket_self_eq_zero, map_zero]

/-- Polarization gives skew symmetry with the same bracket convention. -/
theorem intrinsicLeviPair_skew {n : ℕ}
    {Y : SmoothProperComplexVariety (2 * n + 1)}
    (C : IntrinsicContactSequence Y) (U : Y.scheme.Opens)
    (u v : SectionsOn C.distribution.sheaf U) :
    (intrinsicLeviPair C).apply U u v = -(intrinsicLeviPair C).apply U v u := by
  have h := intrinsicLeviPair_alternating C U (u + v)
  have hsum : (intrinsicLeviPair C).apply U u v +
      (intrinsicLeviPair C).apply U v u = 0 := by
    simpa only [map_add, LinearMap.add_apply,
      intrinsicLeviPair_alternating C U, zero_add, add_zero, add_comm] using h
  exact eq_neg_of_add_eq_zero_left hsum

/-! ### Normalized pullback preserves the identities used below -/

/-- Negative transposition is constructed on all opens, with its actual
restriction compatibility. It is used to transport skew symmetry by
uniqueness of normalized pullback, rather than assuming that global
sections alone generate an arbitrary pullback sheaf. -/
def negativeFlip {Y : Scheme} {E G : OModule Y}
    (b : SheafBilinearMap E E G) : SheafBilinearMap E E G where
  apply U := -(b.apply U).flip
  naturality := by
    intro U V i u v
    change G.presheaf.map i.op (-(b.apply V v u)) =
      -(b.apply U (E.presheaf.map i.op v) (E.presheaf.map i.op u))
    rw [map_neg, b.naturality]

@[simp]
theorem negativeFlip_apply {Y : Scheme} {E G : OModule Y}
    (b : SheafBilinearMap E E G) (U : Y.Opens)
    (u v : SectionsOn E U) :
    (negativeFlip b).apply U u v = -(b.apply U v u) := rfl

/-- Skew symmetry is preserved on every section of every pullback open. -/
theorem pullbackPair_skew {T Y : Scheme} (f : T ⟶ Y)
    {E G : OModule Y} (b : SheafBilinearMap E E G)
    (hskew : ∀ U u v, b.apply U u v = -(b.apply U v u))
    (V : T.Opens) (u v : SectionsOn (pullbackModule f E) V) :
    (pullbackPair f b).apply V u v = -(pullbackPair f b).apply V v u := by
  have hnorm : IsPullbackPair f b (negativeFlip (pullbackPair f b)) := by
    intro U e z
    change -((pullbackPair f b).apply (f ⁻¹ᵁ U)
      (pullLocalSection f E U z) (pullLocalSection f E U e)) =
        pullLocalSection f G U (b.apply U e z)
    rw [pullbackPair_normalized f b U z e, hskew U e z]
    simp only [pullLocalSection, map_neg]
  have heq : negativeFlip (pullbackPair f b) = pullbackPair f b :=
    (Classical.choose_spec (pullbackPair_existsUnique f b)).2 _ hnorm
  have h := congrArg (fun q : SheafBilinearMap (pullbackModule f E)
    (pullbackModule f E) (pullbackModule f G) => q.apply V u v) heq
  exact h.symm

/-- Naturality of the adjunction unit fixes the map on pulled sections. -/
theorem pullLocalSection_map {T Y : Scheme} (f : T ⟶ Y)
    {E F : OModule Y} (h : E ⟶ F) (U : Y.Opens) (u : SectionsOn E U) :
    pullLocalSection f F U (h.app U u) =
      ((Scheme.Modules.pullback f).map h).app (f ⁻¹ᵁ U)
        (pullLocalSection f E U u) := by
  have hn := (Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality h
  exact congrArg (fun k : E ⟶
    (Scheme.Modules.pushforward f).obj (pullbackModule f F) => k.app U u) hn

/-- Pullback commutes with precomposition by the specified morphisms.
This supplies the comparison needed by the actual contact currying map. -/
theorem pullbackPair_precompose {T Y : Scheme} (f : T ⟶ Y)
    {E F E' F' G : OModule Y} (b : SheafBilinearMap E' F' G)
    (a : E ⟶ E') (c : F ⟶ F') :
    pullbackPair f (b.precompose a c) =
      (pullbackPair f b).precompose ((Scheme.Modules.pullback f).map a)
        ((Scheme.Modules.pullback f).map c) := by
  have hn : IsPullbackPair f (b.precompose a c)
      ((pullbackPair f b).precompose ((Scheme.Modules.pullback f).map a)
        ((Scheme.Modules.pullback f).map c)) := by
    intro U u v
    change (pullbackPair f b).apply (f ⁻¹ᵁ U)
      (((Scheme.Modules.pullback f).map a).app (f ⁻¹ᵁ U)
        (pullLocalSection f E U u))
      (((Scheme.Modules.pullback f).map c).app (f ⁻¹ᵁ U)
        (pullLocalSection f F U v)) =
      pullLocalSection f G U (b.apply U (a.app U u) (c.app U v))
    rw [← pullLocalSection_map f a U u, ← pullLocalSection_map f c U v]
    exact pullbackPair_normalized f b U (a.app U u) (c.app U v)
  exact ((Classical.choose_spec
    (pullbackPair_existsUnique f (b.precompose a c))).2 _ hn).symm

/-! ### The canonical map from the Hom fiber to fiberwise linear maps -/

/-- The evaluation pairing for the project's chosen internal Hom.
Its normalization comes from the tensor and Hom presentations. -/
def sheafEvaluationPair {Y : Scheme} (E F : OModule Y) :
    SheafBilinearMap (internalHomSheaf E F) E F :=
  (tensorPresentation (internalHomSheaf E F) E).pair.postcompose
    (internalHomPresentation E F).evaluate

/-- Evaluation after currying reproduces the original bilinear map,
including its normalization on local sections. -/
theorem sheafEvaluationPair_curry {Y : Scheme} {Z E F : OModule Y}
    (b : SheafBilinearMap Z E F) :
    (sheafEvaluationPair E F).precompose (currySheaf (tensorLift b)) (𝟙 E) = b := by
  apply sheafBilinearMap_ext
  intro U u v
  have h := congrArg (fun k : tensorSheaf Z E ⟶ F =>
    k.app U ((tensorPresentation Z E).pair.apply U u v))
      (currySheaf_evaluate (tensorLift b))
  change (internalHomPresentation E F).evaluate.app U
    ((tensorMap (currySheaf (tensorLift b)) (𝟙 E)).app U
      ((tensorPresentation Z E).pair.apply U u v)) = _ at h
  rw [tensorMap_apply] at h
  have hp := congrArg (fun q : SheafBilinearMap Z E F => q.apply U u v)
    (tensorLift_pair b)
  exact h.trans hp

/-- Complex scalar restriction of a genuine pulled-back sheaf pairing. -/
def fiberPair {Y : Scheme} {E F G : OModule Y}
    (b : SheafBilinearMap E F G) (x : ComplexBase ⟶ Y) :
    Fiber E x →ₗ[ℂ] Fiber F x →ₗ[ℂ] Fiber G x where
  toFun u :=
    { toFun := fun v => (pullbackPair x b).apply ⊤ u v
      map_add' := by intro v w; exact map_add _ v w
      map_smul' := by
        intro c v
        change (pullbackPair x b).apply ⊤ u
          ((complexConstants (𝟙 ComplexBase) c) •
            (show SectionsOn (pullbackModule x F) ⊤ from v)) =
            (complexConstants (𝟙 ComplexBase) c) •
              (pullbackPair x b).apply ⊤ u v
        exact map_smul _ _ _ }
  map_add' := by
    intro u v
    ext w
    change (pullbackPair x b).apply ⊤ (u + v) w = _
    rw [map_add, LinearMap.add_apply]
    rfl
  map_smul' := by
    intro c u
    ext v
    change (pullbackPair x b).apply ⊤
      ((complexConstants (𝟙 ComplexBase) c) •
        (show SectionsOn (pullbackModule x E) ⊤ from u)) v =
        (complexConstants (𝟙 ComplexBase) c) •
          (pullbackPair x b).apply ⊤ u v
    rw [map_smul, LinearMap.smul_apply]

@[simp]
theorem fiberPair_apply {Y : Scheme} {E F G : OModule Y}
    (b : SheafBilinearMap E F G) (x : ComplexBase ⟶ Y)
    (u : Fiber E x) (v : Fiber F x) :
    fiberPair b x u v = (pullbackPair x b).apply ⊤ u v := rfl

/-- The precise Hom-fiber comparison used in the nondegeneracy bridge.
It is constructed from sheaf evaluation, not from a chosen vector-space
isomorphism or an assumed perfect fiber pairing. -/
def homFiberEvaluation {Y : Scheme} (E F : OModule Y) (x : ComplexBase ⟶ Y) :
    Fiber (internalHomSheaf E F) x →ₗ[ℂ] Fiber E x →ₗ[ℂ] Fiber F x :=
  fiberPair (sheafEvaluationPair E F) x

/-- The diagram relating sheaf currying and fiber evaluation commutes
on all fiber vectors. This is the required normalization statement. -/
theorem homFiberEvaluation_curry {Y : Scheme} {Z E F : OModule Y}
    (b : SheafBilinearMap Z E F) (x : ComplexBase ⟶ Y)
    (u : Fiber Z x) (v : Fiber E x) :
    homFiberEvaluation E F x (fiberMap (currySheaf (tensorLift b)) x u) v =
      fiberPair b x u v := by
  have hp := pullbackPair_precompose x (sheafEvaluationPair E F)
    (currySheaf (tensorLift b)) (𝟙 E)
  rw [sheafEvaluationPair_curry b] at hp
  have h := congrArg (fun q : SheafBilinearMap (pullbackModule x Z)
    (pullbackModule x E) (pullbackModule x F) => q.apply ⊤ u v) hp
  change (pullbackPair x b).apply ⊤ u v =
    (pullbackPair x (sheafEvaluationPair E F)).apply ⊤
      (((Scheme.Modules.pullback x).map (currySheaf (tensorLift b))).app ⊤ u)
      (((Scheme.Modules.pullback x).map (𝟙 E)).app ⊤ v) at h
  rw [CategoryTheory.Functor.map_id] at h
  exact h.symm

/-- Pullback and sections preserve an already established sheaf isomorphism. -/
theorem fiberMap_bijective_of_iso {Y : Scheme} {E F : OModule Y}
    (h : E ⟶ F) [IsIso h] (x : ComplexBase ⟶ Y) :
    Function.Bijective (fiberMap h x) :=
  onCSections_bijective_of_iso (𝟙 ComplexBase)
    ((Scheme.Modules.pullback x).mapIso (asIso h))

/-! ### Consequences for the original contact distribution and kernel -/

section ActualContact

variable {n : ℕ} (X : ContactFanoManifold n) (x : ComplexPoint X.variety)

/-- The intrinsic bracket convention survives pullback to the complex point. -/
theorem leviFiberValue_skew
    (u v : Fiber X.contact.sequence.distribution.sheaf x.map) :
    leviFiberValue X x u v = -leviFiberValue X x v u :=
  pullbackPair_skew x.map (intrinsicLeviPair X.contact.sequence)
    (intrinsicLeviPair_skew X.contact.sequence) ⊤ u v

/-- Complex characteristic zero upgrades fiber skew symmetry to alternation. -/
theorem leviFiberValue_alternating
    (u : Fiber X.contact.sequence.distribution.sheaf x.map) :
    leviFiberValue X x u u = 0 := by
  have hsum : leviFiberValue X x u u + leviFiberValue X x u u = 0 := by
    conv_lhs => lhs; rw [leviFiberValue_skew X x u u]
    exact neg_add_cancel _
  have htwo : (2 : ℂ) • leviFiberValue X x u u = 0 := by
    simpa only [show (2 : ℂ) = 1 + 1 by norm_num, add_smul, one_smul] using hsum
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

theorem contactLevi_skew (a b : contactPlane X x) :
    SuitablePairAlgebra.contactLevi X x a b =
      -SuitablePairAlgebra.contactLevi X x b a :=
  leviFiberValue_skew X x
    ((SuitablePairAlgebra.distributionContactEquiv X x).symm a)
    ((SuitablePairAlgebra.distributionContactEquiv X x).symm b)

/-- This discharges the earlier explicit fiber-alternation hypothesis. -/
theorem contactLevi_alternating (a : contactPlane X x) :
    SuitablePairAlgebra.contactLevi X x a a = 0 :=
  SuitablePairAlgebra.contactLevi_alternating_of_fiber X x
    (leviFiberValue_alternating X x) a

/-- The fiber of the actual bracket-defined sheaf currying morphism. -/
def leviCurryingFiber :
    Fiber X.contact.sequence.distribution.sheaf x.map →ₗ[ℂ]
      Fiber (internalHomSheaf X.contact.sequence.distribution.sheaf
        X.contact.sequence.line.sheaf) x.map :=
  fiberMap (currySheaf (intrinsicLeviMorphism X.contact.sequence)) x.map

/-- Contact perfectness already gives bijectivity before the Hom-fiber
comparison. No local frame or nondegeneracy assumption is needed here. -/
theorem leviCurryingFiber_bijective : Function.Bijective (leviCurryingFiber X x) := by
  letI : IsIso (currySheaf (intrinsicLeviMorphism X.contact.sequence)) :=
    X.contact.nondegenerate
  exact fiberMap_bijective_of_iso
    (currySheaf (intrinsicLeviMorphism X.contact.sequence)) x.map

theorem leviCurryingFiber_evaluate
    (u v : Fiber X.contact.sequence.distribution.sheaf x.map) :
    homFiberEvaluation X.contact.sequence.distribution.sheaf
      X.contact.sequence.line.sheaf x.map (leviCurryingFiber X x u) v =
        leviFiberValue X x u v :=
  homFiberEvaluation_curry (intrinsicLeviPair X.contact.sequence) x.map u v

/-- The exact remaining generic bridge is injectivity of evaluation on
the pulled-back internal Hom. Supplying it, for this locally free source,
proves nondegeneracy of the actual Levi fiber without additional geometric
or symplectic input. This theorem does not assert that bridge. -/
theorem leviFiberValue_leftNondegenerate_of_homFiberEvaluation_injective
    (hcompare : Function.Injective
      (homFiberEvaluation X.contact.sequence.distribution.sheaf
        X.contact.sequence.line.sheaf x.map))
    (u : Fiber X.contact.sequence.distribution.sheaf x.map)
    (hu : ∀ v, leviFiberValue X x u v = 0) : u = 0 := by
  apply (leviCurryingFiber_bijective X x).1
  apply hcompare
  ext v
  rw [leviCurryingFiber_evaluate, hu]
  simp only [map_zero, LinearMap.zero_apply]

theorem contactLevi_leftNondegenerate_of_homFiberEvaluation_injective
    (hcompare : Function.Injective
      (homFiberEvaluation X.contact.sequence.distribution.sheaf
        X.contact.sequence.line.sheaf x.map)) :
    ∀ a : contactPlane X x,
      (∀ b, SuitablePairAlgebra.contactLevi X x a b = 0) → a = 0 :=
  SuitablePairAlgebra.contactLevi_leftNondegenerate_of_fiber X x
    (leviFiberValue_leftNondegenerate_of_homFiberEvaluation_injective X x hcompare)

theorem contactLevi_rightNondegenerate_of_homFiberEvaluation_injective
    (hcompare : Function.Injective
      (homFiberEvaluation X.contact.sequence.distribution.sheaf
        X.contact.sequence.line.sheaf x.map))
    (b : contactPlane X x)
    (hb : ∀ a, SuitablePairAlgebra.contactLevi X x a b = 0) : b = 0 := by
  apply contactLevi_leftNondegenerate_of_homFiberEvaluation_injective X x hcompare b
  intro a
  rw [contactLevi_skew, hb, neg_zero]

end ActualContact

/-! ### Scalarization and finite coordinates of the same contact form -/

section Coordinates

variable {n : ℕ} (X : ContactFanoManifold n) (x : ComplexPoint X.variety)

/-- A pointwise frame exists because the original contact-line fiber has
dimension one. This is not a claim of a chosen Zariski-local trivialization. -/
def lineFiberFrame : Fiber X.contact.sequence.line.sheaf x.map ≃ₗ[ℂ] ℂ := by
  letI := fiber_finite X.contact.sequence.line x.map
  apply LinearEquiv.ofFinrankEq
    (Fiber X.contact.sequence.line.sheaf x.map) ℂ
  simpa only [CommSemiring.finrank_self] using
    fiber_dimension X.contact.sequence.line x.map

/-- A basis of the actual contact kernel is transported from the fiber of
the distribution through its actual inclusion, keeping the rank `2*n`. -/
def contactFiberBasis : Module.Basis (Fin (2 * n)) ℂ (contactPlane X x) := by
  letI := fiber_finite X.contact.sequence.distribution x.map
  exact (Module.finBasisOfFinrankEq ℂ
    (Fiber X.contact.sequence.distribution.sheaf x.map)
      (fiber_dimension X.contact.sequence.distribution x.map)).map
        (SuitablePairAlgebra.distributionContactEquiv X x)

/-- Positivity of the contact rank makes nondegeneracy imply that the
actual form is nonzero, the hypothesis needed by the spanning argument. -/
theorem contactLevi_ne_zero_of_homFiberEvaluation_injective
    (hcompare : Function.Injective
      (homFiberEvaluation X.contact.sequence.distribution.sheaf
        X.contact.sequence.line.sheaf x.map)) :
    SuitablePairAlgebra.contactLevi X x ≠ 0 := by
  let i : Fin (2 * n) := ⟨0, by have hn := X.positiveContactDimension; omega⟩
  intro hzero
  apply (contactFiberBasis X x).ne_zero i
  apply contactLevi_leftNondegenerate_of_homFiberEvaluation_injective X x hcompare
  intro b
  rw [hzero, LinearMap.zero_apply, LinearMap.zero_apply]

variable (frame : Fiber X.contact.sequence.line.sheaf x.map ≃ₗ[ℂ] ℂ)

/-- The scalar form is the original line-valued contact form expressed in
the specified pointwise line frame. -/
def scalarLevi : contactPlane X x →ₗ[ℂ] contactPlane X x →ₗ[ℂ] ℂ :=
  (SuitablePairAlgebra.contactLevi X x).compr₂ frame.toLinearMap

@[simp]
theorem scalarLevi_apply (a b : contactPlane X x) :
    scalarLevi X x frame a b = frame (SuitablePairAlgebra.contactLevi X x a b) := rfl

theorem scalarLevi_skew (a b : contactPlane X x) :
    scalarLevi X x frame a b = -scalarLevi X x frame b a := by
  change frame (SuitablePairAlgebra.contactLevi X x a b) =
    -frame (SuitablePairAlgebra.contactLevi X x b a)
  rw [contactLevi_skew, map_neg]

@[simp]
theorem scalarLevi_alternating (a : contactPlane X x) :
    scalarLevi X x frame a a = 0 := by
  rw [scalarLevi_apply, contactLevi_alternating, map_zero]

theorem scalarLevi_eq_zero_iff (a b : contactPlane X x) :
    scalarLevi X x frame a b = 0 ↔ SuitablePairAlgebra.contactLevi X x a b = 0 :=
  frame.map_eq_zero_iff

/-- Nonvanishing agrees exactly with the original witness-based test. -/
theorem scalarLevi_ne_zero_iff (a b : contactPlane X x) :
    scalarLevi X x frame a b ≠ 0 ↔
      NonzeroLeviPair X x (a : TangentFiber X.variety x) (b : TangentFiber X.variety x) :=
  (not_congr (scalarLevi_eq_zero_iff X x frame a b)).trans
    (SuitablePairAlgebra.nonzeroLeviPair_iff_contactLevi X x a b).symm

theorem scalarLevi_leftNondegenerate_of_homFiberEvaluation_injective
    (hcompare : Function.Injective
      (homFiberEvaluation X.contact.sequence.distribution.sheaf
        X.contact.sequence.line.sheaf x.map))
    (a : contactPlane X x) (ha : ∀ b, scalarLevi X x frame a b = 0) : a = 0 := by
  apply contactLevi_leftNondegenerate_of_homFiberEvaluation_injective X x hcompare a
  intro b
  exact (scalarLevi_eq_zero_iff X x frame a b).mp (ha b)

variable {ι : Type*} [Fintype ι] (B : Module.Basis ι ℂ (contactPlane X x))

/-- Coefficients are values of the actual scalarized Levi form on the
specified contact-plane basis, so the cone function has a fixed sign. -/
def leviMatrix (i j : ι) : ℂ := scalarLevi X x frame (B i) (B j)

theorem leviMatrix_skew (i j : ι) :
    leviMatrix X x frame B i j = -leviMatrix X x frame B j i :=
  scalarLevi_skew X x frame (B i) (B j)

@[simp]
theorem leviMatrix_diagonal (i : ι) : leviMatrix X x frame B i i = 0 :=
  scalarLevi_alternating X x frame (B i)

/-- Direct finite basis expansion fixes the coordinate convention of
`ConePairing.pairing`: first vector, matrix coefficient, second vector. -/
theorem pairing_leviMatrix (a b : contactPlane X x) :
    ConePairing.pairing (leviMatrix X x frame B)
      (fun i => B.repr a i) (fun i => B.repr b i) = scalarLevi X x frame a b := by
  classical
  have hexpand : scalarLevi X x frame
      (∑ i, B.repr a i • B i) (∑ j, B.repr b j • B j) =
        scalarLevi X x frame a b := by
    rw [B.sum_repr a, B.sum_repr b]
  calc
    ConePairing.pairing (leviMatrix X x frame B)
        (fun i => B.repr a i) (fun i => B.repr b i) =
      ∑ i, ∑ j, (B.repr a i) * (B.repr b j) *
        scalarLevi X x frame (B i) (B j) := by
      unfold ConePairing.pairing leviMatrix
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      simp only [Algebra.algebraMap_self, RingHom.id_apply]
      ring
    _ = scalarLevi X x frame
        (∑ i, B.repr a i • B i) (∑ j, B.repr b j • B j) := by
      simp only [map_sum, LinearMap.sum_apply, map_smul,
        LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = scalarLevi X x frame a b := hexpand

/-- The regular cone cross-pairing vanishes exactly where the intrinsic
line-valued form vanishes on the represented contact vectors. -/
theorem pairing_leviMatrix_eq_zero_iff (a b : contactPlane X x) :
    ConePairing.pairing (leviMatrix X x frame B)
      (fun i => B.repr a i) (fun i => B.repr b i) = 0 ↔
        SuitablePairAlgebra.contactLevi X x a b = 0 := by
  rw [pairing_leviMatrix]
  exact scalarLevi_eq_zero_iff X x frame a b

theorem pairing_leviMatrix_ne_zero_iff (a b : contactPlane X x) :
    ConePairing.pairing (leviMatrix X x frame B)
      (fun i => B.repr a i) (fun i => B.repr b i) ≠ 0 ↔
        NonzeroLeviPair X x (a : TangentFiber X.variety x) (b : TangentFiber X.variety x) := by
  rw [pairing_leviMatrix]
  exact scalarLevi_ne_zero_iff X x frame a b

/-- The same normalization for arbitrary coordinate vectors, expressed
through the inverse of the actual contact-plane coordinate equivalence. -/
theorem pairing_leviMatrix_coordinates (a b : ι → ℂ) :
    ConePairing.pairing (leviMatrix X x frame B) a b =
      scalarLevi X x frame (B.equivFun.symm a) (B.equivFun.symm b) := by
  have h := pairing_leviMatrix X x frame B (B.equivFun.symm a) (B.equivFun.symm b)
  change ConePairing.pairing (leviMatrix X x frame B)
    (B.equivFun (B.equivFun.symm a)) (B.equivFun (B.equivFun.symm b)) = _ at h
  simpa only [LinearEquiv.apply_symm_apply] using h

theorem pairing_leviMatrix_coordinates_ne_zero_iff (a b : ι → ℂ) :
    ConePairing.pairing (leviMatrix X x frame B) a b ≠ 0 ↔
      NonzeroLeviPair X x
        ((B.equivFun.symm a : contactPlane X x) : TangentFiber X.variety x)
        ((B.equivFun.symm b : contactPlane X x) : TangentFiber X.variety x) := by
  rw [pairing_leviMatrix_coordinates]
  exact scalarLevi_ne_zero_iff X x frame (B.equivFun.symm a) (B.equivFun.symm b)

end Coordinates

/-! ### Frame independence of the cone nonorthogonality condition -/

section ChangeFrame

variable {n : ℕ} (X : ContactFanoManifold n) (x : ComplexPoint X.variety)
variable (frame frame' : Fiber X.contact.sequence.line.sheaf x.map ≃ₗ[ℂ] ℂ)

/-- The transition factor between actual pointwise frames of the line. -/
def lineFrameRatio : ℂ := frame' (frame.symm 1)

theorem lineFrameRatio_ne_zero : lineFrameRatio X x frame frame' ≠ 0 := by
  intro h
  have hzero : frame.symm 1 = 0 := frame'.injective (h.trans (map_zero frame').symm)
  have hscalar := congrArg frame hzero
  have : (1 : ℂ) = 0 := by simpa only [frame.apply_symm_apply, map_zero] using hscalar
  exact one_ne_zero this

/-- A one-dimensional frame transition multiplies every value by the
same nonzero scalar; it cannot alter the nonorthogonal cone locus. -/
theorem lineFrame_change (v : Fiber X.contact.sequence.line.sheaf x.map) :
    frame' v = lineFrameRatio X x frame frame' * frame v := by
  have hv : v = frame v • frame.symm 1 := by
    apply frame.injective
    simp only [map_smul, frame.apply_symm_apply, smul_eq_mul, mul_one]
  calc
    frame' v = frame' (frame v • frame.symm 1) := congrArg frame' hv
    _ = frame v * frame' (frame.symm 1) := by rw [map_smul, smul_eq_mul]
    _ = lineFrameRatio X x frame frame' * frame v := mul_comm _ _

theorem scalarLevi_change_frame (a b : contactPlane X x) :
    scalarLevi X x frame' a b =
      lineFrameRatio X x frame frame' * scalarLevi X x frame a b :=
  lineFrame_change X x frame frame' (SuitablePairAlgebra.contactLevi X x a b)

theorem scalarLevi_frame_independent_nonzero (a b : contactPlane X x) :
    scalarLevi X x frame a b ≠ 0 ↔ scalarLevi X x frame' a b ≠ 0 :=
  (scalarLevi_ne_zero_iff X x frame a b).trans
    (scalarLevi_ne_zero_iff X x frame' a b).symm

theorem leviMatrix_change_frame {ι : Type*} [Fintype ι]
    (B : Module.Basis ι ℂ (contactPlane X x)) (i j : ι) :
    leviMatrix X x frame' B i j =
      lineFrameRatio X x frame frame' * leviMatrix X x frame B i j :=
  scalarLevi_change_frame X x frame frame' (B i) (B j)

end ChangeFrame

end LeBrunSalamon.Construction.Lines.LeviFiberGeometry

end
/- END RELOCATED POSITIVE-NODE DEPENDENCY: LSLeviFiber -/

/- BEGIN RELOCATED POSITIVE-NODE DEPENDENCY: LSPositiveQuotient -/
/-!
## Fixed-value sections factor through a subbundle with trivial quotient

SOURCE: `lines:suitable-pair`, the final paragraph: a section vanishing at
the marked point has zero projection to the trivial quotient of the
positive part. This is proved for actual sheaf maps and actual evaluation
maps. It does not assume that the projected section is constant or zero.

The positive subbundle and its exact sequence still have to be constructed
from the splitting in `lines:positive`. The result below proves the needed
section argument for any supplied actual exact sequence with trivial
quotient, then specializes it to the existing curve/node evaluation.

No new admitted input is introduced. The existing standard bundle-fiber
dimension and exactness inputs remain dependencies.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseEighteen LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentySix LeBrunSalamon.PhaseTwentySeven
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction
open scoped BigOperators

namespace LeBrunSalamon.Construction.Lines.PositiveQuotient

/-! ### Naturality for the already defined fiber evaluation -/

theorem evaluateSection_naturality {X : Scheme} (sX : X ⟶ ComplexBase)
    {E F : OModule X} (q : E ⟶ F) (x : ComplexBase ⟶ X)
    (hx : x ≫ sX = 𝟙 ComplexBase) (s : CSections sX E) :
    evaluateSection sX F x hx (onCSections sX q s) =
      fiberMap q x (evaluateSection sX E x hx s) := by
  have hs : sectionFromValue (onCSections sX q s) = sectionFromValue s ≫ q := by
    apply (sectionValue_bijective F).injective
    rw [sectionFromValue_spec, sectionValue_comp, sectionFromValue_spec]
    rfl
  change sectionValue (pullSection x (sectionFromValue (onCSections sX q s))) =
    ((Scheme.Modules.pullback x).map q).app ⊤
      (sectionValue (pullSection x (sectionFromValue s)))
  rw [hs, pullSection_naturality, sectionValue_comp]

/-- If evaluation is faithful on every summand, it is faithful on the
actual finite coproduct. The coordinate maps are the sheaf projections. -/
theorem evaluateSection_coproduct_injective {X : Scheme}
    (sX : X ⟶ ComplexBase) {I : Type} [Fintype I] (E : I → OModule X)
    (x : ComplexBase ⟶ X) (hx : x ≫ sX = 𝟙 ComplexBase)
    (h : ∀ i, Function.Injective (evaluateSection sX (E i) x hx)) :
    Function.Injective (evaluateSection sX (∐ E) x hx) := by
  classical
  intro s t hst
  apply (DirectSumSections.cSectionsCoproductEquiv sX E).injective
  funext i
  apply h i
  change evaluateSection sX (E i) x hx (onCSections sX (Sigma.π E i) s) =
    evaluateSection sX (E i) x hx (onCSections sX (Sigma.π E i) t)
  rw [evaluateSection_naturality, evaluateSection_naturality, hst]

theorem evaluateSection_injective_of_iso {X : Scheme}
    (sX : X ⟶ ComplexBase) {E F : OModule X} (e : E ≅ F)
    (x : ComplexBase ⟶ X) (hx : x ≫ sX = 𝟙 ComplexBase)
    (hF : Function.Injective (evaluateSection sX F x hx)) :
    Function.Injective (evaluateSection sX E x hx) := by
  intro s t hst
  apply (onCSections_bijective_of_iso sX e).1
  apply hF
  rw [evaluateSection_naturality, evaluateSection_naturality, hst]

/-! ### The trivial quotient has faithful evaluation at one point -/

/-- Evaluation on O(0) is bijective: its already proved surjectivity and
the actual one-dimensional section/fiber spaces give injectivity. -/
theorem zeroTwistEvaluation_bijective (P : ProjectiveLineOverC)
    (p x : ProjectiveLinePoint P) :
    Function.Bijective (evaluateSection P.structureMap
      (projectiveTwist P p 0).sheaf x.map x.overC) := by
  letI := fiber_finite (projectiveTwist P p 0) x.map
  have hdim : Module.finrank ℂ
      (CSections P.structureMap (projectiveTwist P p 0).sheaf) =
        Module.finrank ℂ (Fiber (projectiveTwist P p 0).sheaf x.map) := by
    rw [P1TwistSections.cSections_finrank, fiber_dimension]
    norm_num
  have hsurj := (P1TwistEvaluation.suppliedEvaluation_surjective_iff P p 0 P x).mpr
    (show (0 : ℤ) ≤ 0 from le_rfl)
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj, hsurj⟩

/-- A specified trivial sheaf on the original projective line. The
definition retains the actual finite coproduct of degree-zero twists. -/
def trivialQuotientSheaf (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    (I : Type) [Fintype I] : OModule ProjectiveLine :=
  ∐ (fun _ : I => (projectiveTwist P p 0).sheaf)

theorem trivialQuotientEvaluation_injective (P : ProjectiveLineOverC)
    (p x : ProjectiveLinePoint P) {I : Type} [Fintype I] :
    Function.Injective (evaluateSection P.structureMap
      (trivialQuotientSheaf P p I) x.map x.overC) :=
  evaluateSection_coproduct_injective P.structureMap
    (fun _ : I => (projectiveTwist P p 0).sheaf) x.map x.overC
    (fun _ => (zeroTwistEvaluation_bijective P p x).1)

/-- A section of an actually trivialized quotient is determined by its
value at the marked point. This includes the rank-zero quotient. -/
theorem evaluation_injective_of_trivial_quotient (P : ProjectiveLineOverC)
    (p x : ProjectiveLinePoint P) {Q : OModule ProjectiveLine}
    {I : Type} [Fintype I] (e : Q ≅ trivialQuotientSheaf P p I) :
    Function.Injective (evaluateSection P.structureMap Q x.map x.overC) :=
  evaluateSection_injective_of_iso P.structureMap e x.map x.overC
    (trivialQuotientEvaluation_injective P p x)

/-! ### The paper's projection and unique section-lifting argument -/

/-- The projection is proved zero from its actual value at the node.
Neither constancy nor vanishing of this projected section is a premise. -/
theorem projection_eq_zero_of_node_zero (P : ProjectiveLineOverC)
    (p x : ProjectiveLinePoint P) {E Q : OModule ProjectiveLine}
    (q : E ⟶ Q) {I : Type} [Fintype I]
    (e : Q ≅ trivialQuotientSheaf P p I)
    (s : CSections P.structureMap E)
    (hs : evaluateSection P.structureMap E x.map x.overC s = 0) :
    onCSections P.structureMap q s = 0 := by
  apply evaluation_injective_of_trivial_quotient P p x e
  rw [evaluateSection_naturality, hs, map_zero, map_zero]

/-- Left exactness supplies a unique genuine section of the subbundle.
No surjectivity on global sections of the short exact sequence is used. -/
theorem nodeZeroSection_lifts (P : ProjectiveLineOverC)
    (p x : ProjectiveLinePoint P) {W E Q : OModule ProjectiveLine}
    (i : W ⟶ E) (q : E ⟶ Q) (hz : i ≫ q = 0)
    (hex : (ShortComplex.mk i q hz).ShortExact)
    {I : Type} [Fintype I] (e : Q ≅ trivialQuotientSheaf P p I)
    (s : CSections P.structureMap E)
    (hs : evaluateSection P.structureMap E x.map x.overC s = 0) :
    ∃! t : CSections P.structureMap W, onCSections P.structureMap i t = s := by
  have hq := projection_eq_zero_of_node_zero P p x q e s hs
  exact ExtensionGluing.existsUnique_kernelSection i q hz hex ⊤ s hq

/-- For vector bundles the fiber inclusion is injective. Therefore the
unique lifted section also vanishes at the fixed node, as needed before
differentiating its coefficients in a positive-subbundle frame. -/
theorem nodeZeroSection_lifts_nodeZero (P : ProjectiveLineOverC)
    (p x : ProjectiveLinePoint P) {a b c : ℕ}
    (W : AlgebraicVectorBundle ProjectiveLine a)
    (E : AlgebraicVectorBundle ProjectiveLine b)
    (Q : AlgebraicVectorBundle ProjectiveLine c)
    (i : W.sheaf ⟶ E.sheaf) (q : E.sheaf ⟶ Q.sheaf) (hz : i ≫ q = 0)
    (hex : (ShortComplex.mk i q hz).ShortExact)
    {I : Type} [Fintype I] (e : Q.sheaf ≅ trivialQuotientSheaf P p I)
    (s : CSections P.structureMap E.sheaf)
    (hs : evaluateSection P.structureMap E.sheaf x.map x.overC s = 0) :
    ∃! t : CSections P.structureMap W.sheaf,
      onCSections P.structureMap i t = s ∧
        evaluateSection P.structureMap W.sheaf x.map x.overC t = 0 := by
  obtain ⟨t, ht, huniq⟩ := nodeZeroSection_lifts P p x i q hz hex e s hs
  have hinj := (vectorBundle_fiber_exact W E Q i q hz hex x.map).1
  have ht0 : evaluateSection P.structureMap W.sheaf x.map x.overC t = 0 := by
    apply hinj
    rw [← evaluateSection_naturality, ht, hs, map_zero]
  exact ⟨t, ⟨ht, ht0⟩, fun u hu => huniq u hu.1⟩

/-- Kernel spaces of the existing node-evaluation maps, without replacing
them by a model tangent space. -/
def nodeZeroSections (P : ProjectiveLineOverC) (x : ProjectiveLinePoint P)
    (E : OModule ProjectiveLine) :=
  LinearMap.ker (evaluateSection P.structureMap E x.map x.overC)

def mapNodeZeroSections (P : ProjectiveLineOverC) (x : ProjectiveLinePoint P)
    {W E : OModule ProjectiveLine} (i : W ⟶ E) :
    nodeZeroSections P x W →ₗ[ℂ] nodeZeroSections P x E where
  toFun t := ⟨onCSections P.structureMap i t.val, by
    change evaluateSection P.structureMap E x.map x.overC
      (onCSections P.structureMap i t.val) = 0
    rw [evaluateSection_naturality, t.property, map_zero]⟩
  map_add' := by intro s t; apply Subtype.ext; exact map_add _ _ _
  map_smul' := by intro z t; apply Subtype.ext; exact map_smul _ _ _

/-- The subbundle inclusion induces a bijection on fixed-node section
spaces when its quotient is actually trivial. -/
theorem mapNodeZeroSections_bijective (P : ProjectiveLineOverC)
    (p x : ProjectiveLinePoint P) {a b c : ℕ}
    (W : AlgebraicVectorBundle ProjectiveLine a)
    (E : AlgebraicVectorBundle ProjectiveLine b)
    (Q : AlgebraicVectorBundle ProjectiveLine c)
    (i : W.sheaf ⟶ E.sheaf) (q : E.sheaf ⟶ Q.sheaf) (hz : i ≫ q = 0)
    (hex : (ShortComplex.mk i q hz).ShortExact)
    {I : Type} [Fintype I] (e : Q.sheaf ≅ trivialQuotientSheaf P p I) :
    Function.Bijective (mapNodeZeroSections P x i) := by
  constructor
  · intro s t hst
    letI : Mono i := hex.mono_f
    apply Subtype.ext
    exact ExtensionGluing.sectionMap_injective i ⊤ (congrArg Subtype.val hst)
  · intro s
    obtain ⟨t, ht, _⟩ := nodeZeroSection_lifts_nodeZero P p x W E Q i q hz hex e s.val s.property
    exact ⟨⟨t, ht.2⟩, Subtype.ext ht.1⟩

/-! ### Specialization to the original contact line and node evaluation -/

theorem fixedNodeCurveSection_lifts {n : ℕ} {X : ContactFanoManifold n}
    (f : FreeLine X) (x : ComplexPoint X.variety)
    (hx : marking.map ≫ f.curve.map = x.map)
    {a c : ℕ} (W : AlgebraicVectorBundle ProjectiveLine a)
    (Q : AlgebraicVectorBundle ProjectiveLine c)
    (i : W.sheaf ⟶ pullbackModule f.curve.map (tangentSheaf X.variety.structureMap))
    (q : pullbackModule f.curve.map (tangentSheaf X.variety.structureMap) ⟶ Q.sheaf)
    (hz : i ≫ q = 0) (hex : (ShortComplex.mk i q hz).ShortExact)
    {I : Type} [Fintype I] (e : Q.sheaf ≅ trivialQuotientSheaf P marking I)
    (s : CSections P.structureMap
      (pullbackModule f.curve.map (tangentSheaf X.variety.structureMap)))
    (hs : nodeEvaluation f x hx s = 0) :
    ∃! t : CSections P.structureMap W.sheaf,
      onCSections P.structureMap i t = s ∧
        evaluateSection P.structureMap W.sheaf marking.map marking.overC t = 0 := by
  have heval : evaluateSection P.structureMap
      (pullbackModule f.curve.map (tangentSheaf X.variety.structureMap))
      marking.map marking.overC s = 0 := by
    apply (fiberComposition_bijective f.curve.map marking.map x.map hx
      (tangentSheaf X.variety.structureMap)).1
    change nodeEvaluation f x hx s = _
    rw [hs, map_zero]
  exact nodeZeroSection_lifts_nodeZero P marking marking W
    (PhaseThirtyFive.pullbackBundle f.curve.map (intrinsicTangentBundle X.variety)) Q i q hz hex e s heval

end LeBrunSalamon.Construction.Lines.PositiveQuotient

end
/- END RELOCATED POSITIVE-NODE DEPENDENCY: LSPositiveQuotient -/

/- BEGIN RELOCATED POSITIVE-NODE DEPENDENCY: LSPositiveSplit -/
/-!
Actual positive and degree-zero summands of a nonnegative splitting on P1.

This file constructs all four sheaf maps, their splitting identities, the
short exact sequence, and the actual trivialization of the quotient.  The
construction uses any supplied splitting isomorphism.  For an actual free
line, such an isomorphism is obtained from the existing standard
Birkhoff--Grothendieck input and the already proved global-generation
criterion.  No special generic contact-line splitting is assumed.

Manuscript locator: lines.tex, lines:positive.  No new admitted theorem.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseEighteen LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentySix LeBrunSalamon.PhaseTwentySeven
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction
open LeBrunSalamon.P1Charts LeBrunSalamon.P1TwistFrames

namespace LeBrunSalamon.Construction.Lines.PositivePart

abbrev PositiveIndex {r : ℕ} (a : TangentSplittingProfile r) :=
  {j : Fin r // 0 < a.degree j}

abbrev ZeroIndex {r : ℕ} (a : TangentSplittingProfile r) :=
  {j : Fin r // a.degree j = 0}

/-- The actual sum of the strictly positive line-bundle summands. -/
def positiveSheaf (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {r : ℕ} (a : TangentSplittingProfile r) : OModule ProjectiveLine :=
  ∐ (fun j : PositiveIndex a => (projectiveTwist P p (a.degree j.val)).sheaf)

/-- The actual sum of the degree-zero summands, before trivializing each one. -/
def zeroSheaf (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {r : ℕ} (a : TangentSplittingProfile r) : OModule ProjectiveLine :=
  ∐ (fun j : ZeroIndex a => (projectiveTwist P p (a.degree j.val)).sheaf)

def splitPositiveInclusion (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {r : ℕ} (a : TangentSplittingProfile r) :
    positiveSheaf P p a ⟶ splitSheaf P p a :=
  Sigma.desc (fun j : PositiveIndex a =>
    Sigma.ι (fun i : Fin r => (projectiveTwist P p (a.degree i)).sheaf) j.val)

def splitZeroInclusion (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {r : ℕ} (a : TangentSplittingProfile r) :
    zeroSheaf P p a ⟶ splitSheaf P p a :=
  Sigma.desc (fun j : ZeroIndex a =>
    Sigma.ι (fun i : Fin r => (projectiveTwist P p (a.degree i)).sheaf) j.val)

def splitPositiveProjection (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {r : ℕ} (a : TangentSplittingProfile r) :
    splitSheaf P p a ⟶ positiveSheaf P p a :=
  Sigma.desc (fun i : Fin r =>
    if h : 0 < a.degree i then
      Sigma.ι (fun j : PositiveIndex a => (projectiveTwist P p (a.degree j.val)).sheaf)
        ⟨i, h⟩
    else 0)

def splitZeroProjection (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {r : ℕ} (a : TangentSplittingProfile r) :
    splitSheaf P p a ⟶ zeroSheaf P p a :=
  Sigma.desc (fun i : Fin r =>
    if h : a.degree i = 0 then
      Sigma.ι (fun j : ZeroIndex a => (projectiveTwist P p (a.degree j.val)).sheaf)
        ⟨i, h⟩
    else 0)

@[reassoc (attr := simp)]
theorem summand_splitPositiveInclusion (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) {r : ℕ} (a : TangentSplittingProfile r)
    (j : PositiveIndex a) :
    Sigma.ι (fun i : PositiveIndex a => (projectiveTwist P p (a.degree i.val)).sheaf) j ≫
        splitPositiveInclusion P p a =
      Sigma.ι (fun i : Fin r => (projectiveTwist P p (a.degree i)).sheaf) j.val := by
  simp [splitPositiveInclusion]

@[reassoc (attr := simp)]
theorem summand_splitZeroInclusion (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) {r : ℕ} (a : TangentSplittingProfile r)
    (j : ZeroIndex a) :
    Sigma.ι (fun i : ZeroIndex a => (projectiveTwist P p (a.degree i.val)).sheaf) j ≫
        splitZeroInclusion P p a =
      Sigma.ι (fun i : Fin r => (projectiveTwist P p (a.degree i)).sheaf) j.val := by
  simp [splitZeroInclusion]

@[reassoc (attr := simp)]
theorem positive_summand_splitPositiveProjection (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) {r : ℕ} (a : TangentSplittingProfile r)
    (j : PositiveIndex a) :
    Sigma.ι (fun i : Fin r => (projectiveTwist P p (a.degree i)).sheaf) j.val ≫
        splitPositiveProjection P p a =
      Sigma.ι (fun i : PositiveIndex a => (projectiveTwist P p (a.degree i.val)).sheaf) j := by
  simp [splitPositiveProjection, j.property]

@[reassoc (attr := simp)]
theorem zero_summand_splitZeroProjection (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) {r : ℕ} (a : TangentSplittingProfile r)
    (j : ZeroIndex a) :
    Sigma.ι (fun i : Fin r => (projectiveTwist P p (a.degree i)).sheaf) j.val ≫
        splitZeroProjection P p a =
      Sigma.ι (fun i : ZeroIndex a => (projectiveTwist P p (a.degree i.val)).sheaf) j := by
  simp [splitZeroProjection, j.property]

@[reassoc (attr := simp)]
theorem positive_summand_splitZeroProjection (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) {r : ℕ} (a : TangentSplittingProfile r)
    (j : PositiveIndex a) :
    Sigma.ι (fun i : Fin r => (projectiveTwist P p (a.degree i)).sheaf) j.val ≫
        splitZeroProjection P p a = 0 := by
  simp [splitZeroProjection, ne_of_gt j.property]

@[reassoc (attr := simp)]
theorem zero_summand_splitPositiveProjection (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) {r : ℕ} (a : TangentSplittingProfile r)
    (j : ZeroIndex a) :
    Sigma.ι (fun i : Fin r => (projectiveTwist P p (a.degree i)).sheaf) j.val ≫
        splitPositiveProjection P p a = 0 := by
  simp [splitPositiveProjection, j.property]

@[reassoc (attr := simp)]
theorem splitPositive_retraction (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) {r : ℕ} (a : TangentSplittingProfile r) :
    splitPositiveInclusion P p a ≫ splitPositiveProjection P p a =
      𝟙 (positiveSheaf P p a) := by
  apply Sigma.hom_ext
  intro j
  simp
  exact (Category.comp_id _).symm

@[reassoc (attr := simp)]
theorem splitZero_retraction (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) {r : ℕ} (a : TangentSplittingProfile r) :
    splitZeroInclusion P p a ≫ splitZeroProjection P p a =
      𝟙 (zeroSheaf P p a) := by
  apply Sigma.hom_ext
  intro j
  simp
  exact (Category.comp_id _).symm

@[reassoc (attr := simp)]
theorem splitPositive_zero (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) {r : ℕ} (a : TangentSplittingProfile r) :
    splitPositiveInclusion P p a ≫ splitZeroProjection P p a = 0 := by
  apply Sigma.hom_ext
  intro j
  simp

@[reassoc (attr := simp)]
theorem splitZero_positive (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) {r : ℕ} (a : TangentSplittingProfile r) :
    splitZeroInclusion P p a ≫ splitPositiveProjection P p a = 0 := by
  apply Sigma.hom_ext
  intro j
  simp

/-- Nonnegativity says the two constructed summand sets exhaust the bundle. -/
theorem splitDecomposition (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) {r : ℕ} (a : TangentSplittingProfile r)
    (ha : a.IsFree) :
    splitPositiveProjection P p a ≫ splitPositiveInclusion P p a +
        splitZeroProjection P p a ≫ splitZeroInclusion P p a =
      𝟙 (splitSheaf P p a) := by
  apply Sigma.hom_ext
  intro j
  by_cases hj : 0 < a.degree j
  · have hz : a.degree j ≠ 0 := ne_of_gt hj
    simp [Preadditive.comp_add, splitPositiveProjection, splitZeroProjection,
      hj, hz, Category.assoc]
    exact (Category.comp_id _).symm
  · have hz : a.degree j = 0 := by
      have hnonneg := ha j
      omega
    simp [Preadditive.comp_add, splitPositiveProjection, splitZeroProjection,
      hj, hz, Category.assoc]
    exact (Category.comp_id _).symm

/-! ### Transport the actual maps through the supplied splitting -/

def positiveInclusion (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {r : ℕ} (a : TangentSplittingProfile r) {E : OModule ProjectiveLine}
    (e : E ≅ splitSheaf P p a) : positiveSheaf P p a ⟶ E :=
  splitPositiveInclusion P p a ≫ e.inv

def positiveRetraction (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {r : ℕ} (a : TangentSplittingProfile r) {E : OModule ProjectiveLine}
    (e : E ≅ splitSheaf P p a) : E ⟶ positiveSheaf P p a :=
  e.hom ≫ splitPositiveProjection P p a

def zeroProjection (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {r : ℕ} (a : TangentSplittingProfile r) {E : OModule ProjectiveLine}
    (e : E ≅ splitSheaf P p a) : E ⟶ zeroSheaf P p a :=
  e.hom ≫ splitZeroProjection P p a

def zeroSection (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {r : ℕ} (a : TangentSplittingProfile r) {E : OModule ProjectiveLine}
    (e : E ≅ splitSheaf P p a) : zeroSheaf P p a ⟶ E :=
  splitZeroInclusion P p a ≫ e.inv

@[reassoc (attr := simp)]
theorem positive_retraction (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) {r : ℕ} (a : TangentSplittingProfile r)
    {E : OModule ProjectiveLine} (e : E ≅ splitSheaf P p a) :
    positiveInclusion P p a e ≫ positiveRetraction P p a e =
      𝟙 (positiveSheaf P p a) := by
  simp [positiveInclusion, positiveRetraction, Category.assoc]

@[reassoc (attr := simp)]
theorem zero_section (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) {r : ℕ} (a : TangentSplittingProfile r)
    {E : OModule ProjectiveLine} (e : E ≅ splitSheaf P p a) :
    zeroSection P p a e ≫ zeroProjection P p a e = 𝟙 (zeroSheaf P p a) := by
  simp [zeroSection, zeroProjection, Category.assoc]

@[reassoc (attr := simp)]
theorem positive_zero (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) {r : ℕ} (a : TangentSplittingProfile r)
    {E : OModule ProjectiveLine} (e : E ≅ splitSheaf P p a) :
    positiveInclusion P p a e ≫ zeroProjection P p a e = 0 := by
  simp [positiveInclusion, zeroProjection, Category.assoc]

@[reassoc (attr := simp)]
theorem zero_positive (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) {r : ℕ} (a : TangentSplittingProfile r)
    {E : OModule ProjectiveLine} (e : E ≅ splitSheaf P p a) :
    zeroSection P p a e ≫ positiveRetraction P p a e = 0 := by
  simp [zeroSection, positiveRetraction, Category.assoc]

theorem split_total (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) {r : ℕ} (a : TangentSplittingProfile r)
    {E : OModule ProjectiveLine} (e : E ≅ splitSheaf P p a) (ha : a.IsFree) :
    positiveRetraction P p a e ≫ positiveInclusion P p a e +
        zeroProjection P p a e ≫ zeroSection P p a e = 𝟙 E := by
  calc
    _ = e.hom ≫
        (splitPositiveProjection P p a ≫ splitPositiveInclusion P p a +
          splitZeroProjection P p a ≫ splitZeroInclusion P p a) ≫ e.inv := by
      simp [positiveRetraction, positiveInclusion, zeroProjection, zeroSection,
        Preadditive.comp_add, Preadditive.add_comp, Category.assoc]
    _ = 𝟙 E := by rw [splitDecomposition P p a ha]; simp

/-- A genuine categorical splitting, including the actual retraction and section. -/
def actualSplitting (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {r : ℕ} (a : TangentSplittingProfile r) {E : OModule ProjectiveLine}
    (e : E ≅ splitSheaf P p a) (ha : a.IsFree) :
    (ShortComplex.mk (positiveInclusion P p a e) (zeroProjection P p a e)
      (positive_zero P p a e)).Splitting where
  r := positiveRetraction P p a e
  s := zeroSection P p a e
  f_r := positive_retraction P p a e
  s_g := zero_section P p a e
  id := split_total P p a e ha

theorem splitShortExact (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {r : ℕ} (a : TangentSplittingProfile r) {E : OModule ProjectiveLine}
    (e : E ≅ splitSheaf P p a) (ha : a.IsFree) :
    (ShortComplex.mk (positiveInclusion P p a e) (zeroProjection P p a e)
      (positive_zero P p a e)).ShortExact :=
  (actualSplitting P p a e ha).shortExact

/-- The quotient is an actual finite sum of O(0), with its explicit sheaf isomorphism. -/
def zeroTrivialization (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {r : ℕ} (a : TangentSplittingProfile r) :
    zeroSheaf P p a ≅ PositiveQuotient.trivialQuotientSheaf P p (ZeroIndex a) :=
  Sigma.mapIso (fun j : ZeroIndex a =>
    eqToIso (congrArg (fun d : ℤ => (projectiveTwist P p d).sheaf) j.property))

/-! ### Actual finite-rank vector bundles on the existing two-chart cover -/

theorem twistCoproduct_rank (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {I : Type} [Fintype I] (d : I → ℤ) :
    IsLocallyFreeOfRank (∐ (fun i : I => (projectiveTwist P p (d i)).sheaf))
      (Fintype.card I) := by
  classical
  apply SheafTensor.rank_of_free_cover _ (Fintype.card I) chartOpen
    ((Opens.coversTop_iff ProjectiveLine chartOpen).mpr chartOpen_cover)
  intro j
  exact SheafTensor.freeReindexIso _ (Fintype.equivFin I).symm ≪≫
    DirectSumGeometry.coproductFrame
      (fun i : I => (projectiveTwist P p (d i)).sheaf) (chartOpen j)
      (fun i => twistOverFrame P p (d i) j)

def positiveBundle (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {r : ℕ} (a : TangentSplittingProfile r) :
    AlgebraicVectorBundle ProjectiveLine (Fintype.card (PositiveIndex a)) :=
  ⟨positiveSheaf P p a, twistCoproduct_rank P p (fun j : PositiveIndex a => a.degree j.val)⟩

def zeroBundle (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {r : ℕ} (a : TangentSplittingProfile r) :
    AlgebraicVectorBundle ProjectiveLine (Fintype.card (ZeroIndex a)) :=
  ⟨zeroSheaf P p a, twistCoproduct_rank P p (fun j : ZeroIndex a => a.degree j.val)⟩

/-! ### Nonnegative splittings for actual globally generated bundles and free lines -/

/-- Birkhoff--Grothendieck supplies the splitting; global generation forces
all degrees to be nonnegative by the previously proved actual sheaf criterion. -/
theorem nonnegativeSplitting_exists (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) {r : ℕ} (E : AlgebraicVectorBundle ProjectiveLine r)
    (hE : IsGloballyGenerated E.sheaf) :
    ∃ a : TangentSplittingProfile r,
      a.IsFree ∧ Nonempty (E.sheaf ≅ splitSheaf P p a) := by
  obtain ⟨a, ha⟩ := birkhoffGrothendieck P p E
  exact ⟨a, (splitBundle_globallyGenerated_iff P p E a ha).mp hE, ha⟩

def freeLineBundle {n : ℕ} {X : ContactFanoManifold n} (f : FreeLine X) :
    AlgebraicVectorBundle ProjectiveLine (2 * n + 1) :=
  PhaseThirtyFive.pullbackBundle f.curve.map (intrinsicTangentBundle X.variety)

theorem freeLine_nonnegativeSplitting_exists {n : ℕ} {X : ContactFanoManifold n}
    (f : FreeLine X) :
    ∃ a : TangentSplittingProfile (2 * n + 1),
      a.IsFree ∧ Nonempty ((freeLineBundle f).sheaf ≅ splitSheaf P marking a) := by
  exact nonnegativeSplitting_exists P marking (freeLineBundle f) f.free

def freeLineProfile {n : ℕ} {X : ContactFanoManifold n} (f : FreeLine X) :
    TangentSplittingProfile (2 * n + 1) :=
  Classical.choose (freeLine_nonnegativeSplitting_exists f)

theorem freeLineProfile_nonnegative {n : ℕ} {X : ContactFanoManifold n}
    (f : FreeLine X) : (freeLineProfile f).IsFree :=
  (Classical.choose_spec (freeLine_nonnegativeSplitting_exists f)).1

def freeLineSplitting {n : ℕ} {X : ContactFanoManifold n} (f : FreeLine X) :
    (freeLineBundle f).sheaf ≅ splitSheaf P marking (freeLineProfile f) :=
  (Classical.choose_spec (freeLine_nonnegativeSplitting_exists f)).2.some

def freeLinePositiveBundle {n : ℕ} {X : ContactFanoManifold n} (f : FreeLine X) :
    AlgebraicVectorBundle ProjectiveLine (Fintype.card (PositiveIndex (freeLineProfile f))) :=
  positiveBundle P marking (freeLineProfile f)

def freeLineZeroBundle {n : ℕ} {X : ContactFanoManifold n} (f : FreeLine X) :
    AlgebraicVectorBundle ProjectiveLine (Fintype.card (ZeroIndex (freeLineProfile f))) :=
  zeroBundle P marking (freeLineProfile f)

def freeLinePositiveInclusion {n : ℕ} {X : ContactFanoManifold n} (f : FreeLine X) :
    (freeLinePositiveBundle f).sheaf ⟶ (freeLineBundle f).sheaf :=
  positiveInclusion P marking (freeLineProfile f) (freeLineSplitting f)

def freeLineZeroProjection {n : ℕ} {X : ContactFanoManifold n} (f : FreeLine X) :
    (freeLineBundle f).sheaf ⟶ (freeLineZeroBundle f).sheaf :=
  zeroProjection P marking (freeLineProfile f) (freeLineSplitting f)

theorem freeLine_positive_zero {n : ℕ} {X : ContactFanoManifold n} (f : FreeLine X) :
    freeLinePositiveInclusion f ≫ freeLineZeroProjection f = 0 :=
  positive_zero P marking (freeLineProfile f) (freeLineSplitting f)

/-- The positive-part short exact sequence for the actual pulled-back tangent
bundle of every free line, with no prescribed generic splitting profile. -/
theorem freeLine_shortExact {n : ℕ} {X : ContactFanoManifold n} (f : FreeLine X) :
    (ShortComplex.mk (freeLinePositiveInclusion f) (freeLineZeroProjection f)
      (freeLine_positive_zero f)).ShortExact :=
  splitShortExact P marking (freeLineProfile f) (freeLineSplitting f)
    (freeLineProfile_nonnegative f)

def freeLineZeroTrivialization {n : ℕ} {X : ContactFanoManifold n} (f : FreeLine X) :
    (freeLineZeroBundle f).sheaf ≅
      PositiveQuotient.trivialQuotientSheaf P marking (ZeroIndex (freeLineProfile f)) :=
  zeroTrivialization P marking (freeLineProfile f)

end LeBrunSalamon.Construction.Lines.PositivePart

end
/- END RELOCATED POSITIVE-NODE DEPENDENCY: LSPositiveSplit -/

/- BEGIN RELOCATED POSITIVE-NODE DEPENDENCY: LSPositiveHom -/
/-!
## Positive twists cannot map to a trivial quotient

SOURCE: the first paragraph of `lines:positive`. The positive summands
of a nonnegative splitting cannot have a nonzero component in the zero
quotient of another splitting. This is the sheaf-level argument used to
show that the positive subbundle is intrinsic.

The degree-vanishing theorem already proved for actual projective twists
is extended to finite coproducts and to different choices of the point
used to define the twists. The comparison lemmas below use actual sheaf
maps and split identities. They do not assume a canonical positive part.
No admitted input is introduced.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseEighteen LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentySix LeBrunSalamon.PhaseTwentySeven
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction
open scoped BigOperators

namespace LeBrunSalamon.Construction.Lines.PositiveHom

/-- Different choices of the point defining the twists do not change
the degree obstruction to a nonzero actual sheaf morphism. -/
theorem hom_twist_eq_zero_of_lt (P : ProjectiveLineOverC)
    (p q : ProjectiveLinePoint P) (a b : ℤ) (h : b < a)
    (f : (projectiveTwist P p a).sheaf ⟶ (projectiveTwist P q b).sheaf) :
    f = 0 := by
  obtain ⟨e⟩ := projectiveTwist_independent P q p b
  apply (cancel_mono e.hom).mp
  simpa only [zero_comp] using descendingDegree_noHom P p a b h (f ≫ e.hom)

/-- A map to a finite actual coproduct is zero if all of its components
are zero. The empty coproduct is included. -/
theorem hom_coproduct_eq_zero {X : Scheme} {A : OModule X}
    {J : Type} [Fintype J] (F : J → OModule X) (f : A ⟶ ∐ F)
    (h : ∀ j, f ≫ (show (∐ F) ⟶ F j from by classical exact Sigma.π F j) = 0) : f = 0 := by
  classical
  calc
    f = f ≫ (∑ j, Sigma.π F j ≫ Sigma.ι F j) := by
      rw [DirectSumGeometry.coproduct_total, Category.comp_id]
    _ = ∑ j, (f ≫ Sigma.π F j) ≫ Sigma.ι F j := by
      simp only [Preadditive.comp_sum, Category.assoc]
    _ = 0 := by simp [h]

/-- Every actual map from a finite sum of strictly positive twists to
an actual trivial finite sum is zero. Source and target twist conventions
may use different points; no common splitting is assumed. -/
theorem hom_positiveCoproduct_trivial_eq_zero
    (P : ProjectiveLineOverC) (p q : ProjectiveLinePoint P)
    {I J : Type} [Fintype I] [Fintype J]
    (d : I → ℤ) (hd : ∀ i, 0 < d i)
    (f : (∐ (fun i => (projectiveTwist P p (d i)).sheaf)) ⟶
      PositiveQuotient.trivialQuotientSheaf P q J) : f = 0 := by
  classical
  apply Sigma.hom_ext
  intro i
  rw [comp_zero]
  apply hom_coproduct_eq_zero
    (fun _ : J => (projectiveTwist P q 0).sheaf)
  intro j
  exact hom_twist_eq_zero_of_lt P p q (d i) 0 (hd i) _

/-- The vanishing statement is unchanged by an actual quotient
trivialization; it applies directly to the quotient of a splitting. -/
theorem hom_positiveCoproduct_eq_zero_of_trivialization
    (P : ProjectiveLineOverC) (p q : ProjectiveLinePoint P)
    {I J : Type} [Fintype I] [Fintype J]
    (d : I → ℤ) (hd : ∀ i, 0 < d i)
    {Q : OModule ProjectiveLine}
    (eQ : Q ≅ PositiveQuotient.trivialQuotientSheaf P q J)
    (f : (∐ (fun i => (projectiveTwist P p (d i)).sheaf)) ⟶ Q) :
    f = 0 := by
  apply (cancel_mono eQ.hom).mp
  simpa only [zero_comp] using
    hom_positiveCoproduct_trivial_eq_zero P p q d hd (f ≫ eQ.hom)

/-! ### Explicit comparisons of split inclusions -/

/-- Vanishing of the quotient component forces factorization through
the supplied actual split inclusion. -/
theorem factor_through_split_inclusion {X : Scheme}
    {A W E Q : OModule X} (f : A ⟶ E)
    (i : W ⟶ E) (r : E ⟶ W) (q : E ⟶ Q) (s : Q ⟶ E)
    (htotal : r ≫ i + q ≫ s = 𝟙 E) (hfq : f ≫ q = 0) :
    (f ≫ r) ≫ i = f := by
  calc
    (f ≫ r) ≫ i = f ≫ (r ≫ i + q ≫ s) := by
      simp only [Preadditive.comp_add, ← Category.assoc, hfq, zero_comp, add_zero]
    _ = f := by rw [htotal, Category.comp_id]

/-- The factor through a split inclusion is unique. This fixes the
comparison as a map over the original ambient sheaf. -/
theorem factor_through_split_inclusion_unique {X : Scheme}
    {A W E : OModule X} (f : A ⟶ E) (i : W ⟶ E) (r : E ⟶ W)
    (hir : i ≫ r = 𝟙 W) (g : A ⟶ W) (hg : g ≫ i = f) :
    g = f ≫ r := by
  calc
    g = (g ≫ i) ≫ r := by rw [Category.assoc, hir, Category.comp_id]
    _ = f ≫ r := by rw [hg]

/-- Two split inclusions which factor through one another have a
specified isomorphism commuting with their maps to the ambient sheaf.
The inverse identities use the retractions, not an assumed equality
of abstract isomorphism classes. -/
def splitInclusionIso {X : Scheme} {W₁ W₂ E : OModule X}
    (i₁ : W₁ ⟶ E) (r₁ : E ⟶ W₁) (i₂ : W₂ ⟶ E) (r₂ : E ⟶ W₂)
    (hr₁ : i₁ ≫ r₁ = 𝟙 W₁) (hr₂ : i₂ ≫ r₂ = 𝟙 W₂)
    (h₁₂ : (i₁ ≫ r₂) ≫ i₂ = i₁) (h₂₁ : (i₂ ≫ r₁) ≫ i₁ = i₂) :
    W₁ ≅ W₂ where
  hom := i₁ ≫ r₂
  inv := i₂ ≫ r₁
  hom_inv_id := by
    calc
      (i₁ ≫ r₂) ≫ (i₂ ≫ r₁) = ((i₁ ≫ r₂) ≫ i₂) ≫ r₁ := by
        simp only [Category.assoc]
      _ = i₁ ≫ r₁ := by rw [h₁₂]
      _ = 𝟙 W₁ := hr₁
  inv_hom_id := by
    calc
      (i₂ ≫ r₁) ≫ (i₁ ≫ r₂) = ((i₂ ≫ r₁) ≫ i₁) ≫ r₂ := by
        simp only [Category.assoc]
      _ = i₂ ≫ r₂ := by rw [h₂₁]
      _ = 𝟙 W₂ := hr₂

end LeBrunSalamon.Construction.Lines.PositiveHom

end
/- END RELOCATED POSITIVE-NODE DEPENDENCY: LSPositiveHom -/

/- BEGIN RELOCATED POSITIVE-NODE DEPENDENCY: LSPositiveNodeImage -/
/-!
## The positive summand has exactly the existing positive node image

SOURCE: `lines:positive` and the last paragraph of `lines:suitable-pair`.
For the supplied actual nonnegative splitting, the fiber image of its
positive-summand inclusion is exactly the node values of actual sections
vanishing at the other marked point. In particular, the original
`Lines.positiveNodeSpace` is identified, not replaced by a model subspace.

The forward inclusion uses the actual zero-quotient section argument.
The reverse inclusion prescribes an arbitrary positive-fiber value at the
node and zero at the other point using actual two-point evaluation.
All sheaf maps, pullbacks, global sections and fibers are the existing ones.
No new admitted input is introduced. This file does not prove horizontal
containment or isotropy of the positive part.

Requires the `PositivePart` construction of the actual positive/zero
summands, their split exact sequence and the actual zero trivialization.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseEighteen LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentySix LeBrunSalamon.PhaseTwentySeven
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction
open scoped BigOperators

namespace LeBrunSalamon.Construction.Lines.PositiveNodeImage

/-! ### Actual two-point evaluation for a finite positive sum -/

/-- The section/fiber-value comparison for any actual sheaf. The original
restriction Hom spaces are related to the fiber-value spaces by the
already normalized unit-pullback isomorphisms, rather than replaced. -/
theorem suppliedPairEvaluation_surjective_iff_restriction
    (Q : ProjectiveLineOverC) (E : OModule ProjectiveLine)
    (x y : ProjectiveLinePoint Q) :
    Function.Surjective (P1TwistEvaluation.suppliedPairEvaluation Q E x y) ↔
      Function.Surjective (twoPointBundleEvaluation Q x y E) := by
  have h := PointBaseTransport.surjective_iff_of_coordinates
    (twoPointBundleEvaluation Q x y E)
    (P1TwistEvaluation.suppliedPairEvaluation Q E x y)
    (sectionAddEquiv E).toEquiv
    ((FrameEvaluation.restrictedSectionValueEquiv x.map E).toEquiv.prodCongr
      (FrameEvaluation.restrictedSectionValueEquiv y.map E).toEquiv) (by
      intro s
      change (sectionValue (pullSection x.map s), sectionValue (pullSection y.map s)) =
        (sectionValue (pullSection x.map (sectionFromValue (sectionValue s))),
          sectionValue (pullSection y.map (sectionFromValue (sectionValue s))))
      rw [sectionFromValue_sectionValue])
  exact h.symm

/-- Pair evaluation of the actual finite coproduct is surjective exactly
when each actual summand's pair evaluation is surjective. This includes
an empty positive index set. -/
theorem suppliedPairEvaluation_coproduct_surjective_iff
    (Q : ProjectiveLineOverC) {I : Type} [Fintype I]
    (E : I → OModule ProjectiveLine) (x y : ProjectiveLinePoint Q) :
    Function.Surjective (P1TwistEvaluation.suppliedPairEvaluation Q (∐ E) x y) ↔
      ∀ i, Function.Surjective (P1TwistEvaluation.suppliedPairEvaluation Q (E i) x y) := by
  rw [suppliedPairEvaluation_surjective_iff_restriction,
    DirectSumEvaluation.twoPointBundleEvaluation_coproduct_surjective_iff]
  exact forall_congr' (fun i =>
    (suppliedPairEvaluation_surjective_iff_restriction Q (E i) x y).symm)

/-- Positive integer degrees suffice for arbitrary distinct points.
The source is the actual positive coproduct from the supplied profile;
the conclusion is about its actual pulled-back fibers. -/
theorem positiveSheaf_pairEvaluation_surjective
    (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {r : ℕ} (a : TangentSplittingProfile r)
    (Q : ProjectiveLineOverC) (x y : ProjectiveLinePoint Q) (hxy : x.map ≠ y.map) :
    Function.Surjective (P1TwistEvaluation.suppliedPairEvaluation Q
      (PositivePart.positiveSheaf P p a) x y) := by
  classical
  change Function.Surjective (P1TwistEvaluation.suppliedPairEvaluation Q
    (∐ (fun j : PositivePart.PositiveIndex a =>
      (projectiveTwist P p (a.degree j.val)).sheaf)) x y)
  apply (suppliedPairEvaluation_coproduct_surjective_iff Q _ x y).mpr
  intro j
  apply (P1TwistEvaluation.suppliedPairEvaluation_surjective_iff
    P p (a.degree j.val) Q x y hxy).mpr
  have hj : 0 < a.degree j.val := j.property
  omega

/-! ### An exact sequence and actual pair evaluation identify the image -/

/-- If the quotient is actually trivial and the subobject has surjective
actual pair evaluation, the node image of sections vanishing at the other
point is exactly the fiber image of the original inclusion.

This does not assume fiber exactness or surjectivity of global sections
for the whole short exact sequence. Left exactness and the proved
trivial-quotient evaluation lemma supply the needed section factorization. -/
theorem vanishingSectionNodeImage_eq_range
    (P : ProjectiveLineOverC) (p x y : ProjectiveLinePoint P)
    {W E Q : OModule ProjectiveLine}
    (i : W ⟶ E) (q : E ⟶ Q) (hz : i ≫ q = 0)
    (hex : (ShortComplex.mk i q hz).ShortExact)
    {I : Type} [Fintype I]
    (eQ : Q ≅ PositiveQuotient.trivialQuotientSheaf P p I)
    (hpair : Function.Surjective
      (P1TwistEvaluation.suppliedPairEvaluation P W x y)) :
    Submodule.map (evaluateSection P.structureMap E x.map x.overC)
      (LinearMap.ker (evaluateSection P.structureMap E y.map y.overC)) =
        LinearMap.range (fiberMap i x.map) := by
  ext v
  constructor
  · intro hv
    obtain ⟨s, hs, hvalue⟩ := Submodule.mem_map.mp hv
    have hs0 : evaluateSection P.structureMap E y.map y.overC s = 0 :=
      LinearMap.mem_ker.mp hs
    obtain ⟨t, ht, _⟩ := PositiveQuotient.nodeZeroSection_lifts
      P p y i q hz hex eQ s hs0
    apply LinearMap.mem_range.mpr
    refine ⟨evaluateSection P.structureMap W x.map x.overC t, ?_⟩
    rw [← PositiveQuotient.evaluateSection_naturality, ht]
    exact hvalue
  · intro hv
    obtain ⟨w, hw⟩ := LinearMap.mem_range.mp hv
    obtain ⟨s, hs⟩ := hpair (w, 0)
    have hx := congrArg Prod.fst hs
    have hy := congrArg Prod.snd hs
    change evaluateSection P.structureMap W x.map x.overC s = w at hx
    change evaluateSection P.structureMap W y.map y.overC s = 0 at hy
    apply Submodule.mem_map.mpr
    refine ⟨onCSections P.structureMap i s, ?_, ?_⟩
    · apply LinearMap.mem_ker.mpr
      rw [PositiveQuotient.evaluateSection_naturality, hy, map_zero]
    · rw [PositiveQuotient.evaluateSection_naturality, hx]
      exact hw

/-- Instantiation for the constructed positive/zero sequence of any
supplied nonnegative splitting. No generic contact-line splitting is used. -/
theorem positiveInclusion_nodeImage
    (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {r : ℕ} (a : TangentSplittingProfile r) (ha : a.IsFree)
    {E : OModule ProjectiveLine} (e : E ≅ splitSheaf P p a)
    (x y : ProjectiveLinePoint P) (hxy : x.map ≠ y.map) :
    Submodule.map (evaluateSection P.structureMap E x.map x.overC)
      (LinearMap.ker (evaluateSection P.structureMap E y.map y.overC)) =
        LinearMap.range (fiberMap (PositivePart.positiveInclusion P p a e) x.map) := by
  exact vanishingSectionNodeImage_eq_range P p x y
    (PositivePart.positiveInclusion P p a e)
    (PositivePart.zeroProjection P p a e)
    (PositivePart.positive_zero P p a e)
    (PositivePart.splitShortExact P p a e ha)
    (PositivePart.zeroTrivialization P p a)
    (positiveSheaf_pairEvaluation_surjective P p a P x y hxy)

/-- The actual node image is independent of which distinct outer point
is held fixed. Its common value is the positive-summand fiber image. -/
theorem positiveNodeImage_independent_outerPoint
    (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {r : ℕ} (a : TangentSplittingProfile r) (ha : a.IsFree)
    {E : OModule ProjectiveLine} (e : E ≅ splitSheaf P p a)
    (x y z : ProjectiveLinePoint P) (hxy : x.map ≠ y.map) (hxz : x.map ≠ z.map) :
    Submodule.map (evaluateSection P.structureMap E x.map x.overC)
      (LinearMap.ker (evaluateSection P.structureMap E y.map y.overC)) =
      Submodule.map (evaluateSection P.structureMap E x.map x.overC)
        (LinearMap.ker (evaluateSection P.structureMap E z.map z.overC)) := by
  rw [positiveInclusion_nodeImage P p a ha e x y hxy,
    positiveInclusion_nodeImage P p a ha e x z hxz]

/-! ### The existing contact-line positiveNodeSpace, with its original maps -/

/-- The original `positiveNodeSpace` is the image of the actual positive
summand fiber under its actual inclusion and the original composition
pullback isomorphism identifying f(0) with the specified point of X. -/
theorem positiveNodeSpace_eq_positiveFiberImage
    {n : ℕ} {X : ContactFanoManifold n}
    (f : FreeLine X) (x : ComplexPoint X.variety)
    (hx : marking.map ≫ f.curve.map = x.map)
    {r : ℕ} (a : TangentSplittingProfile r) (ha : a.IsFree)
    (e : pullbackModule f.curve.map (tangentSheaf X.variety.structureMap) ≅
      splitSheaf P marking a) :
    positiveNodeSpace f x hx =
      LinearMap.range
        ((fiberComposition f.curve.map marking.map x.map hx
          (tangentSheaf X.variety.structureMap)).comp
            (fiberMap (PositivePart.positiveInclusion P marking a e) marking.map)) := by
  unfold positiveNodeSpace nodeEvaluation
  rw [Submodule.map_comp]
  rw [positiveInclusion_nodeImage P marking a ha e marking infinity zero_ne_infinity]
  exact (LinearMap.range_comp _ _).symm

/-- Pointwise membership retains actual positive-fiber witnesses. This is
the form used when transporting the Hom-velocity calculation into the
original node space. -/
theorem mem_positiveNodeSpace_iff_positiveFiber
    {n : ℕ} {X : ContactFanoManifold n}
    (f : FreeLine X) (x : ComplexPoint X.variety)
    (hx : marking.map ≫ f.curve.map = x.map)
    {r : ℕ} (a : TangentSplittingProfile r) (ha : a.IsFree)
    (e : pullbackModule f.curve.map (tangentSheaf X.variety.structureMap) ≅
      splitSheaf P marking a)
    (v : TangentFiber X.variety x) :
    v ∈ positiveNodeSpace f x hx ↔
      ∃ w : Fiber (PositivePart.positiveSheaf P marking a) marking.map,
        fiberComposition f.curve.map marking.map x.map hx
          (tangentSheaf X.variety.structureMap)
          (fiberMap (PositivePart.positiveInclusion P marking a e) marking.map w) = v := by
  rw [positiveNodeSpace_eq_positiveFiberImage f x hx a ha e]
  exact LinearMap.mem_range

/-- Integration endpoint for the actual free line: its existing freeness
supplies a nonnegative splitting, and the constructed positive bundle has
exactly the original positive node image. No splitting or node-space
identification is an extra premise of this theorem. -/
theorem freeLine_positiveNodeSpace_eq_fiberImage
    {n : ℕ} {X : ContactFanoManifold n}
    (f : FreeLine X) (x : ComplexPoint X.variety)
    (hx : marking.map ≫ f.curve.map = x.map) :
    positiveNodeSpace f x hx =
      LinearMap.range
        ((fiberComposition f.curve.map marking.map x.map hx
          (tangentSheaf X.variety.structureMap)).comp
            (fiberMap (PositivePart.freeLinePositiveInclusion f) marking.map)) := by
  exact positiveNodeSpace_eq_positiveFiberImage f x hx
    (PositivePart.freeLineProfile f) (PositivePart.freeLineProfile_nonnegative f)
    (PositivePart.freeLineSplitting f)

end LeBrunSalamon.Construction.Lines.PositiveNodeImage

end
/- END RELOCATED POSITIVE-NODE DEPENDENCY: LSPositiveNodeImage -/

/- BEGIN RELOCATED POSITIVE-NODE DEPENDENCY: LSContactGeneration -/
/-!
## The global-generation contradiction in lines:positive

These are proofs for actual module sheaves and actual sheaf morphisms.
A globally generated sheaf cannot map nontrivially to a sheaf with no
global sections. A section of an actual quotient makes its actual kernel
a retract, so the kernel is globally generated. For a degree-one quotient
on P1, every nonzero component from a strictly positive twist is an
isomorphism and supplies precisely such a section. Consequently a
non-globally-generated kernel forces the entire positive part into it.

This is the contradiction in the manuscript, not an admitted horizontal
conclusion. The contact-specific construction of the nonzero negative map
is handled separately. No new admitted input is introduced here.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseEighteen LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentySix LeBrunSalamon.PhaseTwentySeven
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction

namespace LeBrunSalamon.Construction.Lines.ContactGeneration

/-- Actual generating sections detect every map out of a globally
generated sheaf, even when the index set is infinite. -/
theorem hom_eq_zero_of_globallyGenerated {X : Scheme} {E F : OModule X}
    (hE : IsGloballyGenerated E)
    (hF : ∀ s : AlgebraicSection F, s = 0) (f : E ⟶ F) : f = 0 := by
  obtain ⟨G⟩ := hE
  apply (cancel_epi G.π).mp
  rw [comp_zero]
  apply Cofan.IsColimit.hom_ext (SheafOfModules.isColimitFreeCofan G.I)
  intro i
  simpa only [SheafOfModules.freeCofan_inj, Category.assoc, comp_zero] using
    hF (SheafOfModules.ιFree i ≫ G.π ≫ f)

/-- A concrete nonzero map into a sheaf without global sections obstructs
global generation. No surjectivity of the map is required. -/
theorem not_globallyGenerated_of_nonzero_hom {X : Scheme} {E F : OModule X}
    (hF : ∀ s : AlgebraicSection F, s = 0) (f : E ⟶ F) (hf : f ≠ 0) :
    ¬ IsGloballyGenerated E := by
  intro hE
  exact hf (hom_eq_zero_of_globallyGenerated hE hF f)

/-- The negative target in the manuscript is the original projective twist. -/
theorem not_globallyGenerated_of_negative_twist_map
    (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {E : OModule ProjectiveLine} (d : ℤ) (hd : d < 0)
    (f : E ⟶ (projectiveTwist P p d).sheaf) (hf : f ≠ 0) :
    ¬ IsGloballyGenerated E :=
  not_globallyGenerated_of_nonzero_hom
    (fun s => negativeTwist_noSections P p d hd s) f hf

/-- The actual retraction carries an actual generating family to the
retract. This does not use an abstract isomorphism class of a summand. -/
theorem globallyGenerated_of_retraction {X : Scheme} {E K : OModule X}
    (hE : IsGloballyGenerated E) (i : K ⟶ E) (r : E ⟶ K)
    (hir : i ≫ r = 𝟙 K) : IsGloballyGenerated K := by
  letI : Epi r := epi_of_epi_fac hir
  obtain ⟨G⟩ := hE
  exact ⟨G.ofEpi r⟩

/-- Splitting the actual quotient makes the actual kernel a globally
generated retract of the globally generated middle sheaf. -/
theorem kernel_globallyGenerated_of_quotient_section {X : Scheme}
    {K E L : OModule X} (i : K ⟶ E) (q : E ⟶ L)
    (hz : i ≫ q = 0) (hex : (ShortComplex.mk i q hz).ShortExact)
    (hE : IsGloballyGenerated E) (s : L ⟶ E) (hs : s ≫ q = 𝟙 L) :
    IsGloballyGenerated K := by
  let splitting := ShortComplex.Splitting.ofExactOfSection
    (ShortComplex.mk i q hz) hex.exact s hs hex.mono_f
  exact globallyGenerated_of_retraction hE i splitting.r splitting.f_r

/-- A nonzero map from a positive twist to a degree-one line has degree
one and is an isomorphism. Both conclusions are proved by degree vanishing. -/
theorem positive_twist_map_degree_one_isIso
    (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    (a : ℤ) (ha : 0 < a) {L : OModule ProjectiveLine}
    (eL : L ≅ (projectiveTwist P p 1).sheaf)
    (f : (projectiveTwist P p a).sheaf ⟶ L) (hf : f ≠ 0) :
    a = 1 ∧ IsIso f := by
  have hn : f ≫ eL.hom ≠ 0 := by
    intro hz
    apply hf
    apply (cancel_mono eL.hom).mp
    simpa only [zero_comp] using hz
  have ha1 : a = 1 := by
    by_contra hne
    have hgt : (1 : ℤ) < a := by omega
    exact hn (descendingDegree_noHom P p a 1 hgt (f ≫ eL.hom))
  refine ⟨ha1, ?_⟩
  subst a
  letI : IsIso (f ≫ eL.hom) :=
    equalDegree_nonzeroHom_isIso P p 1 (f ≫ eL.hom) hn
  exact IsIso.of_isIso_comp_right f eL.hom

/-- The positive-to-degree-one component cannot be nonzero if the
actual quotient's kernel is not globally generated. -/
theorem positive_twist_component_eq_zero
    (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {K E L : OModule ProjectiveLine} (i : K ⟶ E) (q : E ⟶ L)
    (hz : i ≫ q = 0) (hex : (ShortComplex.mk i q hz).ShortExact)
    (eL : L ≅ (projectiveTwist P p 1).sheaf)
    (hE : IsGloballyGenerated E) (hK : ¬ IsGloballyGenerated K)
    (a : ℤ) (ha : 0 < a) (u : (projectiveTwist P p a).sheaf ⟶ E) :
    u ≫ q = 0 := by
  by_contra hnonzero
  letI : IsIso (u ≫ q) :=
    (positive_twist_map_degree_one_isIso P p a ha eL (u ≫ q) hnonzero).2
  let s : L ⟶ E := (asIso (u ≫ q)).inv ≫ u
  have hs : s ≫ q = 𝟙 L := by
    simpa only [s, asIso_hom, Category.assoc] using (asIso (u ≫ q)).inv_hom_id
  exact hK (kernel_globallyGenerated_of_quotient_section i q hz hex hE s hs)

/-- Applying the component argument to the actual positive inclusion
proves horizontal vanishing once the actual kernel's failure of global
generation has been established. No generic splitting profile is assumed. -/
theorem positiveInclusion_quotient_eq_zero
    (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {r : ℕ} (a : TangentSplittingProfile r)
    {K E L : OModule ProjectiveLine} (e : E ≅ splitSheaf P p a)
    (i : K ⟶ E) (q : E ⟶ L)
    (hz : i ≫ q = 0) (hex : (ShortComplex.mk i q hz).ShortExact)
    (eL : L ≅ (projectiveTwist P p 1).sheaf)
    (hE : IsGloballyGenerated E) (hK : ¬ IsGloballyGenerated K) :
    PositivePart.positiveInclusion P p a e ≫ q = 0 := by
  apply Sigma.hom_ext
  intro j
  rw [comp_zero, ← Category.assoc]
  exact positive_twist_component_eq_zero P p i q hz hex eL hE hK
    (a.degree j.val) j.property
    (Sigma.ι (fun k : PositivePart.PositiveIndex a =>
      (projectiveTwist P p (a.degree k.val)).sheaf) j ≫
        PositivePart.positiveInclusion P p a e)

end LeBrunSalamon.Construction.Lines.ContactGeneration

end
/- END RELOCATED POSITIVE-NODE DEPENDENCY: LSContactGeneration -/

/- BEGIN RELOCATED POSITIVE-NODE DEPENDENCY: LSContactStandardInputs -/
/-!
## Precisely delimited standard bundle inputs for the contact-positive argument

PB-01: pullback preserves a short exact sequence of vector bundles because
the quotient is locally free and hence flat. This does not assume the
pullback morphism is flat. The maps are the original pullback functor maps.
Sources: Stacks Project tags 00HL (tensoring with flat quotient), 0098
(natural stalk formula for pullback), 01C6 (finite locally free sheaves).

HF-01: evaluation gives an injective canonical map from the fiber of
Hom(E,F) to Hom of the fibers when E is finite locally free. Locally this
is the finite free scalar-extension identity, compatible with evaluation.
F is arbitrary; no contact geometry is assumed. Sources: Stacks 01CM
(internal Hom and evaluation), 0FNU (duals), 0098, by finite-free local reduction.

The pullback statement is now proved from the exact generic local-splitting
input. Hom-fiber injectivity is now proved from the actual canonical Hom
comparison and global evaluation on Spec C. They contain no conclusion about contact lines, positivity,
isotropy, suitable pairs or the conjecture. All manuscript deductions using
them must be proved separately. Their exact source review is recorded in
STANDARD_INPUT_REVIEW.md.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction

namespace LeBrunSalamon.Construction.StandardInputs.BundleGeometry

/-- The original pullback sequence is short exact by pulling actual local
retractions through the canonical comparison maps and using right exactness.
The only admitted input is the generic EGA I 0(5.4.9) local splitting theorem. -/
theorem _root_.LeBrunSalamon.PublishedInputs.BaseChangeFibers.vectorBundle_pullback_shortExact
    {X Y : Scheme} (f : X ⟶ Y) {a b c : ℕ}
    (E : AlgebraicVectorBundle Y a) (F : AlgebraicVectorBundle Y b)
    (G : AlgebraicVectorBundle Y c)
    (i : E.sheaf ⟶ F.sheaf) (q : F.sheaf ⟶ G.sheaf)
    (hz : i ≫ q = 0) (hex : (ShortComplex.mk i q hz).ShortExact) :
    ((ShortComplex.mk i q hz).map (Scheme.Modules.pullback f)).ShortExact := by
  exact LeBrunSalamon.VectorBundlePullback.vectorBundle_pullback_shortExact f E F G i q hz hex

/-- Project API wrapper for pullback exactness. -/
theorem vectorBundle_pullback_shortExact {X Y : Scheme} (f : X ⟶ Y)
    {a b c : ℕ} (E : AlgebraicVectorBundle Y a)
    (F : AlgebraicVectorBundle Y b) (G : AlgebraicVectorBundle Y c)
    (i : E.sheaf ⟶ F.sheaf) (q : F.sheaf ⟶ G.sheaf)
    (hz : i ≫ q = 0) (hex : (ShortComplex.mk i q hz).ShortExact) :
    ((ShortComplex.mk i q hz).map (Scheme.Modules.pullback f)).ShortExact :=
  LeBrunSalamon.PublishedInputs.BaseChangeFibers.vectorBundle_pullback_shortExact
    f E F G i q hz hex

/-- The original fiber-evaluation map is injective by the proved canonical
Hom base-change theorem and the explicit faithfulness of global evaluation
on Spec C. No separate Hom-fiber injectivity theorem is admitted. -/
theorem _root_.LeBrunSalamon.PublishedInputs.BaseChangeFibers.homFiberEvaluation_injective
    {Y : Scheme} {r : ℕ} (E : AlgebraicVectorBundle Y r)
    (F : OModule Y) (x : ComplexBase ⟶ Y) :
    Function.Injective
      (LeBrunSalamon.Construction.Lines.LeviFiberGeometry.homFiberEvaluation
        E.sheaf F x) := by
  intro a b h
  apply LeBrunSalamon.HomFiberInjectivity.homFiberEvaluation_injective E F x
  funext v
  exact congrArg (fun q => q v) h

/-- Project API wrapper for injectivity of internal-Hom fiber evaluation. -/
theorem homFiberEvaluation_injective_of_locallyFree {Y : Scheme} {r : ℕ}
    (E : AlgebraicVectorBundle Y r) (F : OModule Y) (x : ComplexBase ⟶ Y) :
    Function.Injective (Lines.LeviFiberGeometry.homFiberEvaluation E.sheaf F x) :=
  LeBrunSalamon.PublishedInputs.BaseChangeFibers.homFiberEvaluation_injective E F x

end LeBrunSalamon.Construction.StandardInputs.BundleGeometry

end
/- END RELOCATED POSITIVE-NODE DEPENDENCY: LSContactStandardInputs -/

/- BEGIN RELOCATED POSITIVE-NODE DEPENDENCY: LSContactHomBaseChange -/
/-!
Canonical internal-Hom pullback and its actual currying comparison.

HB-01 is the sole standard input in this fragment: the evaluation-normalized
Hom base-change map is invertible when its source sheaf is finite locally
free. It is valid for every scheme morphism and arbitrary target sheaf.
This is the finite-free local calculation, not the finite-presentation-only
flat-base-change statement. Sources: Stacks 01CM, 0FNU, 0098.
All tensor/currying compatibility lemmas below are proved for the actual maps.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven LeBrunSalamon.Skeleton
open LeBrunSalamon.Construction
open LeBrunSalamon.Construction.Lines.LeviFiberGeometry

namespace LeBrunSalamon.Construction.Lines.ContactPositiveHom

theorem tensorMap_zero_left {X : Scheme} {E F E' F' : OModule X}
    (g : F ⟶ F') : tensorMap (0 : E ⟶ E') g = 0 := by
  apply ((tensorPresentation E F).universal _).1
  apply sheafBilinearMap_ext
  intro U u v
  change (tensorMap (0 : E ⟶ E') g).app U
      ((tensorPresentation E F).pair.apply U u v) = 0
  rw [tensorMap_apply]
  simp

@[simp]
theorem currySheaf_zero {X : Scheme} (Z E F : OModule X) :
    currySheaf (0 : tensorSheaf Z E ⟶ F) = 0 := by
  apply (internalHomPresentation E F).hom_ext
  change tensorMap (currySheaf (0 : tensorSheaf Z E ⟶ F)) (𝟙 E) ≫
      (internalHomPresentation E F).evaluate =
    tensorMap (0 : Z ⟶ internalHomSheaf E F) (𝟙 E) ≫
      (internalHomPresentation E F).evaluate
  rw [currySheaf_evaluate, tensorMap_zero_left, zero_comp]

theorem tensorLift_precompose {X : Scheme} {E F E' F' G : OModule X}
    (b : SheafBilinearMap E' F' G) (a : E ⟶ E') (c : F ⟶ F') :
    tensorLift (b.precompose a c) = tensorMap a c ≫ tensorLift b := by
  apply ((tensorPresentation E F).universal G).1
  dsimp only
  rw [tensorLift_pair]
  apply sheafBilinearMap_ext
  intro U u v
  have h := congrArg (fun q : SheafBilinearMap E' F' G =>
    q.apply U (a.app U u) (c.app U v)) (tensorLift_pair b)
  change b.apply U (a.app U u) (c.app U v) =
    (tensorLift b).app U ((tensorMap a c).app U
      ((tensorPresentation E F).pair.apply U u v))
  rw [tensorMap_apply]
  exact h.symm

theorem tensorLift_eq_zero_of_apply_eq_zero {X : Scheme} {E F G : OModule X}
    (b : SheafBilinearMap E F G) (hb : ∀ U u v, b.apply U u v = 0) :
    tensorLift b = 0 := by
  apply ((tensorPresentation E F).universal G).1
  dsimp only
  rw [tensorLift_pair]
  apply sheafBilinearMap_ext
  intro U u v
  exact hb U u v

theorem pairing_eq_zero_of_curry_zero {X : Scheme} {E F G : OModule X}
    (b : SheafBilinearMap E F G) (h : currySheaf (tensorLift b) = 0)
    (U : X.Opens) (u : SectionsOn E U) (v : SectionsOn F U) :
    b.apply U u v = 0 := by
  have hb := congrArg (fun q : SheafBilinearMap E F G => q.apply U u v)
    (sheafEvaluationPair_curry b)
  rw [h] at hb
  simpa [sheafEvaluationPair, SheafBilinearMap.precompose,
    SheafBilinearMap.postcompose] using hb.symm

/-- The actual evaluation-normalized comparison, with no frame choices. -/
def homBaseChange {X Y : Scheme} (f : X ⟶ Y) (E F : OModule Y) :
    pullbackModule f (internalHomSheaf E F) ⟶
      internalHomSheaf (pullbackModule f E) (pullbackModule f F) :=
  currySheaf (tensorLift (pullbackPair f (sheafEvaluationPair E F)))

/-- Currying a pulled-back pairing is the pullback of the original curry
followed by this particular Hom comparison. This proves its normalization. -/
theorem homBaseChange_curry {X Y : Scheme} (f : X ⟶ Y)
    {Z E F : OModule Y} (b : SheafBilinearMap Z E F) :
    (Scheme.Modules.pullback f).map (currySheaf (tensorLift b)) ≫
        homBaseChange f E F =
      currySheaf (tensorLift (pullbackPair f b)) := by
  have hp := pullbackPair_precompose f (sheafEvaluationPair E F)
    (currySheaf (tensorLift b)) (𝟙 E)
  rw [sheafEvaluationPair_curry] at hp
  simp only [CategoryTheory.Functor.map_id] at hp
  unfold homBaseChange
  change _ ≫ (internalHomPresentation (pullbackModule f E)
    (pullbackModule f F)).curry _ = _
  rw [← InternalHomPresentation.curry_precompose, ← tensorLift_precompose, ← hp]
  rfl

end LeBrunSalamon.Construction.Lines.ContactPositiveHom

namespace LeBrunSalamon.Construction.StandardInputs.BundleGeometry

/-- The actual Hom base-change map is an isomorphism by the proved
dual-tensor factorization and its evaluation normalization. The generic
published inputs are EGA I 0(5.4.2), canonical dual base change 0(5.4.5),
and preservation of finite local freeness under pullback. -/
theorem _root_.LeBrunSalamon.PublishedInputs.BaseChangeFibers.homBaseChange_isIso
    {X Y : Scheme} (f : X ⟶ Y) {r : ℕ}
    (E : AlgebraicVectorBundle Y r) (F : OModule Y) :
    IsIso (LeBrunSalamon.Construction.Lines.ContactPositiveHom.homBaseChange
      f E.sheaf F) := by
  exact LeBrunSalamon.FiniteFreeHomBaseChange.homComparison_isIso f E.locallyFree F

/-- Project API wrapper for internal-Hom base change. -/
theorem homBaseChange_isIso {X Y : Scheme} (f : X ⟶ Y)
    {r : ℕ} (E : AlgebraicVectorBundle Y r) (F : OModule Y) :
    IsIso (Lines.ContactPositiveHom.homBaseChange f E.sheaf F) :=
  LeBrunSalamon.PublishedInputs.BaseChangeFibers.homBaseChange_isIso f E F

end LeBrunSalamon.Construction.StandardInputs.BundleGeometry

end
/- END RELOCATED POSITIVE-NODE DEPENDENCY: LSContactHomBaseChange -/

/- BEGIN RELOCATED POSITIVE-NODE DEPENDENCY: LSContactHorizontal -/
/-!
The actual contact-geometric core of lines:positive.

The canonical nonzero differential of the actual nonconstant curve lifts
through the actual pulled-back contact sequence. Perfectness of the
evaluation-normalized pulled-back Levi form then constructs a NONZERO map
f*F → Hom(T_P1,f*L) ≅ O(-1). Hence f*F is not globally generated.
The degree-one quotient splitting contradiction proves actual horizontality
of the positive inclusion and its original positiveNodeSpace.

No manuscript-specific admission is introduced here. The separately
reviewed generic standard boundaries are imported, not reproved by naming
the desired contact-geometric conclusions as hypotheses.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.PhaseThirty LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction
open LeBrunSalamon.Construction.Lines.LeviFiberGeometry
open LeBrunSalamon.Construction.Lines.ContactPositiveHom

namespace LeBrunSalamon.Construction.Lines.ContactPositive

/-! ### Nonvanishing of the actual dual differential -/

theorem genericDualMap_zero {X : Scheme} (E F : OModule X) :
    HomConstruction.Generic.dualMap (R := X.sheaf) (0 : E ⟶ F) = 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply PresheafOfModules.hom_ext
  intro V
  ext e
  change φ.app V 0 = 0
  simp

/-- Actual finite-rank biduality detects a morphism whose pairing with
every local dual section vanishes. No pointwise surrogate is used. -/
theorem hom_eq_zero_of_dualPair_zero {X : Scheme} {E F : OModule X} {r : ℕ}
    (hF : IsLocallyFreeOfRank F r) (f : E ⟶ F)
    (hpair : ∀ (U : X.Opens) (φ : SectionsOn (dualSheaf F) U)
      (e : SectionsOn E U),
      (sheafEvaluationPair F (structureModule X)).apply U φ (f.app U e) = 0) :
    f = 0 := by
  have hd : HomConstruction.Generic.dualMap (R := X.sheaf) f = 0 := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    apply PresheafOfModules.hom_ext
    intro V
    ext e
    change φ.app V (f.val.app (op V.unop.left) e) = 0
    let φV := HomConstruction.Generic.restrictSection V.unop.hom φ
    let ψ := (internalHomGenericIso F (structureModule X)).inv.app V.unop.left φV
    have hi : (internalHomGenericIso F (structureModule X)).hom.app V.unop.left ψ = φV := by
      exact congrArg (fun k => k.app V.unop.left φV)
        (internalHomGenericIso F (structureModule X)).inv_hom_id
    have he : HomConstruction.Generic.evaluationAt (R := X.sheaf)
        F (structureModule X) V.unop.left φV (f.app V.unop.left e) = 0 := by
      rw [← hi, internalHomGenericIso_evaluate_pair]
      exact hpair V.unop.left ψ e
    change HomConstruction.Generic.evaluationAt (R := X.sheaf)
      F (structureModule X) V.unop.left
      (HomConstruction.Generic.restrictSection V.unop.hom φ)
      (f.app V.unop.left e) = 0 at he
    rw [HomConstruction.Generic.evaluationAt_restrict] at he
    exact he
  obtain ⟨q, hq, hr⟩ := hF
  letI := hq
  letI : IsIso (HomConstruction.Generic.bidualMap (R := X.sheaf) F) :=
    HomConstruction.Generic.isIso_bidualMap_of_free_cover F q.X q.coversTop
      (fun _ => Fin r) (fun i => SheafTensor.localBasisTrivialization q hr i)
  apply (cancel_mono (HomConstruction.Generic.bidualMap (R := X.sheaf) F)).1
  rw [HomConstruction.Generic.bidualMap_naturality, zero_comp]
  change HomConstruction.Generic.bidualMap (R := X.sheaf) E ≫
    HomConstruction.Generic.dualMap (HomConstruction.Generic.dualMap f) = 0
  rw [hd, genericDualMap_zero, comp_zero]

/-- The existing canonical raw tangent map is nonzero whenever the
cotangent map is nonzero and its target is finite locally free. -/
theorem tangentMapRaw_ne_zero_of_cotangentMap_ne_zero
    {X Y S : Scheme} (f : X ⟶ Y) (s : Y ⟶ S) {r : ℕ}
    (hΩ : IsLocallyFreeOfRank (cotangentSheaf (f ≫ s)) r)
    (hf : cotangentMap f s ≠ 0) : tangentMapRaw f s ≠ 0 := by
  intro hz
  apply hf
  apply hom_eq_zero_of_dualPair_zero hΩ (cotangentMap f s)
  intro U φ e
  have h := congrArg (fun k :
      tensorSheaf (tangentSheaf (f ≫ s)) (pullbackModule f (cotangentSheaf s)) ⟶
        structureModule X =>
      k.app U ((tensorPresentation (tangentSheaf (f ≫ s))
        (pullbackModule f (cotangentSheaf s))).pair.apply U φ e))
    (currySheaf_evaluate
      (tensorMap (𝟙 (tangentSheaf (f ≫ s))) (cotangentMap f s) ≫
        (internalHomPresentation (cotangentSheaf (f ≫ s)) (structureModule X)).evaluate))
  change (internalHomPresentation (pullbackModule f (cotangentSheaf s))
      (structureModule X)).evaluate.app U
      ((tensorMap (tangentMapRaw f s) (𝟙 _)).app U
        ((tensorPresentation (tangentSheaf (f ≫ s))
          (pullbackModule f (cotangentSheaf s))).pair.apply U φ e)) =
    (internalHomPresentation (cotangentSheaf (f ≫ s)) (structureModule X)).evaluate.app U
      ((tensorMap (𝟙 _) (cotangentMap f s)).app U
        ((tensorPresentation (tangentSheaf (f ≫ s))
          (pullbackModule f (cotangentSheaf s))).pair.apply U φ e)) at h
  rw [tensorMap_apply, tensorMap_apply, hz] at h
  simpa [sheafEvaluationPair, SheafBilinearMap.postcompose] using h.symm

/-! ### The original curve differential and pulled-back contact sequence -/

def distributionBundle {n : ℕ} {X : ContactFanoManifold n} (f : FreeLine X) :
    AlgebraicVectorBundle ProjectiveLine (2 * n) :=
  PhaseThirtyFive.pullbackBundle f.curve.map X.contact.sequence.distribution

def contactLine {n : ℕ} {X : ContactFanoManifold n} (f : FreeLine X) :
    LineBundle ProjectiveLine :=
  pullbackLine f.curve.map X.contact.sequence.line

def distributionInclusion {n : ℕ} {X : ContactFanoManifold n} (f : FreeLine X) :
    (distributionBundle f).sheaf ⟶ (PositivePart.freeLineBundle f).sheaf :=
  (Scheme.Modules.pullback f.curve.map).map X.contact.sequence.inclusion

def contactProjection {n : ℕ} {X : ContactFanoManifold n} (f : FreeLine X) :
    (PositivePart.freeLineBundle f).sheaf ⟶ (contactLine f).sheaf :=
  (Scheme.Modules.pullback f.curve.map).map X.contact.sequence.form

theorem distribution_contact_zero {n : ℕ} {X : ContactFanoManifold n}
    (f : FreeLine X) : distributionInclusion f ≫ contactProjection f = 0 := by
  change (Scheme.Modules.pullback f.curve.map).map X.contact.sequence.inclusion ≫
    (Scheme.Modules.pullback f.curve.map).map X.contact.sequence.form = 0
  rw [← Functor.map_comp, X.contact.sequence.comp_zero, Functor.map_zero]

theorem pullbackContact_shortExact {n : ℕ} {X : ContactFanoManifold n}
    (f : FreeLine X) :
    (ShortComplex.mk (distributionInclusion f) (contactProjection f)
      (distribution_contact_zero f)).ShortExact := by
  exact StandardInputs.BundleGeometry.vectorBundle_pullback_shortExact f.curve.map
    X.contact.sequence.distribution (intrinsicTangentBundle X.variety)
    X.contact.sequence.line X.contact.sequence.inclusion X.contact.sequence.form
    X.contact.sequence.comp_zero X.contact.sequence.shortExact

def contactLineIso {n : ℕ} {X : ContactFanoManifold n} (f : FreeLine X) :
    (contactLine f).sheaf ≅ (projectiveTwist P marking 1).sheaf := by
  have h := projectiveLineDegree_spec P marking (contactLine f)
  have hd : projectiveLineDegree P marking (contactLine f) = 1 := f.degreeOne
  rw [hd] at h
  exact h.some

/-- This is exactly the differential already used in nodeDifferential. -/
def curveDifferential {n : ℕ} {X : ContactFanoManifold n} (f : FreeLine X) :
    tangentSheaf P.structureMap ⟶ (PositivePart.freeLineBundle f).sheaf :=
  differentialOver (projectiveLineVariety P) X.variety f.curve.map f.curve.overC

theorem curveDifferential_ne_zero {n : ℕ} {X : ContactFanoManifold n}
    (f : FreeLine X) : curveDifferential f ≠ 0 := by
  have hΩ : IsLocallyFreeOfRank
      (cotangentSheaf (f.curve.map ≫ X.variety.structureMap)) 1 := by
    rw [f.curve.overC]
    exact smooth_cotangent_rank P.structureMap 1 (projectiveLineVariety P).smooth
  have hn := tangentMapRaw_ne_zero_of_cotangentMap_ne_zero f.curve.map
    X.variety.structureMap hΩ
    (nonconstant_complexCurve_differential_ne_zero P X.variety f.curve)
  letI := dualBaseChange_isIso f.curve.map
    (smooth_cotangent_rank X.variety.structureMap (2 * n + 1) X.variety.smooth)
  let e : tangentSheaf P.structureMap ≅
      tangentSheaf (f.curve.map ≫ X.variety.structureMap) :=
    eqToIso (congrArg tangentSheaf f.curve.overC.symm)
  intro hz
  have h := congrArg (fun k => k ≫ dualBaseChange f.curve.map
    (cotangentSheaf X.variety.structureMap)) hz
  have he : e.hom ≫ tangentMapRaw f.curve.map X.variety.structureMap = 0 := by
    simpa [curveDifferential, differentialOver, e, Category.assoc] using h
  apply hn
  apply (cancel_epi e.hom).1
  simpa only [comp_zero] using he

theorem curveDifferential_contact_zero {n : ℕ} {X : ContactFanoManifold n}
    (f : FreeLine X) : curveDifferential f ≫ contactProjection f = 0 :=
  intrinsicContactLine_velocity_zero P marking X.variety X.contact f.curve
    f.degreeOne (curveDifferential f ≫ contactProjection f)

def distributionDifferential {n : ℕ} {X : ContactFanoManifold n} (f : FreeLine X) :
    tangentSheaf P.structureMap ⟶ (distributionBundle f).sheaf := by
  letI : Mono (distributionInclusion f) := (pullbackContact_shortExact f).mono_f
  exact (pullbackContact_shortExact f).exact.lift
    (curveDifferential f) (curveDifferential_contact_zero f)

@[reassoc]
theorem distributionDifferential_inclusion {n : ℕ} {X : ContactFanoManifold n}
    (f : FreeLine X) :
    distributionDifferential f ≫ distributionInclusion f = curveDifferential f := by
  letI : Mono (distributionInclusion f) := (pullbackContact_shortExact f).mono_f
  exact (pullbackContact_shortExact f).exact.lift_f
    (curveDifferential f) (curveDifferential_contact_zero f)

theorem distributionDifferential_ne_zero {n : ℕ} {X : ContactFanoManifold n}
    (f : FreeLine X) : distributionDifferential f ≠ 0 := by
  intro hz
  apply curveDifferential_ne_zero f
  rw [← distributionDifferential_inclusion f, hz, zero_comp]

/-! ### Perfect Levi contraction gives the nonzero negative-degree map -/

def pulledLeviPair {n : ℕ} {X : ContactFanoManifold n} (f : FreeLine X) :
    SheafBilinearMap (distributionBundle f).sheaf (distributionBundle f).sheaf
      (contactLine f).sheaf :=
  pullbackPair f.curve.map (intrinsicLeviPair X.contact.sequence)

theorem pulledLevi_isIso {n : ℕ} {X : ContactFanoManifold n} (f : FreeLine X) :
    IsIso (currySheaf (tensorLift (pulledLeviPair f))) := by
  letI : IsIso (currySheaf (tensorLift (intrinsicLeviPair X.contact.sequence))) :=
    X.contact.nondegenerate
  letI := StandardInputs.BundleGeometry.homBaseChange_isIso f.curve.map
    X.contact.sequence.distribution X.contact.sequence.line.sheaf
  change IsIso (currySheaf (tensorLift
    (pullbackPair f.curve.map (intrinsicLeviPair X.contact.sequence))))
  rw [← homBaseChange_curry]
  infer_instance

/-- Contraction in the second slot with the canonical distribution-valued
curve derivative. Its codomain is the actual internal Hom. -/
def negativeHom {n : ℕ} {X : ContactFanoManifold n} (f : FreeLine X) :
    (distributionBundle f).sheaf ⟶
      internalHomSheaf (tangentSheaf P.structureMap) (contactLine f).sheaf :=
  currySheaf (tensorLift ((pulledLeviPair f).precompose (𝟙 _)
    (distributionDifferential f)))

theorem negativeHom_ne_zero {n : ℕ} {X : ContactFanoManifold n}
    (f : FreeLine X) : negativeHom f ≠ 0 := by
  intro hz
  have hleft : tensorLift ((pulledLeviPair f).precompose
      (distributionDifferential f) (𝟙 _)) = 0 := by
    apply tensorLift_eq_zero_of_apply_eq_zero
    intro U t u
    have hr := pairing_eq_zero_of_curry_zero
      ((pulledLeviPair f).precompose (𝟙 _) (distributionDifferential f)) hz U u t
    change (pulledLeviPair f).apply U u ((distributionDifferential f).app U t) = 0 at hr
    change (pulledLeviPair f).apply U ((distributionDifferential f).app U t) u = 0
    rw [show (pulledLeviPair f).apply U ((distributionDifferential f).app U t) u =
        -(pulledLeviPair f).apply U u ((distributionDifferential f).app U t) from
      pullbackPair_skew f.curve.map (intrinsicLeviPair X.contact.sequence)
        (intrinsicLeviPair_skew X.contact.sequence) U _ _, hr, neg_zero]
  have hc : distributionDifferential f ≫ currySheaf (tensorLift (pulledLeviPair f)) = 0 := by
    change distributionDifferential f ≫
      (internalHomPresentation (distributionBundle f).sheaf (contactLine f).sheaf).curry
        (tensorLift (pulledLeviPair f)) = 0
    rw [← InternalHomPresentation.curry_precompose, ← tensorLift_precompose, hleft]
    exact currySheaf_zero _ _ _
  letI := pulledLevi_isIso f
  apply distributionDifferential_ne_zero f
  apply (cancel_mono (currySheaf (tensorLift (pulledLeviPair f)))).1
  simpa only [zero_comp] using hc

def negativeHomTargetIso {n : ℕ} {X : ContactFanoManifold n} (f : FreeLine X) :
    internalHomSheaf (tangentSheaf P.structureMap) (contactLine f).sheaf ≅
      (projectiveTwist P marking (-1)).sheaf := by
  let eT := (projectiveLine_tangent_twist P marking).some
  let eH := (internalHomPresentation (tangentSheaf P.structureMap) (contactLine f).sheaf).mapIso
    (internalHomPresentation (projectiveTwist P marking 2).sheaf
      (projectiveTwist P marking 1).sheaf) eT (contactLineIso f)
  exact eH ≪≫ (projectiveTwist_internalHom P marking 2 1).some

def negativeMap {n : ℕ} {X : ContactFanoManifold n} (f : FreeLine X) :
    (distributionBundle f).sheaf ⟶ (projectiveTwist P marking (-1)).sheaf :=
  negativeHom f ≫ (negativeHomTargetIso f).hom

theorem negativeMap_ne_zero {n : ℕ} {X : ContactFanoManifold n}
    (f : FreeLine X) : negativeMap f ≠ 0 := by
  intro hz
  apply negativeHom_ne_zero f
  apply (cancel_mono (negativeHomTargetIso f).hom).1
  simpa only [negativeMap, zero_comp] using hz

/-- Manuscript deduction: the actual pulled-back contact distribution
cannot be globally generated, because its constructed map to O(-1) is nonzero. -/
theorem distribution_not_globallyGenerated {n : ℕ} {X : ContactFanoManifold n}
    (f : FreeLine X) : ¬ IsGloballyGenerated (distributionBundle f).sheaf :=
  ContactGeneration.not_globallyGenerated_of_negative_twist_map
    P marking (-1) (by norm_num) (negativeMap f) (negativeMap_ne_zero f)

/-- Manuscript horizontality for the actual chosen positive inclusion.
Non-generation was proved from canonical df and Levi perfectness above. -/
theorem positiveHorizontal {n : ℕ} {X : ContactFanoManifold n} (f : FreeLine X) :
    PositivePart.freeLinePositiveInclusion f ≫ contactProjection f = 0 := by
  exact ContactGeneration.positiveInclusion_quotient_eq_zero P marking
    (PositivePart.freeLineProfile f) (PositivePart.freeLineSplitting f)
    (distributionInclusion f) (contactProjection f) (distribution_contact_zero f)
    (pullbackContact_shortExact f) (contactLineIso f) f.free
    (distribution_not_globallyGenerated f)

def positiveDistributionLift {n : ℕ} {X : ContactFanoManifold n} (f : FreeLine X) :
    (PositivePart.freeLinePositiveBundle f).sheaf ⟶ (distributionBundle f).sheaf := by
  letI : Mono (distributionInclusion f) := (pullbackContact_shortExact f).mono_f
  exact (pullbackContact_shortExact f).exact.lift
    (PositivePart.freeLinePositiveInclusion f) (positiveHorizontal f)

@[reassoc]
theorem positiveDistributionLift_inclusion {n : ℕ} {X : ContactFanoManifold n}
    (f : FreeLine X) :
    positiveDistributionLift f ≫ distributionInclusion f =
      PositivePart.freeLinePositiveInclusion f := by
  letI : Mono (distributionInclusion f) := (pullbackContact_shortExact f).mono_f
  exact (pullbackContact_shortExact f).exact.lift_f
    (PositivePart.freeLinePositiveInclusion f) (positiveHorizontal f)

/-! ### Naturality retains the original node maps -/

theorem fiberMap_comp {Y : Scheme} {E F G : OModule Y}
    (i : E ⟶ F) (q : F ⟶ G) (x : ComplexBase ⟶ Y) (u : Fiber E x) :
    fiberMap (i ≫ q) x u = fiberMap q x (fiberMap i x u) := by
  change ((Scheme.Modules.pullback x).map (i ≫ q)).app ⊤ u = _
  rw [Functor.map_comp]
  rfl

theorem fiberComposition_naturality {T Y : Scheme} (f : T ⟶ Y)
    (p : ComplexBase ⟶ T) (x : ComplexBase ⟶ Y) (hx : p ≫ f = x)
    {E F : OModule Y} (h : E ⟶ F) (u : Fiber (pullbackModule f E) p) :
    fiberComposition f p x hx F (fiberMap ((Scheme.Modules.pullback f).map h) p u) =
      fiberMap h x (fiberComposition f p x hx E u) := by
  subst x
  have hn := (Scheme.Modules.pullbackComp p f).hom.naturality h
  have hv := congrArg (fun k => k.app ⊤ u) hn
  simpa [fiberComposition, compositionPullback, fiberMap, onCSections] using hv

/-- The original node-space horizontal conclusion, now proved from the
actual positive subbundle and canonical fiber-composition maps. -/
theorem positiveNodeSpace_horizontal {n : ℕ} {X : ContactFanoManifold n}
    (f : FreeLine X) (x : ComplexPoint X.variety)
    (hx : marking.map ≫ f.curve.map = x.map) :
    positiveNodeSpace f x hx ≤ contactPlane X x := by
  rw [PositiveNodeImage.freeLine_positiveNodeSpace_eq_fiberImage f x hx]
  intro v hv
  obtain ⟨w, rfl⟩ := LinearMap.mem_range.mp hv
  change fiberMap X.contact.sequence.form x.map
    (fiberComposition f.curve.map marking.map x.map hx
      (tangentSheaf X.variety.structureMap)
      (fiberMap (PositivePart.freeLinePositiveInclusion f) marking.map w)) = 0
  have hz : fiberMap (PositivePart.freeLinePositiveInclusion f ≫ contactProjection f)
      marking.map w = 0 := by
    rw [positiveHorizontal]
    change (((Scheme.Modules.pullback marking.map).map (0 :
      (PositivePart.freeLinePositiveBundle f).sheaf ⟶ (contactLine f).sheaf)).app ⊤ w) = 0
    rw [CategoryTheory.Functor.map_zero]
    rfl
  have hc := fiberMap_comp (PositivePart.freeLinePositiveInclusion f)
    (contactProjection f) marking.map w
  have hq := hc.symm.trans hz
  have hn := fiberComposition_naturality f.curve.map marking.map x.map hx
    X.contact.sequence.form
    (fiberMap (PositivePart.freeLinePositiveInclusion f) marking.map w)
  exact hn.symm.trans ((congrArg
    (fiberComposition f.curve.map marking.map x.map hx X.contact.sequence.line.sheaf)
    hq).trans (map_zero _))

end LeBrunSalamon.Construction.Lines.ContactPositive

end
/- END RELOCATED POSITIVE-NODE DEPENDENCY: LSContactHorizontal -/

/- BEGIN RELOCATED POSITIVE-NODE DEPENDENCY: LSContactCompletion -/
/-!
## Actual positive-part isotropy and the original node-space rank bound

SOURCE: `lines:positive`. Two positive twist degrees sum to at least two,
so their actual tensor has no morphism to the degree-one contact line.
The proof applies this to the restricted pulled-back intrinsic Levi map,
then transports through the canonical point/composition comparisons to
the original node space. Finite locally free Hom/fiber comparison supplies
actual Levi nondegeneracy; ordinary symplectic linear algebra gives rank.

Every paper-specific assertion below has a proof. The only standard
Hom/fiber boundary used is the separately reviewed HF-01 declaration.
No old admitted positive-node horizontal, isotropic or rank theorem is used.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseEighteen LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentySix LeBrunSalamon.PhaseTwentySeven
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction
open LeBrunSalamon.Construction.Lines
open scoped BigOperators

namespace LeBrunSalamon.Construction.Lines.ContactPositiveIsotropy

/-! ### Tensor degree vanishing on the actual positive coproduct -/

/-- The first tensor factor also preserves the actual coproduct cocone.
This is an application of the existing tensor-Hom adjunction. -/
theorem tensorFirstCoproduct_hom_ext {Y : Scheme} {I : Type}
    (E : I → OModule Y) {Z G : OModule Y}
    {f g : tensorSheaf (∐ E) Z ⟶ G}
    (h : ∀ i, tensorMap (Sigma.ι E i) (𝟙 Z) ≫ f =
      tensorMap (Sigma.ι E i) (𝟙 Z) ≫ g) : f = g := by
  letI := tensorRight_preservesColimits (internalHomPresentation Z)
  exact Cofan.IsColimit.hom_ext
    (isColimitOfHasCoproductOfPreservesColimit (tensorRightFunctor Z) E) f g h

/-- A tensor-coproduct map vanishes once all actual two-index components
vanish. No coordinates or pointwise substitute is introduced. -/
theorem tensorCoproduct_hom_eq_zero {Y : Scheme} {I J : Type}
    (E : I → OModule Y) (F : J → OModule Y) {G : OModule Y}
    (h : tensorSheaf (∐ E) (∐ F) ⟶ G)
    (hh : ∀ i j, tensorMap (Sigma.ι E i) (Sigma.ι F j) ≫ h = 0) : h = 0 := by
  apply InternalHomPresentation.tensorCoproduct_hom_ext internalHomPresentation F
  intro j
  rw [comp_zero]
  apply tensorFirstCoproduct_hom_ext E
  intro i
  rw [comp_zero, ← Category.assoc, ← tensorMap_comp]
  simpa only [Category.comp_id, Category.id_comp] using hh i j

/-- Every tensor of two positive summands has degree greater than one.
The target is the actual line through a supplied degree-one sheaf iso. -/
theorem positiveTensorHom_eq_zero
    (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {r : ℕ} (a : TangentSplittingProfile r) {L : OModule ProjectiveLine}
    (eL : L ≅ (projectiveTwist P p 1).sheaf)
    (h : tensorSheaf (PositivePart.positiveSheaf P p a)
      (PositivePart.positiveSheaf P p a) ⟶ L) : h = 0 := by
  let E := fun i : PositivePart.PositiveIndex a => (projectiveTwist P p (a.degree i.val)).sheaf
  apply tensorCoproduct_hom_eq_zero E E h
  intro i j
  let e : tensorSheaf (E i) (E j) ≅
      (projectiveTwist P p (a.degree i.val + a.degree j.val)).sheaf :=
    Classical.choice (projectiveTwist_add P p (a.degree i.val) (a.degree j.val))
  apply (cancel_epi e.inv).mp
  apply (cancel_mono eL.hom).mp
  have hdegree : (1 : ℤ) < a.degree i.val + a.degree j.val := by
    have hi := i.property
    have hj := j.property
    omega
  simpa only [Category.assoc, comp_zero, zero_comp] using
    PositiveHom.hom_twist_eq_zero_of_lt P p p
      (a.degree i.val + a.degree j.val) 1 hdegree
      (e.inv ≫ tensorMap (Sigma.ι E i) (Sigma.ι E j) ≫ h ≫ eL.hom)

/-- Tensor-lift zero means zero on genuine sections of every open. -/
theorem pair_apply_zero_of_tensorLift_zero {Y : Scheme} {E F G : OModule Y}
    (b : SheafBilinearMap E F G) (hb : tensorLift b = 0)
    (U : Y.Opens) (u : SectionsOn E U) (v : SectionsOn F U) :
    b.apply U u v = 0 := by
  have h := congrArg (fun q : SheafBilinearMap E F G => q.apply U u v)
    (tensorLift_pair b)
  change (tensorLift b).app U ((tensorPresentation E F).pair.apply U u v) =
    b.apply U u v at h
  rw [hb] at h
  exact h.symm

/-! ### Normalized pullback pairings and actual composition transport -/

def zeroPair {Y : Scheme} (E F G : OModule Y) : SheafBilinearMap E F G where
  apply _ := 0
  naturality := by intros; simp

/-- Pullback preserves a pairing proved zero on all local sections.
Uniqueness of the normalized pullback is used, not an assumption that
global sections generate an arbitrary sheaf. -/
theorem pullbackPair_apply_zero {T Y : Scheme} (f : T ⟶ Y)
    {E F G : OModule Y} (b : SheafBilinearMap E F G)
    (hb : ∀ U u v, b.apply U u v = 0)
    (V : T.Opens) (u : SectionsOn (pullbackModule f E) V)
    (v : SectionsOn (pullbackModule f F) V) :
    (pullbackPair f b).apply V u v = 0 := by
  have hn : IsPullbackPair f b
      (zeroPair (pullbackModule f E) (pullbackModule f F) (pullbackModule f G)) := by
    intro U e z
    rw [hb]
    change 0 = pullLocalSection f G U 0
    simp only [pullLocalSection, map_zero]
  have h := (Classical.choose_spec (pullbackPair_existsUnique f b)).2 _ hn
  exact (congrArg (fun q : SheafBilinearMap (pullbackModule f E)
    (pullbackModule f F) (pullbackModule f G) => q.apply V u v) h).symm

/-- Local section form of the composition adjunction unit. -/
theorem pullbackComp_inv_pullLocalSection {T Y Z : Scheme}
    (f : T ⟶ Y) (g : Y ⟶ Z) (E : OModule Z)
    (U : Z.Opens) (u : SectionsOn E U) :
    ((Scheme.Modules.pullbackComp f g).inv.app E).app ((f ≫ g) ⁻¹ᵁ U)
      (pullLocalSection (f ≫ g) E U u) =
        pullLocalSection f (pullbackModule g E) (g ⁻¹ᵁ U)
          (pullLocalSection g E U u) := by
  have h := pullbackComp_homEquiv f g
    (𝟙 (pullbackModule f (pullbackModule g E)))
  simp only [Adjunction.homEquiv_apply, Category.comp_id, CategoryTheory.Functor.map_id] at h
  exact congrArg (fun k : E ⟶
    (Scheme.Modules.pushforward (f ≫ g)).obj (pullbackModule f (pullbackModule g E)) =>
      k.app U u) h

/-- The forward composition comparison has the inverse normalization. -/
theorem pullbackComp_hom_pullLocalSection {T Y Z : Scheme}
    (f : T ⟶ Y) (g : Y ⟶ Z) (E : OModule Z)
    (U : Z.Opens) (u : SectionsOn E U) :
    ((Scheme.Modules.pullbackComp f g).hom.app E).app ((f ≫ g) ⁻¹ᵁ U)
      (pullLocalSection f (pullbackModule g E) (g ⁻¹ᵁ U)
        (pullLocalSection g E U u)) = pullLocalSection (f ≫ g) E U u := by
  rw [← pullbackComp_inv_pullLocalSection f g E U u]
  exact congrArg (fun k : pullbackModule (f ≫ g) E ⟶ pullbackModule (f ≫ g) E =>
    k.app ((f ≫ g) ⁻¹ᵁ U) (pullLocalSection (f ≫ g) E U u))
      ((Scheme.Modules.pullbackComp f g).app E).inv_hom_id

/-- The actual composition pullback transports the normalized pairing.
The proof first compares all pulled local sections, then uses uniqueness. -/
theorem pullbackPair_comp {T Y Z : Scheme} (f : T ⟶ Y) (g : Y ⟶ Z)
    {E F G : OModule Z} (b : SheafBilinearMap E F G)
    (V : T.Opens) (u : SectionsOn (pullbackModule f (pullbackModule g E)) V)
    (v : SectionsOn (pullbackModule f (pullbackModule g F)) V) :
    ((Scheme.Modules.pullbackComp f g).hom.app G).app V
      ((pullbackPair f (pullbackPair g b)).apply V u v) =
        (pullbackPair (f ≫ g) b).apply V
          (((Scheme.Modules.pullbackComp f g).hom.app E).app V u)
          (((Scheme.Modules.pullbackComp f g).hom.app F).app V v) := by
  let eE := (Scheme.Modules.pullbackComp f g).app E
  let eF := (Scheme.Modules.pullbackComp f g).app F
  let eG := (Scheme.Modules.pullbackComp f g).app G
  let q := ((pullbackPair f (pullbackPair g b)).precompose eE.inv eF.inv).postcompose eG.hom
  have hn : IsPullbackPair (f ≫ g) b q := by
    intro U e z
    change eG.hom.app ((f ≫ g) ⁻¹ᵁ U)
      ((pullbackPair f (pullbackPair g b)).apply ((f ≫ g) ⁻¹ᵁ U)
        (eE.inv.app ((f ≫ g) ⁻¹ᵁ U) (pullLocalSection (f ≫ g) E U e))
        (eF.inv.app ((f ≫ g) ⁻¹ᵁ U) (pullLocalSection (f ≫ g) F U z))) = _
    have hp := congrArg₂
      (fun a c => (pullbackPair f (pullbackPair g b)).apply ((f ≫ g) ⁻¹ᵁ U) a c)
      (pullbackComp_inv_pullLocalSection f g E U e)
      (pullbackComp_inv_pullLocalSection f g F U z)
    have hn₁ := pullbackPair_normalized f (pullbackPair g b) (g ⁻¹ᵁ U)
      (pullLocalSection g E U e) (pullLocalSection g F U z)
    have hn₂ := congrArg
      (pullLocalSection f (pullbackModule g G) (g ⁻¹ᵁ U))
      (pullbackPair_normalized g b U e z)
    exact (congrArg
      (fun t => ((Scheme.Modules.pullbackComp f g).hom.app G).app ((f ≫ g) ⁻¹ᵁ U) t)
      (hp.trans (hn₁.trans hn₂))).trans
        (pullbackComp_hom_pullLocalSection f g G U (b.apply U e z))
  have heq : q = pullbackPair (f ≫ g) b :=
    (Classical.choose_spec (pullbackPair_existsUnique (f ≫ g) b)).2 _ hn
  have h := congrArg (fun c : SheafBilinearMap (pullbackModule (f ≫ g) E)
    (pullbackModule (f ≫ g) F) (pullbackModule (f ≫ g) G) =>
      c.apply V (eE.hom.app V u) (eF.hom.app V v)) heq
  have hE : eE.inv.app V (eE.hom.app V u) = u :=
    congrArg (fun k : pullbackModule f (pullbackModule g E) ⟶
      pullbackModule f (pullbackModule g E) => k.app V u) eE.hom_inv_id
  have hF : eF.inv.app V (eF.hom.app V v) = v :=
    congrArg (fun k : pullbackModule f (pullbackModule g F) ⟶
      pullbackModule f (pullbackModule g F) => k.app V v) eF.hom_inv_id
  change eG.hom.app V ((pullbackPair f (pullbackPair g b)).apply V
      (eE.inv.app V (eE.hom.app V u)) (eF.inv.app V (eF.hom.app V v))) = _ at h
  rw [hE, hF] at h
  exact h

/-- The corresponding equality on the original complex fibers, including
the specified equality identifying the image point with the chosen node. -/
theorem fiberComposition_pair {T Y : Scheme} (f : T ⟶ Y)
    (p : ComplexBase ⟶ T) (x : ComplexBase ⟶ Y) (hx : p ≫ f = x)
    {E F G : OModule Y} (b : SheafBilinearMap E F G)
    (u : Fiber (pullbackModule f E) p) (v : Fiber (pullbackModule f F) p) :
    fiberComposition f p x hx G
      (LeviFiberGeometry.fiberPair (pullbackPair f b) p u v) =
        LeviFiberGeometry.fiberPair b x
          (fiberComposition f p x hx E u) (fiberComposition f p x hx F v) := by
  subst x
  change ((compositionPullback p f (p ≫ f) rfl G).hom.app ⊤)
      ((pullbackPair p (pullbackPair f b)).apply ⊤ u v) =
    (pullbackPair (p ≫ f) b).apply ⊤
      (((compositionPullback p f (p ≫ f) rfl E).hom.app ⊤) u)
      (((compositionPullback p f (p ≫ f) rfl F).hom.app ⊤) v)
  simp only [compositionPullback, Iso.trans_hom, eqToIso_refl,
    Iso.refl_hom, Iso.app_hom, Category.comp_id]
  exact pullbackPair_comp p f b ⊤ u v

/-! ### Restrict the pulled-back intrinsic Levi pairing to the positive part -/

def positiveLeviPair {n : ℕ} {X : ContactFanoManifold n} (f : FreeLine X) :
    SheafBilinearMap (PositivePart.freeLinePositiveBundle f).sheaf
      (PositivePart.freeLinePositiveBundle f).sheaf (ContactPositive.contactLine f).sheaf :=
  (pullbackPair f.curve.map (intrinsicLeviPair X.contact.sequence)).precompose
    (ContactPositive.positiveDistributionLift f) (ContactPositive.positiveDistributionLift f)

theorem positiveLevi_tensor_zero {n : ℕ} {X : ContactFanoManifold n}
    (f : FreeLine X) : tensorLift (positiveLeviPair f) = 0 :=
  positiveTensorHom_eq_zero P marking (PositivePart.freeLineProfile f)
    (ContactPositive.contactLineIso f) _

/-- Isotropy is proved on every open before taking a point fiber. -/
theorem positiveLevi_local_zero {n : ℕ} {X : ContactFanoManifold n}
    (f : FreeLine X) (U : ProjectiveLine.Opens)
    (u v : SectionsOn (PositivePart.freeLinePositiveBundle f).sheaf U) :
    (positiveLeviPair f).apply U u v = 0 :=
  pair_apply_zero_of_tensorLift_zero (positiveLeviPair f) (positiveLevi_tensor_zero f) U u v

/-- Pulling the proved zero restricted pairing to the marking gives zero
on all actual positive fiber vectors. -/
theorem positiveLevi_fiber_zero {n : ℕ} {X : ContactFanoManifold n}
    (f : FreeLine X)
    (u v : Fiber (PositivePart.freeLinePositiveBundle f).sheaf marking.map) :
    LeviFiberGeometry.fiberPair
      (pullbackPair f.curve.map (intrinsicLeviPair X.contact.sequence)) marking.map
        (fiberMap (ContactPositive.positiveDistributionLift f) marking.map u)
        (fiberMap (ContactPositive.positiveDistributionLift f) marking.map v) = 0 := by
  have h := congrArg (fun q : SheafBilinearMap
    (pullbackModule marking.map (PositivePart.freeLinePositiveBundle f).sheaf)
    (pullbackModule marking.map (PositivePart.freeLinePositiveBundle f).sheaf)
    (pullbackModule marking.map (ContactPositive.contactLine f).sheaf) => q.apply ⊤ u v)
    (LeviFiberGeometry.pullbackPair_precompose marking.map
      (pullbackPair f.curve.map (intrinsicLeviPair X.contact.sequence))
      (ContactPositive.positiveDistributionLift f) (ContactPositive.positiveDistributionLift f))
  have hz := pullbackPair_apply_zero marking.map (positiveLeviPair f)
    (positiveLevi_local_zero f) ⊤ u v
  exact h.symm.trans hz

/-! ### The original node fiber, with no supplied splitting hypothesis -/

def positiveDistributionNodeMap {n : ℕ} {X : ContactFanoManifold n}
    (f : FreeLine X) (x : ComplexPoint X.variety)
    (hx : marking.map ≫ f.curve.map = x.map) :
    Fiber (PositivePart.freeLinePositiveBundle f).sheaf marking.map →ₗ[ℂ]
      Fiber X.contact.sequence.distribution.sheaf x.map :=
  (fiberComposition f.curve.map marking.map x.map hx
    X.contact.sequence.distribution.sheaf).comp
      (fiberMap (ContactPositive.positiveDistributionLift f) marking.map)

/-- The actual horizontal lift has exactly the original positive tangent
image after inclusion and the fixed composition comparison. -/
theorem positiveDistributionNodeMap_inclusion {n : ℕ} {X : ContactFanoManifold n}
    (f : FreeLine X) (x : ComplexPoint X.variety)
    (hx : marking.map ≫ f.curve.map = x.map)
    (u : Fiber (PositivePart.freeLinePositiveBundle f).sheaf marking.map) :
    fiberMap X.contact.sequence.inclusion x.map (positiveDistributionNodeMap f x hx u) =
      fiberComposition f.curve.map marking.map x.map hx
        (tangentSheaf X.variety.structureMap)
          (fiberMap (PositivePart.freeLinePositiveInclusion f) marking.map u) := by
  have hn := ContactPositive.fiberComposition_naturality f.curve.map marking.map x.map hx
    X.contact.sequence.inclusion
    (fiberMap (ContactPositive.positiveDistributionLift f) marking.map u)
  have hc := ContactPositive.fiberMap_comp (ContactPositive.positiveDistributionLift f)
    (ContactPositive.distributionInclusion f) marking.map u
  have hf := congrArg (fun k : (PositivePart.freeLinePositiveBundle f).sheaf ⟶
      (PositivePart.freeLineBundle f).sheaf => fiberMap k marking.map u)
    (ContactPositive.positiveDistributionLift_inclusion f)
  exact hn.symm.trans (congrArg
    (fiberComposition f.curve.map marking.map x.map hx (tangentSheaf X.variety.structureMap))
    (hc.symm.trans hf))

/-- Isotropy survives the actual transport from the curve's marked fiber
to the original contact fiber at x. -/
theorem positiveDistributionNodeMap_isotropic {n : ℕ} {X : ContactFanoManifold n}
    (f : FreeLine X) (x : ComplexPoint X.variety)
    (hx : marking.map ≫ f.curve.map = x.map)
    (u v : Fiber (PositivePart.freeLinePositiveBundle f).sheaf marking.map) :
    leviFiberValue X x (positiveDistributionNodeMap f x hx u)
      (positiveDistributionNodeMap f x hx v) = 0 := by
  calc
    _ = fiberComposition f.curve.map marking.map x.map hx X.contact.sequence.line.sheaf
        (LeviFiberGeometry.fiberPair
          (pullbackPair f.curve.map (intrinsicLeviPair X.contact.sequence)) marking.map
            (fiberMap (ContactPositive.positiveDistributionLift f) marking.map u)
            (fiberMap (ContactPositive.positiveDistributionLift f) marking.map v)) :=
      (fiberComposition_pair f.curve.map marking.map x.map hx
        (intrinsicLeviPair X.contact.sequence) _ _).symm
    _ = 0 := by rw [positiveLevi_fiber_zero, map_zero]

/-! ### Nondegeneracy is inherited from actual contact perfectness -/

/-- HF-01 is used only for the generic finite locally free Hom comparison.
The contact hypothesis is discharged by the original sheaf currying iso. -/
theorem actualLevi_leftNondegenerate {n : ℕ} (X : ContactFanoManifold n)
    (x : ComplexPoint X.variety)
    (u : Fiber X.contact.sequence.distribution.sheaf x.map)
    (hu : ∀ v, leviFiberValue X x u v = 0) : u = 0 :=
  LeviFiberGeometry.leviFiberValue_leftNondegenerate_of_homFiberEvaluation_injective X x
    (StandardInputs.BundleGeometry.homFiberEvaluation_injective_of_locallyFree
      X.contact.sequence.distribution X.contact.sequence.line.sheaf x.map) u hu

/-- Any pointwise frame of the actual contact line gives the same
nondegenerate scalar form; no symplectic structure is supplied as input. -/
theorem actualScalarLevi_nondegenerate {n : ℕ} (X : ContactFanoManifold n)
    (x : ComplexPoint X.variety) (frame : Fiber X.contact.sequence.line.sheaf x.map ≃ₗ[ℂ] ℂ) :
    (LeviFiberGeometry.scalarLevi X x frame).Nondegenerate := by
  have hcompare := StandardInputs.BundleGeometry.homFiberEvaluation_injective_of_locallyFree
    X.contact.sequence.distribution X.contact.sequence.line.sheaf x.map
  constructor
  · exact LeviFiberGeometry.scalarLevi_leftNondegenerate_of_homFiberEvaluation_injective
      X x frame hcompare
  · intro v hv
    apply LeviFiberGeometry.scalarLevi_leftNondegenerate_of_homFiberEvaluation_injective
      X x frame hcompare v
    intro u
    rw [LeviFiberGeometry.scalarLevi_skew, hv, neg_zero]

/-- Ordinary finite-dimensional bilinear algebra: an isotropic subspace
of a nondegenerate scalar form has at most half the ambient dimension. -/
theorem twice_finrank_le_of_isotropic
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate) (W : Submodule K V)
    (hW : ∀ u ∈ W, ∀ v ∈ W, B u v = 0) :
    2 * Module.finrank K W ≤ Module.finrank K V := by
  have hle : W ≤ B.orthogonal W := by
    intro v hv u hu
    exact hW u hu v hv
  have hm := Submodule.finrank_mono hle
  have hd := LinearMap.BilinForm.finrank_add_finrank_orthogonal' (B := B) W
  rw [hB.ker_eq_bot, inf_bot_eq, finrank_bot, add_zero] at hd
  omega

end LeBrunSalamon.Construction.Lines.ContactPositiveIsotropy

namespace LeBrunSalamon.Construction.Lines.ContactPositive

open ContactPositiveIsotropy

/-- SOURCE `lines:positive`: the original isotropy statement, now derived
from the actual horizontal lift and tensor degree vanishing. The two
fiber vectors and their original inclusion membership are unchanged. -/
theorem positiveNodeSpace_isotropic {n : ℕ} {X : ContactFanoManifold n}
    (f : FreeLine X) (x : ComplexPoint X.variety)
    (hx : marking.map ≫ f.curve.map = x.map)
    (u v : Fiber X.contact.sequence.distribution.sheaf x.map)
    (hu : fiberMap X.contact.sequence.inclusion x.map u ∈ positiveNodeSpace f x hx)
    (hv : fiberMap X.contact.sequence.inclusion x.map v ∈ positiveNodeSpace f x hx) :
    leviFiberValue X x u v = 0 := by
  rw [PositiveNodeImage.freeLine_positiveNodeSpace_eq_fiberImage f x hx] at hu hv
  obtain ⟨u', hu'⟩ := hu
  obtain ⟨v', hv'⟩ := hv
  have heu : positiveDistributionNodeMap f x hx u' = u := by
    apply SuitablePairAlgebra.inclusionFiber_injective X x
    exact (positiveDistributionNodeMap_inclusion f x hx u').trans hu'
  have hev : positiveDistributionNodeMap f x hx v' = v := by
    apply SuitablePairAlgebra.inclusionFiber_injective X x
    exact (positiveDistributionNodeMap_inclusion f x hx v').trans hv'
  rw [← heu, ← hev]
  exact positiveDistributionNodeMap_isotropic f x hx u' v'

/-- SOURCE `lines:positive`: the original rank bound, using proved
horizontal containment and isotropy in the actual rank-2n contact fiber.
The statement has no splitting, form, nondegeneracy or rank premise. -/
theorem positiveNodeSpace_rank_le {n : ℕ} {X : ContactFanoManifold n}
    (f : FreeLine X) (x : ComplexPoint X.variety)
    (hx : marking.map ≫ f.curve.map = x.map) :
    Module.finrank ℂ (positiveNodeSpace f x hx) ≤ n := by
  letI : FiniteDimensional ℂ (TangentFiber X.variety x) :=
    fiber_finite (intrinsicTangentBundle X.variety) x.map
  let frame := LeviFiberGeometry.lineFiberFrame X x
  let B : LinearMap.BilinForm ℂ (contactPlane X x) :=
    LeviFiberGeometry.scalarLevi X x frame
  let W : Submodule ℂ (contactPlane X x) :=
    (positiveNodeSpace f x hx).comap (contactPlane X x).subtype
  have hW : ∀ u ∈ W, ∀ v ∈ W, B u v = 0 := by
    intro u hu v hv
    apply (LeviFiberGeometry.scalarLevi_eq_zero_iff X x frame u v).mpr
    change (u : TangentFiber X.variety x) ∈ positiveNodeSpace f x hx at hu
    change (v : TangentFiber X.variety x) ∈ positiveNodeSpace f x hx at hv
    exact positiveNodeSpace_isotropic f x hx
      ((SuitablePairAlgebra.distributionContactEquiv X x).symm u)
      ((SuitablePairAlgebra.distributionContactEquiv X x).symm v)
      (by simpa only [SuitablePairAlgebra.inclusion_distributionContactEquiv_symm] using hu)
      (by simpa only [SuitablePairAlgebra.inclusion_distributionContactEquiv_symm] using hv)
  have hbound := twice_finrank_le_of_isotropic B
    (actualScalarLevi_nondegenerate X x frame) W hW
  have hdim : Module.finrank ℂ W = Module.finrank ℂ (positiveNodeSpace f x hx) :=
    (Submodule.comapSubtypeEquivOfLe (positiveNodeSpace_horizontal f x hx)).finrank_eq
  rw [hdim, contactPlane_dimension X x] at hbound
  omega

/-- The original node-space dimension is exactly the rank of the actual
positive subbundle, since its split inclusion remains injective on fibers. -/
theorem positiveNodeSpace_finrank_eq_positiveRank {n : ℕ} {X : ContactFanoManifold n}
    (f : FreeLine X) (x : ComplexPoint X.variety)
    (hx : marking.map ≫ f.curve.map = x.map) :
    Module.finrank ℂ (positiveNodeSpace f x hx) =
      Fintype.card (PositivePart.PositiveIndex (PositivePart.freeLineProfile f)) := by
  have hi := (vectorBundle_fiber_exact
    (PositivePart.freeLinePositiveBundle f) (PositivePart.freeLineBundle f)
    (PositivePart.freeLineZeroBundle f)
    (PositivePart.freeLinePositiveInclusion f) (PositivePart.freeLineZeroProjection f)
    (PositivePart.freeLine_positive_zero f) (PositivePart.freeLine_shortExact f)
    marking.map).1
  have hinj : Function.Injective
      ((fiberComposition f.curve.map marking.map x.map hx
        (tangentSheaf X.variety.structureMap)).comp
          (fiberMap (PositivePart.freeLinePositiveInclusion f) marking.map)) := by
    intro u v h
    apply hi
    exact (fiberComposition_bijective f.curve.map marking.map x.map hx
      (tangentSheaf X.variety.structureMap)).1 h
  rw [PositiveNodeImage.freeLine_positiveNodeSpace_eq_fiberImage f x hx,
    LinearMap.finrank_range_of_inj hinj]
  exact fiber_dimension (PositivePart.freeLinePositiveBundle f) marking.map

/-- The rank conclusion in the manuscript's own bundle formulation.
The node is obtained from the actual marked curve; it is not extra data. -/
theorem freeLine_positiveRank_le {n : ℕ} {X : ContactFanoManifold n}
    (f : FreeLine X) :
    Fintype.card (PositivePart.PositiveIndex (PositivePart.freeLineProfile f)) ≤ n := by
  let x : ComplexPoint X.variety :=
    { map := marking.map ≫ f.curve.map
      overC := by rw [Category.assoc, f.curve.overC]; exact marking.overC }
  calc
    _ = Module.finrank ℂ (positiveNodeSpace f x rfl) :=
      (positiveNodeSpace_finrank_eq_positiveRank f x rfl).symm
    _ ≤ n := positiveNodeSpace_rank_le f x rfl

end LeBrunSalamon.Construction.Lines.ContactPositive

end

end

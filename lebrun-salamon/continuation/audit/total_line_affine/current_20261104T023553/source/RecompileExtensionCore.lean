import RecompileSections

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


namespace LeBrunSalamon.PhaseThirtyTwo

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseThree LeBrunSalamon.PhaseEighteen
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven LeBrunSalamon.PhaseTwentyEight

theorem splitSheaf_rank (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {r : ℕ} (a : TangentSplittingProfile r) :
    IsLocallyFreeOfRank (splitSheaf P p a) r := by
  exact P1SplitBundles.splitSheaf_rank P p a

/-- Birkhoff--Grothendieck, in its algebraic direct-sum-of-invertible-sheaves
form. Primary reference: Hazewinkel--Martin, Journal of Pure and Applied
Algebra 25 (1982), 207--211, Theorem 4.1 on p.211.
The theorem is over an arbitrary field; it does not use the project's
marked point, splitting profile, or O(d) construction.
-/
theorem _root_.LeBrunSalamon.PublishedInputs.ProjectiveLine.splitsIntoInvertibleSheaves (k : Type) [Field k]
    (r : ℕ) (E : (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).Modules)
    (hE : IsLocallyFreeOfRank E r) :
    ∃ L : Fin r → (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).Modules,
      (∀ i, IsLocallyFreeOfRank (L i) 1) ∧ Nonempty (E ≅ ∐ L) := by
  sorry


/-- Choose the degree of every invertible summand and transport the actual
finite coproduct through those isomorphisms. The Picard-classification
prerequisite is a separately audited obligation. -/
theorem _root_.LeBrunSalamon.PublishedInputs.ProjectiveLineGeometry.birkhoffGrothendieck
    (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P) {r : ℕ}
    (E : AlgebraicVectorBundle ProjectiveLine r) :
    ∃ a : TangentSplittingProfile r, RealizesSplitting P p E a := by
  obtain ⟨L, hL, ⟨e⟩⟩ :=
    PublishedInputs.ProjectiveLine.splitsIntoInvertibleSheaves ℂ r E.sheaf E.locallyFree
  have hi (i : Fin r) :
      ∃ d : ℤ, Nonempty (L i ≅ (projectiveTwist P p d).sheaf) :=
    (projectiveLineBundle_classification P p ⟨L i, hL i⟩).exists
  choose d hd using hi
  refine ⟨⟨d⟩, ?_⟩
  exact ⟨e ≪≫ Sigma.mapIso (fun i => Classical.choice (hd i))⟩

/-- Project wrapper for Birkhoff--Grothendieck. -/
theorem birkhoffGrothendieck (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) {r : ℕ}
    (E : AlgebraicVectorBundle ProjectiveLine r) :
    ∃ a : TangentSplittingProfile r, RealizesSplitting P p E a :=
  LeBrunSalamon.PublishedInputs.ProjectiveLineGeometry.birkhoffGrothendieck
    P p E

theorem splitBundle_globallyGenerated_iff (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) {r : ℕ}
    (E : AlgebraicVectorBundle ProjectiveLine r) (a : TangentSplittingProfile r)
    (ha : RealizesSplitting P p E a) :
    IsGloballyGenerated E.sheaf ↔ a.IsFree := by
  exact P1SplitBundles.splitBundle_globallyGenerated_iff P p E a ha

def twoPointBundleEvaluation (P : ProjectiveLineOverC)
    (p q : ProjectiveLinePoint P) (E : OModule ProjectiveLine) :=
  fun s : AlgebraicSection E => (restrictSection p.map s, restrictSection q.map s)



/-- This is the Yoneda Ext^1(O,E)=0 formulation of H^1(E)=0. It uses actual short exact sequences of
O-modules. No opaque H1 number is inserted and no arbitrary extension is assumed to split. -/
def HasVanishingFirstCohomology {X : Scheme} (E : OModule X) : Prop :=
  ∀ (F : OModule X) (i : E ⟶ F) (p : F ⟶ structureModule X)
    (hz : i ≫ p = 0),
    (ShortComplex.mk i p hz).ShortExact →
      ∃ s : structureModule X ⟶ F, s ≫ p = 𝟙 (structureModule X)

end LeBrunSalamon.PhaseThirtyTwo

/- BEGIN UNCOMPILED continuation extension_splitting.lean.txt -/
/-!
Actual short-exact extensions and their two-open splitting obstruction.

Uncompiled continuation. Insert after the original PhaseThirtyTwo namespace
and after P1TwistSections. No quasi-coherence of an arbitrary middle term is
assumed. The existence of lifts of 1 on the two entire affine charts remains
an explicit hypothesis; all kernel factorization, correction, and gluing
maps are constructed from the given actual short exact sequence.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.PhaseThirtyTwo LeBrunSalamon.TwoChartSections

namespace LeBrunSalamon.ExtensionGluing

namespace UnitOnOpen

universe uExt

variable {X : Scheme.{uExt}} (M : OModule X) (U : X.Opens)

/-- The compatible restricted family of a section, without a small-universe restriction. -/
def sectionOver (s : SectionsOn M U) : (M.over U).sections where
  val V := M.val.map V.unop.hom.op s
  property := by
    intro V W i
    change M.val.map i.unop.left.op (M.val.map V.unop.hom.op s) =
      M.val.map W.unop.hom.op s
    have hi : V.unop.hom.op ≫ i.unop.left.op = W.unop.hom.op := by
      rw [← op_comp]
      exact congrArg Quiver.Hom.op (Over.w i.unop)
    rw [← PresheafOfModules.map_comp_apply, hi]

/-- Evaluation at the terminal slice object recovers the original open section. -/
def sectionsOverEquiv : (M.over U).sections ≃ SectionsOn M U where
  toFun s := s.val (op (Over.mk (𝟙 U)))
  invFun := sectionOver M U
  left_inv s := by
    ext V
    let i : V.unop ⟶ Over.mk (𝟙 U) := Over.homMk V.unop.hom
    exact s.property i.op
  right_inv s := by
    change M.val.map (𝟙 U).op s = s
    simp

/-- The same local unit comparison for schemes in every universe. -/
def unitOverHomEquiv :
    ((structureModule X).over U ⟶ M.over U) ≃ SectionsOn M U :=
  (M.over U).unitHomEquiv.trans (sectionsOverEquiv M U)

end UnitOnOpen

/-- A mono of module sheaves is injective on sections of every open. -/
theorem sectionMap_injective {X : Scheme} {E F : OModule X}
    (i : E ⟶ F) [Mono i] (U : X.Opens) : Function.Injective (i.app U) := by
  let ev := SheafOfModules.evaluation X.ringCatSheaf (op U)
  haveI : Mono (ev.map i) := inferInstance
  exact (ModuleCat.mono_iff_injective (ev.map i)).mp inferInstance

/-- Left exactness on sections is valid for arbitrary module sheaves. In
particular, no surjectivity on sections or quasi-coherence is asserted here. -/
theorem existsUnique_kernelSection {X : Scheme} {E F G : OModule X}
    (i : E ⟶ F) (p : F ⟶ G) (hz : i ≫ p = 0)
    (hex : (ShortComplex.mk i p hz).ShortExact) (U : X.Opens)
    (w : SectionsOn F U) (hw : p.app U w = 0) :
    ∃! a : SectionsOn E U, i.app U a = w := by
  let ev := SheafOfModules.evaluation X.ringCatSheaf (op U)
  letI : ev.Additive := by
    dsimp [ev, SheafOfModules.evaluation]
    infer_instance
  letI : PreservesFiniteLimits ev :=
    inferInstanceAs (PreservesFiniteLimits
      (SheafOfModules.evaluation X.ringCatSheaf (op U)))
  have he : ((ShortComplex.mk i p hz).map ev).Exact :=
    ((ShortComplex.mk i p hz).map ev).exact_of_f_is_kernel
      (KernelFork.mapIsLimit _ hex.fIsKernel ev)
  obtain ⟨a, ha⟩ :=
    (((ShortComplex.mk i p hz).map ev).moduleCat_exact_iff.mp he) w hw
  haveI : Mono i := hex.mono_f
  refine ⟨a, ha, ?_⟩
  intro b hb
  exact sectionMap_injective i U (hb.trans ha.symm)

/-- The unique preimage of a section in the actual kernel, using left
exactness of evaluation rather than an assumed local presentation. -/
def kernelSection {X : Scheme} {E F G : OModule X}
    (i : E ⟶ F) (p : F ⟶ G) (hz : i ≫ p = 0)
    (hex : (ShortComplex.mk i p hz).ShortExact) (U : X.Opens)
    (w : SectionsOn F U) (hw : p.app U w = 0) : SectionsOn E U :=
  Classical.choose (existsUnique_kernelSection i p hz hex U w hw).exists

@[simp]
theorem kernelSection_spec {X : Scheme} {E F G : OModule X}
    (i : E ⟶ F) (p : F ⟶ G) (hz : i ≫ p = 0)
    (hex : (ShortComplex.mk i p hz).ShortExact) (U : X.Opens)
    (w : SectionsOn F U) (hw : p.app U w = 0) :
    i.app U (kernelSection i p hz hex U w hw) = w :=
  Classical.choose_spec (existsUnique_kernelSection i p hz hex U w hw).exists

/-- The uniquely factored kernel section commutes with actual restriction.
This supplies the compatibility needed when local lift covers are refined. -/
theorem kernelSection_restrict {X : Scheme} {E F G : OModule X}
    (i : E ⟶ F) (p : F ⟶ G) (hz : i ≫ p = 0)
    (hex : (ShortComplex.mk i p hz).ShortExact) {U V : X.Opens} (h : U ≤ V)
    (w : SectionsOn F V) (hw : p.app V w = 0) :
    restrictValue E h (kernelSection i p hz hex V w hw) =
      kernelSection i p hz hex U (restrictValue F h w)
        (by rw [← restrictValue_map p h, hw, map_zero]) := by
  haveI : Mono i := hex.mono_f
  apply sectionMap_injective i U
  rw [← restrictValue_map, kernelSection_spec, kernelSection_spec]

/-- The actual two-open differential commutes with a sheaf morphism. -/
theorem pairDifference_map {X : Scheme} {E F : OModule X}
    (i : E ⟶ F) (U V : X.Opens) (ab : SectionsOn E U × SectionsOn E V) :
    i.app (U ⊓ V) (pairDifference E U V ab) =
      pairDifference F U V (i.app U ab.1, i.app V ab.2) := by
  change i.app (U ⊓ V)
      (restrictValue E inf_le_left ab.1 - restrictValue E inf_le_right ab.2) =
    restrictValue F inf_le_left (i.app U ab.1) -
      restrictValue F inf_le_right (i.app V ab.2)
  rw [map_sub, restrictValue_map, restrictValue_map]

@[simp]
theorem restrict_unit {X : Scheme} {U V : X.Opens} (h : U ≤ V) :
    restrictValue (structureModule X) h (1 : RingSections X V) =
      (1 : RingSections X U) := by
  change X.presheaf.map (homOfLE h).op 1 = 1
  exact map_one _

/-- An actual section of F on U lifting the unit section, equivalently the
value at 1 of a local right inverse of p. Existence is not built into the type. -/
def UnitLift {X : Scheme} {F : OModule X}
    (p : F ⟶ structureModule X) (U : X.Opens) :=
  {s : SectionsOn F U // p.app U s = (1 : RingSections X U)}

/-- Unit lifts restrict along every inclusion of opens. -/
def restrictUnitLift {X : Scheme} {F : OModule X}
    (p : F ⟶ structureModule X) {U V : X.Opens} (h : U ≤ V)
    (s : UnitLift p V) : UnitLift p U :=
  ⟨restrictValue F h s.val, by
    rw [← restrictValue_map p h, s.property, restrict_unit]⟩

/-- A lift of 1 determines an actual right inverse on the over site of U. -/
def localSectionOfUnitLift {X : Scheme} {F : OModule X}
    (p : F ⟶ structureModule X) (U : X.Opens) (s : UnitLift p U) :
    (structureModule X).over U ⟶ F.over U :=
  (UnitOnOpen.unitOverHomEquiv F U).symm s.val

@[simp]
theorem localSectionOfUnitLift_comp {X : Scheme} {F : OModule X}
    (p : F ⟶ structureModule X) (U : X.Opens) (s : UnitLift p U) :
    localSectionOfUnitLift p U s ≫ p.over U = 𝟙 ((structureModule X).over U) := by
  apply (UnitOnOpen.unitOverHomEquiv (structureModule X) U).injective
  change p.app U ((UnitOnOpen.unitOverHomEquiv F U)
    ((UnitOnOpen.unitOverHomEquiv F U).symm s.val)) = (1 : RingSections X U)
  rw [Equiv.apply_symm_apply]
  exact s.property

/-- Conversely an actual local right inverse is determined by a unit lift. -/
theorem localRightInverse_exists_iff_unitLift {X : Scheme} {F : OModule X}
    (p : F ⟶ structureModule X) (U : X.Opens) :
    (∃ s : (structureModule X).over U ⟶ F.over U,
      s ≫ p.over U = 𝟙 ((structureModule X).over U)) ↔ Nonempty (UnitLift p U) := by
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨⟨UnitOnOpen.unitOverHomEquiv F U s, ?_⟩⟩
    have he := congrArg (UnitOnOpen.unitOverHomEquiv (structureModule X) U) hs
    change p.app U (UnitOnOpen.unitOverHomEquiv F U s) = (1 : RingSections X U) at he
    exact he
  · rintro ⟨s⟩
    exact ⟨localSectionOfUnitLift p U s, localSectionOfUnitLift_comp p U s⟩

/-- A global lift of 1 is an actual right inverse in the original sheaf category. -/
def sectionOfUnitLift {X : Scheme} {F : OModule X}
    (p : F ⟶ structureModule X) (s : UnitLift p ⊤) :
    structureModule X ⟶ F := sectionFromValue s.val

@[simp]
theorem sectionOfUnitLift_comp {X : Scheme} {F : OModule X}
    (p : F ⟶ structureModule X) (s : UnitLift p ⊤) :
    sectionOfUnitLift p s ≫ p = 𝟙 (structureModule X) := by
  apply (sectionValue_bijective (structureModule X)).injective
  rw [sectionValue_comp]
  change p.app ⊤ (sectionValue (sectionFromValue s.val)) = (1 : RingSections X ⊤)
  rw [sectionFromValue_spec]
  exact s.property

/-- Conversely, a right inverse supplies the global lift of 1. -/
def unitLiftOfSection {X : Scheme} {F : OModule X}
    (p : F ⟶ structureModule X) (s : structureModule X ⟶ F)
    (hs : s ≫ p = 𝟙 (structureModule X)) : UnitLift p ⊤ :=
  ⟨sectionValue s, by
    change sectionValue (s ≫ p) = (1 : RingSections X ⊤)
    rw [hs] <;> rfl⟩

theorem rightInverse_exists_iff_unitLift {X : Scheme} {F : OModule X}
    (p : F ⟶ structureModule X) :
    (∃ s : structureModule X ⟶ F, s ≫ p = 𝟙 (structureModule X)) ↔
      Nonempty (UnitLift p ⊤) := by
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨unitLiftOfSection p s hs⟩
  · rintro ⟨s⟩
    exact ⟨sectionOfUnitLift p s, sectionOfUnitLift_comp p s⟩

/-- Applying p to the difference of two unit lifts gives zero on the entire overlap. -/
theorem unitLifts_difference_killed {X : Scheme} {F : OModule X}
    (p : F ⟶ structureModule X) (U V : X.Opens)
    (s : UnitLift p U) (t : UnitLift p V) :
    p.app (U ⊓ V) (pairDifference F U V (s.val, t.val)) = 0 := by
  rw [pairDifference_map, s.property, t.property]
  change restrictValue (structureModule X) inf_le_left (1 : RingSections X U) -
    restrictValue (structureModule X) inf_le_right (1 : RingSections X V) = 0
  rw [restrict_unit, restrict_unit, sub_self]

/-- The actual kernel-valued Cech cocycle of two chosen local unit lifts. -/
def extensionCocycle {X : Scheme} {E F : OModule X}
    (i : E ⟶ F) (p : F ⟶ structureModule X) (hz : i ≫ p = 0)
    (hex : (ShortComplex.mk i p hz).ShortExact) (U V : X.Opens)
    (s : UnitLift p U) (t : UnitLift p V) : SectionsOn E (U ⊓ V) :=
  kernelSection i p hz hex (U ⊓ V) (pairDifference F U V (s.val, t.val))
    (unitLifts_difference_killed p U V s t)

@[simp]
theorem extensionCocycle_spec {X : Scheme} {E F : OModule X}
    (i : E ⟶ F) (p : F ⟶ structureModule X) (hz : i ≫ p = 0)
    (hex : (ShortComplex.mk i p hz).ShortExact) (U V : X.Opens)
    (s : UnitLift p U) (t : UnitLift p V) :
    i.app (U ⊓ V) (extensionCocycle i p hz hex U V s t) =
      pairDifference F U V (s.val, t.val) :=
  kernelSection_spec i p hz hex _ _ _

/-- Subtracting an actual kernel section preserves the property of lifting 1. -/
def correctUnitLift {X : Scheme} {E F : OModule X}
    (i : E ⟶ F) (p : F ⟶ structureModule X) (hz : i ≫ p = 0)
    (U : X.Opens) (s : UnitLift p U) (a : SectionsOn E U) : UnitLift p U :=
  ⟨s.val - i.app U a, by
    rw [map_sub, s.property]
    have he := congrArg (fun f : E ⟶ structureModule X => f.app U a) hz
    change p.app U (i.app U a) = 0 at he
    rw [he, sub_zero]⟩

/-- Any two actual unit lifts on the same open differ by a section of the
original kernel. Thus all choices of lifts are covered by the correction law. -/
theorem exists_correction_of_unitLifts {X : Scheme} {E F : OModule X}
    (i : E ⟶ F) (p : F ⟶ structureModule X) (hz : i ≫ p = 0)
    (hex : (ShortComplex.mk i p hz).ShortExact) (U : X.Opens)
    (s t : UnitLift p U) :
    ∃ a : SectionsOn E U, correctUnitLift i p hz U s a = t := by
  have h : p.app U (s.val - t.val) = 0 := by
    rw [map_sub, s.property, t.property, sub_self]
  obtain ⟨a, ha, _⟩ := existsUnique_kernelSection i p hz hex U (s.val - t.val) h
  refine ⟨a, Subtype.ext ?_⟩
  change s.val - i.app U a = t.val
  rw [ha]
  abel

/-- The correction law holds in the actual middle sheaf, with the sign of
the original first-minus-second differential retained. -/
theorem pairDifference_correct {X : Scheme} {E F : OModule X}
    (i : E ⟶ F) (U V : X.Opens)
    (s : SectionsOn F U) (t : SectionsOn F V)
    (a : SectionsOn E U) (b : SectionsOn E V) :
    pairDifference F U V (s - i.app U a, t - i.app V b) =
      pairDifference F U V (s, t) - i.app (U ⊓ V) (pairDifference E U V (a, b)) := by
  rw [pairDifference_map]
  change restrictValue F inf_le_left (s - i.app U a) -
      restrictValue F inf_le_right (t - i.app V b) =
    (restrictValue F inf_le_left s - restrictValue F inf_le_right t) -
      (restrictValue F inf_le_left (i.app U a) -
        restrictValue F inf_le_right (i.app V b))
  rw [map_sub, map_sub]
  abel

/-- Correcting the local lifts changes the actual kernel-valued cocycle by
the actual differential of the corrections. -/
theorem extensionCocycle_correct {X : Scheme} {E F : OModule X}
    (i : E ⟶ F) (p : F ⟶ structureModule X) (hz : i ≫ p = 0)
    (hex : (ShortComplex.mk i p hz).ShortExact) (U V : X.Opens)
    (s : UnitLift p U) (t : UnitLift p V)
    (a : SectionsOn E U) (b : SectionsOn E V) :
    extensionCocycle i p hz hex U V
        (correctUnitLift i p hz U s a) (correctUnitLift i p hz V t b) =
      extensionCocycle i p hz hex U V s t - pairDifference E U V (a, b) := by
  haveI : Mono i := hex.mono_f
  apply sectionMap_injective i (U ⊓ V)
  rw [extensionCocycle_spec, map_sub, extensionCocycle_spec]
  exact pairDifference_correct i U V s.val t.val a b

/-- Compatible actual local lifts glue to a global lift of 1. -/
def glueUnitLifts {X : Scheme} {F : OModule X}
    (p : F ⟶ structureModule X) (U V : X.Opens) (hcover : U ⊔ V = ⊤)
    (s : UnitLift p U) (t : UnitLift p V)
    (h : PairCompatible F U V s.val t.val) : UnitLift p ⊤ :=
  ⟨gluePair F U V hcover ⟨(s.val, t.val), h⟩, by
    apply globalSection_ext (structureModule X) U V hcover
    · rw [restrictValue_map, gluePair_fst, s.property, restrict_unit]
    · rw [restrictValue_map, gluePair_snd, t.property, restrict_unit]⟩

/-- An actual primitive corrects the two unit lifts into a compatible pair
and produces an actual global right inverse. -/
theorem rightInverse_of_cocycle_primitive {X : Scheme} {E F : OModule X}
    (i : E ⟶ F) (p : F ⟶ structureModule X) (hz : i ≫ p = 0)
    (hex : (ShortComplex.mk i p hz).ShortExact) (U V : X.Opens)
    (hcover : U ⊔ V = ⊤) (s : UnitLift p U) (t : UnitLift p V)
    (ab : SectionsOn E U × SectionsOn E V)
    (hab : pairDifference E U V ab = extensionCocycle i p hz hex U V s t) :
    ∃ q : structureModule X ⟶ F, q ≫ p = 𝟙 (structureModule X) := by
  let s' := correctUnitLift i p hz U s ab.1
  let t' := correctUnitLift i p hz V t ab.2
  have hst : PairCompatible F U V s'.val t'.val := by
    apply sub_eq_zero.mp
    change pairDifference F U V
      (s.val - i.app U ab.1, t.val - i.app V ab.2) = 0
    rw [pairDifference_correct, hab, extensionCocycle_spec, sub_self]
  exact ⟨sectionOfUnitLift p (glueUnitLifts p U V hcover s' t' hst),
    sectionOfUnitLift_comp p _⟩

/-- A global splitting makes the cocycle of any chosen local unit lifts a
coboundary. This is the converse needed for an exact obstruction criterion. -/
theorem cocycle_primitive_of_rightInverse {X : Scheme} {E F : OModule X}
    (i : E ⟶ F) (p : F ⟶ structureModule X) (hz : i ≫ p = 0)
    (hex : (ShortComplex.mk i p hz).ShortExact) (U V : X.Opens)
    (s : UnitLift p U) (t : UnitLift p V)
    (q : structureModule X ⟶ F) (hq : q ≫ p = 𝟙 (structureModule X)) :
    ∃ ab : SectionsOn E U × SectionsOn E V,
      pairDifference E U V ab = extensionCocycle i p hz hex U V s t := by
  let g := unitLiftOfSection p q hq
  let u := restrictUnitLift p (show U ≤ ⊤ from le_top) g
  let v := restrictUnitLift p (show V ≤ ⊤ from le_top) g
  have hu : p.app U (s.val - u.val) = 0 := by
    rw [map_sub, s.property, u.property, sub_self]
  have hv : p.app V (t.val - v.val) = 0 := by
    rw [map_sub, t.property, v.property, sub_self]
  obtain ⟨a, ha, _⟩ := existsUnique_kernelSection i p hz hex U (s.val - u.val) hu
  obtain ⟨b, hb, _⟩ := existsUnique_kernelSection i p hz hex V (t.val - v.val) hv
  refine ⟨(a, b), ?_⟩
  haveI : Mono i := hex.mono_f
  apply sectionMap_injective i (U ⊓ V)
  rw [pairDifference_map, ha, hb, extensionCocycle_spec]
  change restrictValue F inf_le_left
        (s.val - restrictValue F (show U ≤ ⊤ from le_top) g.val) -
      restrictValue F inf_le_right
        (t.val - restrictValue F (show V ≤ ⊤ from le_top) g.val) =
    restrictValue F inf_le_left s.val - restrictValue F inf_le_right t.val
  rw [map_sub, map_sub, restrictValue_comp, restrictValue_comp]
  abel

/-- Exact equivalence for the original right-inverse problem, conditional
only on the two specified actual unit lifts. No extension group is redefined. -/
theorem rightInverse_iff_cocycle_primitive {X : Scheme} {E F : OModule X}
    (i : E ⟶ F) (p : F ⟶ structureModule X) (hz : i ≫ p = 0)
    (hex : (ShortComplex.mk i p hz).ShortExact) (U V : X.Opens)
    (hcover : U ⊔ V = ⊤) (s : UnitLift p U) (t : UnitLift p V) :
    (∃ q : structureModule X ⟶ F, q ≫ p = 𝟙 (structureModule X)) ↔
      Nonempty (Primitive E U V (extensionCocycle i p hz hex U V s t)) := by
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨ab, hab⟩ := cocycle_primitive_of_rightInverse i p hz hex U V s t q hq
    exact ⟨⟨ab, hab⟩⟩
  · rintro ⟨⟨ab, hab⟩⟩
    exact rightInverse_of_cocycle_primitive i p hz hex U V hcover s t ab hab

/-- Surjectivity of the actual Cech differential splits any extension that
has unit lifts on these two opens, with no hypothesis on its middle sheaf. -/
theorem rightInverse_of_pairDifference_surjective {X : Scheme} {E F : OModule X}
    (i : E ⟶ F) (p : F ⟶ structureModule X) (hz : i ≫ p = 0)
    (hex : (ShortComplex.mk i p hz).ShortExact) (U V : X.Opens)
    (hcover : U ⊔ V = ⊤) (s : UnitLift p U) (t : UnitLift p V)
    (hδ : Function.Surjective (pairDifference E U V)) :
    ∃ q : structureModule X ⟶ F, q ≫ p = 𝟙 (structureModule X) := by
  obtain ⟨ab, hab⟩ := hδ (extensionCocycle i p hz hex U V s t)
  exact rightInverse_of_cocycle_primitive i p hz hex U V hcover s t ab hab

open LeBrunSalamon.P1Charts

/-- The actual normal-form obstruction is independent of the chosen local
unit lifts. The proof computes their change inside the original kernel sheaf. -/
theorem twist_extension_normalForm_independent (P : ProjectiveLineOverC)
    (z : ProjectiveLinePoint P) (d : ℤ) (F : OModule ProjectiveLine)
    (i : (projectiveTwist P z d).sheaf ⟶ F) (p : F ⟶ structureModule ProjectiveLine)
    (hz : i ≫ p = 0) (hex : (ShortComplex.mk i p hz).ShortExact)
    (s s' : UnitLift p (chartOpen 0)) (t t' : UnitLift p (chartOpen 1)) :
    P1TwistSections.overlapNormalForm P z d
        (extensionCocycle i p hz hex (chartOpen 0) (chartOpen 1) s' t') =
      P1TwistSections.overlapNormalForm P z d
        (extensionCocycle i p hz hex (chartOpen 0) (chartOpen 1) s t) := by
  obtain ⟨a, ha⟩ := exists_correction_of_unitLifts i p hz hex (chartOpen 0) s s'
  obtain ⟨b, hb⟩ := exists_correction_of_unitLifts i p hz hex (chartOpen 1) t t'
  rw [← ha, ← hb, extensionCocycle_correct, map_sub,
    P1TwistSections.normalForm_difference, sub_zero]

/-- The actual extension splits exactly when the explicit overlap normal
form of its cocycle vanishes. The whole-chart unit lifts remain visible. -/
theorem twist_extension_splits_iff_normalForm_zero (P : ProjectiveLineOverC)
    (z : ProjectiveLinePoint P) (d : ℤ) (F : OModule ProjectiveLine)
    (i : (projectiveTwist P z d).sheaf ⟶ F) (p : F ⟶ structureModule ProjectiveLine)
    (hz : i ≫ p = 0) (hex : (ShortComplex.mk i p hz).ShortExact)
    (s : UnitLift p (chartOpen 0)) (t : UnitLift p (chartOpen 1)) :
    (∃ q : structureModule ProjectiveLine ⟶ F, q ≫ p = 𝟙 (structureModule ProjectiveLine)) ↔
      P1TwistSections.overlapNormalForm P z d
        (extensionCocycle i p hz hex (chartOpen 0) (chartOpen 1) s t) = 0 := by
  rw [rightInverse_iff_cocycle_primitive i p hz hex (chartOpen 0) (chartOpen 1)
    chartOpen_zero_sup_one s t]
  exact P1TwistSections.primitive_exists_iff_normalForm_zero P z d _

/-- In degrees at least -1, the constructed actual overlap homotopy removes
the obstruction for any extension equipped with lifts on the two full charts. -/
theorem twist_extension_splits_of_chartUnitLifts (P : ProjectiveLineOverC)
    (z : ProjectiveLinePoint P) (d : ℤ) (hd : -1 ≤ d) (F : OModule ProjectiveLine)
    (i : (projectiveTwist P z d).sheaf ⟶ F) (p : F ⟶ structureModule ProjectiveLine)
    (hz : i ≫ p = 0) (hex : (ShortComplex.mk i p hz).ShortExact)
    (s : UnitLift p (chartOpen 0)) (t : UnitLift p (chartOpen 1)) :
    ∃ q : structureModule ProjectiveLine ⟶ F, q ≫ p = 𝟙 (structureModule ProjectiveLine) := by
  apply (twist_extension_splits_iff_normalForm_zero P z d F i p hz hex s t).mpr
  exact P1TwistSections.normalForm_zero_of_ge_neg_one P z d hd _

/-- A precise reduction of the original Yoneda-vanishing predicate to its
remaining affine existence theorem. The hypothesis concerns every original
middle sheaf and is not asserted as an instance or automatically discharged. -/
theorem twist_firstCohomology_of_chartUnitLift_existence (P : ProjectiveLineOverC)
    (z : ProjectiveLinePoint P) (d : ℤ) (hd : -1 ≤ d)
    (hlift : ∀ (F : OModule ProjectiveLine)
      (i : (projectiveTwist P z d).sheaf ⟶ F) (p : F ⟶ structureModule ProjectiveLine)
      (hz : i ≫ p = 0), (ShortComplex.mk i p hz).ShortExact →
        Nonempty (UnitLift p (chartOpen 0)) ∧ Nonempty (UnitLift p (chartOpen 1))) :
    HasVanishingFirstCohomology (projectiveTwist P z d).sheaf := by
  intro F i p hz hex
  obtain ⟨⟨s⟩, ⟨t⟩⟩ := hlift F i p hz hex
  exact twist_extension_splits_of_chartUnitLifts P z d hd F i p hz hex s t

end LeBrunSalamon.ExtensionGluing

end
/- END UNCOMPILED continuation extension_splitting.lean.txt -/

/- BEGIN UNCOMPILED continuation local_extension_splitting.lean.txt -/
/-!
Local and affine splitting of actual extensions by the structure sheaf.

Uncompiled continuation. Insert after ExtensionGluing. Epimorphisms here are
epimorphisms of the original module sheaves. Local freeness of an arbitrary
middle term is derived from the short exact sequence, not assumed.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open TopologicalSpace
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.SheafTensor LeBrunSalamon.TwoChartSections
open LeBrunSalamon.ExtensionGluing

namespace LeBrunSalamon.LocalExtensionSplitting

universe uLE vLE

/-- Forgetting the module structure preserves finite colimits of sheaves.
This follows by passing through the reflective sheafification adjunction;
preservation of limits or faithfulness alone would not suffice. -/
theorem toSheaf_preservesFiniteColimits (X : Scheme.{uLE}) :
    PreservesFiniteColimits (SheafOfModules.toSheaf.{uLE} X.ringCatSheaf) where
  preservesFiniteColimits J _ _ := by
    apply ((PresheafOfModules.sheafificationAdjunction.{uLE} (𝟙 X.ringCatSheaf.obj)).preservesColimitsOfShape_iff
      (SheafOfModules.toSheaf X.ringCatSheaf) J).mpr
    change PreservesColimitsOfShape J
      (PresheafOfModules.toPresheaf.{uLE} X.ringCatSheaf.obj ⋙
        presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{uLE})
    infer_instance

/-- An actual epimorphism of module sheaves is locally surjective on the
underlying additive presheaves. The intermediate preservation of epis is
justified by the finite-colimit theorem above. -/
theorem epi_isLocallySurjective {X : Scheme} {E F : OModule X}
    (p : E ⟶ F) [Epi p] : TopCat.Presheaf.IsLocallySurjective p.mapPresheaf := by
  letI := toSheaf_preservesFiniteColimits X
  haveI : Epi ((SheafOfModules.toSheaf X.ringCatSheaf).map p) := inferInstance
  exact (TopCat.Sheaf.isLocallySurjective_iff_epi
    ((SheafOfModules.toSheaf X.ringCatSheaf).map p)).mpr inferInstance

/-- The local-surjectivity test is equivalent to the original categorical
epimorphism condition, without a quasi-coherence restriction. -/
theorem epi_iff_isLocallySurjective {X : Scheme} {E F : OModule X}
    (p : E ⟶ F) : Epi p ↔ TopCat.Presheaf.IsLocallySurjective p.mapPresheaf := by
  constructor
  · intro h
    letI := h
    exact epi_isLocallySurjective p
  · intro h
    haveI : Epi ((SheafOfModules.toSheaf X.ringCatSheaf).map p) :=
      (TopCat.Sheaf.isLocallySurjective_iff_epi
        ((SheafOfModules.toSheaf X.ringCatSheaf).map p)).mp h
    exact (SheafOfModules.toSheaf X.ringCatSheaf).epi_of_epi_map inferInstance

/-- A section of the quotient of an actual epi lifts on a neighborhood of
each specified point, inside the originally specified open. -/
theorem exists_local_preimage {X : Scheme} {E F : OModule X}
    (p : E ⟶ F) [Epi p] (U : X.Opens) (s : SectionsOn F U)
    (x : X) (hx : x ∈ U) :
    ∃ (V : X.Opens) (hVU : V ≤ U) (t : SectionsOn E V),
      x ∈ V ∧ p.app V t = restrictValue F hVU s := by
  have h := (TopCat.Presheaf.isLocallySurjective_iff p.mapPresheaf).mp
    (epi_isLocallySurjective p)
  obtain ⟨V, hVU, ⟨t, ht⟩, hxV⟩ := h U s x hx
  exact ⟨V, hVU, t, hxV, ht⟩

/-- The local lift of the actual unit section gives an actual UnitLift.
This is neighborhood existence, not yet existence on an entire affine open. -/
theorem exists_unitLift_neighborhood {X : Scheme} {F : OModule X}
    (p : F ⟶ structureModule X) [Epi p] (U : X.Opens)
    (x : X) (hx : x ∈ U) :
    ∃ V : X.Opens, V ≤ U ∧ x ∈ V ∧ Nonempty (UnitLift p V) := by
  obtain ⟨V, hVU, t, hxV, ht⟩ := exists_local_preimage p U
    (1 : RingSections X U) x hx
  refine ⟨V, hVU, hxV, ⟨⟨t, ?_⟩⟩⟩
  rw [ht, restrict_unit]

/-- Neighborhood unit lifts are genuine local right inverses in the over
site of the original module sheaves. -/
theorem exists_local_rightInverse {X : Scheme} {F : OModule X}
    (p : F ⟶ structureModule X) [Epi p] (U : X.Opens)
    (x : X) (hx : x ∈ U) :
    ∃ V : X.Opens, V ≤ U ∧ x ∈ V ∧
      ∃ s : (structureModule X).over V ⟶ F.over V,
        s ≫ p.over V = 𝟙 ((structureModule X).over V) := by
  obtain ⟨V, hVU, hxV, ⟨s⟩⟩ := exists_unitLift_neighborhood p U x hx
  exact ⟨V, hVU, hxV, localSectionOfUnitLift p V s,
    localSectionOfUnitLift_comp p V s⟩

/-- Conversely, two actual unit lifts on a covering pair make the quotient
map epi. Cancellation is tested on actual maps from the structure sheaf. -/
theorem epi_of_unitLifts {X : Scheme} {F : OModule X}
    (p : F ⟶ structureModule X) (U V : X.Opens) (hcover : U ⊔ V = ⊤)
    (s : UnitLift p U) (t : UnitLift p V) : Epi p := by
  refine ⟨?_⟩
  intro Z f g hfg
  apply (sectionValue_bijective Z).injective
  have hlocal (W : X.Opens) (a : UnitLift p W) :
      restrictValue Z (show W ≤ ⊤ from le_top) (sectionValue f) =
        restrictValue Z (show W ≤ ⊤ from le_top) (sectionValue g) := by
    have he := congrArg (fun k : F ⟶ Z => k.app W a.val) hfg
    change f.app W (p.app W a.val) = g.app W (p.app W a.val) at he
    rw [a.property] at he
    have hf := sheafHom_naturality f (homOfLE (show W ≤ ⊤ from le_top))
      (1 : RingSections X ⊤)
    have hg := sheafHom_naturality g (homOfLE (show W ≤ ⊤ from le_top))
      (1 : RingSections X ⊤)
    change Z.presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op
        (f.app ⊤ (1 : RingSections X ⊤)) =
      f.app W (X.presheaf.map (homOfLE le_top).op (1 : RingSections X ⊤)) at hf
    change Z.presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op
        (g.app ⊤ (1 : RingSections X ⊤)) =
      g.app W (X.presheaf.map (homOfLE le_top).op (1 : RingSections X ⊤)) at hg
    have h1 : X.presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op
        (1 : RingSections X ⊤) = (1 : RingSections X W) := map_one _
    rw [h1] at hf hg
    exact hf.trans (he.trans hg.symm)
  exact globalSection_ext Z U V hcover _ _ (hlocal U s) (hlocal V t)

/-- Restriction to an over site preserves finite limits. It is the genuine
continuous pushforward along the forgetful functor from the over category. -/
theorem over_preservesFiniteLimits (X : Scheme.{uLE}) (U : X.Opens) :
    PreservesFiniteLimits (SheafOfModules.overFunctor.{vLE} X.ringCatSheaf U) := by
  let G := SheafOfModules.forget.{vLE} (X.ringCatSheaf.over U) ⋙
    PresheafOfModules.toPresheaf (X.ringCatSheaf.over U).obj
  haveI : PreservesFiniteLimits
      (SheafOfModules.overFunctor.{vLE} X.ringCatSheaf U ⋙ G) := by
    change PreservesFiniteLimits
      ((SheafOfModules.forget.{vLE} X.ringCatSheaf ⋙
        PresheafOfModules.toPresheaf X.ringCatSheaf.obj) ⋙
          (Functor.whiskeringLeft _ _ _).obj (Over.forget U).op)
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves _ G

/-- Restriction on the over site acts componentwise on sums of sheaf morphisms. -/
instance overFunctor_additive {C : Type*} [Category* C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{uLE}) (U : C) :
    (SheafOfModules.overFunctor.{vLE} R U).Additive where
  map_add := rfl

/-- The actual over-site adjunction is available at every scheme universe. -/
instance overFunctor_leftAdjoint {C : Type*} [Category* C] [HasBinaryProducts C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{uLE}) (U : C) :
    (SheafOfModules.overFunctor.{vLE} R U).IsLeftAdjoint :=
  (SheafOfModules.overPushforwardOverAdj (R := R) U).isLeftAdjoint

/-- The componentwise over-site restriction preserves the actual zero morphisms. -/
instance overFunctor_preservesZeroMorphisms {C : Type*} [Category* C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{uLE}) (U : C) :
    (SheafOfModules.overFunctor.{vLE} R U).PreservesZeroMorphisms where
  map_zero _ _ := rfl

/-- Binary biproducts here follow directly from finite limits and additivity. -/
instance sheafModules_hasBinaryBiproducts {C : Type*} [Category* C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{uLE}) :
    HasBinaryBiproducts (SheafOfModules.{vLE} R) :=
  HasBinaryBiproducts.of_hasBinaryProducts

/-- The original short exact sequence remains short exact on the over site.
The existing over-site left adjunction supplies preservation of colimits. -/
theorem shortExact_over {X : Scheme.{uLE}} {E F G : OModule X}
    (i : E ⟶ F) (p : F ⟶ G) (hz : i ≫ p = 0)
    (hex : (ShortComplex.mk i p hz).ShortExact) (U : X.Opens) :
    letI : (SheafOfModules.overFunctor.{uLE} X.ringCatSheaf U).PreservesZeroMorphisms :=
      overFunctor_preservesZeroMorphisms X.ringCatSheaf U
    ((ShortComplex.mk i p hz).map
      (SheafOfModules.overFunctor.{uLE} X.ringCatSheaf U)).ShortExact := by
  letI : (SheafOfModules.overFunctor.{uLE} X.ringCatSheaf U).PreservesZeroMorphisms :=
    overFunctor_preservesZeroMorphisms X.ringCatSheaf U
  letI := over_preservesFiniteLimits X U
  letI : (SheafOfModules.overFunctor X.ringCatSheaf U).IsLeftAdjoint :=
    (SheafOfModules.overPushforwardOverAdj (R := X.ringCatSheaf) U).isLeftAdjoint
  exact hex.map_of_exact (SheafOfModules.overFunctor X.ringCatSheaf U)

/-- The actual local right inverse determines the complementary kernel
retraction and a splitting of the mapped short exact sequence. -/
def splittingOfUnitLift {X : Scheme.{uLE}} {E F : OModule X}
    (i : E ⟶ F) (p : F ⟶ structureModule X) (hz : i ≫ p = 0)
    (hex : (ShortComplex.mk i p hz).ShortExact) (U : X.Opens) (s : UnitLift p U) :
    letI : (SheafOfModules.overFunctor.{uLE} X.ringCatSheaf U).PreservesZeroMorphisms :=
      overFunctor_preservesZeroMorphisms X.ringCatSheaf U
    ((ShortComplex.mk i p hz).map
      (SheafOfModules.overFunctor.{uLE} X.ringCatSheaf U)).Splitting := by
  letI : (SheafOfModules.overFunctor.{uLE} X.ringCatSheaf U).PreservesZeroMorphisms :=
    overFunctor_preservesZeroMorphisms X.ringCatSheaf U
  exact ShortComplex.Splitting.ofExactOfSection _ (shortExact_over i p hz hex U).exact
    (localSectionOfUnitLift p U s) (localSectionOfUnitLift_comp p U s)
    (shortExact_over i p hz hex U).mono_f

/-- An actual isomorphism from the local middle sheaf to kernel plus unit,
including the original quotient and kernel maps through the splitting data. -/
def localSplitIso {X : Scheme.{uLE}} {E F : OModule X}
    (i : E ⟶ F) (p : F ⟶ structureModule X) (hz : i ≫ p = 0)
    (hex : (ShortComplex.mk i p hz).ShortExact) (U : X.Opens) (s : UnitLift p U) :
    letI : HasBinaryBiproduct (E.over U) ((structureModule X).over U) :=
      HasBinaryBiproduct.of_hasBinaryProduct _ _
    F.over U ≅ E.over U ⊞ (structureModule X).over U := by
  letI : HasBinaryBiproduct (E.over U) ((structureModule X).over U) :=
    HasBinaryBiproduct.of_hasBinaryProduct _ _
  exact (splittingOfUnitLift i p hz hex U s).isoBinaryBiproduct

/-- Adding the unit sheaf adds one to a specified finite free basis. -/
def freeSuccessorIso (X : Scheme) (U : X.Opens) (r : ℕ) :
    SheafOfModules.free (R := X.ringCatSheaf.over U) (Fin (r + 1)) ≅
      SheafOfModules.free (R := X.ringCatSheaf.over U) (Fin r) ⊞
        (structureModule X).over U :=
  freeReindexIso _ (finSumFinEquiv : Fin r ⊕ Fin 1 ≃ Fin (r + 1)).symm ≪≫
    (SheafOfModules.freeSumIso (R := X.ringCatSheaf.over U) (Fin r) (Fin 1)).symm ≪≫
    coprod.mapIso (Iso.refl _)
      (coproductUniqueIso (fun _ : Fin 1 => SheafOfModules.unit (X.ringCatSheaf.over U))) ≪≫
    (biprod.isoCoprod _ _).symm

/-- A free kernel frame and an actual unit lift give a free frame of the
original middle sheaf, with one additional basis vector. -/
def freeFrameOfUnitLift {X : Scheme} {E F : OModule X}
    (i : E ⟶ F) (p : F ⟶ structureModule X) (hz : i ≫ p = 0)
    (hex : (ShortComplex.mk i p hz).ShortExact) (U : X.Opens) {r : ℕ}
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) (Fin r) ≅ E.over U)
    (s : UnitLift p U) :
    SheafOfModules.free (R := X.ringCatSheaf.over U) (Fin (r + 1)) ≅ F.over U :=
  freeSuccessorIso X U r ≪≫ biprod.mapIso e (Iso.refl _) ≪≫
    (localSplitIso i p hz hex U s).symm

/-- Every point has a genuine free neighborhood in an arbitrary extension
of the unit by a locally free kernel. No property of the middle term is assumed. -/
theorem exists_free_neighborhood {X : Scheme} {E F : OModule X} {r : ℕ}
    (hE : IsLocallyFreeOfRank E r) (i : E ⟶ F) (p : F ⟶ structureModule X)
    (hz : i ≫ p = 0) (hex : (ShortComplex.mk i p hz).ShortExact) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ Nonempty
      (SheafOfModules.free (R := X.ringCatSheaf.over U) (Fin (r + 1)) ≅ F.over U) := by
  obtain ⟨q, hq, hr⟩ := hE
  letI := hq
  haveI : Epi p := hex.epi_g
  obtain ⟨a, hxa⟩ := ((Opens.coversTop_iff X q.X).mp q.coversTop).exists_mem x
  obtain ⟨U, hUa, hxU, ⟨s⟩⟩ := exists_unitLift_neighborhood p (q.X a) x hxa
  exact ⟨U, hxU, ⟨freeFrameOfUnitLift i p hz hex U
    (freeTrivializationRestrict (homOfLE hUa) (localBasisTrivialization q hr a)) s⟩⟩

/-- The original arbitrary middle term is locally free of the derived rank.
The neighborhood frames are assembled into the project's original rank predicate. -/
theorem middle_locallyFree {X : Scheme} {E F : OModule X} {r : ℕ}
    (hE : IsLocallyFreeOfRank E r) (i : E ⟶ F) (p : F ⟶ structureModule X)
    (hz : i ≫ p = 0) (hex : (ShortComplex.mk i p hz).ShortExact) :
    IsLocallyFreeOfRank F (r + 1) := by
  choose U hxU he using exists_free_neighborhood hE i p hz hex
  have hU : (Opens.grothendieckTopology X).CoversTop U := by
    apply (Opens.coversTop_iff X U).mpr
    change iSup U = ⊤
    apply eq_top_iff.mpr
    intro x hx
    exact Opens.mem_iSup.mpr ⟨x, hxU x⟩
  exact rank_of_free_cover F (r + 1) U hU (fun x => (he x).some)

/-- A witness of the project's fixed-rank predicate supplies mathlib's
locally-free and quasi-coherent properties. -/
theorem quasicoherent_of_locallyFreeRank {X : Scheme} {E : OModule X} {r : ℕ}
    (hE : IsLocallyFreeOfRank E r) : E.IsQuasicoherent := by
  obtain ⟨q, hq, _⟩ := hE
  letI := hq
  letI : E.IsLocallyFree := q.isLocallyFree
  infer_instance

/-- Quasi-coherence of the original middle term is a consequence of the
actual extension and the kernel's local freeness. -/
theorem middle_quasicoherent {X : Scheme} {E F : OModule X} {r : ℕ}
    (hE : IsLocallyFreeOfRank E r) (i : E ⟶ F) (p : F ⟶ structureModule X)
    (hz : i ≫ p = 0) (hex : (ShortComplex.mk i p hz).ShortExact) :
    F.IsQuasicoherent :=
  quasicoherent_of_locallyFreeRank (middle_locallyFree hE i p hz hex)

/-- On an actual spectrum, an epi between quasi-coherent module sheaves is
surjective on global sections. The proof reflects the ambient epi into the
full quasi-coherent subcategory and applies the actual tilde equivalence. -/
theorem spec_sectionMap_surjective {R : CommRingCat} {E F : OModule (Spec R)}
    [E.IsQuasicoherent] [F.IsQuasicoherent] (p : E ⟶ F) [Epi p] :
    Function.Surjective (p.app ⊤) := by
  let Q := SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf
  let E' : Q.FullSubcategory := ⟨E, inferInstance⟩
  let F' : Q.FullSubcategory := ⟨F, inferInstance⟩
  let p' : E' ⟶ F' := ObjectProperty.homMk p
  haveI : Epi p' := Q.ι.epi_of_epi_map (by change Epi p; infer_instance)
  haveI : Epi ((tildeEquiv (R := R)).inverse.map p') := inferInstance
  change Function.Surjective ((tildeEquiv (R := R)).inverse.map p')
  exact (ModuleCat.epi_iff_surjective ((tildeEquiv (R := R)).inverse.map p')).mp
    inferInstance

/-- Surjectivity holds on every entire affine open. Restriction along its
canonical spectrum chart preserves the actual epi and quasi-coherence. -/
theorem affine_sectionMap_surjective {X : Scheme} {E F : OModule X}
    [E.IsQuasicoherent] [F.IsQuasicoherent] (p : E ⟶ F) [Epi p]
    (U : X.Opens) (hU : IsAffineOpen U) : Function.Surjective (p.app U) := by
  haveI : Epi ((Scheme.Modules.restrictFunctor hU.fromSpec).map p) := inferInstance
  have h := spec_sectionMap_surjective ((Scheme.Modules.restrictFunctor hU.fromSpec).map p)
  change Function.Surjective (p.app (hU.fromSpec ''ᵁ ⊤)) at h
  have himage : hU.fromSpec ''ᵁ ⊤ = U :=
    (Scheme.Hom.image_top_eq_opensRange _).trans hU.opensRange_fromSpec
  rw [himage] at h
  exact h

/-- An actual epi from a quasi-coherent module sheaf to the structure sheaf
has a unit lift on the entire specified affine open. -/
theorem affine_unitLift_of_epi {X : Scheme} {F : OModule X}
    [F.IsQuasicoherent] (p : F ⟶ structureModule X) [Epi p]
    (U : X.Opens) (hU : IsAffineOpen U) : Nonempty (UnitLift p U) := by
  letI : (structureModule X).IsQuasicoherent :=
    quasicoherent_of_locallyFreeRank (structureModule_rank X)
  obtain ⟨s, hs⟩ := affine_sectionMap_surjective p U hU (1 : RingSections X U)
  exact ⟨⟨s, hs⟩⟩

/-- The whole-affine lifting theorem for every original middle module
sheaf. Its quasi-coherence is derived from the short exact sequence and the
specified rank of the kernel, so the original Yoneda quantifier is retained. -/
theorem affine_unitLift_of_shortExact {X : Scheme} {E F : OModule X} {r : ℕ}
    (hE : IsLocallyFreeOfRank E r) (i : E ⟶ F) (p : F ⟶ structureModule X)
    (hz : i ≫ p = 0) (hex : (ShortComplex.mk i p hz).ShortExact)
    (U : X.Opens) (hU : IsAffineOpen U) : Nonempty (UnitLift p U) := by
  letI : F.IsQuasicoherent := middle_quasicoherent hE i p hz hex
  haveI : Epi p := hex.epi_g
  exact affine_unitLift_of_epi p U hU

/-- The whole-affine lift gives the actual splitting of the extension on
that affine over site. This theorem is unconditional on the middle sheaf. -/
theorem affine_rightInverse_of_shortExact {X : Scheme} {E F : OModule X} {r : ℕ}
    (hE : IsLocallyFreeOfRank E r) (i : E ⟶ F) (p : F ⟶ structureModule X)
    (hz : i ≫ p = 0) (hex : (ShortComplex.mk i p hz).ShortExact)
    (U : X.Opens) (hU : IsAffineOpen U) :
    ∃ s : (structureModule X).over U ⟶ F.over U,
      s ≫ p.over U = 𝟙 ((structureModule X).over U) :=
  (localRightInverse_exists_iff_unitLift p U).mpr
    (affine_unitLift_of_shortExact hE i p hz hex U hU)

/-- The original Yoneda-vanishing predicate follows from surjectivity of
the actual two-open differential on an affine covering pair. All extensions
quantified by that predicate acquire chart lifts through the theorem above. -/
theorem firstCohomology_of_affine_pair {X : Scheme} {E : OModule X} {r : ℕ}
    (hE : IsLocallyFreeOfRank E r) (U V : X.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hcover : U ⊔ V = ⊤)
    (hδ : Function.Surjective (pairDifference E U V)) :
    HasVanishingFirstCohomology E := by
  intro F i p hz hex
  obtain ⟨s⟩ := affine_unitLift_of_shortExact hE i p hz hex U hU
  obtain ⟨t⟩ := affine_unitLift_of_shortExact hE i p hz hex V hV
  exact rightInverse_of_pairDifference_surjective i p hz hex U V hcover s t hδ

/-- In degree at least -1, every original extension of O by the actual
projective twist splits. The previously explicit whole-chart lifting
hypothesis is now discharged for every arbitrary original middle sheaf. -/
theorem twist_firstCohomology_of_ge_neg_one (P : ProjectiveLineOverC)
    (z : ProjectiveLinePoint P) (d : ℤ) (hd : -1 ≤ d) :
    HasVanishingFirstCohomology (projectiveTwist P z d).sheaf := by
  apply twist_firstCohomology_of_chartUnitLift_existence P z d hd
  intro F i p hz hex
  exact ⟨affine_unitLift_of_shortExact (projectiveTwist P z d).locallyFree
      i p hz hex (P1Charts.chartOpen 0) (P1Charts.chartOpen_affine 0),
    affine_unitLift_of_shortExact (projectiveTwist P z d).locallyFree
      i p hz hex (P1Charts.chartOpen 1) (P1Charts.chartOpen_affine 1)⟩

end LeBrunSalamon.LocalExtensionSplitting

end
/- END UNCOMPILED continuation local_extension_splitting.lean.txt -/

/- BEGIN UNCOMPILED continuation extension_realization.lean.txt -/
/-!
Realizing an actual two-open cocycle by an actual module-sheaf extension.

Uncompiled continuation. For a section c of E on U ∩ V, the middle sheaf
has sections (a,b,r) with b| - a| = r| • c|. This sign makes the difference
of the specified U and V unit lifts equal the image of c, in the existing
first-minus-second convention of ExtensionGluing.extensionCocycle.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.PhaseThirtyTwo LeBrunSalamon.TwoChartSections

namespace LeBrunSalamon.ExtensionRealization

universe uER

/-- Restriction of regular functions as a ring homomorphism. -/
def ringRestrict {X : Scheme} {A B : X.Opens} (h : A ≤ B) :
    RingSections X B →+* RingSections X A :=
  (X.presheaf.map (homOfLE h).op).hom

@[simp]
theorem ringRestrict_refl {X : Scheme} (A : X.Opens) (r : RingSections X A) :
    ringRestrict (le_refl A) r = r := by
  change X.presheaf.map (𝟙 (op A)) r = r
  simp

@[simp]
theorem ringRestrict_comp {X : Scheme} {A B C : X.Opens}
    (hAB : A ≤ B) (hBC : B ≤ C) (r : RingSections X C) :
    ringRestrict hAB (ringRestrict hBC r) = ringRestrict (hAB.trans hBC) r := by
  change X.presheaf.map (homOfLE hAB).op
    (X.presheaf.map (homOfLE hBC).op r) = _
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp] <;> rfl

/-- The semilinearity used below is the original module presheaf law. -/
theorem restrictValue_smul {X : Scheme} (E : OModule X) {A B : X.Opens}
    (h : A ≤ B) (r : RingSections X B) (s : SectionsOn E B) :
    restrictValue E h (r • s) = ringRestrict h r • restrictValue E h s :=
  E.val.map_smul (homOfLE h).op r s

/-- Sections on W ∩ A, regarded as a module over the functions on W by
the actual restriction homomorphism. -/
abbrev localModule {X : Scheme} (E : OModule X) (A W : X.Opens) :
    ModuleCat (RingSections X W) :=
  (ModuleCat.restrictScalars (ringRestrict (inf_le_left : W ⊓ A ≤ W))).obj
    (E.val.obj (op (W ⊓ A)))

abbrev RawValues {X : Scheme} (E : OModule X) (U V W : X.Opens) :=
  localModule E U W × localModule E V W × RingSections X W

set_option backward.isDefEq.respectTransparency.types false in
/-- The matching condition is a submodule of actual local section triples. -/
def values {X : Scheme} (E : OModule X) (U V : X.Opens)
    (c : SectionsOn E (U ⊓ V)) (W : X.Opens) :
    Submodule (RingSections X W) (RawValues E U V W) where
  carrier := {t |
    restrictValue E (inf_le_inf le_rfl inf_le_right : W ⊓ (U ⊓ V) ≤ W ⊓ V) t.2.1 -
      restrictValue E (inf_le_inf le_rfl inf_le_left : W ⊓ (U ⊓ V) ≤ W ⊓ U) t.1 =
        ringRestrict (inf_le_left : W ⊓ (U ⊓ V) ≤ W) t.2.2 •
          restrictValue E inf_le_right c}
  zero_mem' := by
    change restrictValue E
        (inf_le_inf le_rfl inf_le_right : W ⊓ (U ⊓ V) ≤ W ⊓ V)
          (0 : SectionsOn E (W ⊓ V)) -
      restrictValue E (inf_le_inf le_rfl inf_le_left : W ⊓ (U ⊓ V) ≤ W ⊓ U)
          (0 : SectionsOn E (W ⊓ U)) =
        ringRestrict (inf_le_left : W ⊓ (U ⊓ V) ≤ W) (0 : RingSections X W) •
          restrictValue E inf_le_right c
    simp only [map_zero, sub_self, zero_smul]
  add_mem' := by
    intro t s ht hs
    change restrictValue E _ (t.2.1 + s.2.1) -
      restrictValue E _ (t.1 + s.1) = ringRestrict _ (t.2.2 + s.2.2) • _
    rw [map_add, map_add, map_add, add_smul, ← ht, ← hs]
    abel
  smul_mem' := by
    intro r t ht
    change restrictValue E _ (ringRestrict (inf_le_left : W ⊓ V ≤ W) r • t.2.1) -
      restrictValue E _ (ringRestrict (inf_le_left : W ⊓ U ≤ W) r • t.1) =
        ringRestrict _ (r * t.2.2) • _
    rw [restrictValue_smul, restrictValue_smul, ringRestrict_comp,
      ringRestrict_comp, map_mul, mul_smul, ← smul_sub, ht]

theorem matching_equation {X : Scheme} (E : OModule X) (U V : X.Opens)
    (c : SectionsOn E (U ⊓ V)) (W : X.Opens) (s : values E U V c W) :
    restrictValue E (inf_le_inf le_rfl inf_le_right : W ⊓ (U ⊓ V) ≤ W ⊓ V) s.val.2.1 -
      restrictValue E (inf_le_inf le_rfl inf_le_left : W ⊓ (U ⊓ V) ≤ W ⊓ U) s.val.1 =
        ringRestrict (inf_le_left : W ⊓ (U ⊓ V) ≤ W) s.val.2.2 •
          restrictValue E inf_le_right c := s.property

/-- Restrict all three actual section components. The matching equation
restricts by the semilinearity of E and functoriality of its presheaf. -/
def valueRestriction {X : Scheme} (E : OModule X) (U V : X.Opens)
    (c : SectionsOn E (U ⊓ V)) {A B : X.Opens} (h : A ≤ B) :
    values E U V c B →+ values E U V c A where
  toFun s := ⟨(restrictValue E (inf_le_inf h le_rfl) s.val.1,
    restrictValue E (inf_le_inf h le_rfl) s.val.2.1, ringRestrict h s.val.2.2), by
    change restrictValue E _ (restrictValue E _ s.val.2.1) -
      restrictValue E _ (restrictValue E _ s.val.1) =
        ringRestrict _ (ringRestrict h s.val.2.2) • restrictValue E _ c
    have hs := congrArg
      (restrictValue E (inf_le_inf h le_rfl : A ⊓ (U ⊓ V) ≤ B ⊓ (U ⊓ V)))
      (matching_equation E U V c B s)
    simpa only [map_sub, restrictValue_smul, restrictValue_comp, ringRestrict_comp]
      using hs⟩
  map_zero' := by
    apply Subtype.ext
    exact Prod.ext (map_zero _) (Prod.ext (map_zero _) (map_zero _))
  map_add' s t := by
    apply Subtype.ext
    exact Prod.ext (map_add _ _ _) (Prod.ext (map_add _ _ _) (map_add _ _ _))

@[simp]
theorem valueRestriction_fst {X : Scheme} (E : OModule X) (U V : X.Opens)
    (c : SectionsOn E (U ⊓ V)) {A B : X.Opens} (h : A ≤ B)
    (s : values E U V c B) :
    (valueRestriction E U V c h s).val.1 =
      restrictValue E (inf_le_inf h le_rfl) s.val.1 := rfl

@[simp]
theorem valueRestriction_snd {X : Scheme} (E : OModule X) (U V : X.Opens)
    (c : SectionsOn E (U ⊓ V)) {A B : X.Opens} (h : A ≤ B)
    (s : values E U V c B) :
    (valueRestriction E U V c h s).val.2.1 =
      restrictValue E (inf_le_inf h le_rfl) s.val.2.1 := rfl

@[simp]
theorem valueRestriction_quot {X : Scheme} (E : OModule X) (U V : X.Opens)
    (c : SectionsOn E (U ⊓ V)) {A B : X.Opens} (h : A ≤ B)
    (s : values E U V c B) :
    (valueRestriction E U V c h s).val.2.2 = ringRestrict h s.val.2.2 := rfl

set_option backward.isDefEq.respectTransparency.types false in
theorem valueRestriction_smul {X : Scheme} (E : OModule X) (U V : X.Opens)
    (c : SectionsOn E (U ⊓ V)) {A B : X.Opens} (h : A ≤ B)
    (r : RingSections X B) (s : values E U V c B) :
    valueRestriction E U V c h (r • s) =
      ringRestrict h r • valueRestriction E U V c h s := by
  apply Subtype.ext
  apply Prod.ext
  · change restrictValue E (inf_le_inf h le_rfl : A ⊓ U ≤ B ⊓ U)
        (ringRestrict (inf_le_left : B ⊓ U ≤ B) r • s.val.1) =
      ringRestrict (inf_le_left : A ⊓ U ≤ A) (ringRestrict h r) •
        restrictValue E (inf_le_inf h le_rfl : A ⊓ U ≤ B ⊓ U) s.val.1
    rw [restrictValue_smul, ringRestrict_comp, ringRestrict_comp]
  · apply Prod.ext
    · change restrictValue E (inf_le_inf h le_rfl : A ⊓ V ≤ B ⊓ V)
          (ringRestrict (inf_le_left : B ⊓ V ≤ B) r • s.val.2.1) =
        ringRestrict (inf_le_left : A ⊓ V ≤ A) (ringRestrict h r) •
          restrictValue E (inf_le_inf h le_rfl : A ⊓ V ≤ B ⊓ V) s.val.2.1
      rw [restrictValue_smul, ringRestrict_comp, ringRestrict_comp]
    · exact map_mul (ringRestrict h) r s.val.2.2

/-- The underlying additive matching presheaf. -/
def additivePresheaf {X : Scheme} (E : OModule X) (U V : X.Opens)
    (c : SectionsOn E (U ⊓ V)) : X.Opensᵒᵖ ⥤ AddCommGrpCat where
  obj W := AddCommGrpCat.of (values E U V c W.unop)
  map h := AddCommGrpCat.ofHom (valueRestriction E U V c (leOfHom h.unop))
  map_id W := by
    apply AddCommGrpCat.ext
    intro s
    apply Subtype.ext
    apply Prod.ext
    · exact restrictValue_refl E _ _
    · exact Prod.ext (restrictValue_refl E _ _) (ringRestrict_refl _ _)
  map_comp f g := by
    apply AddCommGrpCat.ext
    intro s
    apply Subtype.ext
    apply Prod.ext
    · exact (restrictValue_comp E _ _ _).symm
    · exact Prod.ext (restrictValue_comp E _ _ _).symm (ringRestrict_comp _ _ _).symm

/-- The additive matching presheaf keeps its original module structure at every open. -/
instance additivePresheaf_module {X : Scheme} (E : OModule X) (U V : X.Opens)
    (c : SectionsOn E (U ⊓ V)) (W : X.Opensᵒᵖ) :
    Module (X.ringCatSheaf.obj.obj W) ((additivePresheaf E U V c).obj W) :=
  inferInstanceAs (Module (RingSections X W.unop) (values E U V c W.unop))

/-- The scalar structure comes from restriction of actual regular functions. -/
def presheaf {X : Scheme} (E : OModule X) (U V : X.Opens)
    (c : SectionsOn E (U ⊓ V)) : PresheafOfModules X.ringCatSheaf.obj := by
  letI : ∀ W : X.Opensᵒᵖ, Module (X.ringCatSheaf.obj.obj W)
      ((additivePresheaf E U V c).obj W) := additivePresheaf_module E U V c
  exact PresheafOfModules.ofPresheaf (additivePresheaf E U V c)
    (fun {_ _} h r s => valueRestriction_smul E U V c (leOfHom h.unop) r s)

/-- A sheaf glues a compatible family on intersections with a fixed open.
Compatibility is expressed on (W_i ∩ W_j) ∩ A, matching the concrete
restriction formula used by the new presheaf. -/
theorem existsUnique_intersectionGluing {X : Scheme} (E : OModule X)
    (A : X.Opens) {I : Type*} (W : I → X.Opens)
    (s : ∀ i, SectionsOn E (W i ⊓ A))
    (hs : ∀ i j,
      restrictValue E (inf_le_inf inf_le_left le_rfl : (W i ⊓ W j) ⊓ A ≤ W i ⊓ A) (s i) =
      restrictValue E (inf_le_inf inf_le_right le_rfl : (W i ⊓ W j) ⊓ A ≤ W j ⊓ A) (s j)) :
    ∃! a : SectionsOn E ((iSup W) ⊓ A), ∀ i,
      restrictValue E (inf_le_inf (le_iSup W i) le_rfl) a = s i := by
  have hc : TopCat.Presheaf.IsCompatible E.presheaf (fun i => W i ⊓ A) s := by
    intro i j
    have h := congrArg
      (restrictValue E (show (W i ⊓ A) ⊓ (W j ⊓ A) ≤ (W i ⊓ W j) ⊓ A from
        le_inf (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left))
          (inf_le_left.trans inf_le_right))) (hs i j)
    change restrictValue E (inf_le_left : (W i ⊓ A) ⊓ (W j ⊓ A) ≤ W i ⊓ A) (s i) =
      restrictValue E (inf_le_right : (W i ⊓ A) ⊓ (W j ⊓ A) ≤ W j ⊓ A) (s j)
    simpa only [restrictValue_comp] using h
  exact (sectionSheaf E).existsUnique_gluing' (fun i => W i ⊓ A) ((iSup W) ⊓ A)
    (fun i => homOfLE (inf_le_inf (le_iSup W i) le_rfl))
    (by rw [iSup_inf_eq]) s hc

/-- The matching presheaf is a genuine sheaf. Its three components glue
in the original sheaves, and their matching equation is checked locally
on the actual overlap. -/
theorem additivePresheaf_isSheaf {X : Scheme} (E : OModule X) (U V : X.Opens)
    (c : SectionsOn E (U ⊓ V)) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X)
      (additivePresheaf E U V c) := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing _).mpr
  intro I W s hs
  have ha : ∀ i j,
      restrictValue E (inf_le_inf inf_le_left le_rfl : (W i ⊓ W j) ⊓ U ≤ W i ⊓ U)
        (s i).val.1 =
      restrictValue E (inf_le_inf inf_le_right le_rfl : (W i ⊓ W j) ⊓ U ≤ W j ⊓ U)
        (s j).val.1 := by
    intro i j
    exact congrArg (fun z : values E U V c (W i ⊓ W j) => z.val.1) (hs i j)
  have hb : ∀ i j,
      restrictValue E (inf_le_inf inf_le_left le_rfl : (W i ⊓ W j) ⊓ V ≤ W i ⊓ V)
        (s i).val.2.1 =
      restrictValue E (inf_le_inf inf_le_right le_rfl : (W i ⊓ W j) ⊓ V ≤ W j ⊓ V)
        (s j).val.2.1 := by
    intro i j
    exact congrArg (fun z : values E U V c (W i ⊓ W j) => z.val.2.1) (hs i j)
  have hr : TopCat.Presheaf.IsCompatible (sectionSheaf (structureModule X)).obj W
      (fun i : I => (show SectionsOn (structureModule X) (W i) from (s i).val.2.2)) := by
    intro i j
    exact congrArg (fun z : values E U V c (W i ⊓ W j) => z.val.2.2) (hs i j)
  obtain ⟨a, ha, ua⟩ := existsUnique_intersectionGluing E U W
    (fun i : I => (show SectionsOn E (W i ⊓ U) from (s i).val.1)) ha
  obtain ⟨b, hb, ub⟩ := existsUnique_intersectionGluing E V W
    (fun i : I => (show SectionsOn E (W i ⊓ V) from (s i).val.2.1)) hb
  obtain ⟨r, hr, ur⟩ := (sectionSheaf (structureModule X)).existsUnique_gluing W
    (fun i : I => (show SectionsOn (structureModule X) (W i) from (s i).val.2.2)) hr
  have hc : (a, b, r) ∈ values E U V c (iSup W) := by
    change restrictValue E _ b - restrictValue E _ a =
      ringRestrict _ r • restrictValue E _ c
    apply (sectionSheaf E).eq_of_locally_eq' (fun i => W i ⊓ (U ⊓ V))
      ((iSup W) ⊓ (U ⊓ V))
      (fun i => homOfLE (inf_le_inf (le_iSup W i) le_rfl))
      (by rw [iSup_inf_eq])
    intro i
    have hai := congrArg
      (restrictValue E (inf_le_inf le_rfl inf_le_left : W i ⊓ (U ⊓ V) ≤ W i ⊓ U)) (ha i)
    have hbi := congrArg
      (restrictValue E (inf_le_inf le_rfl inf_le_right : W i ⊓ (U ⊓ V) ≤ W i ⊓ V)) (hb i)
    have hri := congrArg
      (ringRestrict (inf_le_left : W i ⊓ (U ⊓ V) ≤ W i)) (hr i)
    change ringRestrict (inf_le_left : W i ⊓ (U ⊓ V) ≤ W i)
      (ringRestrict (le_iSup W i) r) = _ at hri
    simp only [restrictValue_comp] at hai hbi
    rw [ringRestrict_comp] at hri
    change restrictValue E _ (restrictValue E _ b - restrictValue E _ a) =
      restrictValue E _ (ringRestrict _ r • restrictValue E _ c)
    rw [map_sub, restrictValue_smul, restrictValue_comp, restrictValue_comp,
      restrictValue_comp, ringRestrict_comp, hai, hbi, hri]
    exact matching_equation E U V c (W i) (s i)
  refine ⟨⟨(a, b, r), hc⟩, ?_, ?_⟩
  · intro i
    apply Subtype.ext
    exact Prod.ext (ha i) (Prod.ext (hb i) (hr i))
  · intro t ht
    apply Subtype.ext
    apply Prod.ext
    · apply ua
      intro i
      exact congrArg (fun z : values E U V c (W i) => z.val.1) (ht i)
    · apply Prod.ext
      · apply ub
        intro i
        exact congrArg (fun z : values E U V c (W i) => z.val.2.1) (ht i)
      · apply ur
        intro i
        exact congrArg (fun z : values E U V c (W i) => z.val.2.2) (ht i)

/-- The actual middle sheaf of the extension realized by c. -/
def middle {X : Scheme} (E : OModule X) (U V : X.Opens)
    (c : SectionsOn E (U ⊓ V)) : OModule X where
  val := presheaf E U V c
  isSheaf := additivePresheaf_isSheaf E U V c

/-- Inclusion of the original kernel sheaf: the same section in both
local components, with quotient component zero. -/
def inclusion {X : Scheme} (E : OModule X) (U V : X.Opens)
    (c : SectionsOn E (U ⊓ V)) : E ⟶ middle E U V c :=
  ⟨{
      app W := ModuleCat.ofHom {
        toFun a := ⟨(restrictValue E inf_le_left a, restrictValue E inf_le_left a, 0), by
          change restrictValue E _ (restrictValue E _ a) -
            restrictValue E _ (restrictValue E _ a) = ringRestrict _ 0 • _
          simp only [restrictValue_comp, sub_self, map_zero, zero_smul]⟩
        map_add' a b := by
          apply Subtype.ext
          exact Prod.ext (map_add _ _ _) (Prod.ext (map_add _ _ _) (zero_add 0).symm)
        map_smul' r a := by
          apply Subtype.ext
          apply Prod.ext (restrictValue_smul E _ r a)
          apply Prod.ext (restrictValue_smul E _ r a)
          change (0 : RingSections X W.unop) =
            (show RingSections X W.unop from r) * 0
          exact (mul_zero (show RingSections X W.unop from r)).symm }
      naturality := by
        intro A B h
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro a
        apply Subtype.ext
        apply Prod.ext
        · change restrictValue E _ (restrictValue E _ a) =
            restrictValue E _ (restrictValue E _ a)
          simp only [restrictValue_comp]
        · apply Prod.ext
          · change restrictValue E _ (restrictValue E _ a) =
              restrictValue E _ (restrictValue E _ a)
            simp only [restrictValue_comp]
          · exact (map_zero _).symm }⟩

/-- The quotient map is the actual regular-function component. -/
def quotient {X : Scheme} (E : OModule X) (U V : X.Opens)
    (c : SectionsOn E (U ⊓ V)) : middle E U V c ⟶ structureModule X :=
  ⟨{
      app _ := ModuleCat.ofHom {
        toFun s := s.val.2.2
        map_add' _ _ := rfl
        map_smul' _ _ := rfl }
      naturality := by intros; rfl }⟩

@[simp]
theorem inclusion_fst {X : Scheme} (E : OModule X) (U V : X.Opens)
    (c : SectionsOn E (U ⊓ V)) (W : X.Opens) (a : SectionsOn E W) :
    ((inclusion E U V c).app W a).val.1 = restrictValue E inf_le_left a := rfl

@[simp]
theorem inclusion_snd {X : Scheme} (E : OModule X) (U V : X.Opens)
    (c : SectionsOn E (U ⊓ V)) (W : X.Opens) (a : SectionsOn E W) :
    ((inclusion E U V c).app W a).val.2.1 = restrictValue E inf_le_left a := rfl

@[simp]
theorem quotient_apply {X : Scheme} (E : OModule X) (U V : X.Opens)
    (c : SectionsOn E (U ⊓ V)) (W : X.Opens) (s : SectionsOn (middle E U V c) W) :
    (quotient E U V c).app W s = s.val.2.2 := rfl

@[simp]
theorem inclusion_quotient {X : Scheme} (E : OModule X) (U V : X.Opens)
    (c : SectionsOn E (U ⊓ V)) : inclusion E U V c ≫ quotient E U V c = 0 := by
  apply Scheme.Modules.hom_ext
  intro W
  ext a
  rfl

/-- The local lifts are explicit sections of the constructed sheaf; no
existence theorem for lifting arbitrary sheaf epimorphisms is used. -/
def firstUnitLift {X : Scheme} (E : OModule X) (U V : X.Opens)
    (c : SectionsOn E (U ⊓ V)) : ExtensionGluing.UnitLift (quotient E U V c) U :=
  ⟨⟨(0, c, 1), by
    change restrictValue E _ c - restrictValue E _ 0 = ringRestrict _ 1 • _
    simp only [map_zero, sub_zero, map_one, one_smul]⟩, rfl⟩

def secondUnitLift {X : Scheme} (E : OModule X) (U V : X.Opens)
    (c : SectionsOn E (U ⊓ V)) : ExtensionGluing.UnitLift (quotient E U V c) V :=
  ⟨⟨(-restrictValue E (le_of_eq (inf_comm V U)) c, 0, 1), by
    change restrictValue E _ 0 -
      restrictValue E _ (-restrictValue E (le_of_eq (inf_comm V U)) c) = ringRestrict _ 1 • _
    simp only [map_zero, map_neg, zero_sub, neg_neg, map_one, one_smul, restrictValue_comp]⟩,
    rfl⟩

/-- Epimorphy follows from the actual local right inverses on a covering pair. -/
theorem quotient_epi {X : Scheme} (E : OModule X) (U V : X.Opens)
    (c : SectionsOn E (U ⊓ V)) (hcover : U ⊔ V = ⊤) : Epi (quotient E U V c) :=
  LocalExtensionSplitting.epi_of_unitLifts (quotient E U V c) U V hcover
    (firstUnitLift E U V c) (secondUnitLift E U V c)

/-- The covering pair separates the two restrictions of a kernel section
on every open, so the actual injection is injective on sections. -/
theorem inclusion_injective {X : Scheme} (E : OModule X) (U V : X.Opens)
    (c : SectionsOn E (U ⊓ V)) (hcover : U ⊔ V = ⊤) (W : X.Opens) :
    Function.Injective ((inclusion E U V c).app W) := by
  intro a b hab
  apply (sectionSheaf E).eq_of_locally_eq₂
    (homOfLE (inf_le_left : W ⊓ U ≤ W))
    (homOfLE (inf_le_left : W ⊓ V ≤ W))
    (by rw [← inf_sup_left, hcover, inf_top_eq])
  · exact congrArg (fun s : values E U V c W => s.val.1) hab
  · exact congrArg (fun s : values E U V c W => s.val.2.1) hab

/-- A compatible pair on subopens of W glues inside the original sheaf E. -/
theorem exists_pairGluing_on {X : Scheme} (E : OModule X) (W A B : X.Opens)
    (hA : A ≤ W) (hB : B ≤ W) (hcover : W ≤ A ⊔ B)
    (a : SectionsOn E A) (b : SectionsOn E B) (hab : PairCompatible E A B a b) :
    ∃ t : SectionsOn E W, restrictValue E hA t = a ∧ restrictValue E hB t = b := by
  let O : Fin 2 → X.Opens := Fin.cases A (fun _ => B)
  let s : ∀ i, SectionsOn E (O i) := Fin.cases a (fun _ => b)
  have hi : ∀ i, O i ≤ W := by
    intro i
    fin_cases i
    · exact hA
    · exact hB
  have hc : W ≤ iSup O :=
    hcover.trans (sup_le (le_iSup O 0) (le_iSup O 1))
  have hs : TopCat.Presheaf.IsCompatible E.presheaf O s := by
    intro i j
    fin_cases i <;> fin_cases j
    · rfl
    · exact hab
    · exact pairCompatible_symm hab
    · rfl
  obtain ⟨t, ht, _⟩ := (sectionSheaf E).existsUnique_gluing' O W
    (fun i => homOfLE (hi i)) hc s hs
  exact ⟨t, ht 0, ht 1⟩

/-- The kernel of the quotient on every open is exactly the image of E.
Only the sheaf gluing axiom is used: no surjectivity on global sections is
claimed for the quotient. -/
theorem section_exact {X : Scheme} (E : OModule X) (U V : X.Opens)
    (c : SectionsOn E (U ⊓ V)) (hcover : U ⊔ V = ⊤) (W : X.Opens) :
    Function.Exact ((inclusion E U V c).app W) ((quotient E U V c).app W) := by
  intro s
  constructor
  · intro hs
    have hr : s.val.2.2 = 0 := hs
    have hm := matching_equation E U V c W s
    rw [hr, map_zero, zero_smul] at hm
    have hm' := (sub_eq_zero.mp hm).symm
    have hab : PairCompatible E (W ⊓ U) (W ⊓ V) s.val.1 s.val.2.1 := by
      have h := congrArg
        (restrictValue E (show (W ⊓ U) ⊓ (W ⊓ V) ≤ W ⊓ (U ⊓ V) from
          le_inf (inf_le_left.trans inf_le_left)
            (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)))) hm'
      change restrictValue E (inf_le_left : (W ⊓ U) ⊓ (W ⊓ V) ≤ W ⊓ U) s.val.1 =
        restrictValue E (inf_le_right : (W ⊓ U) ⊓ (W ⊓ V) ≤ W ⊓ V) s.val.2.1
      simpa only [restrictValue_comp] using h
    obtain ⟨a, ha, hb⟩ := exists_pairGluing_on E W (W ⊓ U) (W ⊓ V)
      inf_le_left inf_le_left (by rw [← inf_sup_left, hcover, inf_top_eq])
      s.val.1 s.val.2.1 hab
    refine ⟨a, ?_⟩
    apply Subtype.ext
    exact Prod.ext ha (Prod.ext hb hr.symm)
  · rintro ⟨a, rfl⟩
    rfl

/-- Pointwise kernels reflect the actual kernel universal property for
module sheaves. This uses the existing fully faithful sheaf-to-presheaf functor
and joint reflection of limits by evaluation of module presheaves. -/
def inclusion_isKernel {X : Scheme.{uER}} (E : OModule X) (U V : X.Opens)
    (c : SectionsOn E (U ⊓ V)) (hcover : U ⊔ V = ⊤) :
    IsLimit (KernelFork.ofι (inclusion E U V c) (inclusion_quotient E U V c)) := by
  let K := KernelFork.ofι (inclusion E U V c) (inclusion_quotient E U V c)
  let F := SheafOfModules.forget.{uER} X.ringCatSheaf
  letI : F.Additive := inferInstanceAs
    (SheafOfModules.forget.{uER} X.ringCatSheaf).Additive
  apply isLimitOfReflects F
  change IsLimit (F.mapCone K)
  refine (K.isLimitMapConeEquiv F).symm ?_
  apply PresheafOfModules.evaluationJointlyReflectsLimits _ _
  intro W
  refine ((K.map F).isLimitMapConeEquiv
    (PresheafOfModules.evaluation.{uER} X.ringCatSheaf.obj W)).symm ?_
  exact ModuleCat.isLimitKernelFork _ _ (section_exact E U V c hcover W.unop)
    (inclusion_injective E U V c hcover W.unop)

set_option maxHeartbeats 800000 in
/-- A genuine short exact sequence E → F_c → O, with all three objects
and both morphisms explicitly constructed in the original sheaf category. -/
theorem shortExact {X : Scheme} (E : OModule X) (U V : X.Opens)
    (c : SectionsOn E (U ⊓ V)) (hcover : U ⊔ V = ⊤) :
    (ShortComplex.mk (inclusion E U V c) (quotient E U V c)
      (inclusion_quotient E U V c)).ShortExact := by
  have hK : IsLimit (KernelFork.ofι (inclusion E U V c)
      (inclusion_quotient E U V c)) := inclusion_isKernel E U V c hcover
  letI : Mono (inclusion E U V c) := mono_of_isLimit_fork hK
  letI : Epi (quotient E U V c) := quotient_epi E U V c hcover
  exact { exact := (ShortComplex.mk _ _ (inclusion_quotient E U V c)).exact_of_f_is_kernel hK }

/-- The two specified actual local lifts have difference exactly i(c).
This checks the sign against the existing first-minus-second differential. -/
theorem localLifts_difference {X : Scheme} (E : OModule X) (U V : X.Opens)
    (c : SectionsOn E (U ⊓ V)) :
    pairDifference (middle E U V c) U V
        ((firstUnitLift E U V c).val, (secondUnitLift E U V c).val) =
      (inclusion E U V c).app (U ⊓ V) c := by
  apply Subtype.ext
  apply Prod.ext
  · change restrictValue E _ 0 -
      restrictValue E _ (-restrictValue E (le_of_eq (inf_comm V U)) c) =
        restrictValue E _ c
    simp only [map_zero, map_neg, zero_sub, neg_neg, restrictValue_comp]
  · apply Prod.ext
    · change restrictValue E _ c - restrictValue E _ 0 = restrictValue E _ c
      simp only [map_zero, sub_zero]
    · change ringRestrict _ 1 - ringRestrict _ 1 = 0
      rw [map_one, map_one, sub_self]

/-- Realization preserves the prescribed cocycle in the original kernel
sheaf and the original ExtensionGluing construction. -/
theorem extensionCocycle_eq {X : Scheme} (E : OModule X) (U V : X.Opens)
    (c : SectionsOn E (U ⊓ V)) (hcover : U ⊔ V = ⊤) :
    ExtensionGluing.extensionCocycle (inclusion E U V c) (quotient E U V c)
      (inclusion_quotient E U V c) (shortExact E U V c hcover) U V
      (firstUnitLift E U V c) (secondUnitLift E U V c) = c := by
  apply inclusion_injective E U V c hcover (U ⊓ V)
  rw [ExtensionGluing.extensionCocycle_spec, localLifts_difference]

/-- The constructed actual extension splits precisely when the original
overlap section has an actual two-chart primitive. -/
theorem splits_iff_primitive {X : Scheme} (E : OModule X) (U V : X.Opens)
    (c : SectionsOn E (U ⊓ V)) (hcover : U ⊔ V = ⊤) :
    (∃ s : structureModule X ⟶ middle E U V c,
      s ≫ quotient E U V c = 𝟙 (structureModule X)) ↔
        Nonempty (Primitive E U V c) := by
  rw [ExtensionGluing.rightInverse_iff_cocycle_primitive
    (inclusion E U V c) (quotient E U V c) (inclusion_quotient E U V c)
    (shortExact E U V c hcover) U V hcover (firstUnitLift E U V c) (secondUnitLift E U V c),
    extensionCocycle_eq E U V c hcover]

/-- The original Yoneda vanishing property solves every actual two-open
cocycle on a covering pair, because each such cocycle is now realized by
an actual short exact extension. -/
theorem pairDifference_surjective_of_hasVanishingFirstCohomology {X : Scheme}
    (E : OModule X) (U V : X.Opens) (hcover : U ⊔ V = ⊤)
    (h : HasVanishingFirstCohomology E) : Function.Surjective (pairDifference E U V) := by
  intro c
  obtain ⟨a⟩ := (splits_iff_primitive E U V c hcover).mp
    (h (middle E U V c) (inclusion E U V c) (quotient E U V c)
      (inclusion_quotient E U V c) (shortExact E U V c hcover))
  exact ⟨a.val, a.property⟩

/-- An actual overlap obstruction now disproves the original Yoneda
vanishing predicate by providing an actual nonsplit short exact extension. -/
theorem not_hasVanishingFirstCohomology_of_noPrimitive {X : Scheme}
    (E : OModule X) (U V : X.Opens) (c : SectionsOn E (U ⊓ V))
    (hcover : U ⊔ V = ⊤) (hc : ¬ Nonempty (Primitive E U V c)) :
    ¬ HasVanishingFirstCohomology E := by
  intro h
  exact hc ((splits_iff_primitive E U V c hcover).mp
    (h (middle E U V c) (inclusion E U V c) (quotient E U V c)
      (inclusion_quotient E U V c) (shortExact E U V c hcover)))

open LeBrunSalamon.P1Charts LeBrunSalamon.P1TwistFrames
open LeBrunSalamon.P1TwistSections
open scoped LaurentPolynomial

/-- The Laurent monomial t^-1, as an actual section of the original twist
on the actual overlap. It is an obstruction for every degree at most -2. -/
def negativeCocycle (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P) (d : ℤ) :
    SectionsOn (projectiveTwist P p d).sheaf (chartOpen 0 ⊓ chartOpen 1) :=
  (laurentCoordinates P p d).symm (LaurentPolynomial.T (-1))

@[simp]
theorem negativeCocycle_coordinates (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ) :
    laurentCoordinates P p d (negativeCocycle P p d) = LaurentPolynomial.T (-1) :=
  (laurentCoordinates P p d).apply_symm_apply _

theorem negativeCocycle_normalForm_ne_zero (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ) (hd : d ≤ -2) :
    overlapNormalForm P p d (negativeCocycle P p d) ≠ 0 := by
  have hgap : d < -1 ∧ (-1 : ℤ) < 0 := by omega
  have hnf : P1Overlap.cechNormalForm d (LaurentPolynomial.T (-1) : ℂ[T;T⁻¹]) =
      LaurentPolynomial.T (-1) := by
    simpa only [map_one, one_mul, if_pos hgap] using
      P1Overlap.cechNormalForm_C_mul_T (K := ℂ) d (-1) 1
  intro h
  have hz := congrArg (laurentCoordinates P p d) h
  rw [normalForm_coordinates, negativeCocycle_coordinates, hnf, map_zero] at hz
  exact (LaurentPolynomial.isUnit_T (-1)).ne_zero hz

/-- The actual short exact extension realizing t^-1 is nonsplit in every
degree at most -2, by the proved normal-form obstruction. -/
theorem negativeExtension_nonsplit (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ) (hd : d ≤ -2) :
    ¬ ∃ s : structureModule ProjectiveLine ⟶
        middle (projectiveTwist P p d).sheaf (chartOpen 0) (chartOpen 1) (negativeCocycle P p d),
      s ≫ quotient (projectiveTwist P p d).sheaf (chartOpen 0) (chartOpen 1)
        (negativeCocycle P p d) = 𝟙 (structureModule ProjectiveLine) := by
  intro h
  have hp := (splits_iff_primitive (projectiveTwist P p d).sheaf
    (chartOpen 0) (chartOpen 1) (negativeCocycle P p d) chartOpen_zero_sup_one).mp h
  exact negativeCocycle_normalForm_ne_zero P p d hd
    ((primitive_exists_iff_normalForm_zero P p d _).mp hp)

/-- This is nonvanishing for the unchanged original Yoneda predicate.
The counterexample is the constructed actual matching sheaf, with the
actual short exact sequence established above. -/
theorem twist_not_hasVanishingFirstCohomology (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ) (hd : d ≤ -2) :
    ¬ HasVanishingFirstCohomology (projectiveTwist P p d).sheaf := by
  apply not_hasVanishingFirstCohomology_of_noPrimitive (projectiveTwist P p d).sheaf
    (chartOpen 0) (chartOpen 1) (negativeCocycle P p d) chartOpen_zero_sup_one
  intro h
  exact negativeCocycle_normalForm_ne_zero P p d hd
    ((primitive_exists_iff_normalForm_zero P p d _).mp h)

theorem twist_degree_ge_neg_one_of_hasVanishingFirstCohomology
    (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P) (d : ℤ)
    (h : HasVanishingFirstCohomology (projectiveTwist P p d).sheaf) : -1 ≤ d := by
  by_contra hd
  exact twist_not_hasVanishingFirstCohomology P p d (by omega) h

end LeBrunSalamon.ExtensionRealization

end
/- END UNCOMPILED continuation extension_realization.lean.txt -/

end

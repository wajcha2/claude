import LSGlobalVelocity

/-!
## Affine functions detect actual sheaf derivations supported at a point

An affine chart detects a point tangent only after the localization comparison
has been proved. The argument here uses the actual structure-sheaf restriction
maps. First Leibniz and invertible denominators determine a derivation on every
basic open. The sheaf axiom then determines it on every smaller open. Finally,
the actual point pushforward has invertible restriction to a neighborhood of
its support. No extension of arbitrary local functions is presumed.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction

namespace LeBrunSalamon.Construction.Lines.AffineDerivationFaithfulness

section Localizations

variable {X S : Scheme} {s : X ⟶ S} {E : OModule X}
variable (D F : RelativeSheafDerivation s E)

/-- Agreement on an affine open determines the derivations on its genuine
basic opens, using the actual localization of its ring of functions. -/
theorem agree_basicOpen (U : X.Opens) (hU : IsAffineOpen U)
    (h : ∀ a : RingSections X U, D.apply U a = F.apply U a)
    (r : RingSections X U) (b : RingSections X (X.basicOpen r)) :
    D.apply (X.basicOpen r) b = F.apply (X.basicOpen r) b := by
  letI := hU.isLocalization_basicOpen r
  let ρ : RingSections X U →+* RingSections X (X.basicOpen r) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom
  have hρ (a : RingSections X U) :
      D.apply (X.basicOpen r) (ρ a) = F.apply (X.basicOpen r) (ρ a) := by
    rw [← D.naturality (homOfLE (X.basicOpen_le r)),
      ← F.naturality (homOfLE (X.basicOpen_le r)), h a]
  obtain ⟨⟨a, m⟩, hm⟩ := IsLocalization.surj (Submonoid.powers r) b
  have heq : b • D.apply (X.basicOpen r) (ρ m) +
        ρ m • D.apply (X.basicOpen r) b =
      b • F.apply (X.basicOpen r) (ρ m) +
        ρ m • F.apply (X.basicOpen r) b := by
    calc
      _ = D.apply (X.basicOpen r) (b * ρ m) := (D.leibniz _ _ _).symm
      _ = D.apply (X.basicOpen r) (ρ a) := congrArg (D.apply _) hm
      _ = F.apply (X.basicOpen r) (ρ a) := hρ a
      _ = F.apply (X.basicOpen r) (b * ρ m) := (congrArg (F.apply _) hm).symm
      _ = _ := F.leibniz _ _ _
  rw [hρ m] at heq
  have hu : IsUnit (ρ m) := IsLocalization.map_units
    (RingSections X (X.basicOpen r)) m
  exact hu.smul_left_cancel.mp (add_left_cancel heq)

/-- All smaller opens are handled by the actual sheaf axiom and the affine
basic-open basis. The local function need not extend to the larger chart. -/
theorem agree_subopen (U : X.Opens) (hU : IsAffineOpen U)
    (h : ∀ a : RingSections X U, D.apply U a = F.apply U a)
    (V : X.Opens) (hVU : V ≤ U) (a : RingSections X V) :
    D.apply V a = F.apply V a := by
  let I := {r : RingSections X U // X.basicOpen r ≤ V}
  let B : I → X.Opens := fun r => X.basicOpen r.val
  have hcover : V ≤ iSup B := by
    intro z hz
    obtain ⟨r, hrV, hzr⟩ := hU.exists_basicOpen_le ⟨z, hz⟩ (hVU hz)
    exact (le_iSup B (⟨r, hrV⟩ : I)) hzr
  apply (TwoChartSections.sectionSheaf E).eq_of_locally_eq' B V
    (fun r => homOfLE r.property) hcover
  intro r
  change E.presheaf.map (homOfLE r.property).op (D.apply V a) =
    E.presheaf.map (homOfLE r.property).op (F.apply V a)
  rw [D.naturality, F.naturality]
  exact agree_basicOpen D F U hU h r.val
    (X.presheaf.map (homOfLE r.property).op a)

/-- For an affine scheme, the global ring determines a sheaf derivation
with values in any module sheaf, not only a quasicoherent one. -/
theorem eq_of_affine_global [IsAffine X]
    (h : ∀ a : RingSections X ⊤, D.apply ⊤ a = F.apply ⊤ a) : D = F := by
  apply FamilyVariation.relativeDerivation_ext
  intro V a
  exact agree_subopen D F ⊤ (isAffineOpen_top X) h V le_top a

/-- The same argument works on a specified affine cover. No smoothness,
reducedness or finite-generation hypothesis is used here. -/
theorem eq_of_affine_cover {I : Type*} (U : I → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hcover : iSup U = ⊤)
    (h : ∀ i (a : RingSections X (U i)), D.apply (U i) a = F.apply (U i) a) :
    D = F := by
  apply FamilyVariation.relativeDerivation_ext
  intro V a
  apply (TwoChartSections.sectionSheaf E).eq_of_locally_eq'
    (fun i => V ⊓ U i) V (fun _ => homOfLE inf_le_left)
    (by rw [← inf_iSup_eq, hcover, inf_top_eq])
  intro i
  change E.presheaf.map (homOfLE (inf_le_left : V ⊓ U i ≤ V)).op (D.apply V a) =
    E.presheaf.map (homOfLE (inf_le_left : V ⊓ U i ≤ V)).op (F.apply V a)
  rw [D.naturality, F.naturality]
  exact agree_subopen D F (U i) (hU i) (h i) (V ⊓ U i) inf_le_right
    (X.presheaf.map (homOfLE inf_le_left).op a)

end Localizations

section SupportedModules

variable {X T S : Scheme} (x : T ⟶ X) (E : OModule T)

/-- If two target opens have the same inverse image, the restriction of
the actual pushforward module is an isomorphism on their sections. -/
theorem pushforward_restriction_injective {U V : X.Opens} (i : U ⟶ V)
    (hi : x ⁻¹ᵁ U = x ⁻¹ᵁ V) :
    Function.Injective (((Scheme.Modules.pushforward x).obj E).presheaf.map i.op) := by
  rw [Scheme.Modules.pushforward_obj_presheaf_map]
  have hm : (TopologicalSpace.Opens.map x.base).map i = eqToHom hi := Subsingleton.elim _ _
  rw [hm]
  exact (ConcreteCategory.bijective_of_isIso (E.presheaf.map (eqToHom hi).op)).1

/-- Restricting to a target neighborhood containing the entire source
does not lose any sections of a pushforward module. -/
theorem pushforward_intersection_injective (U : X.Opens)
    (hU : ⊤ ≤ x ⁻¹ᵁ U) (V : X.Opens) :
    Function.Injective (((Scheme.Modules.pushforward x).obj E).presheaf.map
      (homOfLE (inf_le_right : U ⊓ V ≤ V)).op) := by
  apply pushforward_restriction_injective x E
  apply le_antisymm
  · intro z hz
    exact hz.2
  · intro z hz
    exact ⟨hU (show z ∈ (⊤ : T.Opens) by trivial), hz⟩

/-- A derivation supported on a source lying entirely in one affine open
is determined by its values on that actual affine ring. The source may be
nonreduced and need not itself be affine. -/
theorem supported_eq_of_affine (s : X ⟶ S)
    (D F : RelativeSheafDerivation s ((Scheme.Modules.pushforward x).obj E))
    (U : X.Opens) (hU : IsAffineOpen U) (hxU : ⊤ ≤ x ⁻¹ᵁ U)
    (h : ∀ a : RingSections X U, D.apply U a = F.apply U a) : D = F := by
  apply FamilyVariation.relativeDerivation_ext
  intro V a
  apply pushforward_intersection_injective x E U hxU V
  rw [D.naturality, F.naturality]
  exact agree_subopen D F U hU h (U ⊓ V) inf_le_left
    (X.presheaf.map (homOfLE inf_le_right).op a)

end SupportedModules

section ScalarPoint

variable {X S : Scheme} (s : X ⟶ S) (x : ComplexBase ⟶ X)

/-- Scalar reading of an actual section of the point pushforward. It uses
the prescribed Γ(Spec C) normalization, not a chosen scalar identification. -/
def readPoint (U : X.Opens) (hU : ⊤ ≤ x ⁻¹ᵁ U)
    (a : SectionsOn ((Scheme.Modules.pushforward x).obj (structureModule ComplexBase)) U) :
    ℂ :=
  (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
    (ComplexBase.presheaf.map (homOfLE hU).op a)

/-- On every neighborhood of the full point, scalar reading is injective. -/
theorem readPoint_injective (U : X.Opens) (hU : ⊤ ≤ x ⁻¹ᵁ U) :
    Function.Injective (readPoint x U hU) := by
  intro a b h
  have heq : (⊤ : ComplexBase.Opens) = x ⁻¹ᵁ U := le_antisymm hU le_top
  have hm : homOfLE hU = eqToHom heq := Subsingleton.elim _ _
  have hr := (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).1 h
  rw [hm] at hr
  exact (ConcreteCategory.bijective_of_isIso
    (ComplexBase.presheaf.map (eqToHom heq).op)).1 hr

/-- A point-supported derivation is completely determined by scalar values
of functions on one affine neighborhood. This is the faithful comparison
needed before transporting velocity coordinates into the original fiber. -/
theorem supported_eq_of_affine_scalars
    (D F : RelativeSheafDerivation s
      ((Scheme.Modules.pushforward x).obj (structureModule ComplexBase)))
    (U : X.Opens) (hU : IsAffineOpen U) (hxU : ⊤ ≤ x ⁻¹ᵁ U)
    (h : ∀ a : RingSections X U,
      readPoint x U hxU (D.apply U a) = readPoint x U hxU (F.apply U a)) : D = F := by
  apply supported_eq_of_affine x (structureModule ComplexBase) s D F U hU hxU
  intro a
  exact readPoint_injective x U hxU (h a)

end ScalarPoint

end LeBrunSalamon.Construction.Lines.AffineDerivationFaithfulness

end

/-!
## Canonical tangent-fiber evaluation on actual local functions

The original tangent fiber is converted into a cotangent functional by the
normalized dual-base-change morphism. Its adjoint is a derivation with values
in the actual point pushforward. No arbitrary fiber identification is chosen.
The all-open injectivity statement uses only the original universal cotangent
property and the locally free dual comparison. The affine-chart construction
uses the actual inverse of the open immersion's map on functions.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirty
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction

namespace LeBrunSalamon.Construction.Lines.IntrinsicTangent

open FamilyVariation PositiveFrame

/-! ### The original dual fiber and its actual functional -/

/-- A vector in the original dual fiber gives a functional on the original
pulled-back module. The canonical dual comparison fixes its normalization. -/
def dualFiberFunctional {Y : Scheme} (x : ComplexBase ⟶ Y) (E : OModule Y)
    (v : Fiber (dualSheaf E) x) :
    pullbackModule x E ⟶ structureModule ComplexBase :=
  TwoChartSections.internalHomSectionAddEquiv _ _
    (sectionFromValue v ≫ dualBaseChange x E)

/-- The Hom section of that functional is the actual dual-base-change image
of the original vector's section. -/
theorem dualFiberFunctional_section {Y : Scheme} (x : ComplexBase ⟶ Y)
    (E : OModule Y) (v : Fiber (dualSheaf E) x) :
    TwoChartSections.homSection (dualFiberFunctional x E v) =
      sectionFromValue v ≫ dualBaseChange x E :=
  TwoChartSections.homSection_internalHomSectionAddEquiv _

/-- Recovering a vector from its functional needs the precise locally free
dual comparison, not merely equality of dimensions. -/
theorem dualFiberFunctional_injective {Y : Scheme} (x : ComplexBase ⟶ Y)
    (E : OModule Y) {r : ℕ} (hE : IsLocallyFreeOfRank E r) :
    Function.Injective (dualFiberFunctional x E) := by
  letI := dualBaseChange_isIso x hE
  intro v w h
  have hs := congrArg TwoChartSections.homSection h
  rw [dualFiberFunctional_section, dualFiberFunctional_section] at hs
  have hv : sectionFromValue v = sectionFromValue w :=
    (cancel_mono (dualBaseChange x E)).mp hs
  simpa only [sectionFromValue_spec] using congrArg sectionValue hv

/-- Evaluation of the functional on every actual local section agrees with
the original pulled-back evaluation pairing. -/
theorem dualFiberFunctional_evaluate {Y : Scheme} (x : ComplexBase ⟶ Y)
    (E : OModule Y) (v : Fiber (dualSheaf E) x) (U : ComplexBase.Opens)
    (e : SectionsOn (pullbackModule x E) U) :
    (dualFiberFunctional x E v).app U e =
      (unitPullbackMap x).app U
        ((pullbackPair x (dualEvaluation E)).apply U
          (TwoChartSections.restrictValue (pullbackModule x (dualSheaf E))
            le_top v) e) := by
  have h := homSection_evaluate_one (dualFiberFunctional x E v) U e
  rw [dualFiberFunctional_section] at h
  change (dualEvaluation (pullbackModule x E)).apply U
    ((dualBaseChange x E).app U
      (Scheme.Modules.Hom.app (sectionFromValue v) U (1 : RingSections ComplexBase U))) e = _ at h
  rw [ScalarSections.section_app_one, sectionFromValue_spec,
    dualBaseChange_evaluate] at h
  exact h.symm

/-- At the whole point the restriction is the identity. -/
theorem dualFiberFunctional_evaluate_top {Y : Scheme} (x : ComplexBase ⟶ Y)
    (E : OModule Y) (v : Fiber (dualSheaf E) x)
    (e : Fiber E x) :
    (dualFiberFunctional x E v).app ⊤ e =
      (unitPullbackMap x).app ⊤
        ((pullbackPair x (dualEvaluation E)).apply ⊤ v e) := by
  rw [dualFiberFunctional_evaluate, TwoChartSections.restrictValue_refl]

/-- The adjoint cotangent map is defined against the actual point
pushforward, whose scalar structure is induced by the original point. -/
def adjointFunctional {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (x : ComplexBase ⟶ Y) (v : Fiber (tangentSheaf sY) x) :
    cotangentSheaf sY ⟶ (Scheme.Modules.pushforward x).obj (structureModule ComplexBase) :=
  (Scheme.Modules.pullbackPushforwardAdjunction x).homEquiv _ _
    (dualFiberFunctional x (cotangentSheaf sY) v)

/-- The original tangent vector acts on functions on every actual open. -/
def supportedDerivation {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (x : ComplexBase ⟶ Y) (v : Fiber (tangentSheaf sY) x) :
    RelativeSheafDerivation sY
      ((Scheme.Modules.pushforward x).obj (structureModule ComplexBase)) :=
  (cotangentPresentation sY).differential.postcompose (adjointFunctional sY x v)

/-- The universal differential gives the precise local normalization of
the point-supported derivation. -/
theorem supportedDerivation_apply {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (x : ComplexBase ⟶ Y) (v : Fiber (tangentSheaf sY) x)
    (U : Y.Opens) (a : RingSections Y U) :
    (supportedDerivation sY x v).apply U a =
      (dualFiberFunctional x (cotangentSheaf sY) v).app (x ⁻¹ᵁ U)
        (pullLocalSection x (cotangentSheaf sY) U
          ((cotangentPresentation sY).differential.apply U a)) := rfl

/-- The universal property recovers the actual adjoint, retaining the
chosen differential rather than an unspecified cotangent isomorphism. -/
theorem supportedDerivation_lift {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (x : ComplexBase ⟶ Y) (v : Fiber (tangentSheaf sY) x) :
    differentialLift (supportedDerivation sY x v) = adjointFunctional sY x v := by
  symm
  apply differentialLift_unique
  rfl

/-- All-open evaluation on functions is faithful on the ORIGINAL tangent
fiber. Local-freeness enters only through the canonical dual comparison. -/
theorem supportedDerivation_injective {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (x : ComplexBase ⟶ Y) {r : ℕ}
    (hΩ : IsLocallyFreeOfRank (cotangentSheaf sY) r) :
    Function.Injective (supportedDerivation sY x) := by
  intro v w h
  apply dualFiberFunctional_injective x (cotangentSheaf sY) hΩ
  apply ((Scheme.Modules.pullbackPushforwardAdjunction x).homEquiv _ _).injective
  apply ((cotangentPresentation sY).universal
    ((Scheme.Modules.pushforward x).obj (structureModule ComplexBase))).1
  exact h

theorem smooth_supportedDerivation_injective {d : ℕ}
    (X : SmoothProperComplexVariety d) (x : ComplexPoint X) :
    Function.Injective (supportedDerivation X.structureMap x.map) :=
  supportedDerivation_injective X.structureMap x.map
    (smooth_cotangent_rank X.structureMap d X.smooth)

/-- Point vectors can be compared directly by local differentials, with
the actual support module and its restrictions kept in the statement. -/
theorem eq_of_supported_values {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (x : ComplexBase ⟶ Y) {r : ℕ}
    (hΩ : IsLocallyFreeOfRank (cotangentSheaf sY) r)
    (v w : Fiber (tangentSheaf sY) x)
    (h : ∀ (U : Y.Opens) (a : RingSections Y U),
      (supportedDerivation sY x v).apply U a =
        (supportedDerivation sY x w).apply U a) : v = w := by
  apply supportedDerivation_injective sY x hΩ
  exact relativeDerivation_ext h

/-! ### Scalar coefficients on actual neighborhoods of the point -/

/-- The scalar action on a local function is obtained from the original
fiber pairing with its actual differential. It is complex-linear in the
original tangent vector by construction. -/
def localAction {Y : Scheme} (sY : Y ⟶ ComplexBase) (x : ComplexBase ⟶ Y)
    (U : Y.Opens) (hU : ⊤ ≤ x ⁻¹ᵁ U) (a : RingSections Y U) :
    Fiber (tangentSheaf sY) x →ₗ[ℂ] ℂ :=
  localScalarPairing x (dualEvaluation (cotangentSheaf sY)) U hU
    ((cotangentPresentation sY).differential.apply U a)

/-- The fiber-pairing and cotangent-functional definitions give the same
number, including the canonical scalar normalization on Spec(C). -/
theorem localAction_eq_functional {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (x : ComplexBase ⟶ Y) (U : Y.Opens) (hU : ⊤ ≤ x ⁻¹ᵁ U)
    (a : RingSections Y U) (v : Fiber (tangentSheaf sY) x) :
    localAction sY x U hU a v =
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
        ((dualFiberFunctional x (cotangentSheaf sY) v).app ⊤
          (localFiberValue x (cotangentSheaf sY) U hU
            ((cotangentPresentation sY).differential.apply U a))) := by
  rw [dualFiberFunctional_evaluate_top]
  rfl

/-- Restricting the supported derivation to the whole point recovers the
same scalar action. This is the interface for localization faithfulness. -/
theorem localAction_eq_supported {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (x : ComplexBase ⟶ Y) (U : Y.Opens) (hU : ⊤ ≤ x ⁻¹ᵁ U)
    (a : RingSections Y U) (v : Fiber (tangentSheaf sY) x) :
    localAction sY x U hU a v =
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
        (ComplexBase.presheaf.map (homOfLE hU).op
          ((supportedDerivation sY x v).apply U a)) := by
  rw [localAction_eq_functional, supportedDerivation_apply]
  unfold localFiberValue
  rw [← sheafHom_naturality]
  rfl

/-- The actual point value fixes every complex scalar; the base equation
is necessary for this assertion. -/
theorem localRingValue_constant {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (x : ComplexBase ⟶ Y) (hx : x ≫ sY = 𝟙 ComplexBase)
    (U : Y.Opens) (hU : ⊤ ≤ x ⁻¹ᵁ U) (c : ℂ) :
    localRingValue x U hU (complexConstant sY U c) = c := by
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
    (ComplexBase.presheaf.map (homOfLE hU).op (x.app U (complexConstant sY U c))) = c
  rw [SectionAlgebra.constants_naturality x hx U c,
    ScalarSections.complexConstant_restrict]
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
    ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c) = c
  exact Iso.inv_hom_id_apply _ _

/-- The actual evaluation of a local function is a complex algebra map. -/
def localPoint {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (x : ComplexBase ⟶ Y) (hx : x ≫ sY = 𝟙 ComplexBase)
    (U : Y.Opens) (hU : ⊤ ≤ x ⁻¹ᵁ U) :
    SectionAlgebra.Functions sY U →ₐ[ℂ] ℂ where
  toRingHom := localRingValue x U hU
  commutes' := localRingValue_constant sY x hx U hU

/-- Any relative derivation kills the actual complex constants on every
open, by naturality from the top open of the base. -/
theorem relativeDerivation_constant {Y : Scheme} (sY : Y ⟶ ComplexBase)
    {E : OModule Y} (D : RelativeSheafDerivation sY E)
    (U : Y.Opens) (c : ℂ) : D.apply U (complexConstant sY U c) = 0 := by
  have hk := D.killsBase ⊤ ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c)
  change D.apply ⊤ (sY.appTop ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c)) = 0 at hk
  have hn := D.naturality (homOfLE (show U ≤ ⊤ from le_top))
    (sY.appTop ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c))
  rw [hk, map_zero] at hn
  exact hn.symm

theorem localAction_zero_function {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (x : ComplexBase ⟶ Y) (U : Y.Opens) (hU : ⊤ ≤ x ⁻¹ᵁ U)
    (v : Fiber (tangentSheaf sY) x) : localAction sY x U hU 0 v = 0 := by
  rw [localAction_eq_supported, (supportedDerivation sY x v).zero, map_zero, map_zero]

theorem localAction_add_function {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (x : ComplexBase ⟶ Y) (U : Y.Opens) (hU : ⊤ ≤ x ⁻¹ᵁ U)
    (a b : RingSections Y U) (v : Fiber (tangentSheaf sY) x) :
    localAction sY x U hU (a+b) v =
      localAction sY x U hU a v + localAction sY x U hU b v := by
  simp only [localAction_eq_supported, (supportedDerivation sY x v).add, map_add]

/-- The original tangent fiber satisfies the ordinary point Leibniz rule
on every actual local function domain. -/
theorem localAction_mul_function {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (x : ComplexBase ⟶ Y) (U : Y.Opens) (hU : ⊤ ≤ x ⁻¹ᵁ U)
    (a b : RingSections Y U) (v : Fiber (tangentSheaf sY) x) :
    localAction sY x U hU (a*b) v =
      localRingValue x U hU a * localAction sY x U hU b v +
        localRingValue x U hU b * localAction sY x U hU a v := by
  simp only [localAction_eq_supported, (supportedDerivation sY x v).leibniz]
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
    (ComplexBase.presheaf.map (homOfLE hU).op
      (x.app U a * (show RingSections ComplexBase (x ⁻¹ᵁ U) from
          (supportedDerivation sY x v).apply U b) +
        x.app U b * (show RingSections ComplexBase (x ⁻¹ᵁ U) from
          (supportedDerivation sY x v).apply U a))) = _
  simp only [map_add, map_mul]
  rfl

theorem localAction_constant {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (x : ComplexBase ⟶ Y) (U : Y.Opens) (hU : ⊤ ≤ x ⁻¹ᵁ U)
    (c : ℂ) (v : Fiber (tangentSheaf sY) x) :
    localAction sY x U hU (complexConstant sY U c) v = 0 := by
  rw [localAction_eq_supported, relativeDerivation_constant, map_zero, map_zero]

theorem localAction_smul_function {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (x : ComplexBase ⟶ Y) (hx : x ≫ sY = 𝟙 ComplexBase)
    (U : Y.Opens) (hU : ⊤ ≤ x ⁻¹ᵁ U) (c : ℂ)
    (a : SectionAlgebra.Functions sY U) (v : Fiber (tangentSheaf sY) x) :
    localAction sY x U hU (c • a) v = c * localAction sY x U hU a v := by
  change localAction sY x U hU
    (complexConstant sY U c * (show RingSections Y U from a)) v = _
  rw [localAction_mul_function, localAction_constant, localRingValue_constant sY x hx,
    mul_zero, add_zero]

/-- The local derivative as a complex-linear functional on the actual
section algebra. Its scalar structure comes from the specified structure map. -/
def localDerivativeLinear {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (x : ComplexBase ⟶ Y) (hx : x ≫ sY = 𝟙 ComplexBase)
    (U : Y.Opens) (hU : ⊤ ≤ x ⁻¹ᵁ U) (v : Fiber (tangentSheaf sY) x) :
    SectionAlgebra.Functions sY U →ₗ[ℂ] ℂ where
  toFun a := localAction sY x U hU a v
  map_add' a b := localAction_add_function sY x U hU a b v
  map_smul' c a := localAction_smul_function sY x hx U hU c a v

/-- Canonical local point derivations, constructed from the original
tangent-sheaf fiber and the actual function/differential pairing. -/
def localDerivation {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (x : ComplexBase ⟶ Y) (hx : x ≫ sY = 𝟙 ComplexBase)
    (U : Y.Opens) (hU : ⊤ ≤ x ⁻¹ᵁ U) :
    Fiber (tangentSheaf sY) x →ₗ[ℂ]
      Infinitesimal.Tangent (SectionAlgebra.Functions sY U) (localPoint sY x hx U hU) where
  toFun v := ⟨localDerivativeLinear sY x hx U hU v,
    fun a b => localAction_mul_function sY x U hU a b v⟩
  map_add' v w := by
    apply Subtype.ext
    ext a
    exact (localAction sY x U hU a).map_add v w
  map_smul' c v := by
    apply Subtype.ext
    ext a
    exact (localAction sY x U hU a).map_smul c v

theorem localDerivation_apply {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (x : ComplexBase ⟶ Y) (hx : x ≫ sY = 𝟙 ComplexBase)
    (U : Y.Opens) (hU : ⊤ ≤ x ⁻¹ᵁ U)
    (v : Fiber (tangentSheaf sY) x) (a : SectionAlgebra.Functions sY U) :
    (localDerivation sY x hx U hU v).val a = localAction sY x U hU a v := rfl

/-- Restricting a function to any smaller point neighborhood leaves its
derivative unchanged. No global extension of an arbitrary local function
is asserted. -/
theorem localAction_restrict {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (x : ComplexBase ⟶ Y) {U V : Y.Opens} (hUV : U ≤ V)
    (hU : ⊤ ≤ x ⁻¹ᵁ U) (hV : ⊤ ≤ x ⁻¹ᵁ V)
    (a : RingSections Y V) (v : Fiber (tangentSheaf sY) x) :
    localAction sY x U hU (Y.presheaf.map (homOfLE hUV).op a) v =
      localAction sY x V hV a v := by
  rw [localAction_eq_supported, localAction_eq_supported]
  rw [← (supportedDerivation sY x v).naturality]
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
    (ComplexBase.presheaf.map (homOfLE hU).op
      (ComplexBase.presheaf.map
        (((TopologicalSpace.Opens.map x.base).map (homOfLE hUV)).op)
        ((supportedDerivation sY x v).apply V a))) = _
  apply congrArg (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- Actual localization faithfulness turns equality on one affine
neighborhood into equality in the original tangent fiber. -/
theorem eq_of_affine_localAction {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (x : ComplexBase ⟶ Y) {r : ℕ}
    (hΩ : IsLocallyFreeOfRank (cotangentSheaf sY) r)
    (U : Y.Opens) (hU : IsAffineOpen U) (hxU : ⊤ ≤ x ⁻¹ᵁ U)
    (v w : Fiber (tangentSheaf sY) x)
    (h : ∀ a : RingSections Y U,
      localAction sY x U hxU a v = localAction sY x U hxU a w) : v = w := by
  apply supportedDerivation_injective sY x hΩ
  apply AffineDerivationFaithfulness.supported_eq_of_affine_scalars sY x
    (supportedDerivation sY x v) (supportedDerivation sY x w) U hU hxU
  intro a
  simpa only [localAction_eq_supported, AffineDerivationFaithfulness.readPoint] using h a

/-- The actual local point derivation is faithful as soon as the chosen
open is affine. Neither global functions on the proper target nor a bare
rank comparison is used. -/
theorem localDerivation_injective {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (x : ComplexBase ⟶ Y) (hx : x ≫ sY = 𝟙 ComplexBase) {r : ℕ}
    (hΩ : IsLocallyFreeOfRank (cotangentSheaf sY) r)
    (U : Y.Opens) (hU : IsAffineOpen U) (hxU : ⊤ ≤ x ⁻¹ᵁ U) :
    Function.Injective (localDerivation sY x hx U hxU) := by
  intro v w h
  apply eq_of_affine_localAction sY x hΩ U hU hxU v w
  intro a
  exact congrArg (fun D => D.val a) h

/-! ### Actual affine target chart functions -/

variable {d : ℕ} {X : SmoothProperComplexVariety d} {x : ComplexPoint X}

/-- Use the actual image open of the given chart. -/
def chartOpen (C : GlobalVelocity.TargetChart X x) : X.scheme.Opens :=
  C.inclusion ''ᵁ ⊤

theorem chartOpen_source (C : GlobalVelocity.TargetChart X x) :
    (⊤ : (Spec (CommRingCat.of C.Ring)).Opens) ≤ C.inclusion ⁻¹ᵁ chartOpen C :=
  (Scheme.Hom.preimage_image_eq C.inclusion ⊤).ge

theorem chartOpen_point (C : GlobalVelocity.TargetChart X x) :
    ⊤ ≤ x.map ⁻¹ᵁ chartOpen C := by
  intro z _
  change x.map z ∈ C.inclusion ''ᵁ ⊤
  rw [← C.atPoint]
  exact ⟨C.point z, trivial, rfl⟩

theorem chartOpen_affine (C : GlobalVelocity.TargetChart X x) :
    IsAffineOpen (chartOpen C) := by
  rw [chartOpen, Scheme.Hom.image_top_eq_opensRange]
  exact isAffineOpen_opensRange C.inclusion

/-- Containment of the source chart in an inverse image is exactly the
needed containment of its actual image open. -/
theorem chartOpen_le (C : GlobalVelocity.TargetChart X x) (V : X.scheme.Opens)
    (hV : (⊤ : (Spec (CommRingCat.of C.Ring)).Opens) ≤ C.inclusion ⁻¹ᵁ V) :
    chartOpen C ≤ V := by
  rintro z ⟨q, _, rfl⟩
  exact hV (show q ∈ (⊤ : (Spec (CommRingCat.of C.Ring)).Opens) by trivial)

/-- Every chart algebra element is an actual function on the chart's
image open in the original variety. The inverse is the actual appIso. -/
def chartFunctionsRing (C : GlobalVelocity.TargetChart X x) :
    C.Ring →+* RingSections X.scheme (chartOpen C) :=
  (C.inclusion.appIso ⊤).inv.hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of C.Ring)).inv.hom

theorem chartFunctions_pullback (C : GlobalVelocity.TargetChart X x) (a : C.Ring) :
    C.inclusion.appLE (chartOpen C) ⊤ (chartOpen_source C) (chartFunctionsRing C a) =
      (Scheme.ΓSpecIso (CommRingCat.of C.Ring)).inv a := by
  rw [show C.inclusion.appLE (chartOpen C) ⊤ (chartOpen_source C) =
    (C.inclusion.appIso ⊤).hom from (C.inclusion.appIso_hom' ⊤).symm]
  exact Iso.inv_hom_id_apply _ _

/-- Pullback is injective on the explicitly typed original chart open.
Transport the appIso equality on values, so that its image-open domain
does not change the concrete-category instance in a later rewrite. -/
theorem chartPullback_injective (C : GlobalVelocity.TargetChart X x) :
    Function.Injective (fun a : RingSections X.scheme (chartOpen C) =>
      C.inclusion.appLE (chartOpen C) ⊤ (chartOpen_source C) a) := by
  intro a b hab
  apply (ConcreteCategory.bijective_of_isIso (C.inclusion.appIso ⊤).hom).1
  have happ (t : RingSections X.scheme (chartOpen C)) :
      (C.inclusion.appIso ⊤).hom t =
        C.inclusion.appLE (chartOpen C) ⊤ (chartOpen_source C) t :=
    congrArg (fun k : X.scheme.presheaf.obj (op (chartOpen C)) ⟶
      (Spec (CommRingCat.of C.Ring)).presheaf.obj (op ⊤) => k t)
      (C.inclusion.appIso_hom' ⊤)
  exact (happ a).trans (hab.trans (happ b).symm)

theorem chartFunctions_algebraMap (C : GlobalVelocity.TargetChart X x) (c : ℂ) :
    chartFunctionsRing C (algebraMap ℂ C.Ring c) =
      complexConstant X.structureMap (chartOpen C) c := by
  apply chartPullback_injective C
  change C.inclusion.appLE (chartOpen C) ⊤ (chartOpen_source C)
      (chartFunctionsRing C (algebraMap ℂ C.Ring c)) =
    C.inclusion.appLE (chartOpen C) ⊤ (chartOpen_source C)
      (complexConstant X.structureMap (chartOpen C) c)
  rw [chartFunctions_pullback, GlobalVelocity.specFunction_constant]
  have hn := SectionAlgebra.constants_naturality C.inclusion C.overC (chartOpen C) c
  change complexConstants (DirectionCones.affineBaseMap C.Ring) c =
    (Spec (CommRingCat.of C.Ring)).presheaf.map (homOfLE (chartOpen_source C)).op
      (C.inclusion.app (chartOpen C) (complexConstant X.structureMap (chartOpen C) c))
  rw [hn, ScalarSections.complexConstant_restrict]
  rfl

def chartFunctions (C : GlobalVelocity.TargetChart X x) :
    C.Ring →ₐ[ℂ] SectionAlgebra.Functions X.structureMap (chartOpen C) where
  toRingHom := chartFunctionsRing C
  commutes' := chartFunctions_algebraMap C

/-- The actual function map is bijective. All chart functions are covered,
not merely the restrictions of global functions on the proper target. -/
theorem chartFunctions_bijective (C : GlobalVelocity.TargetChart X x) :
    Function.Bijective (chartFunctions C) :=
  (ConcreteCategory.bijective_of_isIso (C.inclusion.appIso ⊤).inv).comp
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of C.Ring)).inv)

def chartFunctionsEquiv (C : GlobalVelocity.TargetChart X x) :
    C.Ring ≃ₐ[ℂ] SectionAlgebra.Functions X.structureMap (chartOpen C) :=
  AlgEquiv.ofBijective (chartFunctions C) (chartFunctions_bijective C)

/-- The original chart point evaluates the original image-open function
at exactly the specified affine algebra point. -/
theorem chartFunctions_value (C : GlobalVelocity.TargetChart X x) (a : C.Ring) :
    localRingValue x.map (chartOpen C) (chartOpen_point C) (chartFunctions C a) =
      C.evaluation a := by
  have hc : C.inclusion.appLE (chartOpen C) ⊤ (chartOpen_source C) ≫ C.point.appTop =
      x.map.appLE (chartOpen C) ⊤ (chartOpen_point C) := by
    change C.inclusion.appLE (chartOpen C) ⊤ (chartOpen_source C) ≫ C.point.app ⊤ = _
    rw [C.point.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
    exact DualThickening.appLE_of_map_eq C.atPoint (chartOpen C) ⊤ _ _
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
    (x.map.appLE (chartOpen C) ⊤ (chartOpen_point C) (chartFunctions C a)) = _
  rw [← hc]
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
    (C.point.appTop
      (C.inclusion.appLE (chartOpen C) ⊤ (chartOpen_source C) (chartFunctionsRing C a))) = _
  rw [chartFunctions_pullback]
  rfl

/-- The actual coordinate returned by the chart is exactly the original
algebra element used to form its image-open function. -/
theorem chartFunctions_coordinate (C : GlobalVelocity.TargetChart X x) (a : C.Ring) :
    C.localCoordinate (chartOpen C) (chartOpen_source C) (chartFunctions C a) = a := by
  change (Scheme.ΓSpecIso (CommRingCat.of C.Ring)).hom
    (C.inclusion.appLE (chartOpen C) ⊤ (chartOpen_source C) (chartFunctionsRing C a)) = a
  rw [chartFunctions_pullback]
  exact Iso.inv_hom_id_apply _ _

/-- The canonical affine-chart evaluation map from the ORIGINAL tangent
fiber. Its coordinate values are forced by the actual local differentials. -/
def chartEvaluation (C : GlobalVelocity.TargetChart X x) :
    TangentFiber X x →ₗ[ℂ] Infinitesimal.Tangent C.Ring C.evaluation where
  toFun v :=
    ⟨(localDerivativeLinear X.structureMap x.map x.overC
        (chartOpen C) (chartOpen_point C) v).comp (chartFunctions C).toLinearMap, by
      intro a b
      change localAction X.structureMap x.map (chartOpen C) (chartOpen_point C)
        (chartFunctions C (a*b)) v = _
      rw [map_mul, localAction_mul_function, chartFunctions_value, chartFunctions_value]
      rfl⟩
  map_add' v w := by
    apply Subtype.ext
    ext a
    exact (localAction X.structureMap x.map (chartOpen C) (chartOpen_point C)
      (chartFunctions C a)).map_add v w
  map_smul' c v := by
    apply Subtype.ext
    ext a
    exact (localAction X.structureMap x.map (chartOpen C) (chartOpen_point C)
      (chartFunctions C a)).map_smul c v

theorem chartEvaluation_apply (C : GlobalVelocity.TargetChart X x)
    (v : TangentFiber X x) (a : C.Ring) :
    (chartEvaluation C v).val a =
      localAction X.structureMap x.map (chartOpen C) (chartOpen_point C)
        (chartFunctions C a) v := rfl

/-- The coordinate formula exposes the actual differential and the
original cotangent functional, so it excludes arbitrary fiber isomorphisms. -/
theorem chartEvaluation_functional (C : GlobalVelocity.TargetChart X x)
    (v : TangentFiber X x) (a : C.Ring) :
    (chartEvaluation C v).val a =
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
        ((dualFiberFunctional x.map (cotangentSheaf X.structureMap) v).app ⊤
          (localFiberValue x.map (cotangentSheaf X.structureMap)
            (chartOpen C) (chartOpen_point C)
            ((cotangentPresentation X.structureMap).differential.apply (chartOpen C)
              (chartFunctions C a)))) :=
  localAction_eq_functional X.structureMap x.map (chartOpen C) (chartOpen_point C)
    (chartFunctions C a) v

/-- Equality of chart derivations tests every actual function on the
image open, using surjectivity of the actual open-immersion comparison. -/
theorem chartEvaluation_eq_iff_imageOpen (C : GlobalVelocity.TargetChart X x)
    (v w : TangentFiber X x) :
    chartEvaluation C v = chartEvaluation C w ↔
      ∀ a : RingSections X.scheme (chartOpen C),
        localAction X.structureMap x.map (chartOpen C) (chartOpen_point C) a v =
          localAction X.structureMap x.map (chartOpen C) (chartOpen_point C) a w := by
  constructor
  · intro h a
    obtain ⟨b, rfl⟩ := (chartFunctions_bijective C).2 a
    exact congrArg (fun D : Infinitesimal.Tangent C.Ring C.evaluation => D.val b) h
  · intro h
    apply Subtype.ext
    ext a
    exact h (chartFunctions C a)

/-- The canonical chart evaluation is injective. This is the key faithful
comparison from the original tangent sheaf to the actual affine tangent
model; its proof uses genuine basic-open localization and the sheaf axiom. -/
theorem chartEvaluation_injective (C : GlobalVelocity.TargetChart X x) :
    Function.Injective (chartEvaluation C) := by
  intro v w h
  apply eq_of_affine_localAction X.structureMap x.map
    (smooth_cotangent_rank X.structureMap d X.smooth)
    (chartOpen C) (chartOpen_affine C) (chartOpen_point C) v w
  exact (chartEvaluation_eq_iff_imageOpen C v w).mp h

theorem chartEvaluation_eq_iff (C : GlobalVelocity.TargetChart X x)
    (v w : TangentFiber X x) : chartEvaluation C v = chartEvaluation C w ↔ v = w :=
  (chartEvaluation_injective C).eq_iff

theorem chartEvaluation_zero_iff (C : GlobalVelocity.TargetChart X x)
    (v : TangentFiber X x) : chartEvaluation C v = 0 ↔ v = 0 := by
  rw [← (chartEvaluation C).map_zero]
  exact chartEvaluation_eq_iff C v 0

/-- A function on a larger original open restricts to the image-open
function determined by its actual chart coordinate. -/
theorem chartFunctions_localCoordinate (C : GlobalVelocity.TargetChart X x)
    (V : X.scheme.Opens)
    (hV : (⊤ : (Spec (CommRingCat.of C.Ring)).Opens) ≤ C.inclusion ⁻¹ᵁ V)
    (a : RingSections X.scheme V) :
    chartFunctions C (C.localCoordinate V hV a) =
      X.scheme.presheaf.map (homOfLE (chartOpen_le C V hV)).op a := by
  apply chartPullback_injective C
  change C.inclusion.appLE (chartOpen C) ⊤ (chartOpen_source C)
      (chartFunctionsRing C (C.localCoordinate V hV a)) =
    C.inclusion.appLE (chartOpen C) ⊤ (chartOpen_source C)
      (X.scheme.presheaf.map (homOfLE (chartOpen_le C V hV)).op a)
  rw [chartFunctions_pullback, C.localCoordinate_function]
  have hn := C.inclusion.map_appLE (chartOpen_source C)
    (homOfLE (chartOpen_le C V hV)).op
  exact (congrArg (fun k => k a) hn).symm

/-- The canonical chart evaluation acts on every local target function
whose domain contains the chart, in the original function coordinates. -/
theorem chartEvaluation_localCoordinate (C : GlobalVelocity.TargetChart X x)
    (V : X.scheme.Opens)
    (hV : (⊤ : (Spec (CommRingCat.of C.Ring)).Opens) ≤ C.inclusion ⁻¹ᵁ V)
    (hxV : ⊤ ≤ x.map ⁻¹ᵁ V) (a : RingSections X.scheme V)
    (v : TangentFiber X x) :
    (chartEvaluation C v).val (C.localCoordinate V hV a) =
      localAction X.structureMap x.map V hxV a v := by
  rw [chartEvaluation_apply, chartFunctions_localCoordinate]
  exact localAction_restrict X.structureMap x.map (chartOpen_le C V hV)
    (chartOpen_point C) hxV a v

/-- Coordinate equations transport original vector identities through the
canonical faithful map. This is useful for the sum of the two positive
variation spaces in the suitable-pair argument. -/
theorem add_eq_of_chartEvaluation (C : GlobalVelocity.TargetChart X x)
    (u v w : TangentFiber X x)
    (h : chartEvaluation C u + chartEvaluation C v = chartEvaluation C w) :
    u + v = w := by
  apply chartEvaluation_injective C
  simpa only [map_add] using h

/-- A subspace is transported by the actual canonical map. Membership
can be pulled back because the same map has now been proved faithful. -/
theorem mem_iff_chartEvaluation_mem (C : GlobalVelocity.TargetChart X x)
    (W : Submodule ℂ (TangentFiber X x)) (v : TangentFiber X x) :
    chartEvaluation C v ∈ W.map (chartEvaluation C) ↔ v ∈ W := by
  constructor
  · rintro ⟨w, hw, he⟩
    exact (chartEvaluation_injective C he) ▸ hw
  · intro hv
    exact ⟨v, hv, rfl⟩

end LeBrunSalamon.Construction.Lines.IntrinsicTangent

end

/-!
## The original tangent vector of an actual infinitesimal point

A point lift is turned into a family over Spec(C) using the actual
base-change projection. Its variation therefore lies in the original
fiber of the tangent sheaf. The local differential pairing recovers the
actual epsilon coefficient. This construction supplies the normalized
source vector used by the manuscript, without an arbitrary tangent
identification or a tangent-vector existence assumption.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.PhaseThirty
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction
open LeBrunSalamon.P1Charts

namespace LeBrunSalamon.Construction.Lines.SourceTangent

open FamilyVariation LocalVelocityComparison

/-- The base-change projection is the actual inverse of the canonical
inclusion of Dual into the thickening of Spec(C). -/
theorem parameter_dualBaseInclusion :
    DualThickening.parameter (𝟙 ComplexBase) ≫ dualBaseInclusion =
      𝟙 (DualThickening.space (𝟙 ComplexBase)) := by
  apply pullback.hom_ext
  · change (DualThickening.parameter (𝟙 ComplexBase) ≫ dualBaseInclusion) ≫
        DualThickening.projection (𝟙 ComplexBase) =
      𝟙 _ ≫ DualThickening.projection (𝟙 ComplexBase)
    simp only [dualBaseInclusion, DualThickening.projection, Category.assoc,
      pullback.lift_fst, Category.id_comp]
    exact (DualThickening.parameter_overC (𝟙 ComplexBase)).trans
      (Category.comp_id _)
  · change (DualThickening.parameter (𝟙 ComplexBase) ≫ dualBaseInclusion) ≫
        DualThickening.parameter (𝟙 ComplexBase) =
      𝟙 _ ≫ DualThickening.parameter (𝟙 ComplexBase)
    rw [Category.assoc, dualBaseInclusion_parameter, Category.comp_id,
      Category.id_comp]

/-- The normalization is fixed by the two actual pullback projections. -/
def dualBaseIso : DualThickening.space (𝟙 ComplexBase) ≅ Infinitesimal.DualScheme where
  hom := DualThickening.parameter (𝟙 ComplexBase)
  inv := dualBaseInclusion
  hom_inv_id := parameter_dualBaseInclusion
  inv_hom_id := dualBaseInclusion_parameter

@[simp] theorem dualBaseInclusion_projection :
    dualBaseInclusion ≫ DualThickening.projection (𝟙 ComplexBase) =
      Infinitesimal.dualToC := by
  simp [dualBaseInclusion, DualThickening.projection]

/-- The actual Γ(Spec C) scalar of a base function. -/
def baseScalar : RingSections ComplexBase ⊤ →+* ℂ :=
  (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom

/-- Pulling a base function to Dual gives its canonical constant dual
number. This retains both Γ–Spec normalizations. -/
theorem dualBaseInclusion_projectionFunction
    (a : RingSections ComplexBase ⊤) :
    DualMixedBridge.dualGlobalEquiv
      (dualBaseInclusion.appTop
        ((DualThickening.projection (𝟙 ComplexBase)).appTop a)) =
      algebraMap ℂ Infinitesimal.Dual (baseScalar a) := by
  change (Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).hom
    (((DualThickening.projection (𝟙 ComplexBase)).appTop ≫
      dualBaseInclusion.appTop) a) = _
  rw [← Scheme.Hom.comp_appTop, dualBaseInclusion_projection]
  exact congrArg (fun k :
    (Spec (CommRingCat.of ℂ)).presheaf.obj (op ⊤) ⟶
      CommRingCat.of Infinitesimal.Dual => k a)
    (Scheme.ΓSpecIso_naturality
      (CommRingCat.ofHom (algebraMap ℂ Infinitesimal.Dual)))

/-- The nilpotent parameter pulls back to epsilon, with coefficient one. -/
theorem dualBaseInclusion_epsilon :
    DualMixedBridge.dualGlobalEquiv
      (dualBaseInclusion.appTop (DualThickening.epsilonOn (𝟙 ComplexBase) ⊤)) =
      Infinitesimal.epsilon := by
  have he : DualThickening.epsilonOn (𝟙 ComplexBase) ⊤ =
      (DualThickening.parameter (𝟙 ComplexBase)).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).inv
          Infinitesimal.epsilon) := by
    simp [DualThickening.epsilonOn]
  rw [he]
  change (Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).hom
    (((DualThickening.parameter (𝟙 ComplexBase)).appTop ≫
      dualBaseInclusion.appTop)
      ((Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).inv
        Infinitesimal.epsilon)) = _
  rw [← Scheme.Hom.comp_appTop, dualBaseInclusion_parameter]
  change (Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).hom
      ((Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).inv
        Infinitesimal.epsilon) = _
  exact Iso.inv_hom_id_apply _ _

/-- The reviewed two-coefficient normal form on the actual thickening
agrees with the original algebraic normal form on Dual. -/
theorem dualBaseInclusion_normalForm (a b : RingSections ComplexBase ⊤) :
    DualMixedBridge.dualGlobalEquiv
      (dualBaseInclusion.appTop (DualThickening.normalForm (𝟙 ComplexBase) ⊤ a b)) =
      algebraMap ℂ Infinitesimal.Dual (baseScalar a) +
        Infinitesimal.epsilon * algebraMap ℂ Infinitesimal.Dual (baseScalar b) := by
  unfold DualThickening.normalForm
  simp only [map_add, map_mul]
  change DualMixedBridge.dualGlobalEquiv
      (dualBaseInclusion.appTop ((DualThickening.projection (𝟙 ComplexBase)).appTop a)) +
    DualMixedBridge.dualGlobalEquiv
        (dualBaseInclusion.appTop (DualThickening.epsilonOn (𝟙 ComplexBase) ⊤)) *
      DualMixedBridge.dualGlobalEquiv
        (dualBaseInclusion.appTop ((DualThickening.projection (𝟙 ComplexBase)).appTop b)) = _
  rw [dualBaseInclusion_projectionFunction, dualBaseInclusion_projectionFunction,
    dualBaseInclusion_epsilon]

/-- Coefficient extraction on the thickening of Spec(C) has precisely
the usual scalar epsilon coefficient after its canonical identification. -/
theorem coefficient_baseScalar
    (z : RingSections (DualThickening.space (𝟙 ComplexBase)) ⊤) :
    baseScalar (DualThickening.coefficient (𝟙 ComplexBase) ⊤ z) =
      Infinitesimal.linearCoefficient
        (DualMixedBridge.dualGlobalEquiv (dualBaseInclusion.appTop z)) := by
  conv_rhs => rw [DualThickening.reconstruct (𝟙 ComplexBase) ⊤ z]
  rw [dualBaseInclusion_normalForm, Infinitesimal.linearCoefficient_normalForm]

/-- An actual infinitesimal point is an actual family over Spec(C).
The central point and its complex structure are retained explicitly. -/
def pointDeformation {Y : Scheme} {sY : Y ⟶ ComplexBase}
    {y : PointsOver ComplexBase (𝟙 ComplexBase) Y sY}
    (τ : Infinitesimal.PointLift Y sY y) :
    Deformation (𝟙 ComplexBase) sY y.val where
  map := DualThickening.parameter (𝟙 ComplexBase) ≫ τ.map
  overC := by
    rw [Category.assoc, τ.overC]
    exact DualThickening.parameter_overC (𝟙 ComplexBase)
  reduces := by
    rw [← Category.assoc, DualThickening.zeroSection_parameter,
      Category.id_comp, τ.reduces]

@[simp] theorem pointDeformation_onDual {Y : Scheme} {sY : Y ⟶ ComplexBase}
    {y : PointsOver ComplexBase (𝟙 ComplexBase) Y sY}
    (τ : Infinitesimal.PointLift Y sY y) :
    dualBaseInclusion ≫ (pointDeformation τ).map = τ.map := by
  change dualBaseInclusion ≫ (DualThickening.parameter (𝟙 ComplexBase) ≫ τ.map) = _
  rw [← Category.assoc, dualBaseInclusion_parameter, Category.id_comp]

/-- The family's support is the original marked point, on every local
function domain containing that point. -/
theorem pointDeformation_support {Y : Scheme} {sY : Y ⟶ ComplexBase}
    {y : PointsOver ComplexBase (𝟙 ComplexBase) Y sY}
    (τ : Infinitesimal.PointLift Y sY y) (U : Y.Opens)
    (hy : ⊤ ≤ y.val ⁻¹ᵁ U) : ⊤ ≤ (pointDeformation τ).map ⁻¹ᵁ U := by
  rw [DualThickening.preimage_eq (𝟙 ComplexBase)
    (pointDeformation τ).map y.val (pointDeformation τ).reduces U]
  intro z _
  exact hy trivial

/-- The normalized family coefficient on a genuine local function is
exactly differentiation along the originally supplied dual-number point. -/
theorem pointDeformation_onFunction {Y : Scheme} {sY : Y ⟶ ComplexBase}
    {y : PointsOver ComplexBase (𝟙 ComplexBase) Y sY}
    (τ : Infinitesimal.PointLift Y sY y) (U : Y.Opens)
    (hy : ⊤ ≤ y.val ⁻¹ᵁ U) (hτ : ⊤ ≤ τ.map ⁻¹ᵁ U)
    (a : RingSections Y U) :
    baseScalar (ComplexBase.presheaf.map (homOfLE hy).op
      ((pointDeformation τ).onFunction U a)) =
      derivativeAlong τ.map τ.overC U hτ a := by
  let D := pointDeformation τ
  have hr : DualThickening.functionPullback (𝟙 ComplexBase) D.map y.val D.reduces U ≫
      (DualThickening.space (𝟙 ComplexBase)).presheaf.map
        (((TopologicalSpace.Opens.map (DualThickening.projection (𝟙 ComplexBase)).base).map
          (homOfLE hy)).op) = D.map.appLE U ⊤ (pointDeformation_support τ U hy) := by
    unfold DualThickening.functionPullback
    rw [Scheme.Hom.appLE_map]
    rfl
  have hc := DualThickening.coefficient_restrict (𝟙 ComplexBase) (homOfLE hy)
    (DualThickening.functionPullback (𝟙 ComplexBase) D.map y.val D.reduces U a)
  have hra : (DualThickening.space (𝟙 ComplexBase)).presheaf.map
        (((TopologicalSpace.Opens.map (DualThickening.projection (𝟙 ComplexBase)).base).map
          (homOfLE hy)).op)
      (DualThickening.functionPullback (𝟙 ComplexBase) D.map y.val D.reduces U a) =
        D.map.appLE U ⊤ (pointDeformation_support τ U hy) a :=
    congrArg (fun k => k a) hr
  rw [hra] at hc
  change DualThickening.coefficient (𝟙 ComplexBase) ⊤
      (D.map.appLE U ⊤ (pointDeformation_support τ U hy) a) =
    ComplexBase.presheaf.map (homOfLE hy).op (D.onFunction U a) at hc
  rw [← hc, coefficient_baseScalar]
  have hp : D.map.appLE U ⊤ (pointDeformation_support τ U hy) ≫
      dualBaseInclusion.appTop = τ.map.appLE U ⊤ hτ := by
    change D.map.appLE U ⊤ (pointDeformation_support τ U hy) ≫
      dualBaseInclusion.app ⊤ = τ.map.appLE U ⊤ hτ
    rw [dualBaseInclusion.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
    exact DualThickening.appLE_of_map_eq (pointDeformation_onDual τ) U ⊤ _ _
  exact congrArg (fun k => Infinitesimal.linearCoefficient
    (DualMixedBridge.dualGlobalEquiv (k a))) hp

/-- The tangent vector is in the original tangent-sheaf fiber. It is
constructed from the actual point family and normalized dual base change. -/
def pointVector {d : ℕ} (Y : SmoothProperComplexVariety d)
    (y : ComplexPoint Y)
    (τ : Infinitesimal.PointLift Y.scheme Y.structureMap ⟨y.map, y.overC⟩) :
    TangentFiber Y y := (pointDeformation τ).variation Y

/-- This local pairing uses the original universal cotangent differential
and tests all functions on the chosen neighborhood. -/
theorem pointVector_local_pairing {d : ℕ} (Y : SmoothProperComplexVariety d)
    (y : ComplexPoint Y)
    (τ : Infinitesimal.PointLift Y.scheme Y.structureMap ⟨y.map, y.overC⟩)
    (U : Y.scheme.Opens) (hy : ⊤ ≤ y.map ⁻¹ᵁ U) (hτ : ⊤ ≤ τ.map ⁻¹ᵁ U)
    (a : RingSections Y.scheme U) :
    PositiveFrame.localScalarPairing y.map (dualEvaluation (cotangentSheaf Y.structureMap))
        U hy ((cotangentPresentation Y.structureMap).differential.apply U a)
        (pointVector Y y τ) = derivativeAlong τ.map τ.overC U hτ a := by
  let D := pointDeformation τ
  let e := pullLocalSection y.map (cotangentSheaf Y.structureMap) U
    ((cotangentPresentation Y.structureMap).differential.apply U a)
  have hn := (PositiveVelocityPairing.pulledEvaluation y.map Y.structureMap).naturality
    (homOfLE hy)
    (TwoChartSections.restrictValue (pullbackModule y.map (tangentSheaf Y.structureMap))
      le_top (D.variation Y)) e
  rw [PositiveVelocityPairing.variation_pairing Y D, D.cotangentHom_differential U a] at hn
  change ComplexBase.presheaf.map (homOfLE hy).op (D.onFunction U a) =
    (PositiveVelocityPairing.pulledEvaluation y.map Y.structureMap).apply ⊤
      (TwoChartSections.restrictValue (pullbackModule y.map (tangentSheaf Y.structureMap)) hy
        (TwoChartSections.restrictValue (pullbackModule y.map (tangentSheaf Y.structureMap))
          le_top (D.variation Y)))
      ((pullbackModule y.map (cotangentSheaf Y.structureMap)).presheaf.map
        (homOfLE hy).op e) at hn
  rw [TwoChartSections.restrictValue_comp] at hn
  have htop : TwoChartSections.restrictValue
      (pullbackModule y.map (tangentSheaf Y.structureMap))
      (show (⊤ : ComplexBase.Opens) ≤ ⊤ from le_rfl) (D.variation Y) = D.variation Y := by
    simp [TwoChartSections.restrictValue]
  rw [htop] at hn
  change baseScalar
    ((PositiveVelocityPairing.pulledEvaluation y.map Y.structureMap).apply ⊤
      (D.variation Y) ((pullbackModule y.map (cotangentSheaf Y.structureMap)).presheaf.map
        (homOfLE hy).op e)) = _
  rw [← hn]
  exact pointDeformation_onFunction τ U hy hτ a

/-- A single genuinely nonzero local derivative proves nonvanishing of
the constructed original fiber vector. -/
theorem pointVector_ne_zero_of_derivative {d : ℕ}
    (Y : SmoothProperComplexVariety d) (y : ComplexPoint Y)
    (τ : Infinitesimal.PointLift Y.scheme Y.structureMap ⟨y.map, y.overC⟩)
    (U : Y.scheme.Opens) (hy : ⊤ ≤ y.map ⁻¹ᵁ U) (hτ : ⊤ ≤ τ.map ⁻¹ᵁ U)
    (a : RingSections Y.scheme U)
    (ha : derivativeAlong τ.map τ.overC U hτ a ≠ 0) : pointVector Y y τ ≠ 0 := by
  intro hz
  have h := pointVector_local_pairing Y y τ U hy hτ a
  rw [hz, map_zero] at h
  exact ha h.symm

/-- The actual marked point, viewed in the original smooth source variety. -/
def sourcePoint (p : ProjectiveLinePoint canonicalProjectiveLine) :
    ComplexPoint (projectiveLineVariety canonicalProjectiveLine) := ⟨p.map, p.overC⟩

/-- The source tangent vector selected by the original nonconstant
polynomial lift at the marking; the marking's coordinate remains c. -/
def sourceVector (p : ProjectiveLinePoint canonicalProjectiveLine) :
    TangentFiber (projectiveLineVariety canonicalProjectiveLine) (sourcePoint p) :=
  pointVector (projectiveLineVariety canonicalProjectiveLine) (sourcePoint p)
    (PolynomialSourceLift.atMarking p)

/-- Its value on any local source function is the derivative along the
same actual source lift used in the velocity construction. -/
theorem sourceVector_local_pairing
    (p : ProjectiveLinePoint canonicalProjectiveLine)
    (U : ProjectiveLine.Opens) (hp : ⊤ ≤ p.map ⁻¹ᵁ U)
    (hτ : ⊤ ≤ (PolynomialSourceLift.atMarking p).map ⁻¹ᵁ U)
    (a : RingSections ProjectiveLine U) :
    PositiveFrame.localScalarPairing p.map
        (dualEvaluation (cotangentSheaf canonicalProjectiveLine.structureMap))
        U hp ((cotangentPresentation canonicalProjectiveLine.structureMap).differential.apply U a)
        (sourceVector p) =
      derivativeAlong (PolynomialSourceLift.atMarking p).map
        (PolynomialSourceLift.atMarking p).overC U hτ a :=
  pointVector_local_pairing (projectiveLineVariety canonicalProjectiveLine)
    (sourcePoint p) (PolynomialSourceLift.atMarking p) U hp hτ a

/-- The coordinate section is the inverse image of X under the actual
polynomial chart isomorphism, not an unspecified local parameter. -/
def sourceCoordinate (p : ProjectiveLinePoint canonicalProjectiveLine) :
    RingSections ProjectiveLine (chartOpen (PolynomialSourceLift.markingChart p).index) :=
  (P1TwistFrames.polynomialChartRingEquiv
    (PolynomialSourceLift.markingChart p).index).symm Polynomial.X

/-- The original source tangent vector differentiates this actual
coordinate with value one. -/
theorem sourceVector_coordinate
    (p : ProjectiveLinePoint canonicalProjectiveLine)
    (hp : ⊤ ≤ p.map ⁻¹ᵁ chartOpen (PolynomialSourceLift.markingChart p).index)
    (hτ : ⊤ ≤ (PolynomialSourceLift.atMarking p).map ⁻¹ᵁ
      chartOpen (PolynomialSourceLift.markingChart p).index) :
    PositiveFrame.localScalarPairing p.map
        (dualEvaluation (cotangentSheaf canonicalProjectiveLine.structureMap))
        (chartOpen (PolynomialSourceLift.markingChart p).index) hp
        ((cotangentPresentation canonicalProjectiveLine.structureMap).differential.apply
          (chartOpen (PolynomialSourceLift.markingChart p).index) (sourceCoordinate p))
        (sourceVector p) = 1 := by
  rw [sourceVector_local_pairing p _ hp hτ, PolynomialSourceLift.derivativeAlong_atMarking]
  unfold sourceCoordinate
  rw [RingEquiv.apply_symm_apply]
  exact PolynomialSourceLift.derivation_X (PolynomialSourceLift.markingChart p).coordinate

/-- Nonconstancy of the dual test is converted into nonvanishing of an
actual original tangent vector by the proved coordinate normalization. -/
theorem sourceVector_ne_zero (p : ProjectiveLinePoint canonicalProjectiveLine) :
    sourceVector p ≠ 0 := by
  let i := (PolynomialSourceLift.markingChart p).index
  let c := (PolynomialSourceLift.markingChart p).coordinate
  have hp : ⊤ ≤ p.map ⁻¹ᵁ chartOpen i := by
    rw [← (PolynomialSourceLift.markingChart p).identifies]
    exact PolynomialSourceLift.point_top_le_chart i c
  have hτ : ⊤ ≤ (PolynomialSourceLift.atMarking p).map ⁻¹ᵁ chartOpen i :=
    PolynomialSourceLift.mapAt_top_le_chart i c
  intro hz
  have h := sourceVector_coordinate p hp hτ
  rw [hz, map_zero] at h
  exact zero_ne_one h


/-! ### Actual local scalar pairings and composition of fiber pullbacks -/

/-- Postcomposing a sheaf pairing commutes with the canonical pullback
pairing because both have the same value on every pulled local tensor. -/
theorem pullbackPair_postcompose {T Y : Scheme} (f : T ⟶ Y)
    {E F G H : OModule Y} (b : SheafBilinearMap E F G) (h : G ⟶ H) :
    pullbackPair f (b.postcompose h) =
      (pullbackPair f b).postcompose ((Scheme.Modules.pullback f).map h) := by
  have hn : IsPullbackPair f (b.postcompose h)
      ((pullbackPair f b).postcompose ((Scheme.Modules.pullback f).map h)) := by
    intro U e z
    change ((Scheme.Modules.pullback f).map h).app (f ⁻¹ᵁ U)
      ((pullbackPair f b).apply (f ⁻¹ᵁ U)
        (pullLocalSection f E U e) (pullLocalSection f F U z)) =
      pullLocalSection f H U (h.app U (b.apply U e z))
    rw [pullbackPair_normalized]
    exact (LeviFiberGeometry.pullLocalSection_map f h U (b.apply U e z)).symm
  exact ((Classical.choose_spec (pullbackPair_existsUnique f (b.postcompose h))).2 _ hn).symm

/-- The corresponding equality retains the original actual fiber maps. -/
theorem fiberPair_postcompose {Y : Scheme} (x : ComplexBase ⟶ Y)
    {E F G H : OModule Y} (b : SheafBilinearMap E F G) (h : G ⟶ H)
    (u : Fiber E x) (v : Fiber F x) :
    LeviFiberGeometry.fiberPair (b.postcompose h) x u v =
      fiberMap h x (LeviFiberGeometry.fiberPair b x u v) := by
  change (pullbackPair x (b.postcompose h)).apply ⊤ u v = _
  rw [pullbackPair_postcompose]
  rfl

/-- Fiber pairing with a mapped first vector is exactly precomposition
by the original sheaf morphism. No choice of a fiber frame is involved. -/
theorem fiberPair_precompose {Y : Scheme} (x : ComplexBase ⟶ Y)
    {E E' F F' G : OModule Y} (b : SheafBilinearMap E F G)
    (h : E' ⟶ E) (k : F' ⟶ F) (u : Fiber E' x) (v : Fiber F' x) :
    LeviFiberGeometry.fiberPair (b.precompose h k) x u v =
      LeviFiberGeometry.fiberPair b x (fiberMap h x u) (fiberMap k x v) := by
  change (pullbackPair x (b.precompose h k)).apply ⊤ u v = _
  rw [LeviFiberGeometry.pullbackPair_precompose]
  rfl

/-- A local section has the same fiber value after restriction to any
smaller actual neighborhood of the point. -/
theorem localFiberValue_restrict {Y : Scheme} (x : ComplexBase ⟶ Y)
    (E : OModule Y) {U V : Y.Opens} (hUV : U ≤ V)
    (hU : ⊤ ≤ x ⁻¹ᵁ U) (hV : ⊤ ≤ x ⁻¹ᵁ V) (s : SectionsOn E V) :
    PositiveFrame.localFiberValue x E U hU (E.presheaf.map (homOfLE hUV).op s) =
      PositiveFrame.localFiberValue x E V hV s := by
  have hn := (sheafHom_naturality
    ((Scheme.Modules.pullbackPushforwardAdjunction x).unit.app E)
    (homOfLE hUV) s).symm
  change pullLocalSection x E U (E.presheaf.map (homOfLE hUV).op s) =
    (pullbackModule x E).presheaf.map
      (((TopologicalSpace.Opens.map x.base).map (homOfLE hUV)).op)
      (pullLocalSection x E V s) at hn
  unfold PositiveFrame.localFiberValue
  rw [hn, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- The local functional is independent of shrinking its function domain. -/
theorem localScalarPairing_restrict {Y : Scheme} (x : ComplexBase ⟶ Y)
    {E F : OModule Y} (b : SheafBilinearMap E F (structureModule Y))
    {U V : Y.Opens} (hUV : U ≤ V)
    (hU : ⊤ ≤ x ⁻¹ᵁ U) (hV : ⊤ ≤ x ⁻¹ᵁ V) (t : SectionsOn F V)
    (u : Fiber E x) :
    PositiveFrame.localScalarPairing x b U hU
        (F.presheaf.map (homOfLE hUV).op t) u =
      PositiveFrame.localScalarPairing x b V hV t u := by
  change PositiveFrame.scalarFiberValue x
    (LeviFiberGeometry.fiberPair b x u
      (PositiveFrame.localFiberValue x F U hU (F.presheaf.map (homOfLE hUV).op t))) = _
  rw [localFiberValue_restrict]
  rfl

/-- Naturality in both arguments of the actual local scalar pairing. -/
theorem localScalarPairing_precompose {Y : Scheme} (x : ComplexBase ⟶ Y)
    {E E' F F' : OModule Y} (b : SheafBilinearMap E F (structureModule Y))
    (h : E' ⟶ E) (k : F' ⟶ F)
    (U : Y.Opens) (hU : ⊤ ≤ x ⁻¹ᵁ U) (t : SectionsOn F' U) (u : Fiber E' x) :
    PositiveFrame.localScalarPairing x (b.precompose h k) U hU t u =
      PositiveFrame.localScalarPairing x b U hU (k.app U t) (fiberMap h x u) := by
  change PositiveFrame.scalarFiberValue x
    (LeviFiberGeometry.fiberPair (b.precompose h k) x u
      (PositiveFrame.localFiberValue x F' U hU t)) = _
  rw [fiberPair_precompose, ← PositiveFrame.localFiberValue_map]
  rfl

/-- The actual composition pullback transports the fiber value of every
local section, including a section defined only near the image point. -/
theorem localFiberValue_composition {T Y : Scheme} (f : T ⟶ Y)
    (p : ComplexBase ⟶ T) (x : ComplexBase ⟶ Y) (hx : p ≫ f = x)
    (E : OModule Y) (U : Y.Opens)
    (hp : ⊤ ≤ p ⁻¹ᵁ (f ⁻¹ᵁ U)) (hU : ⊤ ≤ x ⁻¹ᵁ U) (t : SectionsOn E U) :
    fiberComposition f p x hx E
      (PositiveFrame.localFiberValue p (pullbackModule f E) (f ⁻¹ᵁ U) hp
        (pullLocalSection f E U t)) =
      PositiveFrame.localFiberValue x E U hU t := by
  subst x
  change ((compositionPullback p f (p ≫ f) rfl E).hom.app ⊤)
    ((pullbackModule p (pullbackModule f E)).presheaf.map (homOfLE hp).op
      (pullLocalSection p (pullbackModule f E) (f ⁻¹ᵁ U)
        (pullLocalSection f E U t))) = _
  simp only [compositionPullback, Iso.trans_hom, eqToIso_refl,
    Iso.refl_hom, Iso.app_hom, Category.comp_id]
  rw [← sheafHom_naturality]
  exact congrArg (fun s : SectionsOn (pullbackModule (p ≫ f) E) ((p ≫ f) ⁻¹ᵁ U) =>
    (pullbackModule (p ≫ f) E).presheaf.map (homOfLE hU).op s)
    (ContactPositiveIsotropy.pullbackComp_hom_pullLocalSection p f E U t)

/-- The scalar comparison of a composite fiber is the composite of its
actual unit-pullback maps. -/
theorem scalarFiberValue_composition {T Y : Scheme} (f : T ⟶ Y)
    (p : ComplexBase ⟶ T) (x : ComplexBase ⟶ Y) (hx : p ≫ f = x)
    (z : Fiber (pullbackModule f (structureModule Y)) p) :
    PositiveFrame.scalarFiberValue x
        (fiberComposition f p x hx (structureModule Y) z) =
      PositiveFrame.scalarFiberValue p (fiberMap (unitPullbackMap f) p z) := by
  subst x
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
      ((unitPullbackMap (p ≫ f)).app ⊤
        ((compositionPullback p f (p ≫ f) rfl (structureModule Y)).hom.app ⊤ z)) =
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
      ((unitPullbackMap p).app ⊤
        (((Scheme.Modules.pullback p).map (unitPullbackMap f)).app ⊤ z))
  apply congrArg (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
  change ((compositionPullback p f (p ≫ f) rfl (structureModule Y)).hom ≫
      unitPullbackMap (p ≫ f)).app ⊤ z =
    ((Scheme.Modules.pullback p).map (unitPullbackMap f) ≫ unitPullbackMap p).app ⊤ z
  simp only [compositionPullback, Iso.trans_hom, eqToIso_refl,
    Iso.refl_hom, Iso.app_hom, Category.comp_id]
  rw [unitPullbackMap_comp_hom]

/-- The scalar pairing of the transported original fiber vector is the
actual pulled-back pairing on the source. This is the normalization
needed by both the source chain rule and the positive-variation argument. -/
theorem localScalarPairing_composition {T Y : Scheme} (f : T ⟶ Y)
    (p : ComplexBase ⟶ T) (x : ComplexBase ⟶ Y) (hx : p ≫ f = x)
    {E F : OModule Y} (b : SheafBilinearMap E F (structureModule Y))
    (U : Y.Opens) (hp : ⊤ ≤ p ⁻¹ᵁ (f ⁻¹ᵁ U)) (hU : ⊤ ≤ x ⁻¹ᵁ U)
    (t : SectionsOn F U) (u : Fiber (pullbackModule f E) p) :
    PositiveFrame.localScalarPairing x b U hU t
        (fiberComposition f p x hx E u) =
      PositiveFrame.localScalarPairing p
        ((pullbackPair f b).postcompose (unitPullbackMap f))
        (f ⁻¹ᵁ U) hp (pullLocalSection f F U t) u := by
  change PositiveFrame.scalarFiberValue x
    (LeviFiberGeometry.fiberPair b x (fiberComposition f p x hx E u)
      (PositiveFrame.localFiberValue x F U hU t)) = _
  rw [← localFiberValue_composition f p x hx F U hp hU t,
    ← ContactPositiveIsotropy.fiberComposition_pair f p x hx b,
    scalarFiberValue_composition,
    ← fiberPair_postcompose]
  rfl

/-! ### The canonical differential on actual local functions -/

/-- This elementary adjunction equation is proved directly, so the
historical admitted cotangentMap_adjoint wrapper is not inherited. -/
theorem cotangentMap_adjoint_proved {Y Z S : Scheme} (f : Y ⟶ Z) (s : Z ⟶ S) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ (cotangentMap f s) =
      differentialLift (pulledFunctionDifferential f s) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).apply_symm_apply _

/-- The original cotangent morphism sends the original local da to d(f#a). -/
theorem cotangentMap_differential {Y Z S : Scheme}
    (f : Y ⟶ Z) (s : Z ⟶ S) (U : Z.Opens) (a : RingSections Z U) :
    (cotangentMap f s).app (f ⁻¹ᵁ U)
      (pullLocalSection f (cotangentSheaf s) U
        ((cotangentPresentation s).differential.apply U a)) =
      (cotangentPresentation (f ≫ s)).differential.apply (f ⁻¹ᵁ U) (f.app U a) := by
  have h := congrArg (fun D : RelativeSheafDerivation s
      ((Scheme.Modules.pushforward f).obj (cotangentSheaf (f ≫ s))) => D.apply U a)
    (differentialLift_spec (pulledFunctionDifferential f s))
  rw [← cotangentMap_adjoint_proved f s] at h
  exact h

/-- Base-map equality transports the same universal differential. -/
theorem differential_transport {Y S : Scheme} (s t : Y ⟶ S) (h : s = t)
    (U : Y.Opens) (a : RingSections Y U) :
    (eqToHom (congrArg cotangentSheaf h)).app U
        ((cotangentPresentation s).differential.apply U a) =
      (cotangentPresentation t).differential.apply U a := by
  subst t
  rfl

/-- Equality of the base maps transports the dual evaluation contravariantly
in its cotangent argument and covariantly in its tangent argument. -/
theorem dualEvaluation_transport {Y S : Scheme} (s t : Y ⟶ S) (h : s = t)
    (U : Y.Opens) (v : SectionsOn (tangentSheaf s) U)
    (a : SectionsOn (cotangentSheaf t) U) :
    (dualEvaluation (cotangentSheaf t)).apply U
        ((eqToHom (congrArg tangentSheaf h)).app U v) a =
      (dualEvaluation (cotangentSheaf s)).apply U v
        ((eqToHom (congrArg cotangentSheaf h.symm)).app U a) := by
  subst t
  rfl

/-- The canonical unadjusted tangent map is characterized by evaluation
against the actual cotangent differential, directly from currying. -/
theorem tangentMapRaw_evaluate {Y Z S : Scheme} (f : Y ⟶ Z) (s : Z ⟶ S)
    (U : Y.Opens) (v : SectionsOn (tangentSheaf (f ≫ s)) U)
    (a : SectionsOn (pullbackModule f (cotangentSheaf s)) U) :
    (dualEvaluation (pullbackModule f (cotangentSheaf s))).apply U
        ((tangentMapRaw f s).app U v) a =
      (dualEvaluation (cotangentSheaf (f ≫ s))).apply U v
        ((cotangentMap f s).app U a) := by
  let k := tensorMap (𝟙 (tangentSheaf (f ≫ s))) (cotangentMap f s) ≫
    (internalHomPresentation (cotangentSheaf (f ≫ s)) (structureModule Y)).evaluate
  have h := congrArg (fun m :
      tensorSheaf (tangentSheaf (f ≫ s)) (pullbackModule f (cotangentSheaf s)) ⟶
        structureModule Y => m.app U
      ((tensorPresentation (tangentSheaf (f ≫ s))
        (pullbackModule f (cotangentSheaf s))).pair.apply U v a))
    (currySheaf_evaluate k)
  change (internalHomPresentation (pullbackModule f (cotangentSheaf s))
      (structureModule Y)).evaluate.app U
    ((tensorMap (currySheaf k) (𝟙 _)).app U
      ((tensorPresentation (tangentSheaf (f ≫ s))
        (pullbackModule f (cotangentSheaf s))).pair.apply U v a)) =
    (internalHomPresentation (cotangentSheaf (f ≫ s)) (structureModule Y)).evaluate.app U
      ((tensorMap (𝟙 (tangentSheaf (f ≫ s))) (cotangentMap f s)).app U
        ((tensorPresentation (tangentSheaf (f ≫ s))
          (pullbackModule f (cotangentSheaf s))).pair.apply U v a)) at h
  rw [tensorMap_apply, tensorMap_apply] at h
  exact h

/-- The original differentialOver is normalized by the canonical dual
base-change morphism used in its definition. -/
theorem differentialOver_baseChange {d e : ℕ}
    (Y : SmoothProperComplexVariety d) (Z : SmoothProperComplexVariety e)
    (f : Y.scheme ⟶ Z.scheme) (hf : f ≫ Z.structureMap = Y.structureMap) :
    differentialOver Y Z f hf ≫ dualBaseChange f (cotangentSheaf Z.structureMap) =
      eqToHom (congrArg tangentSheaf hf.symm) ≫ tangentMapRaw f Z.structureMap := by
  letI := dualBaseChange_isIso f
    (smooth_cotangent_rank Z.structureMap e Z.smooth)
  simp only [differentialOver, Category.assoc, asIso_inv, IsIso.inv_hom_id,
    Category.comp_id]

/-- The cotangent morphism over the original equal structure map. -/
def cotangentOver {d e : ℕ}
    (Y : SmoothProperComplexVariety d) (Z : SmoothProperComplexVariety e)
    (f : Y.scheme ⟶ Z.scheme) (hf : f ≫ Z.structureMap = Y.structureMap) :
    pullbackModule f (cotangentSheaf Z.structureMap) ⟶ cotangentSheaf Y.structureMap :=
  cotangentMap f Z.structureMap ≫ eqToHom (congrArg cotangentSheaf hf)

/-- Actual sheaf-level chain rule, with no supplied tangent equivalence. -/
theorem differentialOver_evaluate {d e : ℕ}
    (Y : SmoothProperComplexVariety d) (Z : SmoothProperComplexVariety e)
    (f : Y.scheme ⟶ Z.scheme) (hf : f ≫ Z.structureMap = Y.structureMap)
    (U : Y.scheme.Opens) (v : SectionsOn (tangentSheaf Y.structureMap) U)
    (a : SectionsOn (pullbackModule f (cotangentSheaf Z.structureMap)) U) :
    (PositiveVelocityPairing.pulledEvaluation f Z.structureMap).apply U
        ((differentialOver Y Z f hf).app U v) a =
      (dualEvaluation (cotangentSheaf Y.structureMap)).apply U v
        ((cotangentOver Y Z f hf).app U a) := by
  change (unitPullbackMap f).app U
    ((pullbackPair f (dualEvaluation (cotangentSheaf Z.structureMap))).apply U
      ((differentialOver Y Z f hf).app U v) a) = _
  rw [← FamilyVariation.dualBaseChange_evaluate]
  have hd := congrArg (fun h : tangentSheaf Y.structureMap ⟶
      dualSheaf (pullbackModule f (cotangentSheaf Z.structureMap)) => h.app U v)
    (differentialOver_baseChange Y Z f hf)
  change (dualEvaluation (pullbackModule f (cotangentSheaf Z.structureMap))).apply U
    ((differentialOver Y Z f hf ≫ dualBaseChange f (cotangentSheaf Z.structureMap)).app U v) a = _
  rw [hd]
  change (dualEvaluation (pullbackModule f (cotangentSheaf Z.structureMap))).apply U
    ((tangentMapRaw f Z.structureMap).app U
      ((eqToHom (congrArg tangentSheaf hf.symm)).app U v)) a = _
  rw [tangentMapRaw_evaluate,
    dualEvaluation_transport Y.structureMap (f ≫ Z.structureMap) hf.symm]
  rfl

/-- The original local target differential is sent to the derivative of
its actual pullback function. -/
theorem cotangentOver_differential {d e : ℕ}
    (Y : SmoothProperComplexVariety d) (Z : SmoothProperComplexVariety e)
    (f : Y.scheme ⟶ Z.scheme) (hf : f ≫ Z.structureMap = Y.structureMap)
    (U : Z.scheme.Opens) (a : RingSections Z.scheme U) :
    (cotangentOver Y Z f hf).app (f ⁻¹ᵁ U)
      (pullLocalSection f (cotangentSheaf Z.structureMap) U
        ((cotangentPresentation Z.structureMap).differential.apply U a)) =
      (cotangentPresentation Y.structureMap).differential.apply (f ⁻¹ᵁ U) (f.app U a) := by
  change (eqToHom (congrArg cotangentSheaf hf)).app (f ⁻¹ᵁ U)
    ((cotangentMap f Z.structureMap).app (f ⁻¹ᵁ U)
      (pullLocalSection f (cotangentSheaf Z.structureMap) U
        ((cotangentPresentation Z.structureMap).differential.apply U a))) = _
  rw [cotangentMap_differential]
  exact differential_transport (f ≫ Z.structureMap) Y.structureMap hf
    (f ⁻¹ᵁ U) (f.app U a)

/-- The source tangent section differentiates the pullback of every
local target function by the canonical derivative of the morphism. -/
theorem differentialOver_local_function {d e : ℕ}
    (Y : SmoothProperComplexVariety d) (Z : SmoothProperComplexVariety e)
    (f : Y.scheme ⟶ Z.scheme) (hf : f ≫ Z.structureMap = Y.structureMap)
    (U : Z.scheme.Opens) (a : RingSections Z.scheme U)
    (v : SectionsOn (tangentSheaf Y.structureMap) (f ⁻¹ᵁ U)) :
    (PositiveVelocityPairing.pulledEvaluation f Z.structureMap).apply (f ⁻¹ᵁ U)
        ((differentialOver Y Z f hf).app (f ⁻¹ᵁ U) v)
        (pullLocalSection f (cotangentSheaf Z.structureMap) U
          ((cotangentPresentation Z.structureMap).differential.apply U a)) =
      tangentActs Y.structureMap (f ⁻¹ᵁ U) v (f.app U a) := by
  rw [differentialOver_evaluate, cotangentOver_differential]
  rfl


/-- Equality of the two normalized pairings on the whole source sheaf.
Pulling this equality to a point proves the chain rule on every fiber vector,
including vectors which were not supplied as values of global sections. -/
theorem differentialOver_pairing {d e : ℕ}
    (Y : SmoothProperComplexVariety d) (Z : SmoothProperComplexVariety e)
    (f : Y.scheme ⟶ Z.scheme) (hf : f ≫ Z.structureMap = Y.structureMap) :
    (PositiveVelocityPairing.pulledEvaluation f Z.structureMap).precompose
        (differentialOver Y Z f hf) (𝟙 _) =
      (dualEvaluation (cotangentSheaf Y.structureMap)).precompose
        (𝟙 _) (cotangentOver Y Z f hf) := by
  apply sheafBilinearMap_ext
  intro U v a
  exact differentialOver_evaluate Y Z f hf U v a

/-- The canonical derivative on the original point fibers, retaining the
specified equality identifying the image point with the marked target point. -/
def pointDifferential {d e : ℕ}
    (Y : SmoothProperComplexVariety d) (Z : SmoothProperComplexVariety e)
    (f : Y.scheme ⟶ Z.scheme) (hf : f ≫ Z.structureMap = Y.structureMap)
    (y : ComplexPoint Y) (z : ComplexPoint Z) (hyz : y.map ≫ f = z.map) :
    TangentFiber Y y →ₗ[ℂ] TangentFiber Z z :=
  (fiberComposition f y.map z.map hyz (tangentSheaf Z.structureMap)).comp
    (fiberMap (differentialOver Y Z f hf) y.map)

/-- Fiber-level chain rule for an arbitrary original tangent vector, tested
against any actual local target function at its image point. -/
theorem pointDifferential_local_pairing {d e : ℕ}
    (Y : SmoothProperComplexVariety d) (Z : SmoothProperComplexVariety e)
    (f : Y.scheme ⟶ Z.scheme) (hf : f ≫ Z.structureMap = Y.structureMap)
    (y : ComplexPoint Y) (z : ComplexPoint Z) (hyz : y.map ≫ f = z.map)
    (U : Z.scheme.Opens) (hy : ⊤ ≤ y.map ⁻¹ᵁ (f ⁻¹ᵁ U)) (hz : ⊤ ≤ z.map ⁻¹ᵁ U)
    (a : RingSections Z.scheme U) (v : TangentFiber Y y) :
    PositiveFrame.localScalarPairing z.map (dualEvaluation (cotangentSheaf Z.structureMap))
        U hz ((cotangentPresentation Z.structureMap).differential.apply U a)
        (pointDifferential Y Z f hf y z hyz v) =
      PositiveFrame.localScalarPairing y.map (dualEvaluation (cotangentSheaf Y.structureMap))
        (f ⁻¹ᵁ U) hy
        ((cotangentPresentation Y.structureMap).differential.apply (f ⁻¹ᵁ U) (f.app U a)) v := by
  change PositiveFrame.localScalarPairing z.map (dualEvaluation (cotangentSheaf Z.structureMap))
    U hz ((cotangentPresentation Z.structureMap).differential.apply U a)
    (fiberComposition f y.map z.map hyz (tangentSheaf Z.structureMap)
      (fiberMap (differentialOver Y Z f hf) y.map v)) = _
  rw [localScalarPairing_composition f y.map z.map hyz _ U hy hz]
  let t := pullLocalSection f (cotangentSheaf Z.structureMap) U
    ((cotangentPresentation Z.structureMap).differential.apply U a)
  have h₁ := localScalarPairing_precompose y.map
    (PositiveVelocityPairing.pulledEvaluation f Z.structureMap)
    (differentialOver Y Z f hf) (𝟙 _) (f ⁻¹ᵁ U) hy t v
  change PositiveFrame.localScalarPairing y.map
      ((PositiveVelocityPairing.pulledEvaluation f Z.structureMap).precompose
        (differentialOver Y Z f hf) (𝟙 _)) (f ⁻¹ᵁ U) hy t v =
    PositiveFrame.localScalarPairing y.map
      (PositiveVelocityPairing.pulledEvaluation f Z.structureMap)
      (f ⁻¹ᵁ U) hy t (fiberMap (differentialOver Y Z f hf) y.map v) at h₁
  change PositiveFrame.localScalarPairing y.map
    (PositiveVelocityPairing.pulledEvaluation f Z.structureMap)
    (f ⁻¹ᵁ U) hy t (fiberMap (differentialOver Y Z f hf) y.map v) = _
  rw [← h₁, differentialOver_pairing, localScalarPairing_precompose,
    PositiveFrame.fiberMap_id]
  change PositiveFrame.localScalarPairing y.map (dualEvaluation (cotangentSheaf Y.structureMap))
    (f ⁻¹ᵁ U) hy ((cotangentOver Y Z f hf).app (f ⁻¹ᵁ U) t) v = _
  dsimp only [t]
  rw [cotangentOver_differential]

/-- Composing an actual dual point with an actual morphism pulls back its
local functions before taking the same epsilon coefficient. -/
theorem derivativeAlong_push {Y Z : Scheme}
    {sY : Y ⟶ ComplexBase} {sZ : Z ⟶ ComplexBase}
    {y : PointsOver ComplexBase (𝟙 ComplexBase) Y sY}
    {z : PointsOver ComplexBase (𝟙 ComplexBase) Z sZ}
    (f : Y ⟶ Z) (hf : f ≫ sZ = sY) (hyz : y.val ≫ f = z.val)
    (τ : Infinitesimal.PointLift Y sY y)
    (U : Z.Opens) (hU : ⊤ ≤ τ.map ⁻¹ᵁ (f ⁻¹ᵁ U))
    (a : RingSections Z U) :
    derivativeAlong (Charts.AffineTangentLift.push f hf hyz τ).map
        (Charts.AffineTangentLift.push f hf hyz τ).overC U hU a =
      derivativeAlong τ.map τ.overC (f ⁻¹ᵁ U) hU (f.app U a) := by
  change Infinitesimal.linearCoefficient
    (DualMixedBridge.dualGlobalEquiv ((τ.map ≫ f).appLE U ⊤ hU a)) = _
  rw [Scheme.Hom.comp_appLE]
  rfl

/-- The original nodeDifferential is exactly the general canonical point
map above, specialized to the original projective source and marking. -/
theorem nodeDifferential_eq_pointDifferential {n : ℕ} {X : ContactFanoManifold n}
    (f : FreeLine X) (x : ComplexPoint X.variety)
    (hx : marking.map ≫ f.curve.map = x.map) :
    nodeDifferential f x hx =
      pointDifferential (projectiveLineVariety P) X.variety f.curve.map f.curve.overC
        (sourcePoint marking) x hx := rfl

/-- The source vector used in the first-jet family has the expected
original df-image on every local target differential. -/
theorem nodeDifferential_sourceVector_local_pairing
    {n : ℕ} {X : ContactFanoManifold n} (f : FreeLine X)
    (x : ComplexPoint X.variety) (hx : marking.map ≫ f.curve.map = x.map)
    (U : X.variety.scheme.Opens) (hxU : ⊤ ≤ x.map ⁻¹ᵁ U)
    (a : RingSections X.variety.scheme U) :
    PositiveFrame.localScalarPairing x.map (dualEvaluation (cotangentSheaf X.variety.structureMap))
        U hxU ((cotangentPresentation X.variety.structureMap).differential.apply U a)
        (nodeDifferential f x hx (sourceVector marking)) =
      derivativeAlong (PolynomialSourceLift.atMarking marking).map
        (PolynomialSourceLift.atMarking marking).overC (f.curve.map ⁻¹ᵁ U)
        (sourceLift_top_le_preimage P marking (PolynomialSourceLift.atMarking marking)
          f.curve.map x.map hx U (by rintro _ ⟨c, rfl⟩; exact hxU trivial))
        (f.curve.map.app U a) := by
  have hp : ⊤ ≤ marking.map ⁻¹ᵁ (f.curve.map ⁻¹ᵁ U) := by
    change ⊤ ≤ (marking.map ≫ f.curve.map) ⁻¹ᵁ U
    rw [hx]
    exact hxU
  rw [nodeDifferential_eq_pointDifferential]
  refine (pointDifferential_local_pairing (projectiveLineVariety P) X.variety
    f.curve.map f.curve.overC (sourcePoint marking) x hx U hp hxU a
    (sourceVector marking)).trans ?_
  exact sourceVector_local_pairing marking (f.curve.map ⁻¹ᵁ U) hp _ (f.curve.map.app U a)


/-- The actual point-vector construction is natural for the ORIGINAL
canonical differential. Affine-chart faithfulness converts the normalized
local-function calculation into equality of original tangent vectors. -/
theorem pointVector_push {d e : ℕ}
    (Y : SmoothProperComplexVariety d) (Z : SmoothProperComplexVariety e)
    (f : Y.scheme ⟶ Z.scheme) (hf : f ≫ Z.structureMap = Y.structureMap)
    (y : ComplexPoint Y) (z : ComplexPoint Z) (hyz : y.map ≫ f = z.map)
    (τ : Infinitesimal.PointLift Y.scheme Y.structureMap ⟨y.map, y.overC⟩) :
    pointVector Z z (Charts.AffineTangentLift.push f hf hyz τ) =
      pointDifferential Y Z f hf y z hyz (pointVector Y y τ) := by
  let C : GlobalVelocity.TargetChart Z z := (GlobalVelocity.targetChart_exists Z z).some
  let U := IntrinsicTangent.chartOpen C
  have hz : ⊤ ≤ z.map ⁻¹ᵁ U := IntrinsicTangent.chartOpen_point C
  have hy : ⊤ ≤ y.map ⁻¹ᵁ (f ⁻¹ᵁ U) := by
    change ⊤ ≤ (y.map ≫ f) ⁻¹ᵁ U
    rw [hyz]
    exact hz
  have hτ : ⊤ ≤ τ.map ⁻¹ᵁ (f ⁻¹ᵁ U) := by
    apply pointLift_top_le_preimage τ
    rintro _ ⟨c, rfl⟩
    exact hy trivial
  apply IntrinsicTangent.eq_of_affine_localAction Z.structureMap z.map
    (smooth_cotangent_rank Z.structureMap e Z.smooth)
    U (IntrinsicTangent.chartOpen_affine C) hz
  intro a
  change PositiveFrame.localScalarPairing z.map
      (dualEvaluation (cotangentSheaf Z.structureMap)) U hz
      ((cotangentPresentation Z.structureMap).differential.apply U a)
      (pointVector Z z (Charts.AffineTangentLift.push f hf hyz τ)) =
    PositiveFrame.localScalarPairing z.map
      (dualEvaluation (cotangentSheaf Z.structureMap)) U hz
      ((cotangentPresentation Z.structureMap).differential.apply U a)
      (pointDifferential Y Z f hf y z hyz (pointVector Y y τ))
  rw [pointVector_local_pairing Z z _ U hz hτ,
    pointDifferential_local_pairing Y Z f hf y z hyz U hy hz,
    pointVector_local_pairing Y y τ (f ⁻¹ᵁ U) hy hτ,
    derivativeAlong_push]

/-- The pushed nonconstant source test and the original node differential
produce exactly the same vector in the original target tangent fiber. -/
theorem nodeDifferential_sourceVector_eq_pointVector
    {n : ℕ} {X : ContactFanoManifold n} (f : FreeLine X)
    (x : ComplexPoint X.variety) (hx : marking.map ≫ f.curve.map = x.map) :
    nodeDifferential f x hx (sourceVector marking) =
      pointVector X.variety x
        (Charts.AffineTangentLift.push f.curve.map f.curve.overC hx
          (PolynomialSourceLift.atMarking marking)) := by
  symm
  exact pointVector_push (projectiveLineVariety P) X.variety
    f.curve.map f.curve.overC (sourcePoint marking) x hx
    (PolynomialSourceLift.atMarking marking)

/-- Every original source vector has contact-tangent df-image for a free
contact line. This uses the proved original sheaf contact-tangency equation,
not the historical positiveNodeSpace_horizontal admission. -/
theorem nodeDifferential_mem_contactPlane {n : ℕ} {X : ContactFanoManifold n}
    (f : FreeLine X) (x : ComplexPoint X.variety)
    (hx : marking.map ≫ f.curve.map = x.map)
    (v : Fiber (tangentSheaf P.structureMap) marking.map) :
    nodeDifferential f x hx v ∈ contactPlane X x := by
  change fiberMap X.contact.sequence.form x.map
    (fiberComposition f.curve.map marking.map x.map hx
      (tangentSheaf X.variety.structureMap)
      (fiberMap (ContactPositive.curveDifferential f) marking.map v)) = 0
  have hz : fiberMap (ContactPositive.curveDifferential f ≫ ContactPositive.contactProjection f)
      marking.map v = 0 := by
    rw [ContactPositive.curveDifferential_contact_zero]
    exact PositiveFrame.fiberMap_zero _ _ _ _
  have hq := (ContactPositive.fiberMap_comp (ContactPositive.curveDifferential f)
    (ContactPositive.contactProjection f) marking.map v).symm.trans hz
  have hn := ContactPositive.fiberComposition_naturality f.curve.map marking.map x.map hx
    X.contact.sequence.form (fiberMap (ContactPositive.curveDifferential f) marking.map v)
  exact hn.symm.trans ((congrArg
    (fiberComposition f.curve.map marking.map x.map hx X.contact.sequence.line.sheaf)
    hq).trans (map_zero _))

/-- Contact membership for the normalized source velocity in its original
fiber. Nonvanishing of the image is a separate geometric question; the
statement does not silently assume that an arbitrary free line is unramified. -/
theorem sourceVelocity_mem_contactPlane {n : ℕ} {X : ContactFanoManifold n}
    (f : FreeLine X) (x : ComplexPoint X.variety)
    (hx : marking.map ≫ f.curve.map = x.map) :
    pointVector X.variety x
      (Charts.AffineTangentLift.push f.curve.map f.curve.overC hx
        (PolynomialSourceLift.atMarking marking)) ∈ contactPlane X x := by
  rw [← nodeDifferential_sourceVector_eq_pointVector]
  exact nodeDifferential_mem_contactPlane f x hx (sourceVector marking)

end LeBrunSalamon.Construction.Lines.SourceTangent

end

/-!
## The canonical tangent-fiber comparison is an equivalence

Every point derivation on the actual target chart is realized by its actual
dual-number spectrum map, composed with the original chart inclusion. Its
variation is a vector in the original tangent-sheaf fiber. The normalized
action on each actual chart function proves surjectivity of the canonical
evaluation map. Together with localization faithfulness this yields the
full linear equivalence, without choosing an arbitrary equal-rank model.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirty
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction

namespace LeBrunSalamon.Construction.Lines.IntrinsicTangent

open FamilyVariation LocalVelocityComparison

variable {d : ℕ} {X : SmoothProperComplexVariety d} {x : ComplexPoint X}

/-- The algebraic first-order point in the actual chart. -/
def chartLiftMap (C : GlobalVelocity.TargetChart X x)
    (D : Infinitesimal.Tangent C.Ring C.evaluation) :
    Infinitesimal.DualScheme ⟶ X.scheme :=
  DirectionCones.affineMap (Infinitesimal.tangentToDual C.evaluation D) ≫ C.inclusion

theorem chartLiftMap_overC (C : GlobalVelocity.TargetChart X x)
    (D : Infinitesimal.Tangent C.Ring C.evaluation) :
    chartLiftMap C D ≫ X.structureMap = Infinitesimal.dualToC := by
  rw [chartLiftMap, Category.assoc, C.overC, DirectionCones.affineMap_overC]
  rfl

/-- The affine algebra point is the point already specified by the
chart, so the reduction is the original point of the original variety. -/
theorem chartLiftMap_reduces (C : GlobalVelocity.TargetChart X x)
    (D : Infinitesimal.Tangent C.Ring C.evaluation) :
    Infinitesimal.origin ≫ chartLiftMap C D = x.map := by
  have hr : Infinitesimal.origin ≫
      DirectionCones.affineMap (Infinitesimal.tangentToDual C.evaluation D) =
      DirectionCones.affineMap C.evaluation := by
    change Spec.map (CommRingCat.ofHom Infinitesimal.residue.toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (Infinitesimal.tangentToDual C.evaluation D).toRingHom) = _
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    ext a
    exact congrArg (fun q : C.Ring →ₐ[ℂ] ℂ => q a)
      (Infinitesimal.tangentToDual_residue C.evaluation D)
  rw [chartLiftMap, ← Category.assoc, hr]
  change DirectionCones.affineMap (GlobalVelocity.specPoint C.point C.point_overC) ≫
    C.inclusion = x.map
  rw [GlobalVelocity.affineMap_specPoint C.point C.point_overC, C.atPoint]

/-- Every chart derivation gives a genuine over-C infinitesimal lift of
the original variety's original point. -/
def chartLift (C : GlobalVelocity.TargetChart X x)
    (D : Infinitesimal.Tangent C.Ring C.evaluation) :
    Infinitesimal.PointLift X.scheme X.structureMap ⟨x.map, x.overC⟩ where
  map := chartLiftMap C D
  overC := chartLiftMap_overC C D
  reduces := chartLiftMap_reduces C D

theorem chartLift_support (C : GlobalVelocity.TargetChart X x)
    (D : Infinitesimal.Tangent C.Ring C.evaluation) :
    ⊤ ≤ (chartLift C D).map ⁻¹ᵁ chartOpen C := by
  intro z _
  exact chartOpen_source C trivial

/-- On every original chart function the entire dual-number pullback is
the original tangentToDual map, not only an unspecified first coefficient. -/
theorem chartLift_function (C : GlobalVelocity.TargetChart X x)
    (D : Infinitesimal.Tangent C.Ring C.evaluation) (a : C.Ring) :
    DualMixedBridge.dualGlobalEquiv
      ((chartLift C D).map.appLE (chartOpen C) ⊤ (chartLift_support C D)
        (chartFunctions C a)) = Infinitesimal.tangentToDual C.evaluation D a := by
  have hc : C.inclusion.appLE (chartOpen C) ⊤ (chartOpen_source C) ≫
      (DirectionCones.affineMap (Infinitesimal.tangentToDual C.evaluation D)).appTop =
      (chartLift C D).map.appLE (chartOpen C) ⊤ (chartLift_support C D) := by
    change C.inclusion.appLE (chartOpen C) ⊤ (chartOpen_source C) ≫
      (DirectionCones.affineMap (Infinitesimal.tangentToDual C.evaluation D)).app ⊤ = _
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
    rfl
  rw [← hc]
  change DualMixedBridge.dualGlobalEquiv
    ((DirectionCones.affineMap (Infinitesimal.tangentToDual C.evaluation D)).appTop
      (C.inclusion.appLE (chartOpen C) ⊤ (chartOpen_source C) (chartFunctionsRing C a))) = _
  rw [chartFunctions_pullback]
  have hn := congrArg (fun k : CommRingCat.of C.Ring ⟶
      (Spec (CommRingCat.of Infinitesimal.Dual)).presheaf.obj (op ⊤) => k a)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom
      (Infinitesimal.tangentToDual C.evaluation D).toRingHom))
  simp only [CommRingCat.comp_apply] at hn
  change (Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).inv
      (Infinitesimal.tangentToDual C.evaluation D a) =
    (DirectionCones.affineMap (Infinitesimal.tangentToDual C.evaluation D)).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of C.Ring)).inv a) at hn
  change (Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).hom
    ((DirectionCones.affineMap (Infinitesimal.tangentToDual C.evaluation D)).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of C.Ring)).inv a)) = _
  rw [← hn]
  exact Iso.inv_hom_id_apply _ _

/-- The actual chart lift differentiates the actual chart function by
exactly the prescribed original point derivation. -/
theorem chartLift_derivative (C : GlobalVelocity.TargetChart X x)
    (D : Infinitesimal.Tangent C.Ring C.evaluation) (a : C.Ring) :
    derivativeAlong (chartLift C D).map (chartLift C D).overC
        (chartOpen C) (chartLift_support C D) (chartFunctions C a) = D.val a := by
  rw [derivativeAlong_apply, chartLift_function]
  exact Infinitesimal.linearCoefficient_normalForm _ _

/-- The vector associated with the actual lift lies in the ORIGINAL
tangent-sheaf fiber by the normalized variation construction. -/
def chartLiftVector (C : GlobalVelocity.TargetChart X x)
    (D : Infinitesimal.Tangent C.Ring C.evaluation) : TangentFiber X x :=
  SourceTangent.pointVector X x (chartLift C D)

theorem chartLiftVector_coordinate (C : GlobalVelocity.TargetChart X x)
    (D : Infinitesimal.Tangent C.Ring C.evaluation) (a : C.Ring) :
    (chartEvaluation C (chartLiftVector C D)).val a = D.val a := by
  rw [chartEvaluation_apply]
  change PositiveFrame.localScalarPairing x.map
    (dualEvaluation (cotangentSheaf X.structureMap)) (chartOpen C) (chartOpen_point C)
    ((cotangentPresentation X.structureMap).differential.apply (chartOpen C)
      (chartFunctions C a)) (SourceTangent.pointVector X x (chartLift C D)) = _
  rw [SourceTangent.pointVector_local_pairing X x (chartLift C D)
    (chartOpen C) (chartOpen_point C) (chartLift_support C D), chartLift_derivative]

/-- Evaluation of the original vector recovers the originally prescribed
derivation on every chart function. -/
theorem chartEvaluation_chartLiftVector (C : GlobalVelocity.TargetChart X x)
    (D : Infinitesimal.Tangent C.Ring C.evaluation) :
    chartEvaluation C (chartLiftVector C D) = D := by
  apply Subtype.ext
  ext a
  exact chartLiftVector_coordinate C D a

theorem chartEvaluation_surjective (C : GlobalVelocity.TargetChart X x) :
    Function.Surjective (chartEvaluation C) := by
  intro D
  exact ⟨chartLiftVector C D, chartEvaluation_chartLiftVector C D⟩

theorem chartEvaluation_bijective (C : GlobalVelocity.TargetChart X x) :
    Function.Bijective (chartEvaluation C) :=
  ⟨chartEvaluation_injective C, chartEvaluation_surjective C⟩

/-- The canonical comparison is a full complex-linear equivalence. Its
forward map is the proved original differential pairing and its inverse is
the proved actual infinitesimal lift construction. -/
def chartEquivalence (C : GlobalVelocity.TargetChart X x) :
    TangentFiber X x ≃ₗ[ℂ] Infinitesimal.Tangent C.Ring C.evaluation :=
  LinearEquiv.ofBijective (chartEvaluation C) (chartEvaluation_bijective C)

theorem chartEquivalence_apply (C : GlobalVelocity.TargetChart X x)
    (v : TangentFiber X x) : chartEquivalence C v = chartEvaluation C v := rfl

theorem chartEquivalence_symm_apply (C : GlobalVelocity.TargetChart X x)
    (D : Infinitesimal.Tangent C.Ring C.evaluation) :
    (chartEquivalence C).symm D = chartLiftVector C D := by
  apply (chartEquivalence C).injective
  rw [LinearEquiv.apply_symm_apply, chartEquivalence_apply,
    chartEvaluation_chartLiftVector]

/-- Starting with an original tangent vector and taking its actual chart
lift reconstructs that same original vector. -/
theorem chartLiftVector_chartEvaluation (C : GlobalVelocity.TargetChart X x)
    (v : TangentFiber X x) : chartLiftVector C (chartEvaluation C v) = v := by
  apply chartEvaluation_injective C
  rw [chartEvaluation_chartLiftVector]

/-- Every original tangent vector is represented by an actual
infinitesimal point, with all local-function normalizations proved. -/
theorem pointVector_surjective (C : GlobalVelocity.TargetChart X x) :
    Function.Surjective (SourceTangent.pointVector X x) := by
  intro v
  exact ⟨chartLift C (chartEvaluation C v), chartLiftVector_chartEvaluation C v⟩

/-- Linearity of the inverse lift vector follows from the canonical
faithfulness, without assuming the intermediate family choice is linear. -/
theorem chartLiftVector_add (C : GlobalVelocity.TargetChart X x)
    (D E : Infinitesimal.Tangent C.Ring C.evaluation) :
    chartLiftVector C (D+E) = chartLiftVector C D + chartLiftVector C E := by
  apply chartEvaluation_injective C
  rw [map_add, chartEvaluation_chartLiftVector, chartEvaluation_chartLiftVector,
    chartEvaluation_chartLiftVector]

theorem chartLiftVector_smul (C : GlobalVelocity.TargetChart X x)
    (c : ℂ) (D : Infinitesimal.Tangent C.Ring C.evaluation) :
    chartLiftVector C (c • D) = c • chartLiftVector C D := by
  apply chartEvaluation_injective C
  rw [map_smul, chartEvaluation_chartLiftVector, chartEvaluation_chartLiftVector]

/-- Transition between two actual tangent charts is defined through the
original tangent fiber, whose evaluations on local functions fixed both
comparisons. It is therefore independent of a choice of vector-space basis. -/
def chartTransition (C D : GlobalVelocity.TargetChart X x) :
    Infinitesimal.Tangent C.Ring C.evaluation ≃ₗ[ℂ]
      Infinitesimal.Tangent D.Ring D.evaluation :=
  (chartEquivalence C).symm.trans (chartEquivalence D)

theorem chartTransition_evaluation (C D : GlobalVelocity.TargetChart X x)
    (v : TangentFiber X x) :
    chartTransition C D (chartEvaluation C v) = chartEvaluation D v := by
  change chartEquivalence D ((chartEquivalence C).symm (chartEquivalence C v)) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

theorem chartTransition_self (C : GlobalVelocity.TargetChart X x) :
    chartTransition C C = LinearEquiv.refl ℂ (Infinitesimal.Tangent C.Ring C.evaluation) := by
  apply LinearEquiv.ext
  intro a
  exact (chartEquivalence C).apply_symm_apply a

theorem chartTransition_cocycle (C D E : GlobalVelocity.TargetChart X x) :
    (chartTransition C D).trans (chartTransition D E) = chartTransition C E := by
  apply LinearEquiv.ext
  intro a
  change chartEquivalence E ((chartEquivalence D).symm
    (chartEquivalence D ((chartEquivalence C).symm a))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

end LeBrunSalamon.Construction.Lines.IntrinsicTangent

end

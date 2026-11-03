import RecompileBasePart04

/-! The existing affine derivation correspondence, placed before projective-line
geometry, and proved intrinsic tangent-action translations. No additional
admitted statement is introduced by this reordering. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

section AffineDerivationInputSection

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive

namespace LeBrunSalamon.Skeleton

/-- Constants in O_X(U), using the actual structure morphism. -/
def complexConstant {X : Scheme} (s : X ⟶ ComplexBase) (U : X.Opens) (c : ℂ) :
    RingSections X U :=
  X.presheaf.map (homOfLE le_top).op
    (s.appTop ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c))

end LeBrunSalamon.Skeleton

open LeBrunSalamon.Skeleton

namespace LeBrunSalamon.StandardInputs

/-- Stacks Project, Tag 01UO, Lemma 29.33.4: a derivation of the ring of
functions on an affine open extends to a sheaf derivation, with the prescribed
action on global sections. Here the base is `Spec ℂ`; annihilating the actual
complex constants is precisely the relative condition. This statement concerns
only affine sheaf derivations, independently of tangent evaluation or contact
geometry. https://stacks.math.columbia.edu/tag/01UO -/
theorem _root_.LeBrunSalamon.PublishedInputs.Step3f.affine_localDerivation_exists
    {Y : Scheme}
    (s : Y ⟶ ComplexBase) (U : Y.Opens) (hU : IsAffineOpen U)
    (D : RingSections Y U → RingSections Y U)
    (h0 : D 0 = 0)
    (hadd : ∀ a b, D (a + b) = D a + D b)
    (hmul : ∀ a b, D (a * b) = a * D b + b * D a)
    (hc : ∀ c : ℂ, D (complexConstant s U c) = 0) :
    ∃ δ : LocalDerivationProof.LocalDerivation s (structureModule Y) U,
      ∀ a, δ.apply (Over.mk (𝟙 U)) a = D a := by
  sorry

/-- Project-facing alias of Stacks Project Tag 01UO. -/
theorem affine_localDerivation_exists {Y : Scheme}
    (s : Y ⟶ ComplexBase) (U : Y.Opens) (hU : IsAffineOpen U)
    (D : RingSections Y U → RingSections Y U)
    (h0 : D 0 = 0)
    (hadd : ∀ a b, D (a + b) = D a + D b)
    (hmul : ∀ a b, D (a * b) = a * D b + b * D a)
    (hc : ∀ c : ℂ, D (complexConstant s U c) = 0) :
    ∃ δ : LocalDerivationProof.LocalDerivation s (structureModule Y) U,
      ∀ a, δ.apply (Over.mk (𝟙 U)) a = D a := by
  exact LeBrunSalamon.PublishedInputs.Step3f.affine_localDerivation_exists
    s U hU D h0 hadd hmul hc

/-- The injective half of Stacks Project, Tag 01UO, Lemma 29.33.4:
two relative sheaf derivations on an affine open agree when their actions on
its global functions agree. The conclusion is equality of the derivations
on every subopen, not a pointwise or contact-geometric assertion.
https://stacks.math.columbia.edu/tag/01UO -/
theorem _root_.LeBrunSalamon.PublishedInputs.Step3f.affine_localDerivation_ext
    {Y : Scheme}
    (s : Y ⟶ ComplexBase) (U : Y.Opens) (hU : IsAffineOpen U)
    (δ ε : LocalDerivationProof.LocalDerivation s (structureModule Y) U)
    (h : ∀ a, δ.apply (Over.mk (𝟙 U)) a = ε.apply (Over.mk (𝟙 U)) a) :
    δ = ε := by
  sorry

/-- Project-facing alias of the injective half of Stacks Project Tag 01UO. -/
theorem affine_localDerivation_ext {Y : Scheme}
    (s : Y ⟶ ComplexBase) (U : Y.Opens) (hU : IsAffineOpen U)
    (δ ε : LocalDerivationProof.LocalDerivation s (structureModule Y) U)
    (h : ∀ a, δ.apply (Over.mk (𝟙 U)) a = ε.apply (Over.mk (𝟙 U)) a) :
    δ = ε := by
  exact LeBrunSalamon.PublishedInputs.Step3f.affine_localDerivation_ext
    s U hU δ ε h

end LeBrunSalamon.StandardInputs

end AffineDerivationInputSection

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.Skeleton

namespace LeBrunSalamon.TangentAffine

/-- The relative differential kills the actual complex constants on every open. -/
theorem relativeDerivation_constant {Y : Scheme} (sY : Y ⟶ ComplexBase)
    {E : OModule Y} (D : RelativeSheafDerivation sY E)
    (U : Y.Opens) (c : ℂ) : D.apply U (complexConstant sY U c) = 0 := by
  have hk := D.killsBase ⊤ ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c)
  change D.apply ⊤ (sY.appTop ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c)) = 0 at hk
  have hn := D.naturality (homOfLE (show U ≤ ⊤ from le_top))
    (sY.appTop ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c))
  rw [hk, map_zero] at hn
  exact hn.symm

/-- A local intrinsic tangent section annihilates the actual complex constants. -/
theorem action_constant {Y : Scheme} (sY : Y ⟶ ComplexBase) (U : Y.Opens)
    (v : SectionsOn (tangentSheaf sY) U) (c : ℂ) :
    tangentActs sY U v (complexConstant sY U c) = 0 := by
  change (tangentCotangentPair sY).apply U v
    ((cotangentPresentation sY).differential.apply U (complexConstant sY U c)) = 0
  rw [relativeDerivation_constant]
  exact ((tangentCotangentPair sY).apply U v).map_zero

/-- An intrinsic tangent section acts on every subopen of its domain. -/
def localAction {Y : Scheme} (s : Y ⟶ ComplexBase) (U : Y.Opens)
    (v : SectionsOn (tangentSheaf s) U) :
    LocalDerivationProof.LocalDerivation s (structureModule Y) U where
  apply W a := tangentActs s W.left (TangentBracketProof.restrictField s U v W) a
  zero W := TangentActionProof.zero_function s W.left _
  add W a b := TangentActionProof.add_function s W.left _ a b
  leibniz W a b := TangentActionProof.leibniz s W.left _ a b
  naturality := by
    intro V W i a
    change Y.presheaf.map i.left.op
        (tangentActs s W.left (TangentBracketProof.restrictField s U v W) a) = _
    rw [TangentActionProof.naturality, TangentBracketProof.restrictField_naturality]
  killsBase := by
    intro V a W i
    exact TangentBracketProof.killsRestrictedBase s V W.left i _ a

theorem localAction_top {Y : Scheme} (s : Y ⟶ ComplexBase) (U : Y.Opens)
    (v : SectionsOn (tangentSheaf s) U) (a : RingSections Y U) :
    (localAction s U v).apply (Over.mk (𝟙 U)) a = tangentActs s U v a := by
  change tangentActs s U ((tangentSheaf s).presheaf.map (𝟙 U).op v) a = _
  simp

/-- On an affine open, testing all of its regular functions already tests
the entire local derivation, so it determines the intrinsic vector. -/
theorem affine_tangent_action_faithful {Y : Scheme} (s : Y ⟶ ComplexBase)
    (U : Y.Opens) (hU : IsAffineOpen U)
    (v w : SectionsOn (tangentSheaf s) U)
    (h : ∀ a, tangentActs s U v a = tangentActs s U w a) : v = w := by
  have he : localAction s U v = localAction s U w :=
    LeBrunSalamon.StandardInputs.affine_localDerivation_ext s U hU
      (localAction s U v) (localAction s U w)
      (fun a => (localAction_top s U v a).trans ((h a).trans (localAction_top s U w a).symm))
  apply tangentActs_faithful s U
  intro V i a
  exact congrArg (fun δ : LocalDerivationProof.LocalDerivation s (structureModule Y) U =>
    δ.apply (Over.mk i) a) he

/-- The affine sheaf-derivation correspondence and the already constructed
cotangent universal property give an intrinsic tangent section with exactly
the specified action on the affine coordinate ring. -/
theorem affine_tangent_action_exists {Y : Scheme} (s : Y ⟶ ComplexBase)
    (U : Y.Opens) (hU : IsAffineOpen U)
    (D : RingSections Y U → RingSections Y U)
    (h0 : D 0 = 0)
    (hadd : ∀ a b, D (a + b) = D a + D b)
    (hmul : ∀ a b, D (a * b) = a * D b + b * D a)
    (hc : ∀ c : ℂ, D (complexConstant s U c) = 0) :
    ∃ v : SectionsOn (tangentSheaf s) U, ∀ a, tangentActs s U v a = D a := by
  obtain ⟨δ, hδ⟩ := LeBrunSalamon.StandardInputs.affine_localDerivation_exists
    s U hU D h0 hadd hmul hc
  obtain ⟨φ, hφ⟩ := LocalDerivationProof.realize (cotangentPresentation s)
    (structureModule Y) U δ
  obtain ⟨v, hv⟩ := TangentBracketProof.localFunctional_surjective s U φ
  refine ⟨v, ?_⟩
  intro a
  have hlocal :
      (TangentBracketProof.localFunctional s U v).val.app (Opposite.op (Over.mk (𝟙 U)))
          ((cotangentPresentation s).differential.apply U a) =
        tangentActs s U ((tangentSheaf s).presheaf.map (𝟙 U).op v) a :=
    TangentBracketProof.localFunctional_apply s U v (Over.mk (𝟙 U)) a
  have hid : (tangentSheaf s).presheaf.map (𝟙 U).op v = v := by simp
  rw [hid, hv] at hlocal
  exact hlocal.symm.trans ((hφ (Over.mk (𝟙 U)) a).trans (hδ a))


end LeBrunSalamon.TangentAffine

import LSAffineDerivations

/-!
# Normalized affine maps out of the actual relative cotangent sheaf

The generic affine derivation correspondence is converted to the project's
fixed cotangent presentation, with its specified universal differential.
There is no admission in this off-graph draft; native checking is pending.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwentyFive

namespace LeBrunSalamon.AffineCotangentHom

def fromLocalTop {Y S : Scheme} {s : Y ⟶ S} {E : OModule Y}
    (D : LocalDerivationProof.LocalDerivation s E ⊤) : RelativeSheafDerivation s E where
  apply U a := D.apply (Over.mk (homOfLE le_top)) a
  zero U := D.zero (Over.mk (homOfLE (show U ≤ ⊤ from le_top)))
  add U a b := D.add (Over.mk (homOfLE (show U ≤ ⊤ from le_top))) a b
  leibniz U a b := D.leibniz (Over.mk (homOfLE (show U ≤ ⊤ from le_top))) a b
  naturality := by
    intro U V i a
    let j : Over.mk (homOfLE (show U ≤ ⊤ from le_top)) ⟶
        Over.mk (homOfLE (show V ≤ ⊤ from le_top)) := Over.homMk i
    exact D.naturality j a
  killsBase W a := by
    have h := D.killsBase W a (Over.mk (homOfLE (show s ⁻¹ᵁ W ≤ ⊤ from le_top)))
      (𝟙 (s ⁻¹ᵁ W))
    have hid : Y.presheaf.map (𝟙 (s ⁻¹ᵁ W)).op (s.app W a) = s.app W a := by simp
    exact (congrArg
      (D.apply (Over.mk (homOfLE (show s ⁻¹ᵁ W ≤ ⊤ from le_top)))) hid).symm.trans h

def localOfGlobalTop {Y S : Scheme} {s : Y ⟶ S} {E : OModule Y}
    (D : RelativeSheafDerivation s E) : LocalDerivationProof.LocalDerivation s E ⊤ where
  apply W a := D.apply W.left a
  zero W := D.zero _
  add W a b := D.add _ a b
  leibniz W a b := D.leibniz _ a b
  naturality i a := D.naturality i.left a
  killsBase V a W i := by
    have h := D.naturality i (s.app V a)
    rw [D.killsBase, map_zero] at h
    exact h.symm

private theorem derivation_ext {Y S : Scheme} {s : Y ⟶ S}
    {E : OModule Y} {D₁ D₂ : RelativeSheafDerivation s E}
    (h : ∀ U a, D₁.apply U a = D₂.apply U a) : D₁ = D₂ := by
  cases D₁ with
  | mk d₁ z₁ a₁ l₁ n₁ b₁ =>
    cases D₂ with
    | mk d₂ z₂ a₂ l₂ n₂ b₂ =>
      have hd : d₁ = d₂ := funext (fun U => funext (fun a => h U a))
      subst d₂
      rfl

theorem exists_normalized {Y S : Scheme} (s : Y ⟶ S) [IsAffine S]
    (hY : IsAffineOpen (⊤ : Y.Opens)) (E : OModule Y)
    (D : RingSections Y ⊤ → SectionsOn E ⊤)
    (h0 : D 0 = 0)
    (hadd : ∀ a b, D (a + b) = D a + D b)
    (hmul : ∀ a b, D (a * b) = a • D b + b • D a)
    (hbase : ∀ a : RingSections S ⊤, D (s.appTop a) = 0) :
    ∃ φ : cotangentSheaf s ⟶ E, ∀ a : RingSections Y ⊤,
      φ.app ⊤ ((cotangentPresentation s).differential.apply ⊤ a) = D a := by
  have hmap : s.appLE ⊤ ⊤ (by simp) = s.appTop := by simp [Scheme.Hom.appLE]
  obtain ⟨δ, hδ⟩ := PublishedInputs.AffineDerivations.exists_relative
    s ⊤ hY E D h0 hadd hmul (by intro a; simpa only [hmap] using hbase a)
  refine ⟨differentialLift (fromLocalTop δ), ?_⟩
  intro a
  have h := congrArg (fun d : RelativeSheafDerivation s E => d.apply ⊤ a)
    (differentialLift_spec (fromLocalTop δ))
  refine h.trans ?_
  change δ.apply (Over.mk (homOfLE (show (⊤ : Y.Opens) ≤ ⊤ from le_top))) a = D a
  have hi : (homOfLE (show (⊤ : Y.Opens) ≤ ⊤ from le_top)) = 𝟙 ⊤ :=
    Subsingleton.elim _ _
  rw [hi]
  exact hδ a

/-- Testing all global differentials on the affine source is enough;
the conclusion concerns the actual sheaf morphisms on every open. -/
theorem hom_ext_of_global_differentials {Y S : Scheme} (s : Y ⟶ S) [IsAffine S]
    (hY : IsAffineOpen (⊤ : Y.Opens)) {E : OModule Y}
    (f g : cotangentSheaf s ⟶ E)
    (h : ∀ a : RingSections Y ⊤,
      f.app ⊤ ((cotangentPresentation s).differential.apply ⊤ a) =
        g.app ⊤ ((cotangentPresentation s).differential.apply ⊤ a)) : f = g := by
  have hd := PublishedInputs.AffineDerivations.ext_relative s ⊤ hY E
    (localOfGlobalTop ((cotangentPresentation s).differential.postcompose f))
    (localOfGlobalTop ((cotangentPresentation s).differential.postcompose g)) h
  apply ((cotangentPresentation s).universal E).injective
  apply derivation_ext
  intro U a
  exact congrArg
    (fun d : LocalDerivationProof.LocalDerivation s E ⊤ =>
      d.apply (Over.mk (homOfLE (show U ≤ ⊤ from le_top))) a) hd

end LeBrunSalamon.AffineCotangentHom
end

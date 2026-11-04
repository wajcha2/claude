import LSRelativeCartier
import RecompileExtensionsPart04Geometry
import LSStandardTautological

/-! Exact classical effective-Cartier correspondences.  The ideal is
the categorical kernel, O(D) is its actual internal-Hom dual, and the
canonical section is the actual inclusion viewed as a Hom section.
All later selected-family and projective-coordinate transports are
proved separately. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.Construction

namespace LeBrunSalamon.PublishedInputs.EffectiveCartier

/-- Stacks Definition31.15.1 and Lemmas31.15.9(2),31.15.10(1).
The dual-ideal section corresponding to the actual inclusion is regular
and its scheme-theoretic zero locus is the original closed subscheme.
The right side is only existence; uniqueness follows from the proved
monomorphism of a closed immersion.
https://stacks.math.columbia.edu/tag/0C4S
https://stacks.math.columbia.edu/tag/01X0 -/
theorem canonical_regular_and_zero_locus
    {X Y : Scheme.{0}} (i : X ⟶ Y) [IsClosedImmersion i]
    (h : IsLocallyFreeOfRank (LeBrunSalamon.EffectiveCartier.ideal i) 1) :
    Mono (LeBrunSalamon.EffectiveCartier.canonicalSection i h) ∧
      ∀ {T : Scheme.{0}} (f : T ⟶ Y),
        pullSection f (LeBrunSalamon.EffectiveCartier.canonicalSection i h) = 0 ↔
          ∃ g : T ⟶ X, g ≫ i = f := by
  sorry

/-- Stacks0C4U, Lemma31.15.5: pullback of O(D), preserving the
canonical section.  Both original and pulled-back ideals are explicitly
invertible, so the hypothesis that the Cartier pullback is defined is
present.  The square specifies the actual pullback closed subscheme.
https://stacks.math.columbia.edu/tag/0C4U -/
theorem baseChange_line
    {X Y X' Y' : Scheme.{0}} (i : X ⟶ Y) [IsClosedImmersion i]
    (a : X' ⟶ X) (i' : X' ⟶ Y') (b : Y' ⟶ Y) (hb : IsPullback a i' i b)
    (h : IsLocallyFreeOfRank (LeBrunSalamon.EffectiveCartier.ideal i) 1)
    (h' : IsLocallyFreeOfRank (LeBrunSalamon.EffectiveCartier.ideal i') 1) :
    ∃ e : pullbackModule b (LeBrunSalamon.EffectiveCartier.line i h).sheaf ≅
        (LeBrunSalamon.EffectiveCartier.line i' h').sheaf,
      pullSection b (LeBrunSalamon.EffectiveCartier.canonicalSection i h) ≫ e.hom =
        LeBrunSalamon.EffectiveCartier.canonicalSection i' h' := by
  sorry

/-- Stacks01X0, Lemma31.15.10(2), together with the zero-scheme
description of31.15.9.  The section-graph fibre product below is the
scheme-theoretic zero scheme: its actual universal property is proved
in SectionEquality, so no arbitrary point-set zero locus is substituted.
Regular means exactly that O_Y -> L is a monomorphism, as in
Definition31.15.6.  No chosen curve or family occurs here.
https://stacks.math.columbia.edu/tag/01X0 -/
theorem regular_zero_locus
    {Y : Scheme.{0}} (L : LineBundle Y) (T : Descent.TotalLine L)
    (s : AlgebraicSection L.sheaf) [Mono s] :
    ∃ h : IsLocallyFreeOfRank (LeBrunSalamon.EffectiveCartier.ideal
          (Smoothing.StandardSourceProof.SectionEquality.inclusion T s 0)) 1,
      ∃ e : (LeBrunSalamon.EffectiveCartier.line
          (Smoothing.StandardSourceProof.SectionEquality.inclusion T s 0) h).sheaf ≅ L.sheaf,
        LeBrunSalamon.EffectiveCartier.canonicalSection
          (Smoothing.StandardSourceProof.SectionEquality.inclusion T s 0) h ≫ e.hom = s := by
  sorry

end LeBrunSalamon.PublishedInputs.EffectiveCartier

namespace LeBrunSalamon.PublishedInputs.ProjectiveSpace

/-- Stacks33.35.1, first paragraph (089X): a nonzero section of
O(d), d>=1, on P^n over a field, n>=1, is regular.  This is the
degree-two instance, where the actual line is O(1) tensor O(1).
The tensor identification is the degree-one-generated case of
Lemma27.10.3 (01MM), using the canonical multiplication27.10.1.1.
https://stacks.math.columbia.edu/tag/089X -/
theorem nonzero_quadratic_section_regular
    (K : Type) [Field K] (N : ℕ) (hN : 1 ≤ N)
    (s : AlgebraicSection (tensorLine (StandardTautological.line K N)
      (StandardTautological.line K N)).sheaf) (hs : s ≠ 0) : Mono s := by
  sorry

end LeBrunSalamon.PublishedInputs.ProjectiveSpace

namespace LeBrunSalamon.EffectiveCartier

theorem canonical_zero {X Y : Scheme.{0}} (i : X ⟶ Y) [IsClosedImmersion i]
    (h : IsLocallyFreeOfRank (ideal i) 1) : pullSection i (canonicalSection i h) = 0 :=
  (PublishedInputs.EffectiveCartier.canonical_regular_and_zero_locus i h).2 i |>.mpr
    ⟨𝟙 X, Category.id_comp i⟩

theorem universal {X Y : Scheme.{0}} (i : X ⟶ Y) [IsClosedImmersion i]
    (h : IsLocallyFreeOfRank (ideal i) 1) {T : Scheme.{0}} (f : T ⟶ Y)
    (hf : pullSection f (canonicalSection i h) = 0) :
    ∃! g : T ⟶ X, g ≫ i = f := by
  obtain ⟨g, hg⟩ := (PublishedInputs.EffectiveCartier.canonical_regular_and_zero_locus i h).2 f |>.mp hf
  exact ⟨g, hg, fun k hk => (cancel_mono i).mp (hk.trans hg.symm)⟩

end LeBrunSalamon.EffectiveCartier
end

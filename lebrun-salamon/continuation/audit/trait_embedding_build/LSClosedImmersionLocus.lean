import Mathlib

/-!
The only published input is the universal closed-immersion locus of
Stacks, Lemma 76.49.3 (05XA), restricted to schemes and a proper source.
The local-base consequence is proved from the actual closed point and
the specified cartesian squares. No polarized embedding is assumed.
-/

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace LeBrunSalamon.PublishedInputs.ClosedImmersionLocus

/-- Stacks 76.49.3, tag 05XA. Properness supplies the stated local finite
type and universal closedness assumptions. The cartesian squares specify
the actual base-changed morphism, independently of chosen pullback objects.
Source: https://stacks.math.columbia.edu/tag/05XA . -/
theorem exists_open
    {S X Y : Scheme} (p : X ⟶ S) (q : Y ⟶ S) (f : X ⟶ Y)
    (hf : f ≫ q = p) [IsProper p] [IsSeparated q] :
    ∃ U : S.Opens,
      ∀ {T X' Y' : Scheme} (g : T ⟶ S)
        (p' : X' ⟶ T) (q' : Y' ⟶ T)
        (i : X' ⟶ X) (j : Y' ⟶ Y) (f' : X' ⟶ Y'),
        IsPullback i p' p g → IsPullback j q' q g →
        f' ≫ j = i ≫ f → f' ≫ q' = p' →
        (IsClosedImmersion f' ↔ Set.range g.base ⊆ U) := by
  sorry

end LeBrunSalamon.PublishedInputs.ClosedImmersionLocus

namespace LeBrunSalamon.ClosedImmersionLocus

/-- Over a local base, an open neighborhood of the closed point is the
whole base. Thus the actual closed-fibre closed immersion suffices. -/
theorem of_local_closed_fibre
    (R : Type) [CommRing R] [IsLocalRing R]
    {X Y : Scheme} (p : X ⟶ Spec (CommRingCat.of R))
    (q : Y ⟶ Spec (CommRingCat.of R)) (f : X ⟶ Y)
    (hf : f ≫ q = p) [IsProper p] [IsSeparated q]
    {T X' Y' : Scheme} (g : T ⟶ Spec (CommRingCat.of R))
    (t : T) (ht : g.base t = IsLocalRing.closedPoint R)
    (p' : X' ⟶ T) (q' : Y' ⟶ T)
    (i : X' ⟶ X) (j : Y' ⟶ Y) (f' : X' ⟶ Y')
    (hp : IsPullback i p' p g) (hq : IsPullback j q' q g)
    (hfj : f' ≫ j = i ≫ f) (hfq : f' ≫ q' = p')
    [IsClosedImmersion f'] : IsClosedImmersion f := by
  obtain ⟨U, hU⟩ := PublishedInputs.ClosedImmersionLocus.exists_open p q f hf
  have hmem : IsLocalRing.closedPoint R ∈ U :=
    ((hU g p' q' i j f' hp hq hfj hfq).mp inferInstance) ⟨t, ht⟩
  have htop : U = ⊤ := (IsLocalRing.closedPoint_mem_iff U).mp hmem
  apply (hU (𝟙 _) p q (𝟙 _) (𝟙 _) f
    (IsPullback.of_id_fst (f := p)) (IsPullback.of_id_fst (f := q))
    (by simp) hf).mpr
  rw [htop]
  exact Set.subset_univ _

end LeBrunSalamon.ClosedImmersionLocus

end

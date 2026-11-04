import LSNormalizedSegre

/-! Proved quotient-tuple translation of the normalized Segre image.
Every test scheme and every actual line is allowed.  Generation and the
determinant equation are sheaf statements, not geometric-point tests.
No new admission.  This candidate is off graph pending native checking. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.Skeleton LeBrunSalamon.Refinement
open LeBrunSalamon.Construction

namespace LeBrunSalamon.NormalizedSegreQuotients

def tensorComparison {T Y : Scheme} (f : T ⟶ Y) (E : OModule Y)
    {G : OModule T} (e : pullbackModule f E ≅ G) :
    pullbackModule f (tensorSheaf E E) ≅ tensorSheaf G G := by
  letI := tensorPullbackComparison_isIso f E E
  exact (asIso (tensorPullbackComparison f E E)).symm ≪≫ tensorIso e e

theorem tensorComparison_sections {T Y : Scheme} (f : T ⟶ Y) (E : OModule Y)
    {G : OModule T} (e : pullbackModule f E ≅ G)
    (a b : AlgebraicSection E) :
    pullSection f (tensorSection a b) ≫ (tensorComparison f E e).hom =
      tensorSection (pullSection f a ≫ e.hom) (pullSection f b ≫ e.hom) := by
  letI := tensorPullbackComparison_isIso f E E
  rw [← tensorPullbackComparison_onSections]
  change (tensorSection _ _ ≫ tensorPullbackComparison f E E) ≫
    ((asIso (tensorPullbackComparison f E E)).inv ≫ tensorMap e.hom e.hom) = _
  change (tensorSection _ _ ≫ (asIso (tensorPullbackComparison f E E)).hom) ≫
    ((asIso (tensorPullbackComparison f E E)).inv ≫ tensorMap e.hom e.hom) = _
  rw [Category.assoc, Iso.hom_inv_id_assoc, tensorSection_map]

variable (R : Type) [CommRing R]

/-- A determinant equation in the chosen target line is exactly the
scheme-theoretic determinant equation after pulling back the normalized
four projective coordinates. -/
theorem determinant_pullback {T : Scheme}
    (f : T ⟶ StandardTautological.space R 3) (L : LineBundle T)
    (b : Fin 4 → AlgebraicSection L.sheaf)
    (e : pullbackModule f (StandardTautological.line R 3).sheaf ≅ L.sheaf)
    (he : ∀ i, pullSection f (StandardTautological.coordinate R 3 i) ≫ e.hom = b i)
    (hb : tensorSection (b 0) (b 3) = tensorSection (b 1) (b 2)) :
    pullSection f (NormalizedSegre.determinantLeft R) =
      pullSection f (NormalizedSegre.determinantRight R) := by
  apply (cancel_mono (tensorComparison f (StandardTautological.line R 3).sheaf e).hom).mp
  change pullSection f (tensorSection _ _) ≫ _ = pullSection f (tensorSection _ _) ≫ _
  rw [tensorComparison_sections, tensorComparison_sections, he, he, he, he]
  exact hb

/-- Recover the original target line from the map to the Segre product.
The actual pullback-composition comparison is part of the isomorphism. -/
def recoveredLine {T : Scheme}
    (g : T ⟶ NormalizedSegre.Product R) (f : T ⟶ StandardTautological.space R 3)
    (hg : g ≫ NormalizedSegre.map R = f) {L : LineBundle T}
    (e : pullbackModule f (StandardTautological.line R 3).sheaf ≅ L.sheaf) :
    pullbackModule g (NormalizedSegre.productLine R).sheaf ≅ L.sheaf :=
  ((Scheme.Modules.pullback g).mapIso (NormalizedSegre.mapLine R)).symm ≪≫
    compositionPullback g (NormalizedSegre.map R) f hg
      (StandardTautological.line R 3).sheaf ≪≫ e

theorem recoveredLine_coordinates {T : Scheme}
    (g : T ⟶ NormalizedSegre.Product R) (f : T ⟶ StandardTautological.space R 3)
    (hg : g ≫ NormalizedSegre.map R = f) {L : LineBundle T}
    (b : Fin 4 → AlgebraicSection L.sheaf)
    (e : pullbackModule f (StandardTautological.line R 3).sheaf ≅ L.sheaf)
    (he : ∀ i, pullSection f (StandardTautological.coordinate R 3 i) ≫ e.hom = b i)
    (i : Fin 4) :
    pullSection g (NormalizedSegre.productCoordinate R i) ≫
      (recoveredLine R g f hg e).hom = b i := by
  have hc := congrArg (fun a => pullSection g a) (NormalizedSegre.map_coordinate R i)
  rw [ExternalExchangeCoherenceProof.pullSection_map] at hc
  rw [← hc]
  let v := (Scheme.Modules.pullback g).mapIso (NormalizedSegre.mapLine R)
  change (pullSection g (pullSection (NormalizedSegre.map R)
      (StandardTautological.coordinate R 3 i)) ≫ v.hom) ≫
    (v.inv ≫ (compositionPullback g (NormalizedSegre.map R) f hg
      (StandardTautological.line R 3).sheaf).hom ≫ e.hom) = b i
  rw [Category.assoc, Iso.hom_inv_id_assoc, ← Category.assoc,
    compositionPullback_sections]
  exact he i

/-- Conversely, a line/coordinate comparison on the product gives the
literal normalized quotient map to projective 3-space. -/
def projectiveLine {T : Scheme} (g : T ⟶ NormalizedSegre.Product R)
    {L : LineBundle T} (e : pullbackModule g (NormalizedSegre.productLine R).sheaf ≅ L.sheaf) :
    pullbackModule (g ≫ NormalizedSegre.map R) (StandardTautological.line R 3).sheaf ≅
      L.sheaf :=
  (compositionPullback g (NormalizedSegre.map R) (g ≫ NormalizedSegre.map R) rfl
    (StandardTautological.line R 3).sheaf).symm ≪≫
      (Scheme.Modules.pullback g).mapIso (NormalizedSegre.mapLine R) ≪≫ e

theorem projectiveLine_coordinates {T : Scheme} (g : T ⟶ NormalizedSegre.Product R)
    {L : LineBundle T} (b : Fin 4 → AlgebraicSection L.sheaf)
    (e : pullbackModule g (NormalizedSegre.productLine R).sheaf ≅ L.sheaf)
    (he : ∀ i, pullSection g (NormalizedSegre.productCoordinate R i) ≫ e.hom = b i)
    (i : Fin 4) :
    pullSection (g ≫ NormalizedSegre.map R) (StandardTautological.coordinate R 3 i) ≫
      (projectiveLine R g e).hom = b i := by
  rw [← compositionPullback_sections g (NormalizedSegre.map R)
    (g ≫ NormalizedSegre.map R) rfl]
  let c := compositionPullback g (NormalizedSegre.map R) (g ≫ NormalizedSegre.map R) rfl
    (StandardTautological.line R 3).sheaf
  change (pullSection g (pullSection (NormalizedSegre.map R)
      (StandardTautological.coordinate R 3 i)) ≫ c.hom) ≫
    (c.inv ≫ (Scheme.Modules.pullback g).map (NormalizedSegre.mapLine R).hom ≫ e.hom) = _
  rw [Category.assoc, Iso.hom_inv_id_assoc, ← Category.assoc,
    ← ExternalExchangeCoherenceProof.pullSection_map, NormalizedSegre.map_coordinate]
  exact he i

/-- The full quotient-tuple formulation follows from the normalized
scheme image.  The unique object is the actual map to P1×P1; its line
comparison is retained explicitly rather than silently forgotten. -/
theorem quotient_universal {T : Scheme} (s : T ⟶ Spec (CommRingCat.of R))
    (L : LineBundle T) (b : Fin 4 → AlgebraicSection L.sheaf)
    (hgen : TupleGenerates L b)
    (hdet : tensorSection (b 0) (b 3) = tensorSection (b 1) (b 2)) :
    ∃! g : {g : T ⟶ NormalizedSegre.Product R // g ≫ NormalizedSegre.base R = s},
      ∃ e : pullbackModule g.val (NormalizedSegre.productLine R).sheaf ≅ L.sheaf,
        ∀ i, pullSection g.val (NormalizedSegre.productCoordinate R i) ≫ e.hom = b i := by
  obtain ⟨f, ⟨e, he⟩, hunique⟩ :=
    (StandardTautological.chosen R 3).universal T s L.sheaf L.locallyFree b hgen
  have hzero := determinant_pullback R f.val L b e he hdet
  obtain ⟨g, hg, hg_unique⟩ := NormalizedSegre.factorization R f.val hzero
  have hover : g ≫ NormalizedSegre.base R = s :=
    (NormalizedSegre.factorization_over R f.val g hg).trans f.property
  refine ⟨⟨g, hover⟩, ⟨recoveredLine R g f.val hg e,
    recoveredLine_coordinates R g f.val hg b e he⟩, ?_⟩
  intro k hk
  obtain ⟨v, hv⟩ := hk
  have hkbase : (k.val ≫ NormalizedSegre.map R) ≫ StandardTautological.toSpec R 3 = s := by
    rw [Category.assoc, NormalizedSegre.map_over, k.property]
  have hp := hunique ⟨k.val ≫ NormalizedSegre.map R, hkbase⟩
    ⟨projectiveLine R k.val v, projectiveLine_coordinates R k.val b v hv⟩
  apply Subtype.ext
  exact hg_unique k.val (congrArg Subtype.val hp)

end LeBrunSalamon.NormalizedSegreQuotients
end

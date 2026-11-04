import LSPublishedCohomologyBaseChange
import LSLineStalkFlat

/-! Actual line-bundle section restriction and finite-tuple lifting.
The cohomology and Yoneda adapters are in the independently checked core;
this file supplies the proved local-frame flatness and the original
residue-field and power-series fibre maps. No admission is introduced. -/

noncomputable section
set_option autoImplicit false
set_option maxErrors 1
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirtyTwo

namespace LeBrunSalamon.CohomologyBaseChange

variable {R : Type} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
variable {X Y : Scheme} (sX : X ⟶ Spec (CommRingCat.of R)) [IsProper sX]
  (p : Y ⟶ X) (q : Y ⟶ Spec (CommRingCat.of (IsLocalRing.ResidueField R)))
  (hsq : IsPullback p q sX (Spec.map
    (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R)))))

include q hsq in
/-- The chosen-line application supplies relative flatness by the proved
local-frame/stalk argument. This is the exact original tuple lift needed
before the separate generation and closed-immersion arguments. -/
theorem line_restriction_surjective [Flat sX] (L : LineBundle X)
    (h1 : HasVanishingFirstCohomology (pullbackModule p L.sheaf)) :
    Function.Surjective (pullSection p : AlgebraicSection L.sheaf →
      AlgebraicSection (pullbackModule p L.sheaf)) :=
  CanonicalSectionBaseChange.pullSection_surjective sX p q hsq.w L.sheaf
    (bundle_residue_baseChange sX p q hsq L
      (LineStalkFlat.relativelyFlat sX L) h1).surjective

include q hsq in
/-- Lift the specified finite tuple, without changing its entries or the
actual restriction map from the original line bundle. -/
theorem lift_line_tuple [Flat sX] (L : LineBundle X)
    (h1 : HasVanishingFirstCohomology (pullbackModule p L.sheaf))
    (n : ℕ) (a : Fin n → AlgebraicSection (pullbackModule p L.sheaf)) :
    ∃ b : Fin n → AlgebraicSection L.sheaf, ∀ i, pullSection p (b i) = a i :=
  lift_bundle_tuple sX p q hsq L (LineStalkFlat.relativelyFlat sX L) h1 n a

/-- A specified field quotient, such as the constant-term quotient of a
power-series trait, is normalized by a proved spectrum isomorphism. The
original fibre object, `p`, its H1 predicate and its section restriction
are all retained exactly. -/
theorem line_restriction_surjective_of_field_quotient
    {K : Type} [Field K] (qK : Y ⟶ Spec (CommRingCat.of K))
    (f : R →+* K) [IsLocalHom f] (hf : Function.Surjective f)
    (hK : IsPullback p qK sX (Spec.map (CommRingCat.ofHom f)))
    [Flat sX] (L : LineBundle X)
    (h1 : HasVanishingFirstCohomology (pullbackModule p L.sheaf)) :
    Function.Surjective (pullSection p : AlgebraicSection L.sheaf →
      AlgebraicSection (pullbackModule p L.sheaf)) :=
  line_restriction_surjective sX p
    (qK ≫ (ResidueFieldPresentation.specIso f hf).hom)
    (ResidueFieldPresentation.pullback_residue sX p qK f hf hK) L h1

/-- The canonical fibre-product specialization retains the exact first
projection used by the separate projective tuple and embedding proofs. -/
theorem fibre_restriction_surjective_of_h1
    {K : Type} [Field K] (f : R →+* K) [IsLocalHom f]
    (hf : Function.Surjective f) [Flat sX] (L : LineBundle X)
    (h1 : HasVanishingFirstCohomology
      (pullbackModule (pullback.fst sX (Spec.map (CommRingCat.ofHom f))) L.sheaf)) :
    Function.Surjective
      (pullSection (pullback.fst sX (Spec.map (CommRingCat.ofHom f))) :
        AlgebraicSection L.sheaf → AlgebraicSection
          (pullbackModule (pullback.fst sX (Spec.map (CommRingCat.ofHom f))) L.sheaf)) :=
  line_restriction_surjective_of_field_quotient sX
    (pullback.fst sX (Spec.map (CommRingCat.ofHom f)))
    (pullback.snd sX (Spec.map (CommRingCat.ofHom f))) f hf
    (IsPullback.of_hasPullback sX (Spec.map (CommRingCat.ofHom f))) L h1

/-- The formal-power-series specialization uses the actual constant-term
quotient and the original first projection, with no replacement fibre. -/
theorem powerSeries_fibre_restriction_surjective
    {K : Type} [Field K] {C : Scheme}
    (pi : C ⟶ Spec (CommRingCat.of (PowerSeries K))) [IsProper pi] [Flat pi]
    (L : LineBundle C)
    (h1 : HasVanishingFirstCohomology
      (pullbackModule (pullback.fst pi (Spec.map
        (CommRingCat.ofHom (PowerSeries.constantCoeff (R := K))))) L.sheaf)) :
    Function.Surjective
      (pullSection (pullback.fst pi (Spec.map
        (CommRingCat.ofHom (PowerSeries.constantCoeff (R := K))))) :
        AlgebraicSection L.sheaf → AlgebraicSection
          (pullbackModule (pullback.fst pi (Spec.map
            (CommRingCat.ofHom (PowerSeries.constantCoeff (R := K))))) L.sheaf)) := by
  letI := ResidueFieldPresentation.constantCoeff_local K
  exact fibre_restriction_surjective_of_h1 pi
    (PowerSeries.constantCoeff (R := K)) PowerSeries.constantCoeff_surj L h1

end LeBrunSalamon.CohomologyBaseChange

end

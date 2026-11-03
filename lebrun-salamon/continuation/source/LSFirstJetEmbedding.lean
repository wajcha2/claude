import RecompileExtensionsPart02

/-!
# Actual first jets of a projective embedding

The lemmas here isolate the ordinary sheaf and linear-algebra parts of the
very-ampleness argument. Every statement uses the existing restriction to
the actual first infinitesimal neighbourhood; no new jet predicate is
postulated. This file contains no admitted proof.

The remaining geometric task is to prove that the coordinate tuple of a
closed immersion is projectively immersive in the chosen local frame.
The universal projective quotient is sufficient for this, by testing on
Spec(C[epsilon]/epsilon^2). The final geometric bridge is not asserted here.

Candidate continuation, 3 November 2026: kernel replay is pending.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseFour LeBrunSalamon.PhaseSeven
open LeBrunSalamon.PhaseSeventeen LeBrunSalamon.PhaseTwentyTwo
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.PhaseThirtyFive
open LeBrunSalamon.Core LeBrunSalamon.Skeleton
open LeBrunSalamon.Refinement LeBrunSalamon.Refinement.Jets

namespace LeBrunSalamon.ClassicalReduction.FirstJetProof

/-- Jet generation is invariant under an actual isomorphism of the target
module sheaf, including the canonical pulled-back source of the jet map. -/
theorem separatesJetsAt_iso {d : ℕ} {X : SmoothProperComplexVariety d}
    {E G : OModule X.scheme} (e : E ≅ G) (x : ComplexPoint X) (k : ℕ) :
    SeparatesJetsAt E x k ↔ SeparatesJetsAt G x k := by
  let F := Scheme.Modules.pullback (pointPowerInclusion x (k + 1))
  constructor
  · intro h j
    obtain ⟨s, hs⟩ := h (j ≫ F.map e.inv)
    refine ⟨s ≫ e.hom, ?_⟩
    change F.map s = j ≫ F.map e.inv at hs
    change F.map (s ≫ e.hom) = j
    rw [Functor.map_comp, hs, Category.assoc, ← Functor.map_comp,
      e.inv_hom_id, CategoryTheory.Functor.map_id, Category.comp_id]
  · intro h j
    obtain ⟨s, hs⟩ := h (j ≫ F.map e.hom)
    refine ⟨s ≫ e.inv, ?_⟩
    change F.map s = j ≫ F.map e.hom at hs
    change F.map (s ≫ e.inv) = j
    rw [Functor.map_comp, hs, Category.assoc, ← Functor.map_comp,
      e.hom_inv_id, CategoryTheory.Functor.map_id, Category.comp_id]

/-- The exact local algebra needed for first jets is spanning modulo the
square of the point ideal, not merely generating the line at the point. -/
theorem separatesJetsAt_iff_coefficients {d : ℕ}
    {X : SmoothProperComplexVariety d} {L : LineBundle X.scheme}
    {x : ComplexPoint X} (F : PointFrame X L x) :
    SeparatesJetsAt L.sheaf x 1 ↔
      ∀ a : F.ChartRing, ∃ s : AlgebraicSection L.sheaf,
        F.coefficient s - a ∈
          (RingHom.ker (x.map.app F.frame.openSet).hom) ^ 2 := by
  constructor
  · intro h a
    obtain ⟨s, hs⟩ := h (F.restrictLocal a)
    refine ⟨s, ?_⟩
    apply (IntrinsicJetAffineQuotientProof.pointPower_restriction_eq_iff
      x F.frame.openSet F.frame.isAffine 2 (F.coefficient s) a).mp
    apply (PointFrame.LocalFrameJetProof.restrictLocal_equal_iff_scalar
      F (F.coefficient s) a).mp
    exact (F.restrictLocal_global s).trans hs
  · intro h j
    obtain ⟨a, rfl⟩ := F.restrictLocal_surjective j
    obtain ⟨s, hs⟩ := h a
    refine ⟨s, ?_⟩
    rw [← F.restrictLocal_global s]
    apply (PointFrame.LocalFrameJetProof.restrictLocal_equal_iff_scalar
      F (F.coefficient s) a).mpr
    exact (IntrinsicJetAffineQuotientProof.pointPower_restriction_eq_iff
      x F.frame.openSet F.frame.isAffine 2 (F.coefficient s) a).mpr hs

/-- The existing local normalization transports surjectivity in both
directions; in particular it does not assume global jet generation. -/
theorem separatesJetsAt_iff_localJet {d : ℕ}
    {X : SmoothProperComplexVariety d} {L : LineBundle X.scheme}
    {x : ComplexPoint X} (F : PointFrame X L x) :
    SeparatesJetsAt L.sheaf x 1 ↔
      Function.Surjective (fun s : AlgebraicSection L.sheaf =>
        F.localJet (F.coefficient s)) := by
  constructor
  · intro h j
    obtain ⟨s, hs⟩ := h (F.jetCoordinates.symm j)
    refine ⟨s, ?_⟩
    change F.localJet (F.coefficient s) = j
    rw [← F.jetCoordinates_global, hs, F.jetCoordinates.apply_symm_apply]
  · intro h j
    obtain ⟨s, hs⟩ := h (F.jetCoordinates j)
    refine ⟨s, F.jetCoordinates.injective ?_⟩
    exact (F.jetCoordinates_global s).trans hs

/-- The value and derivative of any finite tuple of genuine global
sections. No kernel expansion or contact assumption is required. -/
def tupleJet {d m : ℕ} {X : SmoothProperComplexVariety d}
    {L : LineBundle X.scheme} {x : ComplexPoint X}
    (F : PointFrame X L x) (a : Fin m → AlgebraicSection L.sheaf) :
    SectionValuedFirstJet F.Tangent (Fin m → ℂ) where
  value i := F.evaluation (F.coefficient (a i))
  derivative := LinearMap.pi (fun i => F.differential (F.coefficient (a i)))

/-- A constant linear combination of coordinate sections is a genuine
global section of the original line bundle. -/
def tupleContraction {d m : ℕ} (X : SmoothProperComplexVariety d)
    {L : LineBundle X.scheme} (a : Fin m → AlgebraicSection L.sheaf)
    (ell : (Fin m → ℂ) →ₗ[ℂ] ℂ) : AlgebraicSection L.sheaf :=
  ∑ i, scaleSection X (ell (Pi.single i 1)) (a i)

/-- The finite-coordinate contraction commutes with the actual fat-point
restriction and its independently constructed local normalization. -/
theorem tupleContraction_firstJet {d m : ℕ} {X : SmoothProperComplexVariety d}
    {L : LineBundle X.scheme} {x : ComplexPoint X}
    (F : PointFrame X L x) (a : Fin m → AlgebraicSection L.sheaf)
    (ell : (Fin m → ℂ) →ₗ[ℂ] ℂ) :
    F.jetCoordinates (jetRestrictionAt x L.sheaf 1 (tupleContraction X a ell)) =
      (tupleJet F a).contractedJet ell := by
  classical
  let c : AlgebraicSection L.sheaf →+ F.ChartRing :=
    ScalarSections.coefficientAddHom F.frame
  have hc : F.coefficient (tupleContraction X a ell) =
      ∑ i, algebraMap ℂ F.ChartRing (ell (Pi.single i 1)) * F.coefficient (a i) := by
    change c (∑ i, scaleSection X (ell (Pi.single i 1)) (a i)) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact scaleSection_local X L F.frame (ell (Pi.single i 1)) (a i)
  have hscalar (D : F.Tangent) (z : ℂ) (b : F.ChartRing) :
      D.val (algebraMap ℂ F.ChartRing z * b) = z * D.val b := by
    change D.val (z • b) = z • D.val b
    exact D.val.map_smul z b
  rw [F.jetCoordinates_global, PointFrame.localJet, hc]
  apply Prod.ext
  · change F.evaluation
        (∑ i, algebraMap ℂ F.ChartRing (ell (Pi.single i 1)) * F.coefficient (a i)) =
      ell (fun i => F.evaluation (F.coefficient (a i)))
    rw [map_sum]
    simp only [map_mul, AlgHom.commutes]
    exact (functional_coordinate_sum m ell
      (fun i => F.evaluation (F.coefficient (a i)))).symm
  · apply LinearMap.ext
    intro D
    change D.val
        (∑ i, algebraMap ℂ F.ChartRing (ell (Pi.single i 1)) * F.coefficient (a i)) =
      ell (fun i => D.val (F.coefficient (a i)))
    rw [map_sum]
    simp only [hscalar]
    exact (functional_coordinate_sum m ell
      (fun i => D.val (F.coefficient (a i)))).symm

/-- Projective immersivity of the coordinate tuple gives surjectivity of
the original jet map. The supplied tuple need not be a basis of H⁰(L). -/
theorem separatesJetsAt_of_tuple_immersive {d m : ℕ}
    {X : SmoothProperComplexVariety d} {L : LineBundle X.scheme}
    {x : ComplexPoint X} (F : PointFrame X L x)
    (a : Fin m → AlgebraicSection L.sheaf)
    (hi : (tupleJet F a).IsProjectivelyImmersive) :
    SeparatesJetsAt L.sheaf x 1 := by
  intro j
  obtain ⟨ell, he⟩ := immersiveKernel_separatesFirstJets F.Tangent (Fin m → ℂ)
    (tupleJet F a) hi (F.jetCoordinates j)
  exact ⟨tupleContraction X a ell,
    F.jetCoordinates.injective ((tupleContraction_firstJet F a ell).trans he)⟩

/-- Pullback preserves a generating tuple, on every test scheme including
nonreduced infinitesimal schemes. This is the actual left-adjoint argument. -/
theorem tupleGenerates_pullback {Y T : Scheme} {N : ℕ}
    (L : LineBundle Y) (a : Fin (N + 1) → AlgebraicSection L.sheaf)
    (ha : TupleGenerates L a) (f : T ⟶ Y) :
    TupleGenerates (pullbackLine f L) (fun i => pullSection f (a i)) := by
  let F : SheafOfModules.{0} Y.ringCatSheaf ⥤
      SheafOfModules.{0} T.ringCatSheaf := Scheme.Modules.pullback f
  letI : F.IsLeftAdjoint :=
    (SheafOfModules.pullbackPushforwardAdjunction f.toRingCatSheafHom).isLeftAdjoint
  let q : SheafOfModules.free (R := Y.ringCatSheaf) (Fin (N + 1)) ⟶ L.sheaf :=
    Sigma.desc a
  letI : Epi q := ha
  letI : Epi (F.map q) := inferInstance
  let c := SheafOfModules.mapFreeIso F (Fin (N + 1)) (unitPullbackIso f).symm
  change Epi (Sigma.desc (fun i => pullSection f (a i)))
  have h : Sigma.desc (fun i => pullSection f (a i)) = c.hom ≫ F.map q := by
    apply Sigma.hom_ext
    intro i
    rw [Sigma.ι_comp_desc]
    change pullSection f (a i) = SheafOfModules.ιFree i ≫ c.hom ≫ F.map q
    erw [SheafOfModules.ιFree_mapFreeIso_hom_assoc, ← Functor.map_comp]
    simp only [q, SheafOfModules.ιFree, Sigma.ι_comp_desc,
      pullSection, restrictSection, F, Iso.symm_hom]
  rw [h]
  infer_instance

/-- The universal quotient determines morphisms on arbitrary test schemes.
In particular the statement applies to the dual-number test scheme. -/
theorem projectiveMaps_eq_of_coordinateIso {T : Scheme} {N : ℕ}
    (P : ProjectiveCoordinates N) (sT : T ⟶ ComplexBase)
    (f g : PointsOver T sT (ComplexProjectiveSpace N) (projectiveBaseMap N))
    (e : pullbackModule g.val P.hyperplane.sheaf ≅
      pullbackModule f.val P.hyperplane.sheaf)
    (he : ∀ i, pullSection g.val (P.coordinate i) ≫ e.hom =
      pullSection f.val (P.coordinate i)) : f = g := by
  obtain ⟨q, hq, huniq⟩ := P.universal T sT (pullbackLine f.val P.hyperplane)
    (fun i => pullSection f.val (P.coordinate i))
    (tupleGenerates_pullback P.hyperplane P.coordinate P.generates f.val)
  have hf : f = q := huniq f ⟨Iso.refl _, by intro i; simp⟩
  have hg : g = q := huniq g ⟨e, he⟩
  exact hf.trans hg.symm

end LeBrunSalamon.ClassicalReduction.FirstJetProof

end

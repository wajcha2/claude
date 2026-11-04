import LSRelativeGeneration
import LSStandardTautological

/-! Lift an actual generating tuple on the closed fibre and construct
the corresponding projective morphism with its specified line comparison.
No cohomology, embedding, or normal-form assertion is admitted here. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.Skeleton

namespace LeBrunSalamon.LiftedProjectiveTuple

theorem exists_of_surjective_restriction
    (R : Type) [CommRing R] [IsLocalRing R]
    {X T : Scheme.{0}} (pi : X ⟶ Spec (CommRingCat.of R)) [IsProper pi]
    (s : T ⟶ Spec (CommRingCat.of R)) (t : T)
    (ht : s t = IsLocalRing.closedPoint R)
    {N : ℕ} (D : StandardTautological.Data R N) (L : LineBundle X)
    (hsections : Function.Surjective (fun a : AlgebraicSection L.sheaf =>
      pullSection (pullback.fst pi s) a))
    (b : Fin (N+1) → AlgebraicSection (pullbackModule (pullback.fst pi s) L.sheaf))
    (hb : TupleGenerates (pullbackLine (pullback.fst pi s) L) b) :
    ∃ a : Fin (N+1) → AlgebraicSection L.sheaf,
      (∀ i, pullSection (pullback.fst pi s) (a i) = b i) ∧
      TupleGenerates L a ∧
      ∃ f : {f : X ⟶ StandardTautological.space R N //
          f ≫ StandardTautological.toSpec R N = pi},
        ∃ e : pullbackModule f.val D.sheaf ≅ L.sheaf,
          ∀ i, pullSection f.val (D.coordinate i) ≫ e.hom = a i := by
  choose a ha using fun i => hsections (b i)
  have hfibre : TupleGenerates (pullbackLine (pullback.fst pi s) L)
      (fun i => pullSection (pullback.fst pi s) (a i)) := by
    simpa only [ha] using hb
  have hgen : TupleGenerates L a :=
    RelativeGeneration.tupleGenerates_of_closed_fibre R pi s t ht L a hfibre
  obtain ⟨f, hf, _⟩ := D.universal X pi L.sheaf L.locallyFree a hgen
  exact ⟨a, ha, hgen, f, hf⟩

end LeBrunSalamon.LiftedProjectiveTuple
end

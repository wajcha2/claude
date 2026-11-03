import LSTangentDeterminant

/-!
# Remaining generic Step 3e translations

Smooth cotangent rank: Stacks Project Tags 02G1 and 02G2, with the
universal relative differential of Section 29.33. Pinned Mathlib defines
smoothness of relative dimension by local standard-smooth charts. The
source theorem constructs the corresponding locally free differential
sheaf; uniqueness transports it to the project's chosen presentation.

Positive powers: Stacks Project Definition 28.27.1 (01PR) and Lemma
28.27.2 (01PT). The generic statement below uses actual module sheaves
and their recursive tensor powers. The project wrapper is transported by
the already proved `linePower_sheaf_eq_tensorPower` identity.

Short exact determinants: obtained without another admission from the
same generic Stacks 0E9Y exterior map used for determinant duality.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix

namespace LeBrunSalamon.PublishedInputs.Differentials

/-- The universal differential of a smooth morphism of relative dimension d
is finite locally free of rank d (Stacks 02G1, 02G2). The presentation is
provided as data; comparison with the project's chosen presentation is proved. -/
theorem smoothCotangentPresentation {X S : Scheme} (s : X ⟶ S) (d : ℕ)
    (hs : SmoothOfRelativeDimension d s) :
    ∃ P : CotangentPresentation s, IsLocallyFreeOfRank P.object d := by
  sorry

end LeBrunSalamon.PublishedInputs.Differentials

namespace LeBrunSalamon.CotangentRankProof

theorem rank_transport {X : Scheme} {E F : OModule X} {r : ℕ}
    (e : E ≅ F) (hE : IsLocallyFreeOfRank E r) :
    IsLocallyFreeOfRank F r := by
  obtain ⟨q, hq, hr⟩ := hE
  letI := hq
  apply SheafTensor.rank_of_free_cover F r q.X q.coversTop
  intro i
  exact SheafTensor.localBasisTrivialization q hr i ≪≫
    (SheafOfModules.overFunctor X.ringCatSheaf (q.X i)).mapIso e

theorem smooth_cotangent_rank {X S : Scheme} (s : X ⟶ S) (d : ℕ)
    (hs : SmoothOfRelativeDimension d s) :
    IsLocallyFreeOfRank (cotangentSheaf s) d := by
  obtain ⟨P, hP⟩ := PublishedInputs.Differentials.smoothCotangentPresentation s d hs
  obtain ⟨e, _⟩ := cotangentPresentation_unique P (cotangentPresentation s)
  exact rank_transport e hP

end LeBrunSalamon.CotangentRankProof

namespace LeBrunSalamon.SheafAmpleness

/-- Nonvanishing of a line section means it locally trivializes the sheaf. -/
def nonvanishing {X : Scheme} (E : OModule X) (s : AlgebraicSection E) : X.Opens :=
  sSup {U : X.Opens | IsIso (restrictSection U.ι s)}

/-- Stacks 28.27.1 expressed on the actual sheaf and tensor-power construction. -/
def IsAmple {X : Scheme} (E : OModule X) : Prop :=
  CompactSpace X ∧ ∀ x : X,
    ∃ (m : ℕ) (_ : 0 < m) (s : AlgebraicSection (SheafTensor.tensorPower E m)),
      x ∈ nonvanishing (SheafTensor.tensorPower E m) s ∧
      IsAffineOpen (nonvanishing (SheafTensor.tensorPower E m) s)

theorem line_iff {X : Scheme} (L : LineBundle X) :
    IsAmpleLine L ↔ IsAmple L.sheaf := by
  unfold IsAmpleLine IsAmple
  apply and_congr_right
  intro _
  apply forall_congr'
  intro x
  apply exists_congr
  intro m
  apply exists_congr
  intro _
  let Q (E : OModule X) : Prop :=
    ∃ s : AlgebraicSection E,
      x ∈ nonvanishing E s ∧ IsAffineOpen (nonvanishing E s)
  change Q (linePower L m).sheaf ↔ Q (SheafTensor.tensorPower L.sheaf m)
  exact iff_of_eq (congrArg Q (linePower_sheaf_eq_tensorPower L m))

end LeBrunSalamon.SheafAmpleness

namespace LeBrunSalamon.PublishedInputs.Ample

/-- Stacks Project Lemma 28.27.2 (Tag 01PT), for an arbitrary invertible
module sheaf and a positive tensor power, with the quasi-compact convention
of Definition 28.27.1 (Tag 01PR). -/
theorem positive_tensorPower {X : Scheme} (E : OModule X)
    (hE : IsLocallyFreeOfRank E 1) (m : ℕ) (hm : 0 < m) :
    SheafAmpleness.IsAmple (SheafTensor.tensorPower E m) ↔
      SheafAmpleness.IsAmple E := by
  sorry

end LeBrunSalamon.PublishedInputs.Ample

namespace LeBrunSalamon.AmplePowerProof

theorem ample_positivePower_iff {X : Scheme} (L : LineBundle X)
    (m : ℕ) (hm : 0 < m) :
    IsAmpleLine (linePower L m) ↔ IsAmpleLine L := by
  rw [SheafAmpleness.line_iff, SheafAmpleness.line_iff,
    linePower_sheaf_eq_tensorPower]
  exact PublishedInputs.Ample.positive_tensorPower L.sheaf L.locallyFree m hm

end LeBrunSalamon.AmplePowerProof

namespace LeBrunSalamon.TangentDeterminantProof

/-- Cancel the dual determinant in the generic fundamental exterior map. -/
theorem determinant_shortExact {X : Scheme} {a b : ℕ}
    (E : AlgebraicVectorBundle X a) (F : AlgebraicVectorBundle X (a + b))
    (G : AlgebraicVectorBundle X b)
    (i : E.sheaf ⟶ F.sheaf) (p : F.sheaf ⟶ G.sheaf)
    (hz : i ≫ p = 0) (hex : (ShortComplex.mk i p hz).ShortExact) :
    Nonempty ((determinantLine F).sheaf ≅
      (tensorLine (determinantLine E) (determinantLine G)).sheaf) := by
  have hG : IsLocallyFreeOfRank G.sheaf (a + b - a) := by
    simpa only [Nat.add_sub_cancel_left] using G.locallyFree
  obtain ⟨δ, hδ⟩ := PublishedInputs.Determinant.lciExteriorMap_isIso
    E F G.sheaf i p hz hex (Nat.le_add_right a b) hG
  letI := hδ
  obtain ⟨d⟩ := determinantDual_iso E
  let e₀ : (determinantLine G).sheaf ≅
      tensorSheaf (exteriorSheaf (dualSheaf E.sheaf) a)
        (determinantLine F).sheaf := by
    simpa only [determinantLine, Nat.add_sub_cancel_left] using asIso δ
  let e := e₀ ≪≫ tensorIso d (Iso.refl (determinantLine F).sheaf)
  obtain ⟨ev⟩ := line_dual_evaluation (determinantLine E)
  let A := (determinantLine E).sheaf
  let B := (determinantLine F).sheaf
  let D := dualSheaf A
  exact ⟨(TensorConstruction.leftUnitIso B).symm ≪≫
    tensorIso ev.symm (Iso.refl B) ≪≫
    tensorIso (TensorConstruction.commIso D A) (Iso.refl B) ≪≫
    SheafTensor.associativityIso A D B ≪≫
    tensorIso (Iso.refl A) e.symm⟩

end LeBrunSalamon.TangentDeterminantProof

/- Evidence-only closure audit: none of the three replaced project admissions
may occur anywhere in a new proof's full dependency closure. -/
open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let cases : Array (Name × Name) := #[
    (``LeBrunSalamon.CotangentRankProof.smooth_cotangent_rank,
      ``LeBrunSalamon.PublishedInputs.Differentials.smoothCotangentPresentation),
    (``LeBrunSalamon.AmplePowerProof.ample_positivePower_iff,
      ``LeBrunSalamon.PublishedInputs.Ample.positive_tensorPower),
    (``LeBrunSalamon.TangentDeterminantProof.determinant_shortExact,
      ``LeBrunSalamon.PublishedInputs.Determinant.lciExteriorMap_isIso)]
  let forbidden : Array Name := #[
    `LeBrunSalamon.PublishedInputs.Step3e.smooth_cotangent_rank,
    `LeBrunSalamon.PublishedInputs.Step3e.ample_positivePower_iff,
    `LeBrunSalamon.PublishedInputs.Step3e.determinant_shortExact]
  for (target, required) in cases do
    let mut todo : Array Name := #[target]
    let mut cursor := 0
    let mut seen : NameSet := ({} : NameSet).insert target
    let mut directSorry : Array Name := #[]
    while cursor < todo.size do
      let name := todo[cursor]!
      cursor := cursor + 1
      let some ci := env.checked.get.find? name | throwError "Missing dependency {name}"
      let mut deps := ci.type.getUsedConstants
      if let some value := ci.value? (allowOpaque := true) then
        deps := deps ++ value.getUsedConstants
      if let .inductInfo value := ci then
        deps := deps ++ value.ctors.toArray
      if deps.contains ``sorryAx then
        directSorry := directSorry.push name
      for dep in deps do
        if !seen.contains dep then
          seen := seen.insert dep
          todo := todo.push dep
    for old in forbidden do
      if seen.contains old then
        throwError "Replaced project admission {old} is still used by {target}."
    if !seen.contains required then
      throwError "Expected generic published leaf {required} absent from {target}."
    logInfo m!"STEP3E_DEPENDENCIES target={target} old_admissions_used=false generic_leaf_used={required} all_constants={seen.toArray.size}"
    logInfo m!"DIRECT_SORRY_DECLARATIONS\n{String.intercalate "\n" (directSorry.toList.map Name.toString)}"

end

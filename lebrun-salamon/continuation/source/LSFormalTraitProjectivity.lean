import LSProjectivityDefinitions

/-!
# Projectivity after pullback to the complex formal trait

The proof uses affine neighbourhoods, the closed point of a local
spectrum, and stability of closed immersions under base change.
The imported definitions are independent of the Part04 frontier.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseSeven LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentySix LeBrunSalamon.PhaseTwentySeven
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseTwentyNine
open LeBrunSalamon.PhaseThirty LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.PhaseThirtyFour LeBrunSalamon.Skeleton

namespace LeBrunSalamon.Construction.ProjectiveBaseChangeProof

def mapBase {Y S T V : Scheme} (p : Y ⟶ S) (t : T ⟶ S) (i : V ⟶ S)
    (v : T ⟶ V) (hv : v ≫ i = t) : pullback p t ⟶ pullback p i :=
  pullback.lift (pullback.fst p t) (pullback.snd p t ≫ v) (by
    rw [Category.assoc, hv]
    exact pullback.condition)

@[reassoc] theorem mapBase_fst {Y S T V : Scheme}
    (p : Y ⟶ S) (t : T ⟶ S) (i : V ⟶ S) (v : T ⟶ V) (hv : v ≫ i = t) :
    mapBase p t i v hv ≫ pullback.fst p i = pullback.fst p t :=
  pullback.lift_fst _ _ _

@[reassoc] theorem mapBase_snd {Y S T V : Scheme}
    (p : Y ⟶ S) (t : T ⟶ S) (i : V ⟶ S) (v : T ⟶ V) (hv : v ≫ i = t) :
    mapBase p t i v hv ≫ pullback.snd p i = pullback.snd p t ≫ v :=
  pullback.lift_snd _ _ _

theorem mapBase_isPullback {Y S T V : Scheme}
    (p : Y ⟶ S) (t : T ⟶ S) (i : V ⟶ S) (v : T ⟶ V) (hv : v ≫ i = t) :
    IsPullback (mapBase p t i v hv) (pullback.snd p t) (pullback.snd p i) v := by
  apply IsPullback.of_right (t := IsPullback.of_hasPullback p i)
  · simpa only [mapBase_fst, hv] using (IsPullback.of_hasPullback p t)
  · exact mapBase_snd p t i v hv

theorem closedEmbedding_baseChange
    {B C T V : Scheme} (pi : C ⟶ B) (sB : B ⟶ ComplexBase)
    (i : V ⟶ B) (N : ℕ)
    (j : pullback pi i ⟶ pullback (projectiveBaseMap N) (i ≫ sB))
    (hj : IsClosedImmersion j)
    (hjbase : j ≫ pullback.snd (projectiveBaseMap N) (i ≫ sB) =
      pullback.snd pi i)
    (t : T ⟶ B) (sT : T ⟶ ComplexBase) (ht : t ≫ sB = sT)
    (v : T ⟶ V) (hv : v ≫ i = t) :
    ∃ jT : pullback pi t ⟶ pullback (projectiveBaseMap N) sT,
      IsClosedImmersion jT ∧
        jT ≫ pullback.snd (projectiveBaseMap N) sT = pullback.snd pi t := by
  let a := mapBase pi t i v hv
  have haFst : a ≫ pullback.fst pi i = pullback.fst pi t :=
    mapBase_fst pi t i v hv
  have haSnd : a ≫ pullback.snd pi i = pullback.snd pi t ≫ v :=
    mapBase_snd pi t i v hv
  have haPull : IsPullback a (pullback.snd pi t) (pullback.snd pi i) v :=
    mapBase_isPullback pi t i v hv
  have hvC : v ≫ (i ≫ sB) = sT := by
    rw [← Category.assoc, hv, ht]
  let b := mapBase (projectiveBaseMap N) sT (i ≫ sB) v hvC
  have hbFst : b ≫ pullback.fst (projectiveBaseMap N) (i ≫ sB) =
      pullback.fst (projectiveBaseMap N) sT :=
    mapBase_fst (projectiveBaseMap N) sT (i ≫ sB) v hvC
  have hbSnd : b ≫ pullback.snd (projectiveBaseMap N) (i ≫ sB) =
      pullback.snd (projectiveBaseMap N) sT ≫ v :=
    mapBase_snd (projectiveBaseMap N) sT (i ≫ sB) v hvC
  have hbPull : IsPullback b (pullback.snd (projectiveBaseMap N) sT)
      (pullback.snd (projectiveBaseMap N) (i ≫ sB)) v :=
    mapBase_isPullback (projectiveBaseMap N) sT (i ≫ sB) v hvC
  have hcomm :
      (a ≫ j ≫ pullback.fst (projectiveBaseMap N) (i ≫ sB)) ≫
          projectiveBaseMap N = pullback.snd pi t ≫ sT := by
    calc
      _ = (a ≫ j ≫ pullback.snd (projectiveBaseMap N) (i ≫ sB)) ≫
          (i ≫ sB) := by simp only [Category.assoc, pullback.condition]
      _ = (a ≫ pullback.snd pi i) ≫ (i ≫ sB) := by rw [hjbase]
      _ = (pullback.snd pi t ≫ v) ≫ (i ≫ sB) := by rw [haSnd]
      _ = pullback.snd pi t ≫ sT := by rw [Category.assoc, hvC]
  let jT : pullback pi t ⟶ pullback (projectiveBaseMap N) sT :=
    pullback.lift (a ≫ j ≫ pullback.fst (projectiveBaseMap N) (i ≫ sB))
      (pullback.snd pi t) hcomm
  have hjTFst : jT ≫ pullback.fst (projectiveBaseMap N) sT =
      a ≫ j ≫ pullback.fst (projectiveBaseMap N) (i ≫ sB) :=
    pullback.lift_fst _ _ _
  have hjTSnd : jT ≫ pullback.snd (projectiveBaseMap N) sT =
      pullback.snd pi t := pullback.lift_snd _ _ _
  have hjTPull : IsPullback jT a b j := by
    apply IsPullback.of_right (t := hbPull.flip)
    · simpa only [hjTSnd, hjbase] using haPull.flip
    · apply pullback.hom_ext
      · calc
          (jT ≫ b) ≫ pullback.fst (projectiveBaseMap N) (i ≫ sB) =
              jT ≫ pullback.fst (projectiveBaseMap N) sT := by
                rw [Category.assoc, hbFst]
          _ = a ≫ j ≫ pullback.fst (projectiveBaseMap N) (i ≫ sB) := hjTFst
          _ = (a ≫ j) ≫ pullback.fst (projectiveBaseMap N) (i ≫ sB) := by
            rw [Category.assoc]
      · calc
          (jT ≫ b) ≫ pullback.snd (projectiveBaseMap N) (i ≫ sB) =
              (jT ≫ pullback.snd (projectiveBaseMap N) sT) ≫ v := by
                rw [Category.assoc, hbSnd, Category.assoc]
          _ = pullback.snd pi t ≫ v := by rw [hjTSnd]
          _ = a ≫ pullback.snd pi i := haSnd.symm
          _ = (a ≫ j) ≫ pullback.snd (projectiveBaseMap N) (i ≫ sB) := by
            rw [Category.assoc, hjbase]
  exact ⟨jT, MorphismProperty.of_isPullback hjTPull.flip hj, hjTSnd⟩

end LeBrunSalamon.Construction.ProjectiveBaseChangeProof

namespace LeBrunSalamon.StandardInputs

/-- Stacks 01WF: pull back an actual closed projective embedding from
an affine neighbourhood of the closed image of the local trait. Its
preimage contains the closed point and hence the whole trait. Further
restriction gives the demanded embedding over every affine trait open. -/
theorem isProjectiveOver_formalTrait
    {B C : Scheme} (pi : C ⟶ B) (sB : B ⟶ ComplexBase)
    (hprojective : LeBrunSalamon.Construction.StableMaps.IsProjectiveOver pi sB)
    (t : PointsOver LeBrunSalamon.Construction.StableMaps.FormalArcs.Trait
      LeBrunSalamon.Construction.StableMaps.FormalArcs.toC B sB) :
    LeBrunSalamon.Construction.StableMaps.IsProjectiveOver
      (pullback.snd pi t.val) LeBrunSalamon.Construction.StableMaps.FormalArcs.toC := by
  classical
  obtain ⟨V, hV, hxV, _⟩ := exists_isAffineOpen_mem_and_subset
    (U := (⊤ : B.Opens))
    (x := t.val (IsLocalRing.closedPoint (PowerSeries ℂ))) (by trivial)
  have hpre : t.val ⁻¹ᵁ V = ⊤ :=
    Scheme.preimage_eq_top_of_closedPoint_mem t.val hxV
  have hrange : Set.range t.val ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    change x ∈ t.val ⁻¹ᵁ V
    rw [hpre]
    trivial
  let v := IsOpenImmersion.lift V.ι t.val hrange
  have hv : v ≫ V.ι = t.val :=
    IsOpenImmersion.lift_fac V.ι t.val hrange
  obtain ⟨N, j, hj, hjbase⟩ := hprojective V hV
  intro U _hU
  obtain ⟨jU, hjU, hjUbase⟩ :=
    LeBrunSalamon.Construction.ProjectiveBaseChangeProof.closedEmbedding_baseChange
      pi sB V.ι N j hj hjbase (U.ι ≫ t.val)
      (U.ι ≫ LeBrunSalamon.Construction.StableMaps.FormalArcs.toC)
      (by rw [Category.assoc, t.property]) (U.ι ≫ v)
      (by rw [Category.assoc, hv])
  let e := pullbackLeftPullbackSndIso pi t.val U.ι
  have hebase : e.hom ≫ pullback.snd pi (U.ι ≫ t.val) =
      pullback.snd (pullback.snd pi t.val) U.ι :=
    pullbackLeftPullbackSndIso_hom_snd _ _ _
  letI : IsClosedImmersion jU := hjU
  refine ⟨N, e.hom ≫ jU, inferInstance, ?_⟩
  rw [Category.assoc, hjUbase, hebase]

end LeBrunSalamon.StandardInputs

end

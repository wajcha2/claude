import LSP1FamilyDegree

/-! On a trivial projective bundle over an affine UFD, a line is
determined by its actual chosen field-valued fibre. This is a proved
translation of the already isolated projective-bundle Picard theorem;
no new Picard or family normal-form input is introduced. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirtyTwo

namespace LeBrunSalamon.ProjectiveFibreLineRigidity

variable {R : Type} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]

abbrev product (n : ℕ) (s : Spec (CommRingCat.of R) ⟶ ComplexBase) : Scheme :=
  pullback (ProjectiveQuotient.toSpec ℂ n) s

def fibre (n : ℕ) (s : Spec (CommRingCat.of R) ⟶ ComplexBase)
    (a : ComplexBase ⟶ Spec (CommRingCat.of R)) (ha : a ≫ s = 𝟙 ComplexBase) :
    ProjectiveQuotient.space ℂ n ⟶ product n s :=
  pullback.lift (𝟙 _) (ProjectiveQuotient.toSpec ℂ n ≫ a)
    (by simp only [Category.id_comp, Category.assoc, ha, Category.comp_id])

theorem factor (n : ℕ) (hn : 1 ≤ n) (s : Spec (CommRingCat.of R) ⟶ ComplexBase)
    [IsLocallyNoetherian (Spec (CommRingCat.of R))]
    [ConnectedSpace (Spec (CommRingCat.of R))] (L : LineBundle (product n s)) :
    ∃ Q : LineBundle (ProjectiveQuotient.space ℂ n),
      Nonempty (L.sheaf ≅ pullbackModule (pullback.fst (ProjectiveQuotient.toSpec ℂ n) s) Q.sheaf) := by
  obtain ⟨Q, N, hQ, hN, ⟨e⟩⟩ := PublishedInputs.Picard.projectiveBundle_externalLineFactor
    ℂ n hn s L.sheaf L.locallyFree
  obtain ⟨eN⟩ := PublishedInputs.Picard.affineUFD_trivial R N hN
  let q := pullback.snd (ProjectiveQuotient.toSpec ℂ n) s
  let c : structureModule (product n s) ≅ pullbackModule q N :=
    (unitPullbackIso q).symm ≪≫ (Scheme.Modules.pullback q).mapIso eN
  exact ⟨⟨Q, hQ⟩, ⟨(TensorConstruction.rightUnitIso L.sheaf).symm ≪≫
    tensorIso (Iso.refl _) c ≪≫ e⟩⟩

def fibreFactor (n : ℕ) (s : Spec (CommRingCat.of R) ⟶ ComplexBase)
    (a : ComplexBase ⟶ Spec (CommRingCat.of R)) (ha : a ≫ s = 𝟙 ComplexBase)
    (L : LineBundle (product n s)) (Q : LineBundle (ProjectiveQuotient.space ℂ n))
    (e : L.sheaf ≅ pullbackModule (pullback.fst (ProjectiveQuotient.toSpec ℂ n) s) Q.sheaf) :
    pullbackModule (fibre n s a ha) L.sheaf ≅ Q.sheaf :=
  (Scheme.Modules.pullback (fibre n s a ha)).mapIso e ≪≫
    P1FamilyDegree.pullComp (fibre n s a ha)
      (pullback.fst (ProjectiveQuotient.toSpec ℂ n) s) (𝟙 _)
      (pullback.lift_fst _ _ _) Q.sheaf ≪≫
    (Scheme.Modules.pullbackId _).app Q.sheaf

/-- Compare the exact selected line bundles using the exact selected
fibre map. This applies in particular to the defining ideal and O(-2)
once their closed-fibre comparison has been proved. -/
theorem iso_of_fibre_iso (n : ℕ) (hn : 1 ≤ n)
    (s : Spec (CommRingCat.of R) ⟶ ComplexBase)
    [IsLocallyNoetherian (Spec (CommRingCat.of R))]
    [ConnectedSpace (Spec (CommRingCat.of R))]
    (a : ComplexBase ⟶ Spec (CommRingCat.of R)) (ha : a ≫ s = 𝟙 ComplexBase)
    (L M : LineBundle (product n s))
    (e0 : pullbackModule (fibre n s a ha) L.sheaf ≅
      pullbackModule (fibre n s a ha) M.sheaf) : Nonempty (L.sheaf ≅ M.sheaf) := by
  obtain ⟨QL, ⟨eL⟩⟩ := factor n hn s L
  obtain ⟨QM, ⟨eM⟩⟩ := factor n hn s M
  let c : QL.sheaf ≅ QM.sheaf :=
    (fibreFactor n s a ha L QL eL).symm ≪≫ e0 ≪≫ fibreFactor n s a ha M QM eM
  exact ⟨eL ≪≫
    (Scheme.Modules.pullback (pullback.fst (ProjectiveQuotient.toSpec ℂ n) s)).mapIso c ≪≫
    eM.symm⟩

end LeBrunSalamon.ProjectiveFibreLineRigidity

end

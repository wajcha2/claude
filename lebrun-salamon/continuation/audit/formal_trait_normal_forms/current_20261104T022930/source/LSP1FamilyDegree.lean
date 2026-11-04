import LSPublishedProjectiveSpace
import RecompileSections

/-! The generic Picard decomposition of a trivial projective bundle, followed
by actual fibre pullback and cancellation. No degree is assumed in the leaf. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.ProjectiveQuotient LeBrunSalamon.P1Charts

namespace LeBrunSalamon.PublishedInputs.Picard

/-- Kleiman, The Picard scheme (2005), Exercise 4.15 and Answer 4.15,
printed pp.33 and67–68. The standing convention on p.15 is locally
Noetherian schemes. For a connected base T the answer gives
L tensor pr_T^* N = O(n). On the trivial projective bundle O(n) is the
pullback of O(n) on the fixed projective space. We retain this orientation
and only forget the integer and the particular choice of the latter line.

This leaf uses the canonical polynomial Proj, not a marked projective
line, a chosen degree, or the project's alternative complex base map. -/
theorem projectiveBundle_externalLineFactor (K : Type) [Field K]
    (n : ℕ) (hn : 1 ≤ n) {T : Scheme} [IsLocallyNoetherian T]
    [ConnectedSpace T] (s : T ⟶ Spec (CommRingCat.of K))
    (L : (pullback (toSpec K n) s : Scheme).Modules)
    (hL : IsLocallyFreeOfRank L 1) :
    ∃ (Q : (space K n).Modules) (N : T.Modules),
      IsLocallyFreeOfRank Q 1 ∧ IsLocallyFreeOfRank N 1 ∧
      Nonempty (tensorSheaf L (pullbackModule (pullback.snd (toSpec K n) s) N) ≅
        pullbackModule (pullback.fst (toSpec K n) s) Q) := by
  sorry

end LeBrunSalamon.PublishedInputs.Picard

namespace LeBrunSalamon.P1FamilyDegree

def pullComp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : X ⟶ Z) (e : f ≫ g = h) (E : Z.Modules) :
    pullbackModule f (pullbackModule g E) ≅ pullbackModule h E :=
  (Scheme.Modules.pullbackComp f g).app E ≪≫
    (Scheme.Modules.pullbackCongr e).app E

def pullUnit {X Y : Scheme} (f : X ⟶ Y) :
    pullbackModule f (structureModule Y) ≅ structureModule X := unitPullbackIso f

/-- The base factor becomes trivial on an actual field-valued fibre. -/
def fibreBaseTrivial {X T : Scheme} (f : X ⟶ ComplexBase)
    (a : ComplexBase ⟶ T) (N : T.Modules) (hN : IsLocallyFreeOfRank N 1) :
    pullbackModule (f ≫ a) N ≅ structureModule X := by
  let e : structureModule ComplexBase ≅ pullbackModule a N :=
    Classical.choice (PublishedInputs.Picard.affineUFD_trivial ℂ
      (pullbackModule a N) (pullback_locallyFree a hN))
  exact ((Scheme.Modules.pullbackComp f a).app N).symm ≪≫
    (Scheme.Modules.pullback f).mapIso e.symm ≪≫ pullUnit f

/-- Fibre comparison for a given external decomposition. Every map is the
actual pullback projection or fibre inclusion. -/
def fibreIso {X T : Scheme} (f : X ⟶ ComplexBase) (s : T ⟶ ComplexBase)
    (L : (pullback f s : Scheme).Modules) (Q : X.Modules)
    (N : T.Modules) (hN : IsLocallyFreeOfRank N 1)
    (e : tensorSheaf L (pullbackModule (pullback.snd f s) N) ≅
      pullbackModule (pullback.fst f s) Q)
    (a : ComplexBase ⟶ T) (ha : a ≫ s = 𝟙 ComplexBase) :
    pullbackModule (pullback.lift (𝟙 X) (f ≫ a)
      (by simp only [Category.id_comp, Category.assoc, ha, Category.comp_id])) L ≅ Q := by
  let i : X ⟶ pullback f s := pullback.lift (𝟙 X) (f ≫ a)
    (by simp only [Category.id_comp, Category.assoc, ha, Category.comp_id])
  let eN : pullbackModule i (pullbackModule (pullback.snd f s) N) ≅
      structureModule X :=
    pullComp i (pullback.snd f s) (f ≫ a) (by simp [i]) N ≪≫
      fibreBaseTrivial f a N hN
  let eQ : pullbackModule i (pullbackModule (pullback.fst f s) Q) ≅ Q :=
    pullComp i (pullback.fst f s) (𝟙 X) (by simp [i]) Q ≪≫
      (Scheme.Modules.pullbackId X).app Q
  let et := Classical.choice (tensorSheaf_pullback i L (pullbackModule (pullback.snd f s) N))
  exact (TensorConstruction.rightUnitIso (pullbackModule i L)).symm ≪≫
    tensorIso (Iso.refl _) eN.symm ≪≫ et.symm ≪≫
    (Scheme.Modules.pullback i).mapIso e ≪≫ eQ

/-- Rebase the family along the inverse of the supplied complex base
isomorphism. The projective-space point and the parameter point are fixed. -/
def canonicalFamilyIso (P : ProjectiveLineOverC) {T : Scheme}
    (s : T ⟶ ComplexBase) :
    pullback P.structureMap s ≅
      pullback canonicalBaseMap (s ≫ (CotangentTwistProof.baseChangeIso P).inv) := by
  let A := CotangentTwistProof.baseChangeIso P
  have hP : P.structureMap ≫ A.inv = canonicalBaseMap := by
    rw [← CotangentTwistProof.baseMap_factor P]
    simp [A, Category.assoc]
  refine
    { hom := pullback.lift (pullback.fst P.structureMap s)
        (pullback.snd P.structureMap s) ?_
      inv := pullback.lift
        (pullback.fst canonicalBaseMap (s ≫ A.inv))
        (pullback.snd canonicalBaseMap (s ≫ A.inv)) ?_
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · rw [← hP, ← Category.assoc, pullback.condition, Category.assoc]
  · apply (cancel_mono A.inv).1
    simpa only [Category.assoc, hP] using
      pullback.condition (f := canonicalBaseMap) (g := s ≫ A.inv)
  · apply pullback.hom_ext <;> simp [A, Category.assoc]
  · apply pullback.hom_ext <;> simp [A, Category.assoc]

theorem canonicalFamilyIso_fst (P : ProjectiveLineOverC) {T : Scheme}
    (s : T ⟶ ComplexBase) :
    (canonicalFamilyIso P s).hom ≫
      pullback.fst canonicalBaseMap (s ≫ (CotangentTwistProof.baseChangeIso P).inv) =
        pullback.fst P.structureMap s := by
  simp [canonicalFamilyIso]

theorem canonicalFamilyIso_snd (P : ProjectiveLineOverC) {T : Scheme}
    (s : T ⟶ ComplexBase) :
    (canonicalFamilyIso P s).hom ≫
      pullback.snd canonicalBaseMap (s ≫ (CotangentTwistProof.baseChangeIso P).inv) =
        pullback.snd P.structureMap s := by
  simp [canonicalFamilyIso]

theorem toSpec_canonical : toSpec ℂ 1 = canonicalBaseMap := rfl

/-- Transport the generic decomposition across the proved family
isomorphism. This is where the noncanonical complex base is handled. -/
theorem externalFactor (P : ProjectiveLineOverC) {T : Scheme}
    (s : T ⟶ ComplexBase) [LocallyOfFiniteType s] [ConnectedSpace T]
    (L : LineBundle (pullback P.structureMap s)) :
    ∃ (Q : LineBundle ProjectiveLine) (N : LineBundle T),
      Nonempty (tensorSheaf L.sheaf
        (pullbackModule (pullback.snd P.structureMap s) N.sheaf) ≅
          pullbackModule (pullback.fst P.structureMap s) Q.sheaf) := by
  letI : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian s
  let A := CotangentTwistProof.baseChangeIso P
  let t := s ≫ A.inv
  let j := canonicalFamilyIso P s
  let M := pullbackModule j.inv L.sheaf
  have hM : IsLocallyFreeOfRank M 1 := pullback_locallyFree j.inv L.locallyFree
  have hp := PublishedInputs.Picard.projectiveBundle_externalLineFactor ℂ 1
    (by omega) t M hM
  obtain ⟨Q, N, hQ, hN, ⟨e⟩⟩ := hp
  refine ⟨⟨Q, hQ⟩, ⟨N, hN⟩, ?_⟩
  let eL : pullbackModule j.hom M ≅ L.sheaf :=
    pullComp j.hom j.inv (𝟙 _) j.hom_inv_id L.sheaf ≪≫
      (Scheme.Modules.pullbackId _).app L.sheaf
  let eN : pullbackModule j.hom
      (pullbackModule (pullback.snd canonicalBaseMap t) N) ≅
      pullbackModule (pullback.snd P.structureMap s) N :=
    pullComp j.hom (pullback.snd canonicalBaseMap t)
      (pullback.snd P.structureMap s) (canonicalFamilyIso_snd P s) N
  let eQ : pullbackModule j.hom
      (pullbackModule (pullback.fst canonicalBaseMap t) Q) ≅
      pullbackModule (pullback.fst P.structureMap s) Q :=
    pullComp j.hom (pullback.fst canonicalBaseMap t)
      (pullback.fst P.structureMap s) (canonicalFamilyIso_fst P s) Q
  obtain ⟨et⟩ := tensorSheaf_pullback j.hom M
    (pullbackModule (pullback.snd canonicalBaseMap t) N)
  exact ⟨tensorIso eL.symm eN.symm ≪≫ et.symm ≪≫
    (Scheme.Modules.pullback j.hom).mapIso e ≪≫ eQ⟩

/-- The two actual fibre bundles are isomorphic, because each is the
fixed factor Q after cancellation of the base factor. -/
theorem familyDegreeConstant (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {T : Scheme} (s : T ⟶ ComplexBase)
    [LocallyOfFiniteType s] [ConnectedSpace T]
    (L : LineBundle (pullback P.structureMap s))
    (a b : ComplexBase ⟶ T)
    (ha : a ≫ s = 𝟙 ComplexBase) (hb : b ≫ s = 𝟙 ComplexBase) :
    projectiveLineDegree P p
      (pullbackLine (pullback.lift (𝟙 ProjectiveLine) (P.structureMap ≫ a)
        (by simp only [Category.id_comp, Category.assoc, ha,
          Category.comp_id])) L) =
    projectiveLineDegree P p
      (pullbackLine (pullback.lift (𝟙 ProjectiveLine) (P.structureMap ≫ b)
        (by simp only [Category.id_comp, Category.assoc, hb,
          Category.comp_id])) L) := by
  obtain ⟨Q, N, ⟨e⟩⟩ := externalFactor P s L
  exact projectiveLineDegree_iso P p _ _
    (fibreIso P.structureMap s L.sheaf Q.sheaf N.sheaf N.locallyFree e a ha ≪≫
      (fibreIso P.structureMap s L.sheaf Q.sheaf N.sheaf N.locallyFree e b hb).symm)

end LeBrunSalamon.P1FamilyDegree

end

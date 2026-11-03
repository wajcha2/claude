import RecompileExtensionsPart03

/-!
# Actual projective-line source transport

The universal quotient presentation of projective space constructs its
coefficient-change automorphisms. This handles every permitted
degree-zero identification with Spec C, including nontrivial field
automorphisms. Two-point interpolation and degree-two contact curves
are transported through the actual scheme and sheaf maps.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseSeven LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentySix LeBrunSalamon.PhaseTwentySeven
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.PhaseThirtyFive LeBrunSalamon.Core LeBrunSalamon.Skeleton
open LeBrunSalamon.PointBaseTransport

namespace LeBrunSalamon.ProjectiveTransport

/-- A composite over the canonical base which preserves the universal
quotient tuple is the identity. The two factors need not themselves
preserve that base map. -/
theorem composite_identity {N : ℕ} (C : ProjectiveCoordinates N)
    (f g : ComplexProjectiveSpace N ⟶ ComplexProjectiveSpace N)
    (hbase : (f ≫ g) ≫ projectiveBaseMap N = projectiveBaseMap N)
    (l : pullbackModule f C.hyperplane.sheaf ≅ C.hyperplane.sheaf)
    (k : pullbackModule g C.hyperplane.sheaf ≅ C.hyperplane.sheaf)
    (hf : ∀ i, pullSection f (C.coordinate i) ≫ l.hom = C.coordinate i)
    (hg : ∀ i, pullSection g (C.coordinate i) ≫ k.hom = C.coordinate i) :
    f ≫ g = 𝟙 (ComplexProjectiveSpace N) := by
  let p := (Scheme.Modules.pullbackComp f g).app C.hyperplane.sheaf
  let c : pullbackModule (f ≫ g) C.hyperplane.sheaf ≅ C.hyperplane.sheaf :=
    p.symm ≪≫ (Scheme.Modules.pullback f).mapIso k ≪≫ l
  have hc (i : Fin (N+1)) :
      pullSection (f ≫ g) (C.coordinate i) ≫ c.hom = C.coordinate i := by
    calc
      _ = pullSection f (pullSection g (C.coordinate i) ≫ k.hom) ≫ l.hom := by
        change pullSection (f ≫ g) (C.coordinate i) ≫
          (p.inv ≫ (Scheme.Modules.pullback f).map k.hom ≫ l.hom) = _
        rw [← LeBrunSalamon.Refinement.CanonicalPullbackSectionProof.pullSection_comp]
        change (pullSection f (pullSection g (C.coordinate i)) ≫ p.hom) ≫
          (p.inv ≫ (Scheme.Modules.pullback f).map k.hom ≫ l.hom) = _
        simp only [Category.assoc, p.hom_inv_id_assoc]
        rw [ExternalExchangeCoherenceProof.pullSection_map, Category.assoc]
      _ = pullSection f (C.coordinate i) ≫ l.hom := by rw [hg i]
      _ = C.coordinate i := hf i
  let fg : PointsOver (ComplexProjectiveSpace N) (projectiveBaseMap N)
      (ComplexProjectiveSpace N) (projectiveBaseMap N) := ⟨f ≫ g, hbase⟩
  let idp : PointsOver (ComplexProjectiveSpace N) (projectiveBaseMap N)
      (ComplexProjectiveSpace N) (projectiveBaseMap N) := ⟨𝟙 _, Category.id_comp _⟩
  obtain ⟨a, _, hu⟩ := C.universal (ComplexProjectiveSpace N) (projectiveBaseMap N)
    C.hyperplane C.coordinate C.generates
  have hfg : fg = a := hu fg ⟨c, hc⟩
  have hid : idp = a := hu idp
    ⟨(Scheme.Modules.pullbackId (ComplexProjectiveSpace N)).app C.hyperplane.sheaf,
      fun i => ExternalExchangeCoherenceProof.pullSection_id (C.coordinate i)⟩
  exact congrArg Subtype.val (hfg.trans hid.symm)

/-- The full quotient universal property constructs coefficient change
on the actual Proj scheme. No continuity of the field automorphism is
required, and no arbitrary bijection on complex points is substituted. -/
theorem coefficientIso_exists (N : ℕ) (C : ProjectiveCoordinates N)
    (e : ComplexBase ≅ ComplexBase) :
    ∃ i : ComplexProjectiveSpace N ≅ ComplexProjectiveSpace N,
      i.hom ≫ projectiveBaseMap N = projectiveBaseMap N ≫ e.hom := by
  obtain ⟨f, ⟨l, hl⟩, _⟩ := C.universal (ComplexProjectiveSpace N)
    (projectiveBaseMap N ≫ e.hom) C.hyperplane C.coordinate C.generates
  obtain ⟨g, ⟨k, hk⟩, _⟩ := C.universal (ComplexProjectiveSpace N)
    (projectiveBaseMap N ≫ e.inv) C.hyperplane C.coordinate C.generates
  have hfg : (f.val ≫ g.val) ≫ projectiveBaseMap N = projectiveBaseMap N := by
    calc
      _ = f.val ≫ (g.val ≫ projectiveBaseMap N) := Category.assoc _ _ _
      _ = f.val ≫ (projectiveBaseMap N ≫ e.inv) := by rw [g.property]
      _ = (f.val ≫ projectiveBaseMap N) ≫ e.inv := (Category.assoc _ _ _).symm
      _ = (projectiveBaseMap N ≫ e.hom) ≫ e.inv := by rw [f.property]
      _ = projectiveBaseMap N := by simp only [Category.assoc, e.hom_inv_id, Category.comp_id]
  have hgf : (g.val ≫ f.val) ≫ projectiveBaseMap N = projectiveBaseMap N := by
    calc
      _ = g.val ≫ (f.val ≫ projectiveBaseMap N) := Category.assoc _ _ _
      _ = g.val ≫ (projectiveBaseMap N ≫ e.hom) := by rw [f.property]
      _ = (g.val ≫ projectiveBaseMap N) ≫ e.hom := (Category.assoc _ _ _).symm
      _ = (projectiveBaseMap N ≫ e.inv) ≫ e.hom := by rw [g.property]
      _ = projectiveBaseMap N := by simp only [Category.assoc, e.inv_hom_id, Category.comp_id]
  exact ⟨{ hom := f.val, inv := g.val
           hom_inv_id := composite_identity C f.val g.val hfg l k hl hk
           inv_hom_id := composite_identity C g.val f.val hgf k l hk hl }, f.property⟩

def canonicalSourceIso (P : ProjectiveLineOverC) : ProjectiveLine ≅ ProjectiveLine :=
  Classical.choose (coefficientIso_exists 1 (projectiveCoordinates 1)
    (ScalarTransport.projectiveBaseIso P))

theorem canonicalSourceIso_over (P : ProjectiveLineOverC) :
    (canonicalSourceIso P).hom ≫ canonicalProjectiveLine.structureMap = P.structureMap := by
  have h := Classical.choose_spec (coefficientIso_exists 1 (projectiveCoordinates 1)
    (ScalarTransport.projectiveBaseIso P))
  change (canonicalSourceIso P).hom ≫ canonicalProjectiveLine.structureMap =
    canonicalProjectiveLine.structureMap ≫ (ScalarTransport.projectiveBaseIso P).hom at h
  exact h.trans (ScalarTransport.projective_structureMap_factor P)

/-- An actual isomorphism from the supplied P model to the supplied Q model. -/
def sourceIso (P Q : ProjectiveLineOverC) : ProjectiveLine ≅ ProjectiveLine :=
  canonicalSourceIso P ≪≫ (canonicalSourceIso Q).symm

theorem sourceIso_over (P Q : ProjectiveLineOverC) :
    (sourceIso P Q).hom ≫ Q.structureMap = P.structureMap := by
  change ((canonicalSourceIso P).hom ≫ (canonicalSourceIso Q).inv) ≫
    Q.structureMap = P.structureMap
  rw [← canonicalSourceIso_over Q]
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using canonicalSourceIso_over P

theorem inverse_over {P Q : ProjectiveLineOverC} (e : ProjectiveLine ≅ ProjectiveLine)
    (he : e.hom ≫ Q.structureMap = P.structureMap) :
    e.inv ≫ P.structureMap = Q.structureMap := by
  rw [← he]
  simp only [← Category.assoc, e.inv_hom_id, Category.id_comp]

/-- Pulling back a globally interpolating section respects the original
un-normalized restriction targets. Both source-unit and composition
comparisons are kept explicitly. -/
theorem pointPairRestriction_pullback_surjective {Y Z : Scheme}
    (f : Y ⟶ Z) (E : OModule Z) (x y : ComplexBase ⟶ Y)
    (h : Function.Surjective (pointPairRestriction E (x ≫ f) (y ≫ f))) :
    Function.Surjective (pointPairRestriction (pullbackModule f E) x y) := by
  rintro ⟨a, b⟩
  let F := Scheme.Modules.pullback f
  let Fx := Scheme.Modules.pullback x
  let Fy := Scheme.Modules.pullback y
  let cx := Scheme.Modules.pullbackComp x f
  let cy := Scheme.Modules.pullbackComp y f
  let ax := (cx.app (structureModule Z)).inv ≫ Fx.map (unitPullbackIso f).hom ≫
    a ≫ (cx.app E).hom
  let byv := (cy.app (structureModule Z)).inv ≫ Fy.map (unitPullbackIso f).hom ≫
    b ≫ (cy.app E).hom
  obtain ⟨s, hs⟩ := h (ax, byv)
  have hx := congrArg Prod.fst hs
  have hy := congrArg Prod.snd hs
  change (Scheme.Modules.pullback (x ≫ f)).map s = ax at hx
  change (Scheme.Modules.pullback (y ≫ f)).map s = byv at hy
  refine ⟨pullSection f s, Prod.ext ?_ ?_⟩
  · change Fx.map ((unitPullbackIso f).inv ≫ F.map s) = a
    apply (cancel_mono (cx.app E).hom).mp
    rw [Functor.map_comp, Category.assoc]
    have hn := cx.hom.naturality s
    change Fx.map (F.map s) ≫ (cx.app E).hom =
      (cx.app (structureModule Z)).hom ≫
        (Scheme.Modules.pullback (x ≫ f)).map s at hn
    rw [hn, hx]
    simp only [ax, Category.assoc, Iso.hom_inv_id_assoc,
      ← Functor.map_comp_assoc, Iso.inv_hom_id, Functor.map_id, Category.id_comp]
    exact (congrArg
      (fun u : Fx.obj (structureModule Y) ⟶ Fx.obj (structureModule Y) =>
        u ≫ a ≫ (cx.app E).hom)
      (Fx.map_id (structureModule Y))).trans (Category.id_comp _)
  · change Fy.map ((unitPullbackIso f).inv ≫ F.map s) = b
    apply (cancel_mono (cy.app E).hom).mp
    rw [Functor.map_comp, Category.assoc]
    have hn := cy.hom.naturality s
    change Fy.map (F.map s) ≫ (cy.app E).hom =
      (cy.app (structureModule Z)).hom ≫
        (Scheme.Modules.pullback (y ≫ f)).map s at hn
    rw [hn, hy]
    simp only [byv, Category.assoc, Iso.hom_inv_id_assoc,
      ← Functor.map_comp_assoc, Iso.inv_hom_id, Functor.map_id, Category.id_comp]
    exact (congrArg
      (fun u : Fy.obj (structureModule Y) ⟶ Fy.obj (structureModule Y) =>
        u ≫ b ≫ (cy.app E).hom)
      (Fy.map_id (structureModule Y))).trans (Category.id_comp _)

theorem twoPointGeneration_pullback {P Q : ProjectiveLineOverC}
    (f : ProjectiveLine ⟶ ProjectiveLine) [Mono f]
    (hf : f ≫ Q.structureMap = P.structureMap) (E : OModule ProjectiveLine)
    (h : IsTwoPointGloballyGenerated Q E) :
    IsTwoPointGloballyGenerated P (pullbackModule f E) := by
  refine ⟨projectiveLine_hasDistinctPoints P, ?_⟩
  intro x y hxy
  let xf : ProjectiveLinePoint Q := ⟨x.map ≫ f, by rw [Category.assoc, hf, x.overC]⟩
  let yf : ProjectiveLinePoint Q := ⟨y.map ≫ f, by rw [Category.assoc, hf, y.overC]⟩
  have hdist : xf.map ≠ yf.map := by
    intro heq
    exact hxy ((cancel_mono f).mp heq)
  exact pointPairRestriction_pullback_surjective f E x.map y.map (h.2 xf yf hdist)

def curve {P Q : ProjectiveLineOverC} {d : ℕ}
    {X : SmoothProperComplexVariety d} (e : ProjectiveLine ≅ ProjectiveLine)
    (he : e.hom ≫ Q.structureMap = P.structureMap) (g : RationalCurve Q X) :
    RationalCurve P X where
  map := e.hom ≫ g.map
  overC := by rw [Category.assoc, g.overC]; exact he
  nonconstant := by
    rintro ⟨x, hx, h⟩
    apply g.nonconstant
    refine ⟨x, hx, ?_⟩
    have h' := congrArg (fun k => e.inv ≫ k) h
    simpa only [← Category.assoc, e.inv_hom_id, Category.id_comp,
      inverse_over e he] using h'

/-- Degree two can be transported through the actual relative tangent
isomorphism: both tangent bundles are the actual O(2) twists. This
avoids assuming a numerical degree-invariance fact for an arbitrary
semilinear automorphism. -/
theorem degreeTwo_pullback (P Q : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (q : ProjectiveLinePoint Q)
    (e : ProjectiveLine ≅ ProjectiveLine)
    (he : e.hom ≫ Q.structureMap = P.structureMap)
    (L : LineBundle ProjectiveLine) (hL : projectiveLineDegree Q q L = 2) :
    projectiveLineDegree P p (pullbackLine e.hom L) = 2 := by
  have hLi := projectiveLineDegree_spec Q q L
  rw [hL] at hLi
  obtain ⟨l⟩ := hLi
  obtain ⟨tQ⟩ := projectiveLine_tangent_twist Q q
  obtain ⟨tP⟩ := projectiveLine_tangent_twist P p
  let d := differentialOver (projectiveLineVariety P) (projectiveLineVariety Q) e.hom he
  letI : IsIso d := ContactDerivativeIsoProof.differentialOver_isIso
    (projectiveLineVariety P) (projectiveLineVariety Q) e.hom he
  let k : (pullbackLine e.hom L).sheaf ≅ (projectiveTwist P p 2).sheaf :=
    (Scheme.Modules.pullback e.hom).mapIso (l ≪≫ tQ.symm) ≪≫
      (asIso d).symm ≪≫ tP
  exact (projectiveLineBundle_classification P p (pullbackLine e.hom L)).unique
    (projectiveLineDegree_spec P p _) ⟨k⟩

/-- Actual very free contact conics transport between all permitted
projective-line base models and all choices of marking. -/
def conic (P Q : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (q : ProjectiveLinePoint Q)
    {n : ℕ} {X : ContactFanoManifold n}
    (e : ProjectiveLine ≅ ProjectiveLine)
    (he : e.hom ≫ Q.structureMap = P.structureMap)
    (g : VeryFreeContactConic Q q X) : VeryFreeContactConic P p X where
  curve := curve e he g.curve
  contactDegreeTwo := by
    change projectiveLineDegree P p
      (pullbackLine (e.hom ≫ g.curve.map) X.contact.sequence.line) = 2
    have h := degreeTwo_pullback P Q p q e he
      (pullbackLine g.curve.map X.contact.sequence.line) g.contactDegreeTwo
    exact (projectiveLineDegree_iso P p _ _
      ((Scheme.Modules.pullbackComp e.hom g.curve.map).app
        X.contact.sequence.line.sheaf).symm).trans h
  veryFree := by
    have h := twoPointGeneration_pullback e.hom he
      (pullbackModule g.curve.map (intrinsicTangentBundle X.variety).sheaf) g.veryFree
    refine ⟨h.1, ?_⟩
    intro x y hxy
    exact (DirectSumEvaluation.twoPointBundleEvaluation_iso_iff P x y
      ((Scheme.Modules.pullbackComp e.hom g.curve.map).app
        (intrinsicTangentBundle X.variety).sheaf)).mp (h.2 x y hxy)

def conicBetweenModels (P Q : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (q : ProjectiveLinePoint Q)
    {n : ℕ} {X : ContactFanoManifold n} (g : VeryFreeContactConic Q q X) :
    VeryFreeContactConic P p X :=
  conic P Q p q (sourceIso P Q) (sourceIso_over P Q) g

end LeBrunSalamon.ProjectiveTransport

end

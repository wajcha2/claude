import RecompileExtensionsPart03

/-!
Actual contact-conic splitting.  The determinant calculation is made on
the original exterior-power presentations and on the actual finite sum
of line bundles.  No contact-conic conclusion is admitted here.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped BigOperators
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseThree LeBrunSalamon.PhaseSeven
open LeBrunSalamon.PhaseEighteen LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentySix LeBrunSalamon.PhaseTwentySeven
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.PhaseThirtyThree LeBrunSalamon.PhaseThirtyFive
open LeBrunSalamon.Skeleton

namespace LeBrunSalamon.ConicSplitting

namespace Exterior

/-- Precomposition on the original alternating sheaf maps. -/
def precompose {X : Scheme} {E F G : OModule X} {r : ℕ}
    (a : SheafAlternatingMap F G r) (f : E ⟶ F) :
    SheafAlternatingMap E G r where
  apply U v := a.apply U (fun i => f.app U (v i))
  add_slot := by
    intro U v i x y
    change a.apply U (f.app U ∘ Function.update v i (x + y)) =
      a.apply U (f.app U ∘ Function.update v i x) +
        a.apply U (f.app U ∘ Function.update v i y)
    simp only [Function.comp_update, map_add, a.add_slot]
  smul_slot := by
    intro U v i c x
    change a.apply U (f.app U ∘ Function.update v i (c • x)) =
      c • a.apply U (f.app U ∘ Function.update v i x)
    simp only [Function.comp_update, Scheme.Modules.Hom.app_smul, a.smul_slot]
  alternating := by
    intro U v i j hij heq
    exact a.alternating U _ i j hij (congrArg (f.app U) heq)
  naturality := by
    intro U V i v
    rw [a.naturality]
    apply congrArg (a.apply U)
    funext j
    exact sheafHom_naturality f i (v j)

def map {X : Scheme} {E F : OModule X} (f : E ⟶ F) (r : ℕ) :
    exteriorSheaf E r ⟶ exteriorSheaf F r :=
  exteriorLift (precompose (exteriorPresentation F r).wedge f)

theorem map_wedge {X : Scheme} {E F : OModule X} (f : E ⟶ F) (r : ℕ)
    (U : X.Opens) (v : Fin r → SectionsOn E U) :
    (map f r).app U ((exteriorPresentation E r).wedge.apply U v) =
      (exteriorPresentation F r).wedge.apply U (fun i => f.app U (v i)) := by
  exact congrArg (fun a : SheafAlternatingMap E (exteriorSheaf F r) r =>
    a.apply U v) (exteriorLift_spec
      (precompose (exteriorPresentation F r).wedge f))

theorem map_id {X : Scheme} (E : OModule X) (r : ℕ) :
    map (𝟙 E) r = 𝟙 (exteriorSheaf E r) := by
  apply ((exteriorPresentation E r).universal _).1
  apply SmallExteriorPowerProof.alternating_ext
  intro U v
  change (map (𝟙 E) r).app U ((exteriorPresentation E r).wedge.apply U v) = _
  rw [map_wedge]
  rfl

theorem map_comp {X : Scheme} {E F G : OModule X}
    (f : E ⟶ F) (g : F ⟶ G) (r : ℕ) :
    map (f ≫ g) r = map f r ≫ map g r := by
  apply ((exteriorPresentation E r).universal _).1
  apply SmallExteriorPowerProof.alternating_ext
  intro U v
  change (map (f ≫ g) r).app U ((exteriorPresentation E r).wedge.apply U v) =
    (map g r).app U ((map f r).app U
      ((exteriorPresentation E r).wedge.apply U v))
  rw [map_wedge, map_wedge, map_wedge]
  rfl

def mapIso {X : Scheme} {E F : OModule X} (e : E ≅ F) (r : ℕ) :
    exteriorSheaf E r ≅ exteriorSheaf F r where
  hom := map e.hom r
  inv := map e.inv r
  hom_inv_id := by rw [← map_comp, e.hom_inv_id, map_id]
  inv_hom_id := by rw [← map_comp, e.inv_hom_id, map_id]

end Exterior

def splitBundle (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {r : ℕ} (a : TangentSplittingProfile r) : AlgebraicVectorBundle ProjectiveLine r :=
  ⟨splitSheaf P p a, LeBrunSalamon.P1SplitBundles.splitSheaf_rank P p a⟩

def tailProfile {r : ℕ} (a : TangentSplittingProfile (r + 1)) :
    TangentSplittingProfile r := ⟨fun i => a.degree i.succ⟩

def tailInclusion (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {r : ℕ} (a : TangentSplittingProfile (r + 1)) :
    splitSheaf P p (tailProfile a) ⟶ splitSheaf P p a :=
  Sigma.desc (fun i => Sigma.ι (fun j => (projectiveTwist P p (a.degree j)).sheaf) i.succ)

def headProjection (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {r : ℕ} (a : TangentSplittingProfile (r + 1)) :
    splitSheaf P p a ⟶ (projectiveTwist P p (a.degree 0)).sheaf :=
  Sigma.desc (Fin.cases (𝟙 _) (fun _ => 0))

def tailProjection (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {r : ℕ} (a : TangentSplittingProfile (r + 1)) :
    splitSheaf P p a ⟶ splitSheaf P p (tailProfile a) :=
  Sigma.desc (Fin.cases 0 (fun i =>
    Sigma.ι (fun j => (projectiveTwist P p ((tailProfile a).degree j)).sheaf) i))

def headInclusion (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {r : ℕ} (a : TangentSplittingProfile (r + 1)) :
    (projectiveTwist P p (a.degree 0)).sheaf ⟶ splitSheaf P p a :=
  Sigma.ι (fun j => (projectiveTwist P p (a.degree j)).sheaf) 0

theorem tail_head_zero (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {r : ℕ} (a : TangentSplittingProfile (r + 1)) :
    tailInclusion P p a ≫ headProjection P p a = 0 := by
  apply Sigma.hom_ext
  intro i
  simp [tailInclusion, headProjection, Category.assoc]

def splitShortComplex (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {r : ℕ} (a : TangentSplittingProfile (r + 1)) : ShortComplex (OModule ProjectiveLine) :=
  ShortComplex.mk (tailInclusion P p a) (headProjection P p a) (tail_head_zero P p a)

def splitShortComplexSplitting (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {r : ℕ} (a : TangentSplittingProfile (r + 1)) : (splitShortComplex P p a).Splitting where
  r := tailProjection P p a
  s := headInclusion P p a
  f_r := by
    apply Sigma.hom_ext
    intro i
    simp [splitShortComplex, tailInclusion, tailProjection, splitSheaf, Category.assoc]
  s_g := by simp [splitShortComplex, headInclusion, headProjection]
  id := by
    apply Sigma.hom_ext
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [splitShortComplex, tailProjection, headProjection, headInclusion,
        splitSheaf, Preadditive.comp_add, Category.assoc]
    · simp [splitShortComplex, tailProjection, headProjection, tailInclusion,
        splitSheaf, Preadditive.comp_add, Category.assoc]

/-- The degree of the actual determinant of a split bundle is the sum
of its twisting degrees, including the rank-zero case. -/
theorem determinantDegree_split (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {r : ℕ} (a : TangentSplittingProfile r) :
    projectiveLineDegree P p (determinantLine (splitBundle P p a)) = profileDegree a := by
  induction r with
  | zero =>
    obtain ⟨e⟩ := exteriorSheaf_zero (splitSheaf P p a)
    calc
      projectiveLineDegree P p (determinantLine (splitBundle P p a)) =
          projectiveLineDegree P p (projectiveTwist P p 0) :=
        projectiveLineDegree_iso P p _ _ e
      _ = profileDegree a := by rw [projectiveTwist_degree]; simp [profileDegree]
  | succ r ih =>
    obtain ⟨e⟩ := determinant_shortExact
      (splitBundle P p (tailProfile a)) (splitBundle P p a)
      (projectiveTwist P p (a.degree 0))
      (tailInclusion P p a) (headProjection P p a) (tail_head_zero P p a)
      (splitShortComplexSplitting P p a).shortExact
    obtain ⟨h⟩ := exteriorSheaf_one (projectiveTwist P p (a.degree 0)).sheaf
    calc
      projectiveLineDegree P p (determinantLine (splitBundle P p a)) =
          projectiveLineDegree P p (tensorLine
            (determinantLine (splitBundle P p (tailProfile a)))
            (determinantLine (projectiveTwist P p (a.degree 0)))) :=
        projectiveLineDegree_iso P p _ _ e
      _ = projectiveLineDegree P p (determinantLine (splitBundle P p (tailProfile a))) +
          projectiveLineDegree P p (determinantLine (projectiveTwist P p (a.degree 0))) :=
        projectiveLineDegree_tensor P p _ _
      _ = profileDegree (tailProfile a) + a.degree 0 := by
        rw [ih, projectiveLineDegree_iso P p _ (projectiveTwist P p (a.degree 0)) h,
          projectiveTwist_degree]
      _ = profileDegree a := by
        simp only [profileDegree, Fin.sum_univ_succ, tailProfile]
        ring

theorem determinantDegree_of_splitting (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) {r : ℕ} (E : AlgebraicVectorBundle ProjectiveLine r)
    (a : TangentSplittingProfile r) (ha : RealizesSplitting P p E a) :
    projectiveLineDegree P p (determinantLine E) = profileDegree a := by
  obtain ⟨e⟩ := ha
  exact (projectiveLineDegree_iso P p (determinantLine E)
    (determinantLine (splitBundle P p a)) (Exterior.mapIso e r)).trans
      (determinantDegree_split P p a)

/-- Positivity is obtained from actual two-point evaluation at a pair
supplied by very-freeness; the point used to define O(1) may differ. -/
theorem realized_veryFree (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {d : ℕ} (X : SmoothProperComplexVariety d) (f : RationalCurve P X)
    (hf : IsVeryFreeRationalCurve P X (intrinsicTangentBundle X) f)
    (a : TangentSplittingProfile d)
    (ha : RealizesSplitting P p (pullbackBundle f.map (intrinsicTangentBundle X)) a) :
    a.IsVeryFree := by
  obtain ⟨u, v, huv⟩ := hf.1
  obtain ⟨e⟩ := ha
  let h : splitSheaf P p a ≅ splitSheaf P u a :=
    Sigma.mapIso (fun i => (projectiveTwist_independent P p u (a.degree i)).some)
  exact (splitBundle_twoPointEvaluation_iff P u v huv
    (pullbackBundle f.map (intrinsicTangentBundle X)) a ⟨e ≪≫ h⟩).mp (hf.2 u v huv)

theorem profile_reorder_quasiLine (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {n : ℕ} (a : TangentSplittingProfile (2 * n + 1))
    (ha : a.IsVeryFree) (hd : profileDegree a = ((2 * n + 1 : ℕ) : ℤ) + 1) :
    Nonempty (splitSheaf P p a ≅ splitSheaf P p (quasiLineProfile n)) := by
  classical
  obtain ⟨j, hj, _⟩ := nextVeryFreeDegree_forces_quasiLine a ha hd
  let σ : Equiv.Perm (Fin (2 * n + 1)) := Equiv.swap j 0
  have hdegree : ∀ i, (quasiLineProfile n).degree (σ i) = a.degree i := by
    intro i
    by_cases hij : i = j
    · subst i
      simp [σ, quasiLineProfile, hj.1]
    · have hσ : σ i ≠ 0 := by
        intro hz
        apply hij
        apply σ.injective
        simpa [σ] using hz
      have hv : (σ i).val ≠ 0 := by
        intro hz
        apply hσ
        exact Fin.ext hz
      simp [quasiLineProfile, hσ, hv, hj.2 i hij]
  exact ⟨Sigma.whiskerEquiv σ (fun i =>
    eqToIso (congrArg (fun k : ℤ => (projectiveTwist P p k).sheaf) (hdegree i)))⟩

theorem contactConic_splitting (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {n : ℕ} (X : SmoothProperComplexVariety (2 * n + 1))
    (C : IntrinsicContactStructure X) (f : RationalCurve P X)
    (hdegree : IsIntrinsicContactConic P p C f)
    (hfree : IsVeryFreeRationalCurve P X (intrinsicTangentBundle X) f) :
    RealizesSplitting P p (pullbackBundle f.map (intrinsicTangentBundle X))
      (quasiLineProfile n) := by
  let E := pullbackBundle f.map (intrinsicTangentBundle X)
  obtain ⟨a, ha⟩ := birkhoffGrothendieck P p E
  have hpos := realized_veryFree P p X f hfree a ha
  obtain ⟨ep⟩ := exteriorSheaf_pullback f.map (intrinsicTangentBundle X).sheaf (2 * n + 1)
  obtain ⟨et⟩ := tangentDeterminant_anticanonical X
  have hd : profileDegree a = ((2 * n + 1 : ℕ) : ℤ) + 1 := by
    calc
      profileDegree a = projectiveLineDegree P p (determinantLine E) :=
        (determinantDegree_of_splitting P p E a ha).symm
      _ = degreeOnCurve P p f.toParametrizedCurve (anticanonicalLine X) :=
        projectiveLineDegree_iso P p _ _
          (ep.symm ≪≫ (Scheme.Modules.pullback f.map).mapIso et)
      _ = ((n : ℤ) + 1) * degreeOnCurve P p f.toParametrizedCurve C.sequence.line :=
        contact_anticanonicalDegree P p X C f.toParametrizedCurve
      _ = ((2 * n + 1 : ℕ) : ℤ) + 1 := by
        rw [show degreeOnCurve P p f.toParametrizedCurve C.sequence.line = 2 from hdegree]
        push_cast
        ring
  exact ⟨ha.some ≪≫ (profile_reorder_quasiLine P p a hpos hd).some⟩

namespace Duality

open ContactDerivativeIsoProof

/-- The normalized chosen dual map is the actual precomposition map on
local module morphisms.  This fixes the biduality used below. -/
theorem dualMap_comparison {X : Scheme} {E F : OModule X} (f : E ⟶ F) :
    dualMap f ≫ (internalHomGenericIso E (structureModule X)).hom =
      (internalHomGenericIso F (structureModule X)).hom ≫
        HomConstruction.Generic.dualMap (R := X.sheaf) f := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply PresheafOfModules.hom_ext
  intro V
  ext e
  have heval (A : OModule X) (ψ : SectionsOn (dualSheaf A) U.unop)
      (v : SectionsOn A V.unop.left) :
      ((internalHomGenericIso A (structureModule X)).hom.app U.unop ψ).app V v =
        (dualEvaluation A).apply V.unop.left
          ((dualSheaf A).presheaf.map V.unop.hom.op ψ) v := by
    exact IntrinsicHamiltonianInjectivityProof.chosenHom_restricted_apply
      A (structureModule X) U.unop ψ V.unop.left V.unop.hom v
  change ((internalHomGenericIso E (structureModule X)).hom.app U.unop
      ((dualMap f).app U.unop φ)).app V e =
    ((internalHomGenericIso F (structureModule X)).hom.app U.unop φ).app V
      (f.app V.unop.left e)
  calc
    _ = (dualEvaluation E).apply V.unop.left
        ((dualSheaf E).presheaf.map V.unop.hom.op ((dualMap f).app U.unop φ)) e :=
      heval E ((dualMap f).app U.unop φ) e
    _ = (dualEvaluation E).apply V.unop.left
        ((dualMap f).app V.unop.left ((dualSheaf F).presheaf.map V.unop.hom.op φ)) e :=
      congrArg (fun ψ : SectionsOn (dualSheaf E) V.unop.left =>
        (dualEvaluation E).apply V.unop.left ψ e)
          (sheafHom_naturality (dualMap f) V.unop.hom φ)
    _ = (dualEvaluation F).apply V.unop.left
        ((dualSheaf F).presheaf.map V.unop.hom.op φ) (f.app V.unop.left e) :=
      dualMap_evaluate f V.unop.left ((dualSheaf F).presheaf.map V.unop.hom.op φ) e
    _ = _ := (heval F φ (f.app V.unop.left e)).symm

/-- A split monomorphism on the actual dual sheaves makes the original
map of finite locally free sheaves epic.  Mere injectivity of the dual
would not suffice. -/
theorem epi_of_dual_retraction {X : Scheme} {E F : OModule X} {r s : ℕ}
    (hE : IsLocallyFreeOfRank E r) (hF : IsLocallyFreeOfRank F s)
    (f : E ⟶ F) (q : dualSheaf E ⟶ dualSheaf F)
    (hq : dualMap f ≫ q = 𝟙 (dualSheaf F)) : Epi f := by
  let e := internalHomGenericIso E (structureModule X)
  let h := internalHomGenericIso F (structureModule X)
  let q' : HomConstruction.Generic.dual (R := X.sheaf) E ⟶
      HomConstruction.Generic.dual (R := X.sheaf) F := e.inv ≫ q ≫ h.hom
  have hq' : HomConstruction.Generic.dualMap (R := X.sheaf) f ≫ q' = 𝟙 _ := by
    apply (cancel_epi h.hom).1
    dsimp [q']
    rw [← Category.assoc h.hom, ← dualMap_comparison]
    simp [e, h, Category.assoc, hq]
    simpa only [Category.assoc, Category.id_comp] using
      congrArg (fun k : dualSheaf F ⟶ dualSheaf F =>
        k ≫ (internalHomGenericIso F (structureModule X)).hom) hq
  have hs : HomConstruction.Generic.dualMap (R := X.sheaf) q' ≫
      HomConstruction.Generic.dualMap (HomConstruction.Generic.dualMap f) = 𝟙 _ := by
    rw [← HomConstruction.Generic.dualMap_comp, hq', HomConstruction.Generic.dualMap_id]
  letI : Epi (HomConstruction.Generic.dualMap
      (HomConstruction.Generic.dualMap (R := X.sheaf) f)) :=
    (show SplitEpi (HomConstruction.Generic.dualMap
      (HomConstruction.Generic.dualMap (R := X.sheaf) f)) from
        ⟨HomConstruction.Generic.dualMap q', hs⟩).epi
  obtain ⟨u, hu, eu⟩ := hE
  obtain ⟨v, hv, ev⟩ := hF
  letI := hu
  letI := hv
  letI : IsIso (HomConstruction.Generic.bidualMap (R := X.sheaf) E) :=
    HomConstruction.Generic.isIso_bidualMap_of_free_cover E u.X u.coversTop
      (fun _ => Fin r) (fun i => SheafTensor.localBasisTrivialization u eu i)
  letI : IsIso (HomConstruction.Generic.bidualMap (R := X.sheaf) F) :=
    HomConstruction.Generic.isIso_bidualMap_of_free_cover F v.X v.coversTop
      (fun _ => Fin s) (fun i => SheafTensor.localBasisTrivialization v ev i)
  apply (epi_comp_iff_of_isIso f
    (HomConstruction.Generic.bidualMap (R := X.sheaf) F)).mp
  rw [HomConstruction.Generic.bidualMap_naturality]
  change Epi (HomConstruction.Generic.bidualMap (R := X.sheaf) E ≫
    HomConstruction.Generic.dualMap (HomConstruction.Generic.dualMap f))
  infer_instance

end Duality

open LeBrunSalamon.PhaseThirty in
theorem curveDifferential_ne_zero (P : ProjectiveLineOverC) {d : ℕ}
    (X : SmoothProperComplexVariety d) (f : RationalCurve P X) :
    differentialOver (projectiveLineVariety P) X f.map f.overC ≠ 0 := by
  have hΩ : IsLocallyFreeOfRank (cotangentSheaf (f.map ≫ X.structureMap)) 1 := by
    rw [f.overC]
    exact smooth_cotangent_rank P.structureMap 1 (projectiveLineVariety P).smooth
  have hn := Construction.Lines.ContactPositive.tangentMapRaw_ne_zero_of_cotangentMap_ne_zero
    f.map X.structureMap hΩ (nonconstant_complexCurve_differential_ne_zero P X f)
  letI := dualBaseChange_isIso f.map (smooth_cotangent_rank X.structureMap d X.smooth)
  let e : tangentSheaf P.structureMap ≅ tangentSheaf (f.map ≫ X.structureMap) :=
    eqToIso (congrArg tangentSheaf f.overC.symm)
  intro hz
  have h := congrArg (fun k => k ≫ dualBaseChange f.map (cotangentSheaf X.structureMap)) hz
  have he : e.hom ≫ tangentMapRaw f.map X.structureMap = 0 := by
    simpa [differentialOver, e, Category.assoc] using h
  apply hn
  apply (cancel_epi e.hom).1
  simpa only [comp_zero] using he

/-- A nonzero map O(2) into O(2) plus copies of O(1) is split
injective: all lower-degree components vanish, and the remaining
endomorphism of O(2) is invertible. -/
theorem tangent_retraction_of_quasiLine (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) {n : ℕ} {E : OModule ProjectiveLine}
    (e : E ≅ splitSheaf P p (quasiLineProfile n))
    (d : tangentSheaf P.structureMap ⟶ E) (hd : d ≠ 0) :
    ∃ q : E ⟶ tangentSheaf P.structureMap, d ≫ q = 𝟙 _ := by
  classical
  let a := quasiLineProfile n
  let F : Fin (2 * n + 1) → OModule ProjectiveLine :=
    fun i => (projectiveTwist P p (a.degree i)).sheaf
  let t := (projectiveLine_tangent_twist P p).some
  let h : (projectiveTwist P p 2).sheaf ⟶ ∐ F := t.inv ≫ d ≫ e.hom
  have hn : h ≠ 0 := by
    intro hz
    apply hd
    have hh := congrArg (fun k => t.hom ≫ k ≫ e.inv) hz
    simpa [h, Category.assoc] using hh
  have hlow : ∀ i : Fin (2 * n + 1), i ≠ 0 → h ≫ Sigma.π F i = 0 := by
    intro i hi
    have hiv : i.val ≠ 0 := by
      intro hz
      exact hi (Fin.ext hz)
    exact descendingDegree_noHom P p 2 (a.degree i)
      (by simp [a, quasiLineProfile, hi, hiv]) (h ≫ Sigma.π F i)
  let h0 : (projectiveTwist P p 2).sheaf ⟶ (projectiveTwist P p 2).sheaf :=
    h ≫ Sigma.π F 0
  have hn0 : h0 ≠ 0 := by
    intro hz
    apply hn
    have hall : ∀ i, h ≫ Sigma.π F i = 0 := by
      intro i
      by_cases hi : i = 0
      · subst i
        exact hz
      · exact hlow i hi
    calc
      h = h ≫ (∑ i, Sigma.π F i ≫ Sigma.ι F i) := by
        rw [DirectSumGeometry.coproduct_total, Category.comp_id]
      _ = ∑ i, (h ≫ Sigma.π F i) ≫ Sigma.ι F i := by
        simp only [Preadditive.comp_sum, Category.assoc]
      _ = 0 := by simp [hall]
  letI : IsIso h0 := equalDegree_nonzeroHom_isIso P p 2 h0 hn0
  let q0 : (∐ F) ⟶ (projectiveTwist P p 2).sheaf := Sigma.π F 0 ≫ inv h0
  have hq0 : h ≫ q0 = 𝟙 _ := by
    dsimp only [q0]
    rw [← Category.assoc]
    exact IsIso.hom_inv_id h0
  refine ⟨e.hom ≫ q0 ≫ t.inv, ?_⟩
  calc
    d ≫ (e.hom ≫ q0 ≫ t.inv) = t.hom ≫ (h ≫ q0) ≫ t.inv := by
      simp [h, Category.assoc]
    _ = 𝟙 _ := by rw [hq0]; simp

open LeBrunSalamon.PhaseThirty in
theorem contactConic_unramified (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {n : ℕ} (X : SmoothProperComplexVariety (2 * n + 1))
    (C : IntrinsicContactStructure X) (f : RationalCurve P X)
    (hdegree : IsIntrinsicContactConic P p C f)
    (hfree : IsVeryFreeRationalCurve P X (intrinsicTangentBundle X) f) :
    Epi (cotangentMap f.map X.structureMap) := by
  obtain ⟨q, hq⟩ := tangent_retraction_of_quasiLine P p
    (contactConic_splitting P p X C f hdegree hfree).some
    (differentialOver (projectiveLineVariety P) X f.map f.overC)
    (curveDifferential_ne_zero P X f)
  letI := dualBaseChange_isIso f.map
    (smooth_cotangent_rank X.structureMap (2 * n + 1) X.smooth)
  let e : tangentSheaf P.structureMap ≅ tangentSheaf (f.map ≫ X.structureMap) :=
    eqToIso (congrArg tangentSheaf f.overC.symm)
  let b := asIso (dualBaseChange f.map (cotangentSheaf X.structureMap))
  have hraw : tangentMapRaw f.map X.structureMap ≫ (b.inv ≫ q ≫ e.hom) = 𝟙 _ := by
    apply (cancel_epi e.hom).1
    have hh := congrArg (fun k => k ≫ e.hom) hq
    simpa [differentialOver, e, b, Category.assoc] using hh
  apply Duality.epi_of_dual_retraction
    (pullback_locallyFree f.map
      (smooth_cotangent_rank X.structureMap (2 * n + 1) X.smooth))
    (show IsLocallyFreeOfRank (cotangentSheaf (f.map ≫ X.structureMap)) 1 from by
      rw [f.overC]
      exact smooth_cotangent_rank P.structureMap 1 (projectiveLineVariety P).smooth)
    (cotangentMap f.map X.structureMap) (b.inv ≫ q ≫ e.hom)
  exact hraw

end LeBrunSalamon.ConicSplitting

namespace LeBrunSalamon.PhaseThirtyFive

theorem veryFreeContactConic_actualSplitting
    (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P) {n : ℕ}
    (X : SmoothProperComplexVariety (2 * n + 1))
    (C : IntrinsicContactStructure X) (f : RationalCurve P X)
    (hdegree : IsIntrinsicContactConic P p C f)
    (hfree : IsVeryFreeRationalCurve P X (intrinsicTangentBundle X) f) :
    RealizesSplitting P p (pullbackBundle f.map (intrinsicTangentBundle X))
      (quasiLineProfile n) := by
  exact LeBrunSalamon.ConicSplitting.contactConic_splitting P p X C f hdegree hfree

open LeBrunSalamon.PhaseThirty in
theorem veryFreeContactConic_unramified
    (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P) {n : ℕ}
    (X : SmoothProperComplexVariety (2 * n + 1))
    (C : IntrinsicContactStructure X) (f : RationalCurve P X)
    (hdegree : IsIntrinsicContactConic P p C f)
    (hfree : IsVeryFreeRationalCurve P X (intrinsicTangentBundle X) f) :
    Epi (cotangentMap f.map X.structureMap) := by
  exact LeBrunSalamon.ConicSplitting.contactConic_unramified P p X C f hdegree hfree

end LeBrunSalamon.PhaseThirtyFive

namespace LeBrunSalamon.Core

theorem VeryFreeContactConic.splitting (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) {n : ℕ} {X : ContactFanoManifold n}
    (g : VeryFreeContactConic P p X) :
    RealizesSplitting P p
      (pullbackBundle g.curve.map (intrinsicTangentBundle X.variety))
      (LeBrunSalamon.PhaseEighteen.quasiLineProfile n) :=
  veryFreeContactConic_actualSplitting P p X.variety X.contact g.curve
    g.contactDegreeTwo g.veryFree

end LeBrunSalamon.Core

end

import RecompileSections
import LSKunnethDegreeZero

/-!
Actual sheaf frames obtained from affine section coordinates, together with
their normalized pullback and tensor coordinates.  These are translations
through the existing affine equivalence and sheaf tensor construction, not
additional published inputs.  This candidate is kept outside source/ until
native checking.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 300000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.Skeleton

namespace LeBrunSalamon.AffineFrameProof

theorem spec_isIso_of_appTop_bijective {R : CommRingCat}
    {E G : OModule (Spec R)} [E.IsQuasicoherent] [G.IsQuasicoherent]
    (p : E ⟶ G) (hp : Function.Bijective (p.app ⊤)) : IsIso p := by
  let Q := SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf
  let E' : Q.FullSubcategory := ⟨E, inferInstance⟩
  let G' : Q.FullSubcategory := ⟨G, inferInstance⟩
  let p' : E' ⟶ G' := ObjectProperty.homMk p
  haveI : IsIso ((tildeEquiv (R := R)).inverse.map p') := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    exact hp
  haveI : IsIso p' := isIso_of_reflects_iso p' (tildeEquiv (R := R)).inverse
  change IsIso (Q.ι.map p')
  infer_instance

theorem affine_isIso_of_appTop_bijective {Y : Scheme} [IsAffine Y]
    {E G : OModule Y} [E.IsQuasicoherent] [G.IsQuasicoherent]
    (p : E ⟶ G) (hp : Function.Bijective (p.app ⊤)) : IsIso p := by
  let e := Y.isoSpec
  let A := Scheme.Modules.restrictFunctor e.inv
  let B := Scheme.Modules.restrictFunctor e.hom
  let q := A.map p
  have hq : Function.Bijective (q.app ⊤) := by
    change Function.Bijective (p.app (e.inv ''ᵁ ⊤))
    have htop : e.inv ''ᵁ ⊤ = ⊤ :=
      (Scheme.Hom.image_top_eq_opensRange e.inv).trans
        (Scheme.Hom.opensRange_of_isIso e.inv)
    erw [htop]
    exact hp
  letI : IsIso q := spec_isIso_of_appTop_bijective q hq
  let c : A ⋙ B ≅ 𝟭 (OModule Y) :=
    (Scheme.Modules.restrictFunctorComp e.hom e.inv).symm ≪≫
      Scheme.Modules.restrictFunctorCongr e.hom_inv_id ≪≫
        Scheme.Modules.restrictFunctorId
  have heq : p = c.inv.app E ≫ B.map q ≫ c.hom.app G := by
    have h := c.hom.naturality p
    simpa only [q, Functor.id_obj, Functor.id_map, Functor.comp_map,
      ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp] using
        congrArg (fun a => c.inv.app E ≫ a) h.symm
  rw [heq]
  infer_instance

private theorem over_eq_terminal {Y : Scheme} {U : Y.Opens}
    (W : Over U) (h : W.left = U) : W = Over.mk (𝟙 U) := by
  obtain ⟨V, i, rfl⟩ := Over.mk_surjective W
  change V = U at h
  subst V
  exact congrArg (fun i : U ⟶ U => Over.mk i) (Subsingleton.elim _ _)

theorem affine_over_isIso_of_bijective {Y : Scheme} {E G : OModule Y}
    [E.IsQuasicoherent] [G.IsQuasicoherent] (U : Y.Opens) (hU : IsAffineOpen U)
    (p : E.over U ⟶ G.over U)
    (hp : Function.Bijective (p.val.app (op (Over.mk (𝟙 U))))) : IsIso p := by
  let A := (Scheme.Modules.overEquiv U).functor
  letI : IsAffine U.toScheme := hU
  letI : (A.obj (E.over U)).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).prop_of_iso
      ((Scheme.Modules.overFunctorEquiv U).app E).symm inferInstance
  letI : (A.obj (G.over U)).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).prop_of_iso
      ((Scheme.Modules.overFunctorEquiv U).app G).symm inferInstance
  have htop : U.overEquivalence.inverse.obj ⊤ = Over.mk (𝟙 U) := by
    apply over_eq_terminal
    change U.ι ''ᵁ ⊤ = U
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι]
  have hAp : Function.Bijective ((A.map p).app ⊤) := by
    change Function.Bijective (p.val.app (op (U.overEquivalence.inverse.obj ⊤)))
    rw [htop]
    exact hp
  letI : IsIso (A.map p) := affine_isIso_of_appTop_bijective (A.map p) hAp
  exact isIso_of_reflects_iso p A

/-- The actual local unit morphism determined by the given coordinate map. -/
def frameMap {Y : Scheme} {E : OModule Y} (U : Y.Opens)
    (c : SectionsOn E U ≃ₗ[RingSections Y U] RingSections Y U) :
    (structureModule Y).over U ⟶ E.over U :=
  (SheafModuleLocal.unitOverHomEquiv E U).symm (c.symm 1)

theorem frameMap_apply {Y : Scheme} {E : OModule Y} (U : Y.Opens)
    (c : SectionsOn E U ≃ₗ[RingSections Y U] RingSections Y U)
    (a : RingSections Y U) :
    (frameMap U c).val.app (op (Over.mk (𝟙 U))) a = c.symm a := by
  have h1 : (frameMap U c).val.app (op (Over.mk (𝟙 U)))
      (1 : RingSections Y U) = c.symm 1 :=
    (SheafModuleLocal.unitOverHomEquiv E U).apply_symm_apply _
  calc
    _ = a • (frameMap U c).val.app (op (Over.mk (𝟙 U)))
        (1 : RingSections Y U) := by
      simpa only [smul_eq_mul, mul_one] using
        ((frameMap U c).val.app (op (Over.mk (𝟙 U)))).hom.map_smul a
          (1 : RingSections Y U)
    _ = c.symm a := by
      rw [h1, ← c.symm.map_smul]
      simp only [smul_eq_mul, mul_one]

theorem frameMap_isIso {Y : Scheme} {E : OModule Y} [E.IsQuasicoherent]
    (U : Y.Opens) (hU : IsAffineOpen U)
    (c : SectionsOn E U ≃ₗ[RingSections Y U] RingSections Y U) :
    IsIso (frameMap U c) := by
  letI : (structureModule Y).IsQuasicoherent :=
    KunnethDegreeZero.quasicoherent_of_locallyFreeRank (structureModule_rank Y)
  apply affine_over_isIso_of_bijective U hU
  constructor
  · intro a b hab
    exact c.symm.injective ((frameMap_apply U c a).symm.trans
      (hab.trans (frameMap_apply U c b)))
  · intro b
    obtain ⟨a, ha⟩ := c.symm.surjective b
    exact ⟨a, (frameMap_apply U c a).trans ha⟩

/-- An affine module-coordinate equivalence gives the corresponding genuine
sheaf frame, with no new choice of its generator. -/
def frame {Y : Scheme} {E : OModule Y} [E.IsQuasicoherent]
    (U : Y.Opens) (hU : IsAffineOpen U)
    (c : SectionsOn E U ≃ₗ[RingSections Y U] RingSections Y U) :
    LocalFrames.OverFrame E U := by
  letI := frameMap_isIso U hU c
  exact asIso (frameMap U c)

theorem frame_coordinates {Y : Scheme} {E : OModule Y} [E.IsQuasicoherent]
    (U : Y.Opens) (hU : IsAffineOpen U)
    (c : SectionsOn E U ≃ₗ[RingSections Y U] RingSections Y U)
    (x : SectionsOn E U) :
    LocalFrames.coordinates (frame U hU c) x = c x := by
  apply c.symm.injective
  rw [c.symm_apply_apply]
  rw [← frameMap_apply U c]
  exact (LocalFrames.coordinates (frame U hU c)).symm_apply_apply x

/-- Pullback of an actual local morphism through the normalized adjunction. -/
def pullOverHom {Y Z : Scheme} (f : Z ⟶ Y) (U : Y.Opens)
    {E G : OModule Y} (p : E.over U ⟶ G.over U) :
    (pullbackModule f E).over (f ⁻¹ᵁ U) ⟶ (pullbackModule f G).over (f ⁻¹ᵁ U) :=
  (PullbackPairProof.localPullbackHomEquiv f E (pullbackModule f G) U).symm
    (p ≫ ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app G).over U)

theorem pullOverHom_unit {Y Z : Scheme} (f : Z ⟶ Y) (U : Y.Opens)
    {E G : OModule Y} (p : E.over U ⟶ G.over U)
    (W : Over U) (a : SectionsOn E W.left) :
    (pullOverHom f U p).val.app
        (op ((Over.post (TopologicalSpace.Opens.map f.base)).obj W))
        (pullLocalSection f E W.left a) =
      pullLocalSection f G W.left (p.val.app (op W) a) := by
  have h := (PullbackPairProof.localPullbackHomEquiv f E (pullbackModule f G) U).apply_symm_apply
    (p ≫ ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app G).over U)
  rw [PullbackPairProof.localPullbackHomEquiv_eq_unitPrecompose] at h
  exact congrArg (fun q : E.over U ⟶
    ((Scheme.Modules.pushforward f).obj (pullbackModule f G)).over U =>
      q.val.app (op W) a) h

theorem pullOverHom_unit_top {Y Z : Scheme} (f : Z ⟶ Y) (U : Y.Opens)
    {E G : OModule Y} (p : E.over U ⟶ G.over U) (a : SectionsOn E U) :
    (pullOverHom f U p).val.app (op (Over.mk (𝟙 (f ⁻¹ᵁ U))))
      (pullLocalSection f E U a) =
        pullLocalSection f G U (p.val.app (op (Over.mk (𝟙 U))) a) := by
  have h := pullOverHom_unit f U p (Over.mk (𝟙 U)) a
  change (pullOverHom f U p).val.app
    (op (Over.mk ((TopologicalSpace.Opens.map f.base).map (𝟙 U))))
      (pullLocalSection f E U a) = _ at h
  have hid : (TopologicalSpace.Opens.map f.base).map (𝟙 U) = 𝟙 (f ⁻¹ᵁ U) :=
    (TopologicalSpace.Opens.map f.base).map_id U
  erw [hid] at h
  exact h

theorem pullOverHom_id {Y Z : Scheme} (f : Z ⟶ Y) (U : Y.Opens)
    (E : OModule Y) : pullOverHom f U (𝟙 (E.over U)) = 𝟙 _ := by
  apply (PullbackPairProof.localUnitPrecompose_bijective f E (pullbackModule f E) U).injective
  apply SheafOfModules.hom_ext
  ext W a
  change (pullOverHom f U (𝟙 (E.over U))).val.app
    (op ((Over.post (TopologicalSpace.Opens.map f.base)).obj W.unop))
    (pullLocalSection f E W.unop.left a) = pullLocalSection f E W.unop.left a
  rw [pullOverHom_unit]
  rfl

theorem pullOverHom_comp {Y Z : Scheme} (f : Z ⟶ Y) (U : Y.Opens)
    {E G H : OModule Y} (p : E.over U ⟶ G.over U) (q : G.over U ⟶ H.over U) :
    pullOverHom f U (p ≫ q) = pullOverHom f U p ≫ pullOverHom f U q := by
  apply (PullbackPairProof.localUnitPrecompose_bijective f E (pullbackModule f H) U).injective
  apply SheafOfModules.hom_ext
  ext W a
  change (pullOverHom f U (p ≫ q)).val.app
    (op ((Over.post (TopologicalSpace.Opens.map f.base)).obj W.unop))
    (pullLocalSection f E W.unop.left a) =
      (pullOverHom f U q).val.app
        (op ((Over.post (TopologicalSpace.Opens.map f.base)).obj W.unop))
        ((pullOverHom f U p).val.app
          (op ((Over.post (TopologicalSpace.Opens.map f.base)).obj W.unop))
          (pullLocalSection f E W.unop.left a))
  rw [pullOverHom_unit, pullOverHom_unit, pullOverHom_unit]
  rfl

def pullOverIso {Y Z : Scheme} (f : Z ⟶ Y) (U : Y.Opens)
    {E G : OModule Y} (e : E.over U ≅ G.over U) :
    (pullbackModule f E).over (f ⁻¹ᵁ U) ≅ (pullbackModule f G).over (f ⁻¹ᵁ U) where
  hom := pullOverHom f U e.hom
  inv := pullOverHom f U e.inv
  hom_inv_id := by rw [← pullOverHom_comp, e.hom_inv_id, pullOverHom_id]
  inv_hom_id := by rw [← pullOverHom_comp, e.inv_hom_id, pullOverHom_id]

theorem unitPullbackMap_local {Y Z : Scheme} (f : Z ⟶ Y)
    (U : Y.Opens) (a : RingSections Y U) :
    (unitPullbackMap f).app (f ⁻¹ᵁ U)
      (pullLocalSection f (structureModule Y) U a) = f.app U a := by
  exact congrArg (fun q : structureModule Y ⟶
    (Scheme.Modules.pushforward f).obj (structureModule Z) => q.app U a)
      (unitPullbackMap_adjoint f)

/-- A pulled frame includes the actual unit pullback comparison. -/
def pullFrame {Y Z : Scheme} (f : Z ⟶ Y) {E : OModule Y} {U : Y.Opens}
    (e : LocalFrames.OverFrame E U) :
    LocalFrames.OverFrame (pullbackModule f E) (f ⁻¹ᵁ U) :=
  (SheafOfModules.overFunctor Z.ringCatSheaf (f ⁻¹ᵁ U)).mapIso
    (unitPullbackIso f).symm ≪≫ pullOverIso f U e

theorem pullFrame_coordinates {Y Z : Scheme} (f : Z ⟶ Y)
    {E : OModule Y} {U : Y.Opens} (e : LocalFrames.OverFrame E U)
    (x : SectionsOn E U) :
    LocalFrames.coordinates (pullFrame f e) (pullLocalSection f E U x) =
      f.app U (LocalFrames.coordinates e x) := by
  change (unitPullbackMap f).app (f ⁻¹ᵁ U)
    ((pullOverHom f U e.inv).val.app (op (Over.mk (𝟙 (f ⁻¹ᵁ U))))
      (pullLocalSection f E U x)) = _
  rw [pullOverHom_unit_top, unitPullbackMap_local]
  rfl

theorem pullLocalSection_eq_zero_iff {Y Z : Scheme} (f : Z ⟶ Y)
    {E : OModule Y} {U : Y.Opens} (e : LocalFrames.OverFrame E U)
    (x : SectionsOn E U) :
    pullLocalSection f E U x = 0 ↔ f.app U (LocalFrames.coordinates e x) = 0 := by
  rw [← pullFrame_coordinates f e x]
  exact (LocalFrames.coordinates (pullFrame f e)).map_eq_zero_iff.symm

/-- The normalized pullback section has the expected value on every inverse
image open, not only on global sections. -/
theorem pullSection_local {Y Z : Scheme} (f : Z ⟶ Y)
    {E : OModule Y} (a : AlgebraicSection E) (U : Y.Opens) :
    Scheme.Modules.Hom.app (pullSection f a) (f ⁻¹ᵁ U)
      (1 : RingSections Z (f ⁻¹ᵁ U)) =
      pullLocalSection f E U (Scheme.Modules.Hom.app a U (1 : RingSections Y U)) := by
  have h := congrArg (fun q => q.app U (1 : RingSections Y U))
    (pullSection_adjoint f a)
  change Scheme.Modules.Hom.app (pullSection f a) (f ⁻¹ᵁ U)
    (f.app U (1 : RingSections Y U)) =
    pullLocalSection f E U (Scheme.Modules.Hom.app a U (1 : RingSections Y U)) at h
  rw [map_one] at h
  exact h

theorem overSection_eq_zero_iff {Y : Scheme} {E : OModule Y}
    (a : AlgebraicSection E) (U : Y.Opens) :
    a.over U = 0 ↔ Scheme.Modules.Hom.app a U (1 : RingSections Y U) = 0 := by
  constructor
  · intro h
    exact congrArg (fun q : (structureModule Y).over U ⟶ E.over U =>
      q.val.app (op (Over.mk (𝟙 U))) (1 : RingSections Y U)) h
  · intro h
    apply (SheafModuleLocal.unitOverHomEquiv (R := Y.ringCatSheaf) E U).injective
    exact h

theorem pullback_open_eq_zero_iff_over {Y : Scheme} {E G : OModule Y}
    (U : Y.Opens) (a : E ⟶ G) :
    (Scheme.Modules.pullback U.ι).map a = 0 ↔ a.over U = 0 := by
  constructor
  · exact DominantSectionInjectivityProof.over_zero_of_pullback_zero U a
  · intro h
    let A := (Scheme.Modules.overEquiv U).functor
    let e := Scheme.Modules.overFunctorEquiv U ≪≫
      Scheme.Modules.restrictFunctorIsoPullback U.ι
    have hn := e.hom.naturality a
    change A.map (a.over U) ≫ e.hom.app G =
      e.hom.app E ≫ (Scheme.Modules.pullback U.ι).map a at hn
    rw [h, Functor.map_zero, zero_comp] at hn
    apply (cancel_epi (e.hom.app E)).mp
    simpa only [comp_zero] using hn.symm

theorem raw_over_eq_zero_iff_pullSection {Y Z : Scheme} (f : Z ⟶ Y)
    {E : OModule Y} (a : AlgebraicSection E) (V : Z.Opens) :
    ((Scheme.Modules.pullback f).map a).over V = 0 ↔
      (pullSection f a).over V = 0 := by
  let A := SheafOfModules.overFunctor Z.ringCatSheaf V
  constructor
  · intro h
    change A.map (pullSection f a) = 0
    change A.map ((unitPullbackIso f).inv ≫ (Scheme.Modules.pullback f).map a) = 0
    rw [Functor.map_comp]
    change _ ≫ ((Scheme.Modules.pullback f).map a).over V = 0
    rw [h, comp_zero]
  · intro h
    change A.map ((Scheme.Modules.pullback f).map a) = 0
    rw [← unitPullbackMap_pullSection, Functor.map_comp]
    change _ ≫ (pullSection f a).over V = 0
    rw [h, comp_zero]

/-- Zero of the actual pullback to an inverse-image open is detected by the
actual structure-sheaf map applied to the specified frame coefficient. -/
theorem pullbackOnOpen_eq_zero_iff_coefficient {Y Z : Scheme} (f : Z ⟶ Y)
    {E : OModule Y} {U : Y.Opens} (e : LocalFrames.OverFrame E U)
    (a : AlgebraicSection E) :
    (Scheme.Modules.pullback ((f ⁻¹ᵁ U).ι ≫ f)).map a = 0 ↔
      f.app U (LocalFrames.coordinates e
        (Scheme.Modules.Hom.app a U (1 : RingSections Y U))) = 0 := by
  rw [LeBrunSalamon.PhaseFourteen.SliceRestrictionProof.pullback_comp_zero_iff]
  rw [pullback_open_eq_zero_iff_over, raw_over_eq_zero_iff_pullSection,
    overSection_eq_zero_iff, pullSection_local]
  exact pullLocalSection_eq_zero_iff f e (Scheme.Modules.Hom.app a U (1 : RingSections Y U))

/-- The tensor restriction comparison preserves the original pure pairing. -/
theorem tensorOverIso_hom_pair {X : Scheme} (U : X.Opens) (E F : OModule X)
    (x : SectionsOn E U) (y : SectionsOn F U) :
    (SheafTensor.tensorOverIso U E F).hom.val.app (op (Over.mk (𝟙 U)))
      (LocalFrames.Generic.tensorPair (R := X.sheaf) E F U x y) =
        LocalFrames.Generic.tensorPair (R := X.sheaf.over U)
          (E.over U) (F.over U) (Over.mk (𝟙 U)) x y := by
  erw [← SheafTensor.tensorOverIso_inv_pair U E F (Over.mk (𝟙 U)) x y]
  exact congrArg (fun a => a.val.app (op (Over.mk (𝟙 U)))
    (LocalFrames.Generic.tensorPair (R := X.sheaf.over U)
      (E.over U) (F.over U) (Over.mk (𝟙 U)) x y))
      (SheafTensor.tensorOverIso U E F).inv_hom_id

theorem tensorFrame_coordinates_pair {X : Scheme} {E F : OModule X} {U : X.Opens}
    (e : LocalFrames.OverFrame E U) (f : LocalFrames.OverFrame F U)
    (x : SectionsOn E U) (y : SectionsOn F U) :
    LocalFrames.coordinates (LocalFrames.tensorFrame e f)
      ((tensorPresentation E F).pair.apply U x y) =
        LocalFrames.coordinates e x * LocalFrames.coordinates f y := by
  change (LocalFrames.Generic.tensorFrame (R := X.sheaf.over U) e f).inv.val.app
    (op (Over.mk (𝟙 U)))
    ((SheafTensor.tensorOverIso U E F).hom.val.app (op (Over.mk (𝟙 U)))
      (LocalFrames.Generic.tensorPair (R := X.sheaf) E F U x y)) = _
  rw [tensorOverIso_hom_pair]
  exact LocalFrames.Generic.tensorFrame_coordinates_pair (R := X.sheaf.over U)
    e f (Over.mk (𝟙 U)) x y

end LeBrunSalamon.AffineFrameProof

end

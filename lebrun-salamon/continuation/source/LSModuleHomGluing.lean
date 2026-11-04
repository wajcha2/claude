import RecompileBasePart07

/-! Actual module maps can be reconstructed from compatible maps on arbitrary
isomorphic presentations of the opens of a cover. All equivalences below are
built from the existing restriction and pullback functors. No new admission. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseTwentyFive

namespace LeBrunSalamon.ModuleHomGluing

variable {C D : Type*} [Category C] [Category D]

def isoHomEquiv {A B A' B' : C} (e : A ≅ A') (f : B ≅ B') :
    (A ⟶ B) ≃ (A' ⟶ B') where
  toFun a := e.inv ≫ a ≫ f.hom
  invFun a := e.hom ≫ a ≫ f.inv
  left_inv a := by simp [Category.assoc]
  right_inv a := by simp [Category.assoc]

def fullyFaithfulHomEquiv (F : C ⥤ D) [F.Full] [F.Faithful] (A B : C) :
    (A ⟶ B) ≃ (F.obj A ⟶ F.obj B) where
  toFun := F.map
  invFun := F.preimage
  left_inv a := by simp
  right_inv a := by simp

@[simp] theorem isoHomEquiv_naturality {F G : C ⥤ D} (e : F ≅ G)
    {A B : C} (f : A ⟶ B) :
    isoHomEquiv (e.app A) (e.app B) (F.map f) = G.map f := by
  change (e.app A).inv ≫ F.map f ≫ (e.app B).hom = _
  exact NatIso.naturality_2 e.symm f

/-- The actual over-site category and the module category of its open subscheme
have the same morphisms, with the standard comparison components retained. -/
def openHomEquiv {X : Scheme} (E F : OModule X) (U : X.Opens) :
    (E.over U ⟶ F.over U) ≃ (E.restrict U.ι ⟶ F.restrict U.ι) :=
  (fullyFaithfulHomEquiv (Scheme.Modules.overEquiv U).functor _ _).trans
    (isoHomEquiv ((Scheme.Modules.overFunctorEquiv U).app E)
      ((Scheme.Modules.overFunctorEquiv U).app F))

/-- Pullback to a specified scheme isomorphic to an open retains precisely
all local module maps. This equivalence fixes the chart transport once. -/
def chartHomEquiv {X A : Scheme} (E F : OModule X) (U : X.Opens)
    (c : A ≅ U.toScheme) :
    (E.over U ⟶ F.over U) ≃
      (pullbackModule (c.hom ≫ U.ι) E ⟶ pullbackModule (c.hom ≫ U.ι) F) :=
  (openHomEquiv E F U).trans
    ((fullyFaithfulHomEquiv (ModuleGluing.restrictEquivalence c).functor _ _).trans
      ((isoHomEquiv ((Scheme.Modules.restrictFunctorComp c.hom U.ι).app E).symm
        ((Scheme.Modules.restrictFunctorComp c.hom U.ι).app F).symm).trans
          (isoHomEquiv ((Scheme.Modules.restrictFunctorIsoPullback (c.hom ≫ U.ι)).app E)
            ((Scheme.Modules.restrictFunctorIsoPullback (c.hom ≫ U.ι)).app F))))

/-- Restriction of a genuine global map has its original actual pullback. -/
theorem chartHomEquiv_global {X A : Scheme} (E F : OModule X) (U : X.Opens)
    (c : A ≅ U.toScheme) (f : E ⟶ F) :
    chartHomEquiv E F U c ((SheafOfModules.overFunctor X.ringCatSheaf U).map f) =
      (Scheme.Modules.pullback (c.hom ≫ U.ι)).map f := by
  have hopen : openHomEquiv E F U
      ((SheafOfModules.overFunctor X.ringCatSheaf U).map f) =
        (Scheme.Modules.restrictFunctor U.ι).map f :=
    isoHomEquiv_naturality (Scheme.Modules.overFunctorEquiv U) f
  change isoHomEquiv _ _ (isoHomEquiv _ _
    ((Scheme.Modules.restrictFunctor c.hom).map
      (openHomEquiv E F U ((SheafOfModules.overFunctor X.ringCatSheaf U).map f)))) = _
  rw [hopen]
  change isoHomEquiv _ _ (isoHomEquiv
    ((Scheme.Modules.restrictFunctorComp c.hom U.ι).symm.app E)
    ((Scheme.Modules.restrictFunctorComp c.hom U.ι).symm.app F)
    ((Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.restrictFunctor c.hom).map f)) = _
  rw [isoHomEquiv_naturality, isoHomEquiv_naturality]

/-- Canonical restriction of an actual map on an over site. -/
def restrictOverHom {X : Scheme} {E F : OModule X} {U V : X.Opens}
    (i : V ⟶ U) (f : E.over U ⟶ F.over U) : E.over V ⟶ F.over V :=
  ((SheafOfModules.overFunctorMap X.ringCatSheaf i).app E).inv ≫
    (SheafOfModules.overMap X.ringCatSheaf i).map f ≫
      ((SheafOfModules.overFunctorMap X.ringCatSheaf i).app F).hom

/-- The same restriction expressed on the actual smaller open subscheme. -/
def restrictOpenHom {X : Scheme} {E F : OModule X} {U V : X.Opens}
    (i : V ⟶ U) (f : E.restrict U.ι ⟶ F.restrict U.ι) :
    E.restrict V.ι ⟶ F.restrict V.ι :=
  (ModuleGluing.subopenComparison E i).hom ≫
    (Scheme.Modules.restrictFunctor (X.homOfLE (leOfHom i))).map f ≫
      (ModuleGluing.subopenComparison F i).inv

def restrictLocalHom {X U V : Scheme} {E F : OModule X}
    (f : V ⟶ U) (j : U ⟶ X) [IsOpenImmersion f] [IsOpenImmersion j]
    (q : E.restrict j ⟶ F.restrict j) :
    E.restrict (f ≫ j) ⟶ F.restrict (f ≫ j) :=
  (Scheme.Modules.restrictFunctorComp f j).hom.app E ≫
    (Scheme.Modules.restrictFunctor f).map q ≫
      (Scheme.Modules.restrictFunctorComp f j).inv.app F

def transportRestrictHom {X U : Scheme} {E F : OModule X}
    {i j : U ⟶ X} [IsOpenImmersion i] [IsOpenImmersion j] (h : i = j)
    (q : E.restrict i ⟶ F.restrict i) : E.restrict j ⟶ F.restrict j :=
  (Scheme.Modules.restrictFunctorCongr h).inv.app E ≫ q ≫
    (Scheme.Modules.restrictFunctorCongr h).hom.app F

@[simp] theorem transportRestrictHom_rfl {X U : Scheme} {E F : OModule X}
    (i : U ⟶ X) [IsOpenImmersion i] (q : E.restrict i ⟶ F.restrict i) :
    transportRestrictHom (rfl : i = i) q = q := by
  simp [transportRestrictHom, ModuleGluing.restrictFunctorCongr_rfl]

def restrictHomAlong {X U V : Scheme} {E F : OModule X}
    (f : V ⟶ U) (j : U ⟶ X) (i : V ⟶ X)
    [IsOpenImmersion f] [IsOpenImmersion j] [IsOpenImmersion i]
    (h : f ≫ j = i) (q : E.restrict j ⟶ F.restrict j) :
    E.restrict i ⟶ F.restrict i :=
  transportRestrictHom h (restrictLocalHom f j q)

theorem restrictLocalHom_comp {X A B C : Scheme} {E F : OModule X}
    (g : C ⟶ B) (f : B ⟶ A) (j : A ⟶ X)
    [IsOpenImmersion g] [IsOpenImmersion f] [IsOpenImmersion j]
    (q : E.restrict j ⟶ F.restrict j) :
    transportRestrictHom (Category.assoc g f j) (restrictLocalHom (g ≫ f) j q) =
      restrictLocalHom g (f ≫ j) (restrictLocalHom f j q) := by
  have hE := ModuleGluing.restrictionComp_coherence E g f j
  have hF := ModuleGluing.restrictionComp_coherence F g f j
  have hn := (Scheme.Modules.restrictFunctorComp g f).hom.naturality q
  simp only [transportRestrictHom, restrictLocalHom, Functor.map_comp, Category.assoc]
  apply (cancel_epi ((Scheme.Modules.restrictFunctorCongr
    (Category.assoc g f j)).hom.app E)).mp
  apply (cancel_mono ((Scheme.Modules.restrictFunctorComp g (f ≫ j)).hom.app F ≫
    (Scheme.Modules.restrictFunctor g).map
      ((Scheme.Modules.restrictFunctorComp f j).hom.app F))).mp
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app_assoc,
    ← Functor.map_comp, Iso.inv_hom_id_app] at *
  rw [hF]
  simp only [Iso.inv_hom_id_app_assoc, Functor.map_comp]
  rw [(Scheme.Modules.restrictFunctor g).map_id
    ((Scheme.Modules.restrictFunctor j ⋙ Scheme.Modules.restrictFunctor f).obj F)]
  simp only [Functor.comp_obj, Scheme.Modules.restrict, Category.comp_id]
  have hE' := congrArg (fun a => a ≫
    (Scheme.Modules.restrictFunctor g).map
      ((Scheme.Modules.restrictFunctor f).map q)) hE
  simp only [Category.assoc] at hE'
  rw [hE']
  simpa only [Category.assoc, Functor.comp_map, Functor.comp_obj,
    Scheme.Modules.restrict] using congrArg
    (fun a => (Scheme.Modules.restrictFunctorComp (g ≫ f) j).hom.app E ≫ a) hn

theorem restrictHomAlong_comp {X A B C : Scheme} {E F : OModule X}
    (f : B ⟶ A) (j : A ⟶ X) (i : B ⟶ X)
    (g : C ⟶ B) (k : C ⟶ X)
    [IsOpenImmersion f] [IsOpenImmersion j] [IsOpenImmersion i]
    [IsOpenImmersion g] [IsOpenImmersion k]
    (h : f ≫ j = i) (h' : g ≫ i = k) (q : E.restrict j ⟶ F.restrict j) :
    restrictHomAlong g i k h' (restrictHomAlong f j i h q) =
      restrictHomAlong (g ≫ f) j k (by rw [Category.assoc, h, h']) q := by
  subst i
  subst k
  simpa only [restrictHomAlong, transportRestrictHom_rfl] using
    (restrictLocalHom_comp g f j q).symm

theorem restrictHomAlong_congr {X U V : Scheme} {E F : OModule X}
    {f g : V ⟶ U} [IsOpenImmersion f] [IsOpenImmersion g] (hfg : f = g)
    (j : U ⟶ X) (i : V ⟶ X) [IsOpenImmersion j] [IsOpenImmersion i]
    (hf : f ≫ j = i) (hg : g ≫ j = i) (q : E.restrict j ⟶ F.restrict j) :
    restrictHomAlong f j i hf q = restrictHomAlong g j i hg q := by
  subst g
  rfl

theorem restrictOpenHom_eq_along {X : Scheme} {E F : OModule X}
    {U V : X.Opens} (i : V ⟶ U) (q : E.restrict U.ι ⟶ F.restrict U.ι) :
    restrictOpenHom i q = restrictHomAlong (X.homOfLE (leOfHom i)) U.ι V.ι
      (X.homOfLE_ι (leOfHom i)) q := by
  simp [restrictOpenHom, ModuleGluing.subopenComparison, restrictHomAlong,
    transportRestrictHom, restrictLocalHom, Category.assoc]

/-- A named chart map uses equality transport before the restriction/pullback
comparison, so subsequent restriction is governed by the proved coherence. -/
def chartHomAlongEquiv {X A : Scheme} (E F : OModule X) (U : X.Opens)
    (c : A ≅ U.toScheme) (j : A ⟶ X) [IsOpenImmersion j]
    (h : c.hom ≫ U.ι = j) :
    (E.over U ⟶ F.over U) ≃ (pullbackModule j E ⟶ pullbackModule j F) :=
  (openHomEquiv E F U).trans
    ((fullyFaithfulHomEquiv (ModuleGluing.restrictEquivalence c).functor _ _).trans
      ((isoHomEquiv ((Scheme.Modules.restrictFunctorComp c.hom U.ι).app E).symm
        ((Scheme.Modules.restrictFunctorComp c.hom U.ι).app F).symm).trans
        ((isoHomEquiv ((Scheme.Modules.restrictFunctorCongr h).app E)
          ((Scheme.Modules.restrictFunctorCongr h).app F)).trans
          (isoHomEquiv ((Scheme.Modules.restrictFunctorIsoPullback j).app E)
            ((Scheme.Modules.restrictFunctorIsoPullback j).app F)))))

theorem chartHomAlongEquiv_global {X A : Scheme} (E F : OModule X) (U : X.Opens)
    (c : A ≅ U.toScheme) (j : A ⟶ X) [IsOpenImmersion j]
    (h : c.hom ≫ U.ι = j) (q : E ⟶ F) :
    chartHomAlongEquiv E F U c j h
      ((SheafOfModules.overFunctor X.ringCatSheaf U).map q) =
        (Scheme.Modules.pullback j).map q := by
  have hopen : openHomEquiv E F U
      ((SheafOfModules.overFunctor X.ringCatSheaf U).map q) =
        (Scheme.Modules.restrictFunctor U.ι).map q :=
    isoHomEquiv_naturality (Scheme.Modules.overFunctorEquiv U) q
  change isoHomEquiv _ _ (isoHomEquiv _ _ (isoHomEquiv _ _
    ((Scheme.Modules.restrictFunctor c.hom).map
      (openHomEquiv E F U ((SheafOfModules.overFunctor X.ringCatSheaf U).map q))))) = _
  rw [hopen]
  change isoHomEquiv _ _ (isoHomEquiv _ _ (isoHomEquiv
    ((Scheme.Modules.restrictFunctorComp c.hom U.ι).symm.app E)
    ((Scheme.Modules.restrictFunctorComp c.hom U.ι).symm.app F)
    ((Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.restrictFunctor c.hom).map q))) = _
  rw [isoHomEquiv_naturality, isoHomEquiv_naturality, isoHomEquiv_naturality]

/-- Passing between the slice site and the open subscheme commutes with
restriction of actual morphisms, including the canonical comparison maps. -/
theorem openHomEquiv_restrict {X : Scheme} {E F : OModule X} {U V : X.Opens}
    (i : V ⟶ U) (f : E.over U ⟶ F.over U) :
    openHomEquiv E F V (restrictOverHom i f) =
      restrictOpenHom i (openHomEquiv E F U f) := by
  let A := (Scheme.Modules.overEquiv V).functor
  let B := (Scheme.Modules.overEquiv U).functor
  let T := Scheme.Modules.restrictFunctor (X.homOfLE (leOfHom i))
  let dE := ((SheafOfModules.overFunctorMap X.ringCatSheaf i).app E).symm
  let dF := ((SheafOfModules.overFunctorMap X.ringCatSheaf i).app F).symm
  let bE := (Scheme.Modules.overMapCompOverEquiv i).app (E.over U)
  let bF := (Scheme.Modules.overMapCompOverEquiv i).app (F.over U)
  let aE := (Scheme.Modules.overFunctorEquiv U).app E
  let aF := (Scheme.Modules.overFunctorEquiv U).app F
  have hn : A.map ((SheafOfModules.overMap X.ringCatSheaf i).map f) =
      bE.hom ≫ T.map (B.map f) ≫ bF.inv := by
    exact (NatIso.naturality_2 (Scheme.Modules.overMapCompOverEquiv i) f).symm
  have hm : A.map (restrictOverHom i f) =
      (A.mapIso dE ≪≫ bE ≪≫ T.mapIso aE).hom ≫
        T.map (openHomEquiv E F U f) ≫
          (A.mapIso dF ≪≫ bF ≪≫ T.mapIso aF).inv := by
    simp only [restrictOverHom, Functor.map_comp, hn, openHomEquiv,
      Equiv.trans_apply, fullyFaithfulHomEquiv, isoHomEquiv, Iso.trans_hom,
      Iso.trans_inv, Functor.mapIso_hom, Functor.mapIso_inv]
    simp [dE, dF, aE, aF, bE, bF, A, B, T, Category.assoc]
  have hE := ModuleGluing.overRestriction_coherence E i
  have hF := ModuleGluing.overRestriction_coherence F i
  change A.mapIso dE ≪≫ bE ≪≫ T.mapIso aE =
    (Scheme.Modules.overFunctorEquiv V).app E ≪≫
      ModuleGluing.subopenComparison E i at hE
  change A.mapIso dF ≪≫ bF ≪≫ T.mapIso aF =
    (Scheme.Modules.overFunctorEquiv V).app F ≪≫
      ModuleGluing.subopenComparison F i at hF
  rw [hE, hF] at hm
  change ((Scheme.Modules.overFunctorEquiv V).app E).inv ≫
    A.map (restrictOverHom i f) ≫
      ((Scheme.Modules.overFunctorEquiv V).app F).hom = _
  rw [hm]
  simp [restrictOpenHom, T, Category.assoc]

theorem sectionOfOverHom_restrict {X : Scheme} {E F : OModule X} {U V : X.Opens}
    (i : V ⟶ U) (f : E.over U ⟶ F.over U) :
    HomConstruction.restrictSection i ((HomConstruction.sectionOverEquiv E F U).symm f) =
      (HomConstruction.sectionOverEquiv E F V).symm (restrictOverHom i f) := by
  apply (HomConstruction.sectionOverEquiv E F V).injective
  rw [HomConstruction.sectionOverEquiv_restrict, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply]
  rfl

def glueOverHom {X : Scheme} {E F : OModule X} {I : Type}
    (U : I → X.Opens) (hcover : iSup U = ⊤)
    (f : ∀ i, E.over (U i) ⟶ F.over (U i))
    (h : ∀ i j,
      restrictOverHom (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)) (f i) =
        restrictOverHom (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)) (f j)) : E ⟶ F :=
  P1Ideal.glueLocalHom U hcover
    (fun i => (HomConstruction.sectionOverEquiv E F (U i)).symm (f i)) (by
      intro i j
      rw [sectionOfOverHom_restrict, sectionOfOverHom_restrict, h i j])

theorem glueOverHom_local {X : Scheme} {E F : OModule X} {I : Type}
    (U : I → X.Opens) (hcover : iSup U = ⊤)
    (f : ∀ i, E.over (U i) ⟶ F.over (U i))
    (h : ∀ i j,
      restrictOverHom (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)) (f i) =
        restrictOverHom (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)) (f j)) (i : I) :
    (SheafOfModules.overFunctor X.ringCatSheaf (U i)).map (glueOverHom U hcover f h) =
      f i := by
  change HomConstruction.sectionOverEquiv E F (U i)
    (P1Ideal.localSectionOfHom (glueOverHom U hcover f h) (U i)) = f i
  simp only [glueOverHom, P1Ideal.glueLocalHom_local, Equiv.apply_symm_apply]

end LeBrunSalamon.ModuleHomGluing
end

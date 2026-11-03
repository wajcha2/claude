import RecompileBasePart05B

noncomputable section

set_option autoImplicit false
open Bundle
open scoped Bundle ContDiff ENNReal
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance 100] LieRing.ofAssociativeRing
open CategoryTheory
open AlgebraicGeometry
open CategoryTheory.Limits



namespace LeBrunSalamon.PhaseTwentyEight

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseThree LeBrunSalamon.PhaseEight
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven


/- Source-only Phase 3 integration: canonical_external_exchange. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseEight LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.Skeleton LeBrunSalamon.Refinement
open LeBrunSalamon.Skeleton.PullbackPairProof LeBrunSalamon.Refinement.TensorPullbackComparisonProof

namespace ExternalExchangeCoherenceProof

theorem pullLocalSection_map {X Y : Scheme} (f : X ⟶ Y)
    {E F : OModule Y} (a : E ⟶ F) (U : Y.Opens) (e : SectionsOn E U) :
    ((Scheme.Modules.pullback f).map a).app (f ⁻¹ᵁ U) (pullLocalSection f E U e) =
      pullLocalSection f F U (a.app U e) := by
  have h := (Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality a
  have hv := congrArg
    (fun k : E ⟶ (Scheme.Modules.pushforward f).obj (pullbackModule f F) => k.app U e) h
  exact hv.symm

theorem pullLocalSection_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    (E : OModule Z) (U : Z.Opens) (e : SectionsOn E U) :
    ((Scheme.Modules.pullbackComp f g).hom.app E).app ((f ≫ g) ⁻¹ᵁ U)
      (pullLocalSection f (pullbackModule g E) (g ⁻¹ᵁ U) (pullLocalSection g E U e)) =
        pullLocalSection (f ≫ g) E U e := by
  have h := CanonicalPullbackSectionProof.pullbackComp_homEquiv f g
    ((Scheme.Modules.pullbackComp f g).hom.app E)
  simp only [Iso.inv_hom_id_app, Adjunction.homEquiv_id] at h
  have hv := congrArg
    (fun k : E ⟶ (Scheme.Modules.pushforward (f ≫ g)).obj
      (pullbackModule (f ≫ g) E) => k.app U e) h
  exact hv.symm

theorem pullLocalSection_id {X : Scheme} (E : OModule X)
    (U : X.Opens) (e : SectionsOn E U) :
    ((Scheme.Modules.pullbackId X).hom.app E).app U
      (pullLocalSection (𝟙 X) E U e) = e := by
  have h := unit_conjugateEquiv (Adjunction.id : 𝟭 X.Modules ⊣ 𝟭 X.Modules)
    (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X))
    (Scheme.Modules.pullbackId X).hom E
  rw [Scheme.Modules.conjugateEquiv_pullbackId_hom] at h
  have hv := congrArg
    (fun k : E ⟶ (Scheme.Modules.pushforward (𝟙 X)).obj E => k.app U e) h
  exact hv.symm

theorem iso_hom_inv_app {X : Scheme} {E F : OModule X} (e : E ≅ F)
    (U : X.Opens) (s : SectionsOn F U) : e.hom.app U (e.inv.app U s) = s :=
  congrArg (fun k : F ⟶ F => k.app U s) e.inv_hom_id

theorem iso_inv_hom_app {X : Scheme} {E F : OModule X} (e : E ≅ F)
    (U : X.Opens) (s : SectionsOn E U) : e.inv.app U (e.hom.app U s) = s :=
  congrArg (fun k : E ⟶ E => k.app U s) e.hom_inv_id

theorem pullLocalSection_comp_inv {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    (E : OModule Z) (U : Z.Opens) (e : SectionsOn E U) :
    ((Scheme.Modules.pullbackComp f g).inv.app E).app ((f ≫ g) ⁻¹ᵁ U)
      (pullLocalSection (f ≫ g) E U e) =
        pullLocalSection f (pullbackModule g E) (g ⁻¹ᵁ U) (pullLocalSection g E U e) := by
  rw [← pullLocalSection_comp f g E U e]
  exact iso_inv_hom_app ((Scheme.Modules.pullbackComp f g).app E) _ _

theorem comparison_naturality {X Y : Scheme} (f : X ⟶ Y)
    {E E' F F' : OModule Y} (a : E ⟶ E') (b : F ⟶ F') :
    tensorMap ((Scheme.Modules.pullback f).map a) ((Scheme.Modules.pullback f).map b) ≫
        tensorPullbackComparison f E' F' =
      tensorPullbackComparison f E F ≫ (Scheme.Modules.pullback f).map (tensorMap a b) := by
  apply ((tensorPresentation (pullbackModule f E) (pullbackModule f F)).universal _).1
  apply bilinear_pullback_ext f
  intro U e z
  change (tensorPullbackComparison f E' F').app (f ⁻¹ᵁ U)
      ((tensorMap ((Scheme.Modules.pullback f).map a)
          ((Scheme.Modules.pullback f).map b)).app (f ⁻¹ᵁ U)
        ((tensorPresentation (pullbackModule f E) (pullbackModule f F)).pair.apply (f ⁻¹ᵁ U)
          (pullLocalSection f E U e) (pullLocalSection f F U z))) =
    ((Scheme.Modules.pullback f).map (tensorMap a b)).app (f ⁻¹ᵁ U)
      ((tensorPullbackComparison f E F).app (f ⁻¹ᵁ U)
        ((tensorPresentation (pullbackModule f E) (pullbackModule f F)).pair.apply (f ⁻¹ᵁ U)
          (pullLocalSection f E U e) (pullLocalSection f F U z)))
  rw [tensorMap_apply, pullLocalSection_map, pullLocalSection_map,
    comparison_pair, comparison_pair,
    pullbackPair_normalized f (tensorPresentation E' F').pair U (a.app U e) (b.app U z),
    pullbackPair_normalized f (tensorPresentation E F).pair U e z,
    pullLocalSection_map, tensorMap_apply]

theorem comparison_comm {X Y : Scheme} (f : X ⟶ Y) (E F : OModule Y) :
    (TensorConstruction.commIso (pullbackModule f E) (pullbackModule f F)).hom ≫
        tensorPullbackComparison f F E =
      tensorPullbackComparison f E F ≫
        (Scheme.Modules.pullback f).map (TensorConstruction.commIso E F).hom := by
  apply ((tensorPresentation (pullbackModule f E) (pullbackModule f F)).universal _).1
  apply bilinear_pullback_ext f
  intro U e z
  change (tensorPullbackComparison f F E).app (f ⁻¹ᵁ U)
      ((TensorConstruction.commHom (pullbackModule f E) (pullbackModule f F)).app (f ⁻¹ᵁ U)
        ((tensorPresentation (pullbackModule f E) (pullbackModule f F)).pair.apply (f ⁻¹ᵁ U)
          (pullLocalSection f E U e) (pullLocalSection f F U z))) =
    ((Scheme.Modules.pullback f).map (TensorConstruction.commHom E F)).app (f ⁻¹ᵁ U)
      ((tensorPullbackComparison f E F).app (f ⁻¹ᵁ U)
        ((tensorPresentation (pullbackModule f E) (pullbackModule f F)).pair.apply (f ⁻¹ᵁ U)
          (pullLocalSection f E U e) (pullLocalSection f F U z)))
  rw [TensorConstruction.commHom_pair, comparison_pair, comparison_pair,
    pullbackPair_normalized f (tensorPresentation F E).pair U z e,
    pullbackPair_normalized f (tensorPresentation E F).pair U e z,
    pullLocalSection_map, TensorConstruction.commHom_pair]

theorem comparison_id (X : Scheme) (E F : OModule X) :
    tensorPullbackComparison (𝟙 X) E F ≫ (Scheme.Modules.pullbackId X).hom.app (tensorSheaf E F) =
      tensorMap ((Scheme.Modules.pullbackId X).hom.app E)
        ((Scheme.Modules.pullbackId X).hom.app F) := by
  apply ((tensorPresentation (pullbackModule (𝟙 X) E)
    (pullbackModule (𝟙 X) F)).universal _).1
  apply bilinear_pullback_ext (𝟙 X)
  intro U e z
  have hE : ((Scheme.Modules.pullbackId X).hom.app E).app ((𝟙 X) ⁻¹ᵁ U)
      (pullLocalSection (𝟙 X) E U e) = e := pullLocalSection_id E U e
  have hF : ((Scheme.Modules.pullbackId X).hom.app F).app ((𝟙 X) ⁻¹ᵁ U)
      (pullLocalSection (𝟙 X) F U z) = z := pullLocalSection_id F U z
  have hT : ((Scheme.Modules.pullbackId X).hom.app (tensorSheaf E F)).app ((𝟙 X) ⁻¹ᵁ U)
      (pullLocalSection (𝟙 X) (tensorSheaf E F) U ((tensorPresentation E F).pair.apply U e z)) =
        (tensorPresentation E F).pair.apply U e z :=
    pullLocalSection_id (tensorSheaf E F) U ((tensorPresentation E F).pair.apply U e z)
  change ((Scheme.Modules.pullbackId X).hom.app (tensorSheaf E F)).app ((𝟙 X) ⁻¹ᵁ U)
      ((tensorPullbackComparison (𝟙 X) E F).app ((𝟙 X) ⁻¹ᵁ U)
        ((tensorPresentation (pullbackModule (𝟙 X) E) (pullbackModule (𝟙 X) F)).pair.apply ((𝟙 X) ⁻¹ᵁ U)
          (pullLocalSection (𝟙 X) E U e) (pullLocalSection (𝟙 X) F U z))) =
    (tensorMap ((Scheme.Modules.pullbackId X).hom.app E)
      ((Scheme.Modules.pullbackId X).hom.app F)).app ((𝟙 X) ⁻¹ᵁ U)
        ((tensorPresentation (pullbackModule (𝟙 X) E) (pullbackModule (𝟙 X) F)).pair.apply ((𝟙 X) ⁻¹ᵁ U)
          (pullLocalSection (𝟙 X) E U e) (pullLocalSection (𝟙 X) F U z))
  rw [comparison_pair, pullbackPair_normalized (𝟙 X) (tensorPresentation E F).pair U e z,
    hT, tensorMap_apply]
  exact (congrArg₂ (fun a b => (tensorPresentation E F).pair.apply ((𝟙 X) ⁻¹ᵁ U) a b)
    hE hF).symm

theorem comparison_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    (E F : OModule Z) :
    tensorMap ((Scheme.Modules.pullbackComp f g).hom.app E)
        ((Scheme.Modules.pullbackComp f g).hom.app F) ≫
      tensorPullbackComparison (f ≫ g) E F =
    tensorPullbackComparison f (pullbackModule g E) (pullbackModule g F) ≫
      (Scheme.Modules.pullback f).map (tensorPullbackComparison g E F) ≫
        (Scheme.Modules.pullbackComp f g).hom.app (tensorSheaf E F) := by
  let e := (Scheme.Modules.pullbackComp f g).app E
  let z := (Scheme.Modules.pullbackComp f g).app F
  apply (cancel_epi (tensorIso e z).inv).1
  apply ((tensorPresentation (pullbackModule (f ≫ g) E)
    (pullbackModule (f ≫ g) F)).universal _).1
  apply bilinear_pullback_ext (f ≫ g)
  intro U a b
  change (tensorPullbackComparison (f ≫ g) E F).app ((f ≫ g) ⁻¹ᵁ U)
      ((tensorMap e.hom z.hom).app ((f ≫ g) ⁻¹ᵁ U)
        ((tensorMap e.inv z.inv).app ((f ≫ g) ⁻¹ᵁ U)
          ((tensorPresentation (pullbackModule (f ≫ g) E)
              (pullbackModule (f ≫ g) F)).pair.apply ((f ≫ g) ⁻¹ᵁ U)
            (pullLocalSection (f ≫ g) E U a) (pullLocalSection (f ≫ g) F U b)))) =
    ((Scheme.Modules.pullbackComp f g).hom.app (tensorSheaf E F)).app ((f ≫ g) ⁻¹ᵁ U)
      (((Scheme.Modules.pullback f).map (tensorPullbackComparison g E F)).app ((f ≫ g) ⁻¹ᵁ U)
        ((tensorPullbackComparison f (pullbackModule g E) (pullbackModule g F)).app ((f ≫ g) ⁻¹ᵁ U)
          ((tensorMap e.inv z.inv).app ((f ≫ g) ⁻¹ᵁ U)
            ((tensorPresentation (pullbackModule (f ≫ g) E)
                (pullbackModule (f ≫ g) F)).pair.apply ((f ≫ g) ⁻¹ᵁ U)
              (pullLocalSection (f ≫ g) E U a) (pullLocalSection (f ≫ g) F U b)))))
  simp only [tensorMap_apply, iso_hom_inv_app]
  rw [comparison_pair,
    pullbackPair_normalized (f ≫ g) (tensorPresentation E F).pair U a b]
  change pullLocalSection (f ≫ g) (tensorSheaf E F) U
      ((tensorPresentation E F).pair.apply U a b) = _
  dsimp only [e, z]
  simp only [Iso.app_inv]
  rw [pullLocalSection_comp_inv, pullLocalSection_comp_inv]
  simp only [Scheme.Hom.comp_preimage]
  erw [comparison_pair,
    pullbackPair_normalized f
      (tensorPresentation (pullbackModule g E) (pullbackModule g F)).pair (g ⁻¹ᵁ U)
      (pullLocalSection g E U a) (pullLocalSection g F U b),
    pullLocalSection_map, comparison_pair,
    pullbackPair_normalized g (tensorPresentation E F).pair U a b]
  exact (pullLocalSection_comp f g (tensorSheaf E F) U
    ((tensorPresentation E F).pair.apply U a b)).symm

theorem comparison_congr {X Y : Scheme} {f g : X ⟶ Y} (h : f = g)
    (E F : OModule Y) :
    tensorPullbackComparison f E F ≫ (Scheme.Modules.pullbackCongr h).hom.app (tensorSheaf E F) =
      tensorMap ((Scheme.Modules.pullbackCongr h).hom.app E)
        ((Scheme.Modules.pullbackCongr h).hom.app F) ≫ tensorPullbackComparison g E F := by
  subst g
  simp [Scheme.Modules.pullbackCongr, tensorMap_id]

def doublePullbackIso {X : Scheme} (f : X ⟶ X) (hf : f ≫ f = 𝟙 X)
    (E : OModule X) : pullbackModule f (pullbackModule f E) ≅ E :=
  (Scheme.Modules.pullbackComp f f).app E ≪≫
    (Scheme.Modules.pullbackCongr hf).app E ≪≫ (Scheme.Modules.pullbackId X).app E

theorem doublePullback_tensor {X : Scheme} (f : X ⟶ X) (hf : f ≫ f = 𝟙 X)
    (E F : OModule X) :
    tensorPullbackComparison f (pullbackModule f E) (pullbackModule f F) ≫
      (Scheme.Modules.pullback f).map (tensorPullbackComparison f E F) ≫
        (doublePullbackIso f hf (tensorSheaf E F)).hom =
      tensorMap (doublePullbackIso f hf E).hom (doublePullbackIso f hf F).hom := by
  simp only [doublePullbackIso, Iso.trans_hom, Iso.app_hom]
  calc
    _ = (tensorPullbackComparison f (pullbackModule f E) (pullbackModule f F) ≫
          (Scheme.Modules.pullback f).map (tensorPullbackComparison f E F) ≫
            (Scheme.Modules.pullbackComp f f).hom.app (tensorSheaf E F)) ≫
          (Scheme.Modules.pullbackCongr hf).hom.app (tensorSheaf E F) ≫
            (Scheme.Modules.pullbackId X).hom.app (tensorSheaf E F) := by simp only [Category.assoc]
    _ = (tensorMap ((Scheme.Modules.pullbackComp f f).hom.app E)
          ((Scheme.Modules.pullbackComp f f).hom.app F) ≫
            tensorPullbackComparison (f ≫ f) E F) ≫
          (Scheme.Modules.pullbackCongr hf).hom.app (tensorSheaf E F) ≫
            (Scheme.Modules.pullbackId X).hom.app (tensorSheaf E F) := by
      rw [← comparison_comp]
    _ = tensorMap ((Scheme.Modules.pullbackComp f f).hom.app E)
          ((Scheme.Modules.pullbackComp f f).hom.app F) ≫
        tensorMap ((Scheme.Modules.pullbackCongr hf).hom.app E)
          ((Scheme.Modules.pullbackCongr hf).hom.app F) ≫
        tensorMap ((Scheme.Modules.pullbackId X).hom.app E)
          ((Scheme.Modules.pullbackId X).hom.app F) := by
      simp only [Category.assoc]
      rw [← Category.assoc (tensorPullbackComparison (f ≫ f) E F),
        comparison_congr, Category.assoc, comparison_id]
    _ = _ := by
      simp only [tensorMap_comp, Category.assoc]

@[simp]

theorem swap_first {X : Scheme} (s : X ⟶ ComplexBase) :
    swapSelfProduct s ≫ firstProjection s = secondProjection s := by
  simp [swapSelfProduct, firstProjection, secondProjection]

@[simp]

theorem swap_second {X : Scheme} (s : X ⟶ ComplexBase) :
    swapSelfProduct s ≫ secondProjection s = firstProjection s := by
  simp [swapSelfProduct, firstProjection, secondProjection]

@[simp]

theorem swap_square {X : Scheme} (s : X ⟶ ComplexBase) :
    swapSelfProduct s ≫ swapSelfProduct s = 𝟙 (SelfProduct s) := by
  apply pullback.hom_ext <;> simp only [Category.assoc, swap_first, swap_second, Category.id_comp]

theorem pullSection_congr {X Y : Scheme} {f g : X ⟶ Y} (h : f = g)
    {E : OModule Y} (a : AlgebraicSection E) :
    pullSection f a ≫ (Scheme.Modules.pullbackCongr h).hom.app E = pullSection g a := by
  subst g
  simp [Scheme.Modules.pullbackCongr]

theorem pullSection_map {X Y : Scheme} (f : X ⟶ Y)
    {E F : OModule Y} (a : AlgebraicSection E) (b : E ⟶ F) :
    pullSection f (a ≫ b) = pullSection f a ≫ (Scheme.Modules.pullback f).map b := by
  simp only [pullSection, restrictSection, Functor.map_comp, Category.assoc]

theorem pullSection_id {X : Scheme} {E : OModule X} (a : AlgebraicSection E) :
    pullSection (𝟙 X) a ≫ (Scheme.Modules.pullbackId X).hom.app E = a := by
  apply (sectionValue_bijective E).injective
  rw [sectionValue_comp, pullSection_value]
  exact pullLocalSection_id E ⊤ (sectionValue a)

theorem pullSection_double {X : Scheme} (f : X ⟶ X) (hf : f ≫ f = 𝟙 X)
    {E : OModule X} (a : AlgebraicSection E) :
    pullSection f (pullSection f a) ≫ (doublePullbackIso f hf E).hom = a := by
  simp only [doublePullbackIso, Iso.trans_hom, Iso.app_hom]
  rw [← Category.assoc, ← Category.assoc,
    CanonicalPullbackSectionProof.pullSection_comp, pullSection_congr, pullSection_id]

def firstExchangeIso {X : Scheme} (s : X ⟶ ComplexBase) (E : OModule X) :
    pullbackModule (swapSelfProduct s) (pullbackModule (firstProjection s) E) ≅
      pullbackModule (secondProjection s) E :=
  (Scheme.Modules.pullbackComp (swapSelfProduct s) (firstProjection s)).app E ≪≫
    (Scheme.Modules.pullbackCongr (swap_first s)).app E

def secondExchangeIso {X : Scheme} (s : X ⟶ ComplexBase) (E : OModule X) :
    pullbackModule (swapSelfProduct s) (pullbackModule (secondProjection s) E) ≅
      pullbackModule (firstProjection s) E :=
  (Scheme.Modules.pullbackComp (swapSelfProduct s) (secondProjection s)).app E ≪≫
    (Scheme.Modules.pullbackCongr (swap_second s)).app E

theorem projection_pullbackComp_assoc {T Y Z W : Scheme}
    (f : T ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) (E : OModule W) :
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).hom.app E) ≫
        (Scheme.Modules.pullbackComp f (g ≫ h)).hom.app E =
      (Scheme.Modules.pullbackComp f g).hom.app (pullbackModule h E) ≫
        (Scheme.Modules.pullbackComp (f ≫ g) h).hom.app E ≫
          eqToHom (congrArg (fun k : T ⟶ W => pullbackModule k E)
            (Category.assoc f g h)) := by
  have ha := congrArg (fun a => a.app E)
    (Scheme.Modules.pseudofunctor_associativity f g h)
  have ha' :
      (Scheme.Modules.pullbackComp f (g ≫ h)).inv.app E ≫
        (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).inv.app E) ≫
          (Scheme.Modules.pullbackComp f g).hom.app (pullbackModule h E) ≫
            (Scheme.Modules.pullbackComp (f ≫ g) h).hom.app E =
      eqToHom (congrArg (fun k : T ⟶ W => pullbackModule k E)
        (Category.assoc f g h).symm) := by
    simpa only [NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.associator_hom_app, Category.id_comp,
      eqToHom_app] using ha
  have hb := congrArg (fun a =>
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).hom.app E) ≫
      (Scheme.Modules.pullbackComp f (g ≫ h)).hom.app E ≫ a ≫
        eqToHom (congrArg (fun k : T ⟶ W => pullbackModule k E)
          (Category.assoc f g h))) ha'
  simpa [Category.assoc, ← Functor.map_comp_assoc] using hb.symm

theorem projection_pullbackComp_eq_id {X Y : Scheme}
    (f : X ⟶ X) (hf : f = 𝟙 X) (p : X ⟶ Y) (hp : f ≫ p = p) (E : OModule Y) :
    (Scheme.Modules.pullbackComp f p).hom.app E ≫
        (Scheme.Modules.pullbackCongr hp).hom.app E =
      (Scheme.Modules.pullbackCongr hf).hom.app (pullbackModule p E) ≫
        (Scheme.Modules.pullbackId X).hom.app (pullbackModule p E) := by
  subst f
  have hu := congrArg (fun a => a.app E)
    (Scheme.Modules.pseudofunctor_right_unitality p)
  have hu' :
      (Scheme.Modules.pullbackComp (𝟙 X) p).inv.app E ≫
        (Scheme.Modules.pullbackId X).hom.app (pullbackModule p E) =
      eqToHom (congrArg (fun k : X ⟶ Y => pullbackModule k E) (Category.id_comp p)) := by
    change (Scheme.Modules.pullbackComp (𝟙 X) p).inv.app E ≫
      (Scheme.Modules.pullbackId X).hom.app (pullbackModule p E) ≫
        𝟙 (pullbackModule p E) = _ at hu
    erw [Category.comp_id] at hu
    simpa only [eqToHom_app] using hu
  have hv := congrArg (fun a =>
    (Scheme.Modules.pullbackComp (𝟙 X) p).hom.app E ≫ a) hu'
  simpa [Scheme.Modules.pullbackCongr, Category.assoc] using hv.symm

theorem projection_exchange_twice {X Y : Scheme}
    (f : X ⟶ X) (hf : f ≫ f = 𝟙 X)
    (p q : X ⟶ Y) (hp : f ≫ p = q) (hq : f ≫ q = p) (E : OModule Y) :
    (Scheme.Modules.pullback f).map
        ((Scheme.Modules.pullbackComp f p).hom.app E ≫
          (Scheme.Modules.pullbackCongr hp).hom.app E) ≫
      (Scheme.Modules.pullbackComp f q).hom.app E ≫
        (Scheme.Modules.pullbackCongr hq).hom.app E =
      (doublePullbackIso f hf (pullbackModule p E)).hom := by
  subst q
  simp only [Scheme.Modules.pullbackCongr, eqToIso.hom, eqToHom_app,
    eqToHom_refl, NatTrans.id_app, Category.comp_id, doublePullbackIso, Iso.trans_hom,
    Iso.app_hom]
  rw [← Category.assoc, projection_pullbackComp_assoc]
  simp only [Category.assoc, eqToHom_trans]
  apply congrArg (fun a =>
    (Scheme.Modules.pullbackComp f f).hom.app (pullbackModule p E) ≫ a)
  simpa only [Scheme.Modules.pullbackCongr, eqToIso.hom, eqToHom_app] using
    projection_pullbackComp_eq_id (f ≫ f) hf p
      ((Category.assoc f f p).trans hq) E

theorem firstExchangeIso_twice {X : Scheme} (s : X ⟶ ComplexBase) (E : OModule X) :
    (Scheme.Modules.pullback (swapSelfProduct s)).map (firstExchangeIso s E).hom ≫
        (secondExchangeIso s E).hom =
      (doublePullbackIso (swapSelfProduct s) (swap_square s)
        (pullbackModule (firstProjection s) E)).hom := by
  simpa only [firstExchangeIso, secondExchangeIso, Iso.trans_hom, Iso.app_hom,
    Category.assoc] using
    projection_exchange_twice (swapSelfProduct s) (swap_square s)
      (firstProjection s) (secondProjection s) (swap_first s) (swap_second s) E

theorem secondExchangeIso_twice {X : Scheme} (s : X ⟶ ComplexBase) (E : OModule X) :
    (Scheme.Modules.pullback (swapSelfProduct s)).map (secondExchangeIso s E).hom ≫
        (firstExchangeIso s E).hom =
      (doublePullbackIso (swapSelfProduct s) (swap_square s)
        (pullbackModule (secondProjection s) E)).hom := by
  simpa only [firstExchangeIso, secondExchangeIso, Iso.trans_hom, Iso.app_hom,
    Category.assoc] using
    projection_exchange_twice (swapSelfProduct s) (swap_square s)
      (secondProjection s) (firstProjection s) (swap_second s) (swap_first s) E

theorem firstExchangeIso_onSections {X : Scheme} (s : X ⟶ ComplexBase)
    {E : OModule X} (a : AlgebraicSection E) :
    pullSection (swapSelfProduct s) (pullSection (firstProjection s) a) ≫
      (firstExchangeIso s E).hom = pullSection (secondProjection s) a := by
  simp only [firstExchangeIso, Iso.trans_hom, Iso.app_hom]
  rw [← Category.assoc, CanonicalPullbackSectionProof.pullSection_comp,
    pullSection_congr]

theorem secondExchangeIso_onSections {X : Scheme} (s : X ⟶ ComplexBase)
    {E : OModule X} (a : AlgebraicSection E) :
    pullSection (swapSelfProduct s) (pullSection (secondProjection s) a) ≫
      (secondExchangeIso s E).hom = pullSection (firstProjection s) a := by
  simp only [secondExchangeIso, Iso.trans_hom, Iso.app_hom]
  rw [← Category.assoc, CanonicalPullbackSectionProof.pullSection_comp,
    pullSection_congr]

theorem tensorSection_comm {X : Scheme} {E F : OModule X}
    (a : AlgebraicSection E) (b : AlgebraicSection F) :
    tensorSection a b ≫ (TensorConstruction.commIso E F).hom = tensorSection b a := by
  apply (sectionValue_bijective (tensorSheaf F E)).injective
  simp only [sectionValue_comp, sectionValue_tensorSection]
  exact TensorConstruction.commHom_pair E F ⊤ (sectionValue a) (sectionValue b)

theorem tensorMap_comm {X : Scheme} {E F E' F' : OModule X}
    (a : E ⟶ E') (b : F ⟶ F') :
    tensorMap a b ≫ (TensorConstruction.commIso E' F').hom =
      (TensorConstruction.commIso E F).hom ≫ tensorMap b a := by
  apply ((tensorPresentation E F).universal _).1
  apply sheafBilinearMap_ext
  intro U e z
  change (TensorConstruction.commHom E' F').app U
      ((tensorMap a b).app U ((tensorPresentation E F).pair.apply U e z)) =
    (tensorMap b a).app U
      ((TensorConstruction.commHom E F).app U ((tensorPresentation E F).pair.apply U e z))
  rw [tensorMap_apply, TensorConstruction.commHom_pair,
    TensorConstruction.commHom_pair, tensorMap_apply]

def exchangeIsoOfFactors {X : Scheme} (f : X ⟶ X) (E F : OModule X)
    (e : pullbackModule f E ≅ F) (z : pullbackModule f F ≅ E) :
    pullbackModule f (tensorSheaf E F) ≅ tensorSheaf E F := by
  letI := tensorPullbackComparison_isIso f E F
  exact (asIso (tensorPullbackComparison f E F)).symm ≪≫
    tensorIso e z ≪≫ TensorConstruction.commIso F E

theorem exchangeIsoOfFactors_square {X : Scheme} (f : X ⟶ X) (hf : f ≫ f = 𝟙 X)
    (E F : OModule X) (e : pullbackModule f E ≅ F) (z : pullbackModule f F ≅ E)
    (he : (Scheme.Modules.pullback f).map e.hom ≫ z.hom = (doublePullbackIso f hf E).hom)
    (hz : (Scheme.Modules.pullback f).map z.hom ≫ e.hom = (doublePullbackIso f hf F).hom) :
    (Scheme.Modules.pullback f).map (exchangeIsoOfFactors f E F e z).hom ≫
      (exchangeIsoOfFactors f E F e z).hom =
        (doublePullbackIso f hf (tensorSheaf E F)).hom := by
  let P := Scheme.Modules.pullback f
  letI := tensorPullbackComparison_isIso f E F
  letI := tensorPullbackComparison_isIso f (pullbackModule f E) (pullbackModule f F)
  let C := asIso (tensorPullbackComparison f E F)
  let D := asIso (tensorPullbackComparison f (pullbackModule f E) (pullbackModule f F))
  let R := (exchangeIsoOfFactors f E F e z).hom
  have hR : C.hom ≫ R = tensorMap e.hom z.hom ≫ (TensorConstruction.commIso F E).hom := by
    change C.hom ≫ C.inv ≫ _ = _
    simp only [Iso.hom_inv_id_assoc, Iso.trans_hom, tensorIso]
  apply (cancel_epi (D.hom ≫ P.map C.hom)).1
  change (D.hom ≫ P.map C.hom) ≫ (P.map R ≫ R) =
    (D.hom ≫ P.map C.hom) ≫ (doublePullbackIso f hf (tensorSheaf E F)).hom
  calc
    _ = D.hom ≫ P.map (C.hom ≫ R) ≫ R := by
      rw [Functor.map_comp]
      simp only [Category.assoc]
    _ = D.hom ≫ P.map (tensorMap e.hom z.hom) ≫
        P.map (TensorConstruction.commIso F E).hom ≫ R := by
      rw [hR, Functor.map_comp]
      simp only [Category.assoc]
    _ = tensorMap (P.map e.hom) (P.map z.hom) ≫ tensorPullbackComparison f F E ≫
        P.map (TensorConstruction.commIso F E).hom ≫ R := by
      simpa only [P, C, D, asIso_hom, Category.assoc] using congrArg
        (fun q => q ≫ P.map (TensorConstruction.commIso F E).hom ≫ R)
        (comparison_naturality f e.hom z.hom).symm
    _ = tensorMap (P.map e.hom) (P.map z.hom) ≫
        (TensorConstruction.commIso (pullbackModule f F) (pullbackModule f E)).hom ≫
          C.hom ≫ R := by
      simpa only [P, C, D, asIso_hom, Category.assoc] using congrArg
        (fun q => tensorMap (P.map e.hom) (P.map z.hom) ≫ q ≫ R)
        (comparison_comm f F E).symm
    _ = tensorMap (P.map e.hom) (P.map z.hom) ≫
        (TensorConstruction.commIso (pullbackModule f F) (pullbackModule f E)).hom ≫
          tensorMap e.hom z.hom ≫ (TensorConstruction.commIso F E).hom := by rw [hR]
    _ = tensorMap (P.map e.hom) (P.map z.hom) ≫ tensorMap z.hom e.hom ≫
        (TensorConstruction.commIso E F).hom ≫ (TensorConstruction.commIso F E).hom := by
      simpa only [Category.assoc] using congrArg
        (fun q => tensorMap (P.map e.hom) (P.map z.hom) ≫ q ≫
          (TensorConstruction.commIso F E).hom) (tensorMap_comm z.hom e.hom).symm
    _ = tensorMap (P.map e.hom) (P.map z.hom) ≫ tensorMap z.hom e.hom := by
      change _ ≫ _ ≫ (TensorConstruction.commIso E F).hom ≫
        (TensorConstruction.commIso E F).inv = _
      simp only [Iso.hom_inv_id, Category.comp_id]
    _ = tensorMap (P.map e.hom ≫ z.hom) (P.map z.hom ≫ e.hom) :=
      (tensorMap_comp (P.map e.hom) z.hom (P.map z.hom) e.hom).symm
    _ = tensorMap (doublePullbackIso f hf E).hom (doublePullbackIso f hf F).hom := by rw [he, hz]
    _ = _ := by
      simpa only [P, C, D, asIso_hom, Category.assoc] using (doublePullback_tensor f hf E F).symm

def exchangeIso {X : Scheme} (s : X ⟶ ComplexBase) (L : LineBundle X) :
    pullbackModule (swapSelfProduct s) (externalSquareLine s L).sheaf ≅
      (externalSquareLine s L).sheaf := by
  letI := tensorPullbackComparison_isIso (swapSelfProduct s)
    (pullbackModule (firstProjection s) L.sheaf)
    (pullbackModule (secondProjection s) L.sheaf)
  exact (asIso (tensorPullbackComparison (swapSelfProduct s)
      (pullbackModule (firstProjection s) L.sheaf)
      (pullbackModule (secondProjection s) L.sheaf))).symm ≪≫
    tensorIso (firstExchangeIso s L.sheaf) (secondExchangeIso s L.sheaf) ≪≫
    TensorConstruction.commIso (pullbackModule (secondProjection s) L.sheaf)
      (pullbackModule (firstProjection s) L.sheaf)

theorem exchangeIso_factor {X : Scheme} (s : X ⟶ ComplexBase) (L : LineBundle X) :
    tensorPullbackComparison (swapSelfProduct s)
        (pullbackModule (firstProjection s) L.sheaf)
        (pullbackModule (secondProjection s) L.sheaf) ≫ (exchangeIso s L).hom =
      tensorMap (firstExchangeIso s L.sheaf).hom (secondExchangeIso s L.sheaf).hom ≫
        (TensorConstruction.commIso (pullbackModule (secondProjection s) L.sheaf)
          (pullbackModule (firstProjection s) L.sheaf)).hom := by
  letI := tensorPullbackComparison_isIso (swapSelfProduct s)
    (pullbackModule (firstProjection s) L.sheaf)
    (pullbackModule (secondProjection s) L.sheaf)
  change (asIso (tensorPullbackComparison (swapSelfProduct s)
      (pullbackModule (firstProjection s) L.sheaf)
      (pullbackModule (secondProjection s) L.sheaf))).hom ≫
    (asIso (tensorPullbackComparison (swapSelfProduct s)
      (pullbackModule (firstProjection s) L.sheaf)
      (pullbackModule (secondProjection s) L.sheaf))).inv ≫ _ = _
  simp only [Iso.hom_inv_id_assoc, Iso.trans_hom, tensorIso]

def identification {X : Scheme} (s : X ⟶ ComplexBase) (L : LineBundle X) :
    TwoPointExchangeIdentification s (externalSquareLine s L).sheaf where
  onSheaf := exchangeIso s L
  onUnit := unitPullbackIso (swapSelfProduct s)

theorem identification_unit {X : Scheme} (s : X ⟶ ComplexBase) (L : LineBundle X) :
    (identification s L).onUnit = unitPullbackIso (swapSelfProduct s) := rfl

theorem identification_swapSection_eq {X : Scheme} (s : X ⟶ ComplexBase) (L : LineBundle X)
    (B : AlgebraicSection (externalSquareLine s L).sheaf) :
    (identification s L).swapSection B = pullSection (swapSelfProduct s) B ≫ (exchangeIso s L).hom := by
  simp only [identification, TwoPointExchangeIdentification.swapSection,
    pullSection, restrictSection, Category.assoc]

theorem identification_onProducts {X : Scheme} (s : X ⟶ ComplexBase) (L : LineBundle X)
    (a b : AlgebraicSection L.sheaf) :
    (identification s L).swapSection (externalProductSection s a b) =
      externalProductSection s b a := by
  rw [identification_swapSection_eq]
  change pullSection (swapSelfProduct s)
      (tensorSection (pullSection (firstProjection s) a) (pullSection (secondProjection s) b)) ≫
        (exchangeIso s L).hom =
    tensorSection (pullSection (firstProjection s) b) (pullSection (secondProjection s) a)
  rw [← tensorPullbackComparison_onSections]
  rw [Category.assoc, exchangeIso_factor]
  rw [← Category.assoc, tensorSection_map, firstExchangeIso_onSections,
    secondExchangeIso_onSections, tensorSection_comm]

theorem exchangeIso_square {X : Scheme} (s : X ⟶ ComplexBase) (L : LineBundle X) :
    (Scheme.Modules.pullback (swapSelfProduct s)).map (exchangeIso s L).hom ≫
        (exchangeIso s L).hom =
      (doublePullbackIso (swapSelfProduct s) (swap_square s) (externalSquareLine s L).sheaf).hom := by
  exact exchangeIsoOfFactors_square (swapSelfProduct s) (swap_square s)
    (pullbackModule (firstProjection s) L.sheaf)
    (pullbackModule (secondProjection s) L.sheaf)
    (firstExchangeIso s L.sheaf) (secondExchangeIso s L.sheaf)
    (firstExchangeIso_twice s L.sheaf) (secondExchangeIso_twice s L.sheaf)

theorem identification_involutive {X : Scheme} (s : X ⟶ ComplexBase) (L : LineBundle X)
    (B : AlgebraicSection (externalSquareLine s L).sheaf) :
    (identification s L).swapSection ((identification s L).swapSection B) = B := by
  rw [identification_swapSection_eq, identification_swapSection_eq, pullSection_map,
    Category.assoc, exchangeIso_square]
  exact pullSection_double (swapSelfProduct s) (swap_square s) B

theorem involutiveExternalExchange_exists {X : Scheme}
    (s : X ⟶ ComplexBase) (L : LineBundle X) :
    Nonempty (InvolutiveExternalExchange s L) := by
  exact ⟨{
    identification := identification s L
    unitNormalization := identification_unit s L
    involutive := identification_involutive s L
    onProducts := identification_onProducts s L }⟩

end ExternalExchangeCoherenceProof
end


/-- FOUNDATION: tensor symmetry, pullback composition, and unit coherence.
The chosen identification is required to have the right normalization. -/
theorem involutiveExternalExchange_exists {X : Scheme}
    (s : X ⟶ ComplexBase) (L : LineBundle X) :
    Nonempty (InvolutiveExternalExchange s L) := by
  exact LeBrunSalamon.PhaseTwentyEight.ExternalExchangeCoherenceProof.involutiveExternalExchange_exists s L

def chosenExternalExchange {X : Scheme}
    (s : X ⟶ ComplexBase) (L : LineBundle X) :
    InvolutiveExternalExchange s L :=
  Classical.choice (involutiveExternalExchange_exists s L)

def IsSymmetricExternalSection {X : Scheme}
    (s : X ⟶ ComplexBase) (L : LineBundle X)
    (B : AlgebraicSection (externalSquareLine s L).sheaf) : Prop :=
  (chosenExternalExchange s L).identification.swapSection B = B

/- Source-only Phase 3 integration: external_exchange. -/
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseEight

namespace ExchangeAlgebraProof

set_option backward.isDefEq.respectTransparency false in
def swapSectionAddHom {X : Scheme} {s : X ⟶ ComplexBase}
    {E : OModule (SelfProduct s)} (τ : TwoPointExchangeIdentification s E) :
    AlgebraicSection E →+ AlgebraicSection E where
  toFun := τ.swapSection
  map_zero' := by
    change τ.onUnit.inv ≫ (Scheme.Modules.pullback (swapSelfProduct s)).map
      (0 : structureModule (SelfProduct s) ⟶ E) ≫ τ.onSheaf.hom = 0
    rw [Functor.map_zero (Scheme.Modules.pullback (swapSelfProduct s))
      (structureModule (SelfProduct s)) E]
    simp only [comp_zero, zero_comp]
  map_add' := by
    intro B C
    change τ.onUnit.inv ≫ (Scheme.Modules.pullback (swapSelfProduct s)).map
      ((B : structureModule (SelfProduct s) ⟶ E) + C) ≫ τ.onSheaf.hom =
        τ.onUnit.inv ≫ (Scheme.Modules.pullback (swapSelfProduct s)).map B ≫ τ.onSheaf.hom +
          τ.onUnit.inv ≫ (Scheme.Modules.pullback (swapSelfProduct s)).map C ≫ τ.onSheaf.hom
    rw [Functor.map_add (Scheme.Modules.pullback (swapSelfProduct s))
      (X := structureModule (SelfProduct s)) (Y := E) (f := B) (g := C)]
    simp only [Preadditive.add_comp, Preadditive.comp_add]

theorem externalExchange_square {X : Scheme}
    (s : X ⟶ ComplexBase) (L : LineBundle X)
    (B : AlgebraicSection (externalSquareLine s L).sheaf) :
    (chosenExternalExchange s L).identification.swapSection
      ((chosenExternalExchange s L).identification.swapSection B) = B := by
  exact (chosenExternalExchange s L).involutive B

theorem symmetricExternal_zero {X : Scheme}
    (s : X ⟶ ComplexBase) (L : LineBundle X) :
    IsSymmetricExternalSection s L 0 := by
  exact (swapSectionAddHom (chosenExternalExchange s L).identification).map_zero

theorem symmetricExternal_add {X : Scheme}
    (s : X ⟶ ComplexBase) (L : LineBundle X)
    (B C : AlgebraicSection (externalSquareLine s L).sheaf)
    (hB : IsSymmetricExternalSection s L B)
    (hC : IsSymmetricExternalSection s L C) :
    IsSymmetricExternalSection s L (B + C) := by
  change (swapSectionAddHom (chosenExternalExchange s L).identification) (B + C) = B + C
  rw [map_add]
  exact congrArg₂ (· + ·) hB hC

end ExchangeAlgebraProof
end


theorem externalExchange_square {X : Scheme}
    (s : X ⟶ ComplexBase) (L : LineBundle X)
    (B : AlgebraicSection (externalSquareLine s L).sheaf) :
    (chosenExternalExchange s L).identification.swapSection
      ((chosenExternalExchange s L).identification.swapSection B) = B := by
  exact LeBrunSalamon.PhaseTwentyEight.ExchangeAlgebraProof.externalExchange_square (s := s) (L := L) (B := B)

theorem symmetricExternal_zero {X : Scheme}
    (s : X ⟶ ComplexBase) (L : LineBundle X) :
    IsSymmetricExternalSection s L 0 := by
  exact LeBrunSalamon.PhaseTwentyEight.ExchangeAlgebraProof.symmetricExternal_zero (s := s) (L := L)

theorem symmetricExternal_add {X : Scheme}
    (s : X ⟶ ComplexBase) (L : LineBundle X)
    (B C : AlgebraicSection (externalSquareLine s L).sheaf)
    (hB : IsSymmetricExternalSection s L B)
    (hC : IsSymmetricExternalSection s L C) :
    IsSymmetricExternalSection s L (B + C) := by
  exact LeBrunSalamon.PhaseTwentyEight.ExchangeAlgebraProof.symmetricExternal_add (s := s) (L := L) (B := B) (C := C) (hB := hB) (hC := hC)

/-- **Published input (exact).** Degree-zero Künneth for two copies of a
proper complex scheme and two invertible sheaves: the canonical external-product
map on global sections is surjective.  This is the `n = 0` component of Stacks
Project, Lemma 33.29.1 (Tag 0BED), with the displayed external-product map fixed
by the definitions above. -/
theorem _root_.LeBrunSalamon.PublishedInputs.ExternalTensorDiagonal.kunneth_degreeZero_surjective
    {d : ℕ} (X : SmoothProperComplexVariety d) (L M : LineBundle X.scheme)
    (B : AlgebraicSection (externalTensor X.structureMap L.sheaf M.sheaf)) :
    ∃ (N : ℕ) (a : Fin N → AlgebraicSection L.sheaf)
      (b : Fin N → AlgebraicSection M.sheaf),
      B = ∑ i, externalProductSection X.structureMap (a i) (b i) := by
  sorry

/-- Project API wrapper for degree-zero Künneth surjectivity. -/
theorem externalSection_finiteSum {d : ℕ}
    (X : SmoothProperComplexVariety d) (L M : LineBundle X.scheme)
    (B : AlgebraicSection (externalTensor X.structureMap L.sheaf M.sheaf)) :
    ∃ (N : ℕ) (a : Fin N → AlgebraicSection L.sheaf)
      (b : Fin N → AlgebraicSection M.sheaf),
      B = ∑ i, externalProductSection X.structureMap (a i) (b i) :=
  LeBrunSalamon.PublishedInputs.ExternalTensorDiagonal.kunneth_degreeZero_surjective X L M B

/-- The actual moving-pair bundles T_X boxtimes L and L boxtimes T_X. -/
abbrev movingPairBundleLeft {n : ℕ}
    (X : SmoothProperComplexVariety (2 * n + 1))
    (C : IntrinsicContactStructure X) :=
  externalTensor X.structureMap (tangentSheaf X.structureMap) C.sequence.line.sheaf

abbrev movingPairBundleRight {n : ℕ}
    (X : SmoothProperComplexVariety (2 * n + 1))
    (C : IntrinsicContactStructure X) :=
  externalTensor X.structureMap C.sequence.line.sheaf (tangentSheaf X.structureMap)

def movingPairContactLeft {n : ℕ}
    (X : SmoothProperComplexVariety (2 * n + 1))
    (C : IntrinsicContactStructure X) :
    movingPairBundleLeft X C ⟶ (externalSquareLine X.structureMap C.sequence.line).sheaf :=
  externalTensorMap X.structureMap C.sequence.form (𝟙 C.sequence.line.sheaf)

def movingPairContactRight {n : ℕ}
    (X : SmoothProperComplexVariety (2 * n + 1))
    (C : IntrinsicContactStructure X) :
    movingPairBundleRight X C ⟶ (externalSquareLine X.structureMap C.sequence.line).sheaf :=
  externalTensorMap X.structureMap (𝟙 C.sequence.line.sheaf) C.sequence.form

set_option backward.isDefEq.respectTransparency false in
theorem pullSectionValue_smul {Y Z : Scheme} (f : Y ⟶ Z)
    (E : OModule Z) (r : RingSections Z ⊤) (a : GlobalSections E) :
    sectionValue (pullSection f (sectionFromValue (r • a))) =
      f.appTop r • sectionValue (pullSection f (sectionFromValue a)) := by
  simp only [pullSection_value, sectionFromValue_spec]
  exact Scheme.Modules.Hom.app_smul
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app E) r a

set_option backward.isDefEq.respectTransparency false in
theorem pullSection_naturality {X Y : Scheme} (f : X ⟶ Y)
    {E F : OModule Y} (s : AlgebraicSection E) (h : E ⟶ F) :
    pullSection f (s ≫ h) = pullSection f s ≫ (Scheme.Modules.pullback f).map h := by
  simp [pullSection, restrictSection, Functor.map_comp, Category.assoc]

/-- This is the genuine sheaf condition f_*O_X = O_Y, not a claim that
connected set-theoretic fibres alone suffice. -/
def HasStructureSheafDescent {X Y : Scheme} (f : X ⟶ Y) : Prop :=
  IsIso (structurePushforwardMap f)

/-- **Published input (exact).** Degree-zero projection formula for a finite
locally free module, in the case where the canonical comparison
`O_Y → f_* O_X` is an isomorphism.  This is the global-section form of
Stacks Project, Lemma 20.54.2 (Tag 01E6), with the canonical pullback map
identified by `pullSection_adjoint` above. -/
theorem _root_.LeBrunSalamon.PublishedInputs.ExternalTensorDiagonal.projectionFormula_sections_bijective
    {X Y : Scheme} (f : X ⟶ Y)
    (hf : IsIso (structurePushforwardMap f)) {r : ℕ}
    (E : AlgebraicVectorBundle Y r) :
    Function.Bijective (pullSection f (E := E.sheaf)) := by
  sorry

/-- Project API wrapper for the degree-zero projection formula. -/
theorem locallyFree_sections_descend {X Y : Scheme} (f : X ⟶ Y)
    (hf : HasStructureSheafDescent f) {r : ℕ}
    (E : AlgebraicVectorBundle Y r) :
    Function.Bijective (pullSection f (E := E.sheaf)) :=
  LeBrunSalamon.PublishedInputs.ExternalTensorDiagonal.projectionFormula_sections_bijective
    f hf E

theorem locallyFree_descent_existsUnique {X Y : Scheme} (f : X ⟶ Y)
    (hf : HasStructureSheafDescent f) {r : ℕ}
    (E : AlgebraicVectorBundle Y r)
    (a : AlgebraicSection (pullbackModule f E.sheaf)) :
    ∃! b : AlgebraicSection E.sheaf, pullSection f b = a := by
  obtain ⟨b, hb⟩ := (locallyFree_sections_descend f hf E).2 a
  exact ⟨b, hb, fun c hc => (locallyFree_sections_descend f hf E).1 (hc.trans hb.symm)⟩

/- Source-only Phase 3 integration: dominant_section_injectivity. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix LeBrunSalamon.PhaseTwentyEight

namespace DominantSectionInjectivityProof

theorem app_injective_of_dense {X Y : Scheme} (f : X ⟶ Y)
    (hf : DenseRange f.base)
    (hY : ∀ U : Y.Opens, IsReduced (RingSections Y U)) (U : Y.Opens) :
    Function.Injective (f.app U) := by
  letI : AlgebraicGeometry.IsReduced Y := ⟨hY⟩
  apply (injective_iff_map_eq_zero (f.app U).hom).mpr
  intro a ha
  apply AlgebraicGeometry.eq_zero_of_basicOpen_eq_bot a
  have hp : f ⁻¹ᵁ Y.basicOpen a = ⊥ := by
    rw [Scheme.preimage_basicOpen, ha]
    simp
  have hp' : f.base ⁻¹' (Y.basicOpen a : Set Y) = ∅ :=
    congrArg (fun V : X.Opens => (V : Set X)) hp
  have hd := hf.subset_closure_image_preimage_of_isOpen (Y.basicOpen a).isOpen
  rw [hp', Set.image_empty, closure_empty] at hd
  apply TopologicalSpace.Opens.ext
  exact Set.eq_empty_of_subset_empty hd

theorem unit_pullback_detects_zero {X Y : Scheme.{0}} (f : X ⟶ Y)
    (hf : Function.Injective f.appTop)
    (a : AlgebraicSection (structureModule Y))
    (ha : (Scheme.Modules.pullback f).map a = 0) : a = 0 := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction
    (X := X) (Y := Y) f
  have hu : adj.homEquiv (structureModule Y) (structureModule X)
      (unitPullbackMap (X := X) (Y := Y) f) = structurePushforwardMap f :=
    unitPullbackMap_adjoint (X := X) (Y := Y) f
  have hcomp : a ≫ structurePushforwardMap f = 0 := by
    have hn := adj.homEquiv_naturality_left a (unitPullbackMap (X := X) (Y := Y) f)
    rw [hu, ha, zero_comp, adj.homAddEquiv_zero] at hn
    exact hn.symm
  have hvalue := congrArg
    (fun k : structureModule Y ⟶ (Scheme.Modules.pushforward f).obj (structureModule X) =>
      k.app ⊤ (1 : RingSections Y ⊤)) hcomp
  change f.appTop (sectionValue a) = 0 at hvalue
  apply (sectionValue_bijective (structureModule Y)).1
  rw [sectionValue_zero]
  apply hf
  simpa only [map_zero] using hvalue

theorem free_pullback_detects_zero {X Y : Scheme.{0}} (f : X ⟶ Y)
    (hf : Function.Injective f.appTop) {E : OModule Y} {r : ℕ}
    (e : SheafOfModules.free (R := Y.ringCatSheaf) (Fin r) ≅ E)
    (a : AlgebraicSection E)
    (ha : (Scheme.Modules.pullback f).map a = 0) : a = 0 := by
  let P : Fin r → OModule Y := fun _ => structureModule Y
  letI : HasBiproduct P := HasBiproduct.of_hasCoproduct P
  let eP : SheafOfModules.free (R := Y.ringCatSheaf) (Fin r) ≅ ∏ᶜ P :=
    (biproductIso P).symm
  apply (cancel_mono e.inv).1
  apply (cancel_mono eP.hom).1
  simp only [zero_comp]
  apply Pi.hom_ext
  intro i
  rw [zero_comp]
  apply unit_pullback_detects_zero f hf
  simp only [Functor.map_comp, ha, zero_comp]

def localFreePullbackIso {Y : Scheme} {E : OModule Y} {r : ℕ}
    (q : SheafOfModules.LocalGeneratorsData.{0} E) [q.IsLocallyFreeData]
    (hr : ∀ i : q.I, Nonempty ((q.generators i).I ≃ Fin r)) (i : q.I) :
    SheafOfModules.free
      (R := (Scheme.Opens.toScheme (X := Y) (q.X i)).ringCatSheaf) (Fin r) ≅
      pullbackModule (Scheme.Opens.ι (X := Y) (q.X i)) E := by
  let U : Y.Opens := q.X i
  let A := (Scheme.Modules.overEquiv U).functor
  let eunit : A.obj (SheafOfModules.unit (Y.ringCatSheaf.over U)) ≅
      structureModule U.toScheme :=
    (Scheme.Modules.overFunctorEquiv U).app (structureModule Y) ≪≫
      Scheme.Modules.restrictUnitIso U.ι
  exact SheafOfModules.mapFreeIso A (Fin r) eunit.symm ≪≫
    A.mapIso (SheafTensor.localBasisTrivialization q hr i) ≪≫
    (Scheme.Modules.overFunctorEquiv U).app E ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback U.ι).app E

theorem over_zero_of_pullback_zero {Y : Scheme} {E F : OModule Y}
    (U : Y.Opens) (a : E ⟶ F)
    (ha : (Scheme.Modules.pullback U.ι).map a = 0) : a.over U = 0 := by
  let A := (Scheme.Modules.overEquiv U).functor
  let e := Scheme.Modules.overFunctorEquiv U ≪≫
    Scheme.Modules.restrictFunctorIsoPullback U.ι
  have hz : A.map (a.over U) = 0 := by
    apply (cancel_mono (e.hom.app F)).1
    rw [zero_comp]
    change (SheafOfModules.overFunctor Y.ringCatSheaf U ⋙ A).map a ≫
      e.hom.app F = 0
    rw [e.hom.naturality a, ha, comp_zero]
  apply A.map_injective
  simpa only [Functor.map_zero] using hz

theorem locallyFree_pullback_detects_zero {X Y : Scheme.{0}} (f : X ⟶ Y)
    (hf : DenseRange f.base)
    (hY : ∀ U : Y.Opens, IsReduced (RingSections Y U))
    {E : OModule Y} {r : ℕ} (hE : IsLocallyFreeOfRank E r)
    (a : AlgebraicSection E)
    (ha : (Scheme.Modules.pullback f).map a = 0) : a = 0 := by
  obtain ⟨q, hq, hr⟩ := hE
  letI := hq
  have hopen : ∀ i : q.I,
      (Scheme.Modules.pullback (Scheme.Opens.ι (X := Y) (q.X i))).map a = 0 := by
    intro i
    let U : Y.Opens := q.X i
    let V : X.Opens := f ⁻¹ᵁ U
    let g : V.toScheme ⟶ U.toScheme := f.resLE U V le_rfl
    have hg : Function.Injective g.appTop := by
      change Function.Injective ((f.resLE U (f ⁻¹ᵁ U) le_rfl).app ⊤)
      rw [Scheme.Hom.resLE_app_top, Scheme.Hom.appLE_eq_app]
      exact (ConcreteCategory.bijective_of_isIso (f ⁻¹ᵁ U).topIso.inv).injective.comp
        ((app_injective_of_dense f hf hY U).comp
          (ConcreteCategory.bijective_of_isIso U.topIso.hom).injective)
    have hcomp : (Scheme.Modules.pullback (g ≫ U.ι)).map a = 0 := by
      rw [show g ≫ U.ι = V.ι ≫ f from Scheme.Hom.resLE_comp_ι f le_rfl]
      apply (LeBrunSalamon.PhaseFourteen.SliceRestrictionProof.pullback_comp_zero_iff
        V.ι f a).mpr
      rw [ha, Functor.map_zero]
    have hiter :=
      (LeBrunSalamon.PhaseFourteen.SliceRestrictionProof.pullback_comp_zero_iff
        g U.ι a).mp hcomp
    have hlocal : pullSection U.ι a = 0 := by
      apply free_pullback_detects_zero g hg (localFreePullbackIso q hr i)
      change (Scheme.Modules.pullback g).map
        ((unitPullbackIso U.ι).inv ≫ (Scheme.Modules.pullback U.ι).map a) = 0
      rw [Functor.map_comp, hiter, comp_zero]
    have hunit := unitPullbackMap_pullSection U.ι a
    rw [hlocal, comp_zero] at hunit
    exact hunit.symm
  apply (sectionValue_bijective E).1
  rw [sectionValue_zero]
  let S : TopCat.Sheaf AddCommGrpCat Y :=
    (SheafOfModules.toSheaf Y.ringCatSheaf).obj E
  have hcover : iSup q.X = ⊤ := (_root_.Opens.coversTop_iff Y q.X).mp q.coversTop
  apply TopCat.Sheaf.eq_of_locally_eq' S q.X ⊤
    (fun i => (q.X i).leTop) (by rw [hcover])
  intro i
  have ho := over_zero_of_pullback_zero (q.X i) a (hopen i)
  have hvalue := congrArg
    (fun k : (structureModule Y).over (q.X i) ⟶ E.over (q.X i) =>
      k.val.app (op (Over.mk (𝟙 (q.X i)))) (1 : RingSections Y (q.X i))) ho
  change (Scheme.Modules.Hom.app a (q.X i)) (1 : RingSections Y (q.X i)) = 0 at hvalue
  change E.presheaf.map (homOfLE le_top).op (sectionValue a) =
    E.presheaf.map (homOfLE le_top).op 0
  rw [sectionValue, sheafHom_naturality]
  change (Scheme.Modules.Hom.app a (q.X i))
      (Y.presheaf.map (homOfLE le_top).op (1 : RingSections Y ⊤)) =
    E.presheaf.map (homOfLE le_top).op 0
  rw [map_one, map_zero]
  exact hvalue

theorem dominant_pullSection_injective {X Y : Scheme} (f : X ⟶ Y)
    (hf : DenseRange f.base)
    (hY : ∀ U : Y.Opens, IsReduced (RingSections Y U)) {r : ℕ}
    (E : AlgebraicVectorBundle Y r) :
    Function.Injective (pullSection f (E := E.sheaf)) := by
  intro a b hab
  apply sub_eq_zero.mp
  apply locallyFree_pullback_detects_zero f hf hY E.locallyFree (a - b)
  have h := congrArg (fun t => unitPullbackMap f ≫ t) hab
  rw [unitPullbackMap_pullSection, unitPullbackMap_pullSection] at h
  rw [Functor.map_sub, h, sub_self]

end DominantSectionInjectivityProof
end


/-- Dominance gives uniqueness on a reduced target, not existence. -/
theorem dominant_pullSection_injective {X Y : Scheme} (f : X ⟶ Y)
    (hf : DenseRange f.base)
    (hY : ∀ U : Y.Opens, IsReduced (RingSections Y U)) {r : ℕ}
    (E : AlgebraicVectorBundle Y r) :
    Function.Injective (pullSection f (E := E.sheaf)) := by
  exact LeBrunSalamon.PhaseTwentyEight.DominantSectionInjectivityProof.dominant_pullSection_injective
    f hf hY E

/- Source-only Phase 3 integration: zero_principal_parts. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix

namespace ZeroPrincipalPartsProof

def pushforwardPullbackIso {Y Z : Scheme} (f : Y ⟶ Z) [IsIso f]
    (E : OModule Z) :
    (Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback f).obj E) ≅ E := by
  let u := (Scheme.Modules.restrictAdjunction f).unit.app E
  letI : IsIso u := by
    apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
    intro U
    change IsIso (E.presheaf.map (homOfLE (f.image_preimage_le U)).op)
    have hU : f ''ᵁ (f ⁻¹ᵁ U) = U := by
      rw [f.image_preimage_eq_opensRange_inf, f.opensRange_of_isIso, top_inf_eq]
    have hi : homOfLE (f.image_preimage_le U) = (eqToIso hU).hom :=
      Subsingleton.elim _ _
    rw [hi]
    infer_instance
  exact (Scheme.Modules.pushforward f).mapIso
    ((Scheme.Modules.restrictFunctorIsoPullback f).symm.app E) ≪≫ (asIso u).symm

theorem principalParts_zero_iso {d : ℕ}
    (X : SmoothProperComplexVariety d) [IsSeparated X.structureMap]
    (E : OModule X.scheme) :
    Nonempty (ZeroJetSheaf X.structureMap E ≅ E) := by
  let δ := diagonal X.structureMap
  have hfirst : δ.toImage ≫ (δ.imageι ≫ firstProjection X.structureMap) = 𝟙 X.scheme := by
    rw [← Category.assoc, δ.toImage_imageι]
    exact pullback.diagonal_fst X.structureMap
  have hsecond : δ.toImage ≫ (δ.imageι ≫ secondProjection X.structureMap) = 𝟙 X.scheme := by
    rw [← Category.assoc, δ.toImage_imageι]
    exact pullback.diagonal_snd X.structureMap
  have efirst : δ.imageι ≫ firstProjection X.structureMap = inv δ.toImage :=
    IsIso.eq_inv_of_hom_inv_id hfirst
  have esecond : δ.imageι ≫ secondProjection X.structureMap = inv δ.toImage :=
    IsIso.eq_inv_of_hom_inv_id hsecond
  let Q : (SelfProduct X.structureMap).IdealSheafData → OModule X.scheme := fun I =>
    (Scheme.Modules.pushforward (I.subschemeι ≫ firstProjection X.structureMap)).obj
      ((Scheme.Modules.pullback (I.subschemeι ≫ secondProjection X.structureMap)).obj E)
  change Nonempty (Q ((diagonalIdeal X.structureMap) ^ 1) ≅ E)
  rw [pow_one]
  change Nonempty ((Scheme.Modules.pushforward
      (δ.imageι ≫ firstProjection X.structureMap)).obj
    ((Scheme.Modules.pullback (δ.imageι ≫ secondProjection X.structureMap)).obj E) ≅ E)
  rw [efirst, esecond]
  exact ⟨pushforwardPullbackIso (inv δ.toImage) E⟩

end ZeroPrincipalPartsProof
end


theorem principalParts_zero_iso {d : ℕ}
    (X : SmoothProperComplexVariety d) [IsSeparated X.structureMap]
    (E : OModule X.scheme) :
    Nonempty (ZeroJetSheaf X.structureMap E ≅ E) := by
  exact ZeroPrincipalPartsProof.principalParts_zero_iso X E

/- The exact original first-jet target is located in LSCompletedTargets,
after the actual extension and global-kernel constructions. Its statement
and the definition of ContactFanoManifold are unchanged. -/

end LeBrunSalamon.PhaseTwentyEight

end

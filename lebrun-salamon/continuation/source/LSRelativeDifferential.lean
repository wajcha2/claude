import LSNodalFixedEnds

/-!
# Functoriality of relative cotangent maps

All maps are constructed from the original universal derivation. The
composition and equality rules are proved on its actual local generators;
no tangent map or base-change comparison is chosen independently.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirty
open LeBrunSalamon.Skeleton LeBrunSalamon.Refinement

namespace LeBrunSalamon.Construction.RelativeDifferential

theorem pulledCotangent_hom_ext {Y X S : Scheme} (f : Y ⟶ X) (s : X ⟶ S)
    {E : OModule Y} (a b : pullbackModule f (cotangentSheaf s) ⟶ E)
    (h : ∀ (U : X.Opens) (z : RingSections X U),
      a.app (f ⁻¹ᵁ U) (pullLocalSection f (cotangentSheaf s) U
        ((cotangentPresentation s).differential.apply U z)) =
      b.app (f ⁻¹ᵁ U) (pullLocalSection f (cotangentSheaf s) U
        ((cotangentPresentation s).differential.apply U z))) : a = b := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  apply CotangentTransitivityRederivedV02.cotangentHom_ext
  exact h

def cotangent {C B D A : Scheme} (piC : C ⟶ B) (piD : D ⟶ A)
    (f : C ⟶ D) (g : B ⟶ A) (h : f ≫ piD = piC ≫ g) :
    pullbackModule f (cotangentSheaf piD) ⟶ cotangentSheaf piC :=
  cotangentMap f piD ≫ eqToHom (congrArg cotangentSheaf h) ≫
    cotangentToRelative piC g

theorem cotangent_differential {C B D A : Scheme} (piC : C ⟶ B) (piD : D ⟶ A)
    (f : C ⟶ D) (g : B ⟶ A) (h : f ≫ piD = piC ≫ g)
    (U : D.Opens) (z : RingSections D U) :
    (cotangent piC piD f g h).app (f ⁻¹ᵁ U)
      (pullLocalSection f (cotangentSheaf piD) U
        ((cotangentPresentation piD).differential.apply U z)) =
      (cotangentPresentation piC).differential.apply (f ⁻¹ᵁ U) (f.app U z) := by
  change (cotangentToRelative piC g).app _
    ((eqToHom (congrArg cotangentSheaf h)).app _
      ((cotangentMap f piD).app _
        (pullLocalSection f (cotangentSheaf piD) U
          ((cotangentPresentation piD).differential.apply U z)))) = _
  rw [ContactDerivativeIsoProof.cotangentMap_differential,
    ContactDerivativeIsoProof.differential_transport,
    CotangentTransitivityRederivedV02.cotangentToRelative_differential]

/-- Chain rule for arbitrary commuting squares of base schemes. -/
theorem cotangent_comp {E T C B D A : Scheme}
    (piE : E ⟶ T) (piC : C ⟶ B) (piD : D ⟶ A)
    (k : E ⟶ C) (l : T ⟶ B) (f : C ⟶ D) (g : B ⟶ A)
    (hk : k ≫ piC = piE ≫ l) (hf : f ≫ piD = piC ≫ g)
    (hcomp : (k ≫ f) ≫ piD = piE ≫ (l ≫ g)) :
    (Scheme.Modules.pullbackComp k f).hom.app (cotangentSheaf piD) ≫
        cotangent piE piD (k ≫ f) (l ≫ g) hcomp =
      (Scheme.Modules.pullback k).map (cotangent piC piD f g hf) ≫
        cotangent piE piC k l hk := by
  apply (cancel_epi ((Scheme.Modules.pullbackComp k f).inv.app
    (cotangentSheaf piD))).mp
  apply pulledCotangent_hom_ext (k ≫ f) piD
  intro U a
  change (cotangent piE piD (k ≫ f) (l ≫ g) hcomp).app ((k ≫ f) ⁻¹ᵁ U)
      (((Scheme.Modules.pullbackComp k f).hom.app (cotangentSheaf piD)).app
        ((k ≫ f) ⁻¹ᵁ U)
        (((Scheme.Modules.pullbackComp k f).inv.app (cotangentSheaf piD)).app
          ((k ≫ f) ⁻¹ᵁ U)
          (pullLocalSection (k ≫ f) (cotangentSheaf piD) U
            ((cotangentPresentation piD).differential.apply U a)))) =
    (cotangent piE piC k l hk).app ((k ≫ f) ⁻¹ᵁ U)
      (((Scheme.Modules.pullback k).map (cotangent piC piD f g hf)).app
        ((k ≫ f) ⁻¹ᵁ U)
        (((Scheme.Modules.pullbackComp k f).inv.app (cotangentSheaf piD)).app
          ((k ≫ f) ⁻¹ᵁ U)
          (pullLocalSection (k ≫ f) (cotangentSheaf piD) U
            ((cotangentPresentation piD).differential.apply U a))))
  rw [ExternalExchangeCoherenceProof.iso_hom_inv_app, cotangent_differential,
    ExternalExchangeCoherenceProof.pullLocalSection_comp_inv]
  simp only [Scheme.Hom.comp_preimage]
  rw [ExternalExchangeCoherenceProof.pullLocalSection_map,
    cotangent_differential, cotangent_differential]
  rfl

theorem cotangent_congr {C B D A : Scheme} (piC : C ⟶ B) (piD : D ⟶ A)
    {f f' : C ⟶ D} {g g' : B ⟶ A} (hf : f = f') (hg : g = g')
    (h : f ≫ piD = piC ≫ g) (h' : f' ≫ piD = piC ≫ g') :
    cotangent piC piD f g h =
      eqToHom (congrArg (fun q => pullbackModule q (cotangentSheaf piD)) hf) ≫
        cotangent piC piD f' g' h' := by
  subst f'
  subst g'
  simp

theorem cotangent_identity {C B : Scheme} (pi : C ⟶ B)
    (h : (𝟙 C) ≫ pi = pi ≫ (𝟙 B)) :
    cotangent pi pi (𝟙 C) (𝟙 B) h =
      (Scheme.Modules.pullbackId C).hom.app (cotangentSheaf pi) := by
  apply pulledCotangent_hom_ext (𝟙 C) pi
  intro U a
  rw [cotangent_differential, ExternalExchangeCoherenceProof.pullLocalSection_id]
  rfl

/-- When both bases are the original complex base, the relative map is
the original absolute cotangent differential, with its exact transport. -/
theorem cotangent_overC {d e : ℕ} (X : SmoothProperComplexVariety d)
    (Y : SmoothProperComplexVariety e) (f : X.scheme ⟶ Y.scheme)
    (hf : f ≫ Y.structureMap = X.structureMap)
    (h : f ≫ Y.structureMap = X.structureMap ≫ (𝟙 ComplexBase)) :
    cotangent X.structureMap Y.structureMap f (𝟙 ComplexBase) h =
      ContactDerivativeIsoProof.cotangentOver X Y f hf := by
  apply pulledCotangent_hom_ext f Y.structureMap
  intro U a
  rw [cotangent_differential, ContactDerivativeIsoProof.cotangentOver_differential]

theorem cotangent_baseChange {Y S T : Scheme} (f : Y ⟶ S) (g : T ⟶ S) :
    cotangent (pullback.snd f g) f (pullback.fst f g) g pullback.condition =
      CotangentBaseChange.canonicalMap f g := rfl

/-- A section of a Cartesian source family identifies the pulled
relative cotangent sheaf with the original cotangent sheaf, through the
canonical composition comparison. -/
theorem section_baseChange {Y S T : Scheme} (f : Y ⟶ S) (g : T ⟶ S)
    (b : S ⟶ T) (hb : b ≫ g = 𝟙 S)
    (j : Y ⟶ pullback f g) (hj₁ : j ≫ pullback.fst f g = 𝟙 Y)
    (hj₂ : j ≫ pullback.snd f g = f ≫ b) :
    (Scheme.Modules.pullback j).map (CotangentBaseChange.canonicalMap f g) ≫
        cotangent f (pullback.snd f g) j b hj₂ =
      (compositionPullback j (pullback.fst f g) (𝟙 Y) hj₁
        (cotangentSheaf f)).hom ≫ (Scheme.Modules.pullbackId Y).hom.app (cotangentSheaf f) := by
  have hcomp : (j ≫ pullback.fst f g) ≫ f = f ≫ (b ≫ g) := by
    rw [hj₁, hb]
    simp
  rw [← cotangent_baseChange f g]
  rw [← cotangent_comp f (pullback.snd f g) f j b (pullback.fst f g) g
    hj₂ pullback.condition hcomp]
  rw [cotangent_congr f f hj₁ hb hcomp (by simp), cotangent_identity]
  rfl

open ContactDerivativeIsoProof

theorem dualBaseChange_identity {Y : Scheme} (E : OModule Y) :
    dualBaseChange (𝟙 Y) E =
      (Scheme.Modules.pullbackId Y).hom.app (dualSheaf E) ≫
        dualMap ((Scheme.Modules.pullbackId Y).hom.app E) := by
  apply dual_pullback_hom_ext (𝟙 Y) (dualSheaf E) E
  intro U v w
  change (dualEvaluation (pullbackModule (𝟙 Y) E)).apply U
      ((dualBaseChange (𝟙 Y) E).app U
        (pullLocalSection (𝟙 Y) (dualSheaf E) U v))
      (pullLocalSection (𝟙 Y) E U w) =
    (dualEvaluation (pullbackModule (𝟙 Y) E)).apply U
      ((dualMap ((Scheme.Modules.pullbackId Y).hom.app E)).app U
        (((Scheme.Modules.pullbackId Y).hom.app (dualSheaf E)).app U
          (pullLocalSection (𝟙 Y) (dualSheaf E) U v)))
      (pullLocalSection (𝟙 Y) E U w)
  rw [dualBaseChange_evaluate, pullbackPair_normalized,
    unitPullbackMap_pullLocalSection, ExternalExchangeCoherenceProof.pullLocalSection_id,
    dualMap_evaluate, ExternalExchangeCoherenceProof.pullLocalSection_id]
  rfl

theorem dualBaseChange_equality {Y X : Scheme} {f g : Y ⟶ X}
    (h : f = g) (E : OModule X) :
    dualBaseChange f E =
      eqToHom (congrArg (fun q => pullbackModule q (dualSheaf E)) h) ≫
        dualBaseChange g E ≫
          dualMap (eqToHom (congrArg (fun q => pullbackModule q E) h)) := by
  subst g
  simp only [eqToHom_refl, Category.id_comp, dualMap_id, Category.comp_id]

def sectionPullbackIso {Y C : Scheme} (j : Y ⟶ C) (p : C ⟶ Y)
    (h : j ≫ p = 𝟙 Y) (E : OModule Y) : pullbackModule j (pullbackModule p E) ≅ E :=
  compositionPullback j p (𝟙 Y) h E ≪≫ (Scheme.Modules.pullbackId Y).app E

/-- The canonical cotangent and tangent comparisons along a split
pullback are dual to each other with no choice of scalar. -/
theorem dualBaseChange_section {Y C : Scheme} (j : Y ⟶ C) (p : C ⟶ Y)
    (h : j ≫ p = 𝟙 Y) (E : OModule Y) :
    (Scheme.Modules.pullback j).map (dualBaseChange p E) ≫
        dualBaseChange j (pullbackModule p E) =
      (sectionPullbackIso j p h (dualSheaf E)).hom ≫
        dualMap (sectionPullbackIso j p h E).hom := by
  have hc := congrArg (fun k => k ≫
    dualMap ((Scheme.Modules.pullbackComp j p).hom.app E))
      (dualBaseChange_comp j p E)
  simp only [Category.assoc, ← dualMap_comp, Iso.hom_inv_id_app,
    dualMap_id, Category.comp_id] at hc
  rw [dualBaseChange_equality h E, dualBaseChange_identity] at hc
  simp only [sectionPullbackIso, compositionPullback, Iso.trans_hom,
    Iso.app_hom, eqToIso.hom, dualMap_comp, Category.assoc] at hc ⊢
  exact hc.symm

end LeBrunSalamon.Construction.RelativeDifferential

end

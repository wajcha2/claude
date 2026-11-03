import RecompileBasePart05B

/-!
The canonical projection-formula map and its unit/global-section translation.
Only the generic finite-locally-free projection formula is a published input.
This draft remains outside source/ pending native verification and review.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.Skeleton LeBrunSalamon.Skeleton.PullbackPairProof

namespace LeBrunSalamon.ProjectionFormulaProof

/-- The actual projection-formula pairing: e tensor z maps to f*e tensor z.
The second variable is a section on the inverse-image open, so it is not
silently replaced by the pullback of a section on the base. -/
def projectionPair {X Y : Scheme} (f : X ⟶ Y) (E : OModule Y) (F : OModule X) :
    SheafBilinearMap E ((Scheme.Modules.pushforward f).obj F)
      ((Scheme.Modules.pushforward f).obj (tensorSheaf (pullbackModule f E) F)) where
  apply U :=
    { toFun := fun e =>
        { toFun := fun z =>
            (tensorPresentation (pullbackModule f E) F).pair.apply (f ⁻¹ᵁ U)
              (pullLocalSection f E U e) z
          map_add' := by intro z z'; exact map_add _ z z'
          map_smul' := by
            intro a z
            change (tensorPresentation (pullbackModule f E) F).pair.apply (f ⁻¹ᵁ U)
                (pullLocalSection f E U e)
                (f.app U a • (show SectionsOn F (f ⁻¹ᵁ U) from z)) =
              f.app U a • (tensorPresentation (pullbackModule f E) F).pair.apply (f ⁻¹ᵁ U)
                (pullLocalSection f E U e) z
            exact map_smul _ _ _ }
      map_add' := by
        intro e e'
        apply LinearMap.ext
        intro z
        change (tensorPresentation (pullbackModule f E) F).pair.apply (f ⁻¹ᵁ U)
            (pullLocalSection f E U (e + e')) z = _
        rw [pullLocalSection_add, map_add, LinearMap.add_apply]
        rfl
      map_smul' := by
        intro a e
        apply LinearMap.ext
        intro z
        change (tensorPresentation (pullbackModule f E) F).pair.apply (f ⁻¹ᵁ U)
            (pullLocalSection f E U (a • e)) z =
          f.app U a • (tensorPresentation (pullbackModule f E) F).pair.apply (f ⁻¹ᵁ U)
            (pullLocalSection f E U e) z
        rw [pullLocalSection_smul, map_smul, LinearMap.smul_apply] }
  naturality := by
    intro U V i e z
    change (tensorSheaf (pullbackModule f E) F).presheaf.map
        ((TopologicalSpace.Opens.map f.base).map i).op
        ((tensorPresentation (pullbackModule f E) F).pair.apply (f ⁻¹ᵁ V)
          (pullLocalSection f E V e) z) = _
    rw [(tensorPresentation (pullbackModule f E) F).pair.naturality,
      pullLocalSection_restrict]
    rfl

def canonicalMap {X Y : Scheme} (f : X ⟶ Y) (E : OModule Y) (F : OModule X) :
    tensorSheaf E ((Scheme.Modules.pushforward f).obj F) ⟶
      (Scheme.Modules.pushforward f).obj (tensorSheaf (pullbackModule f E) F) :=
  tensorLift (projectionPair f E F)

theorem canonicalMap_pair {X Y : Scheme} (f : X ⟶ Y)
    (E : OModule Y) (F : OModule X) (U : Y.Opens)
    (e : SectionsOn E U) (z : SectionsOn F (f ⁻¹ᵁ U)) :
    (canonicalMap f E F).app U
        ((tensorPresentation E ((Scheme.Modules.pushforward f).obj F)).pair.apply U e z) =
      (tensorPresentation (pullbackModule f E) F).pair.apply (f ⁻¹ᵁ U)
        (pullLocalSection f E U e) z := by
  exact congrArg (fun b => b.apply U e z) (tensorLift_pair (projectionPair f E F))

end LeBrunSalamon.ProjectionFormulaProof

namespace LeBrunSalamon.PublishedInputs.ProjectionFormula

/-- Stacks Project, Lemma 20.54.2, Tag 01E8, degree zero. For a morphism of
ringed spaces and a finite locally free module E, the canonical map
E tensor f_*F -> f_*(f*E tensor F) is invertible. The local generators below
are free trivializations with finite indexing sets; the rank may vary.
https://stacks.math.columbia.edu/tag/01E8

The map is defined and normalized in projectionPair/canonicalMap_pair. No
structure-sheaf-descent hypothesis or project section-bijection conclusion
is included in this published leaf.
-/
theorem canonicalMap_isIso {X Y : Scheme} (f : X ⟶ Y)
    (E : OModule Y) (F : OModule X)
    (q : SheafOfModules.LocalGeneratorsData.{0} E) [q.IsLocallyFreeData]
    (hq : ∀ i : q.I, Finite (q.generators i).I) :
    IsIso (LeBrunSalamon.ProjectionFormulaProof.canonicalMap f E F) := by
  sorry

end LeBrunSalamon.PublishedInputs.ProjectionFormula

namespace LeBrunSalamon.ProjectionFormulaProof

/-- The unit specialization is proved on the actual tensor pairing. -/
theorem unit_comparison {X Y : Scheme} (f : X ⟶ Y) (E : OModule Y) :
    tensorMap (𝟙 E) (structurePushforwardMap f) ≫ canonicalMap f E (structureModule X) ≫
        (Scheme.Modules.pushforward f).map (TensorConstruction.rightUnitIso (pullbackModule f E)).hom =
      (TensorConstruction.rightUnitIso E).hom ≫
        (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app E := by
  apply ((tensorPresentation E (structureModule Y)).universal _).injective
  apply sheafBilinearMap_ext
  intro U e a
  change (TensorConstruction.rightUnitIso (pullbackModule f E)).hom.app (f ⁻¹ᵁ U)
      ((canonicalMap f E (structureModule X)).app U
        ((tensorMap (𝟙 E) (structurePushforwardMap f)).app U
          ((tensorPresentation E (structureModule Y)).pair.apply U e a))) =
    pullLocalSection f E U
      ((TensorConstruction.rightUnitIso E).hom.app U
        ((tensorPresentation E (structureModule Y)).pair.apply U e a))
  rw [tensorMap_apply, canonicalMap_pair, TensorConstruction.rightUnitIso_hom_pair,
    TensorConstruction.rightUnitIso_hom_pair, pullLocalSection_smul]
  rfl

theorem unit_isIso {X Y : Scheme} (f : X ⟶ Y)
    (hf : IsIso (structurePushforwardMap f)) {r : ℕ}
    (E : AlgebraicVectorBundle Y r) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app E.sheaf) := by
  letI := hf
  obtain ⟨q, hq, hr⟩ := E.locallyFree
  letI := hq
  have hfinite (i : q.I) : Finite (q.generators i).I :=
    Finite.of_equiv (Fin r) (Classical.choice (hr i)).symm
  letI := PublishedInputs.ProjectionFormula.canonicalMap_isIso f E.sheaf
    (structureModule X) q hfinite
  let e : E.sheaf ≅ (Scheme.Modules.pushforward f).obj (pullbackModule f E.sheaf) :=
    (TensorConstruction.rightUnitIso E.sheaf).symm ≪≫
      tensorIso (Iso.refl E.sheaf) (asIso (structurePushforwardMap f)) ≪≫
      asIso (canonicalMap f E.sheaf (structureModule X)) ≪≫
      (Scheme.Modules.pushforward f).mapIso
        (TensorConstruction.rightUnitIso (pullbackModule f E.sheaf))
  have he : e.hom = (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app E.sheaf := by
    change (TensorConstruction.rightUnitIso E.sheaf).inv ≫
      (tensorMap (𝟙 E.sheaf) (structurePushforwardMap f) ≫
        canonicalMap f E.sheaf (structureModule X) ≫
          (Scheme.Modules.pushforward f).map
            (TensorConstruction.rightUnitIso (pullbackModule f E.sheaf)).hom) = _
    rw [unit_comparison]
    simp
  rw [← he]
  infer_instance

/-- The final global-section step uses the adjunction and the proved unit
isomorphism, with the original canonical pullSection map unchanged. -/
theorem sections_bijective {X Y : Scheme} (f : X ⟶ Y)
    (hf : IsIso (structurePushforwardMap f)) {r : ℕ}
    (E : AlgebraicVectorBundle Y r) :
    Function.Bijective (pullSection f (E := E.sheaf)) := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f
  letI := unit_isIso f hf E
  constructor
  · intro a b hab
    apply (cancel_mono (adj.unit.app E.sheaf)).mp
    rw [← pullSection_adjoint f a, ← pullSection_adjoint f b, hab]
  · intro v
    let a : AlgebraicSection E.sheaf :=
      adj.homEquiv _ _ (unitPullbackMap f ≫ v) ≫ inv (adj.unit.app E.sheaf)
    refine ⟨a, ?_⟩
    letI := unitPullbackMap_isIso f
    apply (cancel_epi (unitPullbackMap f)).mp
    rw [unitPullbackMap_pullSection]
    apply (adj.homEquiv _ _).injective
    have ha : adj.homEquiv _ _ ((Scheme.Modules.pullback f).map a) =
        a ≫ adj.unit.app E.sheaf := by
      rw [adj.homEquiv_apply]
      exact (adj.unit.naturality a).symm
    rw [ha]
    dsimp [a]
    simp

end LeBrunSalamon.ProjectionFormulaProof

end

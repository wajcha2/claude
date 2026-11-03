import RecompileBasePart04

/-!
# Sectionwise exactness gives an actual sheaf short exact sequence

This criterion only uses the existing module-category kernels and the
pointwise construction of presheaf limits. It introduces no admission.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne

namespace LeBrunSalamon.SheafSectionExact

theorem shortExact_of_sections {X : Scheme} {A B C : OModule X}
    (f : A ⟶ B) (g : B ⟶ C) (hfg : f ≫ g = 0)
    (hf : ∀ U : X.Opens, Function.Injective (f.app U))
    (hg : ∀ U : X.Opens, Function.Surjective (g.app U))
    (hex : ∀ U : X.Opens, Function.Exact (f.app U) (g.app U)) :
    (ShortComplex.mk f g hfg).ShortExact := by
  letI : Mono f := ⟨by
    intro Z a b hab
    apply Scheme.Modules.hom_ext
    intro U
    ext z
    apply hf U
    exact congrArg (fun q : Z ⟶ B => q.app U z) hab⟩
  letI : Epi g := ⟨by
    intro Z a b hab
    apply Scheme.Modules.hom_ext
    intro U
    ext z
    obtain ⟨w, rfl⟩ := hg U z
    exact congrArg (fun q : B ⟶ Z => q.app U w) hab⟩
  have hk : IsLimit (KernelFork.ofι f hfg) := by
    let K := KernelFork.ofι f hfg
    let forgetModules := SheafOfModules.forget X.ringCatSheaf
    letI : forgetModules.Additive := inferInstanceAs
      (SheafOfModules.forget X.ringCatSheaf).Additive
    apply isLimitOfReflects forgetModules
    change IsLimit (forgetModules.mapCone K)
    refine (K.isLimitMapConeEquiv forgetModules).symm ?_
    apply PresheafOfModules.evaluationJointlyReflectsLimits _ _
    intro U
    refine ((K.map forgetModules).isLimitMapConeEquiv
      (PresheafOfModules.evaluation X.ringCatSheaf.obj U)).symm ?_
    exact ModuleCat.isLimitKernelFork (f.val.app U) (g.val.app U)
      (hex U.unop) (hf U.unop)
  exact ⟨(ShortComplex.mk f g hfg).exact_of_f_is_kernel hk⟩

end LeBrunSalamon.SheafSectionExact
end

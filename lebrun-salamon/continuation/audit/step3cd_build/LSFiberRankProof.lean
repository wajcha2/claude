import RecompileExtensionsPart02
import Mathlib.Algebra.Category.ModuleCat.Products

/-!
An independent proof candidate for the two Step 3d fiber-rank obligations.
This diagnostic file imports the current interface but does not use either
historically admitted fiber-rank theorem. Once checked, its proof belongs just
before those declarations in RecompileExtensionsPart02.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.Construction

namespace LeBrunSalamon.FiberRankProof

/-- Evaluation of a finite free sheaf is a finite free module. -/
def finiteFreeSectionsEquiv
    {C : Type} [Category.{0} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat) [HasSheafify J AddCommGrpCat]
    [J.WEqualsLocallyBijective AddCommGrpCat]
    (U : Cᵒᵖ) (r : ℕ) :
    (SheafOfModules.free (R := R) (Fin r)).val.obj U ≃ₗ[R.obj.obj U]
      (Fin r → R.obj.obj U) := by
  let F := SheafOfModules.evaluation R U
  let family := fun _ : Fin r => SheafOfModules.unit R
  letI : HasBiproduct family := HasBiproduct.of_hasProduct family
  let e := F.mapIso (biproductIso family).symm ≪≫
    asIso (piComparison F family) ≪≫ ModuleCat.piIsoPi (fun i => F.obj (family i))
  exact e.toLinearEquiv

/-- The actual complex scalar action is transported through ΓSpecIso, not
through a chosen abstract field isomorphism. -/
def complexSectionsEquiv (G : OModule ComplexBase) {r : ℕ}
    (e : GlobalSections G ≃ₗ[RingSections ComplexBase ⊤]
      (Fin r → RingSections ComplexBase ⊤)) :
    CSections (𝟙 ComplexBase) G ≃ₗ[ℂ] (Fin r → ℂ) := by
  let γ := Scheme.ΓSpecIso (CommRingCat.of ℂ)
  let f : CSections (𝟙 ComplexBase) G →ₗ[ℂ] (Fin r → ℂ) :=
    { toFun := fun v i => γ.hom (e v i)
      map_add' := by
        intro v w
        ext i
        simp only [map_add, Pi.add_apply]
      map_smul' := by
        intro c v
        ext i
        change γ.hom (e (complexConstants (𝟙 ComplexBase) c •
          (show GlobalSections G from v)) i) =
          c * γ.hom (e v i)
        rw [e.map_smul]
        change γ.hom (complexConstants (𝟙 ComplexBase) c * e v i) = _
        rw [map_mul, complexConstants_apply_top]
        change γ.hom (γ.inv c) * γ.hom (e v i) = _
        simp }
  apply LinearEquiv.ofBijective f
  constructor
  · intro v w h
    apply e.injective
    ext i
    apply (ConcreteCategory.bijective_of_isIso γ.hom).injective
    exact congrFun h i
  · intro v
    obtain ⟨w, hw⟩ := e.surjective (fun i => γ.inv (v i))
    refine ⟨w, ?_⟩
    ext i
    change γ.hom (e w i) = v i
    rw [hw]
    simp

/-- Pulling an actual local frame through the point's factorization gives a
global free frame on Spec ℂ. This avoids any admitted pullback-rank theorem. -/
theorem fiber_freeIso {X : Scheme} {r : ℕ}
    (E : AlgebraicVectorBundle X r) (x : ComplexBase ⟶ X) :
    Nonempty (SheafOfModules.free (R := ComplexBase.ringCatSheaf) (Fin r) ≅
      pullbackModule x E.sheaf) := by
  obtain ⟨q, hq, hr⟩ := E.locallyFree
  letI := hq
  obtain ⟨i, hi⟩ :=
    ((_root_.Opens.coversTop_iff X q.X).mp q.coversTop).exists_mem
      (x (IsLocalRing.closedPoint ℂ))
  let U : X.Opens := q.X i
  have hxU : Set.range x ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    change x z ∈ U
    rw [Subsingleton.elim z (IsLocalRing.closedPoint ℂ)]
    exact hi
  let g := IsOpenImmersion.lift U.ι x hxU
  have hg : g ≫ U.ι = x := IsOpenImmersion.lift_fac U.ι x hxU
  let F := Scheme.Modules.pullback g
  letI : F.IsLeftAdjoint :=
    (SheafOfModules.pullbackPushforwardAdjunction g.toRingCatSheafHom).isLeftAdjoint
  let freePullback := SheafOfModules.mapFreeIso F (Fin r) (unitPullbackIso g).symm
  let e := DominantSectionInjectivityProof.localFreePullbackIso q hr i
  let comp : pullbackModule g (pullbackModule U.ι E.sheaf) ≅
      pullbackModule x E.sheaf :=
    (Scheme.Modules.pullbackComp g U.ι).app E.sheaf ≪≫
      (Scheme.Modules.pullbackCongr hg).app E.sheaf
  exact ⟨freePullback ≪≫ F.mapIso e ≪≫ comp⟩

/-- Explicit finite-dimensional model for the original fiber definition. -/
theorem fiber_linearEquiv {X : Scheme} {r : ℕ}
    (E : AlgebraicVectorBundle X r) (x : ComplexBase ⟶ X) :
    Nonempty (Fiber E.sheaf x ≃ₗ[ℂ] (Fin r → ℂ)) := by
  obtain ⟨e⟩ := fiber_freeIso E x
  let eΓ : GlobalSections (SheafOfModules.free (R := ComplexBase.ringCatSheaf) (Fin r))
      ≃ₗ[RingSections ComplexBase ⊤] GlobalSections (pullbackModule x E.sheaf) :=
    ((SheafOfModules.evaluation ComplexBase.ringCatSheaf (op ⊤)).mapIso e).toLinearEquiv
  let eFree := finiteFreeSectionsEquiv ComplexBase.ringCatSheaf (op ⊤) r
  exact ⟨complexSectionsEquiv (pullbackModule x E.sheaf) (eΓ.symm.trans eFree)⟩

/-- Both former fiber-rank claims follow from the same actual equivalence. -/
theorem fiber_rank_and_finite {X : Scheme} {r : ℕ}
    (E : AlgebraicVectorBundle X r) (x : ComplexBase ⟶ X) :
    Module.finrank ℂ (Fiber E.sheaf x) = r ∧
      FiniteDimensional ℂ (Fiber E.sheaf x) := by
  obtain ⟨e⟩ := fiber_linearEquiv E x
  refine ⟨?_, ?_⟩
  · simpa using e.finrank_eq
  · exact Module.Finite.of_injective e.toLinearMap e.injective

end LeBrunSalamon.FiberRankProof

end

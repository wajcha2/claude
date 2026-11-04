import LSVectorBundlePullback
import LSFiberRankProof

/-! Fiber specialization of the proved actual pullback sequence.
The extra fiber-rank import is the already checked isolated diagnostic helper;
the final proof belongs after the corresponding definitions in Ext02. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction

namespace LeBrunSalamon.VectorBundlePullback

/-- The existing actual frame on the field-valued point proves the
quasi-coherence required for the affine section-surjectivity theorem. -/
theorem fiber_quasicoherent {X : Scheme.{0}} {r : ℕ}
    (E : AlgebraicVectorBundle X r) (x : ComplexBase ⟶ X) :
    (pullbackModule x E.sheaf).IsQuasicoherent := by
  obtain ⟨e⟩ := FiberRankProof.fiber_freeIso E x
  exact LocalExtensionSplitting.quasicoherent_of_locallyFreeRank
    (locallyFreeOfRank_iso e (freeSheaf_rank ComplexBase r))

/-- Injectivity, surjectivity and image/kernel equality for the actual
fiber maps. No abstract replacement vector spaces or chosen linear maps
are substituted for the project's canonical pullback/global-section maps. -/
theorem vectorBundle_fiber_exact {X : Scheme.{0}} {a b c : ℕ}
    (E : AlgebraicVectorBundle X a) (F : AlgebraicVectorBundle X b)
    (G : AlgebraicVectorBundle X c) (i : E.sheaf ⟶ F.sheaf) (q : F.sheaf ⟶ G.sheaf)
    (h0 : i ≫ q = 0) (h : (ShortComplex.mk i q h0).ShortExact)
    (x : ComplexBase ⟶ X) :
    Function.Injective (fiberMap i x) ∧ Function.Surjective (fiberMap q x) ∧
      LinearMap.range (fiberMap i x) = LinearMap.ker (fiberMap q x) := by
  let H := Scheme.Modules.pullback x
  have hex := vectorBundle_pullback_shortExact x E F G i q h0 h
  letI : Mono (H.map i) := hex.mono_f
  letI : Epi (H.map q) := hex.epi_g
  letI : (pullbackModule x F.sheaf).IsQuasicoherent := fiber_quasicoherent F x
  letI : (pullbackModule x G.sheaf).IsQuasicoherent := fiber_quasicoherent G x
  have hz : H.map i ≫ H.map q = 0 := by rw [← H.map_comp, h0, H.map_zero]
  refine ⟨ExtensionGluing.sectionMap_injective (H.map i) ⊤,
    LocalExtensionSplitting.spec_sectionMap_surjective (H.map q), ?_⟩
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    change (H.map q).app ⊤ ((H.map i).app ⊤ w) = 0
    have he := congrArg (fun f => f.app ⊤ w) hz
    exact he
  · intro hv
    change (H.map q).app ⊤ v = 0 at hv
    obtain ⟨w, hw, _⟩ :=
      ExtensionGluing.existsUnique_kernelSection (H.map i) (H.map q) hz hex ⊤ v hv
    exact ⟨w, hw⟩

end LeBrunSalamon.VectorBundlePullback

end

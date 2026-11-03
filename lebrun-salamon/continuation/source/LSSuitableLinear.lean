import LSSuitableDirections

/-!
## Suitable pairs: spanning, the dimension-three endpoint, and actual fibers

Source: pinned OpenAI manuscript, `lines:suitable-pair` and its separate
dimension-three argument. This continuation has not been compiled: the user
has deferred the next compilation until the integrated source reaches 35k lines.

The algebra below uses the union of the component cones. No individual cone is
assumed to span. The final constructor consumes the actual derivative-sum map
and the actual endpoint-fixed evaluation spaces already used by `SuitablePair`.
Its geometric inputs remain visible hypotheses; this is not a construction of
the fixed-value Hom scheme or a proof of generic smoothness for that scheme.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseThree LeBrunSalamon.PhaseSeven
open LeBrunSalamon.PhaseEight LeBrunSalamon.PhaseTen
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.PhaseThirty LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.PhaseThirtyFour LeBrunSalamon.PhaseThirtyFive
open LeBrunSalamon.Core LeBrunSalamon.Skeleton

namespace LeBrunSalamon.Construction.Lines.SuitablePairAlgebra

section Spanning

variable {K V W : Type*} [Field K]
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup W] [Module K W]

/-- Orthogonality to a set extends to its linear span, in the first slot. -/
theorem pairing_zero_on_span_left (ω : V →ₗ[K] V →ₗ[K] W)
    (S : Set V) (b : V) (h : ∀ a ∈ S, ω a b = 0)
    {a : V} (ha : a ∈ Submodule.span K S) : ω a b = 0 := by
  have hker : Submodule.span K S ≤ LinearMap.ker (ω.flip b) := by
    apply Submodule.span_le.mpr
    intro v hv
    change ω v b = 0
    exact h v hv
  exact hker ha

/-- The second-slot version keeps the pairing valued in its original module;
no frame of a one-dimensional value space is needed. -/
theorem pairing_zero_on_span_right (ω : V →ₗ[K] V →ₗ[K] W)
    (T : Set V) (a : V) (h : ∀ b ∈ T, ω a b = 0)
    {b : V} (hb : b ∈ Submodule.span K T) : ω a b = 0 := by
  have hker : Submodule.span K T ≤ LinearMap.ker (ω a) := by
    apply Submodule.span_le.mpr
    intro v hv
    exact h v hv
  exact hker hb

theorem pairing_zero_on_spans (ω : V →ₗ[K] V →ₗ[K] W)
    (S T : Set V) (h : ∀ a ∈ S, ∀ b ∈ T, ω a b = 0)
    {a b : V} (ha : a ∈ Submodule.span K S)
    (hb : b ∈ Submodule.span K T) : ω a b = 0 := by
  apply pairing_zero_on_span_left ω S b _ ha
  intro v hv
  exact pairing_zero_on_span_right ω T v (h v hv) hb

/-- Vanishing on two spanning sets forces the whole bilinear map to vanish. -/
theorem pairing_eq_zero_of_spanning (ω : V →ₗ[K] V →ₗ[K] W)
    (S T : Set V) (hS : Submodule.span K S = ⊤)
    (hT : Submodule.span K T = ⊤)
    (h : ∀ a ∈ S, ∀ b ∈ T, ω a b = 0) : ω = 0 := by
  ext a b
  apply pairing_zero_on_spans ω S T h
  · rw [hS]
    trivial
  · rw [hT]
    trivial

/-- The two nonorthogonal vectors can be selected from the generators
themselves, rather than from unspecified linear combinations. -/
theorem exists_nonorthogonal_generators (ω : V →ₗ[K] V →ₗ[K] W)
    (hω : ω ≠ 0) (S T : Set V)
    (hS : Submodule.span K S = ⊤) (hT : Submodule.span K T = ⊤) :
    ∃ a ∈ S, ∃ b ∈ T, ω a b ≠ 0 := by
  classical
  by_contra h
  apply hω
  apply pairing_eq_zero_of_spanning ω S T hS hT
  intro a ha b hb
  by_contra hab
  exact h ⟨a, ha, b, hb, hab⟩

/-- This is the selection step used for a possibly disconnected direction
variety. Only the union spans. The two component indices may coincide. -/
theorem exists_nonorthogonal_components {ι : Type*}
    (ω : V →ₗ[K] V →ₗ[K] W) (hω : ω ≠ 0) (U : ι → Set V)
    (hU : Submodule.span K (⋃ i, U i) = ⊤) :
    ∃ i j, ∃ a ∈ U i, ∃ b ∈ U j, ω a b ≠ 0 := by
  obtain ⟨a, ha, b, hb, hab⟩ :=
    exists_nonorthogonal_generators ω hω (⋃ i, U i) (⋃ i, U i) hU hU
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ha
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hb
  exact ⟨i, j, a, hi, b, hj, hab⟩

/-- Nondegeneracy is used only to rule out the zero pairing. In applications,
`v₀` is any nonzero vector in the positive-dimensional contact plane. -/
theorem exists_nonorthogonal_components_of_nondegenerate {ι : Type*}
    (ω : V →ₗ[K] V →ₗ[K] W)
    (hnd : ∀ a : V, (∀ b : V, ω a b = 0) → a = 0)
    (v₀ : V) (hv₀ : v₀ ≠ 0) (U : ι → Set V)
    (hU : Submodule.span K (⋃ i, U i) = ⊤) :
    ∃ i j, ∃ a ∈ U i, ∃ b ∈ U j, ω a b ≠ 0 := by
  apply exists_nonorthogonal_components ω _ U hU
  intro hzero
  apply hv₀
  apply hnd v₀
  intro b
  simp only [hzero, LinearMap.zero_apply]

theorem nonorthogonal_left_ne_zero (ω : V →ₗ[K] V →ₗ[K] W)
    {a b : V} (h : ω a b ≠ 0) : a ≠ 0 := by
  intro ha
  apply h
  simp [ha]

theorem nonorthogonal_right_ne_zero (ω : V →ₗ[K] V →ₗ[K] W)
    {a b : V} (h : ω a b ≠ 0) : b ≠ 0 := by
  intro hb
  apply h
  simp [hb]

/-- Distinct projective directions follow from the nonzero pairing itself. -/
theorem nonorthogonal_not_scalar_multiple (ω : V →ₗ[K] V →ₗ[K] W)
    (halt : ∀ a : V, ω a a = 0) {a b : V} (hab : ω a b ≠ 0)
    (c : K) : b ≠ c • a := by
  intro h
  apply hab
  rw [h, map_smul, halt a, smul_zero]

end Spanning

section SymplecticPlane

variable {K V W : Type*} [Field K]
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup W] [Module K W]

/-- The linear addition map for two affine lines through the origin. -/
def twoVectorSum (a b : V) : K × K →ₗ[K] V :=
  (LinearMap.toSpanSingleton K V a).coprod (LinearMap.toSpanSingleton K V b)

@[simp]
theorem twoVectorSum_apply (a b : V) (r s : K) :
    twoVectorSum a b (r, s) = r • a + s • b := rfl

/-- Nonzero alternating pairing makes the two-vector sum injective in any
dimension. The argument retains an arbitrary module as value space. -/
theorem twoVectorSum_injective (ω : V →ₗ[K] V →ₗ[K] W)
    (halt : ∀ a : V, ω a a = 0) {a b : V} (hab : ω a b ≠ 0) :
    Function.Injective (twoVectorSum (K := K) a b) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  rintro ⟨r, s⟩ hrs
  change r • a + s • b = 0 at hrs
  have hr : r • ω a b = 0 := by
    have h := congrArg (fun v : V => ω v b) hrs
    simpa only [map_add, LinearMap.add_apply, map_smul,
      LinearMap.smul_apply, halt b, smul_zero, add_zero,
      map_zero, LinearMap.zero_apply] using h
  have hs : s • ω a b = 0 := by
    have h := congrArg (fun v : V => ω a v) hrs
    simpa only [map_add, map_smul, halt a, smul_zero, zero_add, map_zero] using h
  apply Prod.ext
  · exact (smul_eq_zero.mp hr).resolve_right hab
  · exact (smul_eq_zero.mp hs).resolve_right hab

/-- The `n = 1` endpoint: addition of the two nonorthogonal lines is a
linear isomorphism onto the symplectic plane. No higher-dimensional
Legendrian smoothness theorem enters this argument. -/
theorem twoVectorSum_bijective [FiniteDimensional K V]
    (hV : Module.finrank K V = 2) (ω : V →ₗ[K] V →ₗ[K] W)
    (halt : ∀ a : V, ω a a = 0) {a b : V} (hab : ω a b ≠ 0) :
    Function.Bijective (twoVectorSum (K := K) a b) := by
  have hinj := twoVectorSum_injective ω halt hab
  refine ⟨hinj, ?_⟩
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (show Module.finrank K (K × K) = Module.finrank K V by
      simp [Module.finrank_prod, CommSemiring.finrank_self, hV])).mp
  exact hinj

def twoVectorEquiv [FiniteDimensional K V]
    (hV : Module.finrank K V = 2) (ω : V →ₗ[K] V →ₗ[K] W)
    (halt : ∀ a : V, ω a a = 0) (a b : V) (hab : ω a b ≠ 0) :
    (K × K) ≃ₗ[K] V :=
  LinearEquiv.ofBijective (twoVectorSum a b) (twoVectorSum_bijective hV ω halt hab)

@[simp]
theorem twoVectorEquiv_apply [FiniteDimensional K V]
    (hV : Module.finrank K V = 2) (ω : V →ₗ[K] V →ₗ[K] W)
    (halt : ∀ a : V, ω a a = 0) (a b : V) (hab : ω a b ≠ 0) (r s : K) :
    twoVectorEquiv hV ω halt a b hab (r, s) = r • a + s • b := rfl

theorem plane_lines_span [FiniteDimensional K V]
    (hV : Module.finrank K V = 2) (ω : V →ₗ[K] V →ₗ[K] W)
    (halt : ∀ a : V, ω a a = 0) {a b : V} (hab : ω a b ≠ 0) :
    Submodule.span K {a} ⊔ Submodule.span K {b} = ⊤ := by
  rw [← LinearMap.range_toSpanSingleton a, ← LinearMap.range_toSpanSingleton b,
    ← LinearMap.range_coprod]
  exact LinearMap.range_eq_top.mpr (twoVectorSum_bijective hV ω halt hab).2

end SymplecticPlane

/-! The declarations formerly in this block were moved, with their
proofs unchanged, into RecompileExtensions before the three original
positive-node theorems. This module retains its public import path.
Source-order relocation: ActualContactFibers. No additional axiom is introduced. -/

section DerivativeSum

variable {K V A B : Type*} [Field K]
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup A] [Module K A]
variable [AddCommGroup B] [Module K B]

/-- The algebraic end of the suitable-pair argument. A surjective sum of
two variation maps, each landing in its prescribed positive subspace,
forces those subspaces to fill the ambient contact hyperplane. -/
theorem sup_eq_of_surjective_sum (F P Q : Submodule K V)
    (hP : P ≤ F) (hQ : Q ≤ F) (d₁ : A →ₗ[K] F) (d₂ : B →ₗ[K] F)
    (h₁ : ∀ a, (d₁ a : V) ∈ P) (h₂ : ∀ b, (d₂ b : V) ∈ Q)
    (hsurj : Function.Surjective (d₁.coprod d₂)) : P ⊔ Q = F := by
  apply le_antisymm (sup_le hP hQ)
  intro v hv
  obtain ⟨⟨a, b⟩, hab⟩ := hsurj ⟨v, hv⟩
  have heq : (d₁ a : V) + (d₂ b : V) = v :=
    congrArg (fun z : F => (z : V)) hab
  rw [← heq]
  exact Submodule.add_mem_sup (h₁ a) (h₂ b)

/-- A common parameter space is also allowed: the two coordinate variations
may come from a single tangent vector. Independence of parameters is not
needed for the range-containment conclusion. -/
theorem sup_eq_of_surjective_joint_variation (F P Q : Submodule K V)
    (hP : P ≤ F) (hQ : Q ≤ F) (d₁ d₂ : A →ₗ[K] F)
    (h₁ : ∀ a, (d₁ a : V) ∈ P) (h₂ : ∀ a, (d₂ a : V) ∈ Q)
    (hsurj : Function.Surjective (d₁ + d₂)) : P ⊔ Q = F := by
  apply le_antisymm (sup_le hP hQ)
  intro v hv
  obtain ⟨a, ha⟩ := hsurj ⟨v, hv⟩
  have heq : (d₁ a : V) + (d₂ a : V) = v :=
    congrArg (fun z : F => (z : V)) ha
  rw [← heq]
  exact Submodule.add_mem_sup (h₁ a) (h₂ a)

end DerivativeSum

section ActualSuitablePair

variable {n : ℕ} {X : ContactFanoManifold n}
variable {A B : Type*} [AddCommGroup A] [Module ℂ A]
variable [AddCommGroup B] [Module ℂ B]

/-- Assemble the original `SuitablePair`, with its original curve maps,
canonical differentials and actual positive evaluation subspaces.

The source-specific work still needed at a geometric application is precisely
the construction of `d₁`, `d₂`, their landing identities, and their surjective
sum. Neither those facts nor suitable-pair existence are postulated globally.
The nonzero source parameters are derived from the actual Levi test.
-/
def suitablePair_of_surjective_variation (x : ComplexPoint X.variety)
    (f g : FreeLine X) (hf : marking.map ≫ f.curve.map = x.map)
    (hg : marking.map ≫ g.curve.map = x.map)
    (p q : Fiber (tangentSheaf P.structureMap) marking.map)
    (htrans : NonzeroLeviPair X x (nodeDifferential f x hf p) (nodeDifferential g x hg q))
    (d₁ : A →ₗ[ℂ] contactPlane X x) (d₂ : B →ₗ[ℂ] contactPlane X x)
    (h₁ : ∀ a, (d₁ a : TangentFiber X.variety x) ∈ positiveNodeSpace f x hf)
    (h₂ : ∀ b, (d₂ b : TangentFiber X.variety x) ∈ positiveNodeSpace g x hg)
    (hsurj : Function.Surjective (d₁.coprod d₂)) : SuitablePair X where
  node := x
  first := f
  second := g
  firstAtNode := hf
  secondAtNode := hg
  firstParameter := p
  secondParameter := q
  firstParameter_ne := by
    intro hp
    apply nonzeroLeviPair_left_ne_zero X x htrans
    rw [hp, map_zero]
  secondParameter_ne := by
    intro hq
    apply nonzeroLeviPair_right_ne_zero X x htrans
    rw [hq, map_zero]
  spans := sup_eq_of_surjective_sum (contactPlane X x)
    (positiveNodeSpace f x hf) (positiveNodeSpace g x hg)
    (positiveNodeSpace_horizontal f x hf) (positiveNodeSpace_horizontal g x hg)
    d₁ d₂ h₁ h₂ hsurj
  transverse := htrans

end ActualSuitablePair

/-- In complex dimension three, the linear-plane argument supplies the
surjective sum directly. The tangent vectors must belong to the actual
positive spaces; that geometric comparison remains an explicit input.
Alternation is the intrinsic Levi-fiber obligation, not the higher-dimensional
Legendrian theorem, whose hypothesis `n ≥ 2` does not apply here. -/
def dimensionThree_suitablePair_of_tangents (X : ContactFanoManifold 1)
    (x : ComplexPoint X.variety) (f g : FreeLine X)
    (hf : marking.map ≫ f.curve.map = x.map)
    (hg : marking.map ≫ g.curve.map = x.map)
    (p q : Fiber (tangentSheaf P.structureMap) marking.map)
    (hp : nodeDifferential f x hf p ∈ positiveNodeSpace f x hf)
    (hq : nodeDifferential g x hg q ∈ positiveNodeSpace g x hg)
    (htrans : NonzeroLeviPair X x (nodeDifferential f x hf p) (nodeDifferential g x hg q))
    (halt : ∀ a : contactPlane X x, contactLevi X x a a = 0) : SuitablePair X := by
  letI : FiniteDimensional ℂ (TangentFiber X.variety x) :=
    fiber_finite (intrinsicTangentBundle X.variety) x.map
  let a : contactPlane X x :=
    ⟨nodeDifferential f x hf p, positiveNodeSpace_horizontal f x hf hp⟩
  let b : contactPlane X x :=
    ⟨nodeDifferential g x hg q, positiveNodeSpace_horizontal g x hg hq⟩
  have hab : contactLevi X x a b ≠ 0 :=
    (nonzeroLeviPair_iff_contactLevi X x a b).mp htrans
  have hdim : Module.finrank ℂ (contactPlane X x) = 2 := by
    simpa using contactPlane_dimension X x
  let d₁ := LinearMap.toSpanSingleton ℂ (contactPlane X x) a
  let d₂ := LinearMap.toSpanSingleton ℂ (contactPlane X x) b
  have h₁ : ∀ c : ℂ, (d₁ c : TangentFiber X.variety x) ∈ positiveNodeSpace f x hf := by
    intro c
    change c • nodeDifferential f x hf p ∈ positiveNodeSpace f x hf
    exact (positiveNodeSpace f x hf).smul_mem c hp
  have h₂ : ∀ c : ℂ, (d₂ c : TangentFiber X.variety x) ∈ positiveNodeSpace g x hg := by
    intro c
    change c • nodeDifferential g x hg q ∈ positiveNodeSpace g x hg
    exact (positiveNodeSpace g x hg).smul_mem c hq
  have hsurj : Function.Surjective (d₁.coprod d₂) :=
    (twoVectorSum_bijective hdim (contactLevi X x) halt hab).2
  exact suitablePair_of_surjective_variation x f g hf hg p q htrans d₁ d₂ h₁ h₂ hsurj

end LeBrunSalamon.Construction.Lines.SuitablePairAlgebra

end

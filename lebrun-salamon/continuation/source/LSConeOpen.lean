import LSSuitableDirections
import LSConePole

/-!
## Projective component separation and the actual nonorthogonal open

Source: the pinned manuscript, `lines:cone-addition`.  This continuation
uses the existing closed projective embedding, its actual complex points,
the component cone coordinate rings, and their tensor-product spectrum.
No additional geometric existence, dominance, or smoothness assertion is
introduced.  The standard geometric production of irreducible open
neighborhoods and of irreducible cone products remains a separate task.

UNCOMPILED: respect the user's 35,000-line incremental compilation gate.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseThree LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentySix LeBrunSalamon.PhaseTwentySeven
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.Skeleton
open scoped TensorProduct BigOperators

namespace LeBrunSalamon.Construction.Lines.ConeGeometry

open DirectionCones

/-! ### The projective embedding remembers its actual complex point -/

section ComponentSeparation
variable {N : ℕ} (D : ReducedProjectiveDirections N)
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable (e : V ≃ₗ[ℂ] (Fin (N+1) → ℂ))

/-- Equality of directions first gives equality of the represented
projective points.  Cancellation of the actual closed immersion then
gives equality of the complex points of the direction scheme. -/
theorem direction_injective : Function.Injective (D.direction e) := by
  intro z w h
  obtain ⟨c, hc⟩ :=
    (Projectivization.mk_eq_mk_iff' ℂ
      (e.symm (D.coordinateRepresentative w))
      (e.symm (D.coordinateRepresentative z))
      (D.representative_ne_zero e w) (D.representative_ne_zero e z)).mp h.symm
  have hc0 : c ≠ 0 := by
    intro hc0
    apply D.representative_ne_zero e w
    simpa only [hc0, zero_smul] using hc.symm
  have hcoords : D.coordinateRepresentative w = c • D.coordinateRepresentative z := by
    simpa only [map_smul, e.apply_symm_apply] using (congrArg e hc).symm
  have hpoints : D.projectivePoint z = D.projectivePoint w :=
    (projectiveCoordinates_samePoint_iff (projectiveCoordinates N)
      (D.projectivePoint z) (D.projectivePoint w)
      (D.coordinateRepresentative z) (D.coordinateRepresentative w)
      (D.coordinateRepresentative_spec z) (D.coordinateRepresentative_spec w)).mpr
        ⟨c, hc0, hcoords⟩
  apply Subtype.ext
  apply (cancel_mono D.embedding).mp
  exact congrArg Subtype.val hpoints

/-- Membership in a component can be read using any point of `Spec ℂ`.
This removes the existential choices in `componentDirections` without
identifying scheme morphisms merely from their underlying topological map. -/
theorem direction_mem_component_iff (C : D.Component) (z : D.Points)
    (p : ComplexBase) :
    D.direction e z ∈ D.componentDirections e C ↔ z.val p ∈ C.val := by
  constructor
  · rintro ⟨w, q, hq, hd⟩
    have hw : w = z := direction_injective D e hd
    subst w
    have hqp : q = p := Subsingleton.elim _ _
    simpa only [hqp] using hq
  · intro hp
    exact ⟨z, p, hp, rfl⟩

/-- Disjointness is an assertion about the actual projective components;
injectivity transfers it to their sets of vector-space directions. -/
theorem componentDirections_disjoint (C E : D.Component)
    (hCE : Disjoint C.val E.val) :
    Disjoint (D.componentDirections e C) (D.componentDirections e E) := by
  apply Set.disjoint_left.mpr
  rintro d ⟨z, p, hz, hzd⟩ hdE
  have hzE : z.val p ∈ E.val :=
    (direction_mem_component_iff D e E z p).mp (hzd.symm ▸ hdE)
  exact Set.disjoint_left.mp hCE hz hzE

theorem componentDirections_pairwiseDisjoint
    (hdisj : Pairwise (fun C E : D.Component => Disjoint C.val E.val)) :
    Pairwise (fun C E : D.Component =>
      Disjoint (D.componentDirections e C) (D.componentDirections e E)) := by
  intro C E hCE
  exact componentDirections_disjoint D e C E (hdisj hCE)

theorem mem_componentConePoints_iff (C : D.Component) (v : Fin (N+1) → ℂ) :
    v ∈ D.componentConePoints e C ↔
      e.symm v ∈ projectiveCone (D.componentDirections e C) := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa only [e.symm_apply_apply] using hw
  · intro h
    exact ⟨e.symm v, h, e.apply_symm_apply v⟩

/-- Distinct projective components have cone intersection equal to the
vertex, even when the full direction variety is disconnected. -/
theorem componentConePoints_inter_eq_vertex (C E : D.Component)
    (hCE : Disjoint C.val E.val) :
    D.componentConePoints e C ∩ D.componentConePoints e E = {0} := by
  ext v
  constructor
  · rintro ⟨hvC, hvE⟩
    have hz : e.symm v = 0 :=
      cone_intersection_of_disjoint (componentDirections_disjoint D e C E hCE)
        ((mem_componentConePoints_iff D e C v).mp hvC)
        ((mem_componentConePoints_iff D e E v).mp hvE)
    have hv : v = 0 := by
      simpa only [e.apply_symm_apply, map_zero] using congrArg e hz
    exact Set.mem_singleton_iff.mpr hv
  · intro hv
    have hv0 : v = 0 := Set.mem_singleton_iff.mp hv
    subst v
    exact ⟨D.zero_mem_componentConePoints e C, D.zero_mem_componentConePoints e E⟩

/-- The common nonzero rescaled limit in the pole argument identifies
the two actual component indices.  No component-spanning premise occurs. -/
theorem component_eq_of_common_nonzero
    (hdisj : Pairwise (fun C E : D.Component => Disjoint C.val E.val))
    {C E : D.Component} {v : Fin (N+1) → ℂ} (hv : v ≠ 0)
    (hvC : v ∈ D.componentConePoints e C) (hvE : v ∈ D.componentConePoints e E) :
    C = E := by
  by_contra hCE
  have hmem : v ∈ ({0} : Set (Fin (N+1) → ℂ)) := by
    rw [← componentConePoints_inter_eq_vertex D e C E (hdisj hCE)]
    exact ⟨hvC, hvE⟩
  exact hv (Set.mem_singleton_iff.mp hmem)

end ComponentSeparation

/-! ### A topological separation step for smooth direction geometry -/

section IrreducibleNeighborhoods
variable {T : Type*} [TopologicalSpace T]

/-- An irreducible open neighborhood meeting a component is contained in
that component.  Its proof uses maximality and density of the open
intersection, and so does not assume component disjointness. -/
theorem irreducibleOpen_subset_component
    {C : Set T} (hC : C ∈ irreducibleComponents T)
    (U : TopologicalSpace.Opens T) (hU : IsPreirreducible (U : Set T))
    (hmeet : (C ∩ (U : Set T)).Nonempty) : (U : Set T) ⊆ C := by
  have hUne : (U : Set T).Nonempty := hmeet.mono Set.inter_subset_right
  obtain ⟨E, hE, hUE⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible (U : Set T) ⟨hUne, hU⟩
  have hCE : C ⊆ E := by
    refine (subset_closure_inter_of_isPreirreducible_of_isOpen hC.1.2 U.isOpen hmeet).trans ?_
    apply (isClosed_of_mem_irreducibleComponents E hE).closure_subset_iff.mpr
    exact Set.inter_subset_right.trans hUE
  exact hUE.trans (hC.2 hE.1 hCE)

/-- Locally irreducible neighborhoods force two components through the
same point to agree.  The later standard smoothness bridge must provide
the displayed open neighborhoods of the actual direction scheme. -/
theorem component_eq_of_irreducible_neighborhoods
    (hlocal : ∀ x : T, ∃ U : TopologicalSpace.Opens T,
      x ∈ U ∧ IsPreirreducible (U : Set T))
    {C E : Set T} (hC : C ∈ irreducibleComponents T)
    (hE : E ∈ irreducibleComponents T) {x : T} (hxC : x ∈ C) (hxE : x ∈ E) :
    C = E := by
  obtain ⟨U, hxU, hU⟩ := hlocal x
  have hUE : (U : Set T) ⊆ E :=
    irreducibleOpen_subset_component hE U hU ⟨x, hxE, hxU⟩
  have hCE : C ⊆ E := by
    refine (subset_closure_inter_of_isPreirreducible_of_isOpen
      hC.1.2 U.isOpen ⟨x, hxC, hxU⟩).trans ?_
    apply (isClosed_of_mem_irreducibleComponents E hE).closure_subset_iff.mpr
    exact Set.inter_subset_right.trans hUE
  exact Set.Subset.antisymm hCE (hC.2 hE.1 hCE)

theorem components_pairwiseDisjoint_of_irreducible_neighborhoods
    (hlocal : ∀ x : T, ∃ U : TopologicalSpace.Opens T,
      x ∈ U ∧ IsPreirreducible (U : Set T)) :
    Pairwise (fun C E : {C : Set T // C ∈ irreducibleComponents T} =>
      Disjoint C.val E.val) := by
  intro C E hCE
  apply Set.disjoint_left.mpr
  intro x hxC hxE
  apply hCE
  apply Subtype.ext
  exact component_eq_of_irreducible_neighborhoods hlocal C.property E.property hxC hxE

end IrreducibleNeighborhoods

theorem component_eq_of_common_nonzero_of_irreducible_neighborhoods
    {N : ℕ} (D : ReducedProjectiveDirections N)
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (e : V ≃ₗ[ℂ] (Fin (N+1) → ℂ))
    (hlocal : ∀ x : D.scheme, ∃ U : D.scheme.Opens,
      x ∈ U ∧ IsPreirreducible (U : Set D.scheme))
    {C E : D.Component} {v : Fin (N+1) → ℂ} (hv : v ≠ 0)
    (hvC : v ∈ D.componentConePoints e C) (hvE : v ∈ D.componentConePoints e E) :
    C = E :=
  component_eq_of_common_nonzero D e
    (components_pairwiseDisjoint_of_irreducible_neighborhoods hlocal) hv hvC hvE

/-! ### The principal open of the actual regular cross-pairing -/

section NonorthogonalOpen
variable {I : Type} [Fintype I]

/-- The bilinear pairing as an element of the genuine product coordinate
ring, using the two actual tensor-factor coordinate pullbacks. -/
def pairingFunction (S T : Set (I → ℂ)) (ω : I → I → ℂ) : ProductRing S T :=
  ConePairing.pairing ω (firstCoordinate S T) (secondCoordinate S T)

/-- The nonorthogonality condition is the principal Zariski open of the
actual product spectrum.  It is not an arbitrary open set with a witness. -/
def nonorthogonalOpen (S T : Set (I → ℂ)) (ω : I → I → ℂ) :
    (productScheme S T).Opens :=
  PrimeSpectrum.basicOpen (pairingFunction S T ω)

theorem productEvaluation_pairingFunction (S T : Set (I → ℂ))
    (ω : I → I → ℂ) (a b : I → ℂ) (ha : a ∈ S) (hb : b ∈ T) :
    productEvaluation S T a b ha hb (pairingFunction S T ω) =
      ConePairing.pairing ω a b := by
  simpa only [pairingFunction, productEvaluation_first, productEvaluation_second] using
    (ConePairing.pairing_map (productEvaluation S T a b ha hb) ω
      (firstCoordinate S T) (secondCoordinate S T))

/-- Any complex-valued algebra point belongs to a principal open exactly
when the defining regular function has nonzero complex value. -/
theorem affineMap_mem_basicOpen {A : Type} [CommRing A] [Algebra ℂ A]
    (q : A →ₐ[ℂ] ℂ) (f : A) (p : ComplexBase) :
    affineMap q p ∈ PrimeSpectrum.basicOpen f ↔ q f ≠ 0 := by
  change q f ∉ (show PrimeSpectrum ℂ from p).asIdeal ↔ q f ≠ 0
  have hp : (show PrimeSpectrum ℂ from p) = ⊥ := Subsingleton.elim _ _
  simp only [hp, PrimeSpectrum.asIdeal_bot, Ideal.mem_bot]

theorem pairPoint_mem_nonorthogonalOpen (S T : Set (I → ℂ))
    (ω : I → I → ℂ) (a b : I → ℂ) (ha : a ∈ S) (hb : b ∈ T)
    (p : ComplexBase) :
    pairPoint S T a b ha hb p ∈ nonorthogonalOpen S T ω ↔
      ConePairing.pairing ω a b ≠ 0 := by
  rw [nonorthogonalOpen, pairPoint,
    affineMap_mem_basicOpen, productEvaluation_pairingFunction]

theorem pairPoint_preimage_nonorthogonalOpen (S T : Set (I → ℂ))
    (ω : I → I → ℂ) (a b : I → ℂ) (ha : a ∈ S) (hb : b ∈ T) :
    pairPoint S T a b ha hb ⁻¹ᵁ nonorthogonalOpen S T ω =
      PrimeSpectrum.basicOpen (ConePairing.pairing ω a b) := by
  unfold pairPoint affineMap nonorthogonalOpen
  rw [SpecMap_preimage_basicOpen]
  exact congrArg (fun c : ℂ => PrimeSpectrum.basicOpen c)
    (productEvaluation_pairingFunction S T ω a b ha hb)

theorem nonorthogonalOpen_nonempty (S T : Set (I → ℂ))
    (ω : I → I → ℂ) (a b : I → ℂ) (ha : a ∈ S) (hb : b ∈ T)
    (hω : ConePairing.pairing ω a b ≠ 0) :
    (nonorthogonalOpen S T ω : Set (productScheme S T)).Nonempty := by
  let p : ComplexBase := Classical.choice (inferInstance : Nonempty ComplexBase)
  exact ⟨pairPoint S T a b ha hb p,
    (pairPoint_mem_nonorthogonalOpen S T ω a b ha hb p).mpr hω⟩

theorem pairingFunction_ne_zero_of_witness (S T : Set (I → ℂ))
    (ω : I → I → ℂ) (a b : I → ℂ) (ha : a ∈ S) (hb : b ∈ T)
    (hω : ConePairing.pairing ω a b ≠ 0) : pairingFunction S T ω ≠ 0 := by
  intro hzero
  have heval := productEvaluation_pairingFunction S T ω a b ha hb
  rw [hzero, map_zero] at heval
  exact hω heval.symm

/-- Both projections of a nonorthogonal pair lie away from their cone
vertices.  These are genuine unions of principal opens on the product. -/
def firstPuncturedOpen (S T : Set (I → ℂ)) : (productScheme S T).Opens :=
  ⨆ i : I, PrimeSpectrum.basicOpen (firstCoordinate S T i)

def secondPuncturedOpen (S T : Set (I → ℂ)) : (productScheme S T).Opens :=
  ⨆ i : I, PrimeSpectrum.basicOpen (secondCoordinate S T i)

theorem nonorthogonalOpen_le_firstPuncturedOpen (S T : Set (I → ℂ))
    (ω : I → I → ℂ) : nonorthogonalOpen S T ω ≤ firstPuncturedOpen S T := by
  classical
  intro p hp
  apply TopologicalSpace.Opens.mem_iSup.mpr
  by_contra hn
  have hc : ∀ i, firstCoordinate S T i ∈ p.asIdeal := by
    intro i
    by_contra hi
    exact hn ⟨i, hi⟩
  apply hp
  change (∑ i, ∑ j, firstCoordinate S T i *
    algebraMap ℂ (ProductRing S T) (ω i j) * secondCoordinate S T j) ∈ p.asIdeal
  apply p.asIdeal.sum_mem
  intro i _
  apply p.asIdeal.sum_mem
  intro j _
  exact p.asIdeal.mul_mem_right _ (p.asIdeal.mul_mem_right _ (hc i))

theorem nonorthogonalOpen_le_secondPuncturedOpen (S T : Set (I → ℂ))
    (ω : I → I → ℂ) : nonorthogonalOpen S T ω ≤ secondPuncturedOpen S T := by
  classical
  intro p hp
  apply TopologicalSpace.Opens.mem_iSup.mpr
  by_contra hn
  have hc : ∀ j, secondCoordinate S T j ∈ p.asIdeal := by
    intro j
    by_contra hj
    exact hn ⟨j, hj⟩
  apply hp
  change (∑ i, ∑ j, firstCoordinate S T i *
    algebraMap ℂ (ProductRing S T) (ω i j) * secondCoordinate S T j) ∈ p.asIdeal
  apply p.asIdeal.sum_mem
  intro i _
  apply p.asIdeal.sum_mem
  intro j _
  exact p.asIdeal.mul_mem_left _ (hc j)

theorem nonorthogonalOpen_le_puncturedProduct (S T : Set (I → ℂ))
    (ω : I → I → ℂ) :
    nonorthogonalOpen S T ω ≤ firstPuncturedOpen S T ⊓ secondPuncturedOpen S T :=
  le_inf (nonorthogonalOpen_le_firstPuncturedOpen S T ω)
    (nonorthogonalOpen_le_secondPuncturedOpen S T ω)

/-- The nonorthogonal complex-pair morphism factors through that actual
open subscheme, by the universal property of an open immersion. -/
def nonorthogonalPairPoint (S T : Set (I → ℂ)) (ω : I → I → ℂ)
    (a b : I → ℂ) (ha : a ∈ S) (hb : b ∈ T)
    (hω : ConePairing.pairing ω a b ≠ 0) :
    ComplexBase ⟶ (nonorthogonalOpen S T ω).toScheme :=
  IsOpenImmersion.lift (nonorthogonalOpen S T ω).ι (pairPoint S T a b ha hb) (by
    rw [Scheme.Opens.range_ι]
    rintro z ⟨p, rfl⟩
    exact (pairPoint_mem_nonorthogonalOpen S T ω a b ha hb p).mpr hω)

@[reassoc] theorem nonorthogonalPairPoint_ι (S T : Set (I → ℂ))
    (ω : I → I → ℂ) (a b : I → ℂ) (ha : a ∈ S) (hb : b ∈ T)
    (hω : ConePairing.pairing ω a b ≠ 0) :
    nonorthogonalPairPoint S T ω a b ha hb hω ≫ (nonorthogonalOpen S T ω).ι =
      pairPoint S T a b ha hb :=
  IsOpenImmersion.lift_fac _ _ _

/-- Addition restricted to the actual nonorthogonality open. -/
def nonorthogonalAddition (S T : Set (I → ℂ)) (ω : I → I → ℂ) :
    (nonorthogonalOpen S T ω).toScheme ⟶ affineSpace I :=
  (nonorthogonalOpen S T ω).ι ≫ additionMorphism S T

theorem nonorthogonalAddition_overC (S T : Set (I → ℂ)) (ω : I → I → ℂ) :
    nonorthogonalAddition S T ω ≫ affineBaseMap (CoordinatePolynomial I) =
      (nonorthogonalOpen S T ω).ι ≫ affineBaseMap (ProductRing S T) := by
  rw [nonorthogonalAddition, Category.assoc, additionMorphism_overC]

theorem nonorthogonalPairPoint_addition (S T : Set (I → ℂ))
    (ω : I → I → ℂ) (a b : I → ℂ) (ha : a ∈ S) (hb : b ∈ T)
    (hω : ConePairing.pairing ω a b ≠ 0) :
    nonorthogonalPairPoint S T ω a b ha hb hω ≫ nonorthogonalAddition S T ω =
      coordinatePoint (a+b) := by
  rw [nonorthogonalAddition, ← Category.assoc, nonorthogonalPairPoint_ι,
    pairPoint_addition]

end NonorthogonalOpen

/-! ### Generic conditions can be imposed inside the nonorthogonal open -/

section GenericOpen
variable {I : Type} [Fintype I]
variable (S T : Set (I → ℂ)) (ω : I → I → ℂ)
variable [IrreducibleSpace (productScheme S T)]

/-- Irreducibility belongs to the actual spectrum of the tensor-product
ring.  It is not inferred from irreducibility of arbitrary point sets. -/
theorem nonorthogonalOpen_dense (a b : I → ℂ) (ha : a ∈ S) (hb : b ∈ T)
    (hω : ConePairing.pairing ω a b ≠ 0) :
    Dense (nonorthogonalOpen S T ω : Set (productScheme S T)) :=
  (nonorthogonalOpen S T ω).isOpen.dense
    (nonorthogonalOpen_nonempty S T ω a b ha hb hω)

/-- In the nondominance argument, the positive-fiber-dimension locus can
be intersected with the nonorthogonality open using this theorem. -/
theorem nonorthogonalOpen_inter_nonempty (a b : I → ℂ)
    (ha : a ∈ S) (hb : b ∈ T) (hω : ConePairing.pairing ω a b ≠ 0)
    (G : (productScheme S T).Opens) (hG : (G : Set (productScheme S T)).Nonempty) :
    ((nonorthogonalOpen S T ω : Set (productScheme S T)) ∩ G).Nonempty :=
  nonempty_preirreducible_inter (nonorthogonalOpen S T ω).isOpen G.isOpen
    (nonorthogonalOpen_nonempty S T ω a b ha hb hω) hG

/-- Two independent generic open conditions can be retained at once,
as required when the fiber-dimension and smoothness loci are combined. -/
theorem nonorthogonalOpen_inter_two_nonempty (a b : I → ℂ)
    (ha : a ∈ S) (hb : b ∈ T) (hω : ConePairing.pairing ω a b ≠ 0)
    (G H : (productScheme S T).Opens)
    (hG : (G : Set (productScheme S T)).Nonempty)
    (hH : (H : Set (productScheme S T)).Nonempty) :
    ((nonorthogonalOpen S T ω : Set (productScheme S T)) ∩ G ∩ H).Nonempty := by
  exact nonempty_preirreducible_inter
    ((nonorthogonalOpen S T ω).isOpen.inter G.isOpen) H.isOpen
    (nonorthogonalOpen_inter_nonempty S T ω a b ha hb hω G hG) hH

/-- Restricting a dominant actual addition morphism to this nonempty
open preserves dominance.  This prepares the generic-smoothness step
after the manuscript's pole contradiction has proved dominance. -/
theorem nonorthogonalAddition_denseRange (a b : I → ℂ)
    (ha : a ∈ S) (hb : b ∈ T) (hω : ConePairing.pairing ω a b ≠ 0)
    (hadd : DenseRange (fun z => additionMorphism S T z)) :
    DenseRange (fun z => nonorthogonalAddition S T ω z) := by
  have hinc : DenseRange (fun z => (nonorthogonalOpen S T ω).ι z) := by
    change Dense (Set.range (nonorthogonalOpen S T ω).ι)
    rw [Scheme.Opens.range_ι]
    exact nonorthogonalOpen_dense S T ω a b ha hb hω
  simpa only [nonorthogonalAddition, Scheme.Hom.comp_apply,
    Function.comp_def] using hadd.comp hinc (additionMorphism S T).continuous

end GenericOpen

/-! ### The selected family predicate comes from actual parameters -/

section CoveringSelector
variable {n : ℕ} {X : ContactFanoManifold n}

/-- Membership in this selected family is witnessed by an actual complex
parameter of the existing covering family, not by all free contact lines. -/
def coveringSelector (F : CoveringFamily X) (f : FreeLine X) : Prop :=
  ∃ t : PointsOver ComplexBase (𝟙 ComplexBase) F.parameter F.toC, F.lineAt t = f

theorem coveringSelector_lineAt (F : CoveringFamily X)
    (t : PointsOver ComplexBase (𝟙 ComplexBase) F.parameter F.toC) :
    coveringSelector F (F.lineAt t) := ⟨t, rfl⟩

/-- The selected vector is the node differential of a fiber of the
actual universal evaluation map, via `CoveringFamily.lineAt_spec`. -/
theorem isSelectedVector_coveringSelector_iff (F : CoveringFamily X)
    (x : ComplexPoint X.variety) (v : contactPlane X x) :
    IsSelectedVector (coveringSelector F) x v ↔
      ∃ t : PointsOver ComplexBase (𝟙 ComplexBase) F.parameter F.toC,
        ∃ hx : marking.map ≫ (F.lineAt t).curve.map = x.map,
          ∃ u : Fiber (tangentSheaf P.structureMap) marking.map,
            nodeDifferential (F.lineAt t) x hx u = (v : TangentFiber X.variety x) := by
  constructor
  · rintro ⟨f, ⟨t, rfl⟩, hx, u, hu⟩
    exact ⟨t, hx, u, hu⟩
  · rintro ⟨t, hx, u, hu⟩
    exact ⟨F.lineAt t, coveringSelector_lineAt F t, hx, u, hu⟩

theorem coveringSelector_curve_is_evaluation (F : CoveringFamily X)
    (f : FreeLine X) (hf : coveringSelector F f) :
    ∃ t : PointsOver ComplexBase (𝟙 ComplexBase) F.parameter F.toC,
      f.curve.map = pullback.lift (𝟙 ProjectiveLine) (P.structureMap ≫ t.val)
        (by simp [Category.assoc, t.property]) ≫ F.evaluation := by
  obtain ⟨t, rfl⟩ := hf
  exact ⟨t, F.lineAt_spec t⟩

end CoveringSelector

end LeBrunSalamon.Construction.Lines.ConeGeometry

end

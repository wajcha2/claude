import RecompileTail

/-!
## Selected contact directions and their concrete affine cone schemes

Source: the pinned OpenAI manuscript, `lines:cone-addition` and
`lines:suitable-pair`.  This continuation has not been compiled: the user
has requested the next compiler run only when the integrated source reaches
35,000 lines.

The selected family is retained explicitly.  The published direction theorem
concerns a covering family (or an allowed union of its components); it does
not assert a generic splitting type for every free contact line.  Affine
schemes below are actual spectra of coordinate algebras.  For an arbitrary
point set they represent its reduced Zariski closure; exact identification
with the point set is expressed separately by `EquationClosed`.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseThree LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseSeven
open LeBrunSalamon.PhaseTwentySix LeBrunSalamon.PhaseTwentySeven
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.Skeleton
open scoped TensorProduct

namespace LeBrunSalamon.Construction.Lines.DirectionCones

/-! ### The directions are derivatives of actual selected line maps -/

/-- A vector in the intrinsic contact plane is selected only when it is
the canonical differential of a selected actual free contact line through
the specified point.  Horizontality is not silently assumed here: the
equality has its value in the existing intrinsic contact-plane subtype. -/
def IsSelectedVector {n : ℕ} {X : ContactFanoManifold n}
    (H : FreeLine X → Prop) (x : ComplexPoint X.variety)
    (v : contactPlane X x) : Prop :=
  ∃ f : FreeLine X, H f ∧
    ∃ hx : marking.map ≫ f.curve.map = x.map,
      ∃ t : Fiber (tangentSheaf P.structureMap) marking.map,
        nodeDifferential f x hx t = (v : TangentFiber X.variety x)

theorem isSelectedVector_smul {n : ℕ} {X : ContactFanoManifold n}
    (H : FreeLine X → Prop) (x : ComplexPoint X.variety)
    {v : contactPlane X x} (hv : IsSelectedVector H x v) (c : ℂ) :
    IsSelectedVector H x (c • v) := by
  obtain ⟨f, hf, hx, t, ht⟩ := hv
  refine ⟨f, hf, hx, c • t, ?_⟩
  rw [map_smul, ht]
  rfl

theorem isSelectedVector_smul_iff {n : ℕ} {X : ContactFanoManifold n}
    (H : FreeLine X → Prop) (x : ComplexPoint X.variety)
    (v : contactPlane X x) (c : ℂ) (hc : c ≠ 0) :
    IsSelectedVector H x (c • v) ↔ IsSelectedVector H x v := by
  constructor
  · intro h
    simpa only [inv_smul_smul₀ hc] using isSelectedVector_smul H x h c⁻¹
  · intro h
    exact isSelectedVector_smul H x h c

/-- Projective directions of selected parametrized lines, using mathlib's
projectivization of the actual intrinsic contact plane. -/
def selectedDirections {n : ℕ} {X : ContactFanoManifold n}
    (H : FreeLine X → Prop) (x : ComplexPoint X.variety) :
    Set (Projectivization ℂ (contactPlane X x)) :=
  {d | ∃ v : contactPlane X x, ∃ hv : v ≠ 0,
    IsSelectedVector H x v ∧ Projectivization.mk ℂ v hv = d}

theorem selectedDirections_mono {n : ℕ} {X : ContactFanoManifold n}
    {H K : FreeLine X → Prop} (hHK : ∀ f, H f → K f)
    (x : ComplexPoint X.variety) : selectedDirections H x ⊆ selectedDirections K x := by
  rintro d ⟨v, hv, ⟨f, hf, hx, t, ht⟩, hd⟩
  exact ⟨v, hv, ⟨f, hHK f hf, hx, t, ht⟩, hd⟩

/-! ### Affine cones of sets of projective directions -/

section ProjectiveCone
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The affine cone includes its vertex, even when the set of projective
directions is empty.  No ambient topology is used in this definition. -/
def projectiveCone (Z : Set (Projectivization ℂ V)) : Set V :=
  {v | v = 0 ∨ ∃ hv : v ≠ 0, Projectivization.mk ℂ v hv ∈ Z}

theorem zero_mem_projectiveCone (Z : Set (Projectivization ℂ V)) :
    (0 : V) ∈ projectiveCone Z := Or.inl rfl

theorem mem_projectiveCone_of_ne_zero (Z : Set (Projectivization ℂ V))
    (v : V) (hv : v ≠ 0) :
    v ∈ projectiveCone Z ↔ Projectivization.mk ℂ v hv ∈ Z := by
  constructor
  · rintro (h | ⟨hv', hd⟩)
    · exact False.elim (hv h)
    · exact hd
  · intro hd
    exact Or.inr ⟨hv, hd⟩

theorem projectiveCone_mono {Z W : Set (Projectivization ℂ V)} (h : Z ⊆ W) :
    projectiveCone Z ⊆ projectiveCone W := by
  rintro v (hv | ⟨hv, hd⟩)
  · exact Or.inl hv
  · exact Or.inr ⟨hv, h hd⟩

theorem projectiveCone_smul (Z : Set (Projectivization ℂ V))
    {v : V} (hv : v ∈ projectiveCone Z) (c : ℂ) : c • v ∈ projectiveCone Z := by
  by_cases hc : c = 0
  · subst c
    simpa using zero_mem_projectiveCone Z
  rcases hv with rfl | ⟨hv, hd⟩
  · simpa using zero_mem_projectiveCone Z
  · have hcv : c • v ≠ 0 := smul_ne_zero hc hv
    refine Or.inr ⟨hcv, ?_⟩
    have heq : Projectivization.mk ℂ (c • v) hcv =
        Projectivization.mk ℂ v hv :=
      (Projectivization.mk_eq_mk_iff' ℂ _ _ hcv hv).mpr ⟨c, rfl⟩
    rw [heq]
    exact hd

theorem projectiveCone_smul_iff (Z : Set (Projectivization ℂ V))
    (v : V) (c : ℂ) (hc : c ≠ 0) :
    c • v ∈ projectiveCone Z ↔ v ∈ projectiveCone Z := by
  constructor
  · intro h
    simpa only [inv_smul_smul₀ hc] using projectiveCone_smul Z h c⁻¹
  · exact fun h => projectiveCone_smul Z h c

/-- A common nonzero vector gives a common projective direction.  This is
the component-comparison step used after rescaling a pole in the manuscript. -/
theorem cone_common_nonzero_direction {Z W : Set (Projectivization ℂ V)}
    {v : V} (hv : v ≠ 0) (hZ : v ∈ projectiveCone Z) (hW : v ∈ projectiveCone W) :
    ∃ d, d ∈ Z ∧ d ∈ W :=
  ⟨Projectivization.mk ℂ v hv,
    (mem_projectiveCone_of_ne_zero Z v hv).mp hZ,
    (mem_projectiveCone_of_ne_zero W v hv).mp hW⟩

theorem cone_intersection_of_disjoint {Z W : Set (Projectivization ℂ V)}
    (h : Disjoint Z W) {v : V} (hZ : v ∈ projectiveCone Z)
    (hW : v ∈ projectiveCone W) : v = 0 := by
  by_contra hv
  obtain ⟨d, hdZ, hdW⟩ := cone_common_nonzero_direction hv hZ hW
  exact Set.disjoint_left.mp h hdZ hdW

/-- This lemma permits disconnected direction varieties: only distinct
components are required to be disjoint; no component is required to span. -/
theorem cone_component_eq_of_common_nonzero {I : Type*}
    (Z : I → Set (Projectivization ℂ V))
    (hdisj : Pairwise (fun i j => Disjoint (Z i) (Z j)))
    {i j : I} {v : V} (hv : v ≠ 0)
    (hi : v ∈ projectiveCone (Z i)) (hj : v ∈ projectiveCone (Z j)) : i = j := by
  by_contra hij
  exact hv (cone_intersection_of_disjoint (hdisj hij) hi hj)

end ProjectiveCone

/-- Nonzero vectors of the cone of actual selected directions are again
actual differential values.  This uses source-tangent rescaling, not a
postulated ability to realize arbitrary points of an unrelated variety. -/
theorem selectedCone_nonzero_iff {n : ℕ} {X : ContactFanoManifold n}
    (H : FreeLine X → Prop) (x : ComplexPoint X.variety)
    (v : contactPlane X x) (hv : v ≠ 0) :
    v ∈ projectiveCone (selectedDirections H x) ↔ IsSelectedVector H x v := by
  rw [mem_projectiveCone_of_ne_zero _ v hv]
  constructor
  · rintro ⟨w, hw, hselected, hdir⟩
    obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' ℂ v w hv hw).mp hdir.symm
    rw [← hc]
    exact isSelectedVector_smul H x hselected c
  · intro h
    exact ⟨v, hv, h, rfl⟩

/-! ### Polynomial coordinate rings of reduced affine closures -/

section CoordinateRings
variable {I : Type}

abbrev CoordinatePolynomial (I : Type) := MvPolynomial I ℂ

/-- The ideal of all polynomials vanishing on the specified coordinate
points.  Its definition makes its link to those points explicit. -/
def vanishingIdeal (S : Set (I → ℂ)) : Ideal (CoordinatePolynomial I) where
  carrier := {p | ∀ v ∈ S, MvPolynomial.eval v p = 0}
  zero_mem' := by intro v hv; exact map_zero _
  add_mem' := by
    intro p q hp hq v hv
    rw [map_add, hp v hv, hq v hv, add_zero]
  smul_mem' := by
    intro p q hq v hv
    change MvPolynomial.eval v (p * q) = 0
    rw [map_mul, hq v hv, mul_zero]

@[simp] theorem mem_vanishingIdeal (S : Set (I → ℂ)) (p : CoordinatePolynomial I) :
    p ∈ vanishingIdeal S ↔ ∀ v ∈ S, MvPolynomial.eval v p = 0 := Iff.rfl

theorem vanishingIdeal_antitone {S T : Set (I → ℂ)} (h : S ⊆ T) :
    vanishingIdeal T ≤ vanishingIdeal S := fun _ hp v hv => hp v (h hv)

theorem vanishingIdeal_union (S T : Set (I → ℂ)) :
    vanishingIdeal (S ∪ T) = vanishingIdeal S ⊓ vanishingIdeal T := by
  ext p
  constructor
  · intro h
    exact ⟨fun v hv => h v (Or.inl hv), fun v hv => h v (Or.inr hv)⟩
  · rintro ⟨hS, hT⟩ v (hv | hv)
    · exact hS v hv
    · exact hT v hv

theorem vanishingIdeal_isRadical (S : Set (I → ℂ)) :
    (vanishingIdeal S).IsRadical := by
  intro p hp
  obtain ⟨k, hk⟩ := hp
  intro v hv
  apply eq_zero_of_pow_eq_zero (n := k)
  simpa only [map_pow] using hk v hv

abbrev CoordinateRing (S : Set (I → ℂ)) :=
  CoordinatePolynomial I ⧸ vanishingIdeal S

instance coordinateRing_reduced (S : Set (I → ℂ)) : _root_.IsReduced (CoordinateRing S) :=
  (Ideal.isRadical_iff_quotient_reduced (vanishingIdeal S)).mp
    (vanishingIdeal_isRadical S)

def coordinate (S : Set (I → ℂ)) (i : I) : CoordinateRing S :=
  Ideal.Quotient.mk (vanishingIdeal S) (MvPolynomial.X i)

/-- Exact membership in an algebraic set requires the reverse implication
of the vanishing equations.  It is deliberately separate from the generic
reduced-closure construction. -/
def EquationClosed (S : Set (I → ℂ)) : Prop :=
  ∀ v : I → ℂ, (∀ p ∈ vanishingIdeal S, MvPolynomial.eval v p = 0) → v ∈ S

def quotientEvaluation (S : Set (I → ℂ)) (v : I → ℂ) (hv : v ∈ S) :
    CoordinateRing S →ₐ[ℂ] ℂ :=
  Ideal.Quotient.liftₐ (vanishingIdeal S) (MvPolynomial.aeval v)
    (fun p hp => hp v hv)

@[simp] theorem quotientEvaluation_mk (S : Set (I → ℂ)) (v : I → ℂ)
    (hv : v ∈ S) (p : CoordinatePolynomial I) :
    quotientEvaluation S v hv (Ideal.Quotient.mk (vanishingIdeal S) p) =
      MvPolynomial.eval v p := rfl

@[simp] theorem quotientEvaluation_coordinate (S : Set (I → ℂ)) (v : I → ℂ)
    (hv : v ∈ S) (i : I) : quotientEvaluation S v hv (coordinate S i) = v i := by
  exact MvPolynomial.eval_X i

/-- Coordinates recover every complex algebra point of the quotient.
This is polynomial freeness, before any appeal to the Nullstellensatz. -/
theorem quotientPoint_polynomial (S : Set (I → ℂ))
    (q : CoordinateRing S →ₐ[ℂ] ℂ) (p : CoordinatePolynomial I) :
    q (Ideal.Quotient.mk (vanishingIdeal S) p) =
      MvPolynomial.eval (fun i => q (coordinate S i)) p := by
  have h : q.comp (Ideal.Quotient.mkₐ ℂ (vanishingIdeal S)) =
      MvPolynomial.aeval (fun i => q (coordinate S i)) := by
    ext i
    simp [coordinate]
  exact congrArg (fun f : CoordinatePolynomial I →ₐ[ℂ] ℂ => f p) h

theorem quotientPoint_satisfiesEquations (S : Set (I → ℂ))
    (q : CoordinateRing S →ₐ[ℂ] ℂ) (p : CoordinatePolynomial I)
    (hp : p ∈ vanishingIdeal S) :
    MvPolynomial.eval (fun i => q (coordinate S i)) p = 0 := by
  rw [← quotientPoint_polynomial]
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]

theorem quotientPoint_mem (S : Set (I → ℂ)) (hS : EquationClosed S)
    (q : CoordinateRing S →ₐ[ℂ] ℂ) : (fun i => q (coordinate S i)) ∈ S :=
  hS _ (quotientPoint_satisfiesEquations S q)

theorem quotientPoint_ext (S : Set (I → ℂ))
    {p q : CoordinateRing S →ₐ[ℂ] ℂ}
    (h : ∀ i, p (coordinate S i) = q (coordinate S i)) : p = q := by
  apply Ideal.Quotient.algHom_ext
  ext i
  exact h i

/-- The complex algebra points are exactly the original coordinates when
the set is equation-closed; no extra abstract point bijection is chosen. -/
def quotientPointEquiv (S : Set (I → ℂ)) (hS : EquationClosed S) :
    (CoordinateRing S →ₐ[ℂ] ℂ) ≃ S where
  toFun q := ⟨fun i => q (coordinate S i), quotientPoint_mem S hS q⟩
  invFun v := quotientEvaluation S v.val v.property
  left_inv q := by
    apply quotientPoint_ext
    intro i
    exact quotientEvaluation_coordinate S _ _ i
  right_inv v := by
    apply Subtype.ext
    funext i
    exact quotientEvaluation_coordinate S _ _ i

end CoordinateRings

/-! ### Actual affine scheme morphisms and their coordinate formulas -/

section AffineSchemes

def affineBaseMap (A : Type) [CommRing A] [Algebra ℂ A] :
    Spec (CommRingCat.of A) ⟶ ComplexBase :=
  Spec.map (CommRingCat.ofHom (algebraMap ℂ A))

def affineMap {A B : Type} [CommRing A] [CommRing B]
    [Algebra ℂ A] [Algebra ℂ B] (f : A →ₐ[ℂ] B) :
    Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom f.toRingHom)

theorem affineMap_overC {A B : Type} [CommRing A] [CommRing B]
    [Algebra ℂ A] [Algebra ℂ B] (f : A →ₐ[ℂ] B) :
    affineMap f ≫ affineBaseMap A = affineBaseMap B := by
  change Spec.map (CommRingCat.ofHom f.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap ℂ A)) = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext c
  exact f.commutes c

variable {I : Type}

abbrev affineSpace (I : Type) : Scheme := Spec (CommRingCat.of (CoordinatePolynomial I))
abbrev closureScheme (S : Set (I → ℂ)) : Scheme := Spec (CommRingCat.of (CoordinateRing S))

instance closureScheme_reduced (S : Set (I → ℂ)) : AlgebraicGeometry.IsReduced (closureScheme S) :=
  inferInstanceAs (AlgebraicGeometry.IsReduced (Spec (CommRingCat.of (CoordinateRing S))))

def closureInclusion (S : Set (I → ℂ)) : closureScheme S ⟶ affineSpace I :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (vanishingIdeal S)))

instance closureInclusion_closed (S : Set (I → ℂ)) : IsClosedImmersion (closureInclusion S) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

def coordinatePoint (v : I → ℂ) : ComplexBase ⟶ affineSpace I :=
  affineMap (MvPolynomial.aeval v)

def closurePoint (S : Set (I → ℂ)) (v : I → ℂ) (hv : v ∈ S) :
    ComplexBase ⟶ closureScheme S := affineMap (quotientEvaluation S v hv)

theorem closurePoint_inclusion (S : Set (I → ℂ)) (v : I → ℂ) (hv : v ∈ S) :
    closurePoint S v hv ≫ closureInclusion S = coordinatePoint v := by
  change Spec.map (CommRingCat.ofHom (quotientEvaluation S v hv).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (vanishingIdeal S))) = _
  rw [← Spec.map_comp]
  congr 1

/-- The affine product coordinate algebra, retaining both cone factors. -/
abbrev ProductRing (S T : Set (I → ℂ)) := CoordinateRing S ⊗[ℂ] CoordinateRing T

abbrev productScheme (S T : Set (I → ℂ)) : Scheme :=
  Spec (CommRingCat.of (ProductRing S T))

/-- The tensor-algebra source is canonically the actual fibre product
of the two reduced affine cone closures over Spec C. -/
def productSchemeIso (S T : Set (I → ℂ)) :
    productScheme S T ≅
      pullback (affineBaseMap (CoordinateRing S)) (affineBaseMap (CoordinateRing T)) :=
  (AlgebraicGeometry.pullbackSpecIso ℂ (CoordinateRing S) (CoordinateRing T)).symm

def productFirst (S T : Set (I → ℂ)) : productScheme S T ⟶ closureScheme S :=
  affineMap (Algebra.TensorProduct.includeLeft : CoordinateRing S →ₐ[ℂ] ProductRing S T)

def productSecond (S T : Set (I → ℂ)) : productScheme S T ⟶ closureScheme T :=
  affineMap (Algebra.TensorProduct.includeRight : CoordinateRing T →ₐ[ℂ] ProductRing S T)

theorem productScheme_isPullback (S T : Set (I → ℂ)) :
    IsPullback (productFirst S T) (productSecond S T)
      (affineBaseMap (CoordinateRing S)) (affineBaseMap (CoordinateRing T)) :=
  AlgebraicGeometry.isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct ℂ (CoordinateRing S) (CoordinateRing T))

def firstCoordinate (S T : Set (I → ℂ)) (i : I) : ProductRing S T :=
  (Algebra.TensorProduct.includeLeft : CoordinateRing S →ₐ[ℂ] ProductRing S T)
    (coordinate S i)

def secondCoordinate (S T : Set (I → ℂ)) (i : I) : ProductRing S T :=
  Algebra.TensorProduct.includeRight (coordinate T i)

/-- The comorphism of addition sends the i-th ambient coordinate to the
sum of its two genuine tensor-factor coordinates. -/
def additionComorphism (S T : Set (I → ℂ)) :
    CoordinatePolynomial I →ₐ[ℂ] ProductRing S T :=
  MvPolynomial.aeval (fun i => firstCoordinate S T i + secondCoordinate S T i)

@[simp] theorem additionComorphism_X (S T : Set (I → ℂ)) (i : I) :
    additionComorphism S T (MvPolynomial.X i) =
      firstCoordinate S T i + secondCoordinate S T i := MvPolynomial.aeval_X _ i

def additionMorphism (S T : Set (I → ℂ)) : productScheme S T ⟶ affineSpace I :=
  affineMap (additionComorphism S T)

theorem additionMorphism_overC (S T : Set (I → ℂ)) :
    additionMorphism S T ≫ affineBaseMap (CoordinatePolynomial I) =
      affineBaseMap (ProductRing S T) := affineMap_overC _

def productEvaluation (S T : Set (I → ℂ)) (a b : I → ℂ)
    (ha : a ∈ S) (hb : b ∈ T) : ProductRing S T →ₐ[ℂ] ℂ :=
  Algebra.TensorProduct.lift (quotientEvaluation S a ha) (quotientEvaluation T b hb)
    (fun _ _ => Commute.all _ _)

@[simp] theorem productEvaluation_first (S T : Set (I → ℂ)) (a b : I → ℂ)
    (ha : a ∈ S) (hb : b ∈ T) (i : I) :
    productEvaluation S T a b ha hb (firstCoordinate S T i) = a i := by
  simp [productEvaluation, firstCoordinate, Algebra.TensorProduct.includeLeft_apply]

@[simp] theorem productEvaluation_second (S T : Set (I → ℂ)) (a b : I → ℂ)
    (ha : a ∈ S) (hb : b ∈ T) (i : I) :
    productEvaluation S T a b ha hb (secondCoordinate S T i) = b i := by
  simp [productEvaluation, secondCoordinate, Algebra.TensorProduct.includeRight_apply]

theorem productEvaluation_addition (S T : Set (I → ℂ)) (a b : I → ℂ)
    (ha : a ∈ S) (hb : b ∈ T) :
    (productEvaluation S T a b ha hb).comp (additionComorphism S T) =
      MvPolynomial.aeval (a + b) := by
  ext i
  simp only [AlgHom.comp_apply, additionComorphism_X, map_add,
    productEvaluation_first, productEvaluation_second, MvPolynomial.aeval_X, Pi.add_apply]

def pairPoint (S T : Set (I → ℂ)) (a b : I → ℂ) (ha : a ∈ S) (hb : b ∈ T) :
    ComplexBase ⟶ productScheme S T := affineMap (productEvaluation S T a b ha hb)

/-- The scheme map evaluates on every represented complex pair as a+b.
Thus later dominance arguments concern the actual addition morphism. -/
theorem pairPoint_addition (S T : Set (I → ℂ)) (a b : I → ℂ)
    (ha : a ∈ S) (hb : b ∈ T) :
    pairPoint S T a b ha hb ≫ additionMorphism S T = coordinatePoint (a + b) := by
  unfold pairPoint additionMorphism coordinatePoint affineMap
  rw [← Spec.map_comp]
  exact congrArg (fun f : CoordinatePolynomial I →ₐ[ℂ] ℂ =>
    Spec.map (CommRingCat.ofHom f.toRingHom))
      (productEvaluation_addition S T a b ha hb)

end AffineSchemes

/-! ### Genuine projective realizations and their component cones -/

/-- A reduced closed projective subscheme of the actual chosen projective
space.  Its existence with the contact-line properties is a deferred
published-geometric construction, not an extra admitted theorem here. -/
structure ReducedProjectiveDirections (N : ℕ) where
  scheme : Scheme
  embedding : scheme ⟶ ComplexProjectiveSpace N
  closed : IsClosedImmersion embedding
  reduced : AlgebraicGeometry.IsReduced scheme

attribute [instance] ReducedProjectiveDirections.closed ReducedProjectiveDirections.reduced

namespace ReducedProjectiveDirections
variable {N : ℕ} (D : ReducedProjectiveDirections N)

def toC : D.scheme ⟶ ComplexBase := D.embedding ≫ projectiveBaseMap N
abbrev Points := PointsOver ComplexBase (𝟙 ComplexBase) D.scheme D.toC

def projectivePoint (z : D.Points) :
    PointsOver ComplexBase (𝟙 ComplexBase) (ComplexProjectiveSpace N) (projectiveBaseMap N) :=
  ⟨z.val ≫ D.embedding, by simpa only [Category.assoc, toC] using z.property⟩

/-- The indices are the actual topological irreducible components of the
projective scheme; a single globally irreducible component is not assumed. -/
abbrev Component := {C : Set D.scheme // C ∈ irreducibleComponents D.scheme}

theorem component_closed (C : D.Component) : IsClosed C.val :=
  isClosed_of_mem_irreducibleComponents _ C.property

theorem component_irreducible (C : D.Component) : IsIrreducible C.val := C.property.1

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
    (e : V ≃ₗ[ℂ] (Fin (N+1) → ℂ))

def coordinateRepresentative (z : D.Points) : Fin (N+1) → ℂ :=
  Classical.choose (projectiveCoordinates_representatives (projectiveCoordinates N) (D.projectivePoint z))

theorem coordinateRepresentative_spec (z : D.Points) :
    (projectiveCoordinates N).Represents (D.projectivePoint z) (D.coordinateRepresentative z) :=
  Classical.choose_spec
    (projectiveCoordinates_representatives (projectiveCoordinates N) (D.projectivePoint z))

theorem representative_ne_zero (z : D.Points) : e.symm (D.coordinateRepresentative z) ≠ 0 := by
  intro h
  apply (D.coordinateRepresentative_spec z).1
  have hh := congrArg e h
  simpa only [e.apply_symm_apply, map_zero] using hh

/-- This direction is determined by the actual projective embedding and
the tautological quotient's representative, then transported by the frame. -/
def direction (z : D.Points) : Projectivization ℂ V :=
  Projectivization.mk ℂ (e.symm (D.coordinateRepresentative z)) (D.representative_ne_zero e z)

theorem direction_eq_of_represents (z : D.Points) (v : V) (hv : v ≠ 0)
    (h : (projectiveCoordinates N).Represents (D.projectivePoint z) (e v)) :
    D.direction e z = Projectivization.mk ℂ v hv := by
  obtain ⟨c, _hc, hcoords⟩ :=
    (projectiveCoordinates_samePoint_iff (projectiveCoordinates N)
      (D.projectivePoint z) (D.projectivePoint z) (D.coordinateRepresentative z) (e v)
      (D.coordinateRepresentative_spec z) h).mp rfl
  symm
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ hv (D.representative_ne_zero e z)).mpr
  refine ⟨c, ?_⟩
  apply e.injective
  simpa only [map_smul, e.apply_symm_apply] using hcoords.symm

/-- The direction subset of a genuine component.  A complex point is
included when its topological image meets that component. -/
def componentDirections (C : D.Component) : Set (Projectivization ℂ V) :=
  {d | ∃ z : D.Points, ∃ p : ComplexBase, z.val p ∈ C.val ∧ D.direction e z = d}

theorem componentDirections_subset (C : D.Component) :
    D.componentDirections e C ⊆ Set.range (D.direction e) := by
  rintro d ⟨z, p, hp, rfl⟩
  exact ⟨z, rfl⟩

theorem direction_in_component (z : D.Points) (p : ComplexBase) :
    ∃ C : D.Component, D.direction e z ∈ D.componentDirections e C := by
  refine ⟨⟨irreducibleComponent (z.val p),
    irreducibleComponent_mem_irreducibleComponents (z.val p)⟩, z, p, ?_, rfl⟩
  exact mem_irreducibleComponent

theorem directions_eq_component_union :
    Set.range (D.direction e) = ⋃ C : D.Component, D.componentDirections e C := by
  ext d
  constructor
  · rintro ⟨z, rfl⟩
    let p : ComplexBase := Classical.choice (inferInstance : Nonempty ComplexBase)
    obtain ⟨C, hC⟩ := D.direction_in_component e z p
    exact Set.mem_iUnion.mpr ⟨C, hC⟩
  · intro h
    obtain ⟨C, hC⟩ := Set.mem_iUnion.mp h
    exact D.componentDirections_subset e C hC

/-- Coordinates of the affine cone over one actual component. -/
def componentConePoints (C : D.Component) : Set (Fin (N+1) → ℂ) :=
  e '' projectiveCone (D.componentDirections e C)

theorem zero_mem_componentConePoints (C : D.Component) :
    (0 : Fin (N+1) → ℂ) ∈ D.componentConePoints e C :=
  ⟨0, zero_mem_projectiveCone _, map_zero e⟩

theorem componentConePoints_smul (C : D.Component) {v : Fin (N+1) → ℂ}
    (hv : v ∈ D.componentConePoints e C) (c : ℂ) :
    c • v ∈ D.componentConePoints e C := by
  obtain ⟨w, hw, rfl⟩ := hv
  exact ⟨c • w, projectiveCone_smul _ hw c, map_smul e c w⟩

/-- Reduced affine closure of the component cone, with its canonical
closed inclusion in the chosen affine coordinates on the contact plane. -/
abbrev componentConeScheme (C : D.Component) : Scheme :=
  closureScheme (D.componentConePoints e C)

def componentConeInclusion (C : D.Component) : D.componentConeScheme e C ⟶ affineSpace (Fin (N+1)) :=
  closureInclusion (D.componentConePoints e C)

def componentAddition (C E : D.Component) :
    productScheme (D.componentConePoints e C) (D.componentConePoints e E) ⟶
      affineSpace (Fin (N+1)) :=
  additionMorphism (D.componentConePoints e C) (D.componentConePoints e E)

theorem componentAddition_values (C E : D.Component) (a b : Fin (N+1) → ℂ)
    (ha : a ∈ D.componentConePoints e C) (hb : b ∈ D.componentConePoints e E) :
    pairPoint (D.componentConePoints e C) (D.componentConePoints e E) a b ha hb ≫
      D.componentAddition e C E = coordinatePoint (a + b) :=
  pairPoint_addition _ _ a b ha hb

end ReducedProjectiveDirections

/-- Exact contact-line realization condition, separate from the general
projective construction.  No conclusion of the suitable-pair argument is
included: no dominance, tangent-space transversality, or spanning of an
individual component is required. -/
def RealizesSelectedDirections {n : ℕ} {X : ContactFanoManifold n}
    (H : FreeLine X → Prop) (x : ComplexPoint X.variety) {N : ℕ}
    (e : contactPlane X x ≃ₗ[ℂ] (Fin (N+1) → ℂ))
    (D : ReducedProjectiveDirections N) : Prop :=
  Set.range (D.direction e) = selectedDirections H x

theorem componentVector_is_actual {n : ℕ} {X : ContactFanoManifold n}
    (H : FreeLine X → Prop) (x : ComplexPoint X.variety) {N : ℕ}
    (e : contactPlane X x ≃ₗ[ℂ] (Fin (N+1) → ℂ))
    (D : ReducedProjectiveDirections N) (hD : RealizesSelectedDirections H x e D)
    (C : D.Component) (v : contactPlane X x) (hv : v ≠ 0)
    (hC : v ∈ projectiveCone (D.componentDirections e C)) : IsSelectedVector H x v := by
  apply (selectedCone_nonzero_iff H x v hv).mp
  apply projectiveCone_mono (fun d hd => ?_) hC
  rw [← hD]
  exact D.componentDirections_subset e C hd

/-!
Remaining geometry is deliberately visible.  Construct the published
general-point projective realization (with a separate n=1 proof), prove
component cones are equation-closed and smooth away from zero, identify
their tangent spaces as Lagrangian, and prove disjointness of the projective
components implies disjointness of the component direction sets.  The
algebraic map above is then the morphism whose dominance the manuscript
establishes.  No existence or dominance admission has been inserted here.
-/

end LeBrunSalamon.Construction.Lines.DirectionCones

end

import LSTangentComparison

/-!
## The actual closed linear target of a finite-dimensional velocity image

The affine velocity scheme represents derivations on a chosen target chart.
For a subspace W of these derivations, its linear equations are the actual
point differentials annihilated by every vector in W. We impose their linear
coordinates as an ideal in the existing representing algebra. The resulting
quotient defines an actual closed immersion, not a separate vector-space
label. Finite dimensionality is required only of W, not of the whole chart
derivation space. Double-annihilator separation then identifies both its
complex points and its actual tangent spaces with precisely W.

The factorization criterion below is a criterion on actual regular functions.
The geometric assertion that contact-line velocities satisfy these equations
is deliberately not an input to the definition of the target.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirty
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction

namespace LeBrunSalamon.Construction.Lines.LinearVelocityTarget

open AffineVelocity

section PointFunctionals

variable {A : Type} [CommRing A] [Algebra ℂ A]

/-- A chart derivation acts on the original point-differential quotient.
The normalization on da determines this functional uniquely. -/
def functional (p : A →ₐ[ℂ] ℂ) :
    Infinitesimal.Tangent A p →ₗ[ℂ] Module.Dual ℂ (PointDifferentials p) where
  toFun v := descend p v.val (by
    intro a b
    simpa only [smul_eq_mul] using v.property a b)
  map_add' := by
    intro v w
    apply LinearMap.ext
    intro u
    obtain ⟨a, rfl⟩ := pointDifferential_surjective p u
    rfl
  map_smul' := by
    intro c v
    apply LinearMap.ext
    intro u
    obtain ⟨a, rfl⟩ := pointDifferential_surjective p u
    rfl

@[simp] theorem functional_differential (p : A →ₐ[ℂ] ℂ)
    (v : Infinitesimal.Tangent A p) (a : A) :
    functional p v (pointDifferential p a) = v.val a := rfl

/-- Conversely, evaluation on da gives a point derivation; the Leibniz
rule is a relation of the original point-differential quotient. -/
def ofFunctional (p : A →ₐ[ℂ] ℂ) :
    Module.Dual ℂ (PointDifferentials p) →ₗ[ℂ] Infinitesimal.Tangent A p where
  toFun q := ⟨q.comp (pointDifferential p), by
    intro a b
    change q (pointDifferential p (a*b)) =
      p a * q (pointDifferential p b) + p b * q (pointDifferential p a)
    rw [pointDifferential_mul, map_add, map_smul, map_smul]
    rfl⟩
  map_add' := by intro q r; apply Subtype.ext; ext a; rfl
  map_smul' := by intro c q; apply Subtype.ext; ext a; rfl

@[simp] theorem ofFunctional_apply (p : A →ₐ[ℂ] ℂ)
    (q : Module.Dual ℂ (PointDifferentials p)) (a : A) :
    (ofFunctional p q).val a = q (pointDifferential p a) := rfl

@[simp] theorem ofFunctional_functional (p : A →ₐ[ℂ] ℂ)
    (v : Infinitesimal.Tangent A p) : ofFunctional p (functional p v) = v := by
  apply Subtype.ext
  ext a
  rfl

@[simp] theorem functional_ofFunctional (p : A →ₐ[ℂ] ℂ)
    (q : Module.Dual ℂ (PointDifferentials p)) :
    functional p (ofFunctional p q) = q := by
  apply LinearMap.ext
  intro u
  obtain ⟨a, rfl⟩ := pointDifferential_surjective p u
  rfl

/-- This equivalence is fixed by the actual universal differential da.
No basis or unspecified equal-dimension identification enters it. -/
def functionalEquiv (p : A →ₐ[ℂ] ℂ) :
    Infinitesimal.Tangent A p ≃ₗ[ℂ] Module.Dual ℂ (PointDifferentials p) where
  toLinearMap := functional p
  invFun := ofFunctional p
  left_inv := ofFunctional_functional p
  right_inv := functional_ofFunctional p

@[simp] theorem functionalEquiv_apply (p : A →ₐ[ℂ] ℂ)
    (v : Infinitesimal.Tangent A p) : functionalEquiv p v = functional p v := rfl

@[simp] theorem functionalEquiv_symm_apply (p : A →ₐ[ℂ] ℂ)
    (q : Module.Dual ℂ (PointDifferentials p)) :
    (functionalEquiv p).symm q = ofFunctional p q := rfl

end PointFunctionals

section LinearEquations

variable {A : Type} [CommRing A] [Algebra ℂ A]
variable (p : A →ₐ[ℂ] ℂ) (W : Submodule ℂ (Infinitesimal.Tangent A p))

/-- The same concrete subspace regarded as functionals on point
differentials, through the uniquely normalized comparison above. -/
def dualImage : Submodule ℂ (Module.Dual ℂ (PointDifferentials p)) :=
  W.map (functional p)

theorem functional_mem_dualImage (v : Infinitesimal.Tangent A p) :
    functional p v ∈ dualImage p W ↔ v ∈ W := by
  constructor
  · rintro ⟨w, hw, h⟩
    have hwv : w = v := (functionalEquiv p).injective h
    exact hwv ▸ hw
  · intro hv
    exact ⟨v, hv, rfl⟩

/-- The genuine homogeneous linear equations of W. -/
def linearRelations : Submodule ℂ (PointDifferentials p) :=
  (dualImage p W).dualCoannihilator

theorem mem_linearRelations (u : PointDifferentials p) :
    u ∈ linearRelations p W ↔
      ∀ v : Infinitesimal.Tangent A p, v ∈ W → functional p v u = 0 := by
  change u ∈ (dualImage p W).dualCoannihilator ↔ _
  rw [Submodule.mem_dualCoannihilator]
  constructor
  · intro h v hv
    exact h (functional p v) ((functional_mem_dualImage p W v).mpr hv)
  · intro h q hq
    obtain ⟨v, hv, rfl⟩ := hq
    exact h v hv

theorem vector_annihilates (v : W) (u : PointDifferentials p)
    (hu : u ∈ linearRelations p W) : functional p v.val u = 0 :=
  (mem_linearRelations p W u).mp hu v.val v.property

/-- Algebraic double-annihilator separation requires only the finite
dimension of the represented subspace. The ambient cotangent quotient
and full space of chart derivations may still be infinite-dimensional. -/
theorem annihilates_iff_mem [FiniteDimensional ℂ W]
    (v : Infinitesimal.Tangent A p) :
    (∀ u ∈ linearRelations p W, functional p v u = 0) ↔ v ∈ W := by
  haveI : FiniteDimensional ℂ (dualImage p W) := inferInstanceAs
    (FiniteDimensional ℂ (W.map (functional p)))
  rw [← Submodule.mem_dualAnnihilator]
  change functional p v ∈ (dualImage p W).dualCoannihilator.dualAnnihilator ↔ _
  rw [Subspace.dualCoannihilator_dualAnnihilator_eq]
  exact functional_mem_dualImage p W v

/-- The ideal is generated by the actual linear coordinate functions
of the annihilating point differentials. -/
def linearIdeal : Ideal (CoordinateRing p) :=
  Ideal.span (SymmetricAlgebra.ι ℂ (PointDifferentials p) ''
    (linearRelations p W : Set (PointDifferentials p)))

theorem linearGenerator_mem (u : PointDifferentials p)
    (hu : u ∈ linearRelations p W) :
    SymmetricAlgebra.ι ℂ (PointDifferentials p) u ∈ linearIdeal p W :=
  Ideal.subset_span ⟨u, hu, rfl⟩

abbrev CoordinateAlgebra := (CoordinateRing p) ⧸ linearIdeal p W

/-- The comorphism of the closed linear embedding. -/
def quotientMap : CoordinateRing p →ₐ[ℂ] CoordinateAlgebra p W :=
  Ideal.Quotient.mkₐ ℂ (linearIdeal p W)

theorem quotientMap_surjective : Function.Surjective (quotientMap p W) :=
  Ideal.Quotient.mkₐ_surjective ℂ (linearIdeal p W)

/-- The same differential coordinate restricted to the closed target. -/
def coordinate : A →ₗ[ℂ] CoordinateAlgebra p W :=
  (quotientMap p W).toLinearMap.comp (AffineVelocity.coordinate p)

@[simp] theorem coordinate_apply (a : A) :
    coordinate p W a = quotientMap p W (AffineVelocity.coordinate p a) := rfl

theorem quotientMap_linearRelation (u : PointDifferentials p)
    (hu : u ∈ linearRelations p W) :
    quotientMap p W (SymmetricAlgebra.ι ℂ (PointDifferentials p) u) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (linearGenerator_mem p W u hu)

theorem coordinate_mul (a b : A) :
    coordinate p W (a*b) = p a • coordinate p W b + p b • coordinate p W a := by
  change quotientMap p W (AffineVelocity.coordinate p (a*b)) = _
  rw [AffineVelocity.coordinate_mul, map_add, map_smul, map_smul]
  rfl

variable {B : Type} [CommRing B] [Algebra ℂ B]

theorem coordinate_ext {q r : CoordinateAlgebra p W →ₐ[ℂ] B}
    (h : ∀ a : A, q (coordinate p W a) = r (coordinate p W a)) : q = r := by
  apply Ideal.Quotient.algHom_ext
  apply AffineVelocity.coordinate_ext p
  exact h

/-- Checking the defining ideal is exactly checking its genuine linear
generators, including for nonreduced parameter algebras. -/
theorem killsIdeal_iff (φ : CoordinateRing p →ₐ[ℂ] B) :
    (∀ r ∈ linearIdeal p W, φ r = 0) ↔
      ∀ u ∈ linearRelations p W,
        φ (SymmetricAlgebra.ι ℂ (PointDifferentials p) u) = 0 := by
  constructor
  · intro h u hu
    exact h _ (linearGenerator_mem p W u hu)
  · intro h
    have hi : linearIdeal p W ≤ RingHom.ker φ.toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨u, hu, rfl⟩
      exact h u hu
    intro r hr
    exact hi hr

/-- Factor the actual comorphism through the actual quotient. This
construction accepts explicit equations and proves the factorization. -/
def factor (φ : CoordinateRing p →ₐ[ℂ] B)
    (hφ : ∀ u ∈ linearRelations p W,
      φ (SymmetricAlgebra.ι ℂ (PointDifferentials p) u) = 0) :
    CoordinateAlgebra p W →ₐ[ℂ] B :=
  Ideal.Quotient.liftₐ (linearIdeal p W) φ ((killsIdeal_iff p W φ).mpr hφ)

@[simp] theorem factor_quotientMap (φ : CoordinateRing p →ₐ[ℂ] B)
    (hφ : ∀ u ∈ linearRelations p W,
      φ (SymmetricAlgebra.ι ℂ (PointDifferentials p) u) = 0)
    (r : CoordinateRing p) : factor p W φ hφ (quotientMap p W r) = φ r := rfl

theorem factor_comp (φ : CoordinateRing p →ₐ[ℂ] B)
    (hφ : ∀ u ∈ linearRelations p W,
      φ (SymmetricAlgebra.ι ℂ (PointDifferentials p) u) = 0) :
    (factor p W φ hφ).comp (quotientMap p W) = φ := rfl

@[simp] theorem factor_coordinate (φ : CoordinateRing p →ₐ[ℂ] B)
    (hφ : ∀ u ∈ linearRelations p W,
      φ (SymmetricAlgebra.ι ℂ (PointDifferentials p) u) = 0)
    (a : A) : factor p W φ hφ (coordinate p W a) =
      φ (AffineVelocity.coordinate p a) := rfl

theorem factor_unique (φ : CoordinateRing p →ₐ[ℂ] B)
    (hφ : ∀ u ∈ linearRelations p W,
      φ (SymmetricAlgebra.ι ℂ (PointDifferentials p) u) = 0)
    (ψ : CoordinateAlgebra p W →ₐ[ℂ] B)
    (hψ : ψ.comp (quotientMap p W) = φ) : ψ = factor p W φ hφ := by
  apply Ideal.Quotient.algHom_ext
  exact hψ.trans (factor_comp p W φ hφ).symm

theorem factorization_iff (φ : CoordinateRing p →ₐ[ℂ] B) :
    (∃ ψ : CoordinateAlgebra p W →ₐ[ℂ] B,
      ψ.comp (quotientMap p W) = φ) ↔
    ∀ u ∈ linearRelations p W,
      φ (SymmetricAlgebra.ι ℂ (PointDifferentials p) u) = 0 := by
  constructor
  · rintro ⟨ψ, hψ⟩ u hu
    rw [← hψ, AlgHom.comp_apply, quotientMap_linearRelation p W u hu, map_zero]
  · intro hφ
    exact ⟨factor p W φ hφ, factor_comp p W φ hφ⟩

end LinearEquations

section ActualSchemes

variable {A : Type} [CommRing A] [Algebra ℂ A]
variable (p : A →ₐ[ℂ] ℂ) (W : Submodule ℂ (Infinitesimal.Tangent A p))

abbrev scheme : Scheme := Spec (CommRingCat.of (CoordinateAlgebra p W))

def toC : scheme p W ⟶ ComplexBase :=
  DirectionCones.affineBaseMap (CoordinateAlgebra p W)

/-- The closed target is embedded into the same affine velocity scheme
by Spec of its actual quotient map. -/
def inclusion : scheme p W ⟶ AffineVelocity.tangentScheme p :=
  DirectionCones.affineMap (quotientMap p W)

instance inclusion_isClosedImmersion : IsClosedImmersion (inclusion p W) :=
  IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (quotientMap p W).toRingHom) (quotientMap_surjective p W)

theorem inclusion_overC :
    inclusion p W ≫ AffineVelocity.tangentSchemeToC p = toC p W :=
  DirectionCones.affineMap_overC (quotientMap p W)

variable {B : Type} [CommRing B] [Algebra ℂ B]

def affineFactor (φ : CoordinateRing p →ₐ[ℂ] B)
    (hφ : ∀ u ∈ linearRelations p W,
      φ (SymmetricAlgebra.ι ℂ (PointDifferentials p) u) = 0) :
    Spec (CommRingCat.of B) ⟶ scheme p W :=
  DirectionCones.affineMap (factor p W φ hφ)

theorem affineFactor_inclusion (φ : CoordinateRing p →ₐ[ℂ] B)
    (hφ : ∀ u ∈ linearRelations p W,
      φ (SymmetricAlgebra.ι ℂ (PointDifferentials p) u) = 0) :
    affineFactor p W φ hφ ≫ inclusion p W = DirectionCones.affineMap φ := by
  change Spec.map (CommRingCat.ofHom (factor p W φ hφ).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (quotientMap p W).toRingHom) = _
  rw [← Spec.map_comp]
  rfl

theorem affineFactor_overC (φ : CoordinateRing p →ₐ[ℂ] B)
    (hφ : ∀ u ∈ linearRelations p W,
      φ (SymmetricAlgebra.ι ℂ (PointDifferentials p) u) = 0) :
    affineFactor p W φ hφ ≫ toC p W = DirectionCones.affineBaseMap B :=
  DirectionCones.affineMap_overC (factor p W φ hφ)

variable {Y : Scheme} {sY : Y ⟶ ComplexBase}

/-- The same factorization works on an arbitrary parameter scheme by
the actual Gamma--Spec adjunction; Y is not assumed affine. -/
def globalFactor (φ : CoordinateRing p →ₐ[ℂ] SectionAlgebra.Functions sY ⊤)
    (hφ : ∀ u ∈ linearRelations p W,
      φ (SymmetricAlgebra.ι ℂ (PointDifferentials p) u) = 0) :
    Y ⟶ scheme p W := GlobalVelocity.toSpec (factor p W φ hφ)

theorem globalFactor_overC
    (φ : CoordinateRing p →ₐ[ℂ] SectionAlgebra.Functions sY ⊤)
    (hφ : ∀ u ∈ linearRelations p W,
      φ (SymmetricAlgebra.ι ℂ (PointDifferentials p) u) = 0) :
    globalFactor p W φ hφ ≫ toC p W = sY :=
  GlobalVelocity.toSpec_overC (factor p W φ hφ)

theorem globalFactor_inclusion
    (φ : CoordinateRing p →ₐ[ℂ] SectionAlgebra.Functions sY ⊤)
    (hφ : ∀ u ∈ linearRelations p W,
      φ (SymmetricAlgebra.ι ℂ (PointDifferentials p) u) = 0) :
    globalFactor p W φ hφ ≫ inclusion p W = GlobalVelocity.toSpec φ := by
  apply GlobalVelocity.toSpec_unique
  intro r
  change (globalFactor p W φ hφ).appTop
    ((inclusion p W).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (CoordinateRing p))).inv r)) = φ r
  have hn := congrArg (fun k : CommRingCat.of (CoordinateRing p) ⟶
    (scheme p W).presheaf.obj (op ⊤) => k r)
      (Scheme.ΓSpecIso_inv_naturality
        (CommRingCat.ofHom (quotientMap p W).toRingHom))
  simp only [CommRingCat.comp_apply] at hn
  change (Scheme.ΓSpecIso (CommRingCat.of (CoordinateAlgebra p W))).inv
      (quotientMap p W r) =
    (inclusion p W).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (CoordinateRing p))).inv r) at hn
  exact (congrArg (fun u : (scheme p W).presheaf.obj (op ⊤) =>
      (globalFactor p W φ hφ).appTop u) hn.symm).trans
    (GlobalVelocity.toSpec_function (factor p W φ hφ) (quotientMap p W r))

theorem globalFactor_function
    (φ : CoordinateRing p →ₐ[ℂ] SectionAlgebra.Functions sY ⊤)
    (hφ : ∀ u ∈ linearRelations p W,
      φ (SymmetricAlgebra.ι ℂ (PointDifferentials p) u) = 0)
    (r : CoordinateAlgebra p W) :
    (globalFactor p W φ hφ).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (CoordinateAlgebra p W))).inv r) =
        factor p W φ hφ r :=
  GlobalVelocity.toSpec_function (factor p W φ hφ) r

end ActualSchemes

section ActualPoints

variable {A : Type} [CommRing A] [Algebra ℂ A]
variable (p : A →ₐ[ℂ] ℂ) (W : Submodule ℂ (Infinitesimal.Tangent A p))

def ambientPoint (q : CoordinateAlgebra p W →ₐ[ℂ] ℂ) : CoordinateRing p →ₐ[ℂ] ℂ :=
  q.comp (quotientMap p W)

/-- Evaluation of an arbitrary linear generator equals the canonical
functional of the represented vector. -/
theorem point_functional (q : CoordinateRing p →ₐ[ℂ] ℂ)
    (u : PointDifferentials p) :
    functional p (AffineVelocity.tangentPointEquiv p q) u =
      q (SymmetricAlgebra.ι ℂ (PointDifferentials p) u) := by
  obtain ⟨a, rfl⟩ := pointDifferential_surjective p u
  rfl

theorem ambientPoint_mem [FiniteDimensional ℂ W]
    (q : CoordinateAlgebra p W →ₐ[ℂ] ℂ) :
    AffineVelocity.tangentPointEquiv p (ambientPoint p W q) ∈ W := by
  apply (annihilates_iff_mem p W _).mp
  intro u hu
  rw [point_functional]
  change q (quotientMap p W (SymmetricAlgebra.ι ℂ (PointDifferentials p) u)) = 0
  rw [quotientMap_linearRelation p W u hu, map_zero]

/-- Every vector of W determines a point of the actual quotient scheme.
Its values on coordinates are its original chart derivation. -/
def pointOfVector (v : W) : CoordinateAlgebra p W →ₐ[ℂ] ℂ :=
  factor p W ((AffineVelocity.tangentPointEquiv p).symm v.val) (by
    intro u hu
    have h := point_functional p ((AffineVelocity.tangentPointEquiv p).symm v.val) u
    rw [Equiv.apply_symm_apply] at h
    exact h.symm.trans (vector_annihilates p W v u hu))

@[simp] theorem pointOfVector_coordinate (v : W) (a : A) :
    pointOfVector p W v (coordinate p W a) = v.val.val a := by
  change (AffineVelocity.tangentPointEquiv p).symm v.val
    (AffineVelocity.coordinate p a) = _
  exact AffineVelocity.coordinateLift_coordinate p v.val.val _ a

theorem ambientPoint_pointOfVector (v : W) :
    ambientPoint p W (pointOfVector p W v) =
      (AffineVelocity.tangentPointEquiv p).symm v.val := rfl

/-- Exact point identification; the image contains neither extra
closed points nor an unproved contact-direction hypothesis. -/
def pointEquiv [FiniteDimensional ℂ W] :
    (CoordinateAlgebra p W →ₐ[ℂ] ℂ) ≃ W where
  toFun q := ⟨AffineVelocity.tangentPointEquiv p (ambientPoint p W q),
    ambientPoint_mem p W q⟩
  invFun := pointOfVector p W
  left_inv q := by
    apply coordinate_ext p W
    intro a
    rw [pointOfVector_coordinate]
    rfl
  right_inv v := by
    apply Subtype.ext
    change AffineVelocity.tangentPointEquiv p
      (ambientPoint p W (pointOfVector p W v)) = v.val
    rw [ambientPoint_pointOfVector, Equiv.apply_symm_apply]

@[simp] theorem pointEquiv_coordinate [FiniteDimensional ℂ W]
    (q : CoordinateAlgebra p W →ₐ[ℂ] ℂ) (a : A) :
    (pointEquiv p W q).val.val a = q (coordinate p W a) := rfl

/-- The exact represented vector can be tested on every original da. -/
theorem pointEquiv_eq_iff [FiniteDimensional ℂ W]
    (q : CoordinateAlgebra p W →ₐ[ℂ] ℂ) (v : W) :
    pointEquiv p W q = v ↔ ∀ a : A, q (coordinate p W a) = v.val.val a := by
  constructor
  · intro h a
    exact congrArg (fun w : W => w.val.val a) h
  · intro h
    apply Subtype.ext
    apply Subtype.ext
    ext a
    exact h a

end ActualPoints

section ActualTangents

variable {A : Type} [CommRing A] [Algebra ℂ A]
variable (p : A →ₐ[ℂ] ℂ) (W : Submodule ℂ (Infinitesimal.Tangent A p))

/-- The differential of the actual closed immersion followed by the
already normalized tangent trivialization of the ambient velocity scheme. -/
def inclusionDifferential (q : CoordinateAlgebra p W →ₐ[ℂ] ℂ) :
    Infinitesimal.Tangent (CoordinateAlgebra p W) q →ₗ[ℂ]
      Infinitesimal.Tangent A p :=
  (AffineVelocity.tangentTrivialization p (ambientPoint p W q)).comp
    (Infinitesimal.tangentMap (quotientMap p W) q)

@[simp] theorem inclusionDifferential_coordinate
    (q : CoordinateAlgebra p W →ₐ[ℂ] ℂ)
    (D : Infinitesimal.Tangent (CoordinateAlgebra p W) q) (a : A) :
    (inclusionDifferential p W q D).val a = D.val (coordinate p W a) := rfl

theorem inclusionDifferential_functional
    (q : CoordinateAlgebra p W →ₐ[ℂ] ℂ)
    (D : Infinitesimal.Tangent (CoordinateAlgebra p W) q)
    (u : PointDifferentials p) :
    functional p (inclusionDifferential p W q D) u =
      D.val (quotientMap p W (SymmetricAlgebra.ι ℂ (PointDifferentials p) u)) := by
  obtain ⟨a, rfl⟩ := pointDifferential_surjective p u
  rfl

/-- The linear equations defining the scheme also annihilate every
actual infinitesimal tangent direction. This includes nonzero base points. -/
theorem inclusionDifferential_mem [FiniteDimensional ℂ W]
    (q : CoordinateAlgebra p W →ₐ[ℂ] ℂ)
    (D : Infinitesimal.Tangent (CoordinateAlgebra p W) q) :
    inclusionDifferential p W q D ∈ W := by
  apply (annihilates_iff_mem p W _).mp
  intro u hu
  rw [inclusionDifferential_functional, quotientMap_linearRelation p W u hu, map_zero]

theorem inclusionDifferential_injective
    (q : CoordinateAlgebra p W →ₐ[ℂ] ℂ) :
    Function.Injective (inclusionDifferential p W q) := by
  intro D E h
  have ht : Infinitesimal.tangentMap (quotientMap p W) q D =
      Infinitesimal.tangentMap (quotientMap p W) q E :=
    AffineVelocity.tangentTrivialization_injective p (ambientPoint p W q) h
  apply Subtype.ext
  apply LinearMap.ext
  intro r
  obtain ⟨a, rfl⟩ := quotientMap_surjective p W r
  exact congrArg (fun v : Infinitesimal.Tangent (CoordinateRing p)
    (ambientPoint p W q) => v.val a) ht

/-- The ambient infinitesimal translation is normalized on all linear
generators, not just a chosen basis of point differentials. -/
theorem infinitesimalTranslation_linear (q : CoordinateRing p →ₐ[ℂ] ℂ)
    (v : Infinitesimal.Tangent A p) (u : PointDifferentials p) :
    AffineVelocity.infinitesimalTranslation p q v
      (SymmetricAlgebra.ι ℂ (PointDifferentials p) u) =
      algebraMap ℂ Infinitesimal.Dual
        (q (SymmetricAlgebra.ι ℂ (PointDifferentials p) u)) +
      Infinitesimal.epsilon * algebraMap ℂ Infinitesimal.Dual (functional p v u) := by
  obtain ⟨a, rfl⟩ := pointDifferential_surjective p u
  exact AffineVelocity.infinitesimalTranslation_coordinate p q v a

/-- Translation by a vector of W preserves all its defining linear
equations even over the dual numbers, with their nilpotents retained. -/
def translatedPoint (q : CoordinateAlgebra p W →ₐ[ℂ] ℂ) (v : W) :
    CoordinateAlgebra p W →ₐ[ℂ] Infinitesimal.Dual :=
  factor p W
    (AffineVelocity.infinitesimalTranslation p (ambientPoint p W q) v.val) (by
      intro u hu
      rw [infinitesimalTranslation_linear]
      change algebraMap ℂ Infinitesimal.Dual
          (q (quotientMap p W (SymmetricAlgebra.ι ℂ (PointDifferentials p) u))) +
        Infinitesimal.epsilon * algebraMap ℂ Infinitesimal.Dual
          (functional p v.val u) = 0
      rw [quotientMap_linearRelation p W u hu, vector_annihilates p W v u hu]
      simp only [map_zero, mul_zero, add_zero])

theorem translatedPoint_coordinate (q : CoordinateAlgebra p W →ₐ[ℂ] ℂ)
    (v : W) (a : A) :
    translatedPoint p W q v (coordinate p W a) =
      algebraMap ℂ Infinitesimal.Dual (q (coordinate p W a)) +
        Infinitesimal.epsilon * algebraMap ℂ Infinitesimal.Dual (v.val.val a) := by
  change AffineVelocity.infinitesimalTranslation p (ambientPoint p W q) v.val
    (AffineVelocity.coordinate p a) = _
  exact AffineVelocity.infinitesimalTranslation_coordinate p (ambientPoint p W q) v.val a

theorem translatedPoint_residue (q : CoordinateAlgebra p W →ₐ[ℂ] ℂ) (v : W) :
    Infinitesimal.residue.comp (translatedPoint p W q v) = q := by
  apply coordinate_ext p W
  intro a
  change Infinitesimal.residue (translatedPoint p W q v (coordinate p W a)) = _
  rw [translatedPoint_coordinate]
  exact Infinitesimal.residue_normalForm _ _

/-- Every vector of W is realized by an actual tangent direction of
the closed target, at every one of its actual complex points. -/
theorem inclusionDifferential_hits
    (q : CoordinateAlgebra p W →ₐ[ℂ] ℂ) (v : W) :
    ∃ D : Infinitesimal.Tangent (CoordinateAlgebra p W) q,
      inclusionDifferential p W q D = v.val := by
  let lift : {r : CoordinateAlgebra p W →ₐ[ℂ] Infinitesimal.Dual //
      Infinitesimal.residue.comp r = q} :=
    ⟨translatedPoint p W q v, translatedPoint_residue p W q v⟩
  obtain ⟨D, hD⟩ := (Infinitesimal.tangentToDual_bijective q).2 lift
  refine ⟨D, ?_⟩
  apply Subtype.ext
  ext a
  have hc := congrArg
    (fun r : {r : CoordinateAlgebra p W →ₐ[ℂ] Infinitesimal.Dual //
        Infinitesimal.residue.comp r = q} =>
      Infinitesimal.linearCoefficient (r.val (coordinate p W a))) hD
  change Infinitesimal.linearCoefficient
      (algebraMap ℂ Infinitesimal.Dual (q (coordinate p W a)) +
        Infinitesimal.epsilon * algebraMap ℂ Infinitesimal.Dual
          (D.val (coordinate p W a))) =
    Infinitesimal.linearCoefficient (translatedPoint p W q v (coordinate p W a)) at hc
  rw [translatedPoint_coordinate, Infinitesimal.linearCoefficient_normalForm,
    Infinitesimal.linearCoefficient_normalForm] at hc
  exact hc

theorem inclusionDifferential_range [FiniteDimensional ℂ W]
    (q : CoordinateAlgebra p W →ₐ[ℂ] ℂ) :
    LinearMap.range (inclusionDifferential p W q) = W := by
  apply le_antisymm
  · rintro _ ⟨D, rfl⟩
    exact inclusionDifferential_mem p W q D
  · intro v hv
    obtain ⟨D, hD⟩ := inclusionDifferential_hits p W q ⟨v, hv⟩
    exact ⟨D, hD⟩

/-- The normalized tangent identification with the represented subspace.
The underlying map is the actual scheme inclusion differential. -/
def tangentEquiv [FiniteDimensional ℂ W]
    (q : CoordinateAlgebra p W →ₐ[ℂ] ℂ) :
    Infinitesimal.Tangent (CoordinateAlgebra p W) q ≃ₗ[ℂ] W :=
  LinearEquiv.ofBijective
    ((inclusionDifferential p W q).codRestrict W
      (inclusionDifferential_mem p W q)) (by
        constructor
        · intro D E h
          exact inclusionDifferential_injective p W q (congrArg Subtype.val h)
        · intro v
          obtain ⟨D, hD⟩ := inclusionDifferential_hits p W q v
          exact ⟨D, Subtype.ext hD⟩)

@[simp] theorem tangentEquiv_apply [FiniteDimensional ℂ W]
    (q : CoordinateAlgebra p W →ₐ[ℂ] ℂ)
    (D : Infinitesimal.Tangent (CoordinateAlgebra p W) q) :
    (tangentEquiv p W q D).val = inclusionDifferential p W q D := rfl

@[simp] theorem tangentEquiv_coordinate [FiniteDimensional ℂ W]
    (q : CoordinateAlgebra p W →ₐ[ℂ] ℂ)
    (D : Infinitesimal.Tangent (CoordinateAlgebra p W) q) (a : A) :
    (tangentEquiv p W q D).val.val a = D.val (coordinate p W a) := rfl

/-- The canonical inverse tangent map gives precisely the translated
dual-number point, including the base point and epsilon coefficient. -/
theorem tangentEquiv_symm_translation [FiniteDimensional ℂ W]
    (q : CoordinateAlgebra p W →ₐ[ℂ] ℂ) (v : W) :
    Infinitesimal.tangentToDual q ((tangentEquiv p W q).symm v) =
      translatedPoint p W q v := by
  apply coordinate_ext p W
  intro a
  have hc : ((tangentEquiv p W q).symm v).val (coordinate p W a) = v.val.val a :=
    congrArg (fun w : W => w.val.val a) ((tangentEquiv p W q).apply_symm_apply v)
  change algebraMap ℂ Infinitesimal.Dual (q (coordinate p W a)) +
    Infinitesimal.epsilon * algebraMap ℂ Infinitesimal.Dual
      (((tangentEquiv p W q).symm v).val (coordinate p W a)) = _
  rw [hc, translatedPoint_coordinate]

theorem tangent_finrank [FiniteDimensional ℂ W]
    (q : CoordinateAlgebra p W →ₐ[ℂ] ℂ) :
    Module.finrank ℂ (Infinitesimal.Tangent (CoordinateAlgebra p W) q) =
      Module.finrank ℂ W := (tangentEquiv p W q).finrank_eq

end ActualTangents

section DifferentialsOfFactors

variable {A B : Type} [CommRing A] [Algebra ℂ A]
variable [CommRing B] [Algebra ℂ B]
variable (p : A →ₐ[ℂ] ℂ) (W : Submodule ℂ (Infinitesimal.Tangent A p))

/-- The ordinary differential of an arbitrary comorphism into the
ambient velocity space, in its canonical linear trivialization. -/
def ambientDifferential (φ : CoordinateRing p →ₐ[ℂ] B) (s : B →ₐ[ℂ] ℂ) :
    Infinitesimal.Tangent B s →ₗ[ℂ] Infinitesimal.Tangent A p :=
  (AffineVelocity.tangentTrivialization p (s.comp φ)).comp
    (Infinitesimal.tangentMap φ s)

@[simp] theorem ambientDifferential_coordinate
    (φ : CoordinateRing p →ₐ[ℂ] B) (s : B →ₐ[ℂ] ℂ)
    (D : Infinitesimal.Tangent B s) (a : A) :
    (ambientDifferential p φ s D).val a = D.val (φ (AffineVelocity.coordinate p a)) := rfl

/-- The derivative of a factored morphism takes values in the actual
closed target's tangent space. The map is the scheme differential,
followed by the proved normalized equivalence, not a supplied image map. -/
def factorDifferential [FiniteDimensional ℂ W]
    (φ : CoordinateRing p →ₐ[ℂ] B)
    (hφ : ∀ u ∈ linearRelations p W,
      φ (SymmetricAlgebra.ι ℂ (PointDifferentials p) u) = 0)
    (s : B →ₐ[ℂ] ℂ) : Infinitesimal.Tangent B s →ₗ[ℂ] W :=
  (tangentEquiv p W (s.comp (factor p W φ hφ))).toLinearMap.comp
    (Infinitesimal.tangentMap (factor p W φ hφ) s)

theorem factorDifferential_inclusion [FiniteDimensional ℂ W]
    (φ : CoordinateRing p →ₐ[ℂ] B)
    (hφ : ∀ u ∈ linearRelations p W,
      φ (SymmetricAlgebra.ι ℂ (PointDifferentials p) u) = 0)
    (s : B →ₐ[ℂ] ℂ) (D : Infinitesimal.Tangent B s) :
    (factorDifferential p W φ hφ s D).val = ambientDifferential p φ s D := by
  apply Subtype.ext
  ext a
  rfl

theorem ambientDifferential_mem [FiniteDimensional ℂ W]
    (φ : CoordinateRing p →ₐ[ℂ] B)
    (hφ : ∀ u ∈ linearRelations p W,
      φ (SymmetricAlgebra.ι ℂ (PointDifferentials p) u) = 0)
    (s : B →ₐ[ℂ] ℂ) (D : Infinitesimal.Tangent B s) :
    ambientDifferential p φ s D ∈ W := by
  rw [← factorDifferential_inclusion p W φ hφ s D]
  exact (factorDifferential p W φ hφ s D).property

/-- This is the exact surjectivity criterion needed for a later
generic-smoothness argument into the contact target. It does not ask
for surjectivity onto the larger ambient tangent space. -/
theorem factorDifferential_surjective_iff [FiniteDimensional ℂ W]
    (φ : CoordinateRing p →ₐ[ℂ] B)
    (hφ : ∀ u ∈ linearRelations p W,
      φ (SymmetricAlgebra.ι ℂ (PointDifferentials p) u) = 0)
    (s : B →ₐ[ℂ] ℂ) :
    Function.Surjective (factorDifferential p W φ hφ s) ↔
      Function.Surjective (Infinitesimal.tangentMap (factor p W φ hφ) s) := by
  constructor
  · intro h u
    obtain ⟨D, hD⟩ := h (tangentEquiv p W (s.comp (factor p W φ hφ)) u)
    refine ⟨D, ?_⟩
    exact (tangentEquiv p W (s.comp (factor p W φ hφ))).injective hD
  · intro h
    exact (tangentEquiv p W (s.comp (factor p W φ hφ))).surjective.comp h

theorem ambientDifferential_range_eq_of_surjective [FiniteDimensional ℂ W]
    (φ : CoordinateRing p →ₐ[ℂ] B)
    (hφ : ∀ u ∈ linearRelations p W,
      φ (SymmetricAlgebra.ι ℂ (PointDifferentials p) u) = 0)
    (s : B →ₐ[ℂ] ℂ)
    (hs : Function.Surjective (Infinitesimal.tangentMap (factor p W φ hφ) s)) :
    LinearMap.range (ambientDifferential p φ s) = W := by
  apply le_antisymm
  · rintro _ ⟨D, rfl⟩
    exact ambientDifferential_mem p W φ hφ s D
  · intro v hv
    obtain ⟨D, hD⟩ := (factorDifferential_surjective_iff p W φ hφ s).mpr hs ⟨v, hv⟩
    refine ⟨D, ?_⟩
    exact (factorDifferential_inclusion p W φ hφ s D).symm.trans
      (congrArg Subtype.val hD)

end DifferentialsOfFactors

section ReducedParameters

variable {B : Type} [CommRing B] [Algebra ℂ B]

/-- Zariski's lemma identifies the residue field of each actual maximal
ideal of a finite-type complex algebra with C, by its scalar map. -/
def maximalPoint [Algebra.FiniteType ℂ B] (m : Ideal B) [m.IsMaximal] : B →ₐ[ℂ] ℂ := by
  letI : Field (B ⧸ m) := Ideal.Quotient.field m
  letI : Module.Finite ℂ (B ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℂ (B ⧸ m)
  let e : ℂ ≃ₐ[ℂ] B ⧸ m := AlgEquiv.ofBijective (Algebra.ofId ℂ (B ⧸ m))
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  exact e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ ℂ m)

theorem maximalPoint_eq_zero_iff [Algebra.FiniteType ℂ B]
    (m : Ideal B) [m.IsMaximal] (b : B) : maximalPoint m b = 0 ↔ b ∈ m := by
  letI : Field (B ⧸ m) := Ideal.Quotient.field m
  letI : Module.Finite ℂ (B ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℂ (B ⧸ m)
  let e : ℂ ≃ₐ[ℂ] B ⧸ m := AlgEquiv.ofBijective (Algebra.ofId ℂ (B ⧸ m))
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  change e.symm (Ideal.Quotient.mk m b) = 0 ↔ b ∈ m
  rw [map_eq_zero_iff _ e.symm.injective, Ideal.Quotient.eq_zero_iff_mem]

/-- Actual complex points detect regular functions on a reduced
finite-type affine parameter. The proof uses the Jacobson property and
the actual maximal-ideal residue maps, not an assumed detection package. -/
theorem reducedFiniteType_pointsDetect [Algebra.FiniteType ℂ B] [IsReduced B]
    (b : B) (hb : ∀ s : B →ₐ[ℂ] ℂ, s b = 0) : b = 0 := by
  letI : IsJacobsonRing B := isJacobsonRing_of_finiteType (A := ℂ)
  have hmem : b ∈ (⊥ : Ideal B).jacobson := by
    apply Ideal.mem_sInf.mpr
    intro m hm
    letI : m.IsMaximal := hm.2
    exact (maximalPoint_eq_zero_iff m b).mp (hb (maximalPoint m))
  rw [← Ideal.radical_eq_jacobson, Ideal.radical_bot_of_isReduced] at hmem
  exact Ideal.mem_bot.mp hmem

theorem reducedFiniteType_algHom_ext [Algebra.FiniteType ℂ B] [IsReduced B]
    {R : Type} [CommRing R] [Algebra ℂ R]
    {φ ψ : R →ₐ[ℂ] B}
    (h : ∀ s : B →ₐ[ℂ] ℂ, s.comp φ = s.comp ψ) : φ = ψ := by
  ext r
  apply sub_eq_zero.mp
  apply reducedFiniteType_pointsDetect
  intro s
  rw [map_sub]
  exact sub_eq_zero.mpr (AlgHom.congr_fun (h s) r)

variable {A : Type} [CommRing A] [Algebra ℂ A]
variable (p : A →ₐ[ℂ] ℂ) (W : Submodule ℂ (Infinitesimal.Tangent A p))

/-- Pointwise containment yields the actual linear equations on a
reduced finite-type affine parameter. Reducedness and finite type are
explicit and are not inferred for the unrestricted Hom parameter. -/
theorem linearEquations_of_points [Algebra.FiniteType ℂ B] [IsReduced B]
    (φ : CoordinateRing p →ₐ[ℂ] B)
    (hφ : ∀ s : B →ₐ[ℂ] ℂ, AffineVelocity.tangentPointEquiv p (s.comp φ) ∈ W) :
    ∀ u ∈ linearRelations p W,
      φ (SymmetricAlgebra.ι ℂ (PointDifferentials p) u) = 0 := by
  intro u hu
  apply reducedFiniteType_pointsDetect
  intro s
  have h := (mem_linearRelations p W u).mp hu
    (AffineVelocity.tangentPointEquiv p (s.comp φ)) (hφ s)
  rw [point_functional] at h
  exact h

/-- An exact algebraic criterion for factorization through the closed
linear target, valid on the actual reduced finite-type parameter ring. -/
theorem factorization_iff_points [Algebra.FiniteType ℂ B] [IsReduced B]
    [FiniteDimensional ℂ W] (φ : CoordinateRing p →ₐ[ℂ] B) :
    (∃ ψ : CoordinateAlgebra p W →ₐ[ℂ] B,
      ψ.comp (quotientMap p W) = φ) ↔
    ∀ s : B →ₐ[ℂ] ℂ, AffineVelocity.tangentPointEquiv p (s.comp φ) ∈ W := by
  constructor
  · rintro ⟨ψ, hψ⟩ s
    have hcomp : s.comp φ = ambientPoint p W (s.comp ψ) := by
      rw [← hψ]
      rfl
    rw [hcomp]
    exact ambientPoint_mem p W (s.comp ψ)
  · intro hφ
    exact (factorization_iff p W φ).mpr (linearEquations_of_points p W φ hφ)

def factorOfPoints [Algebra.FiniteType ℂ B] [IsReduced B]
    (φ : CoordinateRing p →ₐ[ℂ] B)
    (hφ : ∀ s : B →ₐ[ℂ] ℂ, AffineVelocity.tangentPointEquiv p (s.comp φ) ∈ W) :
    CoordinateAlgebra p W →ₐ[ℂ] B :=
  factor p W φ (linearEquations_of_points p W φ hφ)

theorem factorOfPoints_comp [Algebra.FiniteType ℂ B] [IsReduced B]
    (φ : CoordinateRing p →ₐ[ℂ] B)
    (hφ : ∀ s : B →ₐ[ℂ] ℂ, AffineVelocity.tangentPointEquiv p (s.comp φ) ∈ W) :
    (factorOfPoints p W φ hφ).comp (quotientMap p W) = φ := rfl

theorem differential_mem_of_points [Algebra.FiniteType ℂ B] [IsReduced B]
    [FiniteDimensional ℂ W] (φ : CoordinateRing p →ₐ[ℂ] B)
    (hφ : ∀ s : B →ₐ[ℂ] ℂ, AffineVelocity.tangentPointEquiv p (s.comp φ) ∈ W)
    (s : B →ₐ[ℂ] ℂ) (D : Infinitesimal.Tangent B s) :
    ambientDifferential p φ s D ∈ W :=
  ambientDifferential_mem p W φ (linearEquations_of_points p W φ hφ) s D

end ReducedParameters

section PolynomialModel

variable {A : Type} [CommRing A] [Algebra ℂ A]
variable (p : A →ₐ[ℂ] ℂ) (W : Submodule ℂ (Infinitesimal.Tangent A p))

abbrev LinearCoordinates := (PointDifferentials p) ⧸ linearRelations p W

/-- Linear functions on the closed target are precisely point
differentials modulo the actual linear relations of W. -/
def quotientLinearGenerator :
    LinearCoordinates p W →ₗ[ℂ] CoordinateAlgebra p W :=
  (linearRelations p W).liftQ
    ((quotientMap p W).toLinearMap.comp (SymmetricAlgebra.ι ℂ (PointDifferentials p)))
    (by intro u hu; exact quotientMap_linearRelation p W u hu)

@[simp] theorem quotientLinearGenerator_mk (u : PointDifferentials p) :
    quotientLinearGenerator p W ((linearRelations p W).mkQ u) =
      quotientMap p W (SymmetricAlgebra.ι ℂ (PointDifferentials p) u) := rfl

def fromSymmetric :
    SymmetricAlgebra ℂ (LinearCoordinates p W) →ₐ[ℂ] CoordinateAlgebra p W :=
  SymmetricAlgebra.lift (quotientLinearGenerator p W)

def toSymmetric :
    CoordinateAlgebra p W →ₐ[ℂ] SymmetricAlgebra ℂ (LinearCoordinates p W) :=
  factor p W
    (SymmetricAlgebra.lift
      ((SymmetricAlgebra.ι ℂ (LinearCoordinates p W)).comp (linearRelations p W).mkQ))
    (by
      intro u hu
      rw [SymmetricAlgebra.lift_ι_apply]
      change SymmetricAlgebra.ι ℂ (LinearCoordinates p W)
        ((linearRelations p W).mkQ u) = 0
      rw [Submodule.mkQ_apply,
        (Submodule.Quotient.mk_eq_zero (linearRelations p W)).mpr hu, map_zero])

theorem toSymmetric_quotientGenerator (u : PointDifferentials p) :
    toSymmetric p W (quotientMap p W (SymmetricAlgebra.ι ℂ (PointDifferentials p) u)) =
      SymmetricAlgebra.ι ℂ (LinearCoordinates p W) ((linearRelations p W).mkQ u) := by
  change SymmetricAlgebra.lift _ (SymmetricAlgebra.ι ℂ (PointDifferentials p) u) = _
  rw [SymmetricAlgebra.lift_ι_apply]
  rfl

theorem fromSymmetric_quotientGenerator (u : PointDifferentials p) :
    fromSymmetric p W
      (SymmetricAlgebra.ι ℂ (LinearCoordinates p W) ((linearRelations p W).mkQ u)) =
      quotientMap p W (SymmetricAlgebra.ι ℂ (PointDifferentials p) u) := by
  rw [fromSymmetric, SymmetricAlgebra.lift_ι_apply]
  rfl

theorem toSymmetric_fromSymmetric :
    (toSymmetric p W).comp (fromSymmetric p W) =
      AlgHom.id ℂ (SymmetricAlgebra ℂ (LinearCoordinates p W)) := by
  apply SymmetricAlgebra.algHom_ext
  apply LinearMap.ext
  intro u
  obtain ⟨v, rfl⟩ := (linearRelations p W).mkQ_surjective u
  change toSymmetric p W
      (fromSymmetric p W (SymmetricAlgebra.ι ℂ (LinearCoordinates p W)
        ((linearRelations p W).mkQ v))) = _
  rw [fromSymmetric_quotientGenerator, toSymmetric_quotientGenerator]
  rfl

theorem fromSymmetric_toSymmetric :
    (fromSymmetric p W).comp (toSymmetric p W) =
      AlgHom.id ℂ (CoordinateAlgebra p W) := by
  apply coordinate_ext p W
  intro a
  change fromSymmetric p W
    (toSymmetric p W (quotientMap p W
      (SymmetricAlgebra.ι ℂ (PointDifferentials p) (pointDifferential p a)))) = _
  rw [toSymmetric_quotientGenerator, fromSymmetric_quotientGenerator]
  rfl

/-- The quotient ideal imposes exactly the linear equations: the
resulting algebra is the symmetric algebra on the quotient module. -/
def symmetricEquiv :
    CoordinateAlgebra p W ≃ₐ[ℂ] SymmetricAlgebra ℂ (LinearCoordinates p W) :=
  AlgEquiv.ofAlgHom (toSymmetric p W) (fromSymmetric p W)
    (toSymmetric_fromSymmetric p W) (fromSymmetric_toSymmetric p W)

/-- The target algebra is reduced before any finite-dimensionality
assumption; it is a symmetric algebra over the field C. -/
instance coordinateAlgebra_isReduced : IsReduced (CoordinateAlgebra p W) :=
  isReduced_of_injective (symmetricEquiv p W).toRingHom (symmetricEquiv p W).injective

instance linearCoordinates_finite [FiniteDimensional ℂ W] :
    FiniteDimensional ℂ (LinearCoordinates p W) := by
  haveI : FiniteDimensional ℂ (dualImage p W) := inferInstanceAs
    (FiniteDimensional ℂ (W.map (functional p)))
  exact Subspace.finiteDimensional_quot_dualCoannihilator_iff.mpr inferInstance

/-- This map retains the original vector and its canonical functional;
it is used only to count the dimension of the target already constructed. -/
def dualImageEquiv : W ≃ₗ[ℂ] dualImage p W :=
  LinearEquiv.ofBijective
    (((functional p).comp W.subtype).codRestrict (dualImage p W)
      (fun v => (functional_mem_dualImage p W v.val).mpr v.property)) (by
        constructor
        · intro v w h
          apply Subtype.ext
          exact (functionalEquiv p).injective (congrArg Subtype.val h)
        · rintro ⟨q, v, hv, hvq⟩
          exact ⟨⟨v, hv⟩, Subtype.ext hvq⟩)

theorem linearCoordinates_finrank [FiniteDimensional ℂ W] :
    Module.finrank ℂ (LinearCoordinates p W) = Module.finrank ℂ W := by
  haveI : FiniteDimensional ℂ (dualImage p W) := inferInstanceAs
    (FiniteDimensional ℂ (W.map (functional p)))
  let e : LinearCoordinates p W ≃ₗ[ℂ] Module.Dual ℂ (dualImage p W) :=
    LinearEquiv.ofBijective (dualImage p W).quotDualCoannihilatorToDual
      (Subspace.quotDualCoannihilatorToDual_bijective (dualImage p W))
  calc
    Module.finrank ℂ (LinearCoordinates p W) =
        Module.finrank ℂ (Module.Dual ℂ (dualImage p W)) := e.finrank_eq
    _ = Module.finrank ℂ (dualImage p W) := Subspace.dual_finrank_eq
    _ = Module.finrank ℂ W := (dualImageEquiv p W).finrank_eq.symm

/-- A polynomial presentation of the actual closed target. Coordinates
are chosen only after its canonical inclusion and tangent maps exist. -/
def polynomialEquiv [FiniteDimensional ℂ W] :
    CoordinateAlgebra p W ≃ₐ[ℂ]
      MvPolynomial (Fin (Module.finrank ℂ (LinearCoordinates p W))) ℂ :=
  (symmetricEquiv p W).trans
    (SymmetricAlgebra.equivMvPolynomial (Module.finBasis ℂ (LinearCoordinates p W)))

instance coordinateAlgebra_finiteType [FiniteDimensional ℂ W] :
    Algebra.FiniteType ℂ (CoordinateAlgebra p W) :=
  Algebra.FiniteType.of_surjective (polynomialEquiv p W).symm.toAlgHom
    (polynomialEquiv p W).symm.surjective

instance coordinateAlgebra_standardSmooth [FiniteDimensional ℂ W] :
    Algebra.IsStandardSmoothOfRelativeDimension
      (Module.finrank ℂ (LinearCoordinates p W)) ℂ (CoordinateAlgebra p W) :=
  Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv
    (Module.finrank ℂ (LinearCoordinates p W)) (polynomialEquiv p W).symm

/-- Smoothness belongs to the actual quotient target and is derived
from its polynomial presentation. No smoothness premise is requested. -/
instance toC_smoothOfRelativeDimension [FiniteDimensional ℂ W] :
    AlgebraicGeometry.SmoothOfRelativeDimension
      (Module.finrank ℂ (LinearCoordinates p W)) (toC p W) := by
  change AlgebraicGeometry.SmoothOfRelativeDimension _
    (Spec.map (CommRingCat.ofHom (algebraMap ℂ (CoordinateAlgebra p W))))
  rw [HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.SmoothOfRelativeDimension _)]
  apply RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso
  change RingHom.IsStandardSmoothOfRelativeDimension
    (Module.finrank ℂ (LinearCoordinates p W)) (algebraMap ℂ (CoordinateAlgebra p W))
  exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap
    (Module.finrank ℂ (LinearCoordinates p W))).mpr inferInstance

end PolynomialModel

end LeBrunSalamon.Construction.Lines.LinearVelocityTarget

namespace LeBrunSalamon.Construction.Lines.ContactVelocityTarget

variable {n : ℕ} (X : ContactFanoManifold n) (x : ComplexPoint X.variety)
variable (C : GlobalVelocity.TargetChart X.variety x)

/-- The contact target is the image of the original contact plane under
the evaluation determined by actual local differentials. It is not the
entire ambient chart-derivation space. -/
def image : Submodule ℂ (Infinitesimal.Tangent C.Ring C.evaluation) :=
  (contactPlane X x).map (IntrinsicTangent.chartEvaluation C)

instance image_finite : FiniteDimensional ℂ (image X x C) := by
  letI : FiniteDimensional ℂ (TangentFiber X.variety x) :=
    fiber_finite (intrinsicTangentBundle X.variety) x.map
  exact inferInstanceAs
    (FiniteDimensional ℂ ((contactPlane X x).map (IntrinsicTangent.chartEvaluation C)))

/-- Restriction of the actual injective chart evaluation to the original
contact plane; its codomain is precisely its defined image. -/
def imageEquiv : contactPlane X x ≃ₗ[ℂ] image X x C :=
  LinearEquiv.ofBijective
    (((IntrinsicTangent.chartEvaluation C).comp (contactPlane X x).subtype).codRestrict
      (image X x C) (fun v => ⟨v.val, v.property, rfl⟩)) (by
        constructor
        · intro v w h
          apply Subtype.ext
          exact IntrinsicTangent.chartEvaluation_injective C (congrArg Subtype.val h)
        · rintro ⟨v, w, hw, hwv⟩
          exact ⟨⟨w, hw⟩, Subtype.ext hwv⟩)

@[simp] theorem imageEquiv_apply (v : contactPlane X x) :
    (imageEquiv X x C v).val = IntrinsicTangent.chartEvaluation C v.val := rfl

theorem imageEquiv_symm_normalized (v : image X x C) :
    IntrinsicTangent.chartEvaluation C ((imageEquiv X x C).symm v).val = v.val :=
  congrArg Subtype.val ((imageEquiv X x C).apply_symm_apply v)

theorem mem_image_iff (v : TangentFiber X.variety x) :
    IntrinsicTangent.chartEvaluation C v ∈ image X x C ↔ v ∈ contactPlane X x := by
  constructor
  · rintro ⟨w, hw, hwv⟩
    exact IntrinsicTangent.chartEvaluation_injective C hwv ▸ hw
  · intro hv
    exact ⟨v, hv, rfl⟩

theorem image_finrank : Module.finrank ℂ (image X x C) = 2*n := by
  rw [← (imageEquiv X x C).finrank_eq]
  exact contactPlane_dimension X x

abbrev CoordinateAlgebra :=
  LinearVelocityTarget.CoordinateAlgebra C.evaluation (image X x C)

abbrev scheme : Scheme := LinearVelocityTarget.scheme C.evaluation (image X x C)

def toC : scheme X x C ⟶ ComplexBase :=
  LinearVelocityTarget.toC C.evaluation (image X x C)

def inclusion : scheme X x C ⟶ AffineVelocity.tangentScheme C.evaluation :=
  LinearVelocityTarget.inclusion C.evaluation (image X x C)

instance inclusion_isClosedImmersion : IsClosedImmersion (inclusion X x C) :=
  LinearVelocityTarget.inclusion_isClosedImmersion C.evaluation (image X x C)

theorem inclusion_overC :
    inclusion X x C ≫ AffineVelocity.tangentSchemeToC C.evaluation = toC X x C :=
  LinearVelocityTarget.inclusion_overC C.evaluation (image X x C)

/-- Complex points of the actual closed target are the original contact
vectors, with normalization inherited from chart evaluation. -/
def pointEquiv : (CoordinateAlgebra X x C →ₐ[ℂ] ℂ) ≃ contactPlane X x :=
  (LinearVelocityTarget.pointEquiv C.evaluation (image X x C)).trans
    (imageEquiv X x C).symm.toEquiv

theorem pointEquiv_normalized (q : CoordinateAlgebra X x C →ₐ[ℂ] ℂ) :
    IntrinsicTangent.chartEvaluation C (pointEquiv X x C q).val =
      AffineVelocity.tangentPointEquiv C.evaluation
        (LinearVelocityTarget.ambientPoint C.evaluation (image X x C) q) :=
  imageEquiv_symm_normalized X x C
    (LinearVelocityTarget.pointEquiv C.evaluation (image X x C) q)

/-- Tangents to the actual contact target are identified with the
original contact fiber through its actual closed immersion differential. -/
def tangentEquiv (q : CoordinateAlgebra X x C →ₐ[ℂ] ℂ) :
    Infinitesimal.Tangent (CoordinateAlgebra X x C) q ≃ₗ[ℂ] contactPlane X x :=
  (LinearVelocityTarget.tangentEquiv C.evaluation (image X x C) q).trans
    (imageEquiv X x C).symm

theorem tangentEquiv_normalized (q : CoordinateAlgebra X x C →ₐ[ℂ] ℂ)
    (D : Infinitesimal.Tangent (CoordinateAlgebra X x C) q) :
    IntrinsicTangent.chartEvaluation C (tangentEquiv X x C q D).val =
      LinearVelocityTarget.inclusionDifferential C.evaluation (image X x C) q D :=
  imageEquiv_symm_normalized X x C
    (LinearVelocityTarget.tangentEquiv C.evaluation (image X x C) q D)

theorem tangent_finrank (q : CoordinateAlgebra X x C →ₐ[ℂ] ℂ) :
    Module.finrank ℂ (Infinitesimal.Tangent (CoordinateAlgebra X x C) q) = 2*n := by
  rw [(tangentEquiv X x C q).finrank_eq]
  exact contactPlane_dimension X x

theorem linearCoordinates_finrank :
    Module.finrank ℂ
      (LinearVelocityTarget.LinearCoordinates C.evaluation (image X x C)) = 2*n := by
  rw [LinearVelocityTarget.linearCoordinates_finrank, image_finrank]

/-- A finite polynomial presentation of the actual contact target uses
exactly 2n generators. Its embedding was already fixed canonically. -/
def polynomialEquiv : CoordinateAlgebra X x C ≃ₐ[ℂ] MvPolynomial (Fin (2*n)) ℂ := by
  have h := LinearVelocityTarget.polynomialEquiv C.evaluation (image X x C)
  rw [linearCoordinates_finrank X x C] at h
  exact h

instance coordinateAlgebra_isReduced : IsReduced (CoordinateAlgebra X x C) :=
  LinearVelocityTarget.coordinateAlgebra_isReduced C.evaluation (image X x C)

instance coordinateAlgebra_finiteType : Algebra.FiniteType ℂ (CoordinateAlgebra X x C) :=
  LinearVelocityTarget.coordinateAlgebra_finiteType C.evaluation (image X x C)

instance coordinateAlgebra_standardSmooth :
    Algebra.IsStandardSmoothOfRelativeDimension (2*n) ℂ (CoordinateAlgebra X x C) :=
  Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv (2*n) (polynomialEquiv X x C).symm

/-- The actual contact target is smooth of relative dimension 2n.
This has the dimension needed by the manuscript's derivative-sum map. -/
instance toC_smoothOfRelativeDimension :
    AlgebraicGeometry.SmoothOfRelativeDimension (2*n) (toC X x C) := by
  have h := LinearVelocityTarget.toC_smoothOfRelativeDimension C.evaluation (image X x C)
  rw [linearCoordinates_finrank X x C] at h
  exact h

end LeBrunSalamon.Construction.Lines.ContactVelocityTarget

end

/-!
## Actual addition and parameter differentials in the closed contact target

The addition comorphism descends through the same genuine linear ideal as
the closed velocity target. Its source is the spectrum of the tensor product,
canonically the actual fiber product over C. Pointwise and infinitesimal
normalizations are both proved. The tensor-product tangent equivalence retains
the two original parameter derivations and gives the exact derivative sum.
Thus later generic smoothness must concern this actual sum morphism into the
2n-dimensional contact target, rather than a supplied surjective linear map.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirty
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction

namespace LeBrunSalamon.Construction.Lines.LinearVelocityAddition

open LinearVelocityTarget

section SumComorphisms

variable {A B C : Type} [CommRing A] [Algebra ℂ A]
variable [CommRing B] [Algebra ℂ B] [CommRing C] [Algebra ℂ C]
variable (p : A →ₐ[ℂ] ℂ) (W : Submodule ℂ (Infinitesimal.Tangent A p))

/-- The linear part of addition on the actual quotient coordinate
algebra, with both maps taking values in the same test algebra. -/
def sumGenerator (φ ψ : CoordinateAlgebra p W →ₐ[ℂ] B) :
    AffineVelocity.PointDifferentials p →ₗ[ℂ] B :=
  φ.toLinearMap.comp ((quotientMap p W).toLinearMap.comp
      (SymmetricAlgebra.ι ℂ (AffineVelocity.PointDifferentials p))) +
  ψ.toLinearMap.comp ((quotientMap p W).toLinearMap.comp
      (SymmetricAlgebra.ι ℂ (AffineVelocity.PointDifferentials p)))

/-- Addition descends because each genuine defining linear equation
vanishes separately in the two summands. -/
def sum (φ ψ : CoordinateAlgebra p W →ₐ[ℂ] B) : CoordinateAlgebra p W →ₐ[ℂ] B :=
  factor p W (SymmetricAlgebra.lift (sumGenerator p W φ ψ)) (by
    intro u hu
    rw [SymmetricAlgebra.lift_ι_apply]
    change φ (quotientMap p W (SymmetricAlgebra.ι ℂ (AffineVelocity.PointDifferentials p) u)) +
      ψ (quotientMap p W (SymmetricAlgebra.ι ℂ (AffineVelocity.PointDifferentials p) u)) = 0
    rw [quotientMap_linearRelation p W u hu]
    simp only [map_zero, add_zero])

@[simp] theorem sum_coordinate (φ ψ : CoordinateAlgebra p W →ₐ[ℂ] B) (a : A) :
    sum p W φ ψ (coordinate p W a) =
      φ (coordinate p W a) + ψ (coordinate p W a) := by
  change SymmetricAlgebra.lift (sumGenerator p W φ ψ)
    (SymmetricAlgebra.ι ℂ (AffineVelocity.PointDifferentials p)
      (AffineVelocity.pointDifferential p a)) = _
  rw [SymmetricAlgebra.lift_ι_apply]
  rfl

theorem sum_comm (φ ψ : CoordinateAlgebra p W →ₐ[ℂ] B) :
    sum p W φ ψ = sum p W ψ φ := by
  apply coordinate_ext p W
  intro a
  simp only [sum_coordinate, add_comm]

theorem sum_assoc (φ ψ χ : CoordinateAlgebra p W →ₐ[ℂ] B) :
    sum p W (sum p W φ ψ) χ = sum p W φ (sum p W ψ χ) := by
  apply coordinate_ext p W
  intro a
  simp only [sum_coordinate, add_assoc]

/-- Change of test algebra commutes with the constructed addition on
all coordinates and therefore on the whole quotient algebra. -/
theorem sum_natural (φ ψ : CoordinateAlgebra p W →ₐ[ℂ] B) (g : B →ₐ[ℂ] C) :
    g.comp (sum p W φ ψ) = sum p W (g.comp φ) (g.comp ψ) := by
  apply coordinate_ext p W
  intro a
  simp only [AlgHom.comp_apply, sum_coordinate, map_add]

def zeroPoint : CoordinateAlgebra p W →ₐ[ℂ] B :=
  (Algebra.ofId ℂ B).comp (pointOfVector p W 0)

@[simp] theorem zeroPoint_coordinate (a : A) :
    zeroPoint p W (B := B) (coordinate p W a) = 0 := by
  change algebraMap ℂ B (pointOfVector p W 0 (coordinate p W a)) = 0
  rw [pointOfVector_coordinate]
  exact map_zero (algebraMap ℂ B)

theorem sum_zero (φ : CoordinateAlgebra p W →ₐ[ℂ] B) :
    sum p W φ (zeroPoint p W) = φ := by
  apply coordinate_ext p W
  intro a
  simp only [sum_coordinate, zeroPoint_coordinate, add_zero]

theorem zero_sum (φ : CoordinateAlgebra p W →ₐ[ℂ] B) :
    sum p W (zeroPoint p W) φ = φ := by
  rw [sum_comm, sum_zero]

/-- Scaling by a regular function on the test scheme also respects
the actual homogeneous linear equations. -/
def scale (r : B) (φ : CoordinateAlgebra p W →ₐ[ℂ] B) :
    CoordinateAlgebra p W →ₐ[ℂ] B :=
  factor p W
    (SymmetricAlgebra.lift
      ((LinearMap.mul ℂ B r).comp
        (φ.toLinearMap.comp ((quotientMap p W).toLinearMap.comp
          (SymmetricAlgebra.ι ℂ (AffineVelocity.PointDifferentials p)))))) (by
      intro u hu
      rw [SymmetricAlgebra.lift_ι_apply]
      change r * φ (quotientMap p W
        (SymmetricAlgebra.ι ℂ (AffineVelocity.PointDifferentials p) u)) = 0
      rw [quotientMap_linearRelation p W u hu, map_zero, mul_zero])

@[simp] theorem scale_coordinate (r : B)
    (φ : CoordinateAlgebra p W →ₐ[ℂ] B) (a : A) :
    scale p W r φ (coordinate p W a) = r * φ (coordinate p W a) := by
  change SymmetricAlgebra.lift _
    (SymmetricAlgebra.ι ℂ (AffineVelocity.PointDifferentials p)
      (AffineVelocity.pointDifferential p a)) = _
  rw [SymmetricAlgebra.lift_ι_apply]
  rfl

theorem scale_natural (r : B) (φ : CoordinateAlgebra p W →ₐ[ℂ] B)
    (g : B →ₐ[ℂ] C) :
    g.comp (scale p W r φ) = scale p W (g r) (g.comp φ) := by
  apply coordinate_ext p W
  intro a
  simp only [AlgHom.comp_apply, scale_coordinate, map_mul]

theorem scale_one (φ : CoordinateAlgebra p W →ₐ[ℂ] B) : scale p W 1 φ = φ := by
  apply coordinate_ext p W
  intro a
  simp only [scale_coordinate, one_mul]

theorem scale_mul (r t : B) (φ : CoordinateAlgebra p W →ₐ[ℂ] B) :
    scale p W r (scale p W t φ) = scale p W (r*t) φ := by
  apply coordinate_ext p W
  intro a
  simp only [scale_coordinate, mul_assoc]

theorem scale_sum (r : B) (φ ψ : CoordinateAlgebra p W →ₐ[ℂ] B) :
    scale p W r (sum p W φ ψ) = sum p W (scale p W r φ) (scale p W r ψ) := by
  apply coordinate_ext p W
  intro a
  simp only [scale_coordinate, sum_coordinate, mul_add]

theorem pointEquiv_sum [FiniteDimensional ℂ W]
    (q r : CoordinateAlgebra p W →ₐ[ℂ] ℂ) :
    pointEquiv p W (sum p W q r) = pointEquiv p W q + pointEquiv p W r := by
  apply Subtype.ext
  apply Subtype.ext
  apply LinearMap.ext
  intro a
  exact sum_coordinate p W q r a

theorem pointEquiv_scale [FiniteDimensional ℂ W]
    (c : ℂ) (q : CoordinateAlgebra p W →ₐ[ℂ] ℂ) :
    pointEquiv p W (scale p W c q) = c • pointEquiv p W q := by
  apply Subtype.ext
  apply Subtype.ext
  apply LinearMap.ext
  intro a
  exact scale_coordinate p W c q a

end SumComorphisms

section ActualProductSchemes

variable (B C : Type) [CommRing B] [Algebra ℂ B] [CommRing C] [Algebra ℂ C]

abbrev productScheme : Scheme := Spec (CommRingCat.of (B ⊗[ℂ] C))

def productFirst : productScheme B C ⟶ Spec (CommRingCat.of B) :=
  DirectionCones.affineMap (Algebra.TensorProduct.includeLeft : B →ₐ[ℂ] B ⊗[ℂ] C)

def productSecond : productScheme B C ⟶ Spec (CommRingCat.of C) :=
  DirectionCones.affineMap (Algebra.TensorProduct.includeRight : C →ₐ[ℂ] B ⊗[ℂ] C)

/-- The spectrum of the tensor product is the actual parameter fiber
product over the specified complex structure maps. -/
def productSchemeIso : productScheme B C ≅
    pullback (DirectionCones.affineBaseMap B) (DirectionCones.affineBaseMap C) :=
  (AlgebraicGeometry.pullbackSpecIso ℂ B C).symm

theorem productScheme_isPullback :
    IsPullback (productFirst B C) (productSecond B C)
      (DirectionCones.affineBaseMap B) (DirectionCones.affineBaseMap C) :=
  AlgebraicGeometry.isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct ℂ B C)

end ActualProductSchemes

section AdditionMorphisms

variable {A : Type} [CommRing A] [Algebra ℂ A]
variable (p : A →ₐ[ℂ] ℂ) (W : Submodule ℂ (Infinitesimal.Tangent A p))

def additionComorphism : CoordinateAlgebra p W →ₐ[ℂ]
    CoordinateAlgebra p W ⊗[ℂ] CoordinateAlgebra p W :=
  sum (B := CoordinateAlgebra p W ⊗[ℂ] CoordinateAlgebra p W) p W
    (Algebra.TensorProduct.includeLeft :
      CoordinateAlgebra p W →ₐ[ℂ] CoordinateAlgebra p W ⊗[ℂ] CoordinateAlgebra p W)
    (Algebra.TensorProduct.includeRight :
      CoordinateAlgebra p W →ₐ[ℂ] CoordinateAlgebra p W ⊗[ℂ] CoordinateAlgebra p W)

def additionMorphism :
    productScheme (CoordinateAlgebra p W) (CoordinateAlgebra p W) ⟶ scheme p W :=
  DirectionCones.affineMap (additionComorphism p W)

theorem additionMorphism_overC :
    additionMorphism p W ≫ toC p W =
      DirectionCones.affineBaseMap (CoordinateAlgebra p W ⊗[ℂ] CoordinateAlgebra p W) := by
  simpa only [additionMorphism, LinearVelocityTarget.toC] using
    (DirectionCones.affineMap_overC
      (A := CoordinateAlgebra p W)
      (B := CoordinateAlgebra p W ⊗[ℂ] CoordinateAlgebra p W)
      (additionComorphism p W))

variable {B C : Type} [CommRing B] [Algebra ℂ B] [CommRing C] [Algebra ℂ C]

/-- The actual sum of two parameter morphisms, on the actual product
parameter scheme. -/
def parameterSum (φ : CoordinateAlgebra p W →ₐ[ℂ] B)
    (ψ : CoordinateAlgebra p W →ₐ[ℂ] C) : CoordinateAlgebra p W →ₐ[ℂ] B ⊗[ℂ] C :=
  sum p W
    ((Algebra.TensorProduct.includeLeft : B →ₐ[ℂ] B ⊗[ℂ] C).comp φ)
    ((Algebra.TensorProduct.includeRight : C →ₐ[ℂ] B ⊗[ℂ] C).comp ψ)

@[simp] theorem parameterSum_coordinate (φ : CoordinateAlgebra p W →ₐ[ℂ] B)
    (ψ : CoordinateAlgebra p W →ₐ[ℂ] C) (a : A) :
    parameterSum p W φ ψ (coordinate p W a) =
      (φ (coordinate p W a)) ⊗ₜ[ℂ] (1 : C) +
        (1 : B) ⊗ₜ[ℂ] (ψ (coordinate p W a)) := by
  rw [parameterSum, sum_coordinate]
  rfl

theorem parameterSum_eq_map_addition (φ : CoordinateAlgebra p W →ₐ[ℂ] B)
    (ψ : CoordinateAlgebra p W →ₐ[ℂ] C) :
    parameterSum p W φ ψ =
      (Algebra.TensorProduct.map φ ψ).comp (additionComorphism p W) := by
  apply coordinate_ext p W
  intro a
  simp only [AlgHom.comp_apply, additionComorphism, sum_coordinate,
    parameterSum_coordinate, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply, map_add,
    Algebra.TensorProduct.map_tmul, map_one]

def parameterSumMorphism (φ : CoordinateAlgebra p W →ₐ[ℂ] B)
    (ψ : CoordinateAlgebra p W →ₐ[ℂ] C) : productScheme B C ⟶ scheme p W :=
  DirectionCones.affineMap (parameterSum p W φ ψ)

theorem parameterSumMorphism_eq (φ : CoordinateAlgebra p W →ₐ[ℂ] B)
    (ψ : CoordinateAlgebra p W →ₐ[ℂ] C) :
    parameterSumMorphism p W φ ψ =
      DirectionCones.affineMap (Algebra.TensorProduct.map φ ψ) ≫ additionMorphism p W := by
  unfold parameterSumMorphism additionMorphism DirectionCones.affineMap
  rw [← Spec.map_comp]
  exact congrArg (fun f : CoordinateAlgebra p W →ₐ[ℂ] B ⊗[ℂ] C =>
    Spec.map (CommRingCat.ofHom f.toRingHom)) (parameterSum_eq_map_addition p W φ ψ)

theorem parameterSumMorphism_overC (φ : CoordinateAlgebra p W →ₐ[ℂ] B)
    (ψ : CoordinateAlgebra p W →ₐ[ℂ] C) :
    parameterSumMorphism p W φ ψ ≫ toC p W =
      DirectionCones.affineBaseMap (B ⊗[ℂ] C) :=
  DirectionCones.affineMap_overC (parameterSum p W φ ψ)

end AdditionMorphisms

section TensorParameterTangents

variable {B C : Type} [CommRing B] [Algebra ℂ B] [CommRing C] [Algebra ℂ C]

/-- The actual algebra point of the tensor-product parameter, with
its original two rational points retained. -/
def tensorPoint (s : B →ₐ[ℂ] ℂ) (t : C →ₐ[ℂ] ℂ) : B ⊗[ℂ] C →ₐ[ℂ] ℂ :=
  Algebra.TensorProduct.lift s t (fun _ _ => Commute.all _ _)

@[simp] theorem tensorPoint_tmul (s : B →ₐ[ℂ] ℂ) (t : C →ₐ[ℂ] ℂ) (b : B) (c : C) :
    tensorPoint s t (b ⊗ₜ[ℂ] c) = s b * t c := rfl

@[simp] theorem tensorPoint_left (s : B →ₐ[ℂ] ℂ) (t : C →ₐ[ℂ] ℂ) (b : B) :
    tensorPoint s t ((Algebra.TensorProduct.includeLeft : B →ₐ[ℂ] B ⊗[ℂ] C) b) =
      s b := by
  simp only [Algebra.TensorProduct.includeLeft_apply, tensorPoint_tmul, map_one, mul_one]

@[simp] theorem tensorPoint_right (s : B →ₐ[ℂ] ℂ) (t : C →ₐ[ℂ] ℂ) (c : C) :
    tensorPoint s t ((Algebra.TensorProduct.includeRight : C →ₐ[ℂ] B ⊗[ℂ] C) c) =
      t c := by
  simp only [Algebra.TensorProduct.includeRight_apply, tensorPoint_tmul, map_one, one_mul]

/-- The pair of actual dual-number parameter points induces the actual
dual-number point of their fiber product. -/
def tensorJet (s : B →ₐ[ℂ] ℂ) (t : C →ₐ[ℂ] ℂ)
    (D : Infinitesimal.Tangent B s) (E : Infinitesimal.Tangent C t) :
    B ⊗[ℂ] C →ₐ[ℂ] Infinitesimal.Dual :=
  Algebra.TensorProduct.lift (Infinitesimal.tangentToDual s D)
    (Infinitesimal.tangentToDual t E) (fun _ _ => Commute.all _ _)

theorem tensorJet_residue (s : B →ₐ[ℂ] ℂ) (t : C →ₐ[ℂ] ℂ)
    (D : Infinitesimal.Tangent B s) (E : Infinitesimal.Tangent C t) :
    Infinitesimal.residue.comp (tensorJet s t D E) = tensorPoint s t := by
  apply Algebra.TensorProduct.ext'
  intro b c
  change Infinitesimal.residue
    (Infinitesimal.tangentToDual s D b * Infinitesimal.tangentToDual t E c) = s b * t c
  rw [map_mul]
  exact congrArg₂ (fun u v : ℂ => u*v)
    (AlgHom.congr_fun (Infinitesimal.tangentToDual_residue s D) b)
    (AlgHom.congr_fun (Infinitesimal.tangentToDual_residue t E) c)

theorem tensorJet_left (s : B →ₐ[ℂ] ℂ) (t : C →ₐ[ℂ] ℂ)
    (D : Infinitesimal.Tangent B s) (E : Infinitesimal.Tangent C t) (b : B) :
    tensorJet s t D E ((Algebra.TensorProduct.includeLeft : B →ₐ[ℂ] B ⊗[ℂ] C) b) =
      Infinitesimal.tangentToDual s D b := by
  simp only [tensorJet, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.lift_tmul, map_one, mul_one]

theorem tensorJet_right (s : B →ₐ[ℂ] ℂ) (t : C →ₐ[ℂ] ℂ)
    (D : Infinitesimal.Tangent B s) (E : Infinitesimal.Tangent C t) (c : C) :
    tensorJet s t D E ((Algebra.TensorProduct.includeRight : C →ₐ[ℂ] B ⊗[ℂ] C) c) =
      Infinitesimal.tangentToDual t E c := by
  simp only [tensorJet, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.lift_tmul, map_one, one_mul]

/-- The derivation of the actual product dual-number point. Its
Leibniz rule follows from the actual algebra map, retaining nilpotents. -/
def tensorTangent (s : B →ₐ[ℂ] ℂ) (t : C →ₐ[ℂ] ℂ)
    (D : Infinitesimal.Tangent B s) (E : Infinitesimal.Tangent C t) :
    Infinitesimal.Tangent (B ⊗[ℂ] C) (tensorPoint s t) :=
  ⟨{ toFun := fun z => Infinitesimal.linearCoefficient (tensorJet s t D E z)
     map_add' := by intro z w; rw [map_add, Infinitesimal.linearCoefficient_add]
     map_smul' := by
       intro c z
       simp only [map_smul, Infinitesimal.linearCoefficient_smul, RingHom.id_apply] }, by
    intro z w
    change Infinitesimal.linearCoefficient (tensorJet s t D E (z*w)) =
      tensorPoint s t z * Infinitesimal.linearCoefficient (tensorJet s t D E w) +
        tensorPoint s t w * Infinitesimal.linearCoefficient (tensorJet s t D E z)
    rw [map_mul, Infinitesimal.linearCoefficient_mul]
    have hres (v : B ⊗[ℂ] C) :
        Infinitesimal.residue (tensorJet s t D E v) = tensorPoint s t v :=
      AlgHom.congr_fun (tensorJet_residue s t D E) v
    rw [hres z, hres w]⟩

theorem tensorTangent_left (s : B →ₐ[ℂ] ℂ) (t : C →ₐ[ℂ] ℂ)
    (D : Infinitesimal.Tangent B s) (E : Infinitesimal.Tangent C t) (b : B) :
    (tensorTangent s t D E).val
      ((Algebra.TensorProduct.includeLeft : B →ₐ[ℂ] B ⊗[ℂ] C) b) = D.val b := by
  change Infinitesimal.linearCoefficient (tensorJet s t D E _) = _
  rw [tensorJet_left]
  exact Infinitesimal.linearCoefficient_normalForm _ _

theorem tensorTangent_right (s : B →ₐ[ℂ] ℂ) (t : C →ₐ[ℂ] ℂ)
    (D : Infinitesimal.Tangent B s) (E : Infinitesimal.Tangent C t) (c : C) :
    (tensorTangent s t D E).val
      ((Algebra.TensorProduct.includeRight : C →ₐ[ℂ] B ⊗[ℂ] C) c) = E.val c := by
  change Infinitesimal.linearCoefficient (tensorJet s t D E _) = _
  rw [tensorJet_right]
  exact Infinitesimal.linearCoefficient_normalForm _ _

/-- The left parameter direction is the actual projection differential;
the equation of its center is proved by the tensor-point normalization. -/
def leftTangent (s : B →ₐ[ℂ] ℂ) (t : C →ₐ[ℂ] ℂ) :
    Infinitesimal.Tangent (B ⊗[ℂ] C) (tensorPoint s t) →ₗ[ℂ] Infinitesimal.Tangent B s where
  toFun D := ⟨D.val.comp
    (Algebra.TensorProduct.includeLeft : B →ₐ[ℂ] B ⊗[ℂ] C).toLinearMap, by
      intro a b
      change D.val ((Algebra.TensorProduct.includeLeft : B →ₐ[ℂ] B ⊗[ℂ] C) (a*b)) =
        s a * D.val ((Algebra.TensorProduct.includeLeft : B →ₐ[ℂ] B ⊗[ℂ] C) b) +
          s b * D.val ((Algebra.TensorProduct.includeLeft : B →ₐ[ℂ] B ⊗[ℂ] C) a)
      rw [map_mul, D.property, tensorPoint_left, tensorPoint_left]⟩
  map_add' := by intro D E; apply Subtype.ext; apply LinearMap.ext; intro b; rfl
  map_smul' := by intro c D; apply Subtype.ext; apply LinearMap.ext; intro b; rfl

def rightTangent (s : B →ₐ[ℂ] ℂ) (t : C →ₐ[ℂ] ℂ) :
    Infinitesimal.Tangent (B ⊗[ℂ] C) (tensorPoint s t) →ₗ[ℂ] Infinitesimal.Tangent C t where
  toFun D := ⟨D.val.comp
    (Algebra.TensorProduct.includeRight : C →ₐ[ℂ] B ⊗[ℂ] C).toLinearMap, by
      intro a b
      change D.val ((Algebra.TensorProduct.includeRight : C →ₐ[ℂ] B ⊗[ℂ] C) (a*b)) =
        t a * D.val ((Algebra.TensorProduct.includeRight : C →ₐ[ℂ] B ⊗[ℂ] C) b) +
          t b * D.val ((Algebra.TensorProduct.includeRight : C →ₐ[ℂ] B ⊗[ℂ] C) a)
      rw [map_mul, D.property, tensorPoint_right, tensorPoint_right]⟩
  map_add' := by intro D E; apply Subtype.ext; apply LinearMap.ext; intro c; rfl
  map_smul' := by intro b D; apply Subtype.ext; apply LinearMap.ext; intro c; rfl

theorem tangent_tmul (s : B →ₐ[ℂ] ℂ) (t : C →ₐ[ℂ] ℂ)
    (D : Infinitesimal.Tangent (B ⊗[ℂ] C) (tensorPoint s t)) (b : B) (c : C) :
    D.val (b ⊗ₜ[ℂ] c) =
      s b * (rightTangent s t D).val c + t c * (leftTangent s t D).val b := by
  calc
    D.val (b ⊗ₜ[ℂ] c) = D.val
        ((Algebra.TensorProduct.includeLeft : B →ₐ[ℂ] B ⊗[ℂ] C) b *
          (Algebra.TensorProduct.includeRight : C →ₐ[ℂ] B ⊗[ℂ] C) c) := by
      simp only [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    _ = _ := by
      rw [D.property, tensorPoint_left, tensorPoint_right]
      rfl

theorem leftTangent_tensorTangent (s : B →ₐ[ℂ] ℂ) (t : C →ₐ[ℂ] ℂ)
    (D : Infinitesimal.Tangent B s) (E : Infinitesimal.Tangent C t) :
    leftTangent s t (tensorTangent s t D E) = D := by
  apply Subtype.ext
  apply LinearMap.ext
  intro b
  exact tensorTangent_left s t D E b

theorem rightTangent_tensorTangent (s : B →ₐ[ℂ] ℂ) (t : C →ₐ[ℂ] ℂ)
    (D : Infinitesimal.Tangent B s) (E : Infinitesimal.Tangent C t) :
    rightTangent s t (tensorTangent s t D E) = E := by
  apply Subtype.ext
  apply LinearMap.ext
  intro c
  exact tensorTangent_right s t D E c

/-- An actual derivation on the product is determined by its two
projection directions. This uses the tensor-algebra Leibniz rule. -/
theorem tensorTangent_ext (s : B →ₐ[ℂ] ℂ) (t : C →ₐ[ℂ] ℂ)
    {D E : Infinitesimal.Tangent (B ⊗[ℂ] C) (tensorPoint s t)}
    (hleft : leftTangent s t D = leftTangent s t E)
    (hright : rightTangent s t D = rightTangent s t E) : D = E := by
  apply Subtype.ext
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul b c => rw [tangent_tmul, tangent_tmul, hleft, hright]
  | add z w hz hw => simp only [map_add, hz, hw]

/-- The canonical linear equivalence between the actual tensor-product
tangent and the two original parameter tangents. -/
def tensorTangentEquiv (s : B →ₐ[ℂ] ℂ) (t : C →ₐ[ℂ] ℂ) :
    Infinitesimal.Tangent (B ⊗[ℂ] C) (tensorPoint s t) ≃ₗ[ℂ]
      Infinitesimal.Tangent B s × Infinitesimal.Tangent C t :=
  LinearEquiv.ofBijective ((leftTangent s t).prod (rightTangent s t)) (by
    constructor
    · intro D E h
      exact tensorTangent_ext s t (congrArg Prod.fst h) (congrArg Prod.snd h)
    · rintro ⟨D, E⟩
      exact ⟨tensorTangent s t D E,
        Prod.ext (leftTangent_tensorTangent s t D E) (rightTangent_tensorTangent s t D E)⟩)

@[simp] theorem tensorTangentEquiv_apply (s : B →ₐ[ℂ] ℂ) (t : C →ₐ[ℂ] ℂ)
    (D : Infinitesimal.Tangent (B ⊗[ℂ] C) (tensorPoint s t)) :
    tensorTangentEquiv s t D = (leftTangent s t D, rightTangent s t D) := rfl

theorem tensorTangentEquiv_symm (s : B →ₐ[ℂ] ℂ) (t : C →ₐ[ℂ] ℂ)
    (D : Infinitesimal.Tangent B s) (E : Infinitesimal.Tangent C t) :
    (tensorTangentEquiv s t).symm (D,E) = tensorTangent s t D E := by
  apply (tensorTangentEquiv s t).injective
  rw [LinearEquiv.apply_symm_apply, tensorTangentEquiv_apply,
    leftTangent_tensorTangent, rightTangent_tensorTangent]

end TensorParameterTangents

section ActualSumValues

variable {A B C : Type} [CommRing A] [Algebra ℂ A]
variable [CommRing B] [Algebra ℂ B] [CommRing C] [Algebra ℂ C]
variable (p : A →ₐ[ℂ] ℂ) (W : Submodule ℂ (Infinitesimal.Tangent A p))

/-- The actual product-parameter point is sent to the sum of the two
original points of the closed target. -/
theorem parameterSum_point (φ : CoordinateAlgebra p W →ₐ[ℂ] B)
    (ψ : CoordinateAlgebra p W →ₐ[ℂ] C)
    (s : B →ₐ[ℂ] ℂ) (t : C →ₐ[ℂ] ℂ) :
    (tensorPoint s t).comp (parameterSum p W φ ψ) =
      sum p W (s.comp φ) (t.comp ψ) := by
  apply coordinate_ext p W
  intro a
  simp only [AlgHom.comp_apply, parameterSum_coordinate, sum_coordinate,
    map_add, tensorPoint_tmul, map_one, mul_one, one_mul]

theorem pointEquiv_parameterSum [FiniteDimensional ℂ W]
    (φ : CoordinateAlgebra p W →ₐ[ℂ] B) (ψ : CoordinateAlgebra p W →ₐ[ℂ] C)
    (s : B →ₐ[ℂ] ℂ) (t : C →ₐ[ℂ] ℂ) :
    pointEquiv p W ((tensorPoint s t).comp (parameterSum p W φ ψ)) =
      pointEquiv p W (s.comp φ) + pointEquiv p W (t.comp ψ) := by
  rw [parameterSum_point, pointEquiv_sum]

end ActualSumValues

section ActualDifferentialSum

variable {A B C : Type} [CommRing A] [Algebra ℂ A]
variable [CommRing B] [Algebra ℂ B] [CommRing C] [Algebra ℂ C]
variable (p : A →ₐ[ℂ] ℂ) (W : Submodule ℂ (Infinitesimal.Tangent A p))
variable [FiniteDimensional ℂ W]

/-- The actual differential into the closed linear target, followed
by its proved canonical tangent equivalence. -/
def differential (φ : CoordinateAlgebra p W →ₐ[ℂ] B) (s : B →ₐ[ℂ] ℂ) :
    Infinitesimal.Tangent B s →ₗ[ℂ] W :=
  (tangentEquiv p W (s.comp φ)).toLinearMap.comp (Infinitesimal.tangentMap φ s)

@[simp] theorem differential_coordinate
    (φ : CoordinateAlgebra p W →ₐ[ℂ] B) (s : B →ₐ[ℂ] ℂ)
    (D : Infinitesimal.Tangent B s) (a : A) :
    (differential p W φ s D).val.val a = D.val (φ (coordinate p W a)) := rfl

theorem differential_surjective_iff
    (φ : CoordinateAlgebra p W →ₐ[ℂ] B) (s : B →ₐ[ℂ] ℂ) :
    Function.Surjective (differential p W φ s) ↔
      Function.Surjective (Infinitesimal.tangentMap φ s) := by
  constructor
  · intro h v
    obtain ⟨D, hD⟩ := h (tangentEquiv p W (s.comp φ) v)
    exact ⟨D, (tangentEquiv p W (s.comp φ)).injective hD⟩
  · intro h
    exact (tangentEquiv p W (s.comp φ)).surjective.comp h

/-- In a common parameter algebra, the derivative of the constructed
addition is the sum of the two genuine scheme differentials. -/
theorem differential_sum (φ ψ : CoordinateAlgebra p W →ₐ[ℂ] B)
    (s : B →ₐ[ℂ] ℂ) (D : Infinitesimal.Tangent B s) :
    differential p W (sum p W φ ψ) s D =
      differential p W φ s D + differential p W ψ s D := by
  apply Subtype.ext
  apply Subtype.ext
  apply LinearMap.ext
  intro a
  change D.val (sum p W φ ψ (coordinate p W a)) =
    D.val (φ (coordinate p W a)) + D.val (ψ (coordinate p W a))
  rw [sum_coordinate, map_add]

/-- The derivative of regular-function scaling includes its necessary
moving-scalar term; constant scaling is a consequence. -/
theorem differential_scale (r : B) (φ : CoordinateAlgebra p W →ₐ[ℂ] B)
    (s : B →ₐ[ℂ] ℂ) (D : Infinitesimal.Tangent B s) :
    differential p W (scale p W r φ) s D =
      s r • differential p W φ s D + D.val r • pointEquiv p W (s.comp φ) := by
  apply Subtype.ext
  apply Subtype.ext
  apply LinearMap.ext
  intro a
  change D.val (scale p W r φ (coordinate p W a)) =
    s r * D.val (φ (coordinate p W a)) + D.val r * s (φ (coordinate p W a))
  rw [scale_coordinate, D.property]
  ring

theorem differential_constantScale (c : ℂ) (φ : CoordinateAlgebra p W →ₐ[ℂ] B)
    (s : B →ₐ[ℂ] ℂ) (D : Infinitesimal.Tangent B s) :
    differential p W (scale p W (algebraMap ℂ B c) φ) s D =
      c • differential p W φ s D := by
  rw [differential_scale, s.commutes,
    Infinitesimal.tangent_kills_constants B s D c, zero_smul, add_zero]
  rfl

def sumDifferentials (φ : CoordinateAlgebra p W →ₐ[ℂ] B)
    (ψ : CoordinateAlgebra p W →ₐ[ℂ] C)
    (s : B →ₐ[ℂ] ℂ) (t : C →ₐ[ℂ] ℂ) :
    (Infinitesimal.Tangent B s × Infinitesimal.Tangent C t) →ₗ[ℂ] W :=
  (differential p W φ s).coprod (differential p W ψ t)

/-- The actual product-parameter sum morphism has exactly the expected
derivative on every actual tensor-product tangent. -/
theorem differential_parameterSum_apply (φ : CoordinateAlgebra p W →ₐ[ℂ] B)
    (ψ : CoordinateAlgebra p W →ₐ[ℂ] C)
    (s : B →ₐ[ℂ] ℂ) (t : C →ₐ[ℂ] ℂ)
    (D : Infinitesimal.Tangent (B ⊗[ℂ] C) (tensorPoint s t)) :
    differential p W (parameterSum p W φ ψ) (tensorPoint s t) D =
      differential p W φ s (leftTangent s t D) +
        differential p W ψ t (rightTangent s t D) := by
  apply Subtype.ext
  apply Subtype.ext
  apply LinearMap.ext
  intro a
  change D.val (parameterSum p W φ ψ (coordinate p W a)) =
    D.val ((Algebra.TensorProduct.includeLeft : B →ₐ[ℂ] B ⊗[ℂ] C)
      (φ (coordinate p W a))) +
      D.val ((Algebra.TensorProduct.includeRight : C →ₐ[ℂ] B ⊗[ℂ] C)
        (ψ (coordinate p W a)))
  rw [parameterSum_coordinate, map_add]
  rfl

theorem differential_parameterSum (φ : CoordinateAlgebra p W →ₐ[ℂ] B)
    (ψ : CoordinateAlgebra p W →ₐ[ℂ] C)
    (s : B →ₐ[ℂ] ℂ) (t : C →ₐ[ℂ] ℂ) :
    differential p W (parameterSum p W φ ψ) (tensorPoint s t) =
      (sumDifferentials p W φ ψ s t).comp (tensorTangentEquiv s t).toLinearMap := by
  apply LinearMap.ext
  intro D
  exact differential_parameterSum_apply p W φ ψ s t D

theorem differential_parameterSum_tensorTangent
    (φ : CoordinateAlgebra p W →ₐ[ℂ] B) (ψ : CoordinateAlgebra p W →ₐ[ℂ] C)
    (s : B →ₐ[ℂ] ℂ) (t : C →ₐ[ℂ] ℂ)
    (D : Infinitesimal.Tangent B s) (E : Infinitesimal.Tangent C t) :
    differential p W (parameterSum p W φ ψ) (tensorPoint s t) (tensorTangent s t D E) =
      differential p W φ s D + differential p W ψ t E := by
  rw [differential_parameterSum_apply, leftTangent_tensorTangent, rightTangent_tensorTangent]

theorem differential_parameterSum_range
    (φ : CoordinateAlgebra p W →ₐ[ℂ] B) (ψ : CoordinateAlgebra p W →ₐ[ℂ] C)
    (s : B →ₐ[ℂ] ℂ) (t : C →ₐ[ℂ] ℂ) :
    LinearMap.range (differential p W (parameterSum p W φ ψ) (tensorPoint s t)) =
      LinearMap.range (differential p W φ s) ⊔ LinearMap.range (differential p W ψ t) := by
  rw [differential_parameterSum,
    LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _),
    sumDifferentials, LinearMap.range_coprod]

/-- Surjectivity of the true scheme differential of the constructed
sum morphism is equivalent to surjectivity of the sum of its two
original parameter derivatives. Neither surjectivity is assumed here. -/
theorem sumDifferentials_surjective_iff_actual
    (φ : CoordinateAlgebra p W →ₐ[ℂ] B) (ψ : CoordinateAlgebra p W →ₐ[ℂ] C)
    (s : B →ₐ[ℂ] ℂ) (t : C →ₐ[ℂ] ℂ) :
    Function.Surjective (sumDifferentials p W φ ψ s t) ↔
      Function.Surjective (Infinitesimal.tangentMap
        (parameterSum p W φ ψ) (tensorPoint s t)) := by
  rw [← differential_surjective_iff p W (parameterSum p W φ ψ) (tensorPoint s t)]
  constructor
  · intro h v
    obtain ⟨w, hw⟩ := h v
    refine ⟨(tensorTangentEquiv s t).symm w, ?_⟩
    rw [differential_parameterSum]
    change sumDifferentials p W φ ψ s t
      (tensorTangentEquiv s t ((tensorTangentEquiv s t).symm w)) = v
    rw [LinearEquiv.apply_symm_apply]
    exact hw
  · intro h v
    obtain ⟨D, hD⟩ := h v
    refine ⟨tensorTangentEquiv s t D, ?_⟩
    exact (congrArg (fun f => f D) (differential_parameterSum p W φ ψ s t)).symm.trans hD

end ActualDifferentialSum

end LeBrunSalamon.Construction.Lines.LinearVelocityAddition

end

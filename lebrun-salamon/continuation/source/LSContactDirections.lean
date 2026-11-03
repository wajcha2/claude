import LSConeDominance
import LSSelectedPair

/-!
## Actual contact-direction coordinates and the suitable-pair construction

The affine target of the universal Hom velocity was defined from actual
point differentials.  Its polynomial coordinates must be normalized on
those differentials before it can be compared with the affine cones of
projective contact-line directions.  This file makes that normalization
explicit, both for complex points and for first-order tangent vectors.

No compiler has been invoked during this source preparation.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseSeven LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentySix LeBrunSalamon.PhaseTwentySeven
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction
open scoped TensorProduct

namespace LeBrunSalamon.Construction.Lines.VelocityCoordinates

open LinearVelocityTarget

section LinearTarget

open scoped Classical

variable {A : Type} [CommRing A] [Algebra ℂ A]
variable (p : A →ₐ[ℂ] ℂ) (W : Submodule ℂ (Infinitesimal.Tangent A p))
variable [FiniteDimensional ℂ W]

/-- A represented vector acts on the actual quotient of point
differentials.  This is the duality pairing inherited from `da`. -/
def linearPointEquiv : W ≃ₗ[ℂ] Module.Dual ℂ (LinearCoordinates p W) := by
  haveI : FiniteDimensional ℂ (dualImage p W) := inferInstanceAs
    (FiniteDimensional ℂ (W.map (functional p)))
  exact (dualImageEquiv p W).trans
    (LinearEquiv.ofBijective (dualImage p W).quotDualCoannihilatorToDual.flip
      (Subspace.flip_quotDualCoannihilatorToDual_bijective (dualImage p W)))

@[simp] theorem linearPointEquiv_mk (v : W) (u : AffineVelocity.PointDifferentials p) :
    linearPointEquiv p W v ((linearRelations p W).mkQ u) =
      functional p v.val u := rfl

/-- Evaluation on an arbitrary linear generator has the same value as
the intrinsic vector represented by the actual algebra point. -/
theorem linearPointEquiv_point (q : CoordinateAlgebra p W →ₐ[ℂ] ℂ)
    (u : LinearCoordinates p W) :
    linearPointEquiv p W (pointEquiv p W q) u =
      q (quotientLinearGenerator p W u) := by
  obtain ⟨v, rfl⟩ := (linearRelations p W).mkQ_surjective u
  change functional p
    (AffineVelocity.tangentPointEquiv p (ambientPoint p W q)) v =
      q (quotientMap p W (SymmetricAlgebra.ι ℂ (AffineVelocity.PointDifferentials p) v))
  exact point_functional p (ambientPoint p W q) v

/-- The corresponding formula for the actual differential of the closed
linear target.  Its base point is arbitrary, including nonzero velocities. -/
theorem linearPointEquiv_tangent (q : CoordinateAlgebra p W →ₐ[ℂ] ℂ)
    (D : Infinitesimal.Tangent (CoordinateAlgebra p W) q)
    (u : LinearCoordinates p W) :
    linearPointEquiv p W (tangentEquiv p W q D) u =
      D.val (quotientLinearGenerator p W u) := by
  obtain ⟨v, rfl⟩ := (linearRelations p W).mkQ_surjective u
  exact inclusionDifferential_functional p W q D v

variable {I : Type} [Fintype I]
variable (b : Module.Basis I ℂ (LinearCoordinates p W))

/-- The vector coordinates are dual to the chosen basis of actual
linear regular functions, so their normalization is fixed. -/
def frame : W ≃ₗ[ℂ] (I → ℂ) :=
  (linearPointEquiv p W).trans b.dualBasis.equivFun

@[simp] theorem frame_apply (v : W) (i : I) :
    frame p W b v i = linearPointEquiv p W v (b i) := by
  exact b.dualBasis_equivFun _ i

/-- Polynomial presentation of the already constructed closed linear
scheme, using the same basis as the vector coordinates. -/
def algebraEquiv : CoordinateAlgebra p W ≃ₐ[ℂ] MvPolynomial I ℂ :=
  (symmetricEquiv p W).trans (SymmetricAlgebra.equivMvPolynomial b)

@[simp] theorem algebraEquiv_symm_X (i : I) :
    (algebraEquiv p W b).symm (MvPolynomial.X i) =
      quotientLinearGenerator p W (b i) := by
  change fromSymmetric p W
    ((SymmetricAlgebra.equivMvPolynomial b).symm (MvPolynomial.X i)) = _
  rw [SymmetricAlgebra.equivMvPolynomial_symm_X, fromSymmetric,
    SymmetricAlgebra.lift_ι_apply]

/-- An actual lift of a linear coordinate to the original point-
differential module. Different lifts have the same restriction to W. -/
def basisLift (i : I) : AffineVelocity.PointDifferentials p :=
  Classical.choose ((linearRelations p W).mkQ_surjective (b i))

@[simp] theorem basisLift_spec (i : I) :
    (linearRelations p W).mkQ (basisLift p W b i) = b i :=
  Classical.choose_spec ((linearRelations p W).mkQ_surjective (b i))

/-- A genuine coordinate projection defined on the entire ambient
velocity scheme, including its maps from nonreduced parameters. Its
restriction to the closed linear target is fixed by the next identity. -/
def ambientPolynomial : MvPolynomial I ℂ →ₐ[ℂ] AffineVelocity.CoordinateRing p :=
  MvPolynomial.aeval (fun i => SymmetricAlgebra.ι ℂ
    (AffineVelocity.PointDifferentials p) (basisLift p W b i))

@[simp] theorem ambientPolynomial_X (i : I) :
    ambientPolynomial p W b (MvPolynomial.X i) =
      SymmetricAlgebra.ι ℂ (AffineVelocity.PointDifferentials p) (basisLift p W b i) :=
  MvPolynomial.aeval_X _ i

theorem ambientPolynomial_quotient :
    (quotientMap p W).comp (ambientPolynomial p W b) =
      (algebraEquiv p W b).symm.toAlgHom := by
  apply MvPolynomial.algHom_ext
  intro i
  change quotientMap p W (ambientPolynomial p W b (MvPolynomial.X i)) =
    (algebraEquiv p W b).symm (MvPolynomial.X i)
  calc
    _ = quotientMap p W (SymmetricAlgebra.ι ℂ
        (AffineVelocity.PointDifferentials p) (basisLift p W b i)) :=
      congrArg (quotientMap p W) (ambientPolynomial_X p W b i)
    _ = quotientLinearGenerator p W
        ((linearRelations p W).mkQ (basisLift p W b i)) :=
      (quotientLinearGenerator_mk p W (basisLift p W b i)).symm
    _ = quotientLinearGenerator p W (b i) :=
      congrArg (quotientLinearGenerator p W) (basisLift_spec p W b i)
    _ = _ := (algebraEquiv_symm_X p W b i).symm

theorem ambientPolynomial_factor
    {B : Type} [CommRing B] [Algebra ℂ B]
    (φ : AffineVelocity.CoordinateRing p →ₐ[ℂ] B)
    (ψ : CoordinateAlgebra p W →ₐ[ℂ] B)
    (hψ : ψ.comp (quotientMap p W) = φ) :
    φ.comp (ambientPolynomial p W b) =
      ψ.comp (algebraEquiv p W b).symm.toAlgHom := by
  rw [← hψ, AlgHom.comp_assoc, ambientPolynomial_quotient]

/-- On any actual ambient algebra point whose represented vector lies
in W, the chosen projection reads exactly that vector's coordinates. -/
theorem ambientPolynomial_point
    (q : AffineVelocity.CoordinateRing p →ₐ[ℂ] ℂ) (v : W)
    (hv : AffineVelocity.tangentPointEquiv p q = v.val) :
    q.comp (ambientPolynomial p W b) = MvPolynomial.aeval (frame p W b v) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, ambientPolynomial_X, MvPolynomial.aeval_X, frame_apply]
  rw [← basisLift_spec p W b i, linearPointEquiv_mk, ← hv]
  exact (point_functional p q (basisLift p W b i)).symm

/-- The same actual lifted coordinates normalize the differential of
the ambient projection at every ambient base point. -/
theorem ambientPolynomial_tangent
    (q : AffineVelocity.CoordinateRing p →ₐ[ℂ] ℂ)
    (D : Infinitesimal.Tangent (AffineVelocity.CoordinateRing p) q)
    (v : W) (hv : AffineVelocity.tangentTrivialization p q D = v.val) (i : I) :
    frame p W b v i = D.val (ambientPolynomial p W b (MvPolynomial.X i)) := by
  rw [frame_apply, ← basisLift_spec p W b i, linearPointEquiv_mk, ← hv,
    ambientPolynomial_X]
  obtain ⟨a, ha⟩ := AffineVelocity.pointDifferential_surjective p (basisLift p W b i)
  rw [← ha]
  rfl

def ambientProjection : AffineVelocity.tangentScheme p ⟶ DirectionCones.affineSpace I :=
  DirectionCones.affineMap (ambientPolynomial p W b)

@[reassoc] theorem ambientProjection_overC :
    ambientProjection p W b ≫ DirectionCones.affineBaseMap (MvPolynomial I ℂ) =
      AffineVelocity.tangentSchemeToC p :=
  DirectionCones.affineMap_overC (ambientPolynomial p W b)

/-- Complete equality of algebra points, not just equality of their
underlying topological supports. -/
theorem point_comorphism (q : CoordinateAlgebra p W →ₐ[ℂ] ℂ) :
    q.comp (algebraEquiv p W b).symm.toAlgHom =
      MvPolynomial.aeval (frame p W b (pointEquiv p W q)) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe,
    algebraEquiv_symm_X, MvPolynomial.aeval_X, frame_apply]
  change q ((algebraEquiv p W b).symm (MvPolynomial.X i)) =
    linearPointEquiv p W (pointEquiv p W q) (b i)
  exact (congrArg (fun z : CoordinateAlgebra p W => q z)
    (algebraEquiv_symm_X p W b i)).trans
      (linearPointEquiv_point p W q (b i)).symm

theorem point_evaluation (q : CoordinateAlgebra p W →ₐ[ℂ] ℂ)
    (a : CoordinateAlgebra p W) :
    q a = MvPolynomial.eval (frame p W b (pointEquiv p W q))
      (algebraEquiv p W b a) := by
  have h := AlgHom.congr_fun (point_comorphism p W b q) (algebraEquiv p W b a)
  change q ((algebraEquiv p W b).symm (algebraEquiv p W b a)) =
    MvPolynomial.eval (frame p W b (pointEquiv p W q))
      (algebraEquiv p W b a) at h
  have hq : q ((algebraEquiv p W b).symm (algebraEquiv p W b a)) = q a :=
    congrArg (fun z : CoordinateAlgebra p W => q z)
      (AlgEquiv.symm_apply_apply (algebraEquiv p W b) a)
  exact hq.symm.trans h

theorem tangent_coordinates (q : CoordinateAlgebra p W →ₐ[ℂ] ℂ)
    (D : Infinitesimal.Tangent (CoordinateAlgebra p W) q) (i : I) :
    frame p W b (tangentEquiv p W q D) i =
      D.val ((algebraEquiv p W b).symm (MvPolynomial.X i)) := by
  rw [frame_apply, algebraEquiv_symm_X]
  exact linearPointEquiv_tangent p W q D (b i)

def schemeIso : scheme p W ≅ DirectionCones.affineSpace I :=
  Scheme.Spec.mapIso (algebraEquiv p W b).toRingEquiv.toCommRingCatIso.symm.op

@[reassoc] theorem schemeIso_overC :
    (schemeIso p W b).hom ≫ DirectionCones.affineBaseMap (MvPolynomial I ℂ) =
      toC p W :=
  DirectionCones.affineMap_overC (algebraEquiv p W b).symm.toAlgHom

/-- The actual affine isomorphism sends a complex point to precisely
the coordinates of its intrinsic represented vector. -/
theorem point_scheme (q : CoordinateAlgebra p W →ₐ[ℂ] ℂ) :
    DirectionCones.affineMap q ≫ (schemeIso p W b).hom =
      DirectionCones.coordinatePoint (frame p W b (pointEquiv p W q)) := by
  change Spec.map (CommRingCat.ofHom q.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraEquiv p W b).symm.toRingHom) = _
  rw [← Spec.map_comp]
  exact congrArg (fun f : MvPolynomial I ℂ →ₐ[ℂ] ℂ =>
    Spec.map (CommRingCat.ofHom f.toRingHom)) (point_comorphism p W b q)

variable {B C : Type} [CommRing B] [Algebra ℂ B]
variable [CommRing C] [Algebra ℂ C]

/-- The coordinate normalization also respects addition as an actual
algebra map on arbitrary parameter rings. -/
theorem parameterSum_generator
    (φ : CoordinateAlgebra p W →ₐ[ℂ] B)
    (ψ : CoordinateAlgebra p W →ₐ[ℂ] C)
    (u : LinearCoordinates p W) :
    LinearVelocityAddition.parameterSum p W φ ψ (quotientLinearGenerator p W u) =
      φ (quotientLinearGenerator p W u) ⊗ₜ[ℂ] (1 : C) +
        (1 : B) ⊗ₜ[ℂ] ψ (quotientLinearGenerator p W u) := by
  obtain ⟨v, rfl⟩ := (linearRelations p W).mkQ_surjective u
  obtain ⟨a, rfl⟩ := AffineVelocity.pointDifferential_surjective p v
  exact LinearVelocityAddition.parameterSum_coordinate p W φ ψ a

theorem parameterSum_comorphism
    (φ : CoordinateAlgebra p W →ₐ[ℂ] B)
    (ψ : CoordinateAlgebra p W →ₐ[ℂ] C) :
    (LinearVelocityAddition.parameterSum p W φ ψ).comp
        (algebraEquiv p W b).symm.toAlgHom =
      MvPolynomial.aeval (fun i =>
        φ ((algebraEquiv p W b).symm (MvPolynomial.X i)) ⊗ₜ[ℂ] (1 : C) +
          (1 : B) ⊗ₜ[ℂ] ψ ((algebraEquiv p W b).symm (MvPolynomial.X i))) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe,
    MvPolynomial.aeval_X, algebraEquiv_symm_X]
  change LinearVelocityAddition.parameterSum p W φ ψ
    ((algebraEquiv p W b).symm (MvPolynomial.X i)) = _
  exact (congrArg (LinearVelocityAddition.parameterSum p W φ ψ)
    (algebraEquiv_symm_X p W b i)).trans
      (parameterSum_generator p W φ ψ (b i))

end LinearTarget

section ContactTarget

variable {n : ℕ} (X : ContactFanoManifold n) (x : ComplexPoint X.variety)
variable (C : GlobalVelocity.TargetChart X.variety x)

abbrev dimension := 2 * n - 1

include X in
theorem dimension_succ : dimension (n := n) + 1 = 2 * n := by
  have hn := X.positiveContactDimension
  dsimp [dimension]
  omega

/-- The finite coordinate count comes from the original rank of the
contact distribution and from the already proved quotient duality. -/
def contactCoordinateBasis : Module.Basis (Fin (dimension (n := n) + 1)) ℂ
    (LinearCoordinates C.evaluation (ContactVelocityTarget.image X x C)) :=
  Module.finBasisOfFinrankEq ℂ _
    ((ContactVelocityTarget.linearCoordinates_finrank X x C).trans
      (dimension_succ X).symm)

def contactFrame : contactPlane X x ≃ₗ[ℂ] (Fin (dimension (n := n) + 1) → ℂ) :=
  (ContactVelocityTarget.imageEquiv X x C).trans
    (frame C.evaluation (ContactVelocityTarget.image X x C)
      (contactCoordinateBasis X x C))

def contactAlgebraEquiv : ContactVelocityTarget.CoordinateAlgebra X x C ≃ₐ[ℂ]
    MvPolynomial (Fin (dimension (n := n) + 1)) ℂ :=
  algebraEquiv C.evaluation (ContactVelocityTarget.image X x C)
    (contactCoordinateBasis X x C)

/-- The coordinate vector on the cone side is the original contact
vector, as read by the already normalized point equivalence. -/
theorem contact_point_comorphism
    (q : ContactVelocityTarget.CoordinateAlgebra X x C →ₐ[ℂ] ℂ) :
    q.comp (contactAlgebraEquiv X x C).symm.toAlgHom =
      MvPolynomial.aeval
        (contactFrame X x C (ContactVelocityTarget.pointEquiv X x C q)) := by
  have h := point_comorphism C.evaluation (ContactVelocityTarget.image X x C)
    (contactCoordinateBasis X x C) q
  simpa only [contactAlgebraEquiv, contactFrame, ContactVelocityTarget.pointEquiv,
    Equiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.coe_toEquiv,
    LinearEquiv.apply_symm_apply] using h

def contactBasis : Module.Basis (Fin (dimension (n := n) + 1)) ℂ (contactPlane X x) :=
  (Pi.basisFun ℂ (Fin (dimension (n := n) + 1))).map (contactFrame X x C).symm

@[simp] theorem contactBasis_repr (v : contactPlane X x) (i : Fin (dimension (n := n) + 1)) :
    (contactBasis X x C).repr v i = contactFrame X x C v i := by
  simp only [contactBasis, Module.Basis.map_repr, LinearEquiv.symm_symm,
    LinearEquiv.trans_apply, Pi.basisFun_repr]

def omega : Fin (dimension (n := n) + 1) → Fin (dimension (n := n) + 1) → ℂ :=
  LeviFiberGeometry.leviMatrix X x (LeviFiberGeometry.lineFiberFrame X x)
    (contactBasis X x C)

theorem omega_skew (i j : Fin (dimension (n := n) + 1)) :
    omega X x C j i = -omega X x C i j :=
  LeviFiberGeometry.leviMatrix_skew X x (LeviFiberGeometry.lineFiberFrame X x)
    (contactBasis X x C) j i

/-- The nonorthogonality polynomial has the sign and value of the
original line-valued Levi pairing, after its chosen one-dimensional frame. -/
theorem pairing_omega (u v : contactPlane X x) :
    ConePairing.pairing (omega X x C) (contactFrame X x C u) (contactFrame X x C v) =
      LeviFiberGeometry.scalarLevi X x (LeviFiberGeometry.lineFiberFrame X x) u v := by
  have h := LeviFiberGeometry.pairing_leviMatrix X x
    (LeviFiberGeometry.lineFiberFrame X x) (contactBasis X x C) u v
  change ConePairing.pairing
    (LeviFiberGeometry.leviMatrix X x (LeviFiberGeometry.lineFiberFrame X x)
      (contactBasis X x C))
    (fun i => contactFrame X x C u i) (fun i => contactFrame X x C v i) = _
  simpa only [contactBasis_repr] using h

end ContactTarget

end LeBrunSalamon.Construction.Lines.VelocityCoordinates

end

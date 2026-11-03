import LSConeOpen
import LSLeviFiber

/-!
## The intrinsic Levi test defines the actual cone nonorthogonality open

Depends on `LeviFiberGeometry` and `ConeGeometry`. The coefficient matrix
is obtained from the actual line-valued Levi pairing. Changing the
contact-line fiber frame scales its regular function by a unit and leaves
its principal open unchanged, including at nonclosed scheme points.

STATUS: new source; no compilation before the user's 35,000-line gate.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.Skeleton
open scoped BigOperators

namespace LeBrunSalamon.Construction.Lines.LeviConeBridge

open DirectionCones LeviFiberGeometry ConeGeometry

variable {I : Type} [Fintype I]

/-- Scalar extension commutes with multiplying every matrix coefficient
by the same complex scalar, on the entire coefficient algebra. -/
theorem pairing_scale_matrix {A : Type*} [CommRing A] [Algebra ℂ A]
    (c : ℂ) (ω : I → I → ℂ) (a b : I → A) :
    ConePairing.pairing (fun i j => c * ω i j) a b =
      algebraMap ℂ A c * ConePairing.pairing ω a b := by
  classical
  unfold ConePairing.pairing
  simp only [map_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

section ActualContact

variable {n : ℕ} (X : ContactFanoManifold n) (x : ComplexPoint X.variety)
variable (frame : Fiber X.contact.sequence.line.sheaf x.map ≃ₗ[ℂ] ℂ)
variable (B : Module.Basis I ℂ (contactPlane X x)) (S T : Set (I → ℂ))

/-- Membership of the represented complex pair in the genuine principal
open is equivalent to the original intrinsic, witness-based Levi test. -/
theorem pairPoint_mem_nonorthogonalOpen_iff
    (a b : contactPlane X x)
    (ha : (fun i => B.repr a i) ∈ S) (hb : (fun i => B.repr b i) ∈ T)
    (p : ComplexBase) :
    pairPoint S T (fun i => B.repr a i) (fun i => B.repr b i) ha hb p ∈
        nonorthogonalOpen S T (leviMatrix X x frame B) ↔
      NonzeroLeviPair X x (a : TangentFiber X.variety x) (b : TangentFiber X.variety x) :=
  (ConeGeometry.pairPoint_mem_nonorthogonalOpen S T (leviMatrix X x frame B)
    (fun i => B.repr a i) (fun i => B.repr b i) ha hb p).trans
      (pairing_leviMatrix_ne_zero_iff X x frame B a b)

/-- The nonorthogonality open has an actual point whenever the selected
cone vectors have a nonzero intrinsic Levi pairing. -/
theorem nonorthogonalOpen_nonempty_of_intrinsic
    (a b : contactPlane X x)
    (ha : (fun i => B.repr a i) ∈ S) (hb : (fun i => B.repr b i) ∈ T)
    (hab : NonzeroLeviPair X x
      (a : TangentFiber X.variety x) (b : TangentFiber X.variety x)) :
    (nonorthogonalOpen S T (leviMatrix X x frame B) :
      Set (productScheme S T)).Nonempty :=
  ConeGeometry.nonorthogonalOpen_nonempty S T (leviMatrix X x frame B)
    (fun i => B.repr a i) (fun i => B.repr b i) ha hb
      ((pairing_leviMatrix_ne_zero_iff X x frame B a b).mpr hab)

/-- The same intrinsic witness gives a genuine complex-point morphism
to the open subscheme, not merely a point of an auxiliary predicate. -/
def intrinsicNonorthogonalPairPoint
    (a b : contactPlane X x)
    (ha : (fun i => B.repr a i) ∈ S) (hb : (fun i => B.repr b i) ∈ T)
    (hab : NonzeroLeviPair X x
      (a : TangentFiber X.variety x) (b : TangentFiber X.variety x)) :
    ComplexBase ⟶ (nonorthogonalOpen S T (leviMatrix X x frame B)).toScheme :=
  nonorthogonalPairPoint S T (leviMatrix X x frame B)
    (fun i => B.repr a i) (fun i => B.repr b i) ha hb
      ((pairing_leviMatrix_ne_zero_iff X x frame B a b).mpr hab)

@[reassoc]
theorem intrinsicNonorthogonalPairPoint_ι
    (a b : contactPlane X x)
    (ha : (fun i => B.repr a i) ∈ S) (hb : (fun i => B.repr b i) ∈ T)
    (hab : NonzeroLeviPair X x
      (a : TangentFiber X.variety x) (b : TangentFiber X.variety x)) :
    intrinsicNonorthogonalPairPoint X x frame B S T a b ha hb hab ≫
      (nonorthogonalOpen S T (leviMatrix X x frame B)).ι =
        pairPoint S T (fun i => B.repr a i) (fun i => B.repr b i) ha hb :=
  nonorthogonalPairPoint_ι S T (leviMatrix X x frame B)
    (fun i => B.repr a i) (fun i => B.repr b i) ha hb
      ((pairing_leviMatrix_ne_zero_iff X x frame B a b).mpr hab)

/-- Restricted addition still computes the sum of the original contact
vectors in the same actual coordinate equivalence. -/
theorem intrinsicNonorthogonalPairPoint_addition
    (a b : contactPlane X x)
    (ha : (fun i => B.repr a i) ∈ S) (hb : (fun i => B.repr b i) ∈ T)
    (hab : NonzeroLeviPair X x
      (a : TangentFiber X.variety x) (b : TangentFiber X.variety x)) :
    intrinsicNonorthogonalPairPoint X x frame B S T a b ha hb hab ≫
      nonorthogonalAddition S T (leviMatrix X x frame B) =
        coordinatePoint (B.equivFun (a + b)) := by
  rw [intrinsicNonorthogonalPairPoint, nonorthogonalPairPoint_addition]
  exact congrArg coordinatePoint (map_add B.equivFun a b).symm

end ActualContact

section FrameIndependence

variable {n : ℕ} (X : ContactFanoManifold n) (x : ComplexPoint X.variety)
variable (frame frame' : Fiber X.contact.sequence.line.sheaf x.map ≃ₗ[ℂ] ℂ)
variable (B : Module.Basis I ℂ (contactPlane X x)) (S T : Set (I → ℂ))

/-- Changing the contact-line frame multiplies the actual regular cone
function by the image of one nonzero complex scalar in its coordinate ring. -/
theorem pairingFunction_change_frame :
    pairingFunction S T (leviMatrix X x frame' B) =
      (@algebraMap ℂ (ProductRing S T) inferInstance inferInstance inferInstance) (lineFrameRatio X x frame frame') *
        pairingFunction S T (leviMatrix X x frame B) := by
  have hmatrix : leviMatrix X x frame' B =
      fun i j => lineFrameRatio X x frame frame' * leviMatrix X x frame B i j := by
    funext i j
    exact leviMatrix_change_frame X x frame frame' B i j
  rw [hmatrix]
  exact pairing_scale_matrix (lineFrameRatio X x frame frame')
    (leviMatrix X x frame B) (firstCoordinate S T) (secondCoordinate S T)

/-- Equality of opens is proved at every prime ideal of the actual
product coordinate ring. No density of complex points is required. -/
theorem nonorthogonalOpen_frame_independent :
    nonorthogonalOpen S T (leviMatrix X x frame' B) =
      nonorthogonalOpen S T (leviMatrix X x frame B) := by
  have hu : IsUnit (lineFrameRatio X x frame frame') :=
    isUnit_iff_ne_zero.mpr (lineFrameRatio_ne_zero X x frame frame')
  have hunit : IsUnit
      ((@algebraMap ℂ (ProductRing S T) inferInstance inferInstance inferInstance) (lineFrameRatio X x frame frame')) :=
    hu.map ((@algebraMap ℂ (ProductRing S T) inferInstance inferInstance inferInstance))
  unfold nonorthogonalOpen
  rw [pairingFunction_change_frame X x frame frame' B S T]
  ext p
  change ((@algebraMap ℂ (ProductRing S T) inferInstance inferInstance inferInstance) (lineFrameRatio X x frame frame') *
    pairingFunction S T (leviMatrix X x frame B)) ∉ p.asIdeal ↔
      pairingFunction S T (leviMatrix X x frame B) ∉ p.asIdeal
  rw [p.isPrime.mul_mem_iff_mem_or_mem]
  simp only [Ideal.notMem_of_isUnit p.asIdeal hunit, false_or]

end FrameIndependence

end LeBrunSalamon.Construction.Lines.LeviConeBridge

end

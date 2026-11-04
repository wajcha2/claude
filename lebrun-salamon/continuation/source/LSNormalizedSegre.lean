import LSStandardTautological
import RecompileExtensionsPart04Geometry

/-! The normalized Segre quadric and its actual scheme factorization.

Only the generic scheme-image theorem is a published input.  It is stated
for the standard homogeneous coordinates over an arbitrary coefficient
ring.  The test-scheme factorization below is proved from the actual
closed subscheme, not postulated as a conic-family normal form.

This candidate is off the live import graph pending native checking. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.Skeleton LeBrunSalamon.Refinement
open LeBrunSalamon.Construction

namespace LeBrunSalamon.NormalizedSegre

variable (R : Type) [CommRing R]

abbrev Product : Scheme :=
  pullback (StandardTautological.toSpec R 1) (StandardTautological.toSpec R 1)

def left : Product R ⟶ StandardTautological.space R 1 := pullback.fst _ _

def right : Product R ⟶ StandardTautological.space R 1 := pullback.snd _ _

def base : Product R ⟶ Spec (CommRingCat.of R) :=
  left R ≫ StandardTautological.toSpec R 1

def productLine : LineBundle (Product R) :=
  tensorLine (pullbackLine (left R) (StandardTautological.line R 1))
    (pullbackLine (right R) (StandardTautological.line R 1))

def firstIndex : Fin 4 → Fin 2 := ![0, 1, 0, 1]

def secondIndex : Fin 4 → Fin 2 := ![0, 0, 1, 1]

def productCoordinate (i : Fin 4) : AlgebraicSection (productLine R).sheaf :=
  tensorSection (pullSection (left R) (StandardTautological.coordinate R 1 (firstIndex i)))
    (pullSection (right R) (StandardTautological.coordinate R 1 (secondIndex i)))

def quadraticLine : LineBundle (StandardTautological.space R 3) :=
  tensorLine (StandardTautological.line R 3) (StandardTautological.line R 3)

def determinantLeft : AlgebraicSection (quadraticLine R).sheaf :=
  tensorSection (StandardTautological.coordinate R 3 0)
    (StandardTautological.coordinate R 3 3)

def determinantRight : AlgebraicSection (quadraticLine R).sheaf :=
  tensorSection (StandardTautological.coordinate R 3 1)
    (StandardTautological.coordinate R 3 2)

def quadraticTotal : Descent.TotalLine (quadraticLine R) :=
  Classical.choice (Descent.totalLine_exists (quadraticLine R))

/-- The literal scheme-theoretic zero locus of Z₀Z₃-Z₁Z₂. -/
abbrev Quadric : Scheme :=
  Smoothing.StandardSourceProof.SectionEquality.locus (quadraticTotal R)
    (determinantLeft R) (determinantRight R)

def inclusion : Quadric R ⟶ StandardTautological.space R 3 :=
  Smoothing.StandardSourceProof.SectionEquality.inclusion (quadraticTotal R)
    (determinantLeft R) (determinantRight R)

/-- The standard Segre construction and its exact determinant scheme
image.  The section equations fix both the order and the normalization of
the four homogeneous coordinates. -/
structure Data where
  iso : Product R ≅ Quadric R
  over_base : iso.hom ≫ inclusion R ≫ StandardTautological.toSpec R 3 = base R
  line : pullbackModule (iso.hom ≫ inclusion R) (StandardTautological.line R 3).sheaf ≅
    (productLine R).sheaf
  coordinate : ∀ i : Fin 4,
    pullSection (iso.hom ≫ inclusion R) (StandardTautological.coordinate R 3 i) ≫
      line.hom = productCoordinate R i

end LeBrunSalamon.NormalizedSegre

namespace LeBrunSalamon.PublishedInputs.ProjectiveSpace

/-- **Generic published Segre image theorem.** Stacks Project 27.13.6
(01WD) constructs the actual relative Segre map using the line O(1,1)
and the coordinates X₀Y₀, X₁Y₀, X₀Y₁, X₁Y₁, in this order.  Vakil,
*Foundations of Algebraic Geometry*, classes15--16 (2007), §5.B and
Example5.1, identifies its scheme image over any ring A with the ideal
of the 2×2 minors, here the single determinant Z₀Z₃-Z₁Z₂.

`Quadric` is exactly this zero subscheme, implemented as the fibre product
of the two section graphs in their representing total line.  The generic
total-line API and `SectionEquality` already prove its scheme structure
and factorization on arbitrary, possibly nonreduced, test schemes.  No
family, chosen deformation, or project-specific polarization occurs in
this input.  Its quotient-tuple translation is proved in the importing
file.

Primary sources:
https://stacks.math.columbia.edu/tag/01WD
https://math.stanford.edu/~vakil/0708-216/216class1516.pdf
-/
theorem segreQuadric (R : Type) [CommRing R] :
    Nonempty (NormalizedSegre.Data R) := by
  sorry

end LeBrunSalamon.PublishedInputs.ProjectiveSpace

namespace LeBrunSalamon.NormalizedSegre

variable (R : Type) [CommRing R]

def chosen : Data R := Classical.choice (PublishedInputs.ProjectiveSpace.segreQuadric R)

def map : Product R ⟶ StandardTautological.space R 3 :=
  (chosen R).iso.hom ≫ inclusion R

@[reassoc] theorem map_over : map R ≫ StandardTautological.toSpec R 3 = base R :=
  (chosen R).over_base

def mapLine : pullbackModule (map R) (StandardTautological.line R 3).sheaf ≅
    (productLine R).sheaf := (chosen R).line

theorem map_coordinate (i : Fin 4) :
    pullSection (map R) (StandardTautological.coordinate R 3 i) ≫ (mapLine R).hom =
      productCoordinate R i := (chosen R).coordinate i

instance map_isClosedImmersion : IsClosedImmersion (map R) := by
  letI : IsClosedImmersion (inclusion R) :=
    Smoothing.StandardSourceProof.SectionEquality.inclusion_closed (quadraticTotal R)
      (determinantLeft R) (determinantRight R)
  dsimp only [map]
  infer_instance

/-- A map satisfying the literal determinant section equation factors
uniquely through the actual Segre map. This is a proof from the closed
scheme-image statement, with no new functor-of-points input. -/
theorem factorization {T : Scheme} (f : T ⟶ StandardTautological.space R 3)
    (hf : pullSection f (determinantLeft R) = pullSection f (determinantRight R)) :
    ∃! g : T ⟶ Product R, g ≫ map R = f := by
  let q := Smoothing.StandardSourceProof.SectionEquality.lift (quadraticTotal R)
    (determinantLeft R) (determinantRight R) f hf
  refine ⟨q ≫ (chosen R).iso.inv, ?_, ?_⟩
  · dsimp only [map]
    rw [Category.assoc, Iso.inv_hom_id_assoc]
    exact Smoothing.StandardSourceProof.SectionEquality.lift_inclusion
      (quadraticTotal R) (determinantLeft R) (determinantRight R) f hf
  · intro g hg
    apply (cancel_mono (map R)).mp
    rw [hg]
    dsimp only [map]
    rw [Category.assoc, Iso.inv_hom_id_assoc]
    exact (Smoothing.StandardSourceProof.SectionEquality.lift_inclusion
      (quadraticTotal R) (determinantLeft R) (determinantRight R) f hf).symm

/-- The recovered factor has the original base morphism. -/
theorem factorization_over {T : Scheme}
    (f : T ⟶ StandardTautological.space R 3) (g : T ⟶ Product R)
    (hg : g ≫ map R = f) : g ≫ base R = f ≫ StandardTautological.toSpec R 3 := by
  rw [← map_over, ← Category.assoc, hg]

end LeBrunSalamon.NormalizedSegre
end

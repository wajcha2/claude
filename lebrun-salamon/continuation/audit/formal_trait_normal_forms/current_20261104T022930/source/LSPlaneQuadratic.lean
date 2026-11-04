import LSStandardTautological
import RecompileExtensionsPart04Geometry

/-! Literal homogeneous quadratics on the normalized projective plane.
The zero scheme is the scheme-theoretic section zero locus already
implemented by the section-graph fibre product. No admission. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.Skeleton LeBrunSalamon.Refinement
open LeBrunSalamon.Construction

namespace LeBrunSalamon.PlaneQuadratic

variable (A : Type) [CommRing A]

/-- Coefficients in the order a,b,c,alpha,beta,gamma of
a*x²+b*y²+c*z²+alpha*y*z+beta*z*x+gamma*x*y. -/
abbrev Coefficients := Fin 6 → A

def polynomial (q : Coefficients A) : MvPolynomial (Fin 3) A :=
  MvPolynomial.C (q 0) * MvPolynomial.X 0 ^ 2 +
  MvPolynomial.C (q 1) * MvPolynomial.X 1 ^ 2 +
  MvPolynomial.C (q 2) * MvPolynomial.X 2 ^ 2 +
  MvPolynomial.C (q 3) * MvPolynomial.X 1 * MvPolynomial.X 2 +
  MvPolynomial.C (q 4) * MvPolynomial.X 2 * MvPolynomial.X 0 +
  MvPolynomial.C (q 5) * MvPolynomial.X 0 * MvPolynomial.X 1

def discriminant (q : Coefficients A) : A :=
  4 * q 0 * q 1 * q 2 + q 3 * q 4 * q 5 -
    q 0 * q 3 ^ 2 - q 1 * q 4 ^ 2 - q 2 * q 5 ^ 2

def diagonal (c : A) : Coefficients A := ![1, 1, c, 0, 0, 0]

def split (a : A) : Coefficients A := ![0, 0, -a, 0, 0, 1]

@[simp] theorem discriminant_diagonal (c : A) :
    discriminant A (diagonal A c) = 4 * c := by
  simp [discriminant, diagonal]

@[simp] theorem discriminant_split (a : A) :
    discriminant A (split A a) = a := by
  simp [discriminant, split]

abbrev Plane : Scheme := StandardTautological.space A 2

def quadraticLine : LineBundle (Plane A) :=
  tensorLine (StandardTautological.line A 2) (StandardTautological.line A 2)

def firstIndex : Fin 6 → Fin 3 := ![0, 1, 2, 1, 2, 0]

def secondIndex : Fin 6 → Fin 3 := ![0, 1, 2, 2, 0, 1]

def monomial (i : Fin 6) : AlgebraicSection (quadraticLine A).sheaf :=
  tensorSection (StandardTautological.coordinate A 2 (firstIndex i))
    (StandardTautological.coordinate A 2 (secondIndex i))

/-- The actual coefficient inclusion into global functions on P²_A. -/
def coefficient (a : A) : RingSections (Plane A) ⊤ :=
  (StandardTautological.toSpec A 2).appTop
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)

/-- The normalized section of O(1) tensor O(1) attached to q. -/
def sectionOf (q : Coefficients A) : AlgebraicSection (quadraticLine A).sheaf :=
  ∑ i : Fin 6, sectionFromValue (coefficient A (q i) • sectionValue (monomial A i))

def total : Descent.TotalLine (quadraticLine A) :=
  Classical.choice (Descent.totalLine_exists (quadraticLine A))

/-- The actual projective quadratic hypersurface, including nilpotents. -/
abbrev ZeroScheme (q : Coefficients A) : Scheme :=
  Smoothing.StandardSourceProof.SectionEquality.locus (total A) (sectionOf A q) 0

def inclusion (q : Coefficients A) : ZeroScheme A q ⟶ Plane A :=
  Smoothing.StandardSourceProof.SectionEquality.inclusion (total A) (sectionOf A q) 0

def projection (q : Coefficients A) : ZeroScheme A q ⟶ Spec (CommRingCat.of A) :=
  inclusion A q ≫ StandardTautological.toSpec A 2

instance inclusion_isClosedImmersion (q : Coefficients A) :
    IsClosedImmersion (inclusion A q) :=
  Smoothing.StandardSourceProof.SectionEquality.inclusion_closed (total A) (sectionOf A q) 0

theorem zero_equation (q : Coefficients A) :
    pullSection (inclusion A q) (sectionOf A q) = 0 := by
  have h := Smoothing.StandardSourceProof.SectionEquality.equation (total A) (sectionOf A q) 0
  simpa only [inclusion, pullSection, restrictSection, Functor.map_zero, comp_zero] using h

/-- The literal defining equation has the expected universal property on
all test schemes. This is a proved consequence of the chosen zero scheme. -/
theorem universal (q : Coefficients A) {T : Scheme} (f : T ⟶ Plane A)
    (hf : pullSection f (sectionOf A q) = 0) :
    ∃! g : T ⟶ ZeroScheme A q, g ≫ inclusion A q = f := by
  have hz : pullSection f (sectionOf A q) = pullSection f 0 := by
    simpa only [pullSection, restrictSection, Functor.map_zero, comp_zero] using hf
  refine ⟨Smoothing.StandardSourceProof.SectionEquality.lift (total A) (sectionOf A q) 0 f hz,
    Smoothing.StandardSourceProof.SectionEquality.lift_inclusion
      (total A) (sectionOf A q) 0 f hz, ?_⟩
  intro g hg
  apply Smoothing.StandardSourceProof.SectionEquality.hom_ext (total A) (sectionOf A q) 0
  exact hg.trans (Smoothing.StandardSourceProof.SectionEquality.lift_inclusion
    (total A) (sectionOf A q) 0 f hz).symm

/-- Over a local ring this is Tanaka's exact primitive-coefficient
criterion, Proposition2.9(4), for the quadratic to be a conic family. -/
def Primitive (q : Coefficients A) : Prop := ∃ i, IsUnit (q i)

/-- An actual invertible linear coordinate substitution. -/
def linearCoordinate (M : (Matrix (Fin 3) (Fin 3) A)ˣ) (i : Fin 3) :
    MvPolynomial (Fin 3) A :=
  ∑ j : Fin 3, MvPolynomial.C ((M : Matrix (Fin 3) (Fin 3) A) i j) * MvPolynomial.X j

def transformed (q : Coefficients A) (M : (Matrix (Fin 3) (Fin 3) A)ˣ) :
    MvPolynomial (Fin 3) A :=
  (MvPolynomial.bind₁ (linearCoordinate A M)) (polynomial A q)

end LeBrunSalamon.PlaneQuadratic
end

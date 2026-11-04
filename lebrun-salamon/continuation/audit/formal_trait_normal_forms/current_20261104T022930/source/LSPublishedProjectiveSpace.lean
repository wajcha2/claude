import RecompileBasePart06
import LSStandardTautological

/-!
Generic published projective-space inputs and proved coefficient maps.
The project-record translations are proved at their declaration sites.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven
open LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.PhaseSeven

namespace LeBrunSalamon.ProjectiveQuotient

/-- The coefficient map into degree zero of a polynomial grading over any ring. -/
def constants (R : Type) [CommRing R] (N : ℕ) :
    R →+* ↥(MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0) where
  toFun c := ⟨MvPolynomial.C c, MvPolynomial.isHomogeneous_C (Fin (N + 1)) c⟩
  map_zero' := by apply Subtype.ext; simp
  map_one' := by apply Subtype.ext; simp
  map_add' := by intro a b; apply Subtype.ext; simp
  map_mul' := by intro a b; apply Subtype.ext; simp

abbrev space (R : Type) [CommRing R] (N : ℕ) : Scheme :=
  Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)

def toSpec (R : Type) [CommRing R] (N : ℕ) :
    space R N ⟶ Spec (CommRingCat.of R) :=
  Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) ≫
    Spec.map (CommRingCat.ofHom (constants R N))

end LeBrunSalamon.ProjectiveQuotient

namespace LeBrunSalamon.PublishedInputs.ProjectiveSpace

open LeBrunSalamon.ProjectiveQuotient

/-- The universal invertible quotient on polynomial Proj over a ring.

Primary source: Stacks Project, Section 27.13, Tag 01ND, Lemma 27.13.1
and the explicit relative statement immediately after Definition 27.13.2.
The source characterizes the unique morphism over the base by pullback of
the universal sheaf and each generating section. Here global sections are
written as homomorphisms from the unit sheaf; generation is the epimorphism
from the finite coproduct of unit sheaves. Neither ProjectiveCoordinates nor
the project's marked projective line occurs in this input.
-/
theorem universalInvertibleQuotient (R : Type) [CommRing R] (N : ℕ) :
    ∃ (L : (space R N).Modules), IsLocallyFreeOfRank L 1 ∧
      ∃ a : Fin (N + 1) → (structureModule (space R N) ⟶ L),
        Epi (Sigma.desc a) ∧
        ∀ (T : Scheme)
          (s : T ⟶ Spec (CommRingCat.of R))
          (F : T.Modules), IsLocallyFreeOfRank F 1 →
          ∀ b : Fin (N + 1) → (structureModule T ⟶ F),
            Epi (Sigma.desc b) →
            ∃! f : {f : T ⟶ space R N // f ≫ toSpec R N = s},
              ∃ e : pullbackModule f.val L ≅ F,
                ∀ i, pullSection f.val (a i) ≫ e.hom = b i := by
  let d := StandardTautological.chosen R N
  refine ⟨d.sheaf, d.locallyFree, d.coordinate, d.generates, ?_⟩
  exact d.universal

end LeBrunSalamon.PublishedInputs.ProjectiveSpace

namespace LeBrunSalamon.ProjectiveQuotient

open LeBrunSalamon.Skeleton

theorem constants_complex (N : ℕ) : constants ℂ N = constantsToDegreeZero N := by
  ext c
  rfl

theorem toSpec_complex (N : ℕ) : toSpec ℂ N = projectiveBaseMap N := by
  unfold toSpec projectiveBaseMap
  rw [constants_complex]

end LeBrunSalamon.ProjectiveQuotient

namespace LeBrunSalamon.PublishedInputs.ProjectiveSpace

open LeBrunSalamon.ProjectiveQuotient

/-- Stacks Project, Lemma 37.50.1, Tag 0B45, implication (5) ⇒ (2).
The base-ample hypothesis is retained explicitly. H-projectivity is written
out as a closed immersion into the polynomial Proj over the affine base.
No smoothness, contact structure, or project embedding certificate is assumed.
-/
theorem properAmpleClosedImmersion (R : Type) [CommRing R]
    (hbase : ∃ L : LineBundle (Spec (CommRingCat.of R)), IsAmpleLine L)
    {X : Scheme} (s : X ⟶ Spec (CommRingCat.of R)) [IsProper s]
    (hX : ∃ L : LineBundle X, IsAmpleLine L) :
    ∃ (N : ℕ) (i : X ⟶ space R N), IsClosedImmersion i ∧ i ≫ toSpec R N = s := by
  sorry

end LeBrunSalamon.PublishedInputs.ProjectiveSpace

namespace LeBrunSalamon.ProjectiveQuotient

open LeBrunSalamon.Skeleton

/-- The unit line on an affine scheme is ample, directly from the project's
affine-nonvanishing definition. The identity trivializes its first power.
-/
theorem trivialLine_ample (X : Scheme) [IsAffine X] :
    IsAmpleLine (trivialLine X) := by
  refine ⟨inferInstance, ?_⟩
  intro x
  let e : (linePower (trivialLine X) 1).sheaf ≅ structureModule X :=
    TensorConstruction.leftUnitIso (structureModule X)
  refine ⟨1, by decide, e.inv, ?_, ?_⟩
  · rw [(nonvanishingOpen_eq_top_iff _ _).mpr inferInstance]
    trivial
  · rw [(nonvanishingOpen_eq_top_iff _ _).mpr inferInstance]
    exact isAffineOpen_top X

end LeBrunSalamon.ProjectiveQuotient

end

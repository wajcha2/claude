import RecompileSections

/-!
The standard tautological line on polynomial Proj, with its actual homogeneous
coordinate normalization.  The generic input is the canonical construction
in Stacks 27.10.1--27.10.3 and its universal property in 27.13.1/01ND.

The additional local-frame equations specify the standard witness; they are
not asserted about the older arbitrary universal-quotient witness.  There is
no marked point, projective-line degree, or project embedding in the input.
This candidate remains outside source/ until native validation.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight

namespace LeBrunSalamon.StandardTautological

variable (R : Type) [CommRing R] (N : ℕ)

abbrev grading := MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R

abbrev space : Scheme := Proj (grading R N)

/-- Literal coefficient inclusion into the degree-zero homogeneous ring. -/
def constants : R →+* ↥(grading R N 0) where
  toFun c := ⟨MvPolynomial.C c, MvPolynomial.isHomogeneous_C (Fin (N + 1)) c⟩
  map_zero' := by apply Subtype.ext; simp
  map_one' := by apply Subtype.ext; simp
  map_add' := by intro a b; apply Subtype.ext; simp
  map_mul' := by intro a b; apply Subtype.ext; simp

def toSpec : space R N ⟶ Spec (CommRingCat.of R) :=
  Proj.toSpecZero (grading R N) ≫ Spec.map (CommRingCat.ofHom (constants R N))

theorem variable_degree (i : Fin (N + 1)) :
    (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) R) ∈ grading R N 1 :=
  MvPolynomial.isHomogeneous_X _ _

/-- The actual homogeneous-coordinate open of the actual polynomial Proj. -/
def chart (i : Fin (N + 1)) : (space R N).Opens :=
  Proj.basicOpen (grading R N) (MvPolynomial.X i)

/-- The actual function X_j/X_i in the degree-zero homogeneous localization. -/
def ratio (i j : Fin (N + 1)) :
    HomogeneousLocalization.Away (grading R N)
      (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) R) :=
  HomogeneousLocalization.Away.isLocalizationElem
    (variable_degree R N i) (variable_degree R N j)

/-- The same ratio as a section of the actual structure sheaf on D_+(X_i). -/
def ratioSection (i j : Fin (N + 1)) : RingSections (space R N) (chart R N i) :=
  (Proj.basicOpenIsoAway (grading R N) (MvPolynomial.X i)
    (variable_degree R N i) (by decide)).hom (ratio R N i j)

/-- Standard tautological data, including the exact section/frame equations.
The universal property is stated on arbitrary test schemes over Spec R. -/
structure Data where
  sheaf : (space R N).Modules
  locallyFree : IsLocallyFreeOfRank sheaf 1
  coordinate : Fin (N + 1) → AlgebraicSection sheaf
  generates : Epi (Sigma.desc coordinate)
  universal :
    ∀ (T : Scheme) (s : T ⟶ Spec (CommRingCat.of R))
      (F : T.Modules), IsLocallyFreeOfRank F 1 →
      ∀ b : Fin (N + 1) → AlgebraicSection F,
        Epi (Sigma.desc b) →
        ∃! f : {f : T ⟶ space R N // f ≫ toSpec R N = s},
          ∃ e : pullbackModule f.val sheaf ≅ F,
            ∀ i, pullSection f.val (coordinate i) ≫ e.hom = b i
  frame : ∀ i, LocalFrames.OverFrame sheaf (chart R N i)
  coefficient : ∀ i j,
    LocalFrames.coordinates (frame i)
      (Scheme.Modules.Hom.app (coordinate j) (chart R N i)
        (1 : RingSections (space R N) (chart R N i))) = ratioSection R N i j

end LeBrunSalamon.StandardTautological

namespace LeBrunSalamon.PublishedInputs.ProjectiveSpace

/-- The canonical standard tautological construction on polynomial Proj.

Primary source: Stacks Project, Definition 27.10.1 and Lemmas 27.10.2--3
(Tag 01MM), together with Lemma 27.13.1 and the relative characterization
following Definition 27.13.2 (Tag 01ND).  Lemma 27.10.2 proves the displayed
local frame by the actual multiplication map x ↦ X_i x; hence the canonical
section X_j has coefficient X_j/X_i.  The relative characterization specifies
the same O(1) and the same sections X_i, rather than a second unrelated
universal witness.  Restriction to the over site is just the definition of
restriction of this frame to all opens inside D_+(X_i).

This input contains only the standard construction and its documented
universal property.  Comparison with the project's marked-point O(1), the
Laurent transition, and all project-coordinate packaging are proved below
or in the importing translation file.  Source match audited; native check
and full current graph replay are pending.
-/
theorem standardTautological (R : Type) [CommRing R] (N : ℕ) :
    Nonempty (StandardTautological.Data R N) := by
  sorry

end LeBrunSalamon.PublishedInputs.ProjectiveSpace

namespace LeBrunSalamon.StandardTautological

variable (R : Type) [CommRing R] (N : ℕ)

/-- A single selection supplies every line, section, and chart frame below. -/
def chosen : Data R N :=
  Classical.choice (PublishedInputs.ProjectiveSpace.standardTautological R N)

def line : LineBundle (space R N) :=
  ⟨(chosen R N).sheaf, (chosen R N).locallyFree⟩

def coordinate (i : Fin (N + 1)) : AlgebraicSection (line R N).sheaf :=
  (chosen R N).coordinate i

def frame (i : Fin (N + 1)) :
    LocalFrames.OverFrame (line R N).sheaf (chart R N i) :=
  (chosen R N).frame i

theorem section_coordinates (i j : Fin (N + 1)) :
    LocalFrames.coordinates (frame R N i)
      (Scheme.Modules.Hom.app (coordinate R N j) (chart R N i)
        (1 : RingSections (space R N) (chart R N i))) = ratioSection R N i j :=
  (chosen R N).coefficient i j

theorem generates : Epi (Sigma.desc (coordinate R N)) :=
  (chosen R N).generates

end LeBrunSalamon.StandardTautological

end

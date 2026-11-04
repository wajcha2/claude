import LSStandardTautological

/-! The binary quadratic Veronese construction on the literal standard
polynomial Proj. The only admission is this generic classical construction;
no selected curve, marked degree, deformation or family occurs in it. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight

namespace LeBrunSalamon.QuadraticVeronese

variable (R : Type) [CommRing R]

def squareLine : LineBundle (StandardTautological.space R 1) :=
  tensorLine (StandardTautological.line R 1) (StandardTautological.line R 1)

def monomials : Fin 3 → AlgebraicSection (squareLine R).sheaf :=
  ![tensorSection (StandardTautological.coordinate R 1 0)
      (StandardTautological.coordinate R 1 0),
    tensorSection (StandardTautological.coordinate R 1 0)
      (StandardTautological.coordinate R 1 1),
    tensorSection (StandardTautological.coordinate R 1 1)
      (StandardTautological.coordinate R 1 1)]

end LeBrunSalamon.QuadraticVeronese

namespace LeBrunSalamon.PublishedInputs.ProjectiveSpace

/-- The quadratic Veronese closed immersion, with its standard quotient
line and its three monomials.

Primary source: Ravi Vakil, Foundations of Algebraic Geometry, June 27,
2011, §9.2.6, Exercise 9.2.I and Remark 9.2.8; §16.2.D identifies
O(1) ⊗ O(1) with O(2), and §17.4.5--6 identifies the
same morphism with the complete O(2) linear series. Exercise 21.1.D
explicitly recalls that the earlier closed-immersion result was proved
over an arbitrary base ring. The ordering is exactly [X0²,X0X1,X1²].
The line comparison is the one defining this linear-series morphism,
not a statement about a second arbitrary projective quotient witness.

All applications to a chosen degree-two line or a family require their
actual comparisons and are proved separately.
-/
theorem quadraticVeronese (R : Type) [CommRing R] :
    ∃ f : StandardTautological.space R 1 ⟶ StandardTautological.space R 2,
      f ≫ StandardTautological.toSpec R 2 = StandardTautological.toSpec R 1 ∧
      IsClosedImmersion f ∧
      ∃ e : pullbackModule f (StandardTautological.line R 2).sheaf ≅
          (QuadraticVeronese.squareLine R).sheaf,
        ∀ j, pullSection f (StandardTautological.coordinate R 2 j) ≫ e.hom =
          QuadraticVeronese.monomials R j := by
  sorry

end LeBrunSalamon.PublishedInputs.ProjectiveSpace

end

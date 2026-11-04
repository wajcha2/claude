import LSPlaneQuadratic
import LSQuadraticVeronese

/-! The exact standard quadratic Veronese image, with its scheme structure
and prescribed coordinate sections. The sole input is the generic explicit
Veronese construction over an arbitrary coefficient ring. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight

namespace LeBrunSalamon.QuadraticVeronese

def equation (R : Type) [CommRing R] : PlaneQuadratic.Coefficients R :=
  ![0, -1, 0, 0, 1, 0]

theorem equation_ne_zero (R : Type) [CommRing R] [Nontrivial R] :
    equation R ≠ 0 := by
  intro h
  have hh := congrFun h (4 : Fin 6)
  exact (one_ne_zero : (1 : R) ≠ 0) (by simpa [equation] using hh)

end LeBrunSalamon.QuadraticVeronese

namespace LeBrunSalamon.PublishedInputs.ProjectiveSpace

/-- Vakil, Foundations of Algebraic Geometry, June27,2011 draft,
Section9.2.6 and Exercise9.2.I (printed p198): the second Veronese
subring is R[u,v,w]/(u*w-v^2). Exercise7.4.D identifies its Proj with
the original P1, and the three generators are X0^2,X0*X1,X1^2.
Remark9.2.8 and Exercise21.1.D explicitly include arbitrary base rings.
Sections16.2.D and17.4.5--6 identify the actual pulled-back O(1) with
O(1) tensor O(1), using those monomials. The displayed six coefficients
are exactly u*w-v^2 in the fixed a,b,c,alpha,beta,gamma ordering.
The section-zero scheme agrees with that homogeneous quotient by its
already proved all-test-scheme universal property.

No chosen family, special fibre, degree classifier or trait appears here.
Primary source:
https://math.stanford.edu/~vakil/216blog/FOAGjun2711publicimperfect.pdf -/
theorem quadraticVeronese_zeroModel (R : Type) [CommRing R] :
    ∃ e : StandardTautological.space R 1 ≅
        PlaneQuadratic.ZeroScheme R (QuadraticVeronese.equation R),
      e.hom ≫ PlaneQuadratic.projection R (QuadraticVeronese.equation R) =
        StandardTautological.toSpec R 1 ∧
      ∃ d : pullbackModule
          (e.hom ≫ PlaneQuadratic.inclusion R (QuadraticVeronese.equation R))
          (StandardTautological.line R 2).sheaf ≅ (QuadraticVeronese.squareLine R).sheaf,
        ∀ j, pullSection
          (e.hom ≫ PlaneQuadratic.inclusion R (QuadraticVeronese.equation R))
          (StandardTautological.coordinate R 2 j) ≫ d.hom =
            QuadraticVeronese.monomials R j := by
  sorry

end LeBrunSalamon.PublishedInputs.ProjectiveSpace
end

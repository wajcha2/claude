import RecompileExtensionsPart04Geometry
import LSAffineCotangentHom
import LSConicLogAlgebra
import LSConicCotangentTools

/-!
# Relative cotangent maps on the prescribed standard-conic charts

This draft builds actual morphisms from the chosen cotangent presentation.
Their normalization uses the original affine-plane coordinates and the
original source parameter. Gluing through the homogeneous line frames is
a separate remaining step. There is no new admission in this file.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.Construction.Smoothing
open LeBrunSalamon.Construction.Smoothing.SourceAffineCharts

namespace LeBrunSalamon.Construction.StandardConicLocal

def derivative (k : Fin 3) (a : RingSections Plane ⊤) : RingSections Plane ⊤ :=
  planeFunction (ConicLogAlgebra.derivation ℂ k
    ((Scheme.ΓSpecIso (CommRingCat.of PlaneRing)).hom a))

theorem derivative_function (k : Fin 3) (p : PlaneRing) :
    derivative k (planeFunction p) = planeFunction (ConicLogAlgebra.derivation ℂ k p) := by
  simp only [derivative, planeFunction, Iso.inv_hom_id_apply]

theorem derivative_zero (k : Fin 3) : derivative k 0 = 0 := by
  simp only [derivative, planeFunction, map_zero]

theorem derivative_add (k : Fin 3) (a b : RingSections Plane ⊤) :
    derivative k (a + b) = derivative k a + derivative k b := by
  simp only [derivative, planeFunction, map_add]

theorem derivative_mul (k : Fin 3) (a b : RingSections Plane ⊤) :
    derivative k (a * b) = a * derivative k b + b * derivative k a := by
  simp only [derivative, planeFunction, map_mul, Derivation.leibniz, smul_eq_mul,
    map_add, Iso.hom_inv_id_apply]

theorem polynomialLine_function (q : PlaneRing) (p : Polynomial ℂ) :
    (polynomialLine q).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℂ))).inv p) =
        planeFunction (Polynomial.eval₂ MvPolynomial.C q p) := by
  exact (congrArg (fun f : CommRingCat.of (Polynomial ℂ) ⟶ Plane.presheaf.obj (op ⊤) => f p)
    (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (Polynomial.eval₂RingHom MvPolynomial.C q)))).symm

theorem derivative_kills_base (k : Fin 3) (a : RingSections AffineLine ⊤) :
    derivative k ((polynomialLine (parameterPolynomial k)).appTop a) = 0 := by
  obtain ⟨p, rfl⟩ :=
    (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℂ))).inv).surjective a
  rw [polynomialLine_function, derivative_function]
  have hp : ConicLogAlgebra.derivation ℂ k
      (Polynomial.eval₂ MvPolynomial.C (parameterPolynomial k) p) = 0 := by
    exact ConicLogAlgebra.derivation_base_polynomial ℂ k p
  rw [hp]
  exact map_zero (Scheme.ΓSpecIso (CommRingCat.of PlaneRing)).inv.hom

theorem chartMap_exists (F : StandardSource) (k : Fin 3) :
    ∃ φ : cotangentSheaf (modelMap F k ≫ F.parameter) ⟶ structureModule Plane,
      ∀ a : RingSections Plane ⊤,
        φ.app ⊤ ((cotangentPresentation (modelMap F k ≫ F.parameter)).differential.apply ⊤ a) =
          derivative k a := by
  apply AffineCotangentHom.exists_normalized (modelMap F k ≫ F.parameter)
    (isAffineOpen_top Plane) (structureModule Plane) (derivative k)
  · exact derivative_zero k
  · exact derivative_add k
  · exact derivative_mul k
  · intro a
    rw [(modelMap_spec F k).1]
    exact derivative_kills_base k a

def chartMap (F : StandardSource) (k : Fin 3) :
    cotangentSheaf (modelMap F k ≫ F.parameter) ⟶ structureModule Plane :=
  Classical.choose (chartMap_exists F k)

theorem chartMap_differential (F : StandardSource) (k : Fin 3)
    (a : RingSections Plane ⊤) :
    (chartMap F k).app ⊤
      ((cotangentPresentation (modelMap F k ≫ F.parameter)).differential.apply ⊤ a) =
        derivative k a :=
  Classical.choose_spec (chartMap_exists F k) a

/-- Both coordinates are normalized on every actual chart. -/
theorem chartMap_coordinate (F : StandardSource) (k : Fin 3) (i : Fin 2) :
    (chartMap F k).app ⊤
      ((cotangentPresentation (modelMap F k ≫ F.parameter)).differential.apply ⊤
        (planeFunction (MvPolynomial.X i))) =
          planeFunction (ConicLogAlgebra.coefficient ℂ k i) := by
  rw [chartMap_differential, derivative_function, ConicLogAlgebra.derivation_variable]

end LeBrunSalamon.Construction.StandardConicLocal
end

import LSOpenCotangentScalar
import LSConicOverlapAlgebra

/-! Scalar algebra for actual cotangent morphisms. Keeping the morphism
abstract avoids expanding a selected chart, its open immersion, and its
pullback comparisons during elementary ring calculations. No admission. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.Skeleton
open LeBrunSalamon.Construction.Smoothing.CoordinateCharts

namespace LeBrunSalamon.CotangentScalarAlgebra

variable {T S : Scheme} {t : T ⟶ S}

/-- The literal scalar obtained by applying a cotangent functional to a
universal differential of a global regular function. -/
def derivative (q : cotangentSheaf t ⟶ structureModule T)
    (a : RingSections T ⊤) : RingSections T ⊤ :=
  q.app ⊤ ((cotangentPresentation t).differential.apply ⊤ a)

theorem derivative_leibniz (q : cotangentSheaf t ⟶ structureModule T)
    (a b : RingSections T ⊤) :
    derivative q (a * b) = a * derivative q b + b * derivative q a := by
  exact ((cotangentPresentation t).differential.postcompose q).leibniz ⊤ a b

theorem derivative_one (q : cotangentSheaf t ⟶ structureModule T) :
    derivative q 1 = 0 :=
  OpenCotangentScalar.derivation_one t
    ((cotangentPresentation t).differential.postcompose q)

theorem scalarSection_apply (r a : RingSections T ⊤) :
    Scheme.Modules.Hom.app (scalarSection r) ⊤ a = r * a := by
  have h := Scheme.Modules.Hom.app_smul
    (sectionFromValue (E := structureModule T) r) a (1 : RingSections T ⊤)
  change Scheme.Modules.Hom.app (sectionFromValue (E := structureModule T) r) ⊤
      (a * (1 : RingSections T ⊤) : RingSections T ⊤) =
    a • sectionValue (sectionFromValue (E := structureModule T) r) at h
  have ha := congrArg (fun z : RingSections T ⊤ =>
    Scheme.Modules.Hom.app (sectionFromValue (E := structureModule T) r) ⊤ z) (mul_one a)
  exact (ha.symm.trans (h.trans
    (congrArg (fun z : GlobalSections (structureModule T) => a • z)
      (sectionFromValue_spec (E := structureModule T) r)))).trans (mul_comm a r)

theorem derivative_scalar (q : cotangentSheaf t ⟶ structureModule T)
    (r a : RingSections T ⊤) :
    derivative (q ≫ scalarSection r) a = r * derivative q a := by
  exact scalarSection_apply r (derivative q a)

/-- Left reciprocal coordinates recover the node vector (u,-v). -/
theorem left_coefficients (q : cotangentSheaf t ⟶ structureModule T)
    (u v w z : RingSections T ⊤) (huw : u * w = 1) (huv : u * v = z)
    (hz : derivative q z = 0) (hw : derivative q w = -1) :
    w * derivative q u = u ∧ w * derivative q v = -v :=
  ConicOverlapAlgebra.node_coefficients_from_left (derivative q)
    (derivative_leibniz q) (derivative_one q) u v w z huw huv hz hw

/-- Right reciprocal coordinates recover the same node vector. -/
theorem right_coefficients (q : cotangentSheaf t ⟶ structureModule T)
    (u v w z : RingSections T ⊤) (hvw : v * w = 1) (huv : u * v = z)
    (hz : derivative q z = 0) (hw : derivative q w = 1) :
    w * derivative q u = u ∧ w * derivative q v = -v :=
  ConicOverlapAlgebra.node_coefficients_from_right (derivative q)
    (derivative_leibniz q) (derivative_one q) u v w z hvw huv hz hw

end LeBrunSalamon.CotangentScalarAlgebra
end

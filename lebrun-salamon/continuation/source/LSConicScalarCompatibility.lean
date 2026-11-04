import LSConicChartDerivations
import LSConicOverlapCoordinates
import LSOpenCotangentScalar
import LSConicCotangentExt
import LSCotangentScalarAlgebra
import LSConicScalarTransport

/-! The normalized relative differentials on actual chart intersections.
The node/outer relations below are equalities of genuine cotangent morphisms,
proved from the original coordinate maps and their universal differentials.
The homogeneous line-frame comparison is kept as a separate final transport. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.PhaseThirty
open LeBrunSalamon.Skeleton
open LeBrunSalamon.Construction.Smoothing
open LeBrunSalamon.Construction.Smoothing.CoordinateCharts
open LeBrunSalamon.Construction.Smoothing.SourceAffineCharts
open LeBrunSalamon.Construction.StandardConicLocal
open LeBrunSalamon.ConicOverlapCoordinates

namespace LeBrunSalamon.ConicScalarCompatibility

def scalarOn {T : Scheme} (F : StandardSource) (k : Fin 3)
    (f : T ⟶ Plane) [IsOpenImmersion f] (t : T ⟶ AffineLine)
    (h : f ≫ (modelMap F k ≫ F.parameter) = t) :
    cotangentSheaf t ⟶ structureModule T :=
  OpenCotangentScalar.pullAlong f (modelMap F k ≫ F.parameter) t h (chartMap F k)

theorem scalarOn_coordinate {T : Scheme} (F : StandardSource) (k : Fin 3)
    (f : T ⟶ Plane) [IsOpenImmersion f] (t : T ⟶ AffineLine)
    (h : f ≫ (modelMap F k ≫ F.parameter) = t) (i : Fin 2) :
    (scalarOn F k f t h).app ⊤
      ((cotangentPresentation t).differential.apply ⊤ (value f i)) =
        f.appTop (planeFunction (ConicLogAlgebra.coefficient ℂ k i)) := by
  have hw := OpenCotangentScalar.pullAlong_differential f
    (modelMap F k ≫ F.parameter) t h (chartMap F k) ⊤
      (planeFunction (MvPolynomial.X i))
  rw [chartMap_coordinate] at hw
  exact hw

theorem scalarSection_apply_top {T : Scheme} (r a : RingSections T ⊤) :
    Scheme.Modules.Hom.app (scalarSection r) ⊤ a = r * a :=
  CotangentScalarAlgebra.scalarSection_apply r a

theorem derivative_coordinate {T : Scheme} (F : StandardSource) (k : Fin 3)
    (f : T ⟶ Plane) [IsOpenImmersion f] (t : T ⟶ AffineLine)
    (h : f ≫ (modelMap F k ≫ F.parameter) = t) (i : Fin 2) :
    CotangentScalarAlgebra.derivative (scalarOn F k f t h) (value f i) =
      f.appTop (planeFunction (ConicLogAlgebra.coefficient ℂ k i)) :=
  scalarOn_coordinate F k f t h i

theorem node_coordinates {T : Scheme} (F : StandardSource)
    (f : T ⟶ Plane) [IsOpenImmersion f] (t : T ⟶ AffineLine)
    (h : f ≫ (modelMap F 0 ≫ F.parameter) = t) :
    CotangentScalarAlgebra.derivative (scalarOn F 0 f t h) (value f 0) = value f 0 ∧
    CotangentScalarAlgebra.derivative (scalarOn F 0 f t h) (value f 1) = -value f 1 := by
  constructor
  · exact derivative_coordinate F 0 f t h 0
  · have hw := derivative_coordinate F 0 f t h 1
    change CotangentScalarAlgebra.derivative (scalarOn F 0 f t h) (value f 1) =
      f.appTop (planeFunction (-MvPolynomial.X (1 : Fin 2))) at hw
    simpa only [planeFunction, map_neg, value] using hw

theorem left_coordinates {T : Scheme} (F : StandardSource)
    (f : T ⟶ Plane) [IsOpenImmersion f] (t : T ⟶ AffineLine)
    (h : f ≫ (modelMap F 1 ≫ F.parameter) = t) :
    CotangentScalarAlgebra.derivative (scalarOn F 1 f t h) (value f 0) = 0 ∧
    CotangentScalarAlgebra.derivative (scalarOn F 1 f t h) (value f 1) = -1 := by
  constructor
  · have hw := derivative_coordinate F 1 f t h 0
    change CotangentScalarAlgebra.derivative (scalarOn F 1 f t h) (value f 0) =
      f.appTop (planeFunction (0 : PlaneRing)) at hw
    simpa only [planeFunction, map_zero] using hw
  · have hw := derivative_coordinate F 1 f t h 1
    change CotangentScalarAlgebra.derivative (scalarOn F 1 f t h) (value f 1) =
      f.appTop (planeFunction (-1 : PlaneRing)) at hw
    simpa only [planeFunction, map_neg, map_one] using hw

theorem right_coordinates {T : Scheme} (F : StandardSource)
    (f : T ⟶ Plane) [IsOpenImmersion f] (t : T ⟶ AffineLine)
    (h : f ≫ (modelMap F 2 ≫ F.parameter) = t) :
    CotangentScalarAlgebra.derivative (scalarOn F 2 f t h) (value f 0) = 0 ∧
    CotangentScalarAlgebra.derivative (scalarOn F 2 f t h) (value f 1) = 1 := by
  constructor
  · have hw := derivative_coordinate F 2 f t h 0
    change CotangentScalarAlgebra.derivative (scalarOn F 2 f t h) (value f 0) =
      f.appTop (planeFunction (0 : PlaneRing)) at hw
    simpa only [planeFunction, map_zero] using hw
  · have hw := derivative_coordinate F 2 f t h 1
    change CotangentScalarAlgebra.derivative (scalarOn F 2 f t h) (value f 1) =
      f.appTop (planeFunction (1 : PlaneRing)) at hw
    simpa only [planeFunction, map_one] using hw

theorem node_left {T : Scheme} (F : StandardSource) (a b : T ⟶ Plane)
    [IsOpenImmersion a] [IsOpenImmersion b]
    (h : a ≫ modelMap F 0 = b ≫ modelMap F 1)
    (hb : b ≫ (modelMap F 1 ≫ F.parameter) = a ≫ (modelMap F 0 ≫ F.parameter)) :
    scalarOn F 0 a (a ≫ (modelMap F 0 ≫ F.parameter)) rfl =
      scalarOn F 1 b (a ≫ (modelMap F 0 ≫ F.parameter)) hb ≫
        scalarSection (value b 1) := by
  have hn := node_coordinates F a (a ≫ (modelMap F 0 ≫ F.parameter)) rfl
  have hb' := left_coordinates F b (a ≫ (modelMap F 0 ≫ F.parameter)) hb
  have hc := ConicOverlapCoordinates.node_left F a b h
  exact ConicScalarTransport.left_form a (modelMap F 0 ≫ F.parameter) affineLineToC
    (by rw [(modelMap_spec F 0).1, polynomialLine_over])
    (a ≫ (modelMap F 0 ≫ F.parameter)) rfl
    (scalarOn F 0 a (a ≫ (modelMap F 0 ≫ F.parameter)) rfl)
    (scalarOn F 1 b (a ≫ (modelMap F 0 ≫ F.parameter)) hb)
    (value b 1) (value b 0) hn.1 hn.2 hc.1 hc.2 hb'.1 hb'.2

theorem node_right {T : Scheme} (F : StandardSource) (a b : T ⟶ Plane)
    [IsOpenImmersion a] [IsOpenImmersion b]
    (h : a ≫ modelMap F 0 = b ≫ modelMap F 2)
    (hb : b ≫ (modelMap F 2 ≫ F.parameter) = a ≫ (modelMap F 0 ≫ F.parameter)) :
    scalarOn F 0 a (a ≫ (modelMap F 0 ≫ F.parameter)) rfl =
      scalarOn F 2 b (a ≫ (modelMap F 0 ≫ F.parameter)) hb ≫
        scalarSection (value b 1) := by
  have hn := node_coordinates F a (a ≫ (modelMap F 0 ≫ F.parameter)) rfl
  have hb' := right_coordinates F b (a ≫ (modelMap F 0 ≫ F.parameter)) hb
  have hc := ConicOverlapCoordinates.node_right F a b h
  exact ConicScalarTransport.right_form a (modelMap F 0 ≫ F.parameter) affineLineToC
    (by rw [(modelMap_spec F 0).1, polynomialLine_over])
    (a ≫ (modelMap F 0 ≫ F.parameter)) rfl
    (scalarOn F 0 a (a ≫ (modelMap F 0 ≫ F.parameter)) rfl)
    (scalarOn F 2 b (a ≫ (modelMap F 0 ≫ F.parameter)) hb)
    (value b 1) (value b 0) hn.1 hn.2 hc.1 hc.2 hb'.1 hb'.2

theorem node_left_common {T : Scheme} (F : StandardSource) (a b : T ⟶ Plane)
    [IsOpenImmersion a] [IsOpenImmersion b]
    (h : a ≫ modelMap F 0 = b ≫ modelMap F 1) (t : T ⟶ AffineLine)
    (ha : a ≫ (modelMap F 0 ≫ F.parameter) = t)
    (hb : b ≫ (modelMap F 1 ≫ F.parameter) = t) :
    scalarOn F 0 a t ha = scalarOn F 1 b t hb ≫ scalarSection (value b 1) := by
  subst t
  exact node_left F a b h hb

theorem node_right_common {T : Scheme} (F : StandardSource) (a b : T ⟶ Plane)
    [IsOpenImmersion a] [IsOpenImmersion b]
    (h : a ≫ modelMap F 0 = b ≫ modelMap F 2) (t : T ⟶ AffineLine)
    (ha : a ≫ (modelMap F 0 ≫ F.parameter) = t)
    (hb : b ≫ (modelMap F 2 ≫ F.parameter) = t) :
    scalarOn F 0 a t ha = scalarOn F 2 b t hb ≫ scalarSection (value b 1) := by
  subst t
  exact node_right F a b h hb

theorem scalar_map_unit {T Y : Scheme} (f : T ⟶ Y) (r : RingSections Y ⊤) :
    (Scheme.Modules.pullback f).map (scalarSection r) ≫ unitPullbackMap f =
      unitPullbackMap f ≫ scalarSection (f.appTop r) := by
  rw [← unitPullbackMap_pullSection, Category.assoc]
  exact congrArg (fun q => unitPullbackMap f ≫ q) (scalarSection_pullback f r)

theorem composition_functional_scalar {X Y Z S : Scheme}
    (f : X ⟶ Y) [IsOpenImmersion f] (g : Y ⟶ Z) (s : Z ⟶ S)
    (q : cotangentSheaf (g ≫ s) ⟶ structureModule Y) (r : RingSections Y ⊤) :
    (Scheme.Modules.pullbackComp f g).inv.app (cotangentSheaf s) ≫
        (Scheme.Modules.pullback f).map (cotangentMap g s ≫ q ≫ scalarSection r) ≫
        unitPullbackMap f =
      cotangentMap (f ≫ g) s ≫
        OpenCotangentScalar.pullAlong f (g ≫ s) ((f ≫ g) ≫ s)
          (Category.assoc f g s).symm q ≫ scalarSection (f.appTop r) := by
  calc
    _ = ((Scheme.Modules.pullbackComp f g).inv.app (cotangentSheaf s) ≫
        (Scheme.Modules.pullback f).map (cotangentMap g s ≫ q) ≫
        unitPullbackMap f) ≫ scalarSection (f.appTop r) := by
      simp only [Functor.map_comp, Category.assoc, scalar_map_unit]
    _ = _ := by rw [OpenCotangentScalar.composition_functional]; simp only [Category.assoc]

end LeBrunSalamon.ConicScalarCompatibility
end

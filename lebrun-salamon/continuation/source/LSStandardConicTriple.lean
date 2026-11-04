import LSNormalizedSegrePairs
import LSConicGeneratingTuples
import LSStandardSourceBaseChange
import LSPlaneConicPresentation
import LSTensorLineTransport

/-! The three actual plane coordinates of the base-changed standard
(1,1) conic.  They are (U1*V0,U0*V1,U0*V0), in the same selected line.
Generation and their equation follow from the normalized Segre scheme
image, not from a pointwise parametrization. No new admission. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.Skeleton LeBrunSalamon.Refinement
open LeBrunSalamon.Construction LeBrunSalamon.Construction.Smoothing

namespace LeBrunSalamon.StandardConicTriple

variable (F : StandardSource) {S : Scheme} (t : S ⟶ AffineLine)

abbrev source := SourceOver F t
abbrev projection : source F t ⟶ S := pullback.snd F.parameter t
abbrev left : source F t ⟶ ProjectiveLine := pullback.fst F.parameter t ≫ F.left
abbrev right : source F t ⟶ ProjectiveLine := pullback.fst F.parameter t ≫ F.right

def line : LineBundle (source F t) := StandardSourceBaseChange.line (left F t) (right F t)

def pairCoordinate (i j : Fin 2) : AlgebraicSection (line F t).sheaf :=
  StandardSourceBaseChange.coordinate (left F t) (right F t) i j

def coordinate : Fin 3 → AlgebraicSection (line F t).sheaf :=
  ![pairCoordinate F t 1 0, pairCoordinate F t 0 1, pairCoordinate F t 0 0]

def parameter : RingSections S ⊤ := t.appTop parameterFunction

theorem left_over : left F t ≫ Lines.P.structureMap =
    projection F t ≫ t ≫ affineLineToC := by
  rw [left, Category.assoc, F.left_over, ← Category.assoc, pullback.condition,
    Category.assoc]

theorem right_over : right F t ≫ Lines.P.structureMap =
    projection F t ≫ t ≫ affineLineToC := by
  rw [right, Category.assoc, F.right_over, ← Category.assoc, pullback.condition,
    Category.assoc]

theorem pair_over : left F t ≫ StandardTautological.toSpec ℂ 1 =
    right F t ≫ StandardTautological.toSpec ℂ 1 :=
  (left_over F t).trans (right_over F t).symm

theorem pair_over_comp {T : Scheme} (h : T ⟶ source F t) :
    (h ≫ left F t) ≫ StandardTautological.toSpec ℂ 1 =
      (h ≫ right F t) ≫ StandardTautological.toSpec ℂ 1 :=
  (Category.assoc h (left F t) (StandardTautological.toSpec ℂ 1)).trans
    ((congrArg (fun f => h ≫ f) (pair_over F t)).trans
      (Category.assoc h (right F t) (StandardTautological.toSpec ℂ 1)).symm)

theorem last_coordinate : pairCoordinate F t 1 1 =
    ConicGeneratingTuples.scale ((projection F t).appTop (parameter t))
      (pairCoordinate F t 0 0) := by
  have h := StandardSourceBaseChange.equation_pullback
    (pullback.fst F.parameter t) F.parameter F.left F.right F.equation
  change pairCoordinate F t 1 1 = sectionFromValue
    ((pullback.fst F.parameter t ≫ F.parameter).appTop parameterFunction •
      sectionValue (pairCoordinate F t 0 0)) at h
  rw [pullback.condition, Scheme.Hom.comp_appTop] at h
  exact h

theorem quadruple_eq :
    ConicGeneratingTuples.quadruple (coordinate F t)
      ((projection F t).appTop (parameter t)) =
        NormalizedSegrePairs.tuple ℂ (left F t) (right F t) := by
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact (last_coordinate F t).symm

theorem generates : TupleGenerates (line F t) (coordinate F t) := by
  apply ConicGeneratingTuples.generates_of_quadruple (line F t) (coordinate F t)
    ((projection F t).appTop (parameter t))
  rw [quadruple_eq]
  exact NormalizedSegrePairs.tuple_generates ℂ (left F t) (right F t) (pair_over F t)

theorem equation : PlaneConicPresentation.Equation (parameter t)
    (projection F t) (line F t) (coordinate F t) := by
  have h := NormalizedSegrePairs.determinant ℂ (left F t) (right F t) (pair_over F t)
  change tensorSection (pairCoordinate F t 0 0) (pairCoordinate F t 1 1) =
    tensorSection (pairCoordinate F t 1 0) (pairCoordinate F t 0 1) at h
  rw [last_coordinate, ConicGeneratingTuples.tensor_scale_right] at h
  exact h.symm

/-- Any generating triple satisfying the actual plane equation comes
from an actual point of the base-changed standard source, with the
specified line comparison and all three coordinates. -/
theorem lift_tuple (T : Scheme) (s : T ⟶ S) (L : LineBundle T)
    (a : Fin 3 → AlgebraicSection L.sheaf) (ha : TupleGenerates L a)
    (heq : PlaneConicPresentation.Equation (parameter t) s L a) :
    ∃ h : T ⟶ source F t, h ≫ projection F t = s ∧
      ∃ e : pullbackModule h (line F t).sheaf ≅ L.sheaf,
        ∀ i, pullSection h (coordinate F t i) ≫ e.hom = a i := by
  let r := s.appTop (parameter t)
  let b := ConicGeneratingTuples.quadruple a r
  obtain ⟨g, ⟨e, he⟩, _⟩ := NormalizedSegreQuotients.quotient_universal ℂ
    ((s ≫ t) ≫ affineLineToC) L b
    (ConicGeneratingTuples.quadruple_generates L a r ha)
    (ConicGeneratingTuples.quadruple_equation a r heq)
  let u : T ⟶ ProjectiveLine := g.val ≫ NormalizedSegre.left ℂ
  let v : T ⟶ ProjectiveLine := g.val ≫ NormalizedSegre.right ℂ
  let c := TensorLineTransport.comparison g.val
    (NormalizedSegre.left ℂ) (NormalizedSegre.right ℂ) u v rfl rfl
    (StandardTautological.line ℂ 1).sheaf (StandardTautological.line ℂ 1).sheaf
  let e' : (StandardSourceBaseChange.line u v).sheaf ≅ L.sheaf := c.symm ≪≫ e
  have hc (i : Fin 4) :
      StandardSourceBaseChange.coordinate u v (NormalizedSegre.firstIndex i)
        (NormalizedSegre.secondIndex i) ≫ e'.hom = b i := by
    have hcoord := TensorLineTransport.sections g.val
      (NormalizedSegre.left ℂ) (NormalizedSegre.right ℂ) u v rfl rfl
      (StandardTautological.coordinate ℂ 1 (NormalizedSegre.firstIndex i))
      (StandardTautological.coordinate ℂ 1 (NormalizedSegre.secondIndex i))
    change pullSection g.val (NormalizedSegre.productCoordinate ℂ i) ≫ c.hom =
      StandardSourceBaseChange.coordinate u v (NormalizedSegre.firstIndex i)
        (NormalizedSegre.secondIndex i) at hcoord
    rw [← hcoord]
    change (pullSection g.val (NormalizedSegre.productCoordinate ℂ i) ≫ c.hom) ≫
      (c.inv ≫ e.hom) = b i
    rw [Category.assoc, Iso.hom_inv_id_assoc]
    exact he i
  have hu : u ≫ Lines.P.structureMap = (s ≫ t) ≫ affineLineToC := by
    change (g.val ≫ NormalizedSegre.left ℂ) ≫ StandardTautological.toSpec ℂ 1 = _
    exact (Category.assoc _ _ _).trans g.property
  have hv : v ≫ Lines.P.structureMap = (s ≫ t) ≫ affineLineToC := by
    calc
      _ = g.val ≫ NormalizedSegre.base ℂ := by
        change (g.val ≫ pullback.snd (StandardTautological.toSpec ℂ 1)
          (StandardTautological.toSpec ℂ 1)) ≫ StandardTautological.toSpec ℂ 1 =
          g.val ≫ (pullback.fst _ _ ≫ StandardTautological.toSpec ℂ 1)
        rw [Category.assoc, ← pullback.condition]
      _ = _ := g.property
  have hconic : ConicEquation (s ≫ t) u v := by
    apply (cancel_mono e'.hom).mp
    change StandardSourceBaseChange.coordinate u v 1 1 ≫ e'.hom = _
    rw [StandardSourceProof.scalarSection_comp]
    rw [show StandardSourceBaseChange.coordinate u v 1 1 ≫ e'.hom = b 3 from hc 3]
    change b 3 = sectionFromValue ((s ≫ t).appTop parameterFunction •
      sectionValue (StandardSourceBaseChange.coordinate u v 0 0 ≫ e'.hom))
    rw [show StandardSourceBaseChange.coordinate u v 0 0 ≫ e'.hom = b 0 from hc 0]
    change ConicGeneratingTuples.scale r (a 2) =
      sectionFromValue ((s ≫ t).appTop parameterFunction • sectionValue (a 2))
    rw [Scheme.Hom.comp_appTop]
    rfl
  obtain ⟨h, hh, _⟩ := StandardSourceBaseChange.universal F t T s u v hu hv hconic
  let d := TensorLineTransport.comparison h (left F t) (right F t) u v
    (by simpa only [left, Category.assoc] using hh.2.1)
    (by simpa only [right, Category.assoc] using hh.2.2)
    (projectiveCoordinates 1).hyperplane.sheaf (projectiveCoordinates 1).hyperplane.sheaf
  refine ⟨h, hh.1, d ≪≫ e', ?_⟩
  intro i
  have hd (j k : Fin 2) : pullSection h (pairCoordinate F t j k) ≫ d.hom =
      StandardSourceBaseChange.coordinate u v j k :=
    TensorLineTransport.sections h (left F t) (right F t) u v _ _
      ((projectiveCoordinates 1).coordinate j) ((projectiveCoordinates 1).coordinate k)
  change pullSection h (coordinate F t i) ≫ (d.hom ≫ e'.hom) = a i
  rw [← Category.assoc]
  fin_cases i
  · exact (congrArg (fun z => z ≫ e'.hom) (hd 1 0)).trans (hc 1)
  · exact (congrArg (fun z => z ≫ e'.hom) (hd 0 1)).trans (hc 2)
  · exact (congrArg (fun z => z ≫ e'.hom) (hd 0 0)).trans (hc 0)

/-- The original fourth Segre coordinate is recovered from the three
plane coordinates by the displayed conic equation.  This also keeps
the actual line comparison when a test map is supplied. -/
theorem pull_pair_tuple {T : Scheme} (s : T ⟶ S)
    (L : LineBundle T) (a : Fin 3 → AlgebraicSection L.sheaf)
    (h : T ⟶ source F t) (hs : h ≫ projection F t = s)
    (e : pullbackModule h (line F t).sheaf ≅ L.sheaf)
    (he : ∀ i, pullSection h (coordinate F t i) ≫ e.hom = a i) :
    ∃ e' : pullbackModule
        (NormalizedSegrePairs.pair ℂ (h ≫ left F t) (h ≫ right F t)
          (pair_over_comp F t h))
        (NormalizedSegre.productLine ℂ).sheaf ≅ L.sheaf,
      ∀ i, pullSection
        (NormalizedSegrePairs.pair ℂ (h ≫ left F t) (h ≫ right F t)
          (pair_over_comp F t h))
        (NormalizedSegre.productCoordinate ℂ i) ≫ e'.hom =
          ConicGeneratingTuples.quadruple a (s.appTop (parameter t)) i := by
  let u := h ≫ left F t
  let v := h ≫ right F t
  have huv : u ≫ StandardTautological.toSpec ℂ 1 = v ≫ StandardTautological.toSpec ℂ 1 := by
    exact pair_over_comp F t h
  let d := TensorLineTransport.comparison h (left F t) (right F t) u v rfl rfl
    (StandardTautological.line ℂ 1).sheaf (StandardTautological.line ℂ 1).sheaf
  refine ⟨NormalizedSegrePairs.lineIso ℂ u v huv ≪≫ d.symm ≪≫ e, ?_⟩
  intro i
  change pullSection (NormalizedSegrePairs.pair ℂ u v huv)
    (NormalizedSegre.productCoordinate ℂ i) ≫
      ((NormalizedSegrePairs.lineIso ℂ u v huv).hom ≫ d.inv ≫ e.hom) = _
  rw [← Category.assoc, NormalizedSegrePairs.lineIso_coordinate]
  have hd : pullSection h
      (pairCoordinate F t (NormalizedSegre.firstIndex i) (NormalizedSegre.secondIndex i)) ≫
      d.hom = NormalizedSegrePairs.tuple ℂ u v i :=
    TensorLineTransport.sections h (left F t) (right F t) u v rfl rfl
      (StandardTautological.coordinate ℂ 1 (NormalizedSegre.firstIndex i))
      (StandardTautological.coordinate ℂ 1 (NormalizedSegre.secondIndex i))
  rw [← hd, Category.assoc, Iso.hom_inv_id_assoc]
  fin_cases i
  · exact he 2
  · exact he 0
  · exact he 1
  · change pullSection h (pairCoordinate F t 1 1) ≫ e.hom = _
    rw [last_coordinate]
    change pullSection h (sectionFromValue
      ((projection F t).appTop (parameter t) • sectionValue (pairCoordinate F t 0 0))) ≫
      e.hom = _
    rw [StandardSourceProof.pullSection_scalar, StandardSourceProof.scalarSection_comp]
    rw [show pullSection h (pairCoordinate F t 0 0) ≫ e.hom = a 2 from he 2]
    change sectionFromValue (((projection F t).appTop ≫ h.appTop) (parameter t) •
      sectionValue (a 2)) = _
    rw [← Scheme.Hom.comp_appTop, hs]
    rfl

theorem lift_tuple_unique {T : Scheme} (s : T ⟶ S) (L : LineBundle T)
    (a : Fin 3 → AlgebraicSection L.sheaf) (ha : TupleGenerates L a)
    (heq : PlaneConicPresentation.Equation (parameter t) s L a)
    (h k : T ⟶ source F t) (hs : h ≫ projection F t = s) (ks : k ≫ projection F t = s)
    (e : pullbackModule h (line F t).sheaf ≅ L.sheaf)
    (e' : pullbackModule k (line F t).sheaf ≅ L.sheaf)
    (he : ∀ i, pullSection h (coordinate F t i) ≫ e.hom = a i)
    (he' : ∀ i, pullSection k (coordinate F t i) ≫ e'.hom = a i) : h = k := by
  let r := s.appTop (parameter t)
  let b := ConicGeneratingTuples.quadruple a r
  obtain ⟨g, hg, unique⟩ := NormalizedSegreQuotients.quotient_universal ℂ
    ((s ≫ t) ≫ affineLineToC) L b
    (ConicGeneratingTuples.quadruple_generates L a r ha)
    (ConicGeneratingTuples.quadruple_equation a r heq)
  let gh := NormalizedSegrePairs.pair ℂ (h ≫ left F t) (h ≫ right F t)
    (pair_over_comp F t h)
  let gk := NormalizedSegrePairs.pair ℂ (k ≫ left F t) (k ≫ right F t)
    (pair_over_comp F t k)
  have hbase : gh ≫ NormalizedSegre.base ℂ = (s ≫ t) ≫ affineLineToC := by
    change gh ≫ (NormalizedSegre.left ℂ ≫ StandardTautological.toSpec ℂ 1) = _
    rw [← Category.assoc, NormalizedSegrePairs.pair_left]
    change (h ≫ left F t) ≫ Lines.P.structureMap = _
    rw [Category.assoc, left_over, ← Category.assoc, hs, Category.assoc]
  have kbase : gk ≫ NormalizedSegre.base ℂ = (s ≫ t) ≫ affineLineToC := by
    change gk ≫ (NormalizedSegre.left ℂ ≫ StandardTautological.toSpec ℂ 1) = _
    rw [← Category.assoc, NormalizedSegrePairs.pair_left]
    change (k ≫ left F t) ≫ Lines.P.structureMap = _
    rw [Category.assoc, left_over, ← Category.assoc, ks, Category.assoc]
  have hgh : (⟨gh, hbase⟩ : {g : T ⟶ NormalizedSegre.Product ℂ //
      g ≫ NormalizedSegre.base ℂ = (s ≫ t) ≫ affineLineToC}) = g :=
    unique ⟨gh, hbase⟩ (pull_pair_tuple F t s L a h hs e he)
  have hgk : (⟨gk, kbase⟩ : {g : T ⟶ NormalizedSegre.Product ℂ //
      g ≫ NormalizedSegre.base ℂ = (s ≫ t) ≫ affineLineToC}) = g :=
    unique ⟨gk, kbase⟩ (pull_pair_tuple F t s L a k ks e' he')
  have hp : gh = gk := congrArg Subtype.val (hgh.trans hgk.symm)
  apply StandardSourceBaseChange.hom_ext F t (hs.trans ks.symm)
  · have hp' := congrArg (fun z => z ≫ NormalizedSegre.left ℂ) hp
    simpa only [gh, gk, NormalizedSegrePairs.pair_left, Category.assoc] using hp'
  · have hp' := congrArg (fun z => z ≫ NormalizedSegre.right ℂ) hp
    simpa only [gh, gk, NormalizedSegrePairs.pair_right, Category.assoc] using hp'

/-- The complete quotient-tuple presentation is proved from the actual
Segre image and the original source's all-test universal property. -/
def presentation : PlaneConicPresentation.Presentation S (parameter t) where
  source := source F t
  projection := projection F t
  line := line F t
  coordinate := coordinate F t
  generates := generates F t
  equation := equation F t
  universal := by
    intro T s L a ha heq
    obtain ⟨h, hs, e, he⟩ := lift_tuple F t T s L a ha heq
    refine ⟨⟨h, hs⟩, ⟨e, he⟩, ?_⟩
    intro k hk
    obtain ⟨e', he'⟩ := hk
    apply Subtype.ext
    exact lift_tuple_unique F t s L a ha heq k.val h k.property hs e' e he' he

end LeBrunSalamon.StandardConicTriple
end

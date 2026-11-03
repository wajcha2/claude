import RecompileExtensionsPart04
import LSProperSections

/-!
The two actual moving-pair vector lifts imply section descent on every
proper integral source over either type of test line. The source need not
have a point over C(P1), and need not be an entire irreducible component.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseThree LeBrunSalamon.PhaseTwentyOne
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.PhaseThirtyTwo LeBrunSalamon.PhaseThirtyFive
open LeBrunSalamon.Core LeBrunSalamon.Skeleton LeBrunSalamon.Refinement
open LeBrunSalamon.Construction.Lines

namespace LeBrunSalamon.Construction.Descent.LineValue

theorem composition_naturality {T Y Z : Scheme}
    (f : T ⟶ Y) (g : Y ⟶ Z) (h : T ⟶ Z) (hh : f ≫ g = h)
    {E F : OModule Z} (a : E ⟶ F) :
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback g).map a) ≫
        (compositionPullback f g h hh F).hom =
      (compositionPullback f g h hh E).hom ≫ (Scheme.Modules.pullback h).map a :=
  Normalization.BundleGluing.compositionPullback_naturality f g h hh a

theorem composition_inv_naturality {T Y Z : Scheme}
    (f : T ⟶ Y) (g : Y ⟶ Z) (h : T ⟶ Z) (hh : f ≫ g = h)
    {E F : OModule Z} (a : E ⟶ F) :
    (Scheme.Modules.pullback h).map a ≫ (compositionPullback f g h hh F).inv =
      (compositionPullback f g h hh E).inv ≫
        (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback g).map a) := by
  apply (cancel_epi (compositionPullback f g h hh E).hom).mp
  rw [← Category.assoc, ← composition_naturality, Category.assoc]
  simp only [Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]

/-- Canonical base change of an external product, with both actual
projection equations supplied explicitly. -/
def externalAlongIso {T X : Scheme} (s : X ⟶ ComplexBase)
    (c : T ⟶ SelfProduct s) (f g : T ⟶ X)
    (hf : c ≫ firstProjection s = f) (hg : c ≫ secondProjection s = g)
    (E F : OModule X) :
    tensorSheaf (pullbackModule f E) (pullbackModule g F) ≅
      pullbackModule c (externalTensor s E F) := by
  letI := tensorPullbackComparison_isIso c
    (pullbackModule (firstProjection s) E) (pullbackModule (secondProjection s) F)
  exact tensorIso (compositionPullback c (firstProjection s) f hf E).symm
      (compositionPullback c (secondProjection s) g hg F).symm ≪≫
    asIso (tensorPullbackComparison c
      (pullbackModule (firstProjection s) E) (pullbackModule (secondProjection s) F))

theorem externalAlongIso_naturality {T X : Scheme} (s : X ⟶ ComplexBase)
    (c : T ⟶ SelfProduct s) (f g : T ⟶ X)
    (hf : c ≫ firstProjection s = f) (hg : c ≫ secondProjection s = g)
    {E E' F F' : OModule X} (a : E ⟶ E') (b : F ⟶ F') :
    tensorMap ((Scheme.Modules.pullback f).map a) ((Scheme.Modules.pullback g).map b) ≫
        (externalAlongIso s c f g hf hg E' F').hom =
      (externalAlongIso s c f g hf hg E F).hom ≫
        (Scheme.Modules.pullback c).map (externalTensorMap s a b) := by
  change tensorMap ((Scheme.Modules.pullback f).map a)
      ((Scheme.Modules.pullback g).map b) ≫
      (tensorMap (compositionPullback c (firstProjection s) f hf E').inv
        (compositionPullback c (secondProjection s) g hg F').inv ≫
        tensorPullbackComparison c (pullbackModule (firstProjection s) E')
          (pullbackModule (secondProjection s) F')) =
    (tensorMap (compositionPullback c (firstProjection s) f hf E).inv
        (compositionPullback c (secondProjection s) g hg F).inv ≫
      tensorPullbackComparison c (pullbackModule (firstProjection s) E)
        (pullbackModule (secondProjection s) F)) ≫
      (Scheme.Modules.pullback c).map
        (tensorMap ((Scheme.Modules.pullback (firstProjection s)).map a)
          ((Scheme.Modules.pullback (secondProjection s)).map b))
  rw [← Category.assoc, ← tensorMap_comp,
    composition_inv_naturality, composition_inv_naturality, tensorMap_comp,
    Category.assoc, ExternalExchangeCoherenceProof.comparison_naturality]
  rfl

theorem square_naturality {T Y W Z : Scheme}
    (a : T ⟶ Y) (b : Y ⟶ Z) (c : T ⟶ W) (d : W ⟶ Z)
    (h : a ≫ b = c ≫ d) {E F : OModule Z} (v : E ⟶ F) :
    (Scheme.Modules.pullback a).map ((Scheme.Modules.pullback b).map v) ≫
        (pullbackSquareIso a b c d h F).hom =
      (pullbackSquareIso a b c d h E).hom ≫
        (Scheme.Modules.pullback c).map ((Scheme.Modules.pullback d).map v) := by
  let e : (Scheme.Modules.pullback b ⋙ Scheme.Modules.pullback a) ≅
      (Scheme.Modules.pullback d ⋙ Scheme.Modules.pullback c) :=
    Scheme.Modules.pullbackComp a b ≪≫ Scheme.Modules.pullbackCongr h ≪≫
      (Scheme.Modules.pullbackComp c d).symm
  simpa only [e, pullbackSquareIso, NatTrans.comp_app, Iso.trans_hom,
    Iso.symm_hom, Iso.app_hom, Iso.app_inv, Scheme.Modules.pullbackCongr,
    eqToIso.hom, eqToHom_app, Functor.comp_map] using e.hom.naturality v

theorem pullSection_postcompose {T Y : Scheme} (f : T ⟶ Y)
    {E F : OModule Y} (v : AlgebraicSection E) (a : E ⟶ F) :
    pullSection f (v ≫ a) = pullSection f v ≫ (Scheme.Modules.pullback f).map a := by
  simp only [pullSection, restrictSection, Functor.map_comp, Category.assoc]

/-- Transport a proved section-descent assertion across its actual
bundle comparison and its actual commuting contact-map square. -/
theorem value_descends_via_iso {T Y : Scheme} (f : T ⟶ Y)
    {E E' L L' : OModule Y} (e : E ≅ E') (l : L ≅ L')
    (theta : E ⟶ L) (theta' : E' ⟶ L')
    (htheta : theta ≫ l.hom = e.hom ≫ theta')
    (h : ∀ v : AlgebraicSection (pullbackModule f E),
      ∃ b : AlgebraicSection L,
        pullSection f b = v ≫ (Scheme.Modules.pullback f).map theta)
    (v : AlgebraicSection (pullbackModule f E')) :
    ∃ b : AlgebraicSection L',
      pullSection f b = v ≫ (Scheme.Modules.pullback f).map theta' := by
  obtain ⟨b, hb⟩ := h (v ≫ (Scheme.Modules.pullback f).map e.inv)
  refine ⟨b ≫ l.hom, ?_⟩
  rw [pullSection_postcompose, hb, Category.assoc, Category.assoc,
    ← Functor.map_comp, htheta, Functor.map_comp,
    ← Category.assoc ((Scheme.Modules.pullback f).map e.inv),
    ← Functor.map_comp, e.inv_hom_id, (Scheme.Modules.pullback f).map_id E', Category.id_comp]

/-- The other endpoint contributes an actual constant line on P1. -/
def constantLineIso {n : ℕ} {X : ContactFanoManifold n}
    (y : ComplexPoint X.variety) :
    pullbackModule (P.structureMap ≫ y.map) X.contact.sequence.line.sheaf ≅
      structureModule ProjectiveLine :=
  ((Scheme.Modules.pullbackComp P.structureMap y.map).app
      X.contact.sequence.line.sheaf).symm ≪≫
    (Scheme.Modules.pullback P.structureMap).mapIso
      (Classical.choice (ProjectiveCoordinateProof.line_at_complex_point_trivial
        X.contact.sequence.line y.map)) ≪≫ unitPullbackIso P.structureMap

/-- The first vector lift, with the original p*O source normalized to O. -/
def vectorLeft {n : ℕ} {X : ContactFanoManifold n} (D : ProperPair X) :
    AlgebraicSection (pullbackModule D.pair.data.projection
      (movingPairBundleLeft X.variety X.contact)) :=
  (unitPullbackIso D.pair.data.projection).inv ≫ D.pair.data.vectorLift12

def vectorRight {n : ℕ} {X : ContactFanoManifold n} (D : ProperPair X) :
    AlgebraicSection (pullbackModule D.pair.data.projection
      (movingPairBundleRight X.variety X.contact)) :=
  (unitPullbackIso D.pair.data.projection).inv ≫ D.pair.data.vectorLift21

theorem vectorLeft_value {n : ℕ} {X : ContactFanoManifold n} (D : ProperPair X) :
    vectorLeft D ≫ (Scheme.Modules.pullback D.pair.data.projection).map
      (movingPairContactLeft X.variety X.contact) = D.value := by
  rw [← D.pair.mapLeft]
  rfl

theorem vectorRight_value {n : ℕ} {X : ContactFanoManifold n} (D : ProperPair X) :
    vectorRight D ≫ (Scheme.Modules.pullback D.pair.data.projection).map
      (movingPairContactRight X.variety X.contact) = D.value := by
  rw [← D.pair.mapRight]
  change (unitPullbackIso D.pair.data.projection).inv ≫
      (D.pair.data.vectorLift21 ≫ (Scheme.Modules.pullback D.pair.data.projection).map
        D.pair.data.map21) = _
  rw [← D.pair.data.commonContactValue]
  rfl

/-- Pulling a vector lift through an actual commutative square retains
the same contact value through the corresponding scalar-bundle comparison. -/
theorem transported_vector_value {T Y W Z : Scheme}
    (a : T ⟶ Y) (b : Y ⟶ Z) (c : T ⟶ W) (d : W ⟶ Z)
    (h : a ≫ b = c ≫ d) {E F : OModule Z} (theta : E ⟶ F)
    (v : AlgebraicSection (pullbackModule b E))
    (w : AlgebraicSection (pullbackModule b F))
    (hw : v ≫ (Scheme.Modules.pullback b).map theta = w) :
    (pullSection a v ≫ (pullbackSquareIso a b c d h E).hom) ≫
        (Scheme.Modules.pullback c).map ((Scheme.Modules.pullback d).map theta) =
      pullSection a w ≫ (pullbackSquareIso a b c d h F).hom := by
  rw [Category.assoc, ← square_naturality, ← Category.assoc,
    ← pullSection_postcompose, hw]

theorem testLine_left_value {n : ℕ} {X : ContactFanoManifold n}
    (f : FreeLine X) (y : ComplexPoint X.variety)
    {T : Scheme} [IsIntegral T] (pi : T ⟶ ProjectiveLine)
    [IsProper (pi ≫ P.structureMap)]
    (v : AlgebraicSection (pullbackModule pi (pullbackModule (testLine f y .first)
      (movingPairBundleLeft X.variety X.contact)))) :
    ∃ a : AlgebraicSection (pullbackModule (testLine f y .first) (SquareLine X).sheaf),
      pullSection pi a = v ≫ (Scheme.Modules.pullback pi).map
        ((Scheme.Modules.pullback (testLine f y .first)).map
          (movingPairContactLeft X.variety X.contact)) := by
  let c := testLine f y .first
  have hfirst : c ≫ firstProjection X.variety.structureMap = f.curve.map :=
    pullback.lift_fst _ _ _
  have hsecond : c ≫ secondProjection X.variety.structureMap = P.structureMap ≫ y.map :=
    pullback.lift_snd _ _ _
  let e := externalAlongIso X.variety.structureMap c f.curve.map
    (P.structureMap ≫ y.map) hfirst hsecond
    (tangentSheaf X.variety.structureMap) X.contact.sequence.line.sheaf
  let l := externalAlongIso X.variety.structureMap c f.curve.map
    (P.structureMap ≫ y.map) hfirst hsecond
    X.contact.sequence.line.sheaf X.contact.sequence.line.sheaf
  apply value_descends_via_iso pi e l
    (tensorMap (ContactPositive.contactProjection f) (𝟙 _))
    ((Scheme.Modules.pullback c).map (movingPairContactLeft X.variety X.contact)) ?_ ?_ v
  · have hn :
        tensorMap (ContactPositive.contactProjection f)
            ((Scheme.Modules.pullback (P.structureMap ≫ y.map)).map
              (𝟙 X.contact.sequence.line.sheaf)) ≫ l.hom =
          e.hom ≫ (Scheme.Modules.pullback c).map
            (movingPairContactLeft X.variety X.contact) :=
        externalAlongIso_naturality X.variety.structureMap c f.curve.map
          (P.structureMap ≫ y.map) hfirst hsecond
          X.contact.sequence.form (𝟙 X.contact.sequence.line.sheaf)
    have hid := congrArg
      (fun u : pullbackModule (P.structureMap ≫ y.map) X.contact.sequence.line.sheaf ⟶
          pullbackModule (P.structureMap ≫ y.map) X.contact.sequence.line.sheaf =>
        tensorMap (ContactPositive.contactProjection f) u ≫ l.hom)
      ((Scheme.Modules.pullback (P.structureMap ≫ y.map)).map_id
        X.contact.sequence.line.sheaf)
    exact hid.symm.trans hn
  · exact LineContactQuotient.component_contact_value_right f pi (constantLineIso y)

theorem testLine_right_value {n : ℕ} {X : ContactFanoManifold n}
    (f : FreeLine X) (y : ComplexPoint X.variety)
    {T : Scheme} [IsIntegral T] (pi : T ⟶ ProjectiveLine)
    [IsProper (pi ≫ P.structureMap)]
    (v : AlgebraicSection (pullbackModule pi (pullbackModule (testLine f y .second)
      (movingPairBundleRight X.variety X.contact)))) :
    ∃ a : AlgebraicSection (pullbackModule (testLine f y .second) (SquareLine X).sheaf),
      pullSection pi a = v ≫ (Scheme.Modules.pullback pi).map
        ((Scheme.Modules.pullback (testLine f y .second)).map
          (movingPairContactRight X.variety X.contact)) := by
  let c := testLine f y .second
  have hfirst : c ≫ firstProjection X.variety.structureMap = P.structureMap ≫ y.map :=
    pullback.lift_fst _ _ _
  have hsecond : c ≫ secondProjection X.variety.structureMap = f.curve.map :=
    pullback.lift_snd _ _ _
  let e := externalAlongIso X.variety.structureMap c (P.structureMap ≫ y.map)
    f.curve.map hfirst hsecond X.contact.sequence.line.sheaf
    (tangentSheaf X.variety.structureMap)
  let l := externalAlongIso X.variety.structureMap c (P.structureMap ≫ y.map)
    f.curve.map hfirst hsecond X.contact.sequence.line.sheaf X.contact.sequence.line.sheaf
  apply value_descends_via_iso pi e l
    (tensorMap (𝟙 _) (ContactPositive.contactProjection f))
    ((Scheme.Modules.pullback c).map (movingPairContactRight X.variety X.contact)) ?_ ?_ v
  · have hn :
        tensorMap ((Scheme.Modules.pullback (P.structureMap ≫ y.map)).map
              (𝟙 X.contact.sequence.line.sheaf))
            (ContactPositive.contactProjection f) ≫ l.hom =
          e.hom ≫ (Scheme.Modules.pullback c).map
            (movingPairContactRight X.variety X.contact) :=
        externalAlongIso_naturality X.variety.structureMap c (P.structureMap ≫ y.map)
          f.curve.map hfirst hsecond
          (𝟙 X.contact.sequence.line.sheaf) X.contact.sequence.form
    have hid := congrArg
      (fun u : pullbackModule (P.structureMap ≫ y.map) X.contact.sequence.line.sheaf ⟶
          pullbackModule (P.structureMap ≫ y.map) X.contact.sequence.line.sheaf =>
        tensorMap u (ContactPositive.contactProjection f) ≫ l.hom)
      ((Scheme.Modules.pullback (P.structureMap ≫ y.map)).map_id
        X.contact.sequence.line.sheaf)
    exact hid.symm.trans hn
  · exact LineContactQuotient.component_contact_value_left f pi (constantLineIso y)

/-- Manuscript des:component-section for either axis, on every proper
integral source over the test line. This assertion is independent of the
existence of rational points of that source over the line's function field. -/
theorem component_section {n : ℕ} {X : ContactFanoManifold n}
    (D : ProperPair X) (f : FreeLine X) (y : ComplexPoint X.variety) (axis : Axis)
    {T : Scheme} [IsIntegral T] (pi : T ⟶ ProjectiveLine)
    [IsProper (pi ≫ P.structureMap)] (d : T ⟶ D.pair.data.source)
    (hd : d ≫ D.pair.data.projection = pi ≫ testLine f y axis) :
    ∃ a : AlgebraicSection (pullbackModule (testLine f y axis) (SquareLine X).sheaf),
      pullSection pi a = pullSection d D.value ≫
        (pullbackSquareIso d D.pair.data.projection pi (testLine f y axis)
          hd (SquareLine X).sheaf).hom := by
  cases axis with
  | first =>
      let v := pullSection d (vectorLeft D) ≫
        (pullbackSquareIso d D.pair.data.projection pi (testLine f y .first)
          hd (movingPairBundleLeft X.variety X.contact)).hom
      obtain ⟨a, ha⟩ := testLine_left_value f y pi v
      refine ⟨a, ha.trans ?_⟩
      exact transported_vector_value d D.pair.data.projection pi (testLine f y .first)
        hd (movingPairContactLeft X.variety X.contact) (vectorLeft D) D.value
        (vectorLeft_value D)
  | second =>
      let v := pullSection d (vectorRight D) ≫
        (pullbackSquareIso d D.pair.data.projection pi (testLine f y .second)
          hd (movingPairBundleRight X.variety X.contact)).hom
      obtain ⟨a, ha⟩ := testLine_right_value f y pi v
      refine ⟨a, ha.trans ?_⟩
      exact transported_vector_value d D.pair.data.projection pi (testLine f y .second)
        hd (movingPairContactRight X.variety X.contact) (vectorRight D) D.value
        (vectorRight_value D)

end LeBrunSalamon.Construction.Descent.LineValue

end

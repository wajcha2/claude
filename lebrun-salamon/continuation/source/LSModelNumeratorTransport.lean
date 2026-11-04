import LSModelGenericParametrization
import LSFamilySchemeTransport


/-!
# Equality transport for a distributive expression

This theorem only transports a proposition across equal types and
heterogeneously equal operations and inputs. It assumes no algebraic laws.
-/

set_option autoImplicit false

universe u v w x

namespace EquationTransport

theorem distribution_eq_iff_output
    {A A' : Type u} {R R' : Type v} {S S' : Type w} {B B' : Type x}
    (hA : A = A') (hR : R = R') (hS : S = S') (hB : B = B')
    (L : A → B) (L' : A' → B') (hL : HEq L L')
    (sourceAdd : A → A → A) (sourceAdd' : A' → A' → A')
    (hSourceAdd : HEq sourceAdd sourceAdd')
    (sourceSub : A → A → A) (sourceSub' : A' → A' → A')
    (hSourceSub : HEq sourceSub sourceSub')
    (sourceScale : R → A → A) (sourceScale' : R' → A' → A')
    (hSourceScale : HEq sourceScale sourceScale')
    (targetAdd : B → B → B) (targetAdd' : B' → B' → B')
    (hTargetAdd : HEq targetAdd targetAdd')
    (targetSub : B → B → B) (targetSub' : B' → B' → B')
    (hTargetSub : HEq targetSub targetSub')
    (targetScale : S → B → B) (targetScale' : S' → B' → B')
    (hTargetScale : HEq targetScale targetScale')
    (coefficient : R → S) (coefficient' : R' → S')
    (hCoefficient : HEq coefficient coefficient')
    (a b c : A) (a' b' c' : A')
    (ha : HEq a a') (hb : HEq b b') (hc : HEq c c')
    (r : R) (r' : R') (hr : HEq r r') :
    (L (sourceSub (sourceAdd a b) (sourceScale r c)) =
      targetSub (targetAdd (L a) (L b))
        (targetScale (coefficient r) (L c))) ↔
    (L' (sourceSub' (sourceAdd' a' b') (sourceScale' r' c')) =
      targetSub' (targetAdd' (L' a') (L' b'))
        (targetScale' (coefficient' r') (L' c'))) := by
  cases hA
  cases hR
  cases hS
  cases hB
  have hL_eq : L = L' := eq_of_heq hL
  cases hL_eq
  have hSourceAdd_eq : sourceAdd = sourceAdd' := eq_of_heq hSourceAdd
  cases hSourceAdd_eq
  have hSourceSub_eq : sourceSub = sourceSub' := eq_of_heq hSourceSub
  cases hSourceSub_eq
  have hSourceScale_eq : sourceScale = sourceScale' := eq_of_heq hSourceScale
  cases hSourceScale_eq
  have hTargetAdd_eq : targetAdd = targetAdd' := eq_of_heq hTargetAdd
  cases hTargetAdd_eq
  have hTargetSub_eq : targetSub = targetSub' := eq_of_heq hTargetSub
  cases hTargetSub_eq
  have hTargetScale_eq : targetScale = targetScale' := eq_of_heq hTargetScale
  cases hTargetScale_eq
  have hCoefficient_eq : coefficient = coefficient' := eq_of_heq hCoefficient
  cases hCoefficient_eq
  have ha_eq : a = a' := eq_of_heq ha
  cases ha_eq
  have hb_eq : b = b' := eq_of_heq hb
  cases hb_eq
  have hc_eq : c = c' := eq_of_heq hc
  cases hc_eq
  have hr_eq : r = r' := eq_of_heq hr
  cases hr_eq
  rfl

end EquationTransport

/-!
# Transport of the actual model numerator

This module isolates the original numerator transport theorem from the
independent parametrization declarations. Its statement is unchanged.
The current proof repair is pending native validation.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseSeven LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentySix LeBrunSalamon.PhaseTwentySeven
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirty
open LeBrunSalamon.PhaseThirtyTwo LeBrunSalamon.PhaseThirtyFive
open LeBrunSalamon.Core LeBrunSalamon.Skeleton LeBrunSalamon.Refinement

namespace LeBrunSalamon.Construction.TraitContact.ModelGenericComparison

local notation "Model" => LeBrunSalamon.Construction.StableMaps.FormalArcs.Model

open StableMaps.FormalArcs StableMaps.FormalArcs.ModelGeometry
open Smoothing.CoordinateCharts Smoothing.SourceAffineCharts
open FamilyBivectors

variable (F : Smoothing.StandardSource) (a : Coefficients)

variable {d : ℕ} (X : SmoothProperComplexVariety d)
variable (e : Model F a ⟶ X.scheme)
variable (he : e ≫ X.structureMap = modelProjection F a ≫ toC)

private theorem numerator_pull_add {T Z : Scheme} (q : T ⟶ Z)
    {V : OModule Z} (s t : AlgebraicSection V) :
    pullSection q (s + t) = pullSection q s + pullSection q t := by
  simp only [pullSection, restrictSection, Functor.map_add, Preadditive.comp_add]

private theorem numerator_box_section {C S : Scheme} (pi : C ⟶ S)
    {L : LineBundle C} (s t : AlgebraicSection L.sheaf) :
    RelativeBox.section pi (L := L) s t =
      RelativeSquare.productSection pi s t := rfl

private theorem numerator_section_specialization {T Z Y : Scheme}
    (k : T ⟶ Z) (eB : Z ⟶ Y) (eA : T ⟶ Y) (hke : k ≫ eB = eA)
    {L : OModule Z} {E : OModule Y}
    (uB : L ⟶ pullbackModule eB E)
    (uA : pullbackModule k L ⟶ pullbackModule eA E)
    (hu : (Scheme.Modules.pullback k).map uB ≫
      (compositionPullback k eB eA hke E).hom = uA)
    (s : AlgebraicSection L) :
    pullSection k (s ≫ uB) ≫ (compositionPullback k eB eA hke E).hom =
      pullSection k s ≫ uA := by
  rw [pullSection_naturality, Category.assoc, hu]

private theorem numerator_source_equation_transport {T T' Y Z : Scheme}
    (hT : T = T') (k : T ⟶ Y) (k' : T' ⟶ Y) (hk : HEq k k')
    (f : Y ⟶ Z) (r : T ⟶ Z) (r' : T' ⟶ Z) (hr : HEq r r')
    (h : k ≫ f = r) (h' : k' ≫ f = r') (E : OModule Z)
    (s : AlgebraicSection (pullbackModule f E))
    (t : AlgebraicSection (pullbackModule r E))
    (t' : AlgebraicSection (pullbackModule r' E)) (ht : HEq t t') :
    (pullSection k s ≫ (compositionPullback k f r h E).hom = t) ↔
      (pullSection k' s ≫ (compositionPullback k' f r' h' E).hom = t') := by
  cases hT
  have hk' : k = k' := eq_of_heq hk
  cases hk'
  have hr' : r = r' := eq_of_heq hr
  cases hr'
  have ht' : t = t' := eq_of_heq ht
  cases ht'
  rfl

private theorem numerator_source_equation_iff {Y Z : Scheme}
    (k : Parametrized.Square Lines.P genericBase ⟶ Y) (f : Y ⟶ Z)
    (r : RelativeSquare.Space p1Parameter ⟶ Z) (h : k ≫ f = r)
    (E : OModule Z) (s : AlgebraicSection (pullbackModule f E))
    (t : AlgebraicSection (pullbackModule r E)) :
    (@pullSection (Parametrized.Square Lines.P genericBase) Y k
        (pullbackModule f E) s ≫
      (@compositionPullback (Parametrized.Square Lines.P genericBase) Y Z
        k f r h E).hom = t) ↔
    (@pullSection (RelativeSquare.Space p1Parameter) Y k
        (pullbackModule f E) s ≫
      (@compositionPullback (RelativeSquare.Space p1Parameter) Y Z
        k f r h E).hom = t) := by
  exact numerator_source_equation_transport
    (show Parametrized.Square Lines.P genericBase = RelativeSquare.Space p1Parameter from rfl)
    k k HEq.rfl f r r HEq.rfl h h E s t t HEq.rfl

private theorem numerator_middle_pull_comp {T Z : Scheme}
    (k : T ⟶ ModelNumerator.Square F a)
    (f : RelativeSquare.Space (modelProjection F a) ⟶ Z)
    (r : T ⟶ Z) (h : k ≫ f = r) (E : OModule Z)
    (s : AlgebraicSection (pullbackModule f E)) :
    @pullSection T (ModelNumerator.Square F a) k (pullbackModule f E) s ≫
      (@compositionPullback T (ModelNumerator.Square F a) Z k f r h E).hom =
    @pullSection T (RelativeSquare.Space (modelProjection F a)) k (pullbackModule f E) s ≫
      (@compositionPullback T (RelativeSquare.Space (modelProjection F a)) Z k f r h E).hom := by
  exact LeBrunSalamon.Construction.FamilySchemeTransport.pull_comp_congr
    (show ModelNumerator.Square F a = RelativeSquare.Space (modelProjection F a) from rfl)
    k k HEq.rfl f f HEq.rfl r h h E s s HEq.rfl

private theorem numerator_product_literal (ha : a ≠ 0)
    {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (eB : Model F a ⟶ Y) (heB : eB ≫ sY = modelProjection F a ≫ toC)
    (eA : P1Generic ⟶ Y) (heA : eA ≫ sY = p1Parameter ≫ genericBase)
    (hke : genericParametrization F a ha ≫ eB = eA)
    {E H : OModule Y}
    (uB : (modelLine F a).sheaf ⟶ pullbackModule eB E)
    (vB : (modelLine F a).sheaf ⟶ pullbackModule eB H)
    (uA : pullbackModule (genericParametrization F a ha) (modelLine F a).sheaf ⟶
      pullbackModule eA E)
    (vA : pullbackModule (genericParametrization F a ha) (modelLine F a).sheaf ⟶
      pullbackModule eA H)
    (hu : (Scheme.Modules.pullback (genericParametrization F a ha)).map uB ≫
      (compositionPullback (genericParametrization F a ha) eB eA hke E).hom = uA)
    (hv : (Scheme.Modules.pullback (genericParametrization F a ha)).map vB ≫
      (compositionPullback (genericParametrization F a ha) eB eA hke H).hom = vA)
    (s t : AlgebraicSection (modelLine F a).sheaf) :
    @pullSection (RelativeSquare.Space p1Parameter)
      (RelativeSquare.Space (modelProjection F a))
      (parametrizedToModelSquare F a ha)
      (pullbackModule (RelativeSquare.evaluation (modelProjection F a) sY toC eB heB)
        (externalTensor sY E H))
      (RelativeSquare.productSection (modelProjection F a) (s ≫ uB) (t ≫ vB) ≫
        RelativeSquare.comparison (modelProjection F a) sY toC eB heB E H) ≫
      (@compositionPullback (RelativeSquare.Space p1Parameter)
        (RelativeSquare.Space (modelProjection F a)) (SelfProduct sY)
        (parametrizedToModelSquare F a ha)
        (RelativeSquare.evaluation (modelProjection F a) sY toC eB heB)
        (RelativeSquare.evaluation p1Parameter sY genericBase eA heA)
        (RelativeSquare.map_evaluation p1Parameter (modelProjection F a)
          (genericParametrization F a ha) genericPoint
          (genericParametrization_parameter F a ha) sY genericBase toC
          eA eB heA heB hke) (externalTensor sY E H)).hom =
      RelativeSquare.productSection p1Parameter
      (pullSection (genericParametrization F a ha) s ≫ uA) (pullSection (genericParametrization F a ha) t ≫ vA) ≫
      RelativeSquare.comparison p1Parameter sY genericBase eA heA E H := by
  exact RelativeSquare.product_baseChange p1Parameter (modelProjection F a)
    sY genericBase toC eA eB heA heB (genericParametrization F a ha) hke (parametrizedToModelSquare F a ha)
    (RelativeSquare.map_left _ _ _ _ _) (RelativeSquare.map_right _ _ _ _ _)
    (RelativeSquare.map_evaluation p1Parameter (modelProjection F a) (genericParametrization F a ha) genericPoint
      (genericParametrization_parameter F a ha) sY genericBase toC eA eB heA heB hke)
    (s ≫ uB) (t ≫ vB)
    (pullSection (genericParametrization F a ha) s ≫ uA) (pullSection (genericParametrization F a ha) t ≫ vA)
    (numerator_section_specialization (genericParametrization F a ha) eB eA hke uB uA hu s)
    (numerator_section_specialization (genericParametrization F a ha) eB eA hke vB vA hv t)

private theorem numerator_product_transport (ha : a ≠ 0)
    {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (eB : Model F a ⟶ Y) (heB : eB ≫ sY = modelProjection F a ≫ toC)
    (eA : P1Generic ⟶ Y) (heA : eA ≫ sY = p1Parameter ≫ genericBase)
    (hke : genericParametrization F a ha ≫ eB = eA)
    {E H : OModule Y}
    (uB : (modelLine F a).sheaf ⟶ pullbackModule eB E)
    (vB : (modelLine F a).sheaf ⟶ pullbackModule eB H)
    (uA : pullbackModule (genericParametrization F a ha) (modelLine F a).sheaf ⟶
      pullbackModule eA E)
    (vA : pullbackModule (genericParametrization F a ha) (modelLine F a).sheaf ⟶
      pullbackModule eA H)
    (hu : (Scheme.Modules.pullback (genericParametrization F a ha)).map uB ≫
      (compositionPullback (genericParametrization F a ha) eB eA hke E).hom = uA)
    (hv : (Scheme.Modules.pullback (genericParametrization F a ha)).map vB ≫
      (compositionPullback (genericParametrization F a ha) eB eA hke H).hom = vA)
    (s t : AlgebraicSection (modelLine F a).sheaf) :
    pullSection (parametrizedToModelSquare F a ha)
      (RelativeSquare.productSection (modelProjection F a) (s ≫ uB) (t ≫ vB) ≫
        RelativeSquare.comparison (modelProjection F a) sY toC eB heB E H) ≫
      (compositionPullback (parametrizedToModelSquare F a ha)
        (RelativeSquare.evaluation (modelProjection F a) sY toC eB heB)
        (RelativeSquare.evaluation p1Parameter sY genericBase eA heA)
        (RelativeSquare.map_evaluation p1Parameter (modelProjection F a)
          (genericParametrization F a ha) genericPoint
          (genericParametrization_parameter F a ha) sY genericBase toC
          eA eB heA heB hke) (externalTensor sY E H)).hom =
      RelativeSquare.productSection p1Parameter
      (pullSection (genericParametrization F a ha) s ≫ uA) (pullSection (genericParametrization F a ha) t ≫ vA) ≫
      RelativeSquare.comparison p1Parameter sY genericBase eA heA E H := by
  let B : AlgebraicSection
      (pullbackModule (RelativeSquare.evaluation (modelProjection F a) sY toC eB heB)
        (externalTensor sY E H)) :=
    RelativeSquare.productSection (modelProjection F a) (s ≫ uB) (t ≫ vB) ≫
      RelativeSquare.comparison (modelProjection F a) sY toC eB heB E H
  let R : AlgebraicSection
      (pullbackModule (RelativeSquare.evaluation p1Parameter sY genericBase eA heA)
        (externalTensor sY E H)) :=
    RelativeSquare.productSection p1Parameter
      (pullSection (genericParametrization F a ha) s ≫ uA)
      (pullSection (genericParametrization F a ha) t ≫ vA) ≫
      RelativeSquare.comparison p1Parameter sY genericBase eA heA E H
  have hmiddle := numerator_middle_pull_comp F a
    (T := Parametrized.Square Lines.P genericBase) (Z := SelfProduct sY)
    (parametrizedToModelSquare F a ha)
    (RelativeSquare.evaluation (modelProjection F a) sY toC eB heB)
    (RelativeSquare.evaluation p1Parameter sY genericBase eA heA)
    (RelativeSquare.map_evaluation p1Parameter (modelProjection F a)
        (genericParametrization F a ha) genericPoint
        (genericParametrization_parameter F a ha) sY genericBase toC
        eA eB heA heB hke) (externalTensor sY E H) B
  have hsource :=
    (numerator_source_equation_iff
      (Y := RelativeSquare.Space (modelProjection F a)) (Z := SelfProduct sY)
      (parametrizedToModelSquare F a ha)
      (RelativeSquare.evaluation (modelProjection F a) sY toC eB heB)
      (RelativeSquare.evaluation p1Parameter sY genericBase eA heA)
      (RelativeSquare.map_evaluation p1Parameter (modelProjection F a)
        (genericParametrization F a ha) genericPoint
        (genericParametrization_parameter F a ha) sY genericBase toC
        eA eB heA heB hke) (externalTensor sY E H) B R).2
      (numerator_product_literal F a ha sY eB heB eA heA hke uB vB uA vA hu hv s t)
  exact hmiddle.trans hsource

private theorem numerator_coefficient_transport (ha : a ≠ 0) :
    (parametrizedToModelSquare F a ha).appTop
      (2 * (ModelNumerator.squareProjection F a).appTop (coefficientSection a)) = 2 * genericCoefficient F a ha := by
  simp only [genericCoefficient, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    map_mul, map_ofNat]

private theorem numerator_pull_congr {T Z : Scheme} (q : T ⟶ Z)
    {E : OModule Z} {G : OModule T} (u : pullbackModule q E ⟶ G)
    {s t : AlgebraicSection E} (h : s = t) :
    pullSection q s ≫ u = pullSection q t ≫ u :=
  congrArg (fun z : AlgebraicSection E => pullSection q z ≫ u) h

private theorem numerator_pull_three {T Z : Scheme} (q : T ⟶ Z)
    {E : OModule Z} {G : OModule T} (u : pullbackModule q E ⟶ G)
    (s t w : AlgebraicSection E) (r : RingSections Z ⊤) :
    pullSection q (s + t - scalarSection r ≫ w) ≫ u =
      (pullSection q s ≫ u) + (pullSection q t ≫ u) -
        scalarSection (q.appTop r) ≫ (pullSection q w ≫ u) := by
  simp only [Normalization.BundleGluing.pullSection_sub, numerator_pull_add,
    LogVelocity.pullSection_scalar, Preadditive.add_comp, Preadditive.sub_comp,
    Category.assoc]

private theorem numeratorOpCast_heq {A A' : Type u} (h : A = A') (x : A) :
    HEq x (cast h x) := by
  cases h
  rfl

private theorem numerator_distribution_from_operations
    {T Z : Scheme} (q : T ⟶ Z) {E : OModule Z} {G : OModule T}
    (u : pullbackModule q E ⟶ G)
    {A R S B : Type}
    (hA : A = AlgebraicSection E) (hR : R = RingSections Z ⊤)
    (hS : S = RingSections T ⊤) (hB : B = AlgebraicSection G)
    (L : A → B)
    (hL : HEq L (fun x : AlgebraicSection E => pullSection q x ≫ u))
    (sourceAdd sourceSub : A → A → A)
    (hSourceAdd : HEq sourceAdd (fun x y : AlgebraicSection E => x + y))
    (hSourceSub : HEq sourceSub (fun x y : AlgebraicSection E => x - y))
    (sourceScale : R → A → A)
    (hSourceScale : HEq sourceScale
      (fun r : RingSections Z ⊤ => fun x : AlgebraicSection E => scalarSection r ≫ x))
    (targetAdd targetSub : B → B → B)
    (hTargetAdd : HEq targetAdd (fun x y : AlgebraicSection G => x + y))
    (hTargetSub : HEq targetSub (fun x y : AlgebraicSection G => x - y))
    (targetScale : S → B → B)
    (hTargetScale : HEq targetScale
      (fun r : RingSections T ⊤ => fun x : AlgebraicSection G => scalarSection r ≫ x))
    (coefficient : R → S)
    (hCoefficient : HEq coefficient (fun r : RingSections Z ⊤ => q.appTop r))
    (x y z : A) (r : R) :
    L (sourceSub (sourceAdd x y) (sourceScale r z)) =
      targetSub (targetAdd (L x) (L y)) (targetScale (coefficient r) (L z)) := by
  exact (EquationTransport.distribution_eq_iff_output hA hR hS hB
    L (fun x : AlgebraicSection E => pullSection q x ≫ u) hL
    sourceAdd (fun x y : AlgebraicSection E => x + y) hSourceAdd
    sourceSub (fun x y : AlgebraicSection E => x - y) hSourceSub
    sourceScale
      (fun r : RingSections Z ⊤ => fun x : AlgebraicSection E => scalarSection r ≫ x)
      hSourceScale
    targetAdd (fun x y : AlgebraicSection G => x + y) hTargetAdd
    targetSub (fun x y : AlgebraicSection G => x - y) hTargetSub
    targetScale
      (fun r : RingSections T ⊤ => fun x : AlgebraicSection G => scalarSection r ≫ x)
      hTargetScale
    coefficient (fun r : RingSections Z ⊤ => q.appTop r) hCoefficient
    x y z (cast hA x) (cast hA y) (cast hA z)
    (numeratorOpCast_heq hA x) (numeratorOpCast_heq hA y)
    (numeratorOpCast_heq hA z) r (cast hR r) (numeratorOpCast_heq hR r)).2
      (numerator_pull_three q u (cast hA x) (cast hA y) (cast hA z) (cast hR r))

private theorem numerator_map_three {C S : Scheme} (pi : C ⟶ S)
    {L : LineBundle C} {E H : OModule C} {G : OModule (RelativeSquare.Space pi)}
    (u : L.sheaf ⟶ E) (v : L.sheaf ⟶ H)
    (q : RelativeSquare.box pi E H ⟶ G)
    (s t w : AlgebraicSection L.sheaf) (r : RingSections (RelativeSquare.Space pi) ⊤) :
    (RelativeBox.section pi s t + RelativeBox.section pi t s -
      sectionFromValue (r • sectionValue (RelativeBox.section pi w w))) ≫
        RelativeSquare.boxMap pi u v ≫ q =
      (RelativeSquare.productSection pi (s ≫ u) (t ≫ v) ≫ q) +
      (RelativeSquare.productSection pi (t ≫ u) (s ≫ v) ≫ q) -
      scalarSection r ≫ (RelativeSquare.productSection pi (w ≫ u) (w ≫ v) ≫ q) := by
  rw [section_scale]
  simp only [Preadditive.add_comp, Preadditive.sub_comp, Category.assoc,
    numerator_box_section, RelativeSquare.productSection_map_assoc]

private theorem numerator_mapped_formula (ha : a ≠ 0)
    {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (eB : Model F a ⟶ Y) (heB : eB ≫ sY = modelProjection F a ≫ toC)
    (eA : P1Generic ⟶ Y) (heA : eA ≫ sY = p1Parameter ≫ genericBase)
    (hke : genericParametrization F a ha ≫ eB = eA)
    {E H : OModule Y}
    (uB : (modelLine F a).sheaf ⟶ pullbackModule eB E)
    (vB : (modelLine F a).sheaf ⟶ pullbackModule eB H)
    (uA : pullbackModule (genericParametrization F a ha) (modelLine F a).sheaf ⟶
      pullbackModule eA E)
    (vA : pullbackModule (genericParametrization F a ha) (modelLine F a).sheaf ⟶
      pullbackModule eA H)
    (hu : (Scheme.Modules.pullback (genericParametrization F a ha)).map uB ≫
      (compositionPullback (genericParametrization F a ha) eB eA hke E).hom = uA)
    (hv : (Scheme.Modules.pullback (genericParametrization F a ha)).map vB ≫
      (compositionPullback (genericParametrization F a ha) eB eA hke H).hom = vA) :
    ModelNumerator.numerator F a ≫
      RelativeSquare.boxMap (modelProjection F a) uB vB ≫
        RelativeSquare.comparison (modelProjection F a) sY toC eB heB E H =
      (RelativeSquare.productSection (modelProjection F a) (ModelNumerator.coordinate F a 1 0 ≫ uB) (ModelNumerator.coordinate F a 0 1 ≫ vB) ≫
        RelativeSquare.comparison (modelProjection F a) sY toC eB heB E H) +
      (RelativeSquare.productSection (modelProjection F a) (ModelNumerator.coordinate F a 0 1 ≫ uB) (ModelNumerator.coordinate F a 1 0 ≫ vB) ≫
        RelativeSquare.comparison (modelProjection F a) sY toC eB heB E H) -
      scalarSection (2 * (ModelNumerator.squareProjection F a).appTop (coefficientSection a)) ≫ (RelativeSquare.productSection (modelProjection F a) (ModelNumerator.coordinate F a 0 0 ≫ uB) (ModelNumerator.coordinate F a 0 0 ≫ vB) ≫
        RelativeSquare.comparison (modelProjection F a) sY toC eB heB E H) := by
  exact numerator_map_three (modelProjection F a) uB vB
    (RelativeSquare.comparison (modelProjection F a) sY toC eB heB E H)
    (ModelNumerator.coordinate F a 1 0) (ModelNumerator.coordinate F a 0 1) (ModelNumerator.coordinate F a 0 0) (2 * (ModelNumerator.squareProjection F a).appTop (coefficientSection a))

private theorem numerator_source_pulled_formula (ha : a ≠ 0)
    {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (eB : Model F a ⟶ Y) (heB : eB ≫ sY = modelProjection F a ≫ toC)
    (eA : P1Generic ⟶ Y) (heA : eA ≫ sY = p1Parameter ≫ genericBase)
    (hke : genericParametrization F a ha ≫ eB = eA)
    {E H : OModule Y}
    (uB : (modelLine F a).sheaf ⟶ pullbackModule eB E)
    (vB : (modelLine F a).sheaf ⟶ pullbackModule eB H)
    (uA : pullbackModule (genericParametrization F a ha) (modelLine F a).sheaf ⟶
      pullbackModule eA E)
    (vA : pullbackModule (genericParametrization F a ha) (modelLine F a).sheaf ⟶
      pullbackModule eA H)
    (hu : (Scheme.Modules.pullback (genericParametrization F a ha)).map uB ≫
      (compositionPullback (genericParametrization F a ha) eB eA hke E).hom = uA)
    (hv : (Scheme.Modules.pullback (genericParametrization F a ha)).map vB ≫
      (compositionPullback (genericParametrization F a ha) eB eA hke H).hom = vA) :
    pullSection (parametrizedToModelSquare F a ha)
      (ModelNumerator.numerator F a ≫
        RelativeSquare.boxMap (modelProjection F a) uB vB ≫
          RelativeSquare.comparison (modelProjection F a) sY toC eB heB E H) ≫
      (compositionPullback (parametrizedToModelSquare F a ha)
        (RelativeSquare.evaluation (modelProjection F a) sY toC eB heB)
        (RelativeSquare.evaluation p1Parameter sY genericBase eA heA)
        (RelativeSquare.map_evaluation p1Parameter (modelProjection F a)
          (genericParametrization F a ha) genericPoint
          (genericParametrization_parameter F a ha) sY genericBase toC
          eA eB heA heB hke) (externalTensor sY E H)).hom =
      pullSection (parametrizedToModelSquare F a ha)
      ((RelativeSquare.productSection (modelProjection F a) (ModelNumerator.coordinate F a 1 0 ≫ uB) (ModelNumerator.coordinate F a 0 1 ≫ vB) ≫
        RelativeSquare.comparison (modelProjection F a) sY toC eB heB E H) + (RelativeSquare.productSection (modelProjection F a) (ModelNumerator.coordinate F a 0 1 ≫ uB) (ModelNumerator.coordinate F a 1 0 ≫ vB) ≫
        RelativeSquare.comparison (modelProjection F a) sY toC eB heB E H) - scalarSection (2 * (ModelNumerator.squareProjection F a).appTop (coefficientSection a)) ≫ (RelativeSquare.productSection (modelProjection F a) (ModelNumerator.coordinate F a 0 0 ≫ uB) (ModelNumerator.coordinate F a 0 0 ≫ vB) ≫
        RelativeSquare.comparison (modelProjection F a) sY toC eB heB E H)) ≫
      (compositionPullback (parametrizedToModelSquare F a ha)
        (RelativeSquare.evaluation (modelProjection F a) sY toC eB heB)
        (RelativeSquare.evaluation p1Parameter sY genericBase eA heA)
        (RelativeSquare.map_evaluation p1Parameter (modelProjection F a)
          (genericParametrization F a ha) genericPoint
          (genericParametrization_parameter F a ha) sY genericBase toC
          eA eB heA heB hke) (externalTensor sY E H)).hom := by
  exact numerator_pull_congr (parametrizedToModelSquare F a ha)
    (compositionPullback (parametrizedToModelSquare F a ha)
        (RelativeSquare.evaluation (modelProjection F a) sY toC eB heB)
        (RelativeSquare.evaluation p1Parameter sY genericBase eA heA)
        (RelativeSquare.map_evaluation p1Parameter (modelProjection F a)
          (genericParametrization F a ha) genericPoint
          (genericParametrization_parameter F a ha) sY genericBase toC
          eA eB heA heB hke) (externalTensor sY E H)).hom
    (numerator_mapped_formula F a ha sY eB heB eA heA hke uB vB uA vA hu hv)

private theorem numeratorRawA_eq (ha : a ≠ 0)
    {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (eB : Model F a ⟶ Y) (heB : eB ≫ sY = modelProjection F a ≫ toC)
    (eA : P1Generic ⟶ Y) (heA : eA ≫ sY = p1Parameter ≫ genericBase)
    (hke : genericParametrization F a ha ≫ eB = eA)
    {E H : OModule Y}
    (uB : (modelLine F a).sheaf ⟶ pullbackModule eB E)
    (vB : (modelLine F a).sheaf ⟶ pullbackModule eB H)
    (uA : pullbackModule (genericParametrization F a ha) (modelLine F a).sheaf ⟶
      pullbackModule eA E)
    (vA : pullbackModule (genericParametrization F a ha) (modelLine F a).sheaf ⟶
      pullbackModule eA H)
    (hu : (Scheme.Modules.pullback (genericParametrization F a ha)).map uB ≫
      (compositionPullback (genericParametrization F a ha) eB eA hke E).hom = uA)
    (hv : (Scheme.Modules.pullback (genericParametrization F a ha)).map vB ≫
      (compositionPullback (genericParametrization F a ha) eB eA hke H).hom = vA) :
    (@Quiver.Hom (SheafOfModules (RelativeSquare.Space (modelProjection F a)).ringCatSheaf) (@CategoryStruct.toQuiver (SheafOfModules (RelativeSquare.Space (modelProjection F a)).ringCatSheaf) (@Category.toCategoryStruct (SheafOfModules (RelativeSquare.Space (modelProjection F a)).ringCatSheaf) SheafOfModules.instCategory)) (SheafOfModules.unit (RelativeSquare.Space (modelProjection F a)).ringCatSheaf) (@pullbackModule (RelativeSquare.Space (modelProjection F a)) (SelfProduct sY) (RelativeSquare.evaluation (modelProjection F a) sY toC eB heB) (externalTensor sY E H))) = (@AlgebraicSection (ModelNumerator.Square F a) (@pullbackModule (ModelNumerator.Square F a) (SelfProduct sY) (RelativeSquare.evaluation (modelProjection F a) sY toC eB heB) (externalTensor sY E H))) := by rfl

private theorem numeratorRawR_eq (ha : a ≠ 0)
    {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (eB : Model F a ⟶ Y) (heB : eB ≫ sY = modelProjection F a ≫ toC)
    (eA : P1Generic ⟶ Y) (heA : eA ≫ sY = p1Parameter ≫ genericBase)
    (hke : genericParametrization F a ha ≫ eB = eA)
    {E H : OModule Y}
    (uB : (modelLine F a).sheaf ⟶ pullbackModule eB E)
    (vB : (modelLine F a).sheaf ⟶ pullbackModule eB H)
    (uA : pullbackModule (genericParametrization F a ha) (modelLine F a).sheaf ⟶
      pullbackModule eA E)
    (vA : pullbackModule (genericParametrization F a ha) (modelLine F a).sheaf ⟶
      pullbackModule eA H)
    (hu : (Scheme.Modules.pullback (genericParametrization F a ha)).map uB ≫
      (compositionPullback (genericParametrization F a ha) eB eA hke E).hom = uA)
    (hv : (Scheme.Modules.pullback (genericParametrization F a ha)).map vB ≫
      (compositionPullback (genericParametrization F a ha) eB eA hke H).hom = vA) :
    ↥((ModelNumerator.Square F a).presheaf.obj (@Opposite.op (ModelNumerator.Square F a).Opens (⊤ : (ModelNumerator.Square F a).Opens))) = (RingSections (ModelNumerator.Square F a) ⊤) := by rfl

private theorem numeratorRawS_eq (ha : a ≠ 0)
    {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (eB : Model F a ⟶ Y) (heB : eB ≫ sY = modelProjection F a ≫ toC)
    (eA : P1Generic ⟶ Y) (heA : eA ≫ sY = p1Parameter ≫ genericBase)
    (hke : genericParametrization F a ha ≫ eB = eA)
    {E H : OModule Y}
    (uB : (modelLine F a).sheaf ⟶ pullbackModule eB E)
    (vB : (modelLine F a).sheaf ⟶ pullbackModule eB H)
    (uA : pullbackModule (genericParametrization F a ha) (modelLine F a).sheaf ⟶
      pullbackModule eA E)
    (vA : pullbackModule (genericParametrization F a ha) (modelLine F a).sheaf ⟶
      pullbackModule eA H)
    (hu : (Scheme.Modules.pullback (genericParametrization F a ha)).map uB ≫
      (compositionPullback (genericParametrization F a ha) eB eA hke E).hom = uA)
    (hv : (Scheme.Modules.pullback (genericParametrization F a ha)).map vB ≫
      (compositionPullback (genericParametrization F a ha) eB eA hke H).hom = vA) :
    ↥((Parametrized.Square Lines.P genericBase).presheaf.obj (@Opposite.op (Parametrized.Square Lines.P genericBase).Opens (⊤ : (Parametrized.Square Lines.P genericBase).Opens))) = (RingSections (Parametrized.Square Lines.P genericBase) ⊤) := by rfl

private theorem numeratorRawB_eq (ha : a ≠ 0)
    {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (eB : Model F a ⟶ Y) (heB : eB ≫ sY = modelProjection F a ≫ toC)
    (eA : P1Generic ⟶ Y) (heA : eA ≫ sY = p1Parameter ≫ genericBase)
    (hke : genericParametrization F a ha ≫ eB = eA)
    {E H : OModule Y}
    (uB : (modelLine F a).sheaf ⟶ pullbackModule eB E)
    (vB : (modelLine F a).sheaf ⟶ pullbackModule eB H)
    (uA : pullbackModule (genericParametrization F a ha) (modelLine F a).sheaf ⟶
      pullbackModule eA E)
    (vA : pullbackModule (genericParametrization F a ha) (modelLine F a).sheaf ⟶
      pullbackModule eA H)
    (hu : (Scheme.Modules.pullback (genericParametrization F a ha)).map uB ≫
      (compositionPullback (genericParametrization F a ha) eB eA hke E).hom = uA)
    (hv : (Scheme.Modules.pullback (genericParametrization F a ha)).map vB ≫
      (compositionPullback (genericParametrization F a ha) eB eA hke H).hom = vA) :
    (@Quiver.Hom (SheafOfModules (Parametrized.Square Lines.P genericBase).ringCatSheaf) (@CategoryStruct.toQuiver (SheafOfModules (Parametrized.Square Lines.P genericBase).ringCatSheaf) (@Category.toCategoryStruct (SheafOfModules (Parametrized.Square Lines.P genericBase).ringCatSheaf) SheafOfModules.instCategory)) (SheafOfModules.unit (Parametrized.Square Lines.P genericBase).ringCatSheaf) (@pullbackModule (Parametrized.Square Lines.P genericBase) (SelfProduct sY) (RelativeSquare.evaluation p1Parameter sY genericBase eA heA) (externalTensor sY E H))) = (@AlgebraicSection (Parametrized.Square Lines.P genericBase) (@pullbackModule (Parametrized.Square Lines.P genericBase) (SelfProduct sY) (RelativeSquare.evaluation p1Parameter sY genericBase eA heA) (externalTensor sY E H))) := by rfl

private theorem numeratorRawAction_heq (ha : a ≠ 0)
    {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (eB : Model F a ⟶ Y) (heB : eB ≫ sY = modelProjection F a ≫ toC)
    (eA : P1Generic ⟶ Y) (heA : eA ≫ sY = p1Parameter ≫ genericBase)
    (hke : genericParametrization F a ha ≫ eB = eA)
    {E H : OModule Y}
    (uB : (modelLine F a).sheaf ⟶ pullbackModule eB E)
    (vB : (modelLine F a).sheaf ⟶ pullbackModule eB H)
    (uA : pullbackModule (genericParametrization F a ha) (modelLine F a).sheaf ⟶
      pullbackModule eA E)
    (vA : pullbackModule (genericParametrization F a ha) (modelLine F a).sheaf ⟶
      pullbackModule eA H)
    (hu : (Scheme.Modules.pullback (genericParametrization F a ha)).map uB ≫
      (compositionPullback (genericParametrization F a ha) eB eA hke E).hom = uA)
    (hv : (Scheme.Modules.pullback (genericParametrization F a ha)).map vB ≫
      (compositionPullback (genericParametrization F a ha) eB eA hke H).hom = vA) :
    @HEq ((@Quiver.Hom (SheafOfModules (RelativeSquare.Space (modelProjection F a)).ringCatSheaf) (@CategoryStruct.toQuiver (SheafOfModules (RelativeSquare.Space (modelProjection F a)).ringCatSheaf) (@Category.toCategoryStruct (SheafOfModules (RelativeSquare.Space (modelProjection F a)).ringCatSheaf) SheafOfModules.instCategory)) (SheafOfModules.unit (RelativeSquare.Space (modelProjection F a)).ringCatSheaf) (@pullbackModule (RelativeSquare.Space (modelProjection F a)) (SelfProduct sY) (RelativeSquare.evaluation (modelProjection F a) sY toC eB heB) (externalTensor sY E H))) → (@Quiver.Hom (SheafOfModules (Parametrized.Square Lines.P genericBase).ringCatSheaf) (@CategoryStruct.toQuiver (SheafOfModules (Parametrized.Square Lines.P genericBase).ringCatSheaf) (@Category.toCategoryStruct (SheafOfModules (Parametrized.Square Lines.P genericBase).ringCatSheaf) SheafOfModules.instCategory)) (SheafOfModules.unit (Parametrized.Square Lines.P genericBase).ringCatSheaf) (@pullbackModule (Parametrized.Square Lines.P genericBase) (SelfProduct sY) (RelativeSquare.evaluation p1Parameter sY genericBase eA heA) (externalTensor sY E H)))) (fun x : (@Quiver.Hom (SheafOfModules (RelativeSquare.Space (modelProjection F a)).ringCatSheaf) (@CategoryStruct.toQuiver (SheafOfModules (RelativeSquare.Space (modelProjection F a)).ringCatSheaf) (@Category.toCategoryStruct (SheafOfModules (RelativeSquare.Space (modelProjection F a)).ringCatSheaf) SheafOfModules.instCategory)) (SheafOfModules.unit (RelativeSquare.Space (modelProjection F a)).ringCatSheaf) (@pullbackModule (RelativeSquare.Space (modelProjection F a)) (SelfProduct sY) (RelativeSquare.evaluation (modelProjection F a) sY toC eB heB) (externalTensor sY E H))) => (@CategoryStruct.comp (SheafOfModules (Parametrized.Square Lines.P genericBase).ringCatSheaf) _ _ _ _ (@pullSection (Parametrized.Square Lines.P genericBase) (ModelNumerator.Square F a) (parametrizedToModelSquare F a ha) (@pullbackModule (RelativeSquare.Space (modelProjection F a)) (SelfProduct sY) (RelativeSquare.evaluation (modelProjection F a) sY toC eB heB) (externalTensor sY E H)) x) ((@compositionPullback (Parametrized.Square Lines.P genericBase) (ModelNumerator.Square F a) (SelfProduct sY) (parametrizedToModelSquare F a ha) (RelativeSquare.evaluation (modelProjection F a) sY toC eB heB) (RelativeSquare.evaluation p1Parameter sY genericBase eA heA)
        (RelativeSquare.map_evaluation p1Parameter (modelProjection F a)
          (genericParametrization F a ha) genericPoint
          (genericParametrization_parameter F a ha) sY genericBase toC
          eA eB heA heB hke) (externalTensor sY E H)).hom))) _ (fun x : (@AlgebraicSection (ModelNumerator.Square F a) (@pullbackModule (ModelNumerator.Square F a) (SelfProduct sY) (RelativeSquare.evaluation (modelProjection F a) sY toC eB heB) (externalTensor sY E H))) => @pullSection (Parametrized.Square Lines.P genericBase) (ModelNumerator.Square F a) (parametrizedToModelSquare F a ha) (@pullbackModule (ModelNumerator.Square F a) (SelfProduct sY) (RelativeSquare.evaluation (modelProjection F a) sY toC eB heB) (externalTensor sY E H)) x ≫ (@compositionPullback (Parametrized.Square Lines.P genericBase) (ModelNumerator.Square F a) (SelfProduct sY) (parametrizedToModelSquare F a ha) (RelativeSquare.evaluation (modelProjection F a) sY toC eB heB) (RelativeSquare.evaluation p1Parameter sY genericBase eA heA)
        (RelativeSquare.map_evaluation p1Parameter (modelProjection F a)
          (genericParametrization F a ha) genericPoint
          (genericParametrization_parameter F a ha) sY genericBase toC
          eA eB heA heB hke) (externalTensor sY E H)).hom) := by rfl

private theorem numeratorRawSourceAdd_heq (ha : a ≠ 0)
    {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (eB : Model F a ⟶ Y) (heB : eB ≫ sY = modelProjection F a ≫ toC)
    (eA : P1Generic ⟶ Y) (heA : eA ≫ sY = p1Parameter ≫ genericBase)
    (hke : genericParametrization F a ha ≫ eB = eA)
    {E H : OModule Y}
    (uB : (modelLine F a).sheaf ⟶ pullbackModule eB E)
    (vB : (modelLine F a).sheaf ⟶ pullbackModule eB H)
    (uA : pullbackModule (genericParametrization F a ha) (modelLine F a).sheaf ⟶
      pullbackModule eA E)
    (vA : pullbackModule (genericParametrization F a ha) (modelLine F a).sheaf ⟶
      pullbackModule eA H)
    (hu : (Scheme.Modules.pullback (genericParametrization F a ha)).map uB ≫
      (compositionPullback (genericParametrization F a ha) eB eA hke E).hom = uA)
    (hv : (Scheme.Modules.pullback (genericParametrization F a ha)).map vB ≫
      (compositionPullback (genericParametrization F a ha) eB eA hke H).hom = vA) :
    HEq (fun x y : (@Quiver.Hom (SheafOfModules (RelativeSquare.Space (modelProjection F a)).ringCatSheaf) (@CategoryStruct.toQuiver (SheafOfModules (RelativeSquare.Space (modelProjection F a)).ringCatSheaf) (@Category.toCategoryStruct (SheafOfModules (RelativeSquare.Space (modelProjection F a)).ringCatSheaf) SheafOfModules.instCategory)) (SheafOfModules.unit (RelativeSquare.Space (modelProjection F a)).ringCatSheaf) (@pullbackModule (RelativeSquare.Space (modelProjection F a)) (SelfProduct sY) (RelativeSquare.evaluation (modelProjection F a) sY toC eB heB) (externalTensor sY E H))) => x + y) (fun x y : (@AlgebraicSection (ModelNumerator.Square F a) (@pullbackModule (ModelNumerator.Square F a) (SelfProduct sY) (RelativeSquare.evaluation (modelProjection F a) sY toC eB heB) (externalTensor sY E H))) => x + y) := by rfl

private theorem numeratorRawSourceSub_heq (ha : a ≠ 0)
    {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (eB : Model F a ⟶ Y) (heB : eB ≫ sY = modelProjection F a ≫ toC)
    (eA : P1Generic ⟶ Y) (heA : eA ≫ sY = p1Parameter ≫ genericBase)
    (hke : genericParametrization F a ha ≫ eB = eA)
    {E H : OModule Y}
    (uB : (modelLine F a).sheaf ⟶ pullbackModule eB E)
    (vB : (modelLine F a).sheaf ⟶ pullbackModule eB H)
    (uA : pullbackModule (genericParametrization F a ha) (modelLine F a).sheaf ⟶
      pullbackModule eA E)
    (vA : pullbackModule (genericParametrization F a ha) (modelLine F a).sheaf ⟶
      pullbackModule eA H)
    (hu : (Scheme.Modules.pullback (genericParametrization F a ha)).map uB ≫
      (compositionPullback (genericParametrization F a ha) eB eA hke E).hom = uA)
    (hv : (Scheme.Modules.pullback (genericParametrization F a ha)).map vB ≫
      (compositionPullback (genericParametrization F a ha) eB eA hke H).hom = vA) :
    HEq (fun x y : (@Quiver.Hom (SheafOfModules (RelativeSquare.Space (modelProjection F a)).ringCatSheaf) (@CategoryStruct.toQuiver (SheafOfModules (RelativeSquare.Space (modelProjection F a)).ringCatSheaf) (@Category.toCategoryStruct (SheafOfModules (RelativeSquare.Space (modelProjection F a)).ringCatSheaf) SheafOfModules.instCategory)) (SheafOfModules.unit (RelativeSquare.Space (modelProjection F a)).ringCatSheaf) (@pullbackModule (RelativeSquare.Space (modelProjection F a)) (SelfProduct sY) (RelativeSquare.evaluation (modelProjection F a) sY toC eB heB) (externalTensor sY E H))) => x - y) (fun x y : (@AlgebraicSection (ModelNumerator.Square F a) (@pullbackModule (ModelNumerator.Square F a) (SelfProduct sY) (RelativeSquare.evaluation (modelProjection F a) sY toC eB heB) (externalTensor sY E H))) => x - y) := by rfl

private theorem numeratorRawSourceScale_heq (ha : a ≠ 0)
    {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (eB : Model F a ⟶ Y) (heB : eB ≫ sY = modelProjection F a ≫ toC)
    (eA : P1Generic ⟶ Y) (heA : eA ≫ sY = p1Parameter ≫ genericBase)
    (hke : genericParametrization F a ha ≫ eB = eA)
    {E H : OModule Y}
    (uB : (modelLine F a).sheaf ⟶ pullbackModule eB E)
    (vB : (modelLine F a).sheaf ⟶ pullbackModule eB H)
    (uA : pullbackModule (genericParametrization F a ha) (modelLine F a).sheaf ⟶
      pullbackModule eA E)
    (vA : pullbackModule (genericParametrization F a ha) (modelLine F a).sheaf ⟶
      pullbackModule eA H)
    (hu : (Scheme.Modules.pullback (genericParametrization F a ha)).map uB ≫
      (compositionPullback (genericParametrization F a ha) eB eA hke E).hom = uA)
    (hv : (Scheme.Modules.pullback (genericParametrization F a ha)).map vB ≫
      (compositionPullback (genericParametrization F a ha) eB eA hke H).hom = vA) :
    HEq (fun r : ↥((ModelNumerator.Square F a).presheaf.obj (@Opposite.op (ModelNumerator.Square F a).Opens (⊤ : (ModelNumerator.Square F a).Opens))) => fun x : (@Quiver.Hom (SheafOfModules (RelativeSquare.Space (modelProjection F a)).ringCatSheaf) (@CategoryStruct.toQuiver (SheafOfModules (RelativeSquare.Space (modelProjection F a)).ringCatSheaf) (@Category.toCategoryStruct (SheafOfModules (RelativeSquare.Space (modelProjection F a)).ringCatSheaf) SheafOfModules.instCategory)) (SheafOfModules.unit (RelativeSquare.Space (modelProjection F a)).ringCatSheaf) (@pullbackModule (RelativeSquare.Space (modelProjection F a)) (SelfProduct sY) (RelativeSquare.evaluation (modelProjection F a) sY toC eB heB) (externalTensor sY E H))) => (@CategoryStruct.comp (SheafOfModules (RelativeSquare.Space (modelProjection F a)).ringCatSheaf) _ _ _ _ (@scalarSection (RelativeSquare.Space (modelProjection F a)) r) (x))) (fun r : (RingSections (ModelNumerator.Square F a) ⊤) => fun x : (@AlgebraicSection (ModelNumerator.Square F a) (@pullbackModule (ModelNumerator.Square F a) (SelfProduct sY) (RelativeSquare.evaluation (modelProjection F a) sY toC eB heB) (externalTensor sY E H))) => @scalarSection (ModelNumerator.Square F a) r ≫ x) := by rfl

private theorem numeratorRawTargetAdd_heq (ha : a ≠ 0)
    {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (eB : Model F a ⟶ Y) (heB : eB ≫ sY = modelProjection F a ≫ toC)
    (eA : P1Generic ⟶ Y) (heA : eA ≫ sY = p1Parameter ≫ genericBase)
    (hke : genericParametrization F a ha ≫ eB = eA)
    {E H : OModule Y}
    (uB : (modelLine F a).sheaf ⟶ pullbackModule eB E)
    (vB : (modelLine F a).sheaf ⟶ pullbackModule eB H)
    (uA : pullbackModule (genericParametrization F a ha) (modelLine F a).sheaf ⟶
      pullbackModule eA E)
    (vA : pullbackModule (genericParametrization F a ha) (modelLine F a).sheaf ⟶
      pullbackModule eA H)
    (hu : (Scheme.Modules.pullback (genericParametrization F a ha)).map uB ≫
      (compositionPullback (genericParametrization F a ha) eB eA hke E).hom = uA)
    (hv : (Scheme.Modules.pullback (genericParametrization F a ha)).map vB ≫
      (compositionPullback (genericParametrization F a ha) eB eA hke H).hom = vA) :
    HEq (fun x y : (@Quiver.Hom (SheafOfModules (Parametrized.Square Lines.P genericBase).ringCatSheaf) (@CategoryStruct.toQuiver (SheafOfModules (Parametrized.Square Lines.P genericBase).ringCatSheaf) (@Category.toCategoryStruct (SheafOfModules (Parametrized.Square Lines.P genericBase).ringCatSheaf) SheafOfModules.instCategory)) (SheafOfModules.unit (Parametrized.Square Lines.P genericBase).ringCatSheaf) (@pullbackModule (Parametrized.Square Lines.P genericBase) (SelfProduct sY) (RelativeSquare.evaluation p1Parameter sY genericBase eA heA) (externalTensor sY E H))) => x + y) (fun x y : (@AlgebraicSection (Parametrized.Square Lines.P genericBase) (@pullbackModule (Parametrized.Square Lines.P genericBase) (SelfProduct sY) (RelativeSquare.evaluation p1Parameter sY genericBase eA heA) (externalTensor sY E H))) => x + y) := by rfl

private theorem numeratorRawTargetSub_heq (ha : a ≠ 0)
    {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (eB : Model F a ⟶ Y) (heB : eB ≫ sY = modelProjection F a ≫ toC)
    (eA : P1Generic ⟶ Y) (heA : eA ≫ sY = p1Parameter ≫ genericBase)
    (hke : genericParametrization F a ha ≫ eB = eA)
    {E H : OModule Y}
    (uB : (modelLine F a).sheaf ⟶ pullbackModule eB E)
    (vB : (modelLine F a).sheaf ⟶ pullbackModule eB H)
    (uA : pullbackModule (genericParametrization F a ha) (modelLine F a).sheaf ⟶
      pullbackModule eA E)
    (vA : pullbackModule (genericParametrization F a ha) (modelLine F a).sheaf ⟶
      pullbackModule eA H)
    (hu : (Scheme.Modules.pullback (genericParametrization F a ha)).map uB ≫
      (compositionPullback (genericParametrization F a ha) eB eA hke E).hom = uA)
    (hv : (Scheme.Modules.pullback (genericParametrization F a ha)).map vB ≫
      (compositionPullback (genericParametrization F a ha) eB eA hke H).hom = vA) :
    HEq (fun x y : (@Quiver.Hom (SheafOfModules (Parametrized.Square Lines.P genericBase).ringCatSheaf) (@CategoryStruct.toQuiver (SheafOfModules (Parametrized.Square Lines.P genericBase).ringCatSheaf) (@Category.toCategoryStruct (SheafOfModules (Parametrized.Square Lines.P genericBase).ringCatSheaf) SheafOfModules.instCategory)) (SheafOfModules.unit (Parametrized.Square Lines.P genericBase).ringCatSheaf) (@pullbackModule (Parametrized.Square Lines.P genericBase) (SelfProduct sY) (RelativeSquare.evaluation p1Parameter sY genericBase eA heA) (externalTensor sY E H))) => x - y) (fun x y : (@AlgebraicSection (Parametrized.Square Lines.P genericBase) (@pullbackModule (Parametrized.Square Lines.P genericBase) (SelfProduct sY) (RelativeSquare.evaluation p1Parameter sY genericBase eA heA) (externalTensor sY E H))) => x - y) := by rfl

private theorem numeratorRawTargetScale_heq (ha : a ≠ 0)
    {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (eB : Model F a ⟶ Y) (heB : eB ≫ sY = modelProjection F a ≫ toC)
    (eA : P1Generic ⟶ Y) (heA : eA ≫ sY = p1Parameter ≫ genericBase)
    (hke : genericParametrization F a ha ≫ eB = eA)
    {E H : OModule Y}
    (uB : (modelLine F a).sheaf ⟶ pullbackModule eB E)
    (vB : (modelLine F a).sheaf ⟶ pullbackModule eB H)
    (uA : pullbackModule (genericParametrization F a ha) (modelLine F a).sheaf ⟶
      pullbackModule eA E)
    (vA : pullbackModule (genericParametrization F a ha) (modelLine F a).sheaf ⟶
      pullbackModule eA H)
    (hu : (Scheme.Modules.pullback (genericParametrization F a ha)).map uB ≫
      (compositionPullback (genericParametrization F a ha) eB eA hke E).hom = uA)
    (hv : (Scheme.Modules.pullback (genericParametrization F a ha)).map vB ≫
      (compositionPullback (genericParametrization F a ha) eB eA hke H).hom = vA) :
    HEq (fun r : ↥((Parametrized.Square Lines.P genericBase).presheaf.obj (@Opposite.op (Parametrized.Square Lines.P genericBase).Opens (⊤ : (Parametrized.Square Lines.P genericBase).Opens))) => fun x : (@Quiver.Hom (SheafOfModules (Parametrized.Square Lines.P genericBase).ringCatSheaf) (@CategoryStruct.toQuiver (SheafOfModules (Parametrized.Square Lines.P genericBase).ringCatSheaf) (@Category.toCategoryStruct (SheafOfModules (Parametrized.Square Lines.P genericBase).ringCatSheaf) SheafOfModules.instCategory)) (SheafOfModules.unit (Parametrized.Square Lines.P genericBase).ringCatSheaf) (@pullbackModule (Parametrized.Square Lines.P genericBase) (SelfProduct sY) (RelativeSquare.evaluation p1Parameter sY genericBase eA heA) (externalTensor sY E H))) => (@CategoryStruct.comp (SheafOfModules (Parametrized.Square Lines.P genericBase).ringCatSheaf) _ _ _ _ (@scalarSection (Parametrized.Square Lines.P genericBase) r) (x))) (fun r : (RingSections (Parametrized.Square Lines.P genericBase) ⊤) => fun x : (@AlgebraicSection (Parametrized.Square Lines.P genericBase) (@pullbackModule (Parametrized.Square Lines.P genericBase) (SelfProduct sY) (RelativeSquare.evaluation p1Parameter sY genericBase eA heA) (externalTensor sY E H))) => @scalarSection (Parametrized.Square Lines.P genericBase) r ≫ x) := by rfl

private theorem numeratorRawCoefficient_heq (ha : a ≠ 0)
    {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (eB : Model F a ⟶ Y) (heB : eB ≫ sY = modelProjection F a ≫ toC)
    (eA : P1Generic ⟶ Y) (heA : eA ≫ sY = p1Parameter ≫ genericBase)
    (hke : genericParametrization F a ha ≫ eB = eA)
    {E H : OModule Y}
    (uB : (modelLine F a).sheaf ⟶ pullbackModule eB E)
    (vB : (modelLine F a).sheaf ⟶ pullbackModule eB H)
    (uA : pullbackModule (genericParametrization F a ha) (modelLine F a).sheaf ⟶
      pullbackModule eA E)
    (vA : pullbackModule (genericParametrization F a ha) (modelLine F a).sheaf ⟶
      pullbackModule eA H)
    (hu : (Scheme.Modules.pullback (genericParametrization F a ha)).map uB ≫
      (compositionPullback (genericParametrization F a ha) eB eA hke E).hom = uA)
    (hv : (Scheme.Modules.pullback (genericParametrization F a ha)).map vB ≫
      (compositionPullback (genericParametrization F a ha) eB eA hke H).hom = vA) :
    @HEq (↥((ModelNumerator.Square F a).presheaf.obj (@Opposite.op (ModelNumerator.Square F a).Opens (⊤ : (ModelNumerator.Square F a).Opens))) → ↥((Parametrized.Square Lines.P genericBase).presheaf.obj (@Opposite.op (Parametrized.Square Lines.P genericBase).Opens (⊤ : (Parametrized.Square Lines.P genericBase).Opens)))) (fun r : ↥((ModelNumerator.Square F a).presheaf.obj (@Opposite.op (ModelNumerator.Square F a).Opens (⊤ : (ModelNumerator.Square F a).Opens))) => (parametrizedToModelSquare F a ha).appTop r) _ (fun r : (RingSections (ModelNumerator.Square F a) ⊤) => (parametrizedToModelSquare F a ha).appTop r) := by rfl

private def numerator_named_coefficient {T Z : Scheme} (q : T ⟶ Z) :
    (↥(Z.presheaf.obj (@Opposite.op Z.Opens (⊤ : Z.Opens))) →
      ↥(T.presheaf.obj (@Opposite.op T.Opens (⊤ : T.Opens)))) :=
  fun r => q.appTop r

private theorem numerator_named_coefficient_heq {T Z : Scheme} (q : T ⟶ Z) :
    @HEq (↥(Z.presheaf.obj (@Opposite.op Z.Opens (⊤ : Z.Opens))) →
      ↥(T.presheaf.obj (@Opposite.op T.Opens (⊤ : T.Opens))))
      (numerator_named_coefficient q) _
      (fun r : RingSections Z ⊤ => q.appTop r) := by rfl

private theorem numerator_named_coefficient_apply {T Z : Scheme} (q : T ⟶ Z)
    (r : ↥(Z.presheaf.obj (@Opposite.op Z.Opens (⊤ : Z.Opens)))) :
    numerator_named_coefficient q r = q.appTop r := by rfl

private def numerator_target_operator_arguments  (ha : a ≠ 0)
    {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (eB : Model F a ⟶ Y) (heB : eB ≫ sY = modelProjection F a ≫ toC)
    (eA : P1Generic ⟶ Y) (heA : eA ≫ sY = p1Parameter ≫ genericBase)
    (hke : genericParametrization F a ha ≫ eB = eA)
    {E H : OModule Y}
    (uB : (modelLine F a).sheaf ⟶ pullbackModule eB E)
    (vB : (modelLine F a).sheaf ⟶ pullbackModule eB H)
    (uA : pullbackModule (genericParametrization F a ha) (modelLine F a).sheaf ⟶
      pullbackModule eA E)
    (vA : pullbackModule (genericParametrization F a ha) (modelLine F a).sheaf ⟶
      pullbackModule eA H)
    (hu : (Scheme.Modules.pullback (genericParametrization F a ha)).map uB ≫
      (compositionPullback (genericParametrization F a ha) eB eA hke E).hom = uA)
    (hv : (Scheme.Modules.pullback (genericParametrization F a ha)).map vB ≫
      (compositionPullback (genericParametrization F a ha) eB eA hke H).hom = vA) :=
  numerator_distribution_from_operations
    (T := (Parametrized.Square Lines.P genericBase)) (Z := (ModelNumerator.Square F a)) (E := (@pullbackModule (ModelNumerator.Square F a) (SelfProduct sY) (RelativeSquare.evaluation (modelProjection F a) sY toC eB heB) (externalTensor sY E H))) (G := (@pullbackModule (Parametrized.Square Lines.P genericBase) (SelfProduct sY) (RelativeSquare.evaluation p1Parameter sY genericBase eA heA) (externalTensor sY E H)))
    (parametrizedToModelSquare F a ha) (@compositionPullback (Parametrized.Square Lines.P genericBase) (ModelNumerator.Square F a) (SelfProduct sY) (parametrizedToModelSquare F a ha) (RelativeSquare.evaluation (modelProjection F a) sY toC eB heB) (RelativeSquare.evaluation p1Parameter sY genericBase eA heA)
        (RelativeSquare.map_evaluation p1Parameter (modelProjection F a)
          (genericParametrization F a ha) genericPoint
          (genericParametrization_parameter F a ha) sY genericBase toC
          eA eB heA heB hke) (externalTensor sY E H)).hom
    (A := (@Quiver.Hom (SheafOfModules (RelativeSquare.Space (modelProjection F a)).ringCatSheaf) (@CategoryStruct.toQuiver (SheafOfModules (RelativeSquare.Space (modelProjection F a)).ringCatSheaf) (@Category.toCategoryStruct (SheafOfModules (RelativeSquare.Space (modelProjection F a)).ringCatSheaf) SheafOfModules.instCategory)) (SheafOfModules.unit (RelativeSquare.Space (modelProjection F a)).ringCatSheaf) (@pullbackModule (RelativeSquare.Space (modelProjection F a)) (SelfProduct sY) (RelativeSquare.evaluation (modelProjection F a) sY toC eB heB) (externalTensor sY E H)))) (R := ↥((ModelNumerator.Square F a).presheaf.obj (@Opposite.op (ModelNumerator.Square F a).Opens (⊤ : (ModelNumerator.Square F a).Opens)))) (S := ↥((Parametrized.Square Lines.P genericBase).presheaf.obj (@Opposite.op (Parametrized.Square Lines.P genericBase).Opens (⊤ : (Parametrized.Square Lines.P genericBase).Opens)))) (B := (@Quiver.Hom (SheafOfModules (Parametrized.Square Lines.P genericBase).ringCatSheaf) (@CategoryStruct.toQuiver (SheafOfModules (Parametrized.Square Lines.P genericBase).ringCatSheaf) (@Category.toCategoryStruct (SheafOfModules (Parametrized.Square Lines.P genericBase).ringCatSheaf) SheafOfModules.instCategory)) (SheafOfModules.unit (Parametrized.Square Lines.P genericBase).ringCatSheaf) (@pullbackModule (Parametrized.Square Lines.P genericBase) (SelfProduct sY) (RelativeSquare.evaluation p1Parameter sY genericBase eA heA) (externalTensor sY E H))))
    (numeratorRawA_eq F a ha sY eB heB eA heA hke uB vB uA vA hu hv) (numeratorRawR_eq F a ha sY eB heB eA heA hke uB vB uA vA hu hv) (numeratorRawS_eq F a ha sY eB heB eA heA hke uB vB uA vA hu hv) (numeratorRawB_eq F a ha sY eB heB eA heA hke uB vB uA vA hu hv)
    (fun x : (@Quiver.Hom (SheafOfModules (RelativeSquare.Space (modelProjection F a)).ringCatSheaf) (@CategoryStruct.toQuiver (SheafOfModules (RelativeSquare.Space (modelProjection F a)).ringCatSheaf) (@Category.toCategoryStruct (SheafOfModules (RelativeSquare.Space (modelProjection F a)).ringCatSheaf) SheafOfModules.instCategory)) (SheafOfModules.unit (RelativeSquare.Space (modelProjection F a)).ringCatSheaf) (@pullbackModule (RelativeSquare.Space (modelProjection F a)) (SelfProduct sY) (RelativeSquare.evaluation (modelProjection F a) sY toC eB heB) (externalTensor sY E H))) => (@CategoryStruct.comp (SheafOfModules (Parametrized.Square Lines.P genericBase).ringCatSheaf) _ _ _ _ (@pullSection (Parametrized.Square Lines.P genericBase) (ModelNumerator.Square F a) (parametrizedToModelSquare F a ha) (@pullbackModule (RelativeSquare.Space (modelProjection F a)) (SelfProduct sY) (RelativeSquare.evaluation (modelProjection F a) sY toC eB heB) (externalTensor sY E H)) x) ((@compositionPullback (Parametrized.Square Lines.P genericBase) (ModelNumerator.Square F a) (SelfProduct sY) (parametrizedToModelSquare F a ha) (RelativeSquare.evaluation (modelProjection F a) sY toC eB heB) (RelativeSquare.evaluation p1Parameter sY genericBase eA heA)
        (RelativeSquare.map_evaluation p1Parameter (modelProjection F a)
          (genericParametrization F a ha) genericPoint
          (genericParametrization_parameter F a ha) sY genericBase toC
          eA eB heA heB hke) (externalTensor sY E H)).hom))) (numeratorRawAction_heq F a ha sY eB heB eA heA hke uB vB uA vA hu hv)
    (fun x y : (@Quiver.Hom (SheafOfModules (RelativeSquare.Space (modelProjection F a)).ringCatSheaf) (@CategoryStruct.toQuiver (SheafOfModules (RelativeSquare.Space (modelProjection F a)).ringCatSheaf) (@Category.toCategoryStruct (SheafOfModules (RelativeSquare.Space (modelProjection F a)).ringCatSheaf) SheafOfModules.instCategory)) (SheafOfModules.unit (RelativeSquare.Space (modelProjection F a)).ringCatSheaf) (@pullbackModule (RelativeSquare.Space (modelProjection F a)) (SelfProduct sY) (RelativeSquare.evaluation (modelProjection F a) sY toC eB heB) (externalTensor sY E H))) => x + y) (fun x y : (@Quiver.Hom (SheafOfModules (RelativeSquare.Space (modelProjection F a)).ringCatSheaf) (@CategoryStruct.toQuiver (SheafOfModules (RelativeSquare.Space (modelProjection F a)).ringCatSheaf) (@Category.toCategoryStruct (SheafOfModules (RelativeSquare.Space (modelProjection F a)).ringCatSheaf) SheafOfModules.instCategory)) (SheafOfModules.unit (RelativeSquare.Space (modelProjection F a)).ringCatSheaf) (@pullbackModule (RelativeSquare.Space (modelProjection F a)) (SelfProduct sY) (RelativeSquare.evaluation (modelProjection F a) sY toC eB heB) (externalTensor sY E H))) => x - y) (numeratorRawSourceAdd_heq F a ha sY eB heB eA heA hke uB vB uA vA hu hv) (numeratorRawSourceSub_heq F a ha sY eB heB eA heA hke uB vB uA vA hu hv)
    (fun r : ↥((ModelNumerator.Square F a).presheaf.obj (@Opposite.op (ModelNumerator.Square F a).Opens (⊤ : (ModelNumerator.Square F a).Opens))) => fun x : (@Quiver.Hom (SheafOfModules (RelativeSquare.Space (modelProjection F a)).ringCatSheaf) (@CategoryStruct.toQuiver (SheafOfModules (RelativeSquare.Space (modelProjection F a)).ringCatSheaf) (@Category.toCategoryStruct (SheafOfModules (RelativeSquare.Space (modelProjection F a)).ringCatSheaf) SheafOfModules.instCategory)) (SheafOfModules.unit (RelativeSquare.Space (modelProjection F a)).ringCatSheaf) (@pullbackModule (RelativeSquare.Space (modelProjection F a)) (SelfProduct sY) (RelativeSquare.evaluation (modelProjection F a) sY toC eB heB) (externalTensor sY E H))) => (@CategoryStruct.comp (SheafOfModules (RelativeSquare.Space (modelProjection F a)).ringCatSheaf) _ _ _ _ (@scalarSection (RelativeSquare.Space (modelProjection F a)) r) (x))) (numeratorRawSourceScale_heq F a ha sY eB heB eA heA hke uB vB uA vA hu hv)
    (fun x y : (@Quiver.Hom (SheafOfModules (Parametrized.Square Lines.P genericBase).ringCatSheaf) (@CategoryStruct.toQuiver (SheafOfModules (Parametrized.Square Lines.P genericBase).ringCatSheaf) (@Category.toCategoryStruct (SheafOfModules (Parametrized.Square Lines.P genericBase).ringCatSheaf) SheafOfModules.instCategory)) (SheafOfModules.unit (Parametrized.Square Lines.P genericBase).ringCatSheaf) (@pullbackModule (Parametrized.Square Lines.P genericBase) (SelfProduct sY) (RelativeSquare.evaluation p1Parameter sY genericBase eA heA) (externalTensor sY E H))) => x + y) (fun x y : (@Quiver.Hom (SheafOfModules (Parametrized.Square Lines.P genericBase).ringCatSheaf) (@CategoryStruct.toQuiver (SheafOfModules (Parametrized.Square Lines.P genericBase).ringCatSheaf) (@Category.toCategoryStruct (SheafOfModules (Parametrized.Square Lines.P genericBase).ringCatSheaf) SheafOfModules.instCategory)) (SheafOfModules.unit (Parametrized.Square Lines.P genericBase).ringCatSheaf) (@pullbackModule (Parametrized.Square Lines.P genericBase) (SelfProduct sY) (RelativeSquare.evaluation p1Parameter sY genericBase eA heA) (externalTensor sY E H))) => x - y) (numeratorRawTargetAdd_heq F a ha sY eB heB eA heA hke uB vB uA vA hu hv) (numeratorRawTargetSub_heq F a ha sY eB heB eA heA hke uB vB uA vA hu hv)
    (fun r : ↥((Parametrized.Square Lines.P genericBase).presheaf.obj (@Opposite.op (Parametrized.Square Lines.P genericBase).Opens (⊤ : (Parametrized.Square Lines.P genericBase).Opens))) => fun x : (@Quiver.Hom (SheafOfModules (Parametrized.Square Lines.P genericBase).ringCatSheaf) (@CategoryStruct.toQuiver (SheafOfModules (Parametrized.Square Lines.P genericBase).ringCatSheaf) (@Category.toCategoryStruct (SheafOfModules (Parametrized.Square Lines.P genericBase).ringCatSheaf) SheafOfModules.instCategory)) (SheafOfModules.unit (Parametrized.Square Lines.P genericBase).ringCatSheaf) (@pullbackModule (Parametrized.Square Lines.P genericBase) (SelfProduct sY) (RelativeSquare.evaluation p1Parameter sY genericBase eA heA) (externalTensor sY E H))) => (@CategoryStruct.comp (SheafOfModules (Parametrized.Square Lines.P genericBase).ringCatSheaf) _ _ _ _ (@scalarSection (Parametrized.Square Lines.P genericBase) r) (x))) (numeratorRawTargetScale_heq F a ha sY eB heB eA heA hke uB vB uA vA hu hv)
    (numerator_named_coefficient (parametrizedToModelSquare F a ha)) (numerator_named_coefficient_heq (parametrizedToModelSquare F a ha))

private def numerator_target_value_arguments  (ha : a ≠ 0)
    {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (eB : Model F a ⟶ Y) (heB : eB ≫ sY = modelProjection F a ≫ toC)
    (eA : P1Generic ⟶ Y) (heA : eA ≫ sY = p1Parameter ≫ genericBase)
    (hke : genericParametrization F a ha ≫ eB = eA)
    {E H : OModule Y}
    (uB : (modelLine F a).sheaf ⟶ pullbackModule eB E)
    (vB : (modelLine F a).sheaf ⟶ pullbackModule eB H)
    (uA : pullbackModule (genericParametrization F a ha) (modelLine F a).sheaf ⟶
      pullbackModule eA E)
    (vA : pullbackModule (genericParametrization F a ha) (modelLine F a).sheaf ⟶
      pullbackModule eA H)
    (hu : (Scheme.Modules.pullback (genericParametrization F a ha)).map uB ≫
      (compositionPullback (genericParametrization F a ha) eB eA hke E).hom = uA)
    (hv : (Scheme.Modules.pullback (genericParametrization F a ha)).map vB ≫
      (compositionPullback (genericParametrization F a ha) eB eA hke H).hom = vA) :=
  numerator_target_operator_arguments F a ha sY eB heB eA heA hke uB vB uA vA hu hv
    (RelativeSquare.productSection (modelProjection F a) (ModelNumerator.coordinate F a 1 0 ≫ uB) (ModelNumerator.coordinate F a 0 1 ≫ vB) ≫ RelativeSquare.comparison (modelProjection F a) sY toC eB heB E H)
    (RelativeSquare.productSection (modelProjection F a) (ModelNumerator.coordinate F a 0 1 ≫ uB) (ModelNumerator.coordinate F a 1 0 ≫ vB) ≫ RelativeSquare.comparison (modelProjection F a) sY toC eB heB E H)
    (@CategoryStruct.comp (SheafOfModules (RelativeSquare.Space (modelProjection F a)).ringCatSheaf) _ (structureModule (RelativeSquare.Space (modelProjection F a))) _ _ (RelativeSquare.productSection (modelProjection F a) (ModelNumerator.coordinate F a 0 0 ≫ uB) (ModelNumerator.coordinate F a 0 0 ≫ vB)) (RelativeSquare.comparison (modelProjection F a) sY toC eB heB E H))
    (@HMul.hMul (↥((ModelNumerator.Square F a).presheaf.obj (@Opposite.op (ModelNumerator.Square F a).Opens (⊤ : (ModelNumerator.Square F a).Opens)))) (↥((ModelNumerator.Square F a).presheaf.obj (@Opposite.op (ModelNumerator.Square F a).Opens (⊤ : (ModelNumerator.Square F a).Opens)))) (RingSections (RelativeSquare.Space (modelProjection F a)) ⊤) _ 2 ((ModelNumerator.squareProjection F a).appTop (coefficientSection a)))



namespace NumeratorInputTransport

private theorem scheme_comp_heq
    {S S' : Scheme} (hS : S = S')
    (A B C : OModule S) (A' B' C' : OModule S')
    (hA : HEq A A') (hB : HEq B B') (hC : HEq C C')
    (f : A ⟶ B) (g : B ⟶ C) (f' : A' ⟶ B') (g' : B' ⟶ C')
    (hf : HEq f f') (hg : HEq g g') :
    HEq (f ≫ g) (f' ≫ g') := by
  cases hS
  have hA' : A = A' := eq_of_heq hA
  cases hA'
  have hB' : B = B' := eq_of_heq hB
  cases hB'
  have hC' : C = C' := eq_of_heq hC
  cases hC'
  have hf' : f = f' := eq_of_heq hf
  cases hf'
  have hg' : g = g' := eq_of_heq hg
  cases hg'
  rfl

private theorem input_comp
    (F : Smoothing.StandardSource) (a : Coefficients)
    {E H : OModule (RelativeSquare.Space (modelProjection F a))}
    (s : AlgebraicSection E) (u : E ⟶ H) :
    @Eq (AlgebraicSection H)
      (@CategoryStruct.comp
        (SheafOfModules (RelativeSquare.Space (modelProjection F a)).ringCatSheaf)
        _ (SheafOfModules.unit (RelativeSquare.Space (modelProjection F a)).ringCatSheaf)
        E H s u)
      (@CategoryStruct.comp
        (SheafOfModules (ModelNumerator.Square F a).ringCatSheaf)
        _ (SheafOfModules.unit (ModelNumerator.Square F a).ringCatSheaf)
        E H s u) := by
  rfl

private theorem product_comp
    (F : Smoothing.StandardSource) (a : Coefficients)
    {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (eB : Model F a ⟶ Y) (heB : eB ≫ sY = modelProjection F a ≫ toC)
    {E H : OModule Y}
    (s : AlgebraicSection (pullbackModule eB E))
    (t : AlgebraicSection (pullbackModule eB H)) :
    @Eq (AlgebraicSection
      (@pullbackModule (RelativeSquare.Space (modelProjection F a)) (SelfProduct sY)
        (RelativeSquare.evaluation (modelProjection F a) sY toC eB heB)
        (externalTensor sY E H)))
      (@CategoryStruct.comp
        (SheafOfModules (RelativeSquare.Space (modelProjection F a)).ringCatSheaf)
        _ (SheafOfModules.unit (RelativeSquare.Space (modelProjection F a)).ringCatSheaf)
        _ _ (RelativeSquare.productSection (modelProjection F a) s t)
        (RelativeSquare.comparison (modelProjection F a) sY toC eB heB E H))
      (@CategoryStruct.comp
        (SheafOfModules (ModelNumerator.Square F a).ringCatSheaf)
        _ (SheafOfModules.unit (ModelNumerator.Square F a).ringCatSheaf)
        _ _ (RelativeSquare.productSection (modelProjection F a) s t)
        (RelativeSquare.comparison (modelProjection F a) sY toC eB heB E H)) := by
  exact input_comp F a
    (RelativeSquare.productSection (modelProjection F a) s t)
    (RelativeSquare.comparison (modelProjection F a) sY toC eB heB E H)

private theorem pull_comp_input
    (F : Smoothing.StandardSource) (a : Coefficients)
    {T : Scheme} (q : T ⟶ ModelNumerator.Square F a)
    {E H : OModule (RelativeSquare.Space (modelProjection F a))}
    {G : OModule T} (v : pullbackModule q H ⟶ G)
    (s : AlgebraicSection E) (u : E ⟶ H) :
    pullSection q
      (@CategoryStruct.comp
        (SheafOfModules (RelativeSquare.Space (modelProjection F a)).ringCatSheaf)
        _ (SheafOfModules.unit (RelativeSquare.Space (modelProjection F a)).ringCatSheaf)
        E H s u) ≫ v =
    pullSection q
      (@CategoryStruct.comp
        (SheafOfModules (ModelNumerator.Square F a).ringCatSheaf)
        _ (SheafOfModules.unit (ModelNumerator.Square F a).ringCatSheaf)
        E H s u) ≫ v := by
  exact congrArg (fun w : AlgebraicSection H => pullSection q w ≫ v)
    (input_comp F a s u)

end NumeratorInputTransport


private theorem numerator_pull_input_literal
    (F : Smoothing.StandardSource) (a : Coefficients)
    {T : Scheme} (q : T ⟶ ModelNumerator.Square F a)
    {E H : OModule (RelativeSquare.Space (modelProjection F a))}
    {G : OModule T} (v : pullbackModule q H ⟶ G)
    (s : AlgebraicSection E) (u : E ⟶ H) :
    @Eq (@Quiver.Hom (SheafOfModules T.ringCatSheaf)
      (@CategoryStruct.toQuiver (SheafOfModules T.ringCatSheaf)
        (@Category.toCategoryStruct (SheafOfModules T.ringCatSheaf)
          SheafOfModules.instCategory))
      (SheafOfModules.unit T.ringCatSheaf) G)
    (@CategoryStruct.comp (SheafOfModules T.ringCatSheaf) _ _ _ _
      (@pullSection T (ModelNumerator.Square F a) q H
        (@CategoryStruct.comp
          (SheafOfModules (RelativeSquare.Space (modelProjection F a)).ringCatSheaf)
          _ (SheafOfModules.unit (RelativeSquare.Space (modelProjection F a)).ringCatSheaf)
          E H s u)) v)
    (@CategoryStruct.comp (SheafOfModules T.ringCatSheaf) _ _ _ _
      (@pullSection T (ModelNumerator.Square F a) q H
        (@CategoryStruct.comp
          (SheafOfModules (ModelNumerator.Square F a).ringCatSheaf)
          _ (SheafOfModules.unit (ModelNumerator.Square F a).ringCatSheaf)
          E H s u)) v) := by
  exact NumeratorInputTransport.pull_comp_input F a q v s u

private theorem numerator_input_from_structure
    {Z : Scheme} {E H : OModule Z}
    (s : AlgebraicSection E) (u : E ⟶ H) :
    @Eq (AlgebraicSection H)
      (@CategoryStruct.comp (SheafOfModules Z.ringCatSheaf) _
        (structureModule Z) E H s u)
      (@CategoryStruct.comp (SheafOfModules Z.ringCatSheaf) _
        (SheafOfModules.unit Z.ringCatSheaf) E H s u) := by
  rfl

private theorem numerator_pull_input_structure
    (F : Smoothing.StandardSource) (a : Coefficients)
    {T : Scheme} (q : T ⟶ ModelNumerator.Square F a)
    {E H : OModule (RelativeSquare.Space (modelProjection F a))}
    {G : OModule T} (v : pullbackModule q H ⟶ G)
    (s : AlgebraicSection E) (u : E ⟶ H) :
    @Eq (@Quiver.Hom (SheafOfModules T.ringCatSheaf)
      (@CategoryStruct.toQuiver (SheafOfModules T.ringCatSheaf)
        (@Category.toCategoryStruct (SheafOfModules T.ringCatSheaf)
          SheafOfModules.instCategory))
      (SheafOfModules.unit T.ringCatSheaf) G)
    (@CategoryStruct.comp (SheafOfModules T.ringCatSheaf) _ _ _ _
      (@pullSection T (ModelNumerator.Square F a) q H
        (@CategoryStruct.comp
          (SheafOfModules (RelativeSquare.Space (modelProjection F a)).ringCatSheaf)
          _ (structureModule (RelativeSquare.Space (modelProjection F a)))
          E H s u)) v)
    (@CategoryStruct.comp (SheafOfModules T.ringCatSheaf) _ _ _ _
      (@pullSection T (ModelNumerator.Square F a) q H
        (@CategoryStruct.comp
          (SheafOfModules (ModelNumerator.Square F a).ringCatSheaf)
          _ (SheafOfModules.unit (ModelNumerator.Square F a).ringCatSheaf)
          E H s u)) v) := by
  exact (congrArg
    (fun w : AlgebraicSection H =>
      @CategoryStruct.comp (SheafOfModules T.ringCatSheaf) _ _ _ _
        (@pullSection T (ModelNumerator.Square F a) q H w) v)
    (numerator_input_from_structure s u)).trans
      (numerator_pull_input_literal F a q v s u)

private theorem numerator_three_congr {B S : Type*}
    (add sub : B → B → B) (scale : S → B → B)
    {x x' y y' z z' : B} {r r' : S}
    (hx : x = x') (hy : y = y') (hz : z = z') (hr : r = r') :
    sub (add x y) (scale r z) = sub (add x' y') (scale r' z') := by
  cases hx
  cases hy
  cases hz
  cases hr
  rfl

private theorem numerator_named_scalar_value (ha : a ≠ 0) :
    @Eq ↥((Parametrized.Square Lines.P genericBase).presheaf.obj (@Opposite.op (Parametrized.Square Lines.P genericBase).Opens (⊤ : (Parametrized.Square Lines.P genericBase).Opens)))
      (numerator_named_coefficient (parametrizedToModelSquare F a ha) (@HMul.hMul (↥((ModelNumerator.Square F a).presheaf.obj (@Opposite.op (ModelNumerator.Square F a).Opens (⊤ : (ModelNumerator.Square F a).Opens)))) (↥((ModelNumerator.Square F a).presheaf.obj (@Opposite.op (ModelNumerator.Square F a).Opens (⊤ : (ModelNumerator.Square F a).Opens)))) (RingSections (RelativeSquare.Space (modelProjection F a)) ⊤) _ 2 ((ModelNumerator.squareProjection F a).appTop (coefficientSection a))))
      ((parametrizedToModelSquare F a ha).appTop (2 * (ModelNumerator.squareProjection F a).appTop (coefficientSection a))) := by
  rfl

private theorem numerator_distribution_rhs  (ha : a ≠ 0)
    {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (eB : Model F a ⟶ Y) (heB : eB ≫ sY = modelProjection F a ≫ toC)
    (eA : P1Generic ⟶ Y) (heA : eA ≫ sY = p1Parameter ≫ genericBase)
    (hke : genericParametrization F a ha ≫ eB = eA)
    {E H : OModule Y}
    (uB : (modelLine F a).sheaf ⟶ pullbackModule eB E)
    (vB : (modelLine F a).sheaf ⟶ pullbackModule eB H)
    (uA : pullbackModule (genericParametrization F a ha) (modelLine F a).sheaf ⟶
      pullbackModule eA E)
    (vA : pullbackModule (genericParametrization F a ha) (modelLine F a).sheaf ⟶
      pullbackModule eA H)
    (hu : (Scheme.Modules.pullback (genericParametrization F a ha)).map uB ≫
      (compositionPullback (genericParametrization F a ha) eB eA hke E).hom = uA)
    (hv : (Scheme.Modules.pullback (genericParametrization F a ha)).map vB ≫
      (compositionPullback (genericParametrization F a ha) eB eA hke H).hom = vA) :
    @Eq (@Quiver.Hom (SheafOfModules (Parametrized.Square Lines.P genericBase).ringCatSheaf) (@CategoryStruct.toQuiver (SheafOfModules (Parametrized.Square Lines.P genericBase).ringCatSheaf) (@Category.toCategoryStruct (SheafOfModules (Parametrized.Square Lines.P genericBase).ringCatSheaf) SheafOfModules.instCategory)) (SheafOfModules.unit (Parametrized.Square Lines.P genericBase).ringCatSheaf) (@pullbackModule (Parametrized.Square Lines.P genericBase) (SelfProduct sY) (RelativeSquare.evaluation p1Parameter sY genericBase eA heA) (externalTensor sY E H)))
      ((@CategoryStruct.comp (SheafOfModules (Parametrized.Square Lines.P genericBase).ringCatSheaf) _ (SheafOfModules.unit (Parametrized.Square Lines.P genericBase).ringCatSheaf) _ _ (@pullSection (Parametrized.Square Lines.P genericBase) (ModelNumerator.Square F a) (parametrizedToModelSquare F a ha) (@pullbackModule (RelativeSquare.Space (modelProjection F a)) (SelfProduct sY) (RelativeSquare.evaluation (modelProjection F a) sY toC eB heB) (externalTensor sY E H)) (@CategoryStruct.comp (SheafOfModules (RelativeSquare.Space (modelProjection F a)).ringCatSheaf) _ (SheafOfModules.unit (RelativeSquare.Space (modelProjection F a)).ringCatSheaf) _ _ (RelativeSquare.productSection (modelProjection F a) (ModelNumerator.coordinate F a 1 0 ≫ uB) (ModelNumerator.coordinate F a 0 1 ≫ vB)) (RelativeSquare.comparison (modelProjection F a) sY toC eB heB E H))) ((@compositionPullback (Parametrized.Square Lines.P genericBase) (ModelNumerator.Square F a) (SelfProduct sY) (parametrizedToModelSquare F a ha) (RelativeSquare.evaluation (modelProjection F a) sY toC eB heB) (RelativeSquare.evaluation p1Parameter sY genericBase eA heA)
        (RelativeSquare.map_evaluation p1Parameter (modelProjection F a)
          (genericParametrization F a ha) genericPoint
          (genericParametrization_parameter F a ha) sY genericBase toC
          eA eB heA heB hke) (externalTensor sY E H)).hom)) + (@CategoryStruct.comp (SheafOfModules (Parametrized.Square Lines.P genericBase).ringCatSheaf) _ (SheafOfModules.unit (Parametrized.Square Lines.P genericBase).ringCatSheaf) _ _ (@pullSection (Parametrized.Square Lines.P genericBase) (ModelNumerator.Square F a) (parametrizedToModelSquare F a ha) (@pullbackModule (RelativeSquare.Space (modelProjection F a)) (SelfProduct sY) (RelativeSquare.evaluation (modelProjection F a) sY toC eB heB) (externalTensor sY E H)) (@CategoryStruct.comp (SheafOfModules (RelativeSquare.Space (modelProjection F a)).ringCatSheaf) _ (SheafOfModules.unit (RelativeSquare.Space (modelProjection F a)).ringCatSheaf) _ _ (RelativeSquare.productSection (modelProjection F a) (ModelNumerator.coordinate F a 0 1 ≫ uB) (ModelNumerator.coordinate F a 1 0 ≫ vB)) (RelativeSquare.comparison (modelProjection F a) sY toC eB heB E H))) ((@compositionPullback (Parametrized.Square Lines.P genericBase) (ModelNumerator.Square F a) (SelfProduct sY) (parametrizedToModelSquare F a ha) (RelativeSquare.evaluation (modelProjection F a) sY toC eB heB) (RelativeSquare.evaluation p1Parameter sY genericBase eA heA)
        (RelativeSquare.map_evaluation p1Parameter (modelProjection F a)
          (genericParametrization F a ha) genericPoint
          (genericParametrization_parameter F a ha) sY genericBase toC
          eA eB heA heB hke) (externalTensor sY E H)).hom)) - (@CategoryStruct.comp (SheafOfModules (Parametrized.Square Lines.P genericBase).ringCatSheaf) _ _ _ _ (@scalarSection (Parametrized.Square Lines.P genericBase) (numerator_named_coefficient (parametrizedToModelSquare F a ha) (@HMul.hMul (↥((ModelNumerator.Square F a).presheaf.obj (@Opposite.op (ModelNumerator.Square F a).Opens (⊤ : (ModelNumerator.Square F a).Opens)))) (↥((ModelNumerator.Square F a).presheaf.obj (@Opposite.op (ModelNumerator.Square F a).Opens (⊤ : (ModelNumerator.Square F a).Opens)))) (RingSections (RelativeSquare.Space (modelProjection F a)) ⊤) _ 2 ((ModelNumerator.squareProjection F a).appTop (coefficientSection a))))) (@CategoryStruct.comp (SheafOfModules (Parametrized.Square Lines.P genericBase).ringCatSheaf) _ (SheafOfModules.unit (Parametrized.Square Lines.P genericBase).ringCatSheaf) _ _ (@pullSection (Parametrized.Square Lines.P genericBase) (ModelNumerator.Square F a) (parametrizedToModelSquare F a ha) (@pullbackModule (RelativeSquare.Space (modelProjection F a)) (SelfProduct sY) (RelativeSquare.evaluation (modelProjection F a) sY toC eB heB) (externalTensor sY E H)) (@CategoryStruct.comp (SheafOfModules (RelativeSquare.Space (modelProjection F a)).ringCatSheaf) _ (structureModule (RelativeSquare.Space (modelProjection F a))) _ _ (RelativeSquare.productSection (modelProjection F a) (ModelNumerator.coordinate F a 0 0 ≫ uB) (ModelNumerator.coordinate F a 0 0 ≫ vB)) (RelativeSquare.comparison (modelProjection F a) sY toC eB heB E H))) ((@compositionPullback (Parametrized.Square Lines.P genericBase) (ModelNumerator.Square F a) (SelfProduct sY) (parametrizedToModelSquare F a ha) (RelativeSquare.evaluation (modelProjection F a) sY toC eB heB) (RelativeSquare.evaluation p1Parameter sY genericBase eA heA)
        (RelativeSquare.map_evaluation p1Parameter (modelProjection F a)
          (genericParametrization F a ha) genericPoint
          (genericParametrization_parameter F a ha) sY genericBase toC
          eA eB heA heB hke) (externalTensor sY E H)).hom))))
      ((pullSection (parametrizedToModelSquare F a ha)
      (RelativeSquare.productSection (modelProjection F a) ((ModelNumerator.coordinate F a 1 0) ≫ uB) ((ModelNumerator.coordinate F a 0 1) ≫ vB) ≫
        RelativeSquare.comparison (modelProjection F a) sY toC eB heB E H) ≫
      (compositionPullback (parametrizedToModelSquare F a ha)
        (RelativeSquare.evaluation (modelProjection F a) sY toC eB heB)
        (RelativeSquare.evaluation p1Parameter sY genericBase eA heA)
        (RelativeSquare.map_evaluation p1Parameter (modelProjection F a)
          (genericParametrization F a ha) genericPoint
          (genericParametrization_parameter F a ha) sY genericBase toC
          eA eB heA heB hke) (externalTensor sY E H)).hom) +
      (pullSection (parametrizedToModelSquare F a ha)
      (RelativeSquare.productSection (modelProjection F a) ((ModelNumerator.coordinate F a 0 1) ≫ uB) ((ModelNumerator.coordinate F a 1 0) ≫ vB) ≫
        RelativeSquare.comparison (modelProjection F a) sY toC eB heB E H) ≫
      (compositionPullback (parametrizedToModelSquare F a ha)
        (RelativeSquare.evaluation (modelProjection F a) sY toC eB heB)
        (RelativeSquare.evaluation p1Parameter sY genericBase eA heA)
        (RelativeSquare.map_evaluation p1Parameter (modelProjection F a)
          (genericParametrization F a ha) genericPoint
          (genericParametrization_parameter F a ha) sY genericBase toC
          eA eB heA heB hke) (externalTensor sY E H)).hom) -
      scalarSection ((parametrizedToModelSquare F a ha).appTop
      (2 * (ModelNumerator.squareProjection F a).appTop (coefficientSection a))) ≫
        (pullSection (parametrizedToModelSquare F a ha)
      (RelativeSquare.productSection (modelProjection F a) ((ModelNumerator.coordinate F a 0 0) ≫ uB) ((ModelNumerator.coordinate F a 0 0) ≫ vB) ≫
        RelativeSquare.comparison (modelProjection F a) sY toC eB heB E H) ≫
      (compositionPullback (parametrizedToModelSquare F a ha)
        (RelativeSquare.evaluation (modelProjection F a) sY toC eB heB)
        (RelativeSquare.evaluation p1Parameter sY genericBase eA heA)
        (RelativeSquare.map_evaluation p1Parameter (modelProjection F a)
          (genericParametrization F a ha) genericPoint
          (genericParametrization_parameter F a ha) sY genericBase toC
          eA eB heA heB hke) (externalTensor sY E H)).hom)) := by
  exact numerator_three_congr
    (fun x y : (@Quiver.Hom (SheafOfModules (Parametrized.Square Lines.P genericBase).ringCatSheaf) (@CategoryStruct.toQuiver (SheafOfModules (Parametrized.Square Lines.P genericBase).ringCatSheaf) (@Category.toCategoryStruct (SheafOfModules (Parametrized.Square Lines.P genericBase).ringCatSheaf) SheafOfModules.instCategory)) (SheafOfModules.unit (Parametrized.Square Lines.P genericBase).ringCatSheaf) (@pullbackModule (Parametrized.Square Lines.P genericBase) (SelfProduct sY) (RelativeSquare.evaluation p1Parameter sY genericBase eA heA) (externalTensor sY E H))) => x + y)
    (fun x y : (@Quiver.Hom (SheafOfModules (Parametrized.Square Lines.P genericBase).ringCatSheaf) (@CategoryStruct.toQuiver (SheafOfModules (Parametrized.Square Lines.P genericBase).ringCatSheaf) (@Category.toCategoryStruct (SheafOfModules (Parametrized.Square Lines.P genericBase).ringCatSheaf) SheafOfModules.instCategory)) (SheafOfModules.unit (Parametrized.Square Lines.P genericBase).ringCatSheaf) (@pullbackModule (Parametrized.Square Lines.P genericBase) (SelfProduct sY) (RelativeSquare.evaluation p1Parameter sY genericBase eA heA) (externalTensor sY E H))) => x - y)
    (fun r : ↥((Parametrized.Square Lines.P genericBase).presheaf.obj (@Opposite.op (Parametrized.Square Lines.P genericBase).Opens (⊤ : (Parametrized.Square Lines.P genericBase).Opens))) => fun x : (@Quiver.Hom (SheafOfModules (Parametrized.Square Lines.P genericBase).ringCatSheaf) (@CategoryStruct.toQuiver (SheafOfModules (Parametrized.Square Lines.P genericBase).ringCatSheaf) (@Category.toCategoryStruct (SheafOfModules (Parametrized.Square Lines.P genericBase).ringCatSheaf) SheafOfModules.instCategory)) (SheafOfModules.unit (Parametrized.Square Lines.P genericBase).ringCatSheaf) (@pullbackModule (Parametrized.Square Lines.P genericBase) (SelfProduct sY) (RelativeSquare.evaluation p1Parameter sY genericBase eA heA) (externalTensor sY E H))) =>
      @CategoryStruct.comp (SheafOfModules (Parametrized.Square Lines.P genericBase).ringCatSheaf) _ _ _ _
        (@scalarSection (Parametrized.Square Lines.P genericBase) r) x)
    (numerator_pull_input_literal F a (T := (Parametrized.Square Lines.P genericBase)) (parametrizedToModelSquare F a ha)
      (H := (@pullbackModule (RelativeSquare.Space (modelProjection F a)) (SelfProduct sY) (RelativeSquare.evaluation (modelProjection F a) sY toC eB heB) (externalTensor sY E H))) (G := (@pullbackModule (Parametrized.Square Lines.P genericBase) (SelfProduct sY) (RelativeSquare.evaluation p1Parameter sY genericBase eA heA) (externalTensor sY E H))) ((@compositionPullback (Parametrized.Square Lines.P genericBase) (ModelNumerator.Square F a) (SelfProduct sY) (parametrizedToModelSquare F a ha) (RelativeSquare.evaluation (modelProjection F a) sY toC eB heB) (RelativeSquare.evaluation p1Parameter sY genericBase eA heA)
        (RelativeSquare.map_evaluation p1Parameter (modelProjection F a)
          (genericParametrization F a ha) genericPoint
          (genericParametrization_parameter F a ha) sY genericBase toC
          eA eB heA heB hke) (externalTensor sY E H)).hom) (RelativeSquare.productSection (modelProjection F a) (ModelNumerator.coordinate F a 1 0 ≫ uB) (ModelNumerator.coordinate F a 0 1 ≫ vB)) (RelativeSquare.comparison (modelProjection F a) sY toC eB heB E H))
    (numerator_pull_input_literal F a (T := (Parametrized.Square Lines.P genericBase)) (parametrizedToModelSquare F a ha)
      (H := (@pullbackModule (RelativeSquare.Space (modelProjection F a)) (SelfProduct sY) (RelativeSquare.evaluation (modelProjection F a) sY toC eB heB) (externalTensor sY E H))) (G := (@pullbackModule (Parametrized.Square Lines.P genericBase) (SelfProduct sY) (RelativeSquare.evaluation p1Parameter sY genericBase eA heA) (externalTensor sY E H))) ((@compositionPullback (Parametrized.Square Lines.P genericBase) (ModelNumerator.Square F a) (SelfProduct sY) (parametrizedToModelSquare F a ha) (RelativeSquare.evaluation (modelProjection F a) sY toC eB heB) (RelativeSquare.evaluation p1Parameter sY genericBase eA heA)
        (RelativeSquare.map_evaluation p1Parameter (modelProjection F a)
          (genericParametrization F a ha) genericPoint
          (genericParametrization_parameter F a ha) sY genericBase toC
          eA eB heA heB hke) (externalTensor sY E H)).hom) (RelativeSquare.productSection (modelProjection F a) (ModelNumerator.coordinate F a 0 1 ≫ uB) (ModelNumerator.coordinate F a 1 0 ≫ vB)) (RelativeSquare.comparison (modelProjection F a) sY toC eB heB E H))
    (numerator_pull_input_structure F a (T := (Parametrized.Square Lines.P genericBase)) (parametrizedToModelSquare F a ha)
      (H := (@pullbackModule (RelativeSquare.Space (modelProjection F a)) (SelfProduct sY) (RelativeSquare.evaluation (modelProjection F a) sY toC eB heB) (externalTensor sY E H))) (G := (@pullbackModule (Parametrized.Square Lines.P genericBase) (SelfProduct sY) (RelativeSquare.evaluation p1Parameter sY genericBase eA heA) (externalTensor sY E H))) ((@compositionPullback (Parametrized.Square Lines.P genericBase) (ModelNumerator.Square F a) (SelfProduct sY) (parametrizedToModelSquare F a ha) (RelativeSquare.evaluation (modelProjection F a) sY toC eB heB) (RelativeSquare.evaluation p1Parameter sY genericBase eA heA)
        (RelativeSquare.map_evaluation p1Parameter (modelProjection F a)
          (genericParametrization F a ha) genericPoint
          (genericParametrization_parameter F a ha) sY genericBase toC
          eA eB heA heB hke) (externalTensor sY E H)).hom) (RelativeSquare.productSection (modelProjection F a) (ModelNumerator.coordinate F a 0 0 ≫ uB) (ModelNumerator.coordinate F a 0 0 ≫ vB)) (RelativeSquare.comparison (modelProjection F a) sY toC eB heB E H))
    (numerator_named_scalar_value F a ha)

private theorem numerator_source_distribution (ha : a ≠ 0)
    {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (eB : Model F a ⟶ Y) (heB : eB ≫ sY = modelProjection F a ≫ toC)
    (eA : P1Generic ⟶ Y) (heA : eA ≫ sY = p1Parameter ≫ genericBase)
    (hke : genericParametrization F a ha ≫ eB = eA)
    {E H : OModule Y}
    (uB : (modelLine F a).sheaf ⟶ pullbackModule eB E)
    (vB : (modelLine F a).sheaf ⟶ pullbackModule eB H)
    (uA : pullbackModule (genericParametrization F a ha) (modelLine F a).sheaf ⟶
      pullbackModule eA E)
    (vA : pullbackModule (genericParametrization F a ha) (modelLine F a).sheaf ⟶
      pullbackModule eA H)
    (hu : (Scheme.Modules.pullback (genericParametrization F a ha)).map uB ≫
      (compositionPullback (genericParametrization F a ha) eB eA hke E).hom = uA)
    (hv : (Scheme.Modules.pullback (genericParametrization F a ha)).map vB ≫
      (compositionPullback (genericParametrization F a ha) eB eA hke H).hom = vA) :
    pullSection (parametrizedToModelSquare F a ha)
      ((RelativeSquare.productSection (modelProjection F a) (ModelNumerator.coordinate F a 1 0 ≫ uB) (ModelNumerator.coordinate F a 0 1 ≫ vB) ≫
        RelativeSquare.comparison (modelProjection F a) sY toC eB heB E H) + (RelativeSquare.productSection (modelProjection F a) (ModelNumerator.coordinate F a 0 1 ≫ uB) (ModelNumerator.coordinate F a 1 0 ≫ vB) ≫
        RelativeSquare.comparison (modelProjection F a) sY toC eB heB E H) - scalarSection (2 * (ModelNumerator.squareProjection F a).appTop (coefficientSection a)) ≫ (RelativeSquare.productSection (modelProjection F a) (ModelNumerator.coordinate F a 0 0 ≫ uB) (ModelNumerator.coordinate F a 0 0 ≫ vB) ≫
        RelativeSquare.comparison (modelProjection F a) sY toC eB heB E H)) ≫
      (compositionPullback (parametrizedToModelSquare F a ha)
        (RelativeSquare.evaluation (modelProjection F a) sY toC eB heB)
        (RelativeSquare.evaluation p1Parameter sY genericBase eA heA)
        (RelativeSquare.map_evaluation p1Parameter (modelProjection F a)
          (genericParametrization F a ha) genericPoint
          (genericParametrization_parameter F a ha) sY genericBase toC
          eA eB heA heB hke) (externalTensor sY E H)).hom =
      (pullSection (parametrizedToModelSquare F a ha)
      (RelativeSquare.productSection (modelProjection F a) ((ModelNumerator.coordinate F a 1 0) ≫ uB) ((ModelNumerator.coordinate F a 0 1) ≫ vB) ≫
        RelativeSquare.comparison (modelProjection F a) sY toC eB heB E H) ≫
      (compositionPullback (parametrizedToModelSquare F a ha)
        (RelativeSquare.evaluation (modelProjection F a) sY toC eB heB)
        (RelativeSquare.evaluation p1Parameter sY genericBase eA heA)
        (RelativeSquare.map_evaluation p1Parameter (modelProjection F a)
          (genericParametrization F a ha) genericPoint
          (genericParametrization_parameter F a ha) sY genericBase toC
          eA eB heA heB hke) (externalTensor sY E H)).hom) +
      (pullSection (parametrizedToModelSquare F a ha)
      (RelativeSquare.productSection (modelProjection F a) ((ModelNumerator.coordinate F a 0 1) ≫ uB) ((ModelNumerator.coordinate F a 1 0) ≫ vB) ≫
        RelativeSquare.comparison (modelProjection F a) sY toC eB heB E H) ≫
      (compositionPullback (parametrizedToModelSquare F a ha)
        (RelativeSquare.evaluation (modelProjection F a) sY toC eB heB)
        (RelativeSquare.evaluation p1Parameter sY genericBase eA heA)
        (RelativeSquare.map_evaluation p1Parameter (modelProjection F a)
          (genericParametrization F a ha) genericPoint
          (genericParametrization_parameter F a ha) sY genericBase toC
          eA eB heA heB hke) (externalTensor sY E H)).hom) -
      scalarSection ((parametrizedToModelSquare F a ha).appTop
      (2 * (ModelNumerator.squareProjection F a).appTop (coefficientSection a))) ≫
        (pullSection (parametrizedToModelSquare F a ha)
      (RelativeSquare.productSection (modelProjection F a) ((ModelNumerator.coordinate F a 0 0) ≫ uB) ((ModelNumerator.coordinate F a 0 0) ≫ vB) ≫
        RelativeSquare.comparison (modelProjection F a) sY toC eB heB E H) ≫
      (compositionPullback (parametrizedToModelSquare F a ha)
        (RelativeSquare.evaluation (modelProjection F a) sY toC eB heB)
        (RelativeSquare.evaluation p1Parameter sY genericBase eA heA)
        (RelativeSquare.map_evaluation p1Parameter (modelProjection F a)
          (genericParametrization F a ha) genericPoint
          (genericParametrization_parameter F a ha) sY genericBase toC
          eA eB heA heB hke) (externalTensor sY E H)).hom) := by
  exact (numerator_target_value_arguments F a ha sY eB heB eA heA hke uB vB uA vA hu hv).trans
    (numerator_distribution_rhs F a ha sY eB heB eA heA hke uB vB uA vA hu hv)

private theorem numerator_expanded_source (ha : a ≠ 0)
    {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (eB : Model F a ⟶ Y) (heB : eB ≫ sY = modelProjection F a ≫ toC)
    (eA : P1Generic ⟶ Y) (heA : eA ≫ sY = p1Parameter ≫ genericBase)
    (hke : genericParametrization F a ha ≫ eB = eA)
    {E H : OModule Y}
    (uB : (modelLine F a).sheaf ⟶ pullbackModule eB E)
    (vB : (modelLine F a).sheaf ⟶ pullbackModule eB H)
    (uA : pullbackModule (genericParametrization F a ha) (modelLine F a).sheaf ⟶
      pullbackModule eA E)
    (vA : pullbackModule (genericParametrization F a ha) (modelLine F a).sheaf ⟶
      pullbackModule eA H)
    (hu : (Scheme.Modules.pullback (genericParametrization F a ha)).map uB ≫
      (compositionPullback (genericParametrization F a ha) eB eA hke E).hom = uA)
    (hv : (Scheme.Modules.pullback (genericParametrization F a ha)).map vB ≫
      (compositionPullback (genericParametrization F a ha) eB eA hke H).hom = vA) :
    pullSection (parametrizedToModelSquare F a ha)
      (ModelNumerator.numerator F a ≫
        RelativeSquare.boxMap (modelProjection F a) uB vB ≫
          RelativeSquare.comparison (modelProjection F a) sY toC eB heB E H) ≫
      (compositionPullback (parametrizedToModelSquare F a ha)
        (RelativeSquare.evaluation (modelProjection F a) sY toC eB heB)
        (RelativeSquare.evaluation p1Parameter sY genericBase eA heA)
        (RelativeSquare.map_evaluation p1Parameter (modelProjection F a)
          (genericParametrization F a ha) genericPoint
          (genericParametrization_parameter F a ha) sY genericBase toC
          eA eB heA heB hke) (externalTensor sY E H)).hom =
      (pullSection (parametrizedToModelSquare F a ha)
      (RelativeSquare.productSection (modelProjection F a) ((ModelNumerator.coordinate F a 1 0) ≫ uB) ((ModelNumerator.coordinate F a 0 1) ≫ vB) ≫
        RelativeSquare.comparison (modelProjection F a) sY toC eB heB E H) ≫
      (compositionPullback (parametrizedToModelSquare F a ha)
        (RelativeSquare.evaluation (modelProjection F a) sY toC eB heB)
        (RelativeSquare.evaluation p1Parameter sY genericBase eA heA)
        (RelativeSquare.map_evaluation p1Parameter (modelProjection F a)
          (genericParametrization F a ha) genericPoint
          (genericParametrization_parameter F a ha) sY genericBase toC
          eA eB heA heB hke) (externalTensor sY E H)).hom) +
      (pullSection (parametrizedToModelSquare F a ha)
      (RelativeSquare.productSection (modelProjection F a) ((ModelNumerator.coordinate F a 0 1) ≫ uB) ((ModelNumerator.coordinate F a 1 0) ≫ vB) ≫
        RelativeSquare.comparison (modelProjection F a) sY toC eB heB E H) ≫
      (compositionPullback (parametrizedToModelSquare F a ha)
        (RelativeSquare.evaluation (modelProjection F a) sY toC eB heB)
        (RelativeSquare.evaluation p1Parameter sY genericBase eA heA)
        (RelativeSquare.map_evaluation p1Parameter (modelProjection F a)
          (genericParametrization F a ha) genericPoint
          (genericParametrization_parameter F a ha) sY genericBase toC
          eA eB heA heB hke) (externalTensor sY E H)).hom) -
      scalarSection ((parametrizedToModelSquare F a ha).appTop
      (2 * (ModelNumerator.squareProjection F a).appTop (coefficientSection a))) ≫
        (pullSection (parametrizedToModelSquare F a ha)
      (RelativeSquare.productSection (modelProjection F a) ((ModelNumerator.coordinate F a 0 0) ≫ uB) ((ModelNumerator.coordinate F a 0 0) ≫ vB) ≫
        RelativeSquare.comparison (modelProjection F a) sY toC eB heB E H) ≫
      (compositionPullback (parametrizedToModelSquare F a ha)
        (RelativeSquare.evaluation (modelProjection F a) sY toC eB heB)
        (RelativeSquare.evaluation p1Parameter sY genericBase eA heA)
        (RelativeSquare.map_evaluation p1Parameter (modelProjection F a)
          (genericParametrization F a ha) genericPoint
          (genericParametrization_parameter F a ha) sY genericBase toC
          eA eB heA heB hke) (externalTensor sY E H)).hom) := by
  exact (numerator_source_pulled_formula F a ha sY eB heB eA heA hke uB vB uA vA hu hv).trans
    (numerator_source_distribution F a ha sY eB heB eA heA hke uB vB uA vA hu hv)

private theorem numerator_expanded_target (ha : a ≠ 0)
    {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (eB : Model F a ⟶ Y) (heB : eB ≫ sY = modelProjection F a ≫ toC)
    (eA : P1Generic ⟶ Y) (heA : eA ≫ sY = p1Parameter ≫ genericBase)
    (hke : genericParametrization F a ha ≫ eB = eA)
    {E H : OModule Y}
    (uB : (modelLine F a).sheaf ⟶ pullbackModule eB E)
    (vB : (modelLine F a).sheaf ⟶ pullbackModule eB H)
    (uA : pullbackModule (genericParametrization F a ha) (modelLine F a).sheaf ⟶
      pullbackModule eA E)
    (vA : pullbackModule (genericParametrization F a ha) (modelLine F a).sheaf ⟶
      pullbackModule eA H)
    (hu : (Scheme.Modules.pullback (genericParametrization F a ha)).map uB ≫
      (compositionPullback (genericParametrization F a ha) eB eA hke E).hom = uA)
    (hv : (Scheme.Modules.pullback (genericParametrization F a ha)).map vB ≫
      (compositionPullback (genericParametrization F a ha) eB eA hke H).hom = vA) :
    genericNumerator F a ha ≫ RelativeSquare.boxMap p1Parameter uA vA ≫
        RelativeSquare.comparison p1Parameter sY genericBase eA heA E H =
      (RelativeSquare.productSection p1Parameter
      (pullSection (genericParametrization F a ha) (ModelNumerator.coordinate F a 1 0) ≫ uA) (pullSection (genericParametrization F a ha) (ModelNumerator.coordinate F a 0 1) ≫ vA) ≫
      RelativeSquare.comparison p1Parameter sY genericBase eA heA E H) +
      (RelativeSquare.productSection p1Parameter
      (pullSection (genericParametrization F a ha) (ModelNumerator.coordinate F a 0 1) ≫ uA) (pullSection (genericParametrization F a ha) (ModelNumerator.coordinate F a 1 0) ≫ vA) ≫
      RelativeSquare.comparison p1Parameter sY genericBase eA heA E H) -
      scalarSection (2 * genericCoefficient F a ha) ≫
        (RelativeSquare.productSection p1Parameter
      (pullSection (genericParametrization F a ha) (ModelNumerator.coordinate F a 0 0) ≫ uA) (pullSection (genericParametrization F a ha) (ModelNumerator.coordinate F a 0 0) ≫ vA) ≫
      RelativeSquare.comparison p1Parameter sY genericBase eA heA E H) := by
  unfold genericNumerator
  simp only [genericCoordinate, Preadditive.add_comp, Preadditive.sub_comp,
    Category.assoc, RelativeSquare.productSection_map_assoc]

private theorem numerator_product_10_transport  (ha : a ≠ 0)
    {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (eB : Model F a ⟶ Y) (heB : eB ≫ sY = modelProjection F a ≫ toC)
    (eA : P1Generic ⟶ Y) (heA : eA ≫ sY = p1Parameter ≫ genericBase)
    (hke : genericParametrization F a ha ≫ eB = eA)
    {E H : OModule Y}
    (uB : (modelLine F a).sheaf ⟶ pullbackModule eB E)
    (vB : (modelLine F a).sheaf ⟶ pullbackModule eB H)
    (uA : pullbackModule (genericParametrization F a ha) (modelLine F a).sheaf ⟶
      pullbackModule eA E)
    (vA : pullbackModule (genericParametrization F a ha) (modelLine F a).sheaf ⟶
      pullbackModule eA H)
    (hu : (Scheme.Modules.pullback (genericParametrization F a ha)).map uB ≫
      (compositionPullback (genericParametrization F a ha) eB eA hke E).hom = uA)
    (hv : (Scheme.Modules.pullback (genericParametrization F a ha)).map vB ≫
      (compositionPullback (genericParametrization F a ha) eB eA hke H).hom = vA) :
    @Eq (@Quiver.Hom (SheafOfModules (Parametrized.Square Lines.P genericBase).ringCatSheaf) (@CategoryStruct.toQuiver (SheafOfModules (Parametrized.Square Lines.P genericBase).ringCatSheaf) (@Category.toCategoryStruct (SheafOfModules (Parametrized.Square Lines.P genericBase).ringCatSheaf) SheafOfModules.instCategory)) (SheafOfModules.unit (Parametrized.Square Lines.P genericBase).ringCatSheaf) (@pullbackModule (Parametrized.Square Lines.P genericBase) (SelfProduct sY) (RelativeSquare.evaluation p1Parameter sY genericBase eA heA) (externalTensor sY E H)))
      (pullSection (parametrizedToModelSquare F a ha)
      (RelativeSquare.productSection (modelProjection F a) ((ModelNumerator.coordinate F a 1 0) ≫ uB) ((ModelNumerator.coordinate F a 0 1) ≫ vB) ≫
        RelativeSquare.comparison (modelProjection F a) sY toC eB heB E H) ≫
      (compositionPullback (parametrizedToModelSquare F a ha)
        (RelativeSquare.evaluation (modelProjection F a) sY toC eB heB)
        (RelativeSquare.evaluation p1Parameter sY genericBase eA heA)
        (RelativeSquare.map_evaluation p1Parameter (modelProjection F a)
          (genericParametrization F a ha) genericPoint
          (genericParametrization_parameter F a ha) sY genericBase toC
          eA eB heA heB hke) (externalTensor sY E H)).hom)
      (RelativeSquare.productSection p1Parameter
      (pullSection (genericParametrization F a ha) (ModelNumerator.coordinate F a 1 0) ≫ uA) (pullSection (genericParametrization F a ha) (ModelNumerator.coordinate F a 0 1) ≫ vA) ≫
      RelativeSquare.comparison p1Parameter sY genericBase eA heA E H) := by
  exact numerator_product_transport F a ha sY eB heB eA heA hke uB vB uA vA hu hv (ModelNumerator.coordinate F a 1 0) (ModelNumerator.coordinate F a 0 1)

private theorem numerator_product_01_transport  (ha : a ≠ 0)
    {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (eB : Model F a ⟶ Y) (heB : eB ≫ sY = modelProjection F a ≫ toC)
    (eA : P1Generic ⟶ Y) (heA : eA ≫ sY = p1Parameter ≫ genericBase)
    (hke : genericParametrization F a ha ≫ eB = eA)
    {E H : OModule Y}
    (uB : (modelLine F a).sheaf ⟶ pullbackModule eB E)
    (vB : (modelLine F a).sheaf ⟶ pullbackModule eB H)
    (uA : pullbackModule (genericParametrization F a ha) (modelLine F a).sheaf ⟶
      pullbackModule eA E)
    (vA : pullbackModule (genericParametrization F a ha) (modelLine F a).sheaf ⟶
      pullbackModule eA H)
    (hu : (Scheme.Modules.pullback (genericParametrization F a ha)).map uB ≫
      (compositionPullback (genericParametrization F a ha) eB eA hke E).hom = uA)
    (hv : (Scheme.Modules.pullback (genericParametrization F a ha)).map vB ≫
      (compositionPullback (genericParametrization F a ha) eB eA hke H).hom = vA) :
    @Eq (@Quiver.Hom (SheafOfModules (Parametrized.Square Lines.P genericBase).ringCatSheaf) (@CategoryStruct.toQuiver (SheafOfModules (Parametrized.Square Lines.P genericBase).ringCatSheaf) (@Category.toCategoryStruct (SheafOfModules (Parametrized.Square Lines.P genericBase).ringCatSheaf) SheafOfModules.instCategory)) (SheafOfModules.unit (Parametrized.Square Lines.P genericBase).ringCatSheaf) (@pullbackModule (Parametrized.Square Lines.P genericBase) (SelfProduct sY) (RelativeSquare.evaluation p1Parameter sY genericBase eA heA) (externalTensor sY E H)))
      (pullSection (parametrizedToModelSquare F a ha)
      (RelativeSquare.productSection (modelProjection F a) ((ModelNumerator.coordinate F a 0 1) ≫ uB) ((ModelNumerator.coordinate F a 1 0) ≫ vB) ≫
        RelativeSquare.comparison (modelProjection F a) sY toC eB heB E H) ≫
      (compositionPullback (parametrizedToModelSquare F a ha)
        (RelativeSquare.evaluation (modelProjection F a) sY toC eB heB)
        (RelativeSquare.evaluation p1Parameter sY genericBase eA heA)
        (RelativeSquare.map_evaluation p1Parameter (modelProjection F a)
          (genericParametrization F a ha) genericPoint
          (genericParametrization_parameter F a ha) sY genericBase toC
          eA eB heA heB hke) (externalTensor sY E H)).hom)
      (RelativeSquare.productSection p1Parameter
      (pullSection (genericParametrization F a ha) (ModelNumerator.coordinate F a 0 1) ≫ uA) (pullSection (genericParametrization F a ha) (ModelNumerator.coordinate F a 1 0) ≫ vA) ≫
      RelativeSquare.comparison p1Parameter sY genericBase eA heA E H) := by
  exact numerator_product_transport F a ha sY eB heB eA heA hke uB vB uA vA hu hv (ModelNumerator.coordinate F a 0 1) (ModelNumerator.coordinate F a 1 0)

private theorem numerator_product_00_transport  (ha : a ≠ 0)
    {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (eB : Model F a ⟶ Y) (heB : eB ≫ sY = modelProjection F a ≫ toC)
    (eA : P1Generic ⟶ Y) (heA : eA ≫ sY = p1Parameter ≫ genericBase)
    (hke : genericParametrization F a ha ≫ eB = eA)
    {E H : OModule Y}
    (uB : (modelLine F a).sheaf ⟶ pullbackModule eB E)
    (vB : (modelLine F a).sheaf ⟶ pullbackModule eB H)
    (uA : pullbackModule (genericParametrization F a ha) (modelLine F a).sheaf ⟶
      pullbackModule eA E)
    (vA : pullbackModule (genericParametrization F a ha) (modelLine F a).sheaf ⟶
      pullbackModule eA H)
    (hu : (Scheme.Modules.pullback (genericParametrization F a ha)).map uB ≫
      (compositionPullback (genericParametrization F a ha) eB eA hke E).hom = uA)
    (hv : (Scheme.Modules.pullback (genericParametrization F a ha)).map vB ≫
      (compositionPullback (genericParametrization F a ha) eB eA hke H).hom = vA) :
    @Eq (@Quiver.Hom (SheafOfModules (Parametrized.Square Lines.P genericBase).ringCatSheaf) (@CategoryStruct.toQuiver (SheafOfModules (Parametrized.Square Lines.P genericBase).ringCatSheaf) (@Category.toCategoryStruct (SheafOfModules (Parametrized.Square Lines.P genericBase).ringCatSheaf) SheafOfModules.instCategory)) (SheafOfModules.unit (Parametrized.Square Lines.P genericBase).ringCatSheaf) (@pullbackModule (Parametrized.Square Lines.P genericBase) (SelfProduct sY) (RelativeSquare.evaluation p1Parameter sY genericBase eA heA) (externalTensor sY E H)))
      (pullSection (parametrizedToModelSquare F a ha)
      (RelativeSquare.productSection (modelProjection F a) ((ModelNumerator.coordinate F a 0 0) ≫ uB) ((ModelNumerator.coordinate F a 0 0) ≫ vB) ≫
        RelativeSquare.comparison (modelProjection F a) sY toC eB heB E H) ≫
      (compositionPullback (parametrizedToModelSquare F a ha)
        (RelativeSquare.evaluation (modelProjection F a) sY toC eB heB)
        (RelativeSquare.evaluation p1Parameter sY genericBase eA heA)
        (RelativeSquare.map_evaluation p1Parameter (modelProjection F a)
          (genericParametrization F a ha) genericPoint
          (genericParametrization_parameter F a ha) sY genericBase toC
          eA eB heA heB hke) (externalTensor sY E H)).hom)
      (RelativeSquare.productSection p1Parameter
      (pullSection (genericParametrization F a ha) (ModelNumerator.coordinate F a 0 0) ≫ uA) (pullSection (genericParametrization F a ha) (ModelNumerator.coordinate F a 0 0) ≫ vA) ≫
      RelativeSquare.comparison p1Parameter sY genericBase eA heA E H) := by
  exact numerator_product_transport F a ha sY eB heB eA heA hke uB vB uA vA hu hv (ModelNumerator.coordinate F a 0 0) (ModelNumerator.coordinate F a 0 0)

private theorem numerator_coefficient_literal (ha : a ≠ 0) :
    @Eq ↥((Parametrized.Square Lines.P genericBase).presheaf.obj (@Opposite.op (Parametrized.Square Lines.P genericBase).Opens (⊤ : (Parametrized.Square Lines.P genericBase).Opens)))
      ((parametrizedToModelSquare F a ha).appTop
        (2 * (ModelNumerator.squareProjection F a).appTop (coefficientSection a)))
      (2 * genericCoefficient F a ha) := by
  exact numerator_coefficient_transport F a ha

private theorem numerator_expanded_transport (ha : a ≠ 0)
    {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (eB : Model F a ⟶ Y) (heB : eB ≫ sY = modelProjection F a ≫ toC)
    (eA : P1Generic ⟶ Y) (heA : eA ≫ sY = p1Parameter ≫ genericBase)
    (hke : genericParametrization F a ha ≫ eB = eA)
    {E H : OModule Y}
    (uB : (modelLine F a).sheaf ⟶ pullbackModule eB E)
    (vB : (modelLine F a).sheaf ⟶ pullbackModule eB H)
    (uA : pullbackModule (genericParametrization F a ha) (modelLine F a).sheaf ⟶
      pullbackModule eA E)
    (vA : pullbackModule (genericParametrization F a ha) (modelLine F a).sheaf ⟶
      pullbackModule eA H)
    (hu : (Scheme.Modules.pullback (genericParametrization F a ha)).map uB ≫
      (compositionPullback (genericParametrization F a ha) eB eA hke E).hom = uA)
    (hv : (Scheme.Modules.pullback (genericParametrization F a ha)).map vB ≫
      (compositionPullback (genericParametrization F a ha) eB eA hke H).hom = vA) :
    (pullSection (parametrizedToModelSquare F a ha)
      (RelativeSquare.productSection (modelProjection F a) ((ModelNumerator.coordinate F a 1 0) ≫ uB) ((ModelNumerator.coordinate F a 0 1) ≫ vB) ≫
        RelativeSquare.comparison (modelProjection F a) sY toC eB heB E H) ≫
      (compositionPullback (parametrizedToModelSquare F a ha)
        (RelativeSquare.evaluation (modelProjection F a) sY toC eB heB)
        (RelativeSquare.evaluation p1Parameter sY genericBase eA heA)
        (RelativeSquare.map_evaluation p1Parameter (modelProjection F a)
          (genericParametrization F a ha) genericPoint
          (genericParametrization_parameter F a ha) sY genericBase toC
          eA eB heA heB hke) (externalTensor sY E H)).hom) +
      (pullSection (parametrizedToModelSquare F a ha)
      (RelativeSquare.productSection (modelProjection F a) ((ModelNumerator.coordinate F a 0 1) ≫ uB) ((ModelNumerator.coordinate F a 1 0) ≫ vB) ≫
        RelativeSquare.comparison (modelProjection F a) sY toC eB heB E H) ≫
      (compositionPullback (parametrizedToModelSquare F a ha)
        (RelativeSquare.evaluation (modelProjection F a) sY toC eB heB)
        (RelativeSquare.evaluation p1Parameter sY genericBase eA heA)
        (RelativeSquare.map_evaluation p1Parameter (modelProjection F a)
          (genericParametrization F a ha) genericPoint
          (genericParametrization_parameter F a ha) sY genericBase toC
          eA eB heA heB hke) (externalTensor sY E H)).hom) -
      scalarSection ((parametrizedToModelSquare F a ha).appTop
      (2 * (ModelNumerator.squareProjection F a).appTop (coefficientSection a))) ≫
        (pullSection (parametrizedToModelSquare F a ha)
      (RelativeSquare.productSection (modelProjection F a) ((ModelNumerator.coordinate F a 0 0) ≫ uB) ((ModelNumerator.coordinate F a 0 0) ≫ vB) ≫
        RelativeSquare.comparison (modelProjection F a) sY toC eB heB E H) ≫
      (compositionPullback (parametrizedToModelSquare F a ha)
        (RelativeSquare.evaluation (modelProjection F a) sY toC eB heB)
        (RelativeSquare.evaluation p1Parameter sY genericBase eA heA)
        (RelativeSquare.map_evaluation p1Parameter (modelProjection F a)
          (genericParametrization F a ha) genericPoint
          (genericParametrization_parameter F a ha) sY genericBase toC
          eA eB heA heB hke) (externalTensor sY E H)).hom) =
      (RelativeSquare.productSection p1Parameter
      (pullSection (genericParametrization F a ha) (ModelNumerator.coordinate F a 1 0) ≫ uA) (pullSection (genericParametrization F a ha) (ModelNumerator.coordinate F a 0 1) ≫ vA) ≫
      RelativeSquare.comparison p1Parameter sY genericBase eA heA E H) +
      (RelativeSquare.productSection p1Parameter
      (pullSection (genericParametrization F a ha) (ModelNumerator.coordinate F a 0 1) ≫ uA) (pullSection (genericParametrization F a ha) (ModelNumerator.coordinate F a 1 0) ≫ vA) ≫
      RelativeSquare.comparison p1Parameter sY genericBase eA heA E H) -
      scalarSection (2 * genericCoefficient F a ha) ≫
        (RelativeSquare.productSection p1Parameter
      (pullSection (genericParametrization F a ha) (ModelNumerator.coordinate F a 0 0) ≫ uA) (pullSection (genericParametrization F a ha) (ModelNumerator.coordinate F a 0 0) ≫ vA) ≫
      RelativeSquare.comparison p1Parameter sY genericBase eA heA E H) := by
  exact numerator_three_congr
    (fun x y : (@Quiver.Hom (SheafOfModules (Parametrized.Square Lines.P genericBase).ringCatSheaf) (@CategoryStruct.toQuiver (SheafOfModules (Parametrized.Square Lines.P genericBase).ringCatSheaf) (@Category.toCategoryStruct (SheafOfModules (Parametrized.Square Lines.P genericBase).ringCatSheaf) SheafOfModules.instCategory)) (SheafOfModules.unit (Parametrized.Square Lines.P genericBase).ringCatSheaf) (@pullbackModule (Parametrized.Square Lines.P genericBase) (SelfProduct sY) (RelativeSquare.evaluation p1Parameter sY genericBase eA heA) (externalTensor sY E H))) => x + y)
    (fun x y : (@Quiver.Hom (SheafOfModules (Parametrized.Square Lines.P genericBase).ringCatSheaf) (@CategoryStruct.toQuiver (SheafOfModules (Parametrized.Square Lines.P genericBase).ringCatSheaf) (@Category.toCategoryStruct (SheafOfModules (Parametrized.Square Lines.P genericBase).ringCatSheaf) SheafOfModules.instCategory)) (SheafOfModules.unit (Parametrized.Square Lines.P genericBase).ringCatSheaf) (@pullbackModule (Parametrized.Square Lines.P genericBase) (SelfProduct sY) (RelativeSquare.evaluation p1Parameter sY genericBase eA heA) (externalTensor sY E H))) => x - y)
    (fun r : ↥((Parametrized.Square Lines.P genericBase).presheaf.obj (@Opposite.op (Parametrized.Square Lines.P genericBase).Opens (⊤ : (Parametrized.Square Lines.P genericBase).Opens))) => fun x : (@Quiver.Hom (SheafOfModules (Parametrized.Square Lines.P genericBase).ringCatSheaf) (@CategoryStruct.toQuiver (SheafOfModules (Parametrized.Square Lines.P genericBase).ringCatSheaf) (@Category.toCategoryStruct (SheafOfModules (Parametrized.Square Lines.P genericBase).ringCatSheaf) SheafOfModules.instCategory)) (SheafOfModules.unit (Parametrized.Square Lines.P genericBase).ringCatSheaf) (@pullbackModule (Parametrized.Square Lines.P genericBase) (SelfProduct sY) (RelativeSquare.evaluation p1Parameter sY genericBase eA heA) (externalTensor sY E H))) =>
      @CategoryStruct.comp (SheafOfModules (Parametrized.Square Lines.P genericBase).ringCatSheaf) _ _ _ _
        (@scalarSection (Parametrized.Square Lines.P genericBase) r) x)
    (numerator_product_10_transport F a ha sY eB heB eA heA hke uB vB uA vA hu hv)
    (numerator_product_01_transport F a ha sY eB heB eA heA hke uB vB uA vA hu hv)
    (numerator_product_00_transport F a ha sY eB heB eA heA hke uB vB uA vA hu hv)
    (numerator_coefficient_literal F a ha)


/-- Base change of the actual three-term model numerator, after any
specified pair of maps out of its logarithmic line. -/
theorem numerator_transport (ha : a ≠ 0)
    {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (eB : Model F a ⟶ Y) (heB : eB ≫ sY = modelProjection F a ≫ toC)
    (eA : P1Generic ⟶ Y) (heA : eA ≫ sY = p1Parameter ≫ genericBase)
    (hke : genericParametrization F a ha ≫ eB = eA)
    {E H : OModule Y}
    (uB : (modelLine F a).sheaf ⟶ pullbackModule eB E)
    (vB : (modelLine F a).sheaf ⟶ pullbackModule eB H)
    (uA : pullbackModule (genericParametrization F a ha) (modelLine F a).sheaf ⟶
      pullbackModule eA E)
    (vA : pullbackModule (genericParametrization F a ha) (modelLine F a).sheaf ⟶
      pullbackModule eA H)
    (hu : (Scheme.Modules.pullback (genericParametrization F a ha)).map uB ≫
      (compositionPullback (genericParametrization F a ha) eB eA hke E).hom = uA)
    (hv : (Scheme.Modules.pullback (genericParametrization F a ha)).map vB ≫
      (compositionPullback (genericParametrization F a ha) eB eA hke H).hom = vA) :
    pullSection (parametrizedToModelSquare F a ha)
      (ModelNumerator.numerator F a ≫
        RelativeSquare.boxMap (modelProjection F a) uB vB ≫
          RelativeSquare.comparison (modelProjection F a) sY toC eB heB E H) ≫
      (compositionPullback (parametrizedToModelSquare F a ha)
        (RelativeSquare.evaluation (modelProjection F a) sY toC eB heB)
        (RelativeSquare.evaluation p1Parameter sY genericBase eA heA)
        (RelativeSquare.map_evaluation p1Parameter (modelProjection F a)
          (genericParametrization F a ha) genericPoint
          (genericParametrization_parameter F a ha) sY genericBase toC
          eA eB heA heB hke) (externalTensor sY E H)).hom =
      genericNumerator F a ha ≫ RelativeSquare.boxMap p1Parameter uA vA ≫
        RelativeSquare.comparison p1Parameter sY genericBase eA heA E H := by
  exact (numerator_expanded_source F a ha sY eB heB eA heA hke uB vB uA vA hu hv).trans
    ((numerator_expanded_transport F a ha sY eB heB eA heA hke uB vB uA vA hu hv).trans
      (numerator_expanded_target F a ha sY eB heB eA heA hke uB vB uA vA hu hv).symm)

end LeBrunSalamon.Construction.TraitContact.ModelGenericComparison

end

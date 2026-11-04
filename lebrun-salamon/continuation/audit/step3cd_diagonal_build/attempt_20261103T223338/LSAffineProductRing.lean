import LSKunnethDegreeZero

/-!
The actual coordinate-ring comparison for a product over a field, with
normalization on pure tensors and on the diagonal.  Its bijectivity is the
unit-sheaf specialization of the already isolated degree-zero Künneth input.
No additional admitted statement is used.  Candidate outside source/.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight
open scoped TensorProduct

namespace LeBrunSalamon.AffineProductRing

variable {k : Type} [Field k]

def Functions {X : Scheme} (s : X ⟶ Spec (CommRingCat.of k)) : Type := RingSections X ⊤

instance functionsCommRing {X : Scheme} (s : X ⟶ Spec (CommRingCat.of k)) :
    CommRing (Functions s) := inferInstanceAs (CommRing (RingSections X ⊤))

instance functionsModule {X : Scheme} (s : X ⟶ Spec (CommRingCat.of k)) :
    Module k (Functions s) := Module.compHom (RingSections X ⊤) (KunnethDegreeZero.constants s ⊤)

instance functionsAlgebra {X : Scheme} (s : X ⟶ Spec (CommRingCat.of k)) :
    Algebra k (Functions s) := Algebra.compHom (RingSections X ⊤) (KunnethDegreeZero.constants s ⊤)

def pullFunctions {X Y : Scheme} (f : X ⟶ Y)
    (sX : X ⟶ Spec (CommRingCat.of k)) (sY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ sY = sX) : Functions sY →ₐ[k] Functions sX where
  toRingHom := f.appTop.hom
  commutes' := KunnethDegreeZero.constants_naturality f sX sY hf

def ringMap {X Y : Scheme}
    (sX : X ⟶ Spec (CommRingCat.of k)) (sY : Y ⟶ Spec (CommRingCat.of k)) :
    (Functions sX ⊗[k] Functions sY) →ₐ[k] Functions (pullback.fst sX sY ≫ sX) :=
  Algebra.TensorProduct.lift
    (pullFunctions (pullback.fst sX sY) (pullback.fst sX sY ≫ sX) sX rfl)
    (pullFunctions (pullback.snd sX sY) (pullback.fst sX sY ≫ sX) sY pullback.condition.symm)
    (fun _ _ => Commute.all _ _)

theorem ringMap_tmul {X Y : Scheme}
    (sX : X ⟶ Spec (CommRingCat.of k)) (sY : Y ⟶ Spec (CommRingCat.of k))
    (a : Functions sX) (b : Functions sY) :
    ringMap sX sY (a ⊗ₜ[k] b) =
      (pullback.fst sX sY).appTop a * (pullback.snd sX sY).appTop b := by
  rw [ringMap, Algebra.TensorProduct.lift_tmul]
  rfl

def unitExternalIso {X Y : Scheme}
    (sX : X ⟶ Spec (CommRingCat.of k)) (sY : Y ⟶ Spec (CommRingCat.of k)) :
    KunnethDegreeZero.externalTensor sX sY (structureModule X) (structureModule Y) ≅
      structureModule (pullback sX sY) :=
  tensorIso (unitPullbackIso (pullback.fst sX sY))
    (unitPullbackIso (pullback.snd sX sY)) ≪≫
      TensorConstruction.leftUnitIso (structureModule (pullback sX sY))

/-- Explicit ring-valued normalization avoids treating unit-sheaf sections
only through their additive-module interface. -/
def unitPullbackFunction {X Y : Scheme} (f : X ⟶ Y)
    (a : GlobalSections (pullbackModule f (structureModule Y))) : RingSections X ⊤ :=
  (unitPullbackMap f).app ⊤ a

theorem unitExternalIso_pair {X Y : Scheme}
    (sX : X ⟶ Spec (CommRingCat.of k)) (sY : Y ⟶ Spec (CommRingCat.of k))
    (a : GlobalSections (pullbackModule (pullback.fst sX sY) (structureModule X)))
    (b : GlobalSections (pullbackModule (pullback.snd sX sY) (structureModule Y))) :
    (unitExternalIso sX sY).hom.app ⊤
      ((tensorPresentation _ _).pair.apply ⊤ a b) =
      unitPullbackFunction (pullback.fst sX sY) a *
        unitPullbackFunction (pullback.snd sX sY) b := by
  change (TensorConstruction.leftUnitIso (structureModule (pullback sX sY))).hom.app ⊤
    ((tensorMap (unitPullbackIso (pullback.fst sX sY)).hom
      (unitPullbackIso (pullback.snd sX sY)).hom).app ⊤
        ((tensorPresentation _ _).pair.apply ⊤ a b)) = _
  rw [tensorMap_apply, TensorConstruction.leftUnitHom_pair]
  rfl

private theorem unitPullbackFunction_sectionValue {X Y : Scheme} (f : X ⟶ Y)
    (a : RingSections Y ⊤) :
    unitPullbackFunction f
      (sectionValue (pullSection f (sectionFromValue (E := structureModule Y) a))) =
        f.appTop a := by
  change (unitPullbackMap f).app ⊤
    (sectionValue (pullSection f (sectionFromValue (E := structureModule Y) a))) = _
  rw [pullSection_value, sectionFromValue_spec]
  exact congrArg (fun q : structureModule Y ⟶
    (Scheme.Modules.pushforward f).obj (structureModule X) => q.app ⊤ a)
      (unitPullbackMap_adjoint f)

/-- The ring morphism is precisely the degree-zero Künneth morphism after
the canonical tensor/unit comparison, on every tensor. -/
theorem ringMap_eq_sectionMap {X Y : Scheme}
    (sX : X ⟶ Spec (CommRingCat.of k)) (sY : Y ⟶ Spec (CommRingCat.of k))
    (t : Functions sX ⊗[k] Functions sY) :
    ringMap sX sY t = (unitExternalIso sX sY).hom.app ⊤
      (KunnethDegreeZero.canonicalMap sX sY (structureModule X) (structureModule Y) t) := by
  refine TensorProduct.inductionOn t ?_ ?_
  · intro a b
    rw [ringMap_tmul, KunnethDegreeZero.canonicalMap_tmul, sectionValue_tensorSection,
      unitExternalIso_pair, unitPullbackFunction_sectionValue, unitPullbackFunction_sectionValue]
  · intro a b ha hb
    simp only [map_add, ha, hb]

theorem ringMap_bijective {X Y : Scheme}
    (sX : X ⟶ Spec (CommRingCat.of k)) (sY : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [CompactSpace Y] [IsSeparated sX] [IsSeparated sY] :
    Function.Bijective (ringMap sX sY) := by
  letI : (structureModule X).IsQuasicoherent :=
    KunnethDegreeZero.quasicoherent_of_locallyFreeRank (structureModule_rank X)
  letI : (structureModule Y).IsQuasicoherent :=
    KunnethDegreeZero.quasicoherent_of_locallyFreeRank (structureModule_rank Y)
  have hk := PublishedInputs.Kunneth.canonicalMap_bijective
    sX sY (structureModule X) (structureModule Y)
  have he := ConcreteCategory.bijective_of_isIso ((unitExternalIso sX sY).hom.app ⊤)
  have hfun : (ringMap sX sY : _ → _) = fun t =>
      (unitExternalIso sX sY).hom.app ⊤
        (KunnethDegreeZero.canonicalMap sX sY (structureModule X) (structureModule Y) t) :=
    funext (ringMap_eq_sectionMap sX sY)
  rw [hfun]
  exact he.comp hk

def ringEquiv {X Y : Scheme}
    (sX : X ⟶ Spec (CommRingCat.of k)) (sY : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [CompactSpace Y] [IsSeparated sX] [IsSeparated sY] :
    (Functions sX ⊗[k] Functions sY) ≃+* Functions (pullback.fst sX sY ≫ sX) :=
  RingEquiv.ofBijective (ringMap sX sY).toRingHom (ringMap_bijective sX sY)

/-- The actual scheme-theoretic diagonal is multiplication of the two
coordinate factors under this very same ring map. -/
theorem diagonal_ringMap {X : Scheme} (s : X ⟶ Spec (CommRingCat.of k))
    (t : Functions s ⊗[k] Functions s) :
    (pullback.diagonal s).appTop (ringMap s s t) = Algebra.TensorProduct.lmul' k t := by
  refine TensorProduct.inductionOn t ?_ ?_
  · intro a b
    rw [ringMap_tmul, map_mul]
    have ha : (pullback.diagonal s).appTop ((pullback.fst s s).appTop a) = a := by
      change (pullback.diagonal s ≫ pullback.fst s s).appTop a = a
      rw [pullback.diagonal_fst]
      simp
    have hb : (pullback.diagonal s).appTop ((pullback.snd s s).appTop b) = b := by
      change (pullback.diagonal s ≫ pullback.snd s s).appTop b = b
      rw [pullback.diagonal_snd]
      simp
    rw [ha, hb]
    rfl
  · intro a b ha hb
    simp only [map_add, ha, hb]

end LeBrunSalamon.AffineProductRing

end

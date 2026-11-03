import LSFamilyBaseChange

/-!
# Finite-type spreading data for a field-valued automorphism

The helper below is an ordinary actual base-change map.  The proposed
published spreading input is reviewed separately and contains no
tensor, differential, or contact conclusion.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne

namespace LeBrunSalamon.Construction.FiniteTypeSpreading

def changeBase {Y S A B : Scheme} (p : Y ⟶ S) (sA : A ⟶ S) (sB : B ⟶ S)
    (b : A ⟶ B) (h : b ≫ sB = sA) : pullback p sA ⟶ pullback p sB :=
  pullback.lift (pullback.fst p sA) (pullback.snd p sA ≫ b) (by
    rw [Category.assoc, h]
    exact pullback.condition)

@[reassoc] theorem changeBase_fst {Y S A B : Scheme}
    (p : Y ⟶ S) (sA : A ⟶ S) (sB : B ⟶ S)
    (b : A ⟶ B) (h : b ≫ sB = sA) :
    changeBase p sA sB b h ≫ pullback.fst p sB = pullback.fst p sA :=
  pullback.lift_fst _ _ _

@[reassoc] theorem changeBase_snd {Y S A B : Scheme}
    (p : Y ⟶ S) (sA : A ⟶ S) (sB : B ⟶ S)
    (b : A ⟶ B) (h : b ≫ sB = sA) :
    changeBase p sA sB b h ≫ pullback.snd p sB = pullback.snd p sA ≫ b :=
  pullback.lift_snd _ _ _

end LeBrunSalamon.Construction.FiniteTypeSpreading

namespace LeBrunSalamon.StandardInputs

/-- Stacks 01ZM(2),(3), applied to the directed finitely generated
subalgebras of the actual field K over C.  The parameter point is
retained through an affine image neighbourhood.  This is generic
finite-presentation spreading and asserts no tensor identity. -/
theorem proper_automorphism_spreads_with_parameter
    (K : Type) [Field K] (sK : Spec (CommRingCat.of K) ⟶ ComplexBase)
    {Y B₀ : Scheme} (sY : Y ⟶ ComplexBase) [IsProper sY]
    (s₀ : B₀ ⟶ ComplexBase) [LocallyOfFiniteType s₀]
    (t : PointsOver (Spec (CommRingCat.of K)) sK B₀ s₀)
    (e : pullback sY sK ≅ pullback sY sK)
    (he : e.hom ≫ pullback.snd sY sK = pullback.snd sY sK) :
    ∃ (B : Scheme) (sB : B ⟶ ComplexBase),
      IsAffine B ∧ IsIntegral B ∧ LocallyOfFiniteType sB ∧
      ∃ (u : B ⟶ B₀), u ≫ s₀ = sB ∧
        ∃ (b : Spec (CommRingCat.of K) ⟶ B), b ≫ u = t.val ∧
          ∃ hb : b ≫ sB = sK,
            ∃ eB : pullback sY sB ≅ pullback sY sB,
              eB.hom ≫ pullback.snd sY sB = pullback.snd sY sB ∧
              LeBrunSalamon.Construction.FiniteTypeSpreading.changeBase sY sK sB b hb ≫
                  eB.hom =
                e.hom ≫
                  LeBrunSalamon.Construction.FiniteTypeSpreading.changeBase sY sK sB b hb := by
  sorry

end LeBrunSalamon.StandardInputs

end

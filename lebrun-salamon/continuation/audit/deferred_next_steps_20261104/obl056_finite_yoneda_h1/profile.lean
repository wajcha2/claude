import RecompileExtensionsPart01
import LSYonedaClassesRepresented

/-! Finite sums of the actual Yoneda extension-splitting predicate.
This isolated helper contains no new input or original-obligation proof. -/

noncomputable section
set_option autoImplicit false
set_option profiler true
set_option stderrAsMessages false

universe w v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseThirtyTwo LeBrunSalamon.YonedaExtensionSplitting

namespace LeBrunSalamon.FiniteFirstCohomology

#eval show IO Unit from do (← IO.getStderr).putStrLn "FINITE_H1_STAGE ENTER_allExtensionsSplit_of_bilimit"

/-- Finite biproducts preserve splitting of every extension by the fixed
quotient object. The proof uses the native covariant Ext equivalence. -/
theorem allExtensionsSplit_of_bilimit
    {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
    [EnoughInjectives C] (U : C)
    {I : Type*} [Fintype I] {E : I → C} {c : Bicone E}
    (hc : c.IsBilimit) (hE : ∀ i, AllExtensionsSplit U (E i)) :
    AllExtensionsSplit U c.pt := by
  apply allExtensionsSplit_of_subsingleton U c.pt
  refine ⟨fun a b => (Ext.addEquivBiproduct U hc 1).injective ?_⟩
  funext i
  exact ((allExtensionsSplit_iff_ext1_subsingleton U (E i)).mp (hE i)).elim _ _


#eval show IO Unit from do (← IO.getStderr).putStrLn "FINITE_H1_STAGE EXIT_allExtensionsSplit_of_bilimit"

#eval show IO Unit from do (← IO.getStderr).putStrLn "FINITE_H1_STAGE ENTER_finite_coproduct"

/-- Vanishing of the original Yoneda H1 predicate is preserved by the
actual finite coproduct of module sheaves, including an empty family. -/
theorem finite_coproduct {X : Scheme} {I : Type} [Fintype I]
    (E : I → OModule X) (hE : ∀ i, HasVanishingFirstCohomology (E i)) :
    HasVanishingFirstCohomology (∐ E) := by
  letI : HasFiniteBiproducts (OModule X) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  have hsum : HasVanishingFirstCohomology (⨁ E) :=
    allExtensionsSplit_of_bilimit (structureModule X) (biproduct.isBilimit E) hE
  exact (FirstCohomology.iso_iff (biproduct.isoCoproduct E)).mp hsum


#eval show IO Unit from do (← IO.getStderr).putStrLn "FINITE_H1_STAGE EXIT_finite_coproduct"

#eval show IO Unit from do (← IO.getStderr).putStrLn "FINITE_H1_STAGE ENTER_finite_coproduct_iff"

/-- The converse uses the original coordinate retraction, so this is an
equivalence for the same concrete coproduct and vanishing predicate. -/
theorem finite_coproduct_iff {X : Scheme} {I : Type} [Fintype I]
    (E : I → OModule X) :
    HasVanishingFirstCohomology (∐ E) ↔
      ∀ i, HasVanishingFirstCohomology (E i) :=
  ⟨fun h i => FirstCohomology.coproduct_summand E h i,
    finite_coproduct E⟩

#eval show IO Unit from do (← IO.getStderr).putStrLn "FINITE_H1_STAGE EXIT_finite_coproduct_iff"


end LeBrunSalamon.FiniteFirstCohomology

end

#print axioms LeBrunSalamon.FiniteFirstCohomology.allExtensionsSplit_of_bilimit
#print axioms LeBrunSalamon.FiniteFirstCohomology.finite_coproduct
#print axioms LeBrunSalamon.FiniteFirstCohomology.finite_coproduct_iff

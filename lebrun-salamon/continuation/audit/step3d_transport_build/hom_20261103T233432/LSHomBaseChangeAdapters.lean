import LSHomFiberInjectivity
import RecompileExtensionsPart03

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.Skeleton
open LeBrunSalamon.Construction

namespace LeBrunSalamon.HomBaseChangeAdapters

theorem homBaseChange_isIso {X Y : Scheme} (f : X ⟶ Y) {r : ℕ}
    (E : AlgebraicVectorBundle Y r) (F : OModule Y) :
    IsIso (Lines.ContactPositiveHom.homBaseChange f E.sheaf F) :=
  FiniteFreeHomBaseChange.homComparison_isIso f E.locallyFree F

theorem homFiberEvaluation_injective {Y : Scheme} {r : ℕ}
    (E : AlgebraicVectorBundle Y r) (F : OModule Y) (x : ComplexBase ⟶ Y) :
    Function.Injective (Lines.LeviFiberGeometry.homFiberEvaluation E.sheaf F x) := by
  intro a b h
  apply HomFiberInjectivity.homFiberEvaluation_injective E F x
  funext v
  exact congrArg (fun q => q v) h

end LeBrunSalamon.HomBaseChangeAdapters

end

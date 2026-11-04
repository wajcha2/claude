import LSP1BivectorVanishing
import LSP1BivectorNormalization
import LSP1BivectorUniqueness

/-! Assembly of the actual, uniquely normalized source tensor. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.Core LeBrunSalamon.Skeleton

namespace LeBrunSalamon.P1BivectorAssembly

theorem existsUnique (P : ProjectiveLineOverC) :
    ∃! B : ExternalSquareSections (projectiveLineVariety P)
        (identityCurveContact P).sequence.line,
      IsSymmetricExternalSection P.structureMap (identityCurveContact P).sequence.line B ∧
      VanishesQuadraticallyAlongDiagonal P.structureMap
        (externalSquareLine P.structureMap (identityCurveContact P).sequence.line).sheaf B ∧
      HasNormalizedContactSymbol (identityCurveContact P) B := by
  refine ⟨P1BivectorConstruction.bivector P,
    ⟨P1BivectorConstruction.symmetric P, P1BivectorVanishing.order_two P,
      P1BivectorNormalization.normalized P⟩, ?_⟩
  intro B hB
  exact P1BivectorUniqueness.unique P (P1BivectorConstruction.bivector P)
    hB.2.1 hB.2.2 (P1BivectorVanishing.order_two P)
    (P1BivectorNormalization.normalized P)

end LeBrunSalamon.P1BivectorAssembly

end

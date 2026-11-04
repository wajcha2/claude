import LSStandardConicTriple
import LSPlaneConicZeroPresentation

/-! Actual comparison of the specified base change of the fixed (1,1)
source with the literal plane equation xy=a*z².  The coefficient equality
is retained as a hypothesis and later proved for the formal-trait map.
No family normal form or new admission occurs here. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.Skeleton
open LeBrunSalamon.Refinement LeBrunSalamon.Construction
open LeBrunSalamon.Construction.Smoothing

namespace LeBrunSalamon.StandardConicZeroComparison

variable (R : Type) [CommRing R] (F : StandardSource)
    (t : Spec (CommRingCat.of R) ⟶ AffineLine) (a : R)
    (ha : t.appTop parameterFunction = (Scheme.ΓSpecIso (CommRingCat.of R)).inv a)

def presentation : PlaneConicPresentation.Presentation (Spec (CommRingCat.of R))
    (PlaneConicZeroPresentation.parameter R a) :=
  PlaneConicPresentation.reparameterize (StandardConicTriple.presentation F t) ha

def iso : SourceOver F t ≅ PlaneQuadratic.ZeroScheme R (PlaneQuadratic.split R a) :=
  PlaneConicPresentation.presentationIso (presentation R F t a ha)
    (PlaneConicZeroPresentation.presentation R a)

@[reassoc] theorem iso_over :
    (iso R F t a ha).hom ≫ PlaneQuadratic.projection R (PlaneQuadratic.split R a) =
      pullback.snd F.parameter t :=
  PlaneConicPresentation.presentationIso_over (presentation R F t a ha)
    (PlaneConicZeroPresentation.presentation R a)

def lineIso : (StandardConicTriple.line F t).sheaf ≅
    pullbackModule (iso R F t a ha).hom (PlaneConicZeroPresentation.line R a).sheaf :=
  PlaneConicPresentation.presentationIso_line (presentation R F t a ha)
    (PlaneConicZeroPresentation.presentation R a)

end LeBrunSalamon.StandardConicZeroComparison
end

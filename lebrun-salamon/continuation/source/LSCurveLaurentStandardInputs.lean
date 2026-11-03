import LSFunctionFieldPlaces
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.LaurentSeries

/-!
## Laurent expansion at a pole

The project theorem is proved from four separately stated published inputs in
`LSFunctionFieldPlaces`: dimension/transcendence degree, existence of a pole,
finiteness of a place's residue field, and the complete discretely valued field
with coefficient field theorem. The completion residue-field map, actual
constant-preserving embedding, and sign of Laurent order are proved in Lean.
The former compactification/completion composite is no longer admitted.
-/

noncomputable section
set_option autoImplicit false

namespace LeBrunSalamon.CurveStandardInputs

/-- The project-facing Laurent expansion, assembled from the separately
cited field-theoretic theorems and actual completion maps. -/
theorem _root_.LeBrunSalamon.PublishedInputs.ProjectiveLineGeometry.laurentExpansionAtPole
    (B : Type) [CommRing B] [IsDomain B] [Algebra ℂ B] [Algebra.FiniteType ℂ B]
    (hdim : ringKrullDim B = 1) (f : B)
    (hf : ¬ ∃ c : ℂ, algebraMap ℂ B c = f) :
    ∃ j : FractionRing B →ₐ[ℂ] LaurentSeries ℂ,
      (j (algebraMap B (FractionRing B) f)).order < 0 := by
  exact LeBrunSalamon.FunctionFieldPlaces.laurentExpansionAtPole B hdim f hf

/-- Project-facing name for the standard Laurent-expansion theorem. -/
theorem exists_laurent_expansion_with_pole
    (B : Type) [CommRing B] [IsDomain B] [Algebra ℂ B] [Algebra.FiniteType ℂ B]
    (hdim : ringKrullDim B = 1) (f : B)
    (hf : ¬ ∃ c : ℂ, algebraMap ℂ B c = f) :
    ∃ j : FractionRing B →ₐ[ℂ] LaurentSeries ℂ,
      (j (algebraMap B (FractionRing B) f)).order < 0 :=
  LeBrunSalamon.PublishedInputs.ProjectiveLineGeometry.laurentExpansionAtPole
    B hdim f hf

end LeBrunSalamon.CurveStandardInputs

end

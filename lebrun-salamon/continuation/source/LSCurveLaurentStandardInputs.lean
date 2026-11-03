import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.LaurentSeries

/-!
## Classical Laurent expansion at a pole of an affine curve function

This is an individually reviewed standard curve-theoretic corollary, not
a contact-geometric or cone-addition assumption. The published inputs are:
Stacks 33.43.6 (0BXW), compactification with DVR boundary stalks;
33.26.2 (04L2), constants on a proper integral variety;
10.97.3 (00MC), faithful flatness of completion;
15.44.1 and 15.44.4 (07NU), preservation of dimension and regularity;
10.160.10(2) (0C0S), the power-series description as a C-algebra.

For a nonconstant regular function on the affine integral curve, some
boundary stalk does not contain that function: otherwise its local regular
extensions glue to a global regular function on the proper completion,
which is constant. At that DVR the function has negative valuation.
The completed DVR has residue field C and is C[[t]] as a C-algebra;
the induced injection of fraction fields has target C((t)) and preserves
the sign of this valuation. No smoothness of the original affine curve is
assumed. The input contains no selected cone, arc, rescaling, or chart.

SOURCE ONLY: final incremental compiler verification is pending.
-/

noncomputable section
set_option autoImplicit false

namespace LeBrunSalamon.CurveStandardInputs

/-- **Published input.** A nonconstant regular function on an integral
affine complex curve has a pole on a proper normal compactification, and the
completed DVR at that boundary point embeds its fraction field into `ℂ((t))`.
This is the standard combination of compactification and boundary DVR theory
(Stacks Project Tags 0BXW, 04L2, 00MC, 07NU and 0C0S). -/
theorem _root_.LeBrunSalamon.PublishedInputs.ProjectiveLineGeometry.laurentExpansionAtPole
    (B : Type) [CommRing B] [IsDomain B] [Algebra ℂ B] [Algebra.FiniteType ℂ B]
    (hdim : ringKrullDim B = 1) (f : B)
    (hf : ¬ ∃ c : ℂ, algebraMap ℂ B c = f) :
    ∃ j : FractionRing B →ₐ[ℂ] LaurentSeries ℂ,
      (j (algebraMap B (FractionRing B) f)).order < 0 := by
  sorry

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

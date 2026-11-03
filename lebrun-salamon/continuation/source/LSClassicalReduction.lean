import RecompileExtensionsPart01

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseSeven LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentySeven LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.PhaseThirtyTwo LeBrunSalamon.Core LeBrunSalamon.Skeleton

namespace LeBrunSalamon.ClassicalReduction

/-- An actual projective embedding with its actual hyperplane pullback.
This is ordinary data; it does not assert first-jet generation. -/
structure PolarizedProjectiveEmbedding {d : ℕ}
    (X : SmoothProperComplexVariety d) (L : LineBundle X.scheme) where
  dimension : ℕ
  coordinates : ProjectiveCoordinates dimension
  embedding : X.scheme ⟶ ComplexProjectiveSpace dimension
  closed : IsClosedImmersion embedding
  overC : embedding ≫ projectiveBaseMap dimension = X.structureMap
  polarization : pullbackModule embedding coordinates.hyperplane.sheaf ≅ L.sheaf

universe uR

namespace StandardInputs

/- Generic very-ampleness consequence. Hartshorne, Algebraic Geometry,
II.7.3 and its proof: the embedding coordinates span the value and the
cotangent space at each point. Thus they span O/m², and the same holds
for the pullback of O(1). The statement is about actual sheaf pullback
and the existing fat-point jetRestrictionAt, not a numerical rank.
The forward implication is the affine-chart/cotangent-quotient argument;
Stacks 01QN, Lemma 29.2.1 supplies the actual closed-immersion quotient.
Stacks 0E8S/0E8T are the converse criteria and are not cited as this statement.
-/
theorem _root_.LeBrunSalamon.PublishedInputs.Step3e.polarizedEmbedding_firstJets {d : ℕ}
    (X : SmoothProperComplexVariety d) (L : LineBundle X.scheme)
    (E : PolarizedProjectiveEmbedding X L) : SeparatesFirstJets X L := by
  sorry

/-- Project-facing consequence of the published first-jet separation theorem
for the actual closed immersion and hyperplane pullback. -/
theorem polarizedEmbedding_firstJets {d : ℕ}
    (X : SmoothProperComplexVariety d) (L : LineBundle X.scheme)
    (E : PolarizedProjectiveEmbedding X L) : SeparatesFirstJets X L := by
  exact LeBrunSalamon.PublishedInputs.Step3e.polarizedEmbedding_firstJets X L E

/- Classical nonprimitive contact-Fano alternative, stated only as the
line embedding needed here. KPSW, Invent.Math.142 (2000), Theorem1.1,
identifies (X,L) with (P(TY),O(1)) when b2>1. Fano forces TY ample;
Mori, Ann.Math.110 (1979), makes Y=P^(n+1). The contact line is therefore
O(1,1) on incidence and its Segre restriction is very ample.
For Picard rank one, L=A^k with k>1 and -K=L^(n+1); Kobayashi--Ochiai,
J.Math.Kyoto13 (1973), index bound/equality case, gives P^(2n+1), k=2,
and the quadratic Veronese gives this embedding. The same index/equality
case follows directly from Araujo--Druel--Kovacs, Invent.Math.174 (2008),
Theorem1.3 (=Corollary5.5), applied to the top exterior tangent power.
The standard Fano Picard freeness/vanishing identifies the rank-one alternatives with
the existing HasPrimitiveContactPicard predicate. No primitive claim
is included, and contact-distribution classification is not required.
This is a stated corollary, not the verbatim wording of KPSW.
-/
theorem nonprimitive_contactLine_embedding {n : ℕ}
    (X : ContactFanoManifold n)
    (hp : ¬ HasPrimitiveContactPicard X.contact) :
    Nonempty (PolarizedProjectiveEmbedding X.variety X.contact.sequence.line) := by
  sorry

/- Published homogeneous contact classification (Boothby/Wolf), with
Beauville 1998 Sections2.1--2.5, Proposition2.6 and Remark2.3 fixing the
minimal adjoint orbit, hyperplane polarization and KKS kernel.
Wolf1965 is available from the author's Berkeley page, paper_024.pdf;
the exhaustive converse in Section2, printed p1036 immediately after
(2.5), classifies every compact simply connected homogeneous complex
contact manifold. Campana, Bull.SMF122 (1994), Corollary5.7,p275
supplies simple connectedness for Fano manifolds. GAGA algebraizes
the projective identifications. The original supplied acting group
need not itself be simple.

The hypothesis is the actual connected regular algebraic group action
with all test-scheme laws, effectivity, transitivity and ContactIso
translations. The output is the original strong presentation, including
the closed scheme embedding, complex-point image criterion, and the
affine-section canonicalContact formula. The affine formula follows by
surjectivity on sections of the orbit-tangent bundle map and the KKS
hyperplane equation; affine quasi-coherent exactness gives the global
regular lifting, and the frame trivializes the radial error. No classification
of a nonhomogeneous contact Fano manifold is asserted.
-/
theorem homogeneous_contact_adjointPresentation {n : ℕ}
    (X : ContactFanoManifold n) (A : AlgebraicContactAction X) :
    Nonempty (AdjointContactPresentation X) := by
  sorry


/- Classical twistor reduction only, with a conditional recovery map.
LeBrun, Int.J.Math.6 (1995), Theorem2.1 gives the positive twistor
contact/KE manifold; Kodaira and GAGA give the actual projective scheme
and algebraic contact sequence. Wolf1965 Theorem6.1 supplies the compact
quaternionic symmetric model for each homogeneous contact type.
LeBrun1995 Corollary3.4 gives a base isometry from the complex twistor
isomorphism class, under the standing scalar normalization after
Definition1.2. Undoing the two positive constant metric rescalings gives
the exact SmoothMetricHomothety output. The given complex isomorphism
need not preserve either chosen real structure.

The output type is the ORIGINAL TwistorReductionOutput, with an actual
ContactFanoManifold and a map from its actual AdjointContactPresentation
to a symmetric Riemannian model/homothety. It does not supply an adjoint
presentation for the twistor space, and thus contains no instance of
LeBrun--Salamon itself. This is a classical composite corollary, not a
claim that the manuscript's argument is a published theorem.
-/
theorem positiveQK_twistorReduction (n : ℕ) (M : ClosedPositiveQK.{uR} n) :
    Nonempty (TwistorReductionOutput.{uR} M) := by
  sorry


end StandardInputs

/-- The nonprimitive projective embedding supplies the actual first jets.
Both inputs are reviewed classical results; this is the ordinary
constructor for the original NonprimitiveBranch obligation. -/
theorem nonprimitiveBranch : NonprimitiveBranch := by
  intro n X hp
  obtain ⟨E⟩ := StandardInputs.nonprimitive_contactLine_embedding X hp
  exact StandardInputs.polarizedEmbedding_firstJets X.variety X.contact.sequence.line E

/-- The supplied actual transitive contact action places X within the
published homogeneous classification. The original strong adjoint
presentation, including its polarization and contact kernel, is retained. -/
theorem homogeneousClassification : HomogeneousClassification := by
  intro n X A
  exact StandardInputs.homogeneous_contact_adjointPresentation X A


/-- The conditional metric recovery remains conditional on the supplied
adjoint presentation; no contact-Fano classification is used here. -/
theorem positiveTwistorReduction : PositiveTwistorReduction.{uR} := by
  intro n M
  exact StandardInputs.positiveQK_twistorReduction n M

/-- All three original Riemannian inputs, with the classical reduction
and the already explicit metric-curvature transport results. -/
theorem riemannianInputs : RiemannianInputs.{uR} where
  twistor := positiveTwistorReduction
  symmetriesParallel := by
    intro n S
    exact globalSymmetries_parallelCurvature S
  homothetyParallel := by
    intro n A B f hB
    exact homothety_parallelCurvature f hB

end LeBrunSalamon.ClassicalReduction

end
